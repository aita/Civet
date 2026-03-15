import Tree

/// Scalar Replacement of Aggregates.
///
/// Decomposes struct variables into individual scalar variables when all
/// accesses are through `.member` + `load`/`store` patterns. Runs before
/// SSA construction so the new scalars can be promoted to SSA registers.
public func scalarReplacement(_ program: Program) -> Program {
    Program(
        functions: program.functions.map { scalarReplacement(in: $0) },
        globals: program.globals
    )
}

public func scalarReplacement(in function: Function) -> Function {
    let blocks = function.blocks
    guard !blocks.isEmpty else { return function }

    // ── Phase 1: Collect candidates ─────────────────────────────────

    // Map local id → CVar for struct locals
    var candidateVars: [Int: CVar] = [:]
    // Map local id → CRecordType
    var candidateRecords: [Int: CRecordType] = [:]

    for v in function.locals {
        guard case .local(let id) = v.storage, id > 0,
              case .structType(let record) = v.type else { continue }
        // No unions, no bitfields, all scalar members
        let eligible = record.members.allSatisfy { m in
            m.name != nil && m.bitOffset == nil && m.bitWidth == nil && isScalarType(m.type)
        }
        guard eligible, !record.members.isEmpty else { continue }
        candidateVars[id] = v
        candidateRecords[id] = record
    }

    guard !candidateVars.isEmpty else { return function }

    // ── Phase 2: Disqualify unsafe uses ─────────────────────────────

    var disqualified: Set<Int> = []

    // Track member temp → base struct id
    var memberTempToBase: [Int: Int] = [:]
    // Track which member temps have verified load/store at i+1
    var verifiedMemberTemps: Set<Int> = []

    // First pass: find member instructions and build temp mapping
    for block in blocks {
        let instrs = block.instructions
        for i in 0..<instrs.count {
            let instr = instrs[i]
            if case .member(let dest, let base, _, _) = instr,
               case .variable(_, let baseId, _) = base,
               candidateRecords[baseId] != nil {
                memberTempToBase[dest.id] = baseId
                // Verify next instruction is load/store using this temp
                if i + 1 < instrs.count {
                    let next = instrs[i + 1]
                    switch next {
                    case .load(_, let addr):
                        if case .variable(_, let aid, _) = addr, aid == dest.id {
                            verifiedMemberTemps.insert(dest.id)
                        }
                    case .store(let addr, _):
                        if case .variable(_, let aid, _) = addr, aid == dest.id {
                            verifiedMemberTemps.insert(dest.id)
                        }
                    default:
                        break
                    }
                }
                if !verifiedMemberTemps.contains(dest.id) {
                    disqualified.insert(baseId)
                }
            }
        }
    }

    // Build set of safe uses: member temps used in verified member+load/store patterns
    // A candidate is safe if it ONLY appears in:
    //   1. member(dest:%t, base:candidate, ...) followed by load/store of %t
    //   2. assign(dest:candidate, src:intConst(0)) — memzero
    //   3. assign(dest:candidateA, src:candidateB) — struct copy
    // Everything else disqualifies.

    // Collect all uses of each candidate
    for block in blocks {
        for instr in block.instructions {
            switch instr {
            case .member:
                break // handled in first pass

            case .assign(let dest, let src):
                // assign(dest:candidate, src:intConst(0)) — memzero OK
                if candidateRecords[dest.id] != nil {
                    if case .intConst(0, _) = src {
                        // Safe
                    } else if case .variable(_, let srcId, _) = src,
                              candidateRecords[srcId] != nil {
                        // struct copy — safe for both sides (fixpoint handles propagation)
                    } else {
                        disqualified.insert(dest.id)
                    }
                }
                // src is a candidate but dest is not → struct escapes
                if case .variable(_, let srcId, _) = src,
                   candidateRecords[srcId] != nil,
                   candidateRecords[dest.id] == nil {
                    disqualified.insert(srcId)
                }

            case .addressOf(_, let src):
                if case .variable(_, let id, _) = src {
                    if candidateRecords[id] != nil {
                        disqualified.insert(id)
                    }
                    if let baseId = memberTempToBase[id] {
                        disqualified.insert(baseId)
                    }
                }

            default:
                // For all other instructions, any candidate in operands is disqualified
                for op in instr.operands {
                    if case .variable(_, let id, _) = op, candidateRecords[id] != nil {
                        // Check it's not a member base (already handled)
                        if case .member(_, let base, _, _) = instr,
                           case .variable(_, let bid, _) = base, bid == id {
                            // This is the member base — safe
                        } else {
                            disqualified.insert(id)
                        }
                    }
                }
            }

            // Also check dest of any instruction — if it writes to a candidate
            // outside of assign (handled above), disqualify
            if let dest = instr.dest, candidateRecords[dest.id] != nil {
                switch instr {
                case .assign: break // handled above
                case .member: break // member dest is a temp, not the struct itself
                default: disqualified.insert(dest.id)
                }
            }
        }

        // Check phi nodes
        for phi in block.phis {
            if candidateRecords[phi.dest.id] != nil {
                disqualified.insert(phi.dest.id)
            }
            for (_, value) in phi.args {
                if case .variable(_, let id, _) = value, candidateRecords[id] != nil {
                    disqualified.insert(id)
                }
            }
        }

        // Check terminator operands
        for op in block.terminator.operands {
            if case .variable(_, let id, _) = op, candidateRecords[id] != nil {
                disqualified.insert(id)
            }
        }
    }

    // Struct copy fixpoint: if assign(A, B) and B is disqualified, A must be too
    var changed = true
    while changed {
        changed = false
        for block in blocks {
            for instr in block.instructions {
                if case .assign(let dest, let src) = instr,
                   case .variable(_, let srcId, _) = src,
                   candidateRecords[dest.id] != nil,
                   candidateRecords[srcId] != nil {
                    if disqualified.contains(srcId) && !disqualified.contains(dest.id) {
                        disqualified.insert(dest.id)
                        changed = true
                    }
                    if disqualified.contains(dest.id) && !disqualified.contains(srcId) {
                        disqualified.insert(srcId)
                        changed = true
                    }
                }
            }
        }
    }

    // Remove disqualified
    for id in disqualified {
        candidateVars.removeValue(forKey: id)
        candidateRecords.removeValue(forKey: id)
    }

    guard !candidateRecords.isEmpty else { return function }

    // ── Phase 3: Create scalar variables ────────────────────────────

    // Find max existing ID across locals, params, AND all variable operands
    // (globals/string literals may have positive IDs not in locals/params).
    var maxId = 0
    for v in function.locals {
        if case .local(let id) = v.storage { maxId = max(maxId, id) }
    }
    for v in function.params {
        if case .local(let id) = v.storage { maxId = max(maxId, id) }
    }
    for block in blocks {
        for instr in block.instructions {
            for op in instr.operands {
                if case .variable(_, let id, _) = op, id > 0 { maxId = max(maxId, id) }
            }
            if let d = instr.dest, d.id > 0 { maxId = max(maxId, d.id) }
        }
        for phi in block.phis {
            if phi.dest.id > 0 { maxId = max(maxId, phi.dest.id) }
            for (_, val) in phi.args {
                if case .variable(_, let id, _) = val, id > 0 { maxId = max(maxId, id) }
            }
        }
        for op in block.terminator.operands {
            if case .variable(_, let id, _) = op, id > 0 { maxId = max(maxId, id) }
        }
    }

    struct FieldInfo {
        let memberName: String
        let offset: Int32
        let scalarPlace: Place
        let scalarVar: CVar
    }

    // Map struct id → [FieldInfo]
    var fieldMap: [Int: [FieldInfo]] = [:]
    var newVars: [CVar] = []

    for (id, record) in candidateRecords {
        let baseName = candidateVars[id]!.name
        var fields: [FieldInfo] = []
        for member in record.members {
            guard let memberName = member.name else { continue }
            maxId += 1
            let newId = maxId
            let place = Place(name: "\(baseName).\(memberName)", id: newId, type: member.type)
            let cvar = CVar(name: "\(baseName).\(memberName)", type: member.type,
                           storage: .local(id: newId))
            fields.append(FieldInfo(memberName: memberName, offset: Int32(member.offset),
                                   scalarPlace: place, scalarVar: cvar))
            newVars.append(cvar)
        }
        fieldMap[id] = fields
    }

    // ── Phase 4: Rewrite instructions ───────────────────────────────

    var newBlocks: [Block] = []

    for block in blocks {
        let instrs = block.instructions
        var newInstrs: [Instr] = []
        var i = 0

        while i < instrs.count {
            let instr = instrs[i]

            // Pattern: member + load → assign from scalar
            if case .member(let dest, let base, let name, _) = instr,
               case .variable(_, let baseId, _) = base,
               let fields = fieldMap[baseId],
               i + 1 < instrs.count {
                let next = instrs[i + 1]
                if case .load(let loadDest, let addr) = next,
                   case .variable(_, let aid, _) = addr, aid == dest.id,
                   let field = fields.first(where: { $0.memberName == name }) {
                    newInstrs.append(.assign(dest: loadDest, src: field.scalarPlace.asOperand))
                    i += 2
                    continue
                }
                if case .store(let addr, let val) = next,
                   case .variable(_, let aid, _) = addr, aid == dest.id,
                   let field = fields.first(where: { $0.memberName == name }) {
                    newInstrs.append(.assign(dest: field.scalarPlace, src: val))
                    i += 2
                    continue
                }
            }

            // Pattern: assign(dest: structVar, src: intConst(0)) → memzero → per-field zero
            if case .assign(let dest, let src) = instr,
               let fields = fieldMap[dest.id] {
                if case .intConst(0, _) = src {
                    for field in fields {
                        newInstrs.append(.assign(dest: field.scalarPlace,
                                                src: zeroForType(field.scalarPlace.type)))
                    }
                    i += 1
                    continue
                }
                // Pattern: assign(dest: A, src: B) both SROA'd → per-field copy
                if case .variable(_, let srcId, _) = src,
                   let srcFields = fieldMap[srcId] {
                    for (dstField, srcField) in zip(fields, srcFields) {
                        newInstrs.append(.assign(dest: dstField.scalarPlace,
                                                src: srcField.scalarPlace.asOperand))
                    }
                    i += 1
                    continue
                }
            }

            newInstrs.append(instr)
            i += 1
        }

        newBlocks.append(Block(label: block.label, phis: block.phis,
                              instructions: newInstrs, terminator: block.terminator))
    }

    // ── Phase 5: Update locals ──────────────────────────────────────

    let sroaIds = Set(candidateRecords.keys)
    let updatedLocals = function.locals.filter { v in
        if case .local(let id) = v.storage { return !sroaIds.contains(id) }
        return true
    } + newVars

    return Function(name: function.name, returnType: function.returnType,
                   params: function.params, locals: updatedLocals,
                   blocks: newBlocks, isStatic: function.isStatic,
                   isInline: function.isInline)
}

// MARK: - Helpers

private func isScalarType(_ type: CType) -> Bool {
    switch type {
    case .structType, .unionType, .array, .vla: return false
    default: return true
    }
}

private func zeroForType(_ type: CType) -> Operand {
    switch type {
    case .float:  return .floatConst(0.0, type: .float)
    case .double: return .floatConst(0.0, type: .double)
    default:      return .intConst(0, type: type)
    }
}
