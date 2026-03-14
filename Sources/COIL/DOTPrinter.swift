// MARK: - DOT output

import Tree

// MARK: - Record label construction

/// Escape characters that have special meaning inside a DOT record label.

// MARK: - Text description helpers

extension Program {
    /// Returns a single Graphviz DOT digraph containing all functions as
    /// `subgraph cluster_*` sections. Functions with no blocks are skipped.
    public func dotRepresentation() -> String {
        let nonEmpty = functions.filter { !$0.blocks.isEmpty }
        guard !nonEmpty.isEmpty else { return "digraph program {}" }

        var lines: [String] = []
        lines.append("digraph program {")
        lines.append("    node [shape=record fontname=\"Courier New\" fontsize=11];")
        lines.append("    edge [fontname=\"Courier New\" fontsize=10];")
        lines.append("    compound=true;")
        lines.append("")

        for (i, fn) in nonEmpty.enumerated() {
            fn.appendDOT(to: &lines, index: i)
            lines.append("")
        }

        lines.append("}")
        return lines.joined(separator: "\n")
    }
}
extension Function {
    /// Returns a standalone Graphviz DOT digraph for this single function.
    public func dotRepresentation() -> String {
        var lines: [String] = []
        lines.append("digraph \"\(name)\" {")
        lines.append("    node [shape=record fontname=\"Courier New\" fontsize=11];")
        lines.append("    edge [fontname=\"Courier New\" fontsize=10];")
        lines.append("")
        appendDOT(to: &lines, index: 0)
        lines.append("}")
        return lines.joined(separator: "\n")
    }

    /// Append this function's DOT nodes and edges into `lines`.
    /// When used inside a `Program`, each function becomes a `subgraph cluster_N`.
    fileprivate func appendDOT(to lines: inout [String], index: Int) {
        let prefix = "\(name)_"  // namespace node IDs to avoid collisions
        let indent = "        "

        lines.append("    subgraph cluster_\(index) {")
        lines.append("\(indent)label=\"\(name)\";")
        lines.append("\(indent)style=dashed;")
        lines.append("")

        for block in blocks {
            let nodeLabel = dotRecordLabel(for: block)
            lines.append("\(indent)\"\(prefix)\(block.label)\" [label=\"\(nodeLabel)\"];")
        }

        lines.append("")

        for block in blocks {
            switch block.terminator {
            case .branch(_, let t, let e):
                lines.append(
                    "\(indent)\"\(prefix)\(block.label)\" -> \"\(prefix)\(t)\" [label=\"T\"];")
                lines.append(
                    "\(indent)\"\(prefix)\(block.label)\" -> \"\(prefix)\(e)\" [label=\"F\"];")
            default:
                for succ in block.terminator.successorLabels {
                    lines.append("\(indent)\"\(prefix)\(block.label)\" -> \"\(prefix)\(succ)\";")
                }
            }
        }

        lines.append("    }")
    }
}
private func dotRecordLabel(for block: Block) -> String {
    // DOT record labels: sections separated by |, newlines as \l (left-aligned).
    // Special chars that must be escaped: { } | < > " \
    var sections: [String] = []

    // Header: block label
    sections.append(esc(block.label))

    // Phis (if any)
    if !block.phis.isEmpty {
        let phiBody = block.phis.map { esc(describePhi($0)) + "\\l" }.joined()
        sections.append(phiBody)
    }

    // Body: instructions (may be empty)
    if !block.instructions.isEmpty {
        let body = block.instructions.map { esc(describe($0)) + "\\l" }.joined()
        sections.append(body)
    }

    // Footer: terminator
    sections.append(esc(describe(block.terminator)) + "\\l")

    return "{\(sections.joined(separator: "|"))}"
}
private func esc(_ s: String) -> String {
    s
        .replacingOccurrences(of: "\\", with: "\\\\")
        .replacingOccurrences(of: "\"", with: "\\\"")
        .replacingOccurrences(of: "{", with: "\\{")
        .replacingOccurrences(of: "}", with: "\\}")
        .replacingOccurrences(of: "<", with: "\\<")
        .replacingOccurrences(of: ">", with: "\\>")
        .replacingOccurrences(of: "|", with: "\\|")
}
private func describePhi(_ phi: Phi) -> String {
    let args = phi.args.map { "\($0.label): \(describe($0.value))" }.joined(separator: ", ")
    return "\(phi.dest.name) = phi(\(args))"
}
private func describe(_ instr: Instr) -> String {
    switch instr {
    case .assign(let d, let s):
        return "\(d.name) = \(describe(s))"
    case .binary(let d, let op, let l, let r):
        return "\(d.name) = \(describe(l)) \(describe(op)) \(describe(r))"
    case .unary(let d, let op, let s):
        return "\(d.name) = \(describe(op))\(describe(s))"
    case .call(let d, let callee, let args):
        let argList = args.map { describe($0) }.joined(separator: ", ")
        let dest = d.map { "\($0.name) = " } ?? ""
        return "\(dest)call \(describe(callee))(\(argList))"
    case .addressOf(let d, let s):
        return "\(d.name) = &\(describe(s))"
    case .load(let d, let addr):
        return "\(d.name) = *\(describe(addr))"
    case .store(let addr, let val):
        return "*\(describe(addr)) = \(describe(val))"
    case .cast(let d, let s, let to):
        return "\(d.name) = (\(describe(to)))\(describe(s))"
    case .cas(let d, let addr, let old, let new):
        return "\(d.name) = cas(\(describe(addr)), \(describe(old)), \(describe(new)))"
    case .exchange(let d, let addr, let val):
        return "\(d.name) = xchg(\(describe(addr)), \(describe(val)))"
    case .member(let d, let base, let name, _):
        return "\(d.name) = \(describe(base)).\(name)"
    case .alloca(let d, let size):
        return "\(d.name) = alloca \(describe(size))"
    case .asm(let text):
        return "asm \"\(text)\""
    case .compare(let l, let r):
        return "compare \(describe(l)), \(describe(r))"
    case .test(let v):
        return "test \(describe(v))"
    }
}
private func describe(_ term: Terminator) -> String {
    switch term {
    case .goto(let l): return "goto \(l)"
    case .branch(let c, let t, let e): return "branch \(describe(c)) ? \(t) : \(e)"
    case .return(let v): return v.map { "return \(describe($0))" } ?? "return"
    case .computedGoto(let v): return "goto *\(describe(v))"
    }
}
private func describe(_ cond: Condition) -> String {
    switch cond {
    case .eq: return "eq"
    case .ne: return "ne"
    case .lt: return "lt"
    case .le: return "le"
    case .zero: return "zero"
    case .nonZero: return "nonzero"
    }
}
private func describe(_ op: Operand) -> String {
    switch op {
    case .variable(let name, _, _): return name
    case .intConst(let v, _): return "\(v)"
    case .floatConst(let v, _): return "\(v)"
    case .labelAddr(let l, _): return "&&\(l)"
    }
}
private func describe(_ op: BinaryOp) -> String {
    switch op {
    case .add: return "+"
    case .sub: return "-"
    case .mul: return "*"
    case .div: return "/"
    case .mod: return "%"
    case .bitAnd: return "&"
    case .bitOr: return "|"
    case .bitXor: return "^"
    case .shl: return "<<"
    case .shr: return ">>"
    case .eq: return "=="
    case .ne: return "!="
    case .lt: return "<"
    case .le: return "<="
    }
}
private func describe(_ op: UnaryOp) -> String {
    switch op {
    case .neg: return "-"
    case .bitNot: return "~"
    }
}
private func describe(_ type: CType) -> String {
    switch type {
    case .void: return "void"
    case .bool: return "bool"
    case .char(let s): return s ? "char" : "uchar"
    case .short(let s): return s ? "short" : "ushort"
    case .int(let s): return s ? "int" : "uint"
    case .long(let s): return s ? "long" : "ulong"
    case .float: return "float"
    case .double: return "double"
    case .longDouble: return "long double"
    case .enumType: return "enum"
    case .pointer(let t): return "\(describe(t))*"
    case .array(let t, let n): return "\(describe(t))[\(n)]"
    case .vla(let t): return "\(describe(t))[]"
    case .function: return "fn"
    case .structType(let r): return "struct \(r.tag ?? "?")"
    case .unionType(let r): return "union \(r.tag ?? "?")"
    }
}
