import Tree

// MARK: - System V AMD64 ABI struct classification

enum ABIClass { case integer, sse, memory, noClass }

struct StructClassification {
    let classes: [ABIClass]
    var isMemory: Bool { classes.count == 1 && classes[0] == .memory }
    var eightbyteCount: Int { classes.count }
}

/// Classify a struct/union/array type according to System V AMD64 ABI.
/// Returns per-eightbyte classification for register passing.
func classifyStruct(_ type: CType) -> StructClassification {
    let size = type.size
    if size == 0 || size > 16 {
        return StructClassification(classes: [.memory])
    }
    let numEB = (size + 7) / 8
    var classes = Array(repeating: ABIClass.noClass, count: numEB)
    classifyFields(type: type, offset: 0, classes: &classes)
    // Replace remaining noClass with integer
    for i in 0..<classes.count {
        if classes[i] == .noClass { classes[i] = .integer }
    }
    return StructClassification(classes: classes)
}

private func classifyFields(type: CType, offset: Int, classes: inout [ABIClass]) {
    switch type {
    case .float:
        mergeClass(at: offset / 8, with: .sse, classes: &classes)
    case .double, .longDouble:
        mergeClass(at: offset / 8, with: .sse, classes: &classes)
    case .structType(let r):
        var fieldOffset = 0
        for m in r.members {
            let a = m.type.align
            fieldOffset = (fieldOffset + a - 1) / a * a
            classifyFields(type: m.type, offset: offset + fieldOffset, classes: &classes)
            fieldOffset += m.type.size
        }
    case .unionType(let r):
        for m in r.members {
            classifyFields(type: m.type, offset: offset, classes: &classes)
        }
    case .array(let elem, let count):
        let elemSz = elem.size
        for i in 0..<count {
            classifyFields(type: elem, offset: offset + i * elemSz, classes: &classes)
        }
    default:
        // Integer types, pointers, bool, char, short, int, long, enum
        mergeClass(at: offset / 8, with: .integer, classes: &classes)
    }
}

private func mergeClass(at idx: Int, with new: ABIClass, classes: inout [ABIClass]) {
    guard idx < classes.count else { return }
    let old = classes[idx]
    if old == new || old == .memory { return }
    if new == .memory { classes[idx] = .memory; return }
    if old == .noClass { classes[idx] = new; return }
    if old == .integer || new == .integer { classes[idx] = .integer; return }
    classes[idx] = new
}
