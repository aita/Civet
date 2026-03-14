# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Civet is a C compiler written in Swift that compiles C source code to x86-64 assembly (AT&T syntax). It uses chibicc (vendored as a git submodule) for parsing/preprocessing C, then lowers through multiple IRs to produce assembly.

## Build & Test Commands

```bash
swift build                    # Build (requires Swift 6.2+)
swift build -c release         # Release build

./test.sh                      # Run all chibicc test suite files
./test.sh string enum          # Run specific chibicc tests
./test.sh --inline             # Run inline snippet tests (Tests/run.sh)
./t.sh <file.c>                # Quick single-file test
./t.sh string                  # Quick test of Vendor/chibicc/test/string.c

bash Tests/run.sh              # Full test suite (inline snippets + chibicc tests)
bash Tests/run.sh --filter foo # Filter tests by name pattern
```

Binary is output to `.build/debug/Civet`. Usage: `Civet <file.c>` outputs assembly to stdout.

## Compilation Pipeline

```
C Source → [chibicc parser] → Syntax → Tree → COIL → Machine → x86-64 Assembly
```

### Module dependency graph (Package.swift targets)

```
ChibiCC (C) ─→ SyntaxMapper ─→ Civet (executable)
Common ─→ Syntax ─→ Tree ─→ COIL ─→ Machine ─↗
```

### IR stages and their modules

1. **Syntax** (`Sources/Syntax/`) — High-level C AST: types, expressions, statements, declarations. Closely mirrors C syntax.

2. **Tree** (`Sources/Tree/`) — Simplified semantic IR. `SyntaxConverter` lowers complex control flow (for/while/switch → if/goto), flattens expressions with synthetic temporaries (negative IDs). Only has `if` and `goto` for control flow.

3. **COIL** (`Sources/COIL/`) — Control-flow Oriented IR with basic blocks, phi nodes, and SSA form. `TreeConverter` builds the CFG, `SSABuilder` converts to SSA using the Cytron algorithm.

4. **Machine** (`Sources/Machine/`) — x86-64 machine IR. `COILConverter` lowers COIL following System V AMD64 ABI. Uses DAG-based instruction selection (`SelectionDAG.swift`, `ISelPatterns.swift`), linear scan register allocation (`RegisterAllocator.swift`), instruction legalization (`Peephole.swift`), and list scheduling (`Scheduler.swift`). `AsmPrinter` emits final assembly.

### COIL Optimization Passes (`Sources/COIL/Passes/`)

Pipeline order (iterated up to 4× until fixpoint, then loop unroll + re-optimize):

1. **SCCP** — Sparse Conditional Constant Propagation (Wegman-Zadeck)
2. **StrengthReduction** — Algebraic identities + power-of-2 lowering
3. **Reassociation** — Constant folding across expressions (`(x+3)+5 → x+8`)
4. **GVN** — Dominator-based Global Value Numbering
5. **ADCE** — Aggressive Dead Code Elimination (SSA def-use chain walk)
6. **CodeSinking** — Move instructions closer to single-use successors
7. **LICM** — Loop Invariant Code Motion
8. **DSE** — Dead Store Elimination (local)
9. **CFG Simplification** — Jump threading + block merging
10. **Loop Unrolling** — After optimization stabilizes, unroll then re-optimize

Supporting analyses: `DominatorTree` (Cooper-Harvey-Kennedy), `LoopInfo` (natural loop detection), `AliasAnalysis`, `ConstantFolding`.

### Machine-level Optimizations

- **Tail Call Optimization** — `call` + `ret` → `tailJmp` (`Peephole.swift`)
- **If-conversion** — Diamond CFG → `cmov` (`Peephole.swift`)
- **Magic Number Division** — Constant divisor → multiply + shift (`ISelPatterns.swift`, `MagicDivision.swift`)
- **Register Coalescing** — vreg-vreg copy elimination via UnionFind (`RegisterAllocator.swift`)
- **Spill Weight** — Loop-depth-aware eviction (`RegisterAllocator.swift`)
- **Stack Slot Coloring** — Non-overlapping spill slot reuse (`RegisterAllocator.swift`)

### Supporting modules

- **Common** (`Sources/Common/`) — Shared utilities (source locations)
- **SyntaxMapper** (`Sources/SyntaxMapper/`) — FFI bridge mapping chibicc's C parse tree to Syntax IR
- **ChibiCC** (`Sources/ChibiCC/`) — Swift wrapper target for the vendored chibicc C code

## COIL IR Design (Named SSA)

Current IR uses named SSA with integer-ID-based variable references:

- **`Place(name, id, type)`** — Writable destination for instructions. Negative IDs = synthetic temps. SSA versions get IDs `≤ -100_001`.
- **`Operand`** — Readable value: `.variable(name, id, type)`, `.intConst`, `.floatConst`, `.labelAddr`
- **`Instr`** — Operations with `dest: Place?` and source `Operand`s. Side-effect-only ops (`store`, `compare`, `test`, `asm`) have `dest = nil`.
- **`Phi(dest: Place, args: [(label, Operand)])`** — SSA merge at join points
- **`Block`** — `label`, `phis`, `instructions: [Instr]`, `terminator: Terminator`
- **`Function`** — `params: [CVar]`, `locals: [CVar]`, `blocks: [Block]`, cached `domTree`

All optimization passes use `[Int: ...]` dictionaries keyed by variable ID.

## Key Conventions

- Synthetic/temporary variables use negative IDs to distinguish from source-level variables
- SSA versions created by `SSABuilder` use IDs `≤ -100_001` (offset from TreeConverter temps)
- The chibicc submodule is at `Vendor/chibicc` and provides both the C parser and test suite
- Tests link against `Vendor/chibicc/test/common` which provides `assert()` and `printf` helpers
- Stack layout preserves chibicc's pre-computed offsets (`CVar.stackOffset`)

## Test Status

- 36 chibicc tests pass: alignof, alloca, arith, asm, attribute, bitfield, builtin, cast, commonsym, complit, compat, const, constexpr, control, decl, enum, extern, float, generic, initializer, literal, macro, offsetof, pointer, sizeof, stdhdr, string, struct, typedef, typeof, unicode, union, usualconv, varargs, variable, vla
- ~136+ inline Swift tests pass (EndToEndTests.swift)
- 9 optimization pass unit tests (OptimizationPassTests.swift)
- 4 peephole unit tests (PeepholeTests.swift)
- 4 tests disabled: function (long double), pragma-once (path resolution), atomic (not implemented), tls (not implemented)
