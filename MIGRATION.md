# Legacy → certified-emission migration ledger

Live status of starving `plugin/go.ml` (policy: `ARCHITECTURE.md` §3). A row is **covered**
only under §3's five-layer definition; anything less is **partial**. Legacy demos live in
`main.v` (the golden suite for the still-live plugin output). Keep this file SHORT: one row
per feature group; compress when it grows.

| Feature group | Legacy location (main.v) | Certified equivalent | Status | Deletion action |
|---|---|---|---|---|
| Constant print/println, panic, defer-call, return, blank-assign | interleaved through most demos | emission `GoEmit.demo_emit_bytes` + `print_emit_bytes` + `panic_emit_bytes`; behavior `gosem_category_coverage` (exact runs for every construct in this row) + `gosem_sound`; gate `GoSemSafe.panic_free_gate` | covered — for supported emission and modeled-or-rejected behavior, NOT BehaviorSafe: a denoted `panic` is rejected by the panic-free behavioral gate | no standalone legacy demo exists for this class alone; nothing deletable yet |
| Short declarations `x := e` | `vlet_demo`, locals uses everywhere | GoSafe `ScopeS` gate (admitted); denotation ABSENT (`shortdecl_supported_undenoted`) | partial | hold until the env statement layer denotes (plans/gosem-locals.md) |
| Slice/map literals, `len`/index (const class) | parts of `slice_demo`/`map_demo`/`builtins_demo` | GoEmit demo; GoSem runtime tiers (`len` and index denote, incl. the OOB panic) | partial (runtime mutation/append/copy unported) | hold |
| `cap` | parts of `slice_makecap_demo` etc. | supported + printed (`GoEmit.demo_prog`); GoSem ABSENT — pinned: `cap_slicelit_e` ∈ `undenoted_frontier`, `undenoted_frontier_pinned` | partial | hold; flips only with a cap denotation arm |
| Control flow (if/for/goto/labels/switch forms) | ~25 demos (`sign`…`irreducible`, `tsw*`, `*_sw*`) | none (no GoAst statements for control flow) | unported | hold |
| Numerics (int63/i64/u64/narrow/floats/FConst/complex) | ~60 demos | none beyond const folds | unported | hold |
| Strings/bytes/runes (runtime ops, range) | ~12 demos | `EStr`/`len` const class only | unported | hold |
| Structs/methods/interfaces/generics/enums/deftype | ~45 demos | none (no decls in GoAst) | unported | hold |
| Pointers/refs/heap | ~12 demos | none | unported | hold |
| Channels/goroutines/select/sessions | ~15 demos | none (proof-only models: cmd.v/unified.v) | unported | hold |
| Functions/recursion/multiret/variadic/captures/modules | ~25 demos | none (no func decls in GoAst) | unported | hold |

No legacy demo is deletable today: every group pins live plugin branches that still produce
`main.go`, and the one covered class has no standalone legacy demo. The first deletions
unlock when a certified feature lands that a whole legacy demo tests exclusively — that
patch names and deletes it (§3).
