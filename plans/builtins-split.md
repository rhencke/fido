# The builtins.v split — wave roadmap (boss directive 2026-07-05; CLAUDE.md law governs)

builtins.v is FROZEN raw ore being mined into final-purpose modules; the monolith and
preamble's global re-export die at the end.  No compatibility façade at any step.

**Landed:** `GoCFG.v` (the CFG semantic authority) + `GoExtractionHooks.v` (plugin-lowered
names only) + plugin ownership re-pinned (`from_gocfg`/`from_hooks`).

## The dependency-honest wave order

The boss's sketch says "GoEffects next"; the DEFINITIONAL dependencies force its
prerequisites out first — `World`'s fields need the heap-cell types, whose cells need
`GoTypeTag`/`GoAny`, whose tag enumerates EVERY carrier (numerics, floats, string, slice,
chan, map, the recursive demo structs).  Every op in builtins is IO-typed, so GoEffects
must sit BELOW builtins in the import DAG — never import it (GoCFG-style interim imports
would be circular here).

1. **GoNumeric.v / GoFloat.v** — the Z-carried fixed-width wrappers (`GoI64`/`GoU8`/…,
   `GoInt`/`GoUint`) + wrapping lemmas; `spec_float` carriers + canonicalization.  Bottom
   of the DAG (ZArith/SpecFloat only).  EXECUTION SPEC (recon 2026-07-05): the region is
   builtins.v ~19–660 with the float layer FIRST (`SpecFloat` Export at ~80, `GoFloat64`
   notation ~85, `renorm`, f32 at ~440–455, float64 ops ~456+) and the fixed-width
   records after (`GoI64` ~586, u8..u64/i8..i32, `GoInt`/`GoUint` + `intwrap`); the
   carrier one-liners `GoString` (~62) and `GoSlice` (~69) are INTERLEAVED — they are
   NOT numeric and stay behind for wave 2 (GoRuntimeTypes) unless trivially hoisted.
   PLUGIN: dozens of the ~57 `from_builtins`-pinned recognizers are numeric
   (`fixed_width_op`, `is_any_i64_op`/`u64`/`int`, `int_lit`/`u64_lit`/`uint_lit`
   folds, wrap ctors, zarith helpers).  Per-recognizer re-pinning each wave would be
   churn; instead generalize ownership ONCE: `from_model r` = exact-dirpath membership
   in the SEMANTIC-module whitelist ({Fido.builtins} ∪ landed semantic modules,
   extended per wave) — preserves the anti-shadow ownership property (exact Fido-owned
   dirpaths) and keeps hooks separate (`from_hooks` stays its own check; the boss's
   hooks-vs-semantics split remains real).  `named`/`named_in` switch to `from_model`.  ★LANDED (2c9134e): `from_model` +
   `model_dirpaths` whitelist are live (singleton today); each wave = whitelist bump +
   the module move.  IMPORT SWEEP (no façade): the numeric/float names are used outside
   builtins ONLY by `main.v`, `GoSemCore.v`, `GoSem.v`, `GoSemDenote.v`,
   `concurrency.v` (GoAst/GoTypes/GoPrint hits are comments) — those five files plus
   builtins.v gain `From Fido Require Import GoNumeric GoFloat.` in the cut.
2. **GoRuntimeTypes.v** — the carrier TYPE seeds it enumerates (`GoString`, `GoSlice`,
   `GoChan`, `GoMap` type-level; `ListNode`/`ChanBox`) + `GoTypeTag` + `GoAny` + `Tagged`
   + `zero_val` + comparability + `tag_eq`.  (If a structure module later wants its type
   seed, it moves then — one authority at every step.)
3. **GoEffects.v** — `RefCell`/`RefHeap`/`ChanCell`/`ChanHeap`/`MapCell`/`MapHeap` (they
   exist only as `World` fields; the structure modules own the OPS later), `World`,
   `Outcome`, `IO`, `run_io`, `ret`, `bind`, `panic`, `catch`, `io_eq` + the setoid
   instances + effect laws + the Hoare layer.  ★`run_io_inj` (the ONE funext touch) does
   NOT come along: challenge it — builtins' own uses get replaced by `io_eq` reasoning
   where possible; the residue moves to the proof-only universe that wants Leibniz-IO
   (concurrency.v/unified.v), explicitly OUTSIDE the MVP theorem surface.
4. **builtins.v shrinks** — imports GoNumeric/GoFloat/GoRuntimeTypes/GoEffects; the
   monolith is then the op layer only.
5. **GoPanic.v — LANDED** (runtime panic payloads; digits+GoRuntimeTypes only).
6. **Structure modules** (ops + laws, each deleting its builtins section):
   **GoSlice.v** first — recon (2026-07-06): TWO families in builtins.  (a) the PURE-LIST
   family (~builtins 2600-2860): `append`/`slice_of_list`/`go_list_nth`/`slice_get` (+ the
   GATED `slice_get_bounds_surface` — its PROGRESS gate name becomes
   `GoSlice.slice_get_bounds_surface`)/`slice_at_ok`/`len_agrees_structural` and the array
   family `arr_lit`/`arr_get_ok`/`arr_set` — self-contained over
   GoEffects+GoPanic+GoRuntimeTypes; GoSlice.v takes THIS family with the aliasing caveat
   stated loudly (pure lists are sound only for single-goroutine no-aliasing programs).
   (b) the HEAP-BACKED `SliceH` family (~4000-4100, shared backing cells, `subslice`
   aliasing) is entangled with the ref-heap machinery and moves with the HEAP wave, where
   the aliasing-capable representation lives.  ★PIECE MAP (the op layer accreted
   demo-first, so the pure-list family is NON-CONTIGUOUS — cut piece by piece, verify
   each): P1 `len`+`len_agrees_structural`+the no-value-cap note+`append` (~2600-2624);
   P2 `slice_of_list` (~2683-2686); P3 `go_list_nth`+`slice_get`+the gated
   `slice_get_bounds_surface`+`slice_at_ok` (~2711-2800); P4 the array family
   `GoArray`/`arr_lit`/`arr_get_ok`/`arr_set` (~2802-2851); P5 `for_each`/`slice_fold`
   (~4720+, iteration combinators — verify their deps before including).  Between the
   pieces sit go_min/go_max and float comparison helpers — they STAY in builtins.
   GoSlice.v imports GoNumeric+GoRuntimeTypes+GoEffects+GoPanic; whitelist +=
   Fido.GoSlice; the PROGRESS gate line renames to `GoSlice.slice_get_bounds_surface`.  Then GoHeap.v / GoMap.v / GoChan.v /
   GoSession.v; then whatever remains is deleted with the monolith and preamble's
   `Require Export`.

Acceptance per wave: `make check` green, golden byte-identical (module moves must not
change emission — the plugin's `from_builtins` ownership follows the definitions:
recognizers re-pin per wave exactly as `from_gocfg`/`from_hooks` did), all gated
surfaces still zero-axiom, no doc contradicting the layout.

## Plugin note (per wave)

`from_builtins` pins every recognizer to `Fido.builtins`.  Each wave that moves
plugin-recognized names adds an exact-dirpath ownership check for the new module and
re-pins ONLY the moved recognizers — the split must be real in the trusted recognition
scheme every step, never pretended.

## Deferred behind the split

The `run_cblocks` emitter connection (spec in plans/fuel-free.md) resumes after wave 3
(its hook lands in GoExtractionHooks.v; its gate lemmas in GoCFG.v/main.v).
