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
   of the DAG (ZArith/SpecFloat only).
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
5. **GoPanic.v** (runtime panic payloads), then **GoSlice.v / GoHeap.v / GoMap.v /
   GoChan.v / GoSession.v** (ops + their laws, each deleting its builtins section),
   then whatever remains is deleted with the monolith and preamble's `Require Export`.

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
