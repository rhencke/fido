# The builtins.v split — wave roadmap (boss directive 2026-07-05; CLAUDE.md law governs)

builtins.v is FROZEN raw ore being mined into final-purpose modules; the monolith and
preamble's global re-export die at the end.  No compatibility façade at any step.

## Landed

`GoCFG.v` (CFG semantic authority) + `GoExtractionHooks.v` (plugin-lowered names only) +
plugin ownership by exact-dirpath whitelist (`from_model`/`model_dirpaths`, extended per
wave; `from_gocfg`/`from_hooks` separate).  Then, in dependency-honest order (each wave:
exact-marker cut → module with honest header → explicit imports by USE, no façade →
dune + whitelist bump → `make check` golden byte-identical → commit → external review,
BLOCKs closed structurally):

1. `GoNumeric.v` — the numeric records + wrapping lemmas + spec_float floats (float
   layer folded in; no separate GoFloat.v), and since wave 10 the ENTIRE pure numeric
   op layer (fixed-width ops/bitwise/shifts/conversions, evidence-carrying div/rem,
   GoI64/GoU64 ops + laws, untyped consts, int64→float64): records and ops are ONE
   authority.  168 qualified `builtins.<op>` refs rewrote to `GoNumeric.<op>`;
   main.v's module-identity ownership demo now collides with the REAL owner name.
2. `GoRuntimeTypes.v` — carriers + `GoTypeTag` + `GoAny` + `Tagged` + `zero_val` +
   runtime comparability (`key_eqb`/`struct_eqb`).
3. `GoEffects.v` — World/Outcome/IO/run_io/ret/bind/panic/catch + `io_eq` setoid +
   effect laws + Hoare layer.  `run_io_inj` (the one funext touch) QUARANTINED to
   concurrency.v — the certified path reasons over `io_eq` only.
4. `GoPanic.v` — the runtime panic payloads (digits + GoRuntimeTypes only).
5. `GoSlice.v` — the PURE-LIST slice/array model + gated `slice_get_bounds_surface`
   (loud aliasing caveat; the aliasing-capable rep is GoHeap's `SliceH`).
6. `GoMap.v` (735198e) — Go maps over the world heap.
7. `GoChan.v` (123a276) — channels + the whole go-mem story (happens-before, races,
   close⤳zero, fork edge); ForkEvent ctors renamed Fk* to kill import-order shadowing.
8. `GoHeap.v` (ee184b7) — the ref heap: locals (`Ref` + `ref_sel`/`ref_upd` selectors),
   `ValidWorld`, pointers + `&x`, closed-world nil-safety, `SliceH`
   aliasing handles, `HStruct` bundles + chan/ref frame lemmas, generic
   `StructRep`/`GSPtr` struct heap.  The STRUCT CHANNELS demo stays in builtins.
9. `GoSession.v` (6f9c779) — Proto/dual + the linear forge-proof `Sess` indexed monad +
   `run_session`; builtins does NOT import it; `builtins.PSend`-style qualified refs in
   concurrency.v/unified.v rewrote to `GoSession.*`.
10. numeric op layer → `GoNumeric.v` (ca28cba; see 1).
11. `GoString.v` — string ops, []byte/string conversions, the faithful UTF-8 rune view,
    string comparison + lexicographic order, the string switch, `range` over a string,
    and the sealed `ComparableW` generic-comparable witnesses (anchored on `str_eqb`).

Reviews 9/10 also enforced: imports honest by USE (the never-used GoChan/GoMap imports
in the cmd/GoSem universe and builtins' dead digits import are gone) and location prose
that tells the truth everywhere (plugin comments state the `model_dirpaths` ownership
rule, not "lives in builtins.v").

12. print/println + `w_log` + `output_distinguishes_programs` + block-scoped
    `with_defer` (+ its two proofs) → `GoEffects.v` (it owns IO/output/panic/catch);
    `w_init` moved DOWN from GoHeap to GoEffects (a pure World constant — the World
    authority owns it); func-scoped `defer_call` → `GoExtractionHooks.v` (its model
    body is a loud-panic plugin-hook guard, not certified semantics — CFG law), with
    its recognizer re-pinned from `from_model` to `from_hooks`.

13. `GoSwitch.v` — ONE module for every switch/assert dispatch combinator: type
    assertions (`type_assert`/`type_assert_safe` + theorems), the type-switch family,
    and the int64 AND string expression switches (`str_switch2/3` pulled over from
    GoString — one authority).  In the same wave the pure tails went home: min/max +
    the faithful float min/max + f64 `>`/`>=`/`!=` → GoNumeric; `Variadic`/`vararg` +
    the array `==` deciders (`arr_eqb` family) → GoSlice.

## Remaining ore (~280 lines) — the endgame carve

- Complex numbers (~160 lines) — GoComplex.v.
- The STRUCT CHANNELS demo (~45 lines) — GoChan.v candidate (channel-of-tuple theorem).
- `range` over a slice → GoSlice.v; integer `range` → decided at cut time.
- Then DELETE builtins.v and preamble's `Require Export builtins` — every consumer
  imports narrowly; the split is complete when the monolith is GONE.

## Acceptance per wave

`make check` green, golden byte-identical, gated surfaces zero-axiom, plugin ownership
genuinely extended (never pretended), no doc contradicting the layout.

## Deferred behind the split

The `run_cblocks` emitter connection (spec in plans/fuel-free.md).
