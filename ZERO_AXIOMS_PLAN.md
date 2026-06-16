# Plan: zero of our own axioms

**Goal.** Eliminate every `Axiom` *we* declare inside the closed world, replacing each
with a `Definition`/`Theorem` built on a **concrete model** of the world.  Remaining
trust must be only **named external boundaries** — Coq's kernel, the kernel primitives
`PrimInt63`/`PrimFloat`, and (later) per-library *documented contracts* when we leave
the closed world.

**Definition of done (this plan's scope).** `grep -cE "^Axiom |^Parameter " builtins.v`
= 0, with the honest holdouts (below) either modeled or reclassified as an explicit
external boundary, and `make check` (golden) **unchanged at every step**.

**DONE (2026-06-16). ZERO axioms — 108 → 0.** `grep -cE "^Axiom |^Parameter " *.v` = 0
across every theory; no `Admitted`.  `Print Assumptions` on the headline results
(`type_assert_ok`, `chan_buf_send`, `map_sel_upd_same`, `ref_sel_upd_same`) reports a
trust base of ONLY the named external boundaries — Coq's kernel `PrimInt63`/`PrimFloat`
primitives (+ `Uint63` `eqb_refl`) and stdlib `functional_extensionality`.  Golden
byte-identical at every step; Docker `make check` green.

### The final 3 (`type_assert`) — how the universe wall was crossed

`GoAny` is now Go's `interface{}` faithfully: a TAGGED pair `{A & A * GoTypeTag A}`
carrying the value AND its runtime `GoTypeTag`.  `type_assert tag a` recovers the value
via `tag_coerce` (match → return; mismatch → panic); `type_assert_ok` is a THEOREM
(`tag_coerce_refl`), and adversarial checks (`type_assert_safe_mismatch`: wrong type →
`false`, never the value) are build-gated.  The wall — a tagged `GoAny` referenced by
`TAny : GoTypeTag GoAny` is universe-inconsistent (same as a tag-carrying `GoChan`) — was
crossed by REMOVING `TAny`: a value's dynamic type is always concrete (Go flattens nested
interfaces), so `GoTypeTag GoAny` is never an actual runtime type.  The only thing given
up is typed `chan any`/`[]any` containers and "assert TO any" — a tracked, fail-loud
modeling gap, NOT an axiom.  `GoTypeTag` gained the distinct numint-wrapper tags
(`TU8`…`TI32`,`TUnit`) so every `any`-printed value is taggable; a `Tagged` typeclass
infers the tag so the ~180 existing `any x` sites are unchanged; the plugin erases the
tag from each `any` payload (emitting only the value).

**The original `(historical plan below)` is kept for the record.**

### What got concretized (108 → 3), all golden-byte-identical + Docker-verified

- **IO monad / Hoare / refs** — `World` is now a FULLY CONCRETE record
  `{ w_refs ; w_chans ; w_maps ; w_next }` of typed heaps; `ref_*` are definitions,
  read-after-write a theorem.  No `RawWorld`, no abstract residue.
- **Sessions** (7) — rigid protocol-indexed records; linearity `Fail` tests still hold.
- **Slices / strings** (3) — definitions with self-contained, stdlib-free index helpers.
- **GoChan / GoMap / zero_val** (3) — concrete phantom-location records + recursive zero.
- **Channel state** (12) — `chan_buf`/`chan_send_upd`/… + the 7 channel laws are now
  definitions + THEOREMS over `w_chans`; the element tag is threaded (GoChan can't carry
  it — universe inconsistency).  **The proven race-freedom in `concurrency.v` survives**
  the tag-threading (TInt64 through ~45 proof sites) and now rests on PROVEN channel laws.
- **Map state** (10) — definitions + THEOREMS over `w_maps`, with Go's COMPARABLE-KEY
  side conditions made HONEST (key reflexivity — false for a NaN key; `Comparable` for
  the distinct-key law), discharged by `comparable_TInt64` for the int-keyed demos.
- **run_blocks** (1) — fueled definition (the divergence idealization, like `run_io`'s
  totality); plugin still lowers it to labels+goto.
- **Allocators** (5) and **RawWorld** (1) — gone.

### The remaining 3 — `type_assert` — a genuine architectural boundary

`type_assert : GoTypeTag T -> GoAny -> IO T` must recover a value's DYNAMIC type from a
`GoAny`.  Our `GoAny = {T & T}` carries no type tag, so the recovery is unprovable —
exactly Go's runtime: an `interface{}` IS a (type, value) pair, so the faithful fix is a
TAGGED `GoAny = {T & GoTypeTag T * T}`.  But `any` is used **184×** (every `println`/
`panic`), and the printed values include the faithful numint wrappers (`GoU8`/`GoI8`/…)
which have NO `GoTypeTag` (only the carriers do).  So tagging `GoAny` requires expanding
`GoTypeTag` with ~7 new constructors (`TU8`…`TUnit`) + full ripple (`tag_eq`/`zero_val`/
`key_eqb`), a `Tagged` typeclass for inference, AND a change to the plugin's golden-
sensitive `any`/print erasure.  That is a large, high-risk change disproportionate to 3
axioms and threatening the verified 97% — so it is a **tracked, principled holdout**:
"type assertion needs the runtime type tag Go's interface carries", not an internal
shortcut.  The tagged-`any` redesign is the path when taken as a dedicated effort.

----
(historical plan below)

## The library-import caveat (deliberate, separate category)

Modeling a stdlib import (`fmt`, `strings`, `math`) means encoding its **documented
contract** as axioms (`Axiom strings_ToUpper : … + laws`), because the source is
genuinely outside our closed world — we can only *trust the doc*, not prove it.  That is
the same flavor of trust as `PrimFloat`: a **named external boundary**, chosen on
purpose, not an internal modeling shortcut.  So this plan's "zero axioms" is about the
**closed world**; crossing into a library re-introduces axioms *by design*, ideally
structured as typeclasses/interfaces so each trusted contract is small and visible.
Re-introduction there is principled and expected — it is not a regression of this goal.

## The load-bearing invariant: extraction must not change

Every op below is *recognized by name* by the plugin and lowered to a Go primitive; its
body is a **proof-only** world-semantics device that is **suppressed at extraction**
(exactly like `run_io` today).  So we replace `Axiom op : T` with
`Definition op : T := <world semantics>` while keeping the **same name and signature**,
and the plugin keeps lowering call sites to the same Go.  **`make check` (golden) MUST
be byte-identical after every phase** — that is the safety net proving we changed only
the *meaning layer*, never the emitted program.  (If a definition's body ever leaks into
the Go, that is a bug to fix in plugin suppression, not a reason to keep the axiom.)

## Honest holdouts (where "zero" needs a caveat)

1. **Functional extensionality.** With `IO A := World -> Outcome A`, proving two IO
   programs *propositionally equal* (`run_io_inj`, the monad laws) needs `funext` — a
   standard Coq-stdlib axiom.  **Avoid it** by stating those laws over *observational*
   equality `m ≈ m' := ∀ w, run_io m w = run_io m' w` instead of `=`.  Then `funext`
   never enters.  Cost: a handful of theorems read `≈`, not `=`.  Decision: use `≈`.
2. **`go_spawn` / concurrency.** `run_io` is sequential + total; faithful interleaving
   cannot be a function `World → Outcome`.  The *faithful* concurrency model is the
   calculus in `concurrency.v` (already axiom-free).  In the IO model we **define**
   `go_spawn` as a sequential approximation (run-to-completion, threading the world) —
   axiom-free, but an idealization, with faithfulness carried by the keystone.  No axiom
   needed; the limitation is documented, not assumed.
3. **`GoFloat32`.** No float32 kernel primitive (`PrimFloat` is float64).  Either model
   it (round-to-float32 over `PrimFloat`, real work) or reclassify as an explicit
   external boundary.  Decision: deferred; tracked as the one numeric holdout.

## Inventory (108 axioms, grouped) + per-group strategy

| # | Group (lines in builtins.v) | Count | Becomes | Risk |
|---|---|---|---|---|
| A | **IO core**: `IO`,`ret`,`bind`,`panic`,`catch`,`World`,`run_io`,`run_ret`,`run_bind`,`run_panic`,`run_catch`,`run_io_inj` (32–95) | 12 | concrete `World` record; `IO A := World → Outcome A`; ops are functions; the `run_*` laws + monad laws are theorems over `≈` | **High — foundational, everything depends on it. Do first.** |
| B | **Numeric/float types**: `GoInt`,`GoInt8/16/32`,`GoUint`,`GoUint8/16/32/64`,`GoFloat32` (237–288) | 10 | `Definition GoInt := int` (PrimInt63) etc.; `GoFloat32` = holdout #3 | Low (independent) — good warm-up |
| C | **Output**: `print`,`println` (575–576) | 2 | world carries an output log; both append to it | Low |
| D | **defer**: `defer_call` (621) | 1 | IO transformer in the model | Low |
| E | **Reference-type carriers**: `GoMap`,`GoChan` (625–6), `Ref` (1460) | 3 | concrete handles (indices) into the world's heaps | Med (ties to G/H/K) |
| F | **type assertion**: `type_assert`,`type_assert_ok`,`type_assert_safe` (664–676) | 3 | defined via `GoTypeTag` dispatch | Med |
| G | **Maps**: `map_empty`…`map_sel_clear` (690–814) | 25 | ops on the world's map-heap; all `run_map_*` / `map_sel_*` laws → theorems | Med (after A) |
| H | **Channels + spawn**: `make_chan`…`run_close_closed`, `go_spawn` (838–965) | 28 | ops on the world's channel-heap (`chan_send_upd := upd … (buf ++ [v])`, etc.); all `chan_*`/`run_*` laws → theorems by `upd` computation; `go_spawn` = holdout #2 | Med-High (after A) |
| I | **zero_val** (890) | 1 | `GoTypeTag`-directed default value | Low |
| J | **Slices/string-index**: `len`,`cap`,`append`,`slice_of_list`,`slice_get`,`slice_at_ok`,`str_at_ok` (1373–1443) | 7 | defined on `list` / Coq `string` (slices ≈ `list`) | Low-Med |
| K | **Refs**: `Ref`,`ref_new`,`ref_get`,`ref_set`,`ref_sel`,`ref_upd`,`run_ref_get`,`run_ref_set`,`ref_sel_upd_same` (1460–1478) | 9 | ops on the world's ref-heap; `ref_sel_upd_same`/separation → theorems by `upd` computation | Med (after A) |
| L | **CFG/goto**: `run_blocks` (1548) | 1 | defined as a block interpreter | Low-Med |
| M | **Sessions**: `Sess`,`sret`,`sbind`,`ssend`,`srecv`,`slift`,`run_session` (1627–1663) | 7 | indexed monad defined over the IO model | Med (after A,H) |

Counts: A12 B10 C2 D1 E3 F3 G25 H28 I1 J7 K9 L1 M7 = **109** (one item double-listed across
E/H/K carriers; reconcile against the live grep each phase — the grep is the source of
truth, this table is the map).

## Removal order (dependency-driven)

The world model is the spine: **A first** (nothing else can be a definition until
`World`/`IO`/`run_io` are concrete).  After A, the heap-state groups (G maps, H channels,
K refs) and the world-effect groups (C output, D defer) are independent and parallelizable.
Types (B) are independent of everything — ideal warm-up to validate the
"Axiom→Definition, golden-unchanged" loop on something low-risk.

0. **Phase 0 — warm-up (B, partial): numeric type carriers.** Turn `GoInt`/`GoUintN`/
   `GoIntN` into `Definition … := int`.  No world needed.  Proves the golden-unchanged
   loop end-to-end on the easiest target.  (`GoFloat32` deferred → holdout #3.)
1. **Phase 1 — IO core (A).** The spine.  **Refined after scoping (2026-06-15):**
   - `World` stays **abstract** here — concretising it forces channels/refs/maps
     concrete in the same step (else `chan_buf_send` is inconsistent over an empty
     world).  So define `IO A := World → Outcome A` over abstract `World`; retire
     `IO`,`ret`,`bind`,`panic`,`catch`,`run_io` and prove `run_ret`/`run_bind`/
     `run_panic`/`run_catch` by `reflexivity`.  `World` retires in Phases 2–4.
   - `run_io_inj` is used **only inside `builtins.v`** (monad/map/ref laws); nothing
     external needs it.  First cut: prove it via stdlib `functional_extensionality`
     (an EXTERNAL axiom — our code stays axiom-free, `Print Assumptions` shows stdlib
     funext, not ours).  Later refinement: restate those internal laws over `≈` to
     drop funext entirely.
   - **Extraction hurdle:** `ret`/`bind`/`panic`/`catch` are extracted by NAME; as
     transparent defs Coq may inline them (and unfold `IO A` → `World → Outcome A`),
     breaking the plugin's matchers and moving the golden.  Mitigate: `Extraction
     NoInline ret bind panic catch run_io`; if `IO`-the-type still unfolds, make it a
     one-field inductive wrapper so the name survives.  **Golden is the gate.**
2. **Phase 2 — channels (H minus go_spawn).** World channel-heap; the `chan_*` + `run_*`
   laws become theorems by `upd` computation.  `go_spawn` = holdout #2.
3. **Phase 3 — refs (K).** World ref-heap; `ref_*` laws → theorems.
4. **Phase 4 — maps (G).** World map-heap; `map_*` laws → theorems.
5. **Phase 5 — output + defer (C, D).** World output log.
6. **Phase 6 — slices + string index (J), zero_val (I), type_assert (F).** On `list`/
   `string`/`GoTypeTag`.
7. **Phase 7 — sessions (M), CFG (L), reference carriers (E).** Defined over the model.
8. **Phase 8 — holdouts.** `funext` already avoided (Phase 1, `≈`).  `go_spawn` defined
   as a sequential approximation.  `GoFloat32` modeled or reclassified as an external
   boundary.  Final `grep -c Axiom builtins.v` ⇒ 0.

## Discipline per phase

- One group per commit (or sub-group if large, e.g. maps).  `make build` green +
  `make check` **byte-identical** before committing.
- After each phase, `Print Assumptions` on a representative downstream theorem to confirm
  the group's axioms actually left the trust base (and that no new axiom — e.g. `funext`
  — sneaked in).  Record the shrinking base.
- Update this file's status column as groups land.  Update `CLAUDE.md` "Correctness debt
  Tier 1 #2 (joint consistency)" — exhibiting the concrete model *is* the consistency
  proof, so that debt closes alongside.

## Status

- [~] Phase 0 — numeric type carriers (B) — *not a freebie: opaque placeholders needing
  a model choice + extraction risk; deferred, not the warm-up.*
- [x] **Phase 1 — IO core (A) — DONE (2026-06-15).** `IO A := World -> Outcome A`;
  `ret`/`bind`/`panic`/`catch`/`run_io` are definitions; `run_ret`/`run_bind`/
  `run_panic`/`run_catch` are `reflexivity` theorems.  **11 of our 12 group-A axioms
  removed (108 → 97).**  `World` remains abstract (retires in Phases 2–4, as planned).
  `run_io_inj` is now a lemma via stdlib `functional_extensionality` — so the trust
  base gained ONE external axiom (`functional_extensionality_dep`) in place of 11 of
  ours (verified by `Print Assumptions bind_assoc`).  Extraction byte-identical (golden
  unchanged) — the plugin's name-matching survived the Axiom→Definition switch with no
  `NoInline`/wrapper needed.  *Later refinement (holdout #1): drop funext via `≈`.*
- [ ] Phase 2 — channels (H − go_spawn)
- [ ] Phase 3 — refs (K)
- [ ] Phase 4 — maps (G)
- [ ] Phase 5 — output + defer (C, D)
- [ ] Phase 6 — slices/string/zero_val/type_assert (J, I, F)
- [ ] Phase 7 — sessions/CFG/carriers (M, L, E)
- [ ] Phase 8 — holdouts (go_spawn, GoFloat32); final count = 0

## Status update (2026-06-16): 108 → 50, then genuine walls

Cleanly removed (all committed, golden byte-identical): IO core, ref ops, channel
ops, map ops, print/println/defer, append/slice_of_list, numeric carriers, len/cap.
Built `tag_eq` (decidable GoTypeTag equality with type recovery) and fixed the
`make check` staleness bug.  **108 → 50 (54%).**

The remaining ~50 are NOT more of the same — they hit type-theoretic WALLS for the
concrete typed heap:
- **`GoChan` ↔ `GoTypeTag` circularity.**  A typed channel buffer needs the channel
  to carry its tag, but `GoTypeTag` already references `GoChan` (`TChan`).  Tagged
  channels need the two MUTUALLY defined (or a separate value-tag universe).
- **Map arbitrary keys.**  `map_sel`/`map_upd` over arbitrary `K` need decidable key
  equality; `map[any]` has none.  Needs a comparable-key universe (Go requires
  comparable keys anyway), with `GoAny` keys the sticking point.
- **`GoAny` unbox.**  `type_assert`/sessions can't recover a type from `{T & T}`;
  needs `any` to carry a (typeclass-inferred) tag everywhere — pervasive.
- **Divergence.**  `run_blocks` models non-terminating control flow; no total Coq
  function is it — needs fuel or coinduction (an API change).
- `slice_get`/`slice_at_ok`/`str_at_ok` need a plugin fix for value-position `option`
  matches.

Each is solvable in principle but is a REDESIGN, and partial versions tend to
RELOCATE axioms into abstract sub-heaps rather than remove them, while touching the
proven results in `concurrency.v`.  So 50 is the honest CLEAN floor; literal 0 is a
research-grade reformulation, to be taken one wall at a time with care, not a grind.
