# Plan: zero of our own axioms

**Goal.** Eliminate every `Axiom` *we* declare inside the closed world, replacing each
with a `Definition`/`Theorem` built on a **concrete model** of the world.  Remaining
trust must be only **named external boundaries** — Coq's kernel, the kernel primitives
`PrimInt63`/`PrimFloat`, and (later) per-library *documented contracts* when we leave
the closed world.

**Definition of done (this plan's scope).** `grep -cE "^Axiom |^Parameter " builtins.v`
= 0, with the honest holdouts (below) either modeled or reclassified as an explicit
external boundary, and `make check` (golden) **unchanged at every step**.

**Current state (2026-06-15).** 108 axioms, *all* in `builtins.v`.  `concurrency.v`,
`main.v`, `preamble.v` are already axiom-free.  So the entire target is `builtins.v`.

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
