# RC-01 sealing vs. the `vm_compute` witness — a conflict for the reviewer

**Status:** open question for adjudication. Raised by the implementer under rule 2 (a conflict between governing
prose and canonical code is a defect to report and resolve, never a precedence shortcut) and rule 10 (name the
conflict; do not implement an alternative autonomously).

**Candidate:** `HEAD` = `1a6a893` (RC-01 core at `e100f84`). Synthesis under implementation: `b1512c48`
(RC-01..RC-09).

---

## 1. What is already done (context)

RC-01's core is landed, green through the full gate, byte-identical, pushed (`e100f84`):

- One structural per-file fold, `Index.occ_file`, is the sole occurrence authority. Each node's member carries
  its exact source view (a shared `Syntax` fragment), in ascending preorder id order.
- `Index.meta_of` reads a cheap **viewless** `Meta` index derived from that same fold (`occ_meta_table`);
  `Index.member_of` reads the retained members; `occurrences_file := occ_file`.
- Deleted: `source_occurrence_at` (the source re-walk), the `build_*` Meta-threading builders, the `end_*` /
  `next_*` subtree-end peers, `all_ids`/`pos_seq`, and the entire agreement forest that reconciled the two old
  authorities. **Index.v: 2153 → 532 lines.**
- The `vm_compute` "wall" the previous two cycles attributed to a toolchain limit is gone **in-model** — no
  toolchain change, nothing added to the TCB. The old OOM was the `PositiveMap` of view-bearing occurrences;
  the plain-list fold reduces to the same normal form as the old lazy oracle.

This resolves RC-01 items 1, 2, 3, 6, 7 and the deletion inventory. The conflict below is about item 5.

## 2. The requirement in conflict

RC-01 "Required outcome" item 5, and the deletion inventory (synthesis lines ~175, ~362, ~605):

> Constructors for ProgramIndex, FileRef, NodeRef, occurrence members, and role refinements are sealed. …
> Remove public raw constructors `MakeOccurrence`, `MakeIndex`, `MakeFileRef`, and `MakeNodeRef` from the
> client surface; replace them with sealed exact construction. … Public negative clients cannot name raw
> occurrence, index, file-ref, node-ref … constructors.

## 3. The conflicting fact

The witness proves admissibility of the demo program **by computation**:

```coq
(* e2e/Witness.v *)
Definition demo_valid : Compilable.Admissible demo_program.
Proof. split; vm_compute; reflexivity. Qed.
```

`Compilable.Admissible p := all_diags p = [] /\ all_boundaries p = []`, and `all_diags` /`all_boundaries`
(`Compilable/Facts.v`) are `flat_map occ_diag (Index.occurrences_file (snd b))` over the file bindings, where
`occ_diag` reads `Index.view_expr` / `occurrence_kind` / `occurrence_role` and resolves names via
`Compilable.Bindings` (which projects `Index.Snapshot.NodeRef`s). **The occurrence layer and the reference API
are inside the `vm_compute` reduction path.** The rejection-fixture controls (bad programs proved `Rejected`)
reduce the same way.

The existing seals do not have this property: `Compilable`/`Safe`/`Emit` seal their constructors
(`MkDecision`, `MkCore`, `Safe.certify`, `Emit.of_safe`, the mint) and those types are opaque, but **none of
them is `vm_compute`-reduced inside a `reflexivity` proof** — the witness reduces `all_diags` (unsealed) and
merely *constructs* `demo_compiled := program_of demo_program demo_valid` as a term. The occurrence layer is
the unique surface that is both *required to be sealed* and *computed*.

## 4. Why sealing breaks it (mechanism)

Hiding a record's constructor in Rocq means abstracting the type through a `Module Type` (a `Parameter`, or a
signature that omits the constructor). An abstracted/ascribed definition has **no unfoldable body**; under
`vm_compute` it compiles to an *accumulator* (a stuck symbolic value). A `flat_map` / diagnostic fold over an
accumulator-list cannot produce a concrete list — the VM accumulates an ever-growing symbolic term instead of
reducing, and memory blows up. This is the same accumulator cliff the map exhibited (395–771s → `Killed`).

## 5. Empirical confirmation

A throwaway scratch sealed *only* the enumeration and left everything else identical:

```coq
Module Type SEALTEST. Parameter occf_sealed : Syntax.File -> list (positive * Occurrence). End SEALTEST.
Module SealTest : SEALTEST. Definition occf_sealed := occ_file. End SealTest.
Definition occurrences_file (f : Syntax.File) : list (positive * Occurrence) := SealTest.occf_sealed f.
```

Result under a forced-fresh `make emit`: the witness compiled Witness.v and then **`Killed` (OOM) at ~788s**
building `demo_valid` — the historical cliff, back verbatim. Sealed occurrences behave to the VM exactly like
the opaque map did. The scratch was reverted; `HEAD` is clean.

## 6. The options

- **A — keep the occurrence/index/ref layer constructor-transparent.** The `vm_compute` witness requires it.
  Cost: RC-01 item 5's constructor-hiding stays unmet for `Occurrence`/`ProgramIndex`/`FileRef`/`NodeRef`
  (documented, with this reason); every other seal (Compilable/Safe/Emit) stands. Residual risk is narrow: a
  client could name `MakeOccurrence` and fabricate a *descriptive* occurrence, but the certified `compile` path
  only ever builds occurrences via `occ_file`, so a fabricated occurrence cannot enter a `Compiled`/`Safe`/
  `Image` result — the exposure is confined to a client's own diagnostic queries, not the certified output.

- **B — re-prove `Admissible` (and the rejection controls) from the sealed API's exposed *theorems*** instead
  of by `vm_compute`, so the occurrence layer can be opaque-sealed. Cost: a system-wide switch of the
  demo-validation strategy from computational (`vm_compute; reflexivity`) to lemma-based. Every `vm_compute`
  proof that currently reduces through the occurrence layer — `demo_valid` plus each negative-control fixture —
  must be re-derived from exposed lemmas about `occ_file`/`occ_diag`/resolution. Substantial, and it changes a
  discipline used well beyond this root.

- **C — a technique we have not found.** We do not believe Rocq offers "opaque constructor, reducible
  projections/fold": module abstraction is all-or-nothing per definition, and `vm_compute` ignores `Opaque`
  hints (it reduces transparent bodies regardless), so neither gives constructor-hiding with a live `vm_compute`
  witness. If the reviewer knows a construction that does, that resolves this cleanly.

## 7. The question

Does RC-01 item 5's sealing requirement stand **for the computed occurrence/reference layer** — mandating B (or
C) — or is A acceptable (relax constructor-hiding for exactly this layer, keep every other seal, and record the
`vm_compute`-witness reason)?

Implementer's lean: **A**. The occurrence layer is internal descriptive metadata, not a certified output; its
constructor-sealing is far less soundness-critical than the Compiled/Safe/Emit seals, and B pays a system-wide
cost (abandoning computational demo validation) for a benefit confined to non-certified client queries. But the
synthesis clearly intended sealing here, and computational validation is load-bearing elsewhere, so this is put
to the reviewer rather than decided in code.

## 8. A smaller, independent note (not the fork)

RC-01 item 5 also says lookup "does not mint a peer from a Boolean proof." Today `Index.Snapshot.node_meta` is
`option_get (meta_of …) (occ_ofb_some … (nr_valid r))` — it projects the *retained* `meta_of` value using the
carried validity proof; it returns retained data, not a fabricated peer. If the reviewer nonetheless wants the
reference to project the retained *member* (view included) rather than re-read `meta_of`, that is a small,
self-contained change (`member_of` is total under `occ_ofb = true`) and is independent of the fork above.
