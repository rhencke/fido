# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.** The full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`; Git history is the detailed archive.

## Authority

- Active checkpoint: **C4** — source type names, compiler resolution, and unified numeric conversions.
- Functional contract: `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- Contract SHA-256: `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- Accepted review basis: `.review/REVIEW_BASIS.md`.
- Original C4 baseline: `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- First blocked candidate: `89b8e54634e7012612a51990756ad29a579c1b0f` (C4 Implementation Review BLOCKING).
- Second blocked candidate: `1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca` (second BLOCKING).
- Third blocked code candidate: `806ce87373e29b6980e5c3d9d274ffa86580449b` (third BLOCKING — recursive/recomputing root).
- Repair-3 baseline (current clean main): `1b38b68c104bc987744ececc36e771d8977bdbf2`.
- Human authorization: `C4-source-type-resolution-1`; repair 1 `C4-retained-facts-and-diagnostics-repair-1`;
  repair 2 `C4-typed-reference-single-path-repair-2`; repair 3 `C4-retained-table-bottom-up-repair-3` (ACTIVE).
- Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_3.md` (repairs 1 and 2 superseded — repair 1
  deleted in the first repair-2 implementation commit; repair 2 deleted in the first repair-3 implementation
  commit; git history is their archive).
- Automatic Codex review: DISABLED. The directive is the accepted human Contract Review; on repair completion
  the candidate is frozen (`review(final): C4 — freeze retained-table bottom-up candidate`) and reported for
  Rob's human Implementation Review — no Codex review is requested or run.
- C5 and every later checkpoint remain forbidden.

## Completed checkpoints

| Checkpoint | Scope | Result |
|---|---|---|
| C0 / C0A / C0B | occurrence-index proof spike, snapshot-local identity, exact source correspondence | GREEN, human-approved |
| C1 / C1A / C1B | specification-shaped files, path-keyed source forest, standard collections | GREEN, human-approved |
| C2 | production occurrence index, references, navigation, indexed traversal | GREEN, human-approved |
| C3 | fresh-image literal-build closeout: exact `go build ./...` acceptance model, fresh-build runner, publication workflow, source type/package semantics | **ACCEPTED** by Rob at baseline `8c9212a` |

## C4 implementation state

**🔒 CURRENT: retained-table bottom-up repair 3 COMPLETE — candidate FROZEN
(`review(final): C4 — freeze retained-table bottom-up candidate`).** The production expression path is now the
proof-carrying BOTTOM-UP ACCUMULATOR `prog_outcomes_c`: a `fold_right` over the retained source-order visit
(`build_outcomes`) that CONSUMES the once-built `prog_tnft` TABLE OBJECT, queries the table at each conversion's
retained target ref (TOTAL `type_name_fact_at_table`, no fallback), reads its operand's ALREADY-COMPUTED outcome
from the processed suffix (TOTAL `from_some` of the operand-closure proof, no fallback), and calls `convert_const`
ONCE per conversion. The FACTS and the DIAGNOSTICS both project that SAME accumulator
(`facts_and_diags_share_outcomes`); `EOConvFail` carries the exact conversion/target/operand refs and the operand
ref is a field of `DRInvalidConversion` (projected without re-mint); `prog_tnft` is sealed into `ElaborationFacts`
by OBJECT IDENTITY (`elaborate_ok_seals_tnfacts`). The rejected `typed_outcome`/`typed_outcome_e`/`tnfact_at`/
`add_typed_outcome`/`prog_conv_outcome_consumes` recursive/recomputing root, the fake `leaf_ci` case, and the old
facts/diagnostics bridges are DELETED. `two_uint8_distinct_target_refs` queries the sealed `prog_tnft` table.
GREEN: `make prove` (axiom-free, whole-theory audit) + `make e2e` + `make check` (byte-identical) + `make
regenerate` (no drift). **STOP: pending Rob's HUMAN Implementation Review; automatic Codex DISABLED; C5 FORBIDDEN.**
Baselines: original `8c9212a`, first blocked `89b8e54`, second blocked `1c4a7de`, third blocked `806ce87`,
repair-3 clean baseline `1b38b68`.

Goal (unchanged): replace the three family-specific conversion constructors
(`EIntConvert`/`EFloatConvert`/`EComplexConvert`) with one source-shaped `EConvert TypeSyntax GoExpr`; resolve
the source type name in `GoCompile` through the current predeclared context; retain occurrence-keyed type-name
facts; render from the source spelling; and delete the old path in the same checkpoint.  Sixteen live target
names (the fourteen existing numeric names plus the `byte`→`uint8` and `rune`→`int32` source aliases); no new
semantic types.  No C5 work (no `uintptr`, no rune literals/constants).

- **`806ce87` (repair-2 candidate) was a THIRD C4 Implementation Review BLOCKING; retained-table bottom-up repair 3
  `C4-retained-table-bottom-up-repair-3` (authority `.review/C4_IMPLEMENTATION_REPAIR_3.md`) was applied from clean
  main `1b38b68` and is now COMPLETE (frozen, see above).** Repair 2 moved typed refs into `typed_outcome` and fixed the hidden use-resolution rescan, but
  it did NOT implement the required production model. Two decisive faults: (a) production does not CONSUME the
  `TypeNameFactTable` object built from the retained visit — `typed_outcome_e` calls `tnfact_at p tr` →
  `prog_type_name_facts p`, re-folding `prog_visit p` for every conversion (equivalent recomputation sold as
  retained authority; `elaborate_ok_seals_tnfacts` proves only extensional EQUALITY, not object consumption); and
  (b) the outcome map is filled by STRUCTURAL RECURSION on each expression subtree, then `add_typed_outcome` folds
  `typed_outcome` over every occurrence — so a nested conversion is evaluated once per ancestor AND again at its own
  entry, several `convert_const` calls per occurrence. "One convert_const per conversion" was false. Blocking
  classes (repair-3 §2):
  - **2.1** the once-built `TypeNameFactTable` is beside production; `tnfact_at`/`prog_type_name_facts` recompute.
  - **2.2** the outcome map is not a bottom-up authority — recursive re-evaluation, not one accumulator reading the
    already-computed operand outcome; multiple `convert_const` per occurrence.
  - **2.3** no proof-carrying typed WORK stream; `add_typed_outcome` does `as_expr … = None ⇒ skip` on the live path.
  - **2.4** `occ_expr_diags_sm` has fail-open `as_expr … = None ⇒ []` structural branches.
  - **2.5** `conv_failure_om` discards the stored operand ref (`_opr`); `DRInvalidConversion` has no operand-ref field;
    diagnostic soundness returns to `local_conv_failure` + recursive `const_info` (a source spec theorem, not production).
  - **2.6** `prog_conv_outcome_consumes` is stated over `prog_outcomes`/`tnfact_at`/recursive `const_info` — it proves
    the rejected recursive helper, not the retained-table/bottom-up path; gate comments repeat the false claims.
  - **2.7** `two_uint8_distinct_target_refs` queries `tnfact_at` (raw recomputing), not a SEALED `TypeNameFactTable`.
  - **2.8** `leaf_ci` keeps the fake `EConvert ⇒ CIUntyped (CBool false)` semantic case.
  - **2.9** false authority/prose claims (one route / consumed+sealed / one convert_const / already-computed operand /
    `tnfact_at` reads the local map / `life.md` "fixed C4 by putting typed_outcome on the path").
  - **2.10** `CLAUDE.md`'s "no review gate governs `life.md`" is incompatible with a frozen-candidate process — a
    tracked file cannot self-exempt from review/freeze.

  **Required model (repair-3 §3):** ONE proof-backed retained `CompilationInput` (index + blocks/visit + proofs),
  consumed by every production builder (no hidden `prog_visit`/`prog_blocks`/`index_program`); ONE proof-backed typed
  WORK stream (each conversion work item carries conversion/target/operand `ExprRef`s + view/child/order/recovery/
  suffix proofs; minting is TOTAL for a Some-expression view); ONE exact `TypeNameFactTable` object with a table-level
  total query, PASSED INTO the outcome builder and SEALED by identity (delete raw `tnfact_at`); ONE proof-carrying
  bottom-up outcome accumulator (`fold_right` over the source-order work stream, operand in the processed suffix, ONE
  `convert_const` per conversion, missing-operand impossible by proof, `EOChildFail` only for a real non-success);
  use-resolution from the computed `ConstInfo`; `EOConvFail` carrying exact evidence; diagnostics a TOTAL projection
  (prefer adding `operand_ref` to `DRInvalidConversion`); ONE phase object proving facts + diagnostics project the
  SAME outcome table; the declarative spec (`const_info`/`local_conv_failure`) stays out of the production path.

  Repair-2 landed inventory + prior repair history is preserved in git; `.review/C4_IMPLEMENTATION_REPAIR_2.md` is
  deleted in the first repair-3 implementation commit (its archive is git history).

## Standing decisions

- Platform resource limits such as NAME_MAX, PATH_MAX, disk, and memory are outside the semantic model.
- Contract Review precedes implementation for checkpoints activated after the policy was adopted. C3 was the
  explicit transition exception; C4's Contract Review is Rob's directive itself, with the automatic Codex
  review path disabled.
- Each review permits at most one bounded confirmation. A blocking confirmation returns control to Rob.
