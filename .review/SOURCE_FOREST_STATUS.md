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
- Fourth blocked candidate / repair-4 baseline (current clean main): `af2fc87e7726a4fc68bb9480c53cf64faa83717b`
  (fourth BLOCKING — proof-carrying accumulator projected down to a raw map, fail-open projections, retained visit
  ignored by the semantic builders).
- Human authorization: `C4-source-type-resolution-1`; repair 1 `C4-retained-facts-and-diagnostics-repair-1`;
  repair 2 `C4-typed-reference-single-path-repair-2`; repair 3 `C4-retained-table-bottom-up-repair-3`;
  repair 4 `C4-retained-phase-scope-ledger-repair-4`; repair 5 `C4-typed-work-direct-cause-scope-repair-5`;
  repair 6 `C4-single-retained-work-domain-repair-6` (ACTIVE — see C4 implementation state).
- Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_6.md` (repairs 1–5 superseded — each deleted in the
  first implementation commit of the next repair; git history is their archive). The scope ledger
  (`.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md`) + `ADR-0001-PINNED-64-BIT-TARGET` (PROPOSED) + `ADR-0002-BOUNDED-
  DECIMALFLOAT-DOMAIN` (REJECTED AS WRITTEN — open) are authorized as review governance under this repair (no
  disposition ACCEPTED; a model does not certify its own trade-offs; PROPOSED entries carry neutral
  classifications, no REVIEWED).
- Automatic Codex review: DISABLED. This directive is Rob's later explicit authorization; on repair completion
  the candidate is frozen with EXACTLY ONE `review(final): C4 — freeze single retained work-domain candidate` and
  reported for Rob's human Implementation Review — no Codex review is requested or run.
- C5 and every later checkpoint remain forbidden.

## Completed checkpoints

| Checkpoint | Scope | Result |
|---|---|---|
| C0 / C0A / C0B | occurrence-index proof spike, snapshot-local identity, exact source correspondence | GREEN, human-approved |
| C1 / C1A / C1B | specification-shaped files, path-keyed source forest, standard collections | GREEN, human-approved |
| C2 | production occurrence index, references, navigation, indexed traversal | GREEN, human-approved |
| C3 | fresh-image literal-build closeout: exact `go build ./...` acceptance model, fresh-build runner, publication workflow, source type/package semantics | **ACCEPTED** by Rob at baseline `8c9212a` |

## C4 implementation state

**CURRENT: single retained work-domain repair 6 ACTIVE from clean baseline `3b4f40e`** (authority
`.review/C4_IMPLEMENTATION_REPAIR_6.md`, token `C4-single-retained-work-domain-repair-6`). The repair-5 candidate
`3b4f40e` was the **SIXTH BLOCKING**: the foundational defect is that there is still **no ONE retained typed-work
domain object** — work discovery happens independently in THREE places (`build_outcomes` folds raw `ci_visit`;
`prog_work`/`build_work_sig` builds a separate `ExprWork` list for facts; `build_awork`/`build_awork_blocks`
re-inspect raw occurrences for diagnostics/contexts), related only by extensional equality theorems. Same class of
defect as before: equivalent structural reconstruction sold as one authority. **Repair 6 must DELETE the split and
build ONE retained `ExprWorkForest`** (conversion-work refinement + exact domain/reverse-domain/NoDup/one-per-
expression laws, built once from the retained input) that the outcome fold, the outcome table, the annotation
forest, facts, and diagnostics all consume — retained in ONE intrinsic `ExpressionPhase` with dependent provenance
so a foreign component is unrepresentable.

**Repair-6 blocking classes (§2 of the repair-6 directive):** 2.1 CompilationInput computes the visit from a
SECOND `prog_blocks` call (two independent `prog_blocks p` terms); 2.2 three independent work builders, not one;
2.3 outcomes fold raw `NodeRef*SourceOccurrence`, not `ExprWork`; 2.4 no retained conversion-work refinement
(build_outcomes reminting target/operand refs); 2.5 `prog_work` a raw projected list with the proof beside it; 2.6
`build_awork` rebuilds work rather than annotating the retained forest; 2.7 `ExpressionPhase` retains no work /
annotated work / diagnostics; 2.8 `ep_eft` not intrinsically tied to `ep_ot`; 2.9 `eot_domain_iff_work` quantifies
over any constructible `ExprWork`, not one retained enumeration; 2.10 `OutcomeCause` carries no exact work item /
processed-suffix witness; 2.11 annotated work carries no context proof in its data; 2.12 phase fixtures prove less
than claimed (only `ep_diags = []` / `<> []` via rewrite to the spec); 2.13 permanent prose overclaims one work
domain; 2.14 stale NEXT_STEPS HEAD; 2.15 multiple `review(final)` commits; 2.16 ADR-0002 factually wrong —
REJECTED AS WRITTEN; 2.17 PROPOSED ledger entries still classified REVIEWED; 2.18 no completed behavioral TODO
evidence table. (Repair-5 results to KEEP per §0 are recorded below; the §2 list further below is the historical
record of the repair-5 findings.)

**Repair 5 (SUPERSEDED, prior frozen candidate `3b4f40e`, now the sixth blocked):** replaced each
named-not-behavioral boundary with a gated zero-axiom theorem — exact typed `ExprWork` domain (no `as_expr` in
production); DIRECT `OutcomeCause` the SOLE carried outcome invariant (`eot_caused`); exact-domain table
(`eot_domain_iff_work`); typed-work diagnostics (`awork_diags`); object-identity `ExprFactTable` seal;
input-provenance `TypeNameFactTable`; real phase fixtures. Detail is in git. Repair 4 results to KEEP (per §0): one `CompilationInput`
value; type-name facts built from the retained input; one proof-carrying `ExprOutcomeTable` value; one
`ExpressionPhase` value; operand read from the processed suffix; total type-name query consuming the passed table;
retained index threaded through conversion child proofs; `EOConvFail`/`DRInvalidConversion` retain refs;
use-context from the computed `ConstInfo`; the recomputing raw-map root deleted; two-uint8 reaches real
`ElaborationFacts`; source-target diagnostics + byte/rune alias differential correct; no C5; `life.md` boundary
acceptable. **Fifth-review blocking classes (§2 of the repair-5 directive) — the weak boundaries to REPLACE (not
paper over):**

- **2.1** NO typed expression-work domain: the "typed work interface" is `self_mem (ci_visit input)` (raw
  `NodeRef*SourceOccurrence` + membership); fact/diag/context projections still call optional
  `as_expr (ci_idx input) r`. Exact `ExprRef`/view/role/children are not one shared production value.
- **2.2** fact projection `add_work_fact` keeps a fail-open `as_expr = None ⇒ m` branch (impossible ≠ removed).
- **2.3** diagnostic `occ_work_diags` (`None ⇒ []`) and `annotate_encl` (`None ⇒` don't push a conversion) keep
  fail-open branches that can suppress the primary diagnostic / an outer context.
- **2.4** `ExprOutcomeTable` is complete but NOT exact-domain: `outcomes_ok` allows extra/foreign keys; no
  no-extras / one-entry-per-work-item / wrong-kind exclusion.
- **2.5** the carried `outcome_convfail_ev` is SOURCE-SPEC evidence (`local_conv_failure` + refs), not the
  production cause (stored target fact, stored operand outcome/status, exact `convert_const` rejection); no
  child-cause; no success relation.
- **2.6** `phase_convfail_cause` RECONSTRUCTS the cause (opens `outcome_convfail_ev`, `local_conv_failure_char`,
  recursive `const_info`, contradiction) — it does not PROJECT a cause carried by the table. Its comment is false.
- **2.7** no direct SUCCESS-cause or CHILD-cause theorem exists (only the reconstructed failure one).
- **2.8** `ExpressionPhase` does not retain the `ExprFactTable` OBJECT it seals — `ep_facts` is a raw map;
  `elaborate` builds a fresh `mkExprFactTable`; `elaborate_ok_seals_facts` proves only map equality. The
  object-identity claim is FALSE.
- **2.9** `TypeNameFactTable` is indexed only by `p`; its proofs are over `prog_visit p`, not the retained input —
  no input-indexed provenance at the type/proof boundary.
- **2.10** the deep "phase" fixtures call `erased_report`/`prog_expr_facts` (the declarative SPEC), not the phase.
- **2.11** `ci_visit` is DERIVED (`concat ci_blocks`) but comments/status call it a STORED value (false).
- **2.12** scope ledger incomplete: omits the bounded DecimalFloat literal box (`|coeff|<10^40`, `|exp10|≤4096`).
- **2.13** SR-006 gives a FALSE reason for the file-name grammar (rejects `foo_bar.go`/`Foo.go`, not only
  ignored/reserved files); "matches go build" is false for restrictions go build does not impose.
- **2.14** SR-005 understates the ModulePath exclusion (lowercase-only, no hyphen, first-segment dot, dot shape,
  reserved names, …), not just `/vN`/gopkg.in.
- **2.15** the ledger SELF-APPROVES: SR-002..008 marked REVIEWED/ACCEPTED by the model. Must be PROPOSED /
  PREVIOUSLY AUTHORIZED (with citation) / ACCEPTED (only after Rob).
- **2.16** ADR-0001 defensible but not accepted as written (adequacy = differential target not kernel theorem;
  widening not necessarily additive; C5 reopens it; qualify "no consumer" vs planned C5 uintptr).
- **2.17** permanent prose + gate comments overclaim (typed work / no fail-open / exact domain / projected cause /
  object identity / phase fixtures / complete ledger / reviewed decisions).
- **2.18** TODO completion was NAME-based, not behavioral (§16 fixes the criteria for repair 5).

**Repair-5 required model (§3–§10):** ONE retained `CompilationInput` (store `ci_visit`, §2.11); ONE exact
proof-backed `ExprWork` domain consumed by all downstream (no optional `as_expr` below the work builder); a direct
`OutcomeCause` relation carried by an EXACT-DOMAIN `ExprOutcomeTable` (no extras, one entry per work item,
foreign-key-uninhabitable); direct success/failure/child cause theorems from the carried relation; a retained
proof-backed `ExprFactTable` object sealed by OBJECT IDENTITY; an input-indexed `TypeNameFactTable`; total
annotated diagnostics; real phase fixtures; and an honest PROPOSED scope ledger + ADR set. **STOP on completion:
pending Rob's HUMAN Implementation Review; automatic Codex DISABLED; C5 FORBIDDEN.**

---

**PRIOR — repair 4 (`af2fc87`→candidate `9d4aff5`), now the FIFTH BLOCKING.** Repair 3 (`af2fc87`)
made real progress (one bottom-up fold; operand read from the processed suffix; a table-level total query;
`EOConvFail`/`DRInvalidConversion` retain refs; use-resolution from the computed `ConstInfo`; fake `EConvert`
leaf removed; alias differential complete; `life.md` character-only) but was **architecturally wrong**: still
"proof BESIDE the path." The fourth-review blocking classes (§2 of the repair-4 directive), whose repair-4
resolutions were NAME-based (behaviorally re-opened by repair-5 §2 above):

- **2.1** the retained `blocks`/`visit` in `elaborate_indexed` are IGNORED by the semantic builders — `prog_tnft`
  and `prog_outcomes_c` each hide their own `prog_visit p`; no `CompilationInput` value exists; equal list values
  do not turn hidden recomputation into one retained input.
- **2.2** `build_outcomes` returns a proof-carrying sigma but `prog_outcomes_bu = proj1_sig (…)` DISCARDS the proof
  and exposes only the raw map; the proof is recovered later by a separate theorem — no `OutcomeTable`/
  `ExpressionPhase` record; the proof does not travel with the production value.
- **2.3** the expression-fact projection (`add_occ_fact_om`) is FAIL-OPEN — a raw map lookup where a missing
  outcome is indistinguishable from a real failed expression; must pattern-match the exact `ExprOutcome`.
- **2.4** the diagnostic projection is FAIL-OPEN — `as_expr None ⇒ []`, `conv_failure_om`/`arg_default_failure_om`
  option-misses ⇒ no reason; a missing ref/outcome must not become "no diagnostic."
- **2.5** the stored invalid-conversion invariant (`outcome_convfail_ev`) discards the CAUSAL fact path — it
  proves `local_conv_failure` + recursive `const_info`, not `t = tnf_type (table query)` ∧ outcome at operand =
  `EOOk opf` ∧ `ci = ef_const_status opf` ∧ `convert_const t ci = None`.
- **2.6** `facts_and_diags_share_outcomes` is only a conjunction of EXTENSIONAL equalities over a global raw map,
  not one retained phase object carrying the completeness proof used by both projections.
- **2.7** the typed WORK layer still does not exist — inline minting is not retained/shared; later paths return to
  raw `NodeRef * SourceOccurrence` pairs + optional `as_expr`/map lookups.
- **2.8** the production proof chain reconstructs a canonical index — `prog_visit_operand`/`prog_visit_type_name`
  call `GoIndex.index_program p`; the live phase constructor may not reconstruct it.
- **2.9** `two_uint8_distinct_target_refs` queries `@prog_tnft` directly, not `ef_type_name_facts facts` from an
  actual successful `elaborate`.
- **2.10** the required deep-nested-phase fixture is absent (no phase object to exercise).
- **2.11** gate + permanent prose overclaim ("proof-carrying," "retained visit," "one phase," "cannot fail open").
- **2.12** the unsupported/restricted-scope decisions are undocumented — no reviewed ledger; the 64-bit target is
  the first required full decision record (ADR-0001).

**Repair-4 resolution (how each class was closed):** 2.1/2.7 — ONE `CompilationInput` (`ci_ip`/`ci_blocks`/
`ci_blocks_ok`/`ci_visit_ok`) built by `build_compilation_input`, consumed by the whole phase; a typed work layer
via the retained `ExprOutcomeTable`. 2.2/2.6 — the PROOF-CARRYING `ExprOutcomeTable` (map + `eot_ok`
completeness proof travels with the value) and ONE `ExpressionPhase` (`ep_tnft`+`ep_ot`), facts and diagnostics
both projecting the SAME `ep_ot` by object identity (`facts_and_diags_share_phase`). 2.3/2.4 — TOTAL projections:
`phase_expr_facts` and `phase_expr_diags` read `total_outcome_at` (returns `ExprOutcome`, never a fail-open
`find`); no `as_expr None ⇒ []`. 2.5 — direct cause `phase_convfail_cause` (target = sealed table query, operand
`EOOk opf`, `ci = ef_const_status opf`, `convert_const = None`), not `local_conv_failure`. 2.8 — the retained
`idx` threaded through `prog_visit_operand`/`prog_visit_type_name`/`operand_closed`/`operand_covered`; no
`index_program` in the live phase closure; global `prog_tnft` deleted, `TypeNameFactTable` built from the input
and sealed (`elaborate_ok_seals_tnfacts`; `ExprFactTable` sealed by `elaborate_ok_seals_facts`). 2.9 —
`two_uint8_distinct_target_refs` queries `ef_type_name_facts` from an actual successful `elaborate`
(`two_uint8_compiles`). 2.10 — deep-nested phase fixtures (`deep_nested_no_diags` / `deep_fail_one_diag`).
2.11 — prose corrected across NEXT_STEPS/STATUS/ARCHITECTURE/PROGRESS/GoCompile+gate comments. 2.12 — scope
ledger `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` + `ADR-0001` (PROPOSED). GREEN: `make check`
(prove axiom-free + e2e + working-tree byte-compare) + `make regenerate` (no drift). §10.1–10.7 each gated
axiom-free.

**Candidate head:** this `review(final): C4 — freeze retained-phase candidate` freeze commit is the new C4
candidate head (git HEAD of `main`). Baselines — original C4 `8c9212a`; first blocked `89b8e54`; second blocked
`1c4a7de`; third blocked `806ce87`; fourth blocked / repair-4 baseline `af2fc87`. Ranges — full human review
`8c9212a..<this freeze head>`; full repair `89b8e54..<this freeze head>`; repair-4 `af2fc87..<this freeze head>`.
Human C4 Implementation Review PENDING; ADR-0001 PROPOSED pending Rob.

**STOP: frozen candidate pending Rob's HUMAN Implementation Review; automatic Codex DISABLED (do NOT request or
run Codex); C5 FORBIDDEN.**

**Required (§3–§10):** ONE retained `CompilationInput` (index + blocks + visit + provenance proofs) built once,
consumed by every production builder (none may call `prog_visit`/`prog_blocks`/`binding_visit`/`Snap.visit_file`/
`index_program`); ONE typed WORK layer; a `TypeNameFactTable` built from the exact input, passed in and SEALED
(delete production use of global `prog_tnft`); a PROOF-CARRYING `ExprOutcomeTable` that stays on the path with a
TOTAL query returning `ExprOutcome` (not option); direct conversion-cause evidence (not `local_conv_failure`); ONE
`ExpressionPhase`; TOTAL fact + diagnostic projections (no fail-open); the scope ledger + ADR-0001.

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
