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
- Fourth blocked candidate / repair-4 baseline: `af2fc87e7726a4fc68bb9480c53cf64faa83717b`
  (fourth BLOCKING — proof-carrying accumulator projected down to a raw map, fail-open projections, retained visit
  ignored by the semantic builders).
- Fifth blocked candidate: `9d4aff5d94d9aac293ff7fb98a7d9fdd59159022` (fifth BLOCKING — named-not-behavioral).
- Sixth blocked candidate: `3b4f40e1f14c501fd76333ec8a8cd3e582ed1598` (sixth BLOCKING — three independent work
  discoveries related only by equality theorems).
- Seventh blocked candidate / repair-7 baseline: `3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc` (seventh BLOCKING —
  no ONE proof-carrying `ExprWorkForest` object passed through production; `prog_forest*` recomputed per phase,
  `ep_work` stored-but-unconsumed).
- Eighth blocked candidate / repair-8 baseline: `91e8dbbcd24fc7df678e6b3d68eabb13b686efa1` (the repair-7 freeze;
  eighth BLOCKING — the final table's causal outcome was the raw-map `OutcomeCause`; the semantic fold discarded
  the exact operand member and did a raw map `find`; `phase_*_work_cause` reconstructed the cause afterward).
- Ninth blocked candidate / repair-9 baseline: `a2a5b46026cc658f41cb04f6d6cb30a29335671c` (the repair-8 freeze;
  ninth BLOCKING — repair 8 correctly repaired the live semantic step, but the final table retains no
  final-to-tail causal relation: the existential `acc_rest` inside `FinalMemberCause` is a POSSIBLE derivation,
  not the authenticated recursive tail of `fot_acc`, so a foreign rest accumulator producing the same head
  outcome still typechecks). All nine blocked candidates end at `a2a5b46`.
- Human authorization: `C4-source-type-resolution-1`; repair 1 `C4-retained-facts-and-diagnostics-repair-1`;
  repair 2 `C4-typed-reference-single-path-repair-2`; repair 3 `C4-retained-table-bottom-up-repair-3`;
  repair 4 `C4-retained-phase-scope-ledger-repair-4`; repair 5 `C4-typed-work-direct-cause-scope-repair-5`;
  repair 6 `C4-single-retained-work-domain-repair-6`; repair 7 `C4-exact-retained-work-object-repair-7`;
  repair 8 `C4-member-indexed-causal-outcome-repair-8`; repair 9
  `C4-final-to-tail-causal-closure-repair-9` (ACTIVE — see section 2 below).
- Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_9.md` (repairs 1–8 superseded — each deleted in the
  first implementation commit of the next repair; git history is their archive). The scope ledger
  (`.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md`) + `ADR-0001-PINNED-64-BIT-TARGET` (PROPOSED) + `ADR-0002-BOUNDED-
  DECIMALFLOAT-DOMAIN` (REJECTED AS WRITTEN — open) are authorized as review governance under this repair (no
  disposition ACCEPTED; a model does not certify its own trade-offs; PROPOSED entries carry neutral
  classifications, no REVIEWED).
- Automatic Codex review: DISABLED. This directive is Rob's later explicit authorization; on repair completion
  the candidate is frozen with EXACTLY ONE `review(final): C4 — freeze causally closed outcome-trace candidate`
  and reported for Rob's human Implementation Review — no Codex review is requested or run.
- C5, every later checkpoint, and the post-C4 trim remain forbidden (the trim until C4 acceptance).

## Repair 9 — blocking classes (final-to-tail causal closure) — ACTIVE at `a2a5b46`

Repair 8 correctly repaired the live semantic step (KEEP it). The one remaining defect is the final RETENTION
boundary: the fold computes each member from the actual tail `OutcomeAccumulator`, but the final table retains no
causal structure proving that the existential `acc_rest` inside `FinalMemberCause` IS the actual tail of
`fot_acc`.

- **2.1** `OutcomeAccumulator` carries no causal predecessor (no exact tail accumulator, current member,
  `StepCause`, or recursive trace); `build_outcome_accumulator` returns the causes as a SEPARATE dependent
  function beside the accumulator, so the object alone does not retain how it was built.
- **2.2** `FinalMemberCause` is not indexed by the final `OutcomeAccumulator`; its existential `acc_rest` has no
  relation to `fot_acc`. The list split proves only that `rest` is the source suffix, not that `acc_rest` is the
  causal tail of `fot_acc`.
- **2.3** `ForestOutcomeTable` permits a FOREIGN causal witness: `fot_acc`/`fot_causes` may be paired with any
  exact-domain rest accumulator that makes a `StepCause` produce the same head result (e.g. an `EOOk` operand
  fact with equal `ConstInfo` but different `ef_use_resolved`; or any failing rest outcome for a child failure).
- **2.4** the final query cannot connect the operand tail result to the final table: `StepCause_convfail_inv`
  proves `oa_total acc_rest operand_suffix = EOOk opf` but NOT `total_forest_outcome_at ot operand_work = EOOk
  opf`, and no retained field states extension preserves suffix-member queries into `fot_acc`.
- **2.5** `total_forest_outcome_cause` projects `fot_causes`, so it returns a POSSIBLE derivation, not an
  authenticated insertion trace; the "exact insertion cause" comments are not justified by the type.
- **2.6** the actual tail relation is discarded during lifting: the head cause stores the actual `acc_rest`, but
  the tail lifting uses a local `Hoo` query equality and then discards it; the retained cause accumulates no
  relation from `acc_rest` to the final accumulator.
- **2.7** `deep_fail_innermost_convfail` stops at the unlinked tail accumulator (`oa_total acc_rest operand_sm =
  EOOk opf`) and never proves the same operand `WorkMember` has `EOOk opf` in the final table.
- **2.8** `deep_fail_outer_childfail`/`deep_nested_all_ok` prove only final outcome shapes (via the source-spec
  bridge / EOOk), never projecting `total_forest_outcome_cause` and connecting each tail operand result to the
  final table.
- **2.9** current prose/gate comments overclaim the final cause (exact insertion cause, exact prior accumulator,
  exact retained operand outcome, foreign components unrepresentable) — false without a final-to-tail relation.

Required (directive §3–§9): an intrinsic causal object (preferred `OutcomeTrace forest tnft items acc`, accumulator
as INDEX, retaining the exact tail trace/accumulator/member/`StepCause`/freshness); `ForestOutcomeTable` = `fot_acc`
+ `fot_trace`; `total_forest_outcome_cause` PROJECTS the trace with tail-to-final query preservation; direct
fixtures prove closure into the final table; foreign witnesses excluded. KEEP the repair-8 semantic branch.

## Repair 8 — blocking classes (member-indexed causal outcome) — RESOLVED (repair-8 classes; candidate superseded by repair 9)

The eighth C4 Implementation Review was BLOCKING at `91e8dbb`. Repair 7's retained-object flow is CORRECT and
kept; the one remaining defect — the causal/outcome-fold root beneath `ForestOutcomeTable` — is REPAIRED. Each
blocking class below is CLOSED by the re-rooted fold: the production cause is now the member/suffix-indexed
`StepCause` carried by `build_outcome_accumulator` (over `SuffixMember`/`ConversionStep`/`OutcomeAccumulator`),
retained on `ForestOutcomeTable` as `fot_causes` and queried by `total_forest_outcome_cause` →
`FinalMemberCause`; the conversion cons-step queries the operand THROUGH `cs_operand_suffix` via `oa_total
acc_rest` with ONE `convert_const` (no raw `find`/`from_some`/`operand_key`/post-hoc `ConversionWork`); the raw
`OutcomeCause`/`outcomes_caused`/`build_outcomes_forest`/`phase_*_cause`/`phase_*_work_cause` root is DELETED;
the direct fixture `deep_fail_innermost_convfail` projects the retained cause (operand `EOOk` through the exact
operand `SuffixMember`); prose is corrected. The original blocking classes (for the record):

- **2.1** `build_outcomes_forest` never consumes `ConversionWork` — its conversion branch destructs the smaller
  `ew_conv`, gets raw refs, and does a raw map lookup; `build_conversion_work` is used only in a later fixture.
- **2.2** the exact operand member (`ewf_operand_in_tail`) is proved then DISCARDED — the outcome reads
  `from_some (find (node_ref_key (erase_ref opr)) m_rest)`, not a suffix-accumulator query through the member.
- **2.3** the production `OutcomeCause` is still raw (idx/tnft/raw-map/NodeRef/occurrence), not
  forest/current-member/suffix/operand-member/accumulator-indexed — the repair-5 direct-cause shape.
- **2.4** `OutcomeCause_add_fresh` transports causes to the final map, erasing which prior/suffix accumulator +
  suffix member supplied the operand.
- **2.5** `phase_convok/convfail/childfail_work_cause` are NOT projections of a stored work-indexed cause — they
  invert the raw cause, receive a separately supplied `ConversionWork`, and translate the raw find into a member
  query (post-hoc reconstruction; the "production cause form" comment is false).
- **2.6** `cw_target_before_op` proves only target-child-before-operand-child source order, NOT processed-suffix
  membership; prose calling it a "processed-suffix order" is incorrect.
- **2.7** `fot_caused` still stores raw `outcomes_caused`; exact domain alone does not repair the causal loss.
- **2.8** `deep_fail_innermost_operand_member` builds `ConversionWork` AFTER the table result and translates the
  raw cause; it does not project a cause the production step retained.
- **2.9** gate + `GoCompile`/`ARCHITECTURE`/`PROGRESS` prose overclaim the cause as forest/work-indexed,
  suffix-retaining, and a projection — correct AFTER the implementation is true.

Required (directive §3–§7): `SuffixMember`/`ConversionStep`, a proof-carrying `OutcomeAccumulator`/`OutcomeTrace`
indexed by the exact suffix, a member/suffix-indexed direct cause built INTO the fold, and a `ForestOutcomeTable`
retaining the exact insertion cause (`total_forest_outcome_cause` → `FinalMemberCause` with the exact
`prefix ++ current :: rest` split). Keep the phase chain, objects, sealing, alias/render/byte results, scope wording.

## Completed checkpoints

| Checkpoint | Scope | Result |
|---|---|---|
| C0 / C0A / C0B | occurrence-index proof spike, snapshot-local identity, exact source correspondence | GREEN, human-approved |
| C1 / C1A / C1B | specification-shaped files, path-keyed source forest, standard collections | GREEN, human-approved |
| C2 | production occurrence index, references, navigation, indexed traversal | GREEN, human-approved |
| C3 | fresh-image literal-build closeout: exact `go build ./...` acceptance model, fresh-build runner, publication workflow, source type/package semantics | **ACCEPTED** by Rob at baseline `8c9212a` |

## C4 implementation state

**CURRENT: exact retained work-object repair 7 ACTIVE from baseline `3a92d22`** (authority
`.review/C4_IMPLEMENTATION_REPAIR_7.md`, token `C4-exact-retained-work-object-repair-7`). The repair-6 candidate
`3a92d22` (and its superseding freeze `c23a7c9`) was the **SEVENTH BLOCKING**: repair 6 closed the three-way work
split, but there is still **no ONE proof-carrying `ExprWorkForest` object passed through production**. `prog_forest`
= `concat (prog_forest_blocks input)` and `prog_forest_blocks` = `proj1_sig (build_forest_blocks …)` — the sigma's
proof is DISCARDED and re-recovered later via a separate `proj2_sig`; each phase builder re-evaluates the canonical
function on `input`, and `ep_work` is stored but consumed by NOTHING. Same prohibited architecture at one final
layer: evidence exists, the evidence-bearing object is discarded, raw data is recomputed through a canonical
helper, equality theorems later claim shared provenance.

**Repair 7 blocking classes (§2 of the repair-7 directive):** 2.1 no `ExprWorkForest` record retaining blocks +
flat + `=concat` + fwd/rev domain + NoDup + one-per-expr + order + operand-in-suffix (proof discarded via
`proj1_sig`, re-recovered via `proj2_sig`); 2.2 `build_expression_phase` recomputes canonical work per builder
(`prog_forest`/`prog_forest_awork` called again) rather than passing one value; `ep_work`/`ep_awork` unconsumed;
2.3 `ForestOutcomeTable input tnft` indexed by input, not by the exact forest object; 2.4 live operand lookup
still uses raw `operand_key`, ref justified afterward; 2.5 `ConvRefinement` lacks roles/direct-child/order/operand
view/exact operand work-item/suffix membership (reconstructed later from `conversion_*_ref_conv` +
`prog_forest_operand_in_tail`); 2.6 `prog_forest_awork` is another `proj1_sig` raw projection, diagnostics consume
a fresh call not `ep_awork`; 2.7 `ExpressionPhase` stores equal results + provenance equalities, not a dependent
causal chain (`ep_ot` not indexed by `ep_work`, `ep_eft` not by `ep_work`+`ep_ot`, …); 2.8 `ep_work` is
stored-but-dead as an authority; 2.9 `OutcomeCause` indexed by raw node/occ + raw prior map, not the exact
work/suffix identities; 2.10 `total_forest_outcome_at` accepts any constructible `ExprWork`, not a retained
membership witness; fixtures query a `program_work_at`-constructed value; 2.11 scope ledger still calls
`GoCompile == go build` an EXACT property (SR-001/SR-002) rather than an external adequacy target; 2.12 prose
overstates the retained-object implementation. **Required replacement: ONE proof-carrying `ExprWorkForest` +
`WorkMember` + `ConversionWork` view; `ForestOutcomeTable forest tnft`; operand lookup by member/ref;
`AnnotatedExprWorkForest`; forest/ot-indexed facts + diagnostics; `ExpressionPhase` a DEPENDENT CHAIN with no
provenance-equality fields; fixtures querying retained members; scope-ledger adequacy wording corrected.**

### Repair 6 APPLIED — the SEVENTH BLOCKED candidate (historical)

The single retained work-domain repair is applied and frozen. **Seventh C4 candidate: the `review(final): C4 —
freeze single retained work-domain candidate` commit at repository HEAD** (repair-6 implementation range
`3b4f40e..HEAD`; sixth blocked candidate `3b4f40e`). An earlier freeze `3a92d22` is SUPERSEDED by this head: after
it, `deep_nested_all_ok` was completed to prove EVERY conversion of the chain EOOk (not a 3-of-5 subset) and a
concrete `deep_nested_seals_eft` was added, so a new freeze head was created per the freeze rule (git holds the
superseded freeze). Status: **pending Rob's HUMAN Implementation Review**;
automatic Codex is DISABLED (not requested/run); ADR-0001 PROPOSED; ADR-0002 REJECTED AS WRITTEN (rewritten,
open); C5 and every later checkpoint remain FORBIDDEN. GREEN: `make check` (pinned-Rocq prove — gate 428/428
axiom-free + whole-theory audit + self-tests A–E — pinned-Go e2e, and the working-tree generated-byte compare),
`make regenerate` no-drift, and the staged pre-commit hook.

**Repair 7 (`C4-exact-retained-work-object-repair-7`) supersedes the above.** The defect is now closed at the
OBJECT level: there is ONE proof-carrying retained work forest OBJECT — the `ExprWorkForest` record built ONCE by
`build_expr_work_forest` (its `build_forest_blocks` PRIVATE inside, proof returned INTO the record fields — no
`proj1_sig` discard). The outcome table, the annotation, the facts, and the diagnostics each RECEIVE that exact
object (or an object typed by it) as a parameter, and the phase is a DEPENDENT CHAIN with NO provenance-equality
fields: `ep_ot : ForestOutcomeTable ep_work ep_tnft`, `ep_awork : AnnotatedExprWorkForest ep_work`, `ep_eft :
ForestExprFactTable ep_work ep_ot`, `ep_diag : ExpressionDiagnostics ep_awork ep_ot` — a foreign component is
unrepresentable by TYPE MISMATCH, not by a stored equality. The canonical-function roots
(`prog_forest`/`prog_forest_blocks`/`prog_forest_awork`/`forest_diags` + the three `ep_*_prov` fields) are DELETED.

**§2.18 completed behavioral evidence table (repair 7)** — production symbol · behavioral condition · load-bearing
theorem · deleted old path · production-object fixture:

| Production symbol | Behavioral condition | Theorem(s) | Deleted old path | Fixture |
|---|---|---|---|---|
| `ExprWorkForest` record + `build_expr_work_forest` | ONE proof-carrying work forest object; `ewf_items = concat ewf_blocks`; forward/reverse domain; key-NoDup; operand-in-suffix — all carried as FIELDS; `build_forest_blocks` PRIVATE, no `proj1_sig` discard | `ewf_forward`, `ewf_reverse`, `ewf_keys_nodup`, `ewf_operand_in_tail` (record fields/derived) | `prog_forest`, `prog_forest_blocks`, `prog_forest_filter`, `prog_forest_complete`, `prog_forest_sound`, `prog_forest_nodup`, `prog_forest_pairs_nodup`, `prog_forest_split`, `prog_forest_operand_in_tail` | `deep_nested_work_count` (=5), `phase_domain_exact` |
| `WorkMember` + `ConversionWork forest w` view | retained-member handle; conversion work carries the exact operand `WorkMember` + roles + direct-child + order + syntax + suffix | `build_conversion_work` (`cw_operand_work`, `cw_target_before_op`) | reminted refs on the live path | `deep_fail_innermost_operand_member` |
| `build_forest_outcome_table forest tnft` / `ForestOutcomeTable forest tnft` | INDEXED by the forest OBJECT; folds `ewf_items` once; operand read via member/ref from the suffix (live key = `node_ref_key (erase_ref opr)`, NO `operand_key`); DIRECT cause | `total_forest_outcome_at_caused`, `total_forest_outcome_at_matches`, `outcomes_caused_matches` | `build_outcomes` (raw), `build_outcome_table`, `total_outcome_at` | `deep_fail_innermost_convfail` |
| `fot_domain_iff_forest` / `fot_nonexpr_absent` | domain = membership in `ewf_items` (not `∃ w`); no foreign / wrong-kind key; TOTAL query requires a `WorkMember` | `fot_domain_iff_forest`, `fot_present`, `fot_nonexpr_absent`, `total_forest_outcome_at` | `eot_domain_iff_work` (the `∃ w` form), `fot_at_not_none` (raw option) | `phase_domain_exact` |
| forest/work-indexed direct cause | `EOConvFail`/`EOChildFail`/`EOOk` cause carries the exact `ConversionWork` + operand `WorkMember` + suffix; operand outcome read THROUGH that exact member | `phase_convfail_work_cause`, `phase_convok_work_cause`, `phase_childfail_work_cause` (over `phase_*_cause`) | the raw-`r`/`occ` cause over `ExprOutcomeTable` | `deep_fail_innermost_operand_member`, `deep_fail_outer_childfail` |
| `AnnotatedExprWorkForest` record + `build_annotated_work_forest` | proof-carrying annotation OBJECT: members ARE `ewf_items` in order; `aewf_diag_fold` ties to `annotate_program`; context sound/same-file/nearest-first/nodup; NO `proj1_sig` discard | `aewf_members`, `aewf_align_eq`, `aewf_context_sound`/`_same_file`/`_nearest_first`/`_nodup`, `annotated_forest_erased_source` | `prog_forest_awork` (a `proj1_sig` projection) | `deep_fail_exactly_one_diag` (len 1) |
| `ForestExprFactTable forest ot` / `ExpressionDiagnostics aw ot` | fact table + diagnostics indexed by the exact objects; diagnostics CONSUME the annotated object | `feft_is_facts`, `forest_facts_eq_spec`, `ed_is_diags`, `expression_diagnostics_eq_spec` | `phase_expr_facts`, `work_fact`, `build_expr_fact_table`, `build_awork`, `awork_diags`, `forest_diags`/`forest_diags_eq_spec` | `deep_nested_all_ok` |
| `ExpressionPhase` DEPENDENT CHAIN (`ep_work`/`ep_tnft`/`ep_ot`/`ep_awork`/`ep_eft`/`ep_diag`) | each field TYPED by the exact prior object; NO provenance-equality field; each component IS the builder over the phase's own prior objects | `phase_ot_consumes_work`, `phase_awork_consumes_work`, `phase_eft_consumes_work_ot`, `phase_diag_consumes_awork_ot`, `facts_and_diags_share_phase` | the three `ep_*_prov` provenance-equality fields | `deep_nested_all_ok`, `deep_nested_work_count` |
| `elaborate` seals `ep_tnft`/`ep_eft` | object identity — the sealed tables ARE the phase's retained objects; `ep_tnft`/`ep_work` DEFINITIONALLY the input builders | `elaborate_ok_seals_tnfacts`, `elaborate_ok_seals_facts`, `elaborate_ok_seals_tnfacts_from_input` | the `ep_tnft_prov` stored equality | `two_uint8_distinct_target_refs` |

Residue evidence: `grep` of every deleted name (`build_outcomes`/`ExprOutcomeTable`/`total_outcome_at`/`eot_*`/
`build_work_sig`/`prog_work`/`prog_work_fold`/`phase_expr_facts`/`phase_expr_diags`/`awork_diags`/`build_awork`/
`build_outcome_table`) in `GoCompile.v` code = 0; the readable Print-Assumptions gate is 428/428 closed and the
whole-certified-theory `Fido Audit Assumptions` confirms zero project assumptions. (Gate count later 442/442 after
repair 8.)

**Repair 8 SUPERSEDES the repair-7 causal/outcome rows above.** The repair-7 table's `build_forest_outcome_table`
and `forest/work-indexed direct cause` rows named `total_forest_outcome_at_caused`, `outcomes_caused_matches`,
`phase_convfail_work_cause`/`phase_convok_work_cause`/`phase_childfail_work_cause`, and the fixture
`deep_fail_innermost_operand_member` — all DELETED. The final table carried the raw-map `OutcomeCause` and the
work-indexed cause was a POST-HOC translation. Repair 8 re-roots the fold on a member/suffix-indexed cause carried
BY CONSTRUCTION; the other repair-7 rows (`ExprWorkForest`, `WorkMember`, domain, annotation, facts/diagnostics,
dependent-chain, sealing) are unchanged and kept.

**§2.18 completed behavioral evidence table (repair 8)** — production symbol · behavioral condition · load-bearing
theorem · deleted old path · production-object fixture:

| Production symbol | Behavioral condition | Theorem(s) | Deleted old path | Fixture |
|---|---|---|---|---|
| `SuffixMember forest items` + `ConversionStep forest current rest ts x` + `build_conversion_step` | the conversion's operand is carried as an EXACT member of the processed tail (`cs_operand_suffix : SuffixMember forest rest`, `cs_operand_exact`), never re-found | `ConversionStep` fields, `build_conversion_step` | raw `operand_key`/`from_some (find … m_rest)` operand lookup | `deep_fail_innermost_convfail` |
| `OutcomeAccumulator forest tnft items` + `oa_total` + `build_outcome_accumulator` | proof-carrying (`oa_covers`/`oa_domain`); `oa_total` TOTAL on `SuffixMember`; the conversion cons-step queries the REST accumulator THROUGH `cs_operand_suffix` via `oa_total acc_rest`, ONE `convert_const`, no raw `find`/`operand_key`/post-hoc `ConversionWork` | `build_outcome_accumulator` (carries `FinalMemberCause` + `outcome_matches` per member) | `build_outcomes_forest` (raw fold, discarded operand member) | `deep_nested_all_ok` |
| `StepCause` (`SCLeaf`/`SCConvOk`/`SCConvFail`/`SCChildFail`) | member/suffix-indexed DIRECT cause built INTO the fold; each conversion case reads the operand outcome THROUGH `cs_operand_suffix` via `oa_total acc_rest` | `StepCause_convfail_inv`, `StepCause_childfail_inv`, `StepCause_ok_conv_inv` (axiom-free inversions) | raw `OutcomeCause` + `leaf_outcome_cause`/`conv_outcome_cause`/`OutcomeCause_add_fresh`/`OutcomeCause_*_inv` | `deep_fail_innermost_convfail`, `deep_fail_outer_childfail` |
| `ForestOutcomeTable` (`fot_acc`/`fot_causes`/`fot_match`) + `total_forest_outcome_cause` | the table RETAINS each member's exact insertion cause; `total_forest_outcome_cause` returns its `FinalMemberCause` (exact `ewf_items = prefix ++ current :: rest` split + prior `OutcomeAccumulator` + `StepCause`); source spec is the SEPARATE per-member `fot_match` | `total_forest_outcome_cause`, `total_forest_outcome_at_matches`, `stepcause_matches` | `fot_caused` (raw `outcomes_caused`), `total_forest_outcome_at_caused`, `outcomes_caused_matches`, `phase_*_cause`, `phase_*_work_cause` | `deep_fail_innermost_convfail`, `deep_nested_all_ok`, `two_uint8_distinct_target_refs` |

Residue evidence (repair 8): `git grep` of every deleted name (`OutcomeCause`/`outcomes_caused`/
`build_outcomes_forest`/`fot_caused`/`phase_*_cause`/`phase_*_work_cause`/`total_forest_outcome_at_caused`/
`deep_fail_innermost_operand_member`/`operand_covered`/`outcome_covers`/`suffix_head_key_fresh`) in `GoCompile.v` +
`gate` + charter/progress = 0; no `from_some` of a raw operand lookup in production; readable gate 442/442 closed,
whole-theory `Fido Audit Assumptions` zero project assumptions, self-tests A–E, working-tree generated bytes
byte-match, `make regenerate` no-drift, `make regen-guard` DAG edge load-bearing.

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
