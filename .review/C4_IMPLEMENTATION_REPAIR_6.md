Claude Code directive: C4 Implementation Review BLOCKING — single retained work-domain repair 6

Repository:

rhencke/fido

Required clean baseline and sixth blocked C4 candidate:

3b4f40e1f14c501fd76333ec8a8cd3e582ed1598

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

Prior blocked C4 candidates:

1. 89b8e54634e7012612a51990756ad29a579c1b0f
2. 1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca
3. 806ce87373e29b6980e5c3d9d274ffa86580449b
4. af2fc87e7726a4fc68bb9480c53cf64faa83717b
5. 9d4aff5d94d9aac293ff7fb98a7d9fdd59159022
6. 3b4f40e1f14c501fd76333ec8a8cd3e582ed1598

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-single-retained-work-domain-repair-6

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

This is Rob's later explicit authorization to replace the remaining split structural root and correct the scope
decision records.

It does not replace or weaken the binding C4 contract.

Start only from the exact clean baseline above. Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 3b4f40e1f14c501fd76333ec8a8cd3e582ed1598.

Repair 5 closed important defects:

- CompilationInput now has a stored ci_visit field;
- ExprWork carries an exact ExprRef and source view;
- ExprOutcomeTable carries OutcomeCause and an exact no-extra-key domain;
- direct conversion-success, conversion-failure, and child-failure cause theorems exist;
- diagnostics use stored refs and total outcome queries;
- ExprFactTable is stored into ElaborationFacts by object identity for the built phase;
- TypeNameFactTable has phase input provenance;
- the source scope ledger no longer self-approves entries;
- the real two-uint8 fixture reaches actual ElaborationFacts;
- no C5 work landed;
- generated Go bytes stayed unchanged.

Keep those ideas unless the correct root requires a direct rewrite.

The remaining defect is foundational:

There is still no ONE retained typed-work domain object.

Instead the current code independently performs the same source-to-work discovery in three places:

1. build_outcomes folds the raw ci_visit, inspects view_expr, and mints ExprRef/target/operand refs itself;
2. prog_work projects a separately built ExprWork list from build_work_sig for fact construction;
3. build_awork/build_awork_blocks independently re-inspect raw occurrences and mint another ExprWork list for
   contexts and diagnostics.

ExpressionPhase retains none of these work lists or annotated-work values.

Thus the code has:

- one raw-visit outcome path;
- one separately rebuilt fact-work path;
- one separately rebuilt diagnostic-work path.

Theorems relate them extensionally. They are not one retained object flow.

This is the same class of defect as before: equivalent structural reconstruction sold as one authority.

Do not add another equality theorem around these three paths. Delete and replace the split.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_6.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 single retained work-domain repair 6;
   - binding contract path and exact hash;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - all six blocked candidates;
   - current repair baseline: full 3b4f40e SHA above;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_6.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; single retained work-domain repair active;
   - ADR-0001 remains proposed pending explicit Rob disposition;
   - ADR-0002 rejected as written and open, per section 12;
   - automatic Codex review disabled;
   - C5 forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-single-retained-work-domain-repair-6
   result: BLOCKING at 3b4f40e; single retained work-domain repair 6 active

4. Update .review/SOURCE_FOREST_STATUS.md with a concise exact record of every blocking class in section 2.

5. Commit only these authority changes:

   review(repair): C4 — require one retained typed work domain

No Rocq, Docker, e2e, gate, generated, plugin, shell, architecture, persona, life, or numeric implementation
change may enter that authority commit.

6. After the authority commit and after the status files preserve repair-5 history, delete the superseded:

   .review/C4_IMPLEMENTATION_REPAIR_5.md

in the first implementation commit. Git history is its archive.

Do not delete:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_6.md.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 CompilationInput still computes the visit from a second prog_blocks call

The current builder is:

  mkCompilationInput ip (prog_blocks p) (prog_visit p) ...

and:

  prog_visit p = concat (prog_blocks p)

Thus the stored blocks and stored visit contain two independent prog_blocks p terms.

The comment says the input is built once. The term computes the file visit blocks once for ci_blocks and again
inside prog_visit for ci_visit.

Replace it with one let-bound computation:

  let blocks := prog_blocks p in
  let visit := concat blocks in
  ...

No second prog_blocks/prog_visit data call may remain in build_compilation_input.

2.2 The claimed single work builder is not single

The current code says build_work_sig is the single place which decides expression-ness.

But build_outcomes independently:

- folds raw NodeRef * SourceOccurrence pairs;
- destructs view_expr;
- mints ExprRef;
- mints conversion target and operand refs.

build_awork independently does the same work discovery again for diagnostic contexts.

There are at least three work builders.

One exact work-domain object must be built once and shared.

2.3 Outcome construction does not consume ExprWork

build_outcomes is typed over:

  list (NodeRef * SourceOccurrence)

not:

  list ExprWork
  ExprWorkForest
  ConversionWork

OutcomeCause is indexed by raw:

  r
  occ

not by the exact work item which production is meant to consume.

The output table's domain is later shown equivalent to the existence of some constructible ExprWork. This is not
the same as folding the retained work enumeration.

The production outcome builder must consume the exact retained work order.

2.4 No retained conversion-work refinement exists

ExprWork carries only:

- node ref;
- occurrence;
- expression ref;
- expression;
- membership/view/as_expr/erase proofs.

It does not carry conversion-specific data:

- target TypeNameRef;
- operand ExprRef;
- exact child roles;
- target-before-operand;
- target/operand source recovery;
- operand work membership in the processed suffix.

build_outcomes remints those values from raw syntax.

Add a conversion-work refinement or make ExprWork an inductive whose conversion case carries all of them.

No conversion semantic step may call conversion_target_ref[_tot] or conversion_operand_ref[_tot] to reconstruct
data already required in work.

2.5 prog_work is a raw projected list with its exactness proof beside it

build_work_sig returns a sigma:

  { work_list | fold relation }

prog_work projects:

  proj1_sig ...

The proof is recovered later by another proj2_sig expression in prog_work_fold.

The work list consumed by facts does not carry:

- domain completeness;
- reverse domain;
- unique keys;
- conversion child facts;
- suffix relation.

Replace it with one retained proof-backed ExprWorkForest/ExprWorkTable value.

2.6 Diagnostic annotation rebuilds work rather than annotating retained work

build_awork/build_awork_blocks again traverse raw blocks, decide view_expr, and mint ExprWork records.

phase_expr_diags projects the raw list with proj1_sig. The proof is recovered later in
phase_expr_diags_eq_spec.

This is another proof-beside-data boundary.

Build annotated work from the retained work forest. Do not remint ExprWork.

2.7 ExpressionPhase does not retain work, annotated work, or diagnostics

The current phase stores:

- ep_tnft;
- ep_ot;
- ep_eft;
- ep_tnft_prov.

It does not store:

- ep_work;
- ep_annotated_work;
- ep_diags;
- work provenance;
- fact-table provenance to ep_ot.

ep_diags is a function which rebuilds annotated work each time it is called.

The required phase object flow does not exist.

2.8 ep_eft is not intrinsically tied to ep_ot

ExpressionPhase can be constructed with any ExprFactTable p (ci_ip input).

There is no field proving:

  ep_eft = build_expr_fact_table input ep_tnft ep_ot

or an equivalent dependent type.

build_expression_phase chooses the right value, but the phase abstraction does not make a foreign fact table
unrepresentable.

Add an ep_eft provenance field or index ExprFactTable by the exact work/outcome phase.

ep_facts must be eft_map ep_eft, not a separately recomputed phase_expr_facts value.

2.9 The exact-domain theorem quantifies over possible ExprWork values, not one retained enumeration

eot_domain_iff_work says a present key iff:

  exists w : ExprWork input, key w = k

Because ExprWork is any record whose proofs can be constructed, this does not identify membership in one
retained work list/table.

Required form:

  key in outcome table
  <->
  key in ep_work exact domain

The work-domain object must have direct completeness, reverse-domain, and NoDup/unique-key laws.

2.10 OutcomeCause does not carry the exact work item or processed-suffix witness

OutcomeCause carries raw refs and a map lookup.

It does not carry:

- the exact ConversionWork value;
- membership of operand work in the already-processed work suffix;
- the exact prior OutcomeTable object queried by the fold step.

The builder used a suffix map, but OutcomeCause_add_fresh lifts causes to the final map and the retained relation
no longer states the processed-order fact.

Carry the exact work/suffix relation in the direct cause, or in a table invariant indexed by the retained work
order.

2.11 The typed-work annotation carries no context proof in its data

The annotated item is only:

  ExprWork * list ExprRef

The context soundness, nearest-first ordering, same-file property, and NoDup are recovered from the old raw
annotate_encl specification.

Use a proof-backed AnnotatedExprWork value or AnnotatedWorkForest which carries the required context facts over
the retained work object.

2.12 The phase fixtures still prove much less than their comments claim

deep_nested_phase_no_diags proves only:

  ep_diags phase = []

and proves it by rewriting to expr_diags and program_typedb.

It does not prove:

- one retained work item per expression;
- each conversion's total outcome is EOOk;
- exact work/outcome order;
- ep_eft provenance.

deep_fail_phase_reports proves only:

  ep_diags phase <> []

and also rewrites to the source specification.

It does not prove:

- exact one diagnostic from ep_diags;
- innermost EOConvFail;
- each outer EOChildFail;
- exact stored operand cause.

Add direct phase queries and exact results.

2.13 Permanent prose overclaims one work domain

NEXT_STEPS, SOURCE_FOREST_STATUS, PROGRESS, ARCHITECTURE, GoCompile comments, gate comments, and the freeze report
say:

- outcomes consume ExprWork;
- facts/outcomes/diagnostics/context use one work domain;
- build_work_sig is the single work builder;
- the phase retains the whole object flow.

The code does not.

Correct all current prose only after the implementation is true.

2.14 NEXT_STEPS contains a stale HEAD statement

NEXT_STEPS still says HEAD 842fd2d is the current state near the 9d4aff baseline.

Current head is 3b4f40e.

Replace the stale statement with unambiguous historical wording or delete it.

2.15 The freeze history used several review(final) commits

The repair contains several intermediate commits named review(final) before the actual final candidate.

A freeze label must identify one final reviewed head.

In repair 6:

- use impl(...) or wip(...) for implementation commits;
- use exactly one review(final) commit after all checks and audits pass;
- if a later fix is needed, create a new final freeze commit and state the prior one is superseded.

2.16 ADR-0002 is factually and conceptually wrong as written

ADR-0002 says all exponent-magnitude forms beyond ±4096, including 1e5000, are valid programs the pinned
toolchain accepts and rounds to F32/F64.

That is false in the current represented use contexts:

- a very long significand near a finite magnitude is accepted and rounded;
- a bare/defaulted or F32/F64-converted 1e5000 overflows and is rejected;
- an unused untyped package constant can be parsed and retained by Go, but current Fido has no such declaration
  form.

The ADR mixes:

- lexical/source representability;
- untyped constant representability;
- accepted current-fragment programs;
- finite F32/F64 conversion.

It must separate them.

The ADR also says a bound is needed for finite data and decidable equality. Arbitrary Rocq Z coefficients and
exponents are still finite values with decidable equality. The bound may help proof evaluation, resource limits,
or implementation performance, but those costs must be measured and stated. It is not required for
canonicality or decidability.

ADR-0002 is REJECTED AS WRITTEN. Do not mark it accepted.

No float implementation change is authorized by this C4 repair.

2.17 Proposed ledger entries still use REVIEWED classifications

SR-001 through several other proposed entries use classifications such as:

  REVIEWED TARGET RESTRICTION
  REVIEWED MODEL EXCLUSION

while their approval state says PROPOSED.

Remove REVIEWED from the classification until Rob explicitly accepts the decision.

Use neutral classes:

- TARGET RESTRICTION
- MODEL EXCLUSION
- THREAT-MODEL EXCLUSION
- BUILD-ENVIRONMENT RESTRICTION
- TEMPORARY FEATURE FRONTIER
- REJECTED DESIGN
- UNRESOLVED EXISTING RESTRICTION

Approval state remains separate.

2.18 No completed behavioral TODO evidence table is present in the candidate

The repair directive required the final report to reproduce the full completed TODO list with:

- production symbol;
- behavioral condition;
- theorem;
- deleted old path;
- fixture;
- residue evidence.

No tracked evidence table exists, and the final freeze message provides only a summary.

If Claude supplied an out-of-band table, preserve it in the next final report. Repair 6 must include the complete
behavioral table in the final response and may also store it in SOURCE_FOREST_STATUS if concise.

===============================================================================
3. ONE RETAINED COMPILATION INPUT
===============================================================================

Build CompilationInput with one actual traversal:

  let blocks := prog_blocks p in
  let visit := concat blocks in
  mkCompilationInput ip blocks visit eq_refl eq_refl

Do not call prog_visit as a second data producer.

Specification proofs may show visit = prog_visit p.

===============================================================================
4. ONE RETAINED TYPED WORK FOREST
===============================================================================

Create one proof-backed object before semantic processing.

Preferred shape:

  ExprWorkForest input := {
    ewf_blocks : list (list (ExprWork input));
    ewf_items  : list (ExprWork input);
    ewf_items = concat ewf_blocks;
    exact forward domain;
    exact reverse domain;
    NoDup work keys;
    each live expression occurrence has exactly one work item;
    each work item denotes one live expression occurrence;
    per-file block provenance;
  }.

The exact representation can differ.

Build it once from ci_blocks/ci_visit.

Store it in ExpressionPhase.

Delete prog_work and build_work_sig once replaced.

===============================================================================
5. CONVERSION WORK MUST CARRY ITS CHILDREN
===============================================================================

Use either:

- an ExprWork inductive with leaf and conversion constructors; or
- ExprWork plus total conversion refinement.

A conversion work item must carry:

- conversion ExprRef;
- source TypeSyntax;
- source operand GoExpr;
- target TypeNameRef;
- operand ExprRef;
- target direct-child role proof;
- operand direct-child role proof;
- target-before-operand proof;
- source target recovery;
- source operand recovery;
- exact operand work item;
- proof operand work is in the processed suffix.

No semantic phase may remint these refs.

===============================================================================
6. OUTCOMES FOLD THE RETAINED WORK ORDER
===============================================================================

Replace build_outcomes over raw occurrences.

The builder must accept:

  ExprWorkForest
  TypeNameFactTable

and fold once over ewf_items in the proven bottom-up order.

For each item:

- leaf case constructs its direct status;
- conversion case pattern-matches its carried ConversionWork;
- total prior query uses the carried operand work/ref;
- type-name query uses the carried target ref;
- one convert_const call produces success/failure;
- child failure comes only from a real failed operand outcome.

No view_expr/as_expr/child-ref construction occurs in the outcome fold.

OutcomeCause must be indexed by the exact work item.

===============================================================================
7. OUTCOME TABLE DOMAIN IS THE RETAINED WORK DOMAIN
===============================================================================

ExprOutcomeTable must be indexed by the exact ExprWorkForest.

Carry:

- map;
- total query by work/ref;
- exact key-domain iff membership in ewf_items;
- direct OutcomeCause for every work item;
- unique insertion;
- no foreign/wrong-kind/extra key.

Do not use exists w : ExprWork input as the domain statement unless it additionally proves membership in the
retained forest.

===============================================================================
8. ANNOTATED WORK DERIVES FROM THE SAME FOREST
===============================================================================

Build one proof-backed AnnotatedExprWorkForest from ewf_blocks.

It must reuse the exact ExprWork values. It must not re-inspect raw occurrences or remint work.

Each annotated item carries:

- exact work item;
- outer conversion refs;
- same-file proof;
- strict-ancestor proof;
- nearest-first order;
- NoDup.

Store the annotated forest in ExpressionPhase.

Delete build_awork/build_awork_blocks once replaced.

===============================================================================
9. FACTS AND DIAGNOSTICS CONSUME THE RETAINED OBJECTS
===============================================================================

Facts:

- fold ewf_items;
- total query exact OutcomeTable;
- build one ExprFactTable object;
- phase retains it;
- ep_eft provenance ties it to ep_work + ep_ot;
- ep_facts is eft_map ep_eft.

Diagnostics:

- fold retained annotated-work items;
- total outcome query;
- no work rebuilding;
- phase stores the exact diagnostic list;
- ep_diags is the stored list.

No projection accepts a raw occurrence stream or separately rebuilt work list.

===============================================================================
10. ONE INTRINSIC EXPRESSION PHASE
===============================================================================

Preferred shape:

  ExpressionPhase input := {
    ep_work;
    ep_tnft;
    ep_ot : ExprOutcomeTable ep_work ep_tnft;
    ep_eft : ExprFactTable ep_work ep_ot;
    ep_awork : AnnotatedWorkForest ep_work;
    ep_diags;
    ep_eft_prov;
    ep_diag_prov;
    ep_tnft_prov;
  }.

Use dependent types or explicit equality/provenance fields.

It must be impossible to construct a phase whose fact table, work forest, outcome table, annotation, or
diagnostics came from another object.

===============================================================================
11. DIRECT LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems about the exact objects elaborate consumes.

11.1 Input

- one blocks computation;
- visit is concat of those exact blocks.

11.2 Work forest

- complete and reverse-complete;
- NoDup keys;
- one item per live expression;
- conversion children/suffix exact.

11.3 Outcome table

- built by folding retained work;
- direct cause indexed by work;
- exact domain by work membership;
- one total query;
- one insertion per work item.

11.4 Facts

- exact success projection of retained outcome table over retained work;
- phase's ep_eft is that exact object.

11.5 Diagnostics

- exact projection over retained annotated work;
- outer context facts carried;
- phase's ep_diags is that exact list.

11.6 Sealing

- ElaborationFacts stores ep_tnft and ep_eft by object identity;
- diagnostic failure returns ep_diags from that same phase.

11.7 Specification bridge

After the production objects are correct, prove equality to the existing index-free source specification.

Do not use specification equality as evidence that the production objects are shared.

===============================================================================
12. REAL PHASE FIXTURES
===============================================================================

The fixtures must query the production objects directly.

12.1 Deep valid nest

Prove:

- exact work item count/list;
- exact conversion work refs;
- every conversion total outcome is EOOk;
- ep_diags = [];
- ep_eft is the retained success projection;
- successful elaboration seals that exact ep_eft.

12.2 Deep failure

Prove:

- innermost conversion total outcome is exact EOConvFail;
- each outer conversion total outcome is EOChildFail;
- ep_diags is exactly one reason, not merely nonempty;
- reason carries exact conversion/target/operand refs;
- direct cause uses exact operand EOOk fact.

12.3 Two uint8

Keep the successful ElaborationFacts theorem.

12.4 Exact-domain negative

Prove a foreign key and a known non-expression key cannot occur in ep_work or ep_ot.

Do not discharge the central phase claims only by rewriting to expr_diags/program_typedb.

===============================================================================
13. SCOPE DECISION CORRECTIONS
===============================================================================

13.1 ADR-0001

Keep PROPOSED unless Rob explicitly accepts it.

Reviewer disposition: the corrected linux/amd64/Go-1.23 decision is defensible and ready for human acceptance,
subject to its automatic C5 reopening rule.

Do not self-mark accepted.

13.2 ADR-0002

Set status:

  REJECTED AS WRITTEN — open decision; no numeric implementation change authorized

Correct:

- lexical syntax vs accepted program vs finite conversion;
- long significands vs huge exponent;
- 1e5000 behavior in current use contexts;
- no false claim that a bound is needed for decidable equality/canonical finite data;
- actual possible reasons: kernel/proof evaluation cost, renderer/resource bound, toolchain fidelity, or explicit
  language subset;
- experiments needed to measure those reasons.

SR-009 classification:

  UNRESOLVED EXISTING RESTRICTION

13.3 Ledger classifications

Remove REVIEWED from every PROPOSED classification.

13.4 FilePath/ModulePath

Keep proposed and honest. Do not broaden syntax in this C4 repair.

Name the future decision need and defer implementation to C6 or a separately authorized foundation checkpoint.

===============================================================================
14. REQUIRED DELETION
===============================================================================

Delete or replace:

- raw-occurrence build_outcomes production root;
- build_work_sig;
- prog_work;
- prog_work_fold;
- build_awork;
- build_awork_blocks;
- phase_expr_facts if it rebuilds work;
- phase_expr_diags if it rebuilds work;
- eot_domain_iff_work over arbitrary constructible work;
- OutcomeCause indexed only by raw r/occ;
- ep_facts recomputation;
- phase records which permit foreign ep_eft/ep_diags;
- false comments/gate entries;
- stale NEXT_STEPS HEAD text.

Specification helpers may remain only when clearly named and not consumed by production.

Run full tracked-tree residue searches.

===============================================================================
15. TODO DISCIPLINE
===============================================================================

Continue the TODO experiment, but use one topological object-flow checklist.

Each TODO must state:

- exact object produced;
- exact prior object consumed;
- forbidden reconstruction calls;
- direct theorem;
- deleted old root;
- fixture;
- residue command.

Do not close a TODO because an existential/equality theorem can reconstruct the requested object.

Final report must reproduce the complete table.

===============================================================================
16. WORK LOOP AND TERMINAL NOTIFICATION
===============================================================================

Work continuously.

Do not stop for:

- design approval;
- intermediate green files;
- proof volume;
- large deletion;
- desire to preserve repair-5 proofs;
- a clean incomplete commit.

Stop only COMPLETE or concrete BLOCKED.

At COMPLETE/BLOCKED use the configured notification method.

Fallback terminal text:

FIDO C4 REPAIR 6 COMPLETE

or

FIDO C4 REPAIR 6 BLOCKED

Do not send progress notifications.

===============================================================================
17. FINAL VERIFICATION
===============================================================================

Run on the exact final freeze:

make prove
make e2e
make check
make regenerate
make regen-guard
git diff --check
staged pre-commit hook

Report:

- exact gate count;
- whole-theory audit;
- self-tests A-E;
- alias matrix;
- generated byte identity;
- one blocks/visit computation;
- one retained work forest;
- one retained annotation forest;
- outcome builder call path;
- no raw occurrence work rebuild;
- direct cause by work;
- exact domain membership;
- ep_eft/ep_diags provenance;
- direct phase fixtures;
- scope decision states;
- residue/no-C5;
- git status;
- logs for all C4 and repair-6 ranges.

===============================================================================
18. FINAL FREEZE
===============================================================================

Use implementation commit names until all work and checks are complete.

Then make exactly one:

  review(final): C4 — freeze single retained work-domain candidate

If a later fix is required, make a new superseding freeze and report it. Do not label partial commits
review(final).

Update status files with:

- seventh candidate head;
- sixth blocked candidate 3b4f40e;
- repair-6 range;
- human review pending;
- ADR-0001 proposed;
- ADR-0002 rejected/open;
- C5 forbidden;
- Codex disabled.

Push main without force.

Notify Rob.

Then stop.
