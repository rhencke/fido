Claude Code directive: C4 Implementation Review BLOCKING — member-indexed causal outcome repair 8

Repository:

rhencke/fido

Required clean baseline and eighth blocked C4 candidate:

91e8dbbcd24fc7df678e6b3d68eabb13b686efa1

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

Prior blocked C4 candidates:

89b8e54634e7012612a51990756ad29a579c1b0f
1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca
806ce87373e29b6980e5c3d9d274ffa86580449b
af2fc87e7726a4fc68bb9480c53cf64faa83717b
9d4aff5d94d9aac293ff7fb98a7d9fdd59159022
3b4f40e1f14c501fd76333ec8a8cd3e582ed1598
3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-member-indexed-causal-outcome-repair-8

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

Post-C4 simplification:

FORBIDDEN until C4 is accepted. A separate ruthless trim checkpoint follows human C4 acceptance.

This is Rob's later explicit authorization to repair the one remaining causal-outcome defect at the exact clean
baseline above. It does not replace or weaken the binding C4 contract.

Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5. Do not begin the post-C4 trim.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 91e8dbbcd24fc7df678e6b3d68eabb13b686efa1.

Repair 7 closed the broad retained-object-flow defects. Keep these results unless the causal repair directly
requires a change:

- one retained CompilationInput with one let-bound source traversal;
- one proof-carrying ExprWorkForest object;
- exact forward/reverse work domain and key uniqueness;
- WorkMember as a retained membership handle;
- one dependent ExpressionPhase chain;
- ForestOutcomeTable indexed by the exact forest and TypeNameFactTable;
- AnnotatedExprWorkForest indexed by the exact forest;
- ForestExprFactTable indexed by the exact forest and outcome table;
- ExpressionDiagnostics indexed by the exact annotated forest and outcome table;
- total public outcome queries over WorkMember;
- exact outcome-map domain;
- total fact and diagnostic projection;
- exact object sealing by elaborate_indexed;
- use-context resolution from the already-computed ConstInfo;
- EOConvFail and DRInvalidConversion retaining conversion/target/operand refs;
- source-target preservation in erased diagnostics;
- source-spelling rendering;
- the full accepted/rejected byte/rune alias differential;
- unchanged canonical generated Go bytes;
- scope-ledger wording which separates kernel theorems from external cmd/go adequacy;
- ADR-0001 PROPOSED;
- ADR-0002 REJECTED AS WRITTEN / OPEN;
- no C5 implementation.

The remaining defect is narrow and load-bearing:

The final table carries the old raw-map OutcomeCause, not a cause indexed by the exact conversion WorkMember,
processed suffix, exact operand WorkMember, and exact suffix accumulator.

The semantic fold proves an operand work item exists in the processed tail, then discards that item and performs a
raw map lookup by the carried operand ExprRef key. Later theorems build ConversionWork again and translate the raw
cause into a WorkMember-shaped conclusion.

That is reconstruction after the fact. It does not prove that the semantic step consumed the exact retained
operand member or that the retained cause names the exact prior accumulator which supplied the result.

Do not disturb the now-correct phase chain to patch this. Replace the causal/outcome-fold root beneath
ForestOutcomeTable and reprove the existing projections.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_8.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 member-indexed causal outcome repair 8;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - all eight blocked candidate SHAs, with 91e8dbb as the current repair baseline;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_8.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; member-indexed causal repair active;
   - ADR-0001: PROPOSED;
   - ADR-0002: REJECTED AS WRITTEN / OPEN;
   - automatic Codex review: disabled;
   - C5: forbidden;
   - post-C4 trim: forbidden until acceptance.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-member-indexed-causal-outcome-repair-8
   result: BLOCKING at 91e8dbb; member-indexed causal outcome repair 8 active

   Keep the original C4 contract path and hash.

4. Update .review/SOURCE_FOREST_STATUS.md with a concise, exact record of the blocking classes in section 2.

5. Commit only these authority changes:

   review(repair): C4 — retain the exact member and suffix cause

No Rocq, Docker, e2e, gate, generated, plugin, shell, architecture, persona, life, ADR, or scope-ledger change may
enter that authority commit.

6. After that authority commit and after NEXT_STEPS/STATUS preserve the prior repair history, delete the
   superseded:

   .review/C4_IMPLEMENTATION_REPAIR_7.md

in the first implementation commit. Git history is its archive.

Keep:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_8.md;
- .review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md;
- both current ADR files.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 The semantic fold does not consume ConversionWork

ConversionWork exists and carries:

- target TypeNameRef;
- exact operand WorkMember;
- target/operand ref equations;
- target/operand roles;
- exact target syntax;
- exact operand source expression;
- direct-child keys;
- target-before-operand source order.

But build_outcomes_forest never calls build_conversion_work and never accepts a ConversionWork value.

Its conversion branch destructs the smaller ew_conv field, obtains target and operand refs, proves an operand
member exists in the retained tail, discards that member, and then reads the prior map by the operand ref's
NodeKey.

build_conversion_work is used only in a later fixture/theorem path.

Therefore ConversionWork is not the semantic interface. It is proof support beside the semantic step.

2.2 The exact operand member is proved and discarded

The conversion branch calls ewf_operand_in_tail and obtains:

  w' with In w' rest

It uses w' only to prove that a raw map lookup cannot return None and that the operand key differs from the
current key.

The computed outcome reads:

  from_some (find (node_ref_key (erase_ref opr)) m_rest) Hpres

It does not query a suffix accumulator through the retained operand WorkMember.

The required path is:

  exact conversion member
    -> exact ConversionWork
    -> exact operand member in the processed suffix
    -> total suffix-accumulator query through that member
    -> one convert_const

A proof that a raw key lookup equals the member query after the computation is not enough.

2.3 The production OutcomeCause is still raw

OutcomeCause is indexed by:

- SyntaxIndex;
- TypeNameFactTable;
- raw NodeKeyMap prior;
- raw NodeRef;
- raw SourceOccurrence;
- resulting ExprOutcome.

It is not indexed by:

- the exact ExprWorkForest;
- the exact conversion WorkMember;
- the exact current suffix;
- the exact operand WorkMember in that suffix;
- a proof-carrying suffix accumulator object;
- the exact conversion-work view consumed by the step.

Its conversion constructors carry raw conversion_target_ref / conversion_operand_ref equations and a raw map
find.

This is the repair-5 direct-cause shape, not the forest/member/suffix shape required by repair 7.

2.4 Final-table transport erases the actual prior accumulator

OutcomeCause_add_fresh transports every cause from the suffix map to each larger map.

The final ForestOutcomeTable therefore carries causes stated against the final fot_map.

It no longer retains:

- which prior/suffix accumulator supplied the operand;
- the exact suffix WorkMember used by that step;
- the exact processed-suffix membership relation.

Repair 7 allowed freshness transport only if the retained cause kept those exact identities and suffix relation.

The current relation does not.

2.5 The "work-indexed cause" theorems reconstruct the cause afterward

phase_convok_work_cause, phase_convfail_work_cause, and phase_childfail_work_cause are not projections of a
work-indexed cause stored in ForestOutcomeTable.

They:

1. invert the raw OutcomeCause;
2. receive a separately supplied ConversionWork;
3. compare the raw target/operand refs to that view;
4. turn the raw final-map find into total_forest_outcome_at on cw_operand_work.

These theorems prove extensional agreement with a retained WorkMember view. They do not prove the fold used that
view or that the table retained it.

The comment calling them "the production cause form" is false.

2.6 cw_target_before_op is not a processed-suffix proof

cw_target_before_op proves only:

  local(type_name_key current) < local(operand_key current)

That is target-child-before-operand-child source order.

It does not prove:

- cw_operand_work belongs to the exact rest list being processed;
- that rest is the already-built suffix accumulator domain;
- the current semantic step queried that suffix accumulator through cw_operand_work.

Comments and gate text call cw_target_before_op the "processed-suffix order." Correct or delete those claims.

2.7 ForestOutcomeTable carries the wrong invariant

ForestOutcomeTable is correctly indexed by the exact forest and table and has an exact domain.

Its fot_caused field still stores:

  outcomes_caused ... raw pair projection ... fot_map

where outcomes_caused carries raw OutcomeCause values.

The table needs a member-indexed retained causal trace/invariant. Exact domain alone does not repair the causal
loss.

2.8 The direct fixture builds ConversionWork after the table result

deep_fail_innermost_operand_member:

- obtains a retained work member;
- builds ConversionWork after the phase is complete;
- queries the final table;
- applies phase_convfail_work_cause to translate the raw cause.

It does not project the ConversionWork and suffix-member cause that the production step retained, because
production retained no such cause.

The replacement fixture must query the exact cause object stored in the outcome table.

2.9 Current gate and prose overclaim the cause

At minimum, current gate and GoCompile comments say:

- the production cause is forest/work-indexed;
- it retains exact ConversionWork;
- it retains processed-suffix order through cw_target_before_op;
- the operand outcome is read through the exact WorkMember;
- the cause is a projection, not reconstruction.

Those claims do not match the code.

Correct:

- .review/NEXT_STEPS.md;
- .review/SOURCE_FOREST_STATUS.md;
- ARCHITECTURE.md;
- PROGRESS.md;
- GoCompile.v comments;
- gate/axiom_gate.v comments;
- final completion report.

Do not weaken the words. Make the implementation true first.

===============================================================================
3. REQUIRED SUFFIX-MEMBER ABSTRACTION
===============================================================================

Keep WorkMember forest.

Add an exact retained suffix-member handle, equivalent to:

  SuffixMember forest items :=
    { wm : WorkMember forest |
        In (proj1_sig wm) items }

The exact representation may differ.

Required properties:

- it retains the exact WorkMember from the one forest;
- it proves membership in the exact suffix list processed by the accumulator;
- it exposes the same ExprRef/NodeRef/source view as the forest member;
- a conversion step's operand is returned as a SuffixMember of the exact current rest list;
- no equal-key arbitrary ExprWork can substitute for it.

Add a total conversion-step view, equivalent to:

  ConversionStep forest current rest ts x := {
    cs_current        : WorkMember forest;
    cs_current_exact  : proj1_sig cs_current = current;
    cs_conversion     : ConversionWork forest current ts x;
    cs_operand_suffix : SuffixMember forest rest;
    cs_operand_exact  :
      proj1_sig (proj1_sig cs_operand_suffix)
      = proj1_sig (cw_operand_work cs_conversion)
  }.

The exact layout may be smaller.

The semantic fold must construct this value once for the conversion head and consume it directly.

The existing ConversionWork can remain as the source/forest conversion view. It must no longer be absent from
the semantic branch.

===============================================================================
4. REQUIRED PROOF-CARRYING SUFFIX ACCUMULATOR
===============================================================================

Replace the raw recursive result:

  { m : NodeKeyMap ExprOutcome | ... }

with one retained proof-carrying accumulator object indexed by the exact suffix, equivalent to:

  OutcomeAccumulator forest tnft items := {
    oa_map       : NodeKeyMap ExprOutcome;
    oa_domain    : exact domain = items;
    oa_total     : forall sm : SuffixMember forest items, ExprOutcome;
    oa_total_find;
    oa_causes    : exact member/suffix-indexed causes for items
  }.

The exact record/inductive design is your choice.

Rules:

- the empty suffix has one empty accumulator;
- the cons step consumes the exact accumulator for rest;
- a leaf adds one leaf step;
- a conversion constructs one ConversionStep for current/rest;
- the conversion queries the rest accumulator through cs_operand_suffix;
- no raw find option is the semantic interface;
- no from_some on a raw map lookup appears in the conversion semantic branch;
- the map may remain an internal field and a public projection;
- a missing outcome is unrepresentable through the typed suffix query.

A recursive proof-carrying trace is also acceptable:

  OutcomeTrace forest tnft items

where each cons node retains:

- the exact tail trace/accumulator;
- the exact head WorkMember;
- the exact step cause;
- the inserted outcome;
- the resulting map.

Choose the smallest form which makes the direct cause true by construction.

===============================================================================
5. REQUIRED MEMBER/SUFFIX-INDEXED DIRECT CAUSE
===============================================================================

Delete or replace the production OutcomeCause shape.

The production cause for a current member must be indexed by:

- exact forest;
- exact TypeNameFactTable;
- exact current WorkMember;
- exact current rest/suffix;
- exact prior OutcomeAccumulator for that rest;
- exact resulting outcome.

For a conversion cause, carry one exact ConversionStep.

Conversion success must carry directly:

- cs_conversion / cw_target_ref;
- type_name_fact_at_table tnft at that target ref;
- cs_operand_suffix;
- total suffix outcome query = EOOk opf;
- one convert_const success;
- exact stored ExprFact.

Local conversion failure must carry directly:

- the same exact target fact;
- the same exact operand suffix member;
- total suffix outcome query = EOOk opf;
- one convert_const rejection;
- exact EOConvFail fields, including the same operand ExprRef.

Child failure must carry directly:

- the exact operand suffix member;
- total suffix outcome query is EOConvFail or EOChildFail;
- exact EOChildFail result.

Leaf cause must be indexed by the exact leaf WorkMember and its exact source view.

The source specification bridge to const_info, occ_expr_fact, local_conv_failure, and diagnostic exactness remains
separate.

===============================================================================
6. REQUIRED FINAL FOREST OUTCOME TABLE
===============================================================================

ForestOutcomeTable must continue to be indexed by the exact forest and TypeNameFactTable.

Replace fot_caused with a retained member-indexed causal object derived from the complete accumulator/trace.

The final table must provide total queries:

  total_forest_outcome_at :
    ForestOutcomeTable forest tnft ->
    WorkMember forest ->
    ExprOutcome

and direct cause queries equivalent to:

  total_forest_outcome_cause :
    forall wm : WorkMember forest,
      FinalMemberCause forest tnft table wm
        (total_forest_outcome_at table wm)

where FinalMemberCause retains an existential exact split:

  ewf_items forest = prefix ++ current :: rest

and the exact suffix accumulator/step cause used when current was inserted.

It is allowed to prove that the suffix result equals the final-map result by freshness.

It is not allowed to discard the suffix accumulator/member and retain only a raw final-map find.

Keep:

- exact domain;
- wrong-kind/foreign absence;
- total WorkMember query;
- one insertion per member.

===============================================================================
7. SEMANTIC STEP RESTRICTIONS
===============================================================================

In the conversion branch of the production fold:

Allowed:

- exact current WorkMember;
- exact ConversionStep;
- exact suffix accumulator;
- total query through cs_operand_suffix;
- total type-name fact query through cw_target_ref;
- one convert_const;
- insertion of one stored outcome.

Forbidden:

- destruct ew_conv as the whole semantic interface when ConversionWork/ConversionStep exists;
- raw NodeKeyMap.find for the operand;
- from_some around a raw operand lookup;
- operand_key as the live lookup;
- re-running ewf_operand_in_tail separately for presence and freshness;
- conversion_target_ref / conversion_operand_ref calls;
- reconstructing ConversionWork after the result;
- source const_info or local_conv_failure.

Raw key formulas may remain inside the construction/proof of ConversionStep.

===============================================================================
8. EXISTING PHASE OBJECTS
===============================================================================

Keep the correct retained objects:

- CompilationInput;
- ExprWorkForest;
- AnnotatedExprWorkForest;
- ForestExprFactTable;
- ExpressionDiagnostics;
- ExpressionPhase.

Re-index ForestOutcomeTable and the downstream wrappers only as needed to consume the corrected accumulator/cause.

The dependent ExpressionPhase chain must remain:

  work
    -> tnft
    -> corrected outcome table
    -> annotated work
    -> fact table
    -> diagnostics

Do not reopen the object-flow architecture which repair 7 got right.

===============================================================================
9. REQUIRED LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems over the exact production definitions.

9.1 Suffix membership

Prove:

- every conversion head has one exact operand SuffixMember in its current rest;
- that member is the same WorkMember carried by ConversionWork;
- its source expression is the exact operand expression;
- no nonmember or equal-key fresh work value can be used.

9.2 Suffix accumulator

Prove:

- exact domain for each suffix accumulator;
- total query for every SuffixMember;
- no total query for a nonmember;
- cons extends the exact tail accumulator once;
- each forest member is inserted exactly once.

9.3 Direct conversion cause

State the main theorems over:

- exact current WorkMember;
- exact rest list;
- exact ConversionStep;
- exact tail accumulator;
- exact target fact;
- exact operand suffix query.

Prove success, local failure, and child failure directly.

Do not begin with or invert raw OutcomeCause.

9.4 Final-table retained cause

Prove the final table's cause query returns the exact insertion step/suffix cause for every retained member.

9.5 Specification bridges

Separately prove:

- direct cause agrees with const_info/outcome_matches;
- fact projection equals prog_expr_facts;
- diagnostic projection equals expr_diags;
- elaboration decision equals GoCompile.

Do not use specification equality as production-cause evidence.

9.6 One semantic call

The source of the conversion cons step must contain one convert_const call.

No helper in that live call closure may call convert_const or recursively evaluate the conversion subtree.

9.7 Existing phase/sealing results

Reprove and keep:

- exact forest object passed through the phase;
- exact outcome table object consumed by facts and diagnostics;
- exact TypeNameFactTable and ExprFactTable sealed on success;
- no fail-open lookup;
- alias/source/render/diagnostic claims.

===============================================================================
10. REQUIRED DIRECT FIXTURES
===============================================================================

Update the deep fixtures to project the retained direct cause from the corrected outcome table.

For the innermost failing conversion prove directly:

- exact conversion WorkMember;
- exact ConversionStep retained by its cause;
- exact operand SuffixMember;
- operand suffix query = EOOk opf;
- target fact query;
- convert_const rejection;
- exact EOConvFail fields;
- same operand WorkMember/ExprRef appears in DRInvalidConversion.

For each enclosing conversion prove directly:

- exact child-failure cause;
- exact operand SuffixMember;
- operand suffix query is a failure;
- result is EOChildFail;
- no local reason.

For the valid deep chain prove:

- one retained cause per member;
- each conversion's exact operand suffix query;
- each conversion success;
- no duplicate conversion step;
- leaf success;
- empty diagnostics.

Do not build ConversionWork after querying the final outcome merely to reinterpret a raw cause.

Keep source-spec fixtures separately.

Keep the real successful two-uint8 ElaborationFacts fixture.

===============================================================================
11. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Inspect and normally delete/replace from the production proof root:

- OutcomeCause in its raw idx/tnft/prior-map/node/occurrence form;
- OutcomeCause_add_fresh;
- outcomes_caused and its raw-pair domain;
- outcomes_caused_add / outcomes_caused_covers if superseded;
- fot_caused in its raw outcomes_caused form;
- phase_convok_cause;
- phase_convfail_cause;
- phase_childfail_cause;
- phase_convok_work_cause / phase_convfail_work_cause / phase_childfail_work_cause if they remain post-hoc
  translations instead of direct projections;
- comments which call cw_target_before_op a suffix proof;
- gate entries which certify the rejected raw cause.

outcome_matches, local_conv_failure, const_info, and source diagnostics may remain as specification helpers when
used only by separate exactness bridges.

Run full tracked-tree residue searches for:

- raw OutcomeCause in production;
- raw prior-map find as the conversion semantic lookup;
- from_some of a raw operand lookup;
- build_conversion_work used only after final outcome construction;
- "processed-suffix" claims attached only to cw_target_before_op;
- "projection" claims backed by post-hoc translation;
- old conversion constructors;
- duplicate resolver/spelling tables;
- C5 uintptr/rune implementation.

===============================================================================
12. SCOPE DECISIONS
===============================================================================

Do not change the numeric model or scope decisions in this repair.

Keep:

- ADR-0001: PROPOSED;
- ADR-0002: REJECTED AS WRITTEN / OPEN;
- SR-009: UNRESOLVED EXISTING RESTRICTION;
- all ledger entries PROPOSED unless Rob explicitly accepts them.

Only fix a scope/prose statement if this repair makes it false.

===============================================================================
13. BEHAVIORAL TODO DISCIPLINE
===============================================================================

Use Claude Code's TODO list throughout.

Each TODO must include:

- exact object produced;
- exact prior object consumed;
- production function;
- direct causal invariant retained;
- observable completion condition;
- load-bearing theorem;
- impossible branch removed;
- old path deleted;
- direct fixture;
- residue search;
- status.

Minimum TODOs:

T1 — SuffixMember and ConversionStep
T2 — proof-carrying suffix OutcomeAccumulator/trace
T3 — conversion fold uses exact ConversionStep + total suffix member query
T4 — member/suffix-indexed direct success cause
T5 — member/suffix-indexed direct local-failure cause
T6 — member/suffix-indexed direct child-failure cause
T7 — ForestOutcomeTable retains exact insertion cause
T8 — fact/diagnostic/spec bridges re-proved
T9 — direct deep fixtures query retained causes
T10 — old raw cause root deleted
T11 — gate/prose/residue corrected
T12 — full verification/freeze/push

A TODO is not complete because a theorem with a matching noun exists.

The final report must reproduce the completed TODO table and point to exact definitions/theorems/fixtures/search
results.

===============================================================================
14. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously.

Use this loop:

1. remove the raw OutcomeCause production boundary;
2. define suffix membership and accumulator/trace;
3. make the conversion fold consume ConversionStep;
4. retain exact causes in the final table;
5. reprove facts, diagnostics, and source bridges;
6. replace post-hoc cause theorems;
7. update direct fixtures;
8. delete residue;
9. run narrow proof checks;
10. run the full verification;
11. audit the actual production call path and TODO table;
12. repeat until clean.

Do not stop for:

- design approval;
- an intermediate green module;
- proof volume;
- a large diff;
- fear of deleting the current cause proof family;
- a clean but incomplete commit;
- a question decided by this directive or the binding contract.

Stop only in one of two terminal states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after direct repair attempts. Report the exact file,
definition/theorem or command, the smallest failing case, and why neither this directive nor the binding contract
decides it.

Ordinary dependent-proof work is not a blocker.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 8 COMPLETE

or

FIDO C4 REPAIR 8 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
15. FINAL VERIFICATION
===============================================================================

Run from a clean supported environment:

make prove
make e2e
make check
make regenerate
make regen-guard
git diff --check

Run the staged pre-commit check on the complete candidate.

Report:

- exact readable assumption gate count and result;
- whole-theory audit and self-tests A-E;
- full pinned-Go alias matrix;
- exact generated go.mod and recursive .go byte identity;
- full old-constructor/no-C5 search;
- duplicate type-name spelling/resolver search;
- standard-collection audit;
- exact build_expression_phase call path;
- exact build_forest_outcome_table call path;
- exact conversion cons-step source;
- one retained ConversionStep;
- one exact operand SuffixMember;
- total suffix-accumulator query;
- exact retained prior accumulator in the cause;
- one convert_const call;
- final-table direct cause query;
- total fact and diagnostic projections;
- direct deep fixtures;
- raw-cause residue search;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 91e8dbb..final.

Green commands do not replace the causal-object audit.

===============================================================================
16. FINAL FREEZE AND PUSH
===============================================================================

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 member-indexed causal outcome repair 8 candidate complete;
   - original C4 baseline: 8c9212a;
   - all eight blocked candidates, ending at 91e8dbb;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-8 range: 91e8dbb..this freeze commit;
   - human C4 Implementation Review pending;
   - ADR-0001 PROPOSED;
   - ADR-0002 REJECTED AS WRITTEN / OPEN;
   - automatic Codex review disabled;
   - C5 forbidden;
   - post-C4 trim forbidden until C4 acceptance.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-member-indexed-causal-outcome-repair-8
   result: eighth BLOCKING result repaired; new human C4 Implementation Review pending

3. Use ordinary `impl(...)` commits during implementation.

4. Make exactly one final freeze commit after all implementation, proof, test, residue, and prose work passes:

   review(final): C4 — freeze member-indexed causal outcome candidate

5. Run every final check and causal-object audit on that exact commit.

6. If anything fails, repair it and create a new final freeze commit. Only the latest passing freeze is the candidate.

7. Push main without force.

8. Notify Rob and report:

   - all baselines and candidate SHAs;
   - repair-8 authority commit;
   - final candidate SHA and ranges;
   - exact files changed;
   - deleted raw cause root;
   - suffix-member and accumulator design;
   - exact ConversionStep consumed by production;
   - exact operand suffix query;
   - exact retained direct causes;
   - final table cause query;
   - re-proved facts/diagnostics/spec bridges;
   - direct fixtures;
   - full verification;
   - gate count;
   - generated-byte identity;
   - residue/no-C5 results;
   - completed behavioral TODO table;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop.

Do not begin C5.

Do not begin the post-C4 trim.
