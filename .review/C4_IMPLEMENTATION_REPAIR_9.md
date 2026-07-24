Claude Code directive: C4 Implementation Review BLOCKING — close the final-to-tail causal trace 9

Repository:

rhencke/fido

Required clean baseline and ninth blocked C4 candidate:

a2a5b46026cc658f41cb04f6d6cb30a29335671c

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
91e8dbbcd24fc7df678e6b3d68eabb13b686efa1

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-final-to-tail-causal-closure-repair-9

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

Post-C4 simplification:

FORBIDDEN until C4 is accepted. A separate ruthless trim checkpoint follows human C4 acceptance.

This is Rob's later explicit authorization to close the one remaining causal-retention defect at the exact clean
baseline above. It does not replace or weaken the binding C4 contract.

Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5. Do not begin the post-C4 trim.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at a2a5b46026cc658f41cb04f6d6cb30a29335671c.

Repair 8 correctly repaired the live semantic step. Keep these results unless the final causal closure directly
requires a change:

- one immutable GoProgram source authority;
- one retained CompilationInput;
- one proof-carrying ExprWorkForest;
- exact WorkMember and SuffixMember handles;
- ConversionWork and ConversionStep;
- the conversion fold consumes one ConversionStep;
- the operand result is read through cs_operand_suffix by oa_total on the exact rest accumulator;
- one convert_const call in the conversion cons step;
- no raw operand find/from_some/key formula in that semantic branch;
- one dependent ExpressionPhase;
- exact forest-indexed TypeNameFactTable, ForestOutcomeTable, AnnotatedExprWorkForest,
  ForestExprFactTable, and ExpressionDiagnostics;
- exact outcome-table domain and total member query;
- total fact and diagnostic projections;
- exact table sealing;
- source-name alias, rendering, diagnostic, and differential results;
- unchanged generated Go bytes;
- scope ledger and ADR statuses;
- no C5 implementation.

The remaining defect is the final retention boundary:

The fold computes each member from the actual tail OutcomeAccumulator. But the final table does not retain a
causal structure proving that the existential acc_rest inside FinalMemberCause is that actual tail of fot_acc.

FinalMemberCause contains:

- a source-list split;
- an arbitrary OutcomeAccumulator for the rest;
- a StepCause over that accumulator.

It contains no restriction/extension/trace relation between acc_rest and the final fot_acc.

Thus the final object proves only:

  there exists some exact-domain rest accumulator which could cause this final outcome

not:

  this is the exact rest accumulator retained by the recursive production construction, and its operand outcome
  is the same retained operand outcome visible in the final table.

The concrete builder supplies the actual acc_rest, but the public ForestOutcomeTable type allows its fot_acc and
fot_causes fields to be paired with another rest accumulator whenever that alternate accumulator can produce the
same head outcome.

This is the last proof-beside-path gap.

Do not reopen the now-correct source, work, phase, fact, diagnostic, or rendering architecture. Repair the causal
trace beneath ForestOutcomeTable and reprove the direct fixtures.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_9.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 final-to-tail causal closure repair 9;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - all nine blocked candidate SHAs, with a2a5b460 as the current repair baseline;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_9.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; final-to-tail causal closure active;
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
   human_override: C4-final-to-tail-causal-closure-repair-9
   result: BLOCKING at a2a5b460; final-to-tail causal closure repair 9 active

   Keep the original C4 contract path and hash.

4. Update .review/SOURCE_FOREST_STATUS.md with a concise, exact record of the blocking classes in section 2.

5. Commit only these authority changes:

   review(repair): C4 — close the retained causal trace

No Rocq, Docker, e2e, gate, generated, plugin, shell, architecture, persona, life, ADR, or scope-ledger change may
enter that authority commit.

6. After that authority commit and after NEXT_STEPS/STATUS preserve the prior repair history, delete the
   superseded:

   .review/C4_IMPLEMENTATION_REPAIR_8.md

in the first implementation commit. Git history is its archive.

Keep:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_9.md;
- .review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md;
- both current ADR files.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 OutcomeAccumulator carries no causal predecessor

OutcomeAccumulator currently carries:

- oa_map;
- oa_covers;
- oa_domain.

It does not carry:

- the exact tail OutcomeAccumulator from which it was extended;
- the exact current member inserted;
- the exact StepCause used for that insertion;
- a recursive causal trace.

build_outcome_accumulator returns the causes as a separate dependent function beside the accumulator.

The concrete recursion is correct, but the accumulator object alone does not retain how it was built.

2.2 FinalMemberCause does not depend on the final accumulator

FinalMemberCause is indexed by:

- forest;
- tnft;
- items;
- current SuffixMember;
- final outcome.

It is not indexed by the final OutcomeAccumulator.

Its existential acc_rest has no relation to the final table accumulator.

The list split proves only that rest is the source suffix. It does not prove that acc_rest is the causal tail of
fot_acc.

2.3 ForestOutcomeTable permits a foreign causal witness

ForestOutcomeTable stores:

- fot_acc;
- fot_causes;
- fot_match.

fot_causes must produce a FinalMemberCause whose result equals the final query at fot_acc, but the embedded
acc_rest may be any exact-domain rest accumulator which makes a StepCause produce that result.

For example, a conversion cause uses only the operand fact's ConstInfo. An alternate rest accumulator can carry
an EOOk operand fact with the same ConstInfo but a different ef_use_resolved field, while producing the same
conversion result. The final cause would still type-check even though it did not use the actual retained operand
fact in fot_acc.

A child-failure cause can likewise point to any failing rest outcome, not necessarily the one retained in the
final table.

Therefore foreign causal components remain representable.

2.4 The final query cannot connect the operand tail result to the final table

StepCause_convfail_inv proves:

  oa_total acc_rest operand_suffix = EOOk opf

It does not prove:

  total_forest_outcome_at ot operand_work = EOOk opf

or even:

  oa_total acc_rest operand_suffix
  =
  oa_total (fot_acc ot) lifted_operand_member

No retained theorem or field states that extending acc_rest through the prefix preserves every suffix-member
query into fot_acc.

The same gap exists for conversion success and child failure.

2.5 total_forest_outcome_cause returns a possible derivation, not an authenticated insertion trace

total_forest_outcome_cause simply projects fot_causes.

Because FinalMemberCause lacks a final-to-tail relation, the result cannot establish that the returned prior
accumulator and StepCause were the ones used by build_outcome_accumulator.

The comments call it "the exact insertion cause." The type does not justify that claim.

2.6 The actual tail relation is discarded during lifting

In build_outcome_accumulator:

- the head cause stores the actual acc_rest;
- a tail cause is unpacked and repacked while the final accumulator grows.

The proof Hoo establishes one query equality while lifting the tail member.

That equality is used locally and then discarded.

The retained FinalMemberCause does not accumulate a relation from acc_rest to the final accumulator.

2.7 The direct failure fixture stops at the unlinked tail accumulator

deep_fail_innermost_convfail proves:

  oa_total acc_rest (cs_operand_suffix step) = EOOk opf

It does not prove that the same operand WorkMember has EOOk opf in the final table.

It therefore demonstrates the StepCause but not causal closure into ForestOutcomeTable.

2.8 The outer-child and successful-chain fixtures do not inspect retained causes

deep_fail_outer_childfail proves only final outcome shapes through the source-spec bridge.

It does not project total_forest_outcome_cause and prove the exact operand suffix member/result for each outer
conversion.

deep_nested_all_ok proves only EOOk results for the final table.

It does not project each conversion's retained success cause and connect its tail operand result to the final
table.

Repair 8 required these direct cause fixtures.

2.9 Current prose and gate comments overclaim the final cause

At minimum, current comments and status text claim:

- ForestOutcomeTable retains the exact insertion cause;
- total_forest_outcome_cause returns the exact prior accumulator used at insertion;
- direct fixtures project the exact retained operand outcome;
- foreign causal components are unrepresentable.

These claims are false without a final-to-tail relation or retained trace.

Correct:

- .review/NEXT_STEPS.md;
- .review/SOURCE_FOREST_STATUS.md;
- ARCHITECTURE.md;
- PROGRESS.md;
- GoCompile.v comments;
- gate/axiom_gate.v comments;
- final completion report.

Make the implementation true before restoring the strong wording.

===============================================================================
3. REQUIRED CAUSAL TRACE OR FINAL-TO-TAIL RELATION
===============================================================================

Choose the smallest form which makes the actual recursive construction intrinsic.

Preferred design:

  OutcomeTrace forest tnft items

with constructors equivalent to:

  TraceNil :
    OutcomeTrace forest tnft []

  TraceCons :
    forall current rest,
      OutcomeTrace forest tnft rest ->
      StepCause forest tnft current rest (trace_acc tail) outcome ->
      OutcomeTrace forest tnft (current :: rest)

The trace must retain:

- the exact tail trace;
- the exact tail OutcomeAccumulator;
- the exact current member;
- the exact StepCause;
- the exact inserted outcome;
- the exact extended accumulator/map.

Then:

- trace_acc projects the final OutcomeAccumulator;
- trace_cause projects the exact insertion cause for each retained member;
- tail query preservation is derived from the retained recursive structure.

An equivalent smaller design is allowed:

  AccumulatorTail acc_rest acc_full prefix

or:

  AccumulatorExtends acc_rest acc_full suffix

provided it is carried inside FinalMemberCause and proves all of these:

- acc_rest is the exact causal tail from which acc_full was built;
- acc_full equals ordered insertion of the retained prefix over acc_rest;
- every SuffixMember of rest has the same outcome in acc_rest and acc_full;
- the exact operand SuffixMember lifts to the same WorkMember in the final forest;
- no unrelated exact-domain accumulator can satisfy the relation.

A theorem that two independently built accumulators are extensionally equal is not enough.

A relation based only on source semantics is not enough.

The relation must express the actual production construction.

===============================================================================
4. REQUIRED OUTCOME ACCUMULATOR / TRACE OBJECT
===============================================================================

The production result of the recursive fold must be one causal object.

Do not return:

  accumulator * separate cause function

unless the type makes the cause function definitionally dependent on the exact recursive tail objects and
retains their extension relation.

Use one of:

- recursive OutcomeTrace;
- CausalOutcomeAccumulator containing its exact predecessor chain;
- another equivalent dependent object.

The final object must supply:

- final OutcomeAccumulator;
- exact map/domain/total queries;
- exact insertion cause for each member;
- exact final-to-tail query preservation;
- exact source-spec match as a separate field/theorem.

The cause and match may be projections. They must not be freely pairable fields whose only connection is the
current result value.

===============================================================================
5. REQUIRED FINAL MEMBER CAUSE
===============================================================================

Replace FinalMemberCause with a form indexed by the exact final causal object or final accumulator.

It must retain:

- exact current WorkMember;
- exact source-list split;
- exact tail causal object/accumulator;
- proof that this tail is the actual predecessor retained by the final causal object;
- exact StepCause;
- exact lift from every tail SuffixMember to the final forest/table;
- query-preservation theorem.

For conversion success/failure, expose a theorem equivalent to:

  final_operand_outcome :
    total_forest_outcome_at ot
      (lift_suffix_member_to_work_member (cs_operand_suffix step))
    =
    oa_total acc_rest (cs_operand_suffix step)

For local failure, strengthen this to:

  exists opf,
    both queries = EOOk opf

not merely equality of ConstInfo.

For child failure:

  both queries are the same EOConvFail or EOChildFail

For success:

  both queries are the same EOOk operand fact used by convert_const.

===============================================================================
6. REQUIRED FOREST OUTCOME TABLE
===============================================================================

ForestOutcomeTable must retain the exact causal trace/object, not parallel freely pairable fields.

Preferred shape:

  Record ForestOutcomeTable forest tnft := {
    fot_trace : OutcomeTrace forest tnft (ewf_items forest)
  }.

Then derive:

- fot_acc;
- fot_map;
- fot_domain;
- total_forest_outcome_at;
- total_forest_outcome_cause;
- total_forest_outcome_at_matches.

A larger record is acceptable if its constructor requires the final-to-tail causal relation intrinsically.

A caller must not be able to construct a table with:

- one final accumulator;
- a different valid rest accumulator;
- a StepCause which merely happens to produce the same head result.

If practical, seal the constructor behind a module/API. The proof relation must still be complete; opacity is not a
substitute for correctness.

===============================================================================
7. REQUIRED PRODUCTION FOLD
===============================================================================

Keep the repair-8 semantic branch:

- one ConversionStep;
- exact cs_operand_suffix;
- oa_total on the exact tail;
- one type-name query;
- one convert_const;
- one outcome.

Change the recursive result so the exact tail causal object is retained by the cons node.

When lifting a tail member into a larger result:

- retain the extension/trace edge;
- do not use a local Hoo equality and discard it;
- make query preservation available from the final table.

No new semantic path may appear.

No raw operand lookup may return.

===============================================================================
8. REQUIRED LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems over the exact production objects.

8.1 Trace shape

Prove:

- empty trace has empty accumulator;
- cons trace retains the exact tail trace;
- final accumulator is the exact extension of tail accumulator by current outcome;
- each forest item appears in exactly one trace step.

8.2 Query preservation

For every retained trace split and tail SuffixMember, prove:

  tail query = final query at the same retained WorkMember

This theorem must use the retained trace/extension relation.

8.3 Exact insertion cause

For every final WorkMember, total_forest_outcome_cause returns the exact trace node which inserted it.

8.4 Direct conversion success

Prove from the retained trace cause:

- exact ConversionStep;
- exact target fact;
- exact operand tail member;
- tail operand query;
- equal final-table operand query;
- one convert_const success;
- exact current final-table result.

8.5 Direct local failure

Prove the same chain with one convert_const rejection and exact EOConvFail fields.

8.6 Direct child failure

Prove the exact tail and final operand query are the same failure outcome and current is EOChildFail.

8.7 Foreign cause exclusion

Prove or make unrepresentable:

- pairing a final table with an unrelated rest accumulator;
- substituting an equal-key fresh WorkMember;
- changing the operand ExprFact while keeping only its ConstInfo;
- changing the tail outcome while retaining the same current result.

8.8 Specification bridges

Separately reprove:

- final outcomes match the source specification;
- fact projection equals prog_expr_facts;
- diagnostics equal expr_diags;
- elaboration equals GoCompile.

These are not causal-retention proofs.

===============================================================================
9. REQUIRED DIRECT FIXTURES
===============================================================================

9.1 Innermost failure

Strengthen deep_fail_innermost_convfail to prove:

- the retained final cause contains the exact trace tail;
- tail operand query = EOOk opf;
- final-table query at the same operand WorkMember = EOOk opf;
- the two query values are propositionally equal through trace preservation;
- convert_const rejects;
- EOConvFail and DRInvalidConversion name that exact operand ref and status.

9.2 Outer child failures

For each int16/int32/int64 outer conversion:

- project total_forest_outcome_cause;
- invert the retained child-failure StepCause;
- identify the exact operand suffix member;
- prove tail query = final-table query;
- prove that shared outcome is a failure;
- prove current outcome is EOChildFail;
- prove no local diagnostic is emitted.

Do not settle for outcome shape derived from local_conv_failure.

9.3 Valid deep chain

For every conversion in the valid chain:

- project its retained success cause;
- identify exact operand suffix member;
- prove tail query = final-table query = EOOk opf;
- prove the exact one convert_const success;
- prove current final result;
- prove one unique trace step per member.

Keep leaf success and empty diagnostics.

9.4 Existing fixtures

Keep:

- successful two-uint8 ElaborationFacts fixture;
- alias boundaries;
- source-spec fixtures labeled as specifications.

===============================================================================
10. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Inspect and normally delete/replace:

- FinalMemberCause without a final-accumulator/trace relation;
- ForestOutcomeTable parallel fot_acc/fot_causes fields if they remain freely pairable;
- build_outcome_accumulator returning accumulator plus separate unlinked cause function;
- local Hoo query equalities which are not retained in the final causal object;
- total_forest_outcome_cause if it returns only a possible derivation;
- direct fixture helpers which prove only final outcome shape;
- comments/gate entries claiming exact causal closure without query preservation.

Keep SuffixMember, ConversionStep, StepCause, and the semantic branch unless the trace design needs a direct
refactor.

Run full tracked-tree residue searches for:

- existential acc_rest with no relation to fot_acc/final trace;
- cause fields parallel to final accumulator with no extension proof;
- direct cause theorem lacking final operand query equality;
- deep child/success fixtures which never call total_forest_outcome_cause;
- old raw OutcomeCause;
- raw operand lookup;
- old conversion constructors;
- duplicate resolver/spelling tables;
- C5 uintptr/rune implementation.

===============================================================================
11. SCOPE DECISIONS
===============================================================================

Do not change the numeric model or scope decisions in this repair.

Keep:

- ADR-0001: PROPOSED;
- ADR-0002: REJECTED AS WRITTEN / OPEN;
- SR-009: UNRESOLVED EXISTING RESTRICTION;
- all ledger entries PROPOSED unless Rob explicitly accepts them.

Only fix a scope/prose statement if this repair makes it false.

===============================================================================
12. BEHAVIORAL TODO DISCIPLINE
===============================================================================

Use Claude Code's TODO list throughout.

Each TODO must include:

- exact causal object produced;
- exact predecessor/tail object consumed;
- production function;
- final-to-tail relation retained;
- observable completion condition;
- load-bearing theorem;
- impossible foreign pairing removed;
- old path deleted;
- direct fixture;
- residue search;
- status.

Minimum TODOs:

T1 — choose and define OutcomeTrace or exact AccumulatorTail relation
T2 — retain exact tail object in every cons step
T3 — derive final accumulator/map/total query from causal object
T4 — index FinalMemberCause by final causal object
T5 — prove tail-to-final query preservation
T6 — direct conversion-success causal closure
T7 — direct local-failure causal closure
T8 — direct child-failure causal closure
T9 — exclude foreign tail accumulators/facts
T10 — re-root ForestOutcomeTable on causal object
T11 — reprove fact/diagnostic/spec bridges
T12 — strengthen all direct deep fixtures
T13 — delete unlinked cause root
T14 — gate/prose/residue correction
T15 — full verification/freeze/push

A TODO is not complete because the concrete builder happens to choose the right existential witness.

The type and retained object must authenticate that witness.

The final report must reproduce the completed TODO table with exact definitions, theorems, fixtures, and searches.

===============================================================================
13. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously.

Use this loop:

1. design the smallest intrinsic causal trace/extension relation;
2. replace the unlinked accumulator/cause return;
3. make the final table derive from the causal object;
4. prove tail-to-final query preservation;
5. reprove direct success/fail/child causes;
6. strengthen production fixtures;
7. reprove source bridges;
8. delete residue;
9. run narrow checks;
10. run full verification;
11. audit constructor strength and attempt foreign pairings;
12. repeat until clean.

Do not stop for:

- design approval;
- an intermediate green module;
- proof volume;
- a large diff;
- fear of replacing the current accumulator/cause family;
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

FIDO C4 REPAIR 9 COMPLETE

or

FIDO C4 REPAIR 9 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
14. FINAL VERIFICATION
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
- exact causal trace object and constructors;
- exact final-to-tail relation;
- exact build_expression_phase call path;
- exact outcome trace/fold call path;
- one retained ConversionStep;
- one exact operand SuffixMember;
- tail query;
- final query;
- proof those are the same result;
- one convert_const call;
- exact retained insertion cause;
- foreign-pairing exclusion evidence;
- total fact and diagnostic projections;
- direct deep success/fail/child fixtures;
- unlinked-cause residue search;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - a2a5b460..final.

Green commands do not replace the causal-closure audit.

===============================================================================
15. FINAL FREEZE AND PUSH
===============================================================================

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 final-to-tail causal closure repair 9 candidate complete;
   - original C4 baseline: 8c9212a;
   - all nine blocked candidates, ending at a2a5b460;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-9 range: a2a5b460..this freeze commit;
   - human C4 Implementation Review pending;
   - ADR-0001 PROPOSED;
   - ADR-0002 REJECTED AS WRITTEN / OPEN;
   - automatic Codex review disabled;
   - C5 forbidden;
   - post-C4 trim forbidden until C4 acceptance.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-final-to-tail-causal-closure-repair-9
   result: ninth BLOCKING result repaired; new human C4 Implementation Review pending

3. Use ordinary impl(...) commits during implementation.

4. Make exactly one final freeze commit after all implementation, proof, test, residue, and prose work passes:

   review(final): C4 — freeze causally closed outcome-trace candidate

5. Run every final check and causal-closure audit on that exact commit.

6. If anything fails, repair it and create a new final freeze commit. Only the latest passing freeze is the candidate.

7. Push main without force.

8. Notify Rob and report:

   - all baselines and candidate SHAs;
   - repair-9 authority commit;
   - final candidate SHA and ranges;
   - exact files changed;
   - deleted unlinked cause root;
   - causal trace/extension design;
   - exact tail retained per member;
   - tail-to-final query preservation;
   - exact ConversionStep and operand member;
   - exact retained direct success/fail/child causes;
   - direct fixtures;
   - re-proved bridges;
   - full verification;
   - gate count;
   - generated-byte identity;
   - residue/no-C5 results;
   - completed behavioral TODO table;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop.

Do not begin C5.

Do not begin the post-C4 trim.
