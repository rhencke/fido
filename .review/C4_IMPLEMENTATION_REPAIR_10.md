Claude Code directive: C4 Implementation Review BLOCKING — evidence and status closeout repair 10

Repository:

rhencke/fido

Required clean baseline and tenth blocked C4 candidate:

a8a44723250edd776c62dbb362d8fab51c21ab8f

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
a2a5b46026cc658f41cb04f6d6cb30a29335671c

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-evidence-status-closeout-repair-10

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

Post-C4 simplification:

FORBIDDEN until C4 is accepted.

This is Rob's later explicit authorization for a narrow evidence/status closeout at the exact clean baseline
above. It does not replace or weaken the binding C4 contract.

Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5. Do not begin the post-C4 trim.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at a8a44723250edd776c62dbb362d8fab51c21ab8f.

The production architecture now passes the causal-path review.

Keep all of these results unless an acceptance theorem needs a direct statement-only adjustment:

- one immutable GoProgram source authority;
- one retained CompilationInput;
- one proof-carrying ExprWorkForest;
- exact WorkMember and SuffixMember handles;
- ConversionWork and ConversionStep;
- one member/suffix-indexed StepCause;
- one intrinsic OutcomeTrace indexed by the exact OutcomeAccumulator it builds;
- TraceCons retaining the exact tail trace, tail accumulator, current item, freshness, and StepCause;
- one ForestOutcomeTable containing fot_acc plus fot_trace indexed by fot_acc;
- total_forest_outcome_cause projected from the retained trace;
- tail-to-final query preservation;
- final_operand_outcome connecting the exact tail operand result to the final-table operand result;
- the conversion semantic branch consuming one ConversionStep and one exact operand SuffixMember;
- one total tail query and one convert_const call per conversion step;
- no raw operand lookup, no recursive semantic rescan, no equivalent table rebuild, no post-hoc cause
  reconstruction;
- one dependent ExpressionPhase object chain;
- total facts and diagnostics projected from the same retained outcome table;
- exact table sealing on successful elaboration;
- all source-name, alias, renderer, diagnostic, and differential results;
- unchanged canonical generated Go bytes;
- no C5 implementation.

No new production-root defect was found in this review.

The candidate remains BLOCKING because the repository's claimed acceptance evidence and current status are not
yet exact:

1. the strongest new direct causal-closure fixtures are not in the readable assumption gate;
2. the innermost failure fixture does not connect its retained EOConvFail cause to the exact stored
   DRInvalidConversion reason required by the repair;
3. the public outer-failure and valid-chain concrete theorem statements discard important exact relations proved
   by their helpers;
4. the permanent SOURCE_FOREST_STATUS ledger contains a false, contradictory "CURRENT repair 7 ACTIVE" section
   and old "repository HEAD" claims.

This repair is an evidence/prose closeout, not another architecture redesign.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_10.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 evidence and status closeout repair 10;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - all ten blocked candidate SHAs, with a8a44723 as the current repair baseline;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_10.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; evidence/status closeout active;
   - production architecture disposition: no new production-path defect found; retain repair-9 architecture;
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
   human_override: C4-evidence-status-closeout-repair-10
   result: BLOCKING at a8a44723; evidence and status closeout repair 10 active

   Keep the original C4 contract path and hash.

4. Replace the current-state portion of .review/SOURCE_FOREST_STATUS.md with an exact concise record of the
   findings in section 2. Do not append another contradictory history layer.

5. Commit only these authority changes:

   review(repair): C4 — close acceptance evidence and current status

No Rocq implementation, Docker, e2e, gate, generated, plugin, shell, architecture, persona, life, ADR, or
scope-ledger change may enter that authority commit.

6. After that authority commit and after current status preserves the prior repair history, delete the
   superseded:

   .review/C4_IMPLEMENTATION_REPAIR_9.md

in the first implementation commit. Git history is its archive.

Keep:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_10.md;
- .review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md;
- both current ADR files.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 The new causal-closure fixtures are not gated

Repair 9 added:

- deep_fail_childfail_closure_at;
- deep_nested_ok_closure_at;
- deep_fail_outer_operands_final_fail;
- deep_nested_chain_operands_final_ok.

These are the concrete surfaces which close tail outcomes into the final table.

The readable gate still prints the older shape fixtures:

- deep_fail_outer_childfail;
- deep_nested_all_ok;

and does not print the new final-to-tail closure fixtures.

The gate comments claim direct final-to-tail closure, but the printed concrete theorem set does not include the
theorems which state it.

Add direct Print Assumptions entries for the final closure fixtures selected as accepted public evidence.

At minimum gate:

- deep_fail_innermost_convfail;
- deep_fail_childfail_closure_at or a stronger universal theorem it instantiates;
- deep_nested_ok_closure_at or a stronger universal theorem it instantiates;
- deep_fail_outer_operands_final_fail;
- deep_nested_chain_operands_final_ok;
- the exact diagnostic fixture required by section 3;
- the unique-trace-step theorem required by section 5.

Do not rely only on whole-theory Fido Audit Assumptions. The readable gate is the reviewed public claim surface.

2.2 The innermost failure fixture stops before the stored diagnostic reason

deep_fail_innermost_convfail now correctly proves:

- exact retained conversion WorkMember;
- exact retained trace tail;
- exact ConversionStep;
- exact operand SuffixMember;
- tail operand query = EOOk opf;
- final-table query at the same operand WorkMember = EOOk opf;
- equality of tail and final queries;
- one rejecting convert_const;
- exact EOConvFail fields.

It does not prove that the phase's stored diagnostic is the exact DRInvalidConversion produced from those same
fields.

deep_fail_exactly_one_diag proves only that the diagnostic list length is one, through the source-spec bridge.

Repair 9 required the concrete fixture to establish that EOConvFail and DRInvalidConversion name the same exact:

- primary conversion ExprRef;
- target TypeNameRef;
- operand ExprRef;
- resolved target;
- operand ConstInfo/status.

Add one direct production-object theorem. An acceptable shape is:

  exists wm rest acc_rest step opf t outer,
    retained conversion cause ...
    /\ ep_diags phase =
         [DRInvalidConversion
            (ew_expr_ref (proj1_sig wm))
            (cw_target_ref (cs_conversion step))
            (ew_expr_ref (proj1_sig (cw_operand_work (cs_conversion step))))
            outer
            t
            (ef_const_status opf)]
    /\ outer is the exact retained nearest-first enclosing context.

A membership theorem plus length = 1 is also acceptable if the conjunction identifies the same exact fields.

The proof must start from:

- ep_diag / ep_diags;
- the retained AnnotatedExprWorkForest;
- the exact ForestOutcomeTable;
- the exact stored EOConvFail / StepCause.

It must not establish the field identity only by calling local_conv_failure or recursive const_info.

The separate source-spec bridge can remain as confirmation.

2.3 The public outer-child concrete theorem discards the exact operand relation

deep_fail_childfail_closure_at is strong. It returns:

- exact current WorkMember;
- exact rest accumulator;
- exact ConversionStep;
- tail operand failure;
- final-table operand query = tail query;
- final-table operand failure;
- current EOChildFail.

deep_fail_outer_operands_final_fail then projects this down to arbitrary existential wm/opw values and says only
that opw has a failing final outcome.

Its statement no longer shows that:

  opw = proj1_sig (cs_operand_suffix step)

or that the same exact tail outcome equals the final outcome.

Either:

- gate deep_fail_childfail_closure_at as the accepted direct theorem and label
  deep_fail_outer_operands_final_fail as a short corollary; or
- strengthen the concrete theorem statement to retain the ConversionStep and exact operand relation.

Also prove, for each outer conversion, that no local DRInvalidConversion is emitted for that current member.
Do not use "the whole list has length one" as the only evidence for all three outer nodes.

2.4 The public valid-chain theorem discards the success cause

deep_nested_ok_closure_at is strong. It returns:

- exact current WorkMember;
- exact rest accumulator;
- exact ConversionStep;
- tail operand EOOk opf;
- final-table operand EOOk opf;
- equality of tail and final queries;
- the retained StepCause inversion proves one convert_const success and exact current fact.

deep_nested_chain_operands_final_ok projects this down to:

- some conversion member;
- some operand member;
- final operand outcome = EOOk opf.

Its public statement discards:

- that opw is the exact cs_operand_suffix member;
- the tail query;
- the query equality;
- the convert_const success;
- the current conversion's final EOOk fact;
- the exact target fact.

Either gate the strong helper for every representative case or strengthen the concrete theorem to retain these
relations.

Repair 9 also required one unique trace step per retained member. Add a generic theorem over OutcomeTrace, then
instantiate or cite it in the valid deep-chain evidence.

2.5 The current status ledger is factually contradictory

.review/SOURCE_FOREST_STATUS.md begins with the current repair-9 candidate, but later contains:

  ## C4 implementation state

  CURRENT: exact retained work-object repair 7 ACTIVE from baseline 3a92d22

It names the deleted `.review/C4_IMPLEMENTATION_REPAIR_7.md`, calls an old candidate repository HEAD, and describes
superseded work as current.

This is false current authority, not harmless history.

The file itself says Git history is the detailed archive. Honor that rule.

Rewrite SOURCE_FOREST_STATUS as a compact current ledger containing:

- completed C0–C3;
- C4 contract and hash;
- original baseline;
- blocked candidate list;
- current repair-10 authority;
- concise current implementation architecture;
- current verification state;
- ADR/scope states;
- C5/trim prohibition;
- no detailed superseded theorem tables.

Historical repair detail belongs in Git and the superseded repair directives, not active current status.

Do not retain any line which calls:

- repair 7 active;
- a superseded freeze repository HEAD;
- deleted symbols the current production authority;
- a superseded repair file active.

2.6 Permanent prose must distinguish accepted architecture from pending acceptance

ARCHITECTURE.md and PROGRESS.md may describe the actual implemented structure, but no file may state that C4 is
human-accepted before this review closes.

NEXT_STEPS and REVIEW_REQUEST remain pending/blocking until the next candidate is reviewed.

Do not edit life.md.

===============================================================================
3. REQUIRED EXACT DIAGNOSTIC FIXTURE
===============================================================================

Add a concrete theorem tying the innermost retained conversion cause to the exact stored diagnostic.

The theorem must prove all of these in one statement or a small gated theorem family:

1. The exact retained work member's final outcome is:

     EOConvFail er tr opr t ci

2. The retained trace cause proves:

   - er is the work member's own ExprRef;
   - tr is the exact target TypeNameRef from ConversionStep;
   - opr is the exact operand WorkMember's ExprRef;
   - t is the exact TypeNameFact query result;
   - ci is the exact EOOk operand fact's ef_const_status;
   - tail operand query = final operand query = EOOk opf;
   - convert_const t ci = None.

3. The stored phase diagnostic list contains exactly:

     DRInvalidConversion er tr opr outer t ci

   for that cause.

4. The diagnostic's outer context is the exact retained annotation for the same work member.

5. The list contains no second local invalid-conversion reason.

The production diagnostic constructor already projects EOConvFail fields. Make that exact connection visible and
gated.

===============================================================================
4. REQUIRED OUTER-FAILURE EVIDENCE
===============================================================================

For each outer conversion in the deep failing chain, expose a direct theorem whose statement retains:

- exact current WorkMember;
- exact ConversionStep;
- exact operand SuffixMember / WorkMember;
- exact tail OutcomeAccumulator;
- tail operand outcome;
- equal final-table operand outcome;
- that shared outcome is EOConvFail or EOChildFail;
- current final outcome = EOChildFail;
- local diagnostic projection for the current work member = [];
- no DRInvalidConversion with the current ExprRef as primary.

A universal theorem over any retained SCChildFail cause plus three concrete instantiations is preferred to three
large duplicate proofs.

Gate the universal theorem and the concrete aggregate fixture.

===============================================================================
5. REQUIRED VALID-CHAIN EVIDENCE
===============================================================================

Add or expose a universal retained-success theorem over any conversion WorkMember:

Given the retained final cause for a conversion EOOk, return:

- exact ConversionStep;
- exact target fact;
- exact operand SuffixMember;
- tail operand query = EOOk opf;
- final-table operand query = EOOk opf;
- equality of those queries;
- one convert_const success;
- exact current final-table ExprFact.

Gate it.

For the concrete four-deep valid chain, prove every conversion instantiates that theorem.

Add a generic trace uniqueness theorem:

- every WorkMember in ewf_items appears at exactly one TraceCons insertion step;
- no two insertion steps in one OutcomeTrace have the same work key.

Use the retained forest NoDup and trace shape. Gate it.

The concrete valid-chain theorem must retain enough data to show each member's exact success cause. A corollary
which merely states final EOOk values may remain, but it is not the acceptance fixture.

===============================================================================
6. REQUIRED GATE CLOSEOUT
===============================================================================

Update gate/axiom_gate.v so the readable gate directly names the accepted repair-9 evidence.

The causal section must include:

- OutcomeTrace;
- trace_retained_cause;
- final_operand_outcome;
- retained_conversion_closure;
- direct success/failure/child cause theorems;
- trace-step uniqueness;
- final-table domain/totality.

The concrete section must include:

- exact innermost retained failure + diagnostic theorem;
- exact outer child-failure closure aggregate;
- exact valid-chain success closure aggregate;
- exact one diagnostic;
- exact work count;
- wrong-kind/foreign exclusion;
- exact fact-table sealing;
- successful two-uint8 retained-fact fixture.

Remove or relabel gate comments which claim a stronger result than the printed theorem statement.

Run the readable gate and whole-theory audit after these changes.

===============================================================================
7. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Do not alter the production architecture merely to satisfy this closeout.

Delete or rewrite:

- the false "CURRENT repair 7 ACTIVE" status section;
- old "repository HEAD" claims for superseded candidates;
- old behavioral evidence tables which name deleted symbols as though current;
- duplicate current-state prose already preserved by Git history;
- gate comments whose listed theorem set does not prove the described closure.

Keep source/spec helpers needed by live proofs.

Run tracked-tree searches for:

- "CURRENT: exact retained work-object repair 7";
- "repair 7 ACTIVE";
- deleted `.review/C4_IMPLEMENTATION_REPAIR_7.md` as active authority;
- superseded candidate called repository HEAD;
- old raw OutcomeCause/build_outcome_accumulator/FinalMemberCause in live code or current claims;
- final-to-tail fixture names absent from gate;
- C5 uintptr/rune implementation;
- old family-specific conversion constructors.

Inspect every hit in context. Historical statements inside the binding repair-10 directive are allowed.

===============================================================================
8. SCOPE DECISIONS
===============================================================================

Do not change the numeric model or scope decisions in this repair.

Keep:

- ADR-0001: PROPOSED;
- ADR-0002: REJECTED AS WRITTEN / OPEN;
- SR-009: UNRESOLVED EXISTING RESTRICTION;
- every scope-ledger entry PROPOSED unless Rob explicitly accepts it.

Do not begin the DecimalFloat decision work.

===============================================================================
9. BEHAVIORAL TODO DISCIPLINE
===============================================================================

Use Claude Code's TODO list.

Each TODO must contain:

- exact theorem or status object produced;
- exact retained objects consumed;
- observable statement required;
- load-bearing proof;
- weaker prior statement identified;
- gate entry;
- false prose deleted;
- residue search;
- status.

Minimum TODOs:

T1 — exact retained EOConvFail-to-DRInvalidConversion fixture
T2 — universal retained child-failure closure + no-local-reason theorem
T3 — concrete three-outer child-failure closure fixture
T4 — universal retained conversion-success closure theorem
T5 — concrete four-conversion success closure fixture
T6 — unique trace insertion per WorkMember
T7 — readable gate names every selected acceptance theorem
T8 — SOURCE_FOREST_STATUS rewritten as compact current ledger
T9 — permanent prose/residue audit
T10 — full verification/freeze/push

A TODO is not complete because a helper's proof internally knows the fact while its theorem statement discards it.

===============================================================================
10. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this narrow closeout.

Use this loop:

1. strengthen the accepted theorem statements without changing the production root;
2. add the exact diagnostic connection;
3. add child-failure no-local-reason evidence;
4. add valid-success and trace-uniqueness evidence;
5. gate the exact surfaces;
6. replace the contradictory status ledger;
7. run residue searches;
8. run full verification;
9. inspect the exact freeze;
10. repeat until clean.

Do not stop for design approval.

Stop only in one of two terminal states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after direct attempts. Report the exact file, theorem, command,
smallest failing case, and why the binding contract and this directive do not decide it.

Ordinary theorem strengthening, gate work, and status cleanup are not blockers.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 10 COMPLETE

or

FIDO C4 REPAIR 10 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
11. FINAL VERIFICATION
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

- exact readable gate count and result;
- whole-theory audit and self-tests A-E;
- full pinned-Go alias matrix;
- exact generated go.mod and recursive .go byte identity;
- exact retained diagnostic theorem;
- exact outer child-failure closure theorem and fixture;
- exact valid success closure theorem and fixture;
- unique trace-insertion theorem;
- corrected compact current status ledger;
- full old-constructor/no-C5 search;
- duplicate resolver/spelling search;
- false-current-status residue search;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - a8a44723..final.

Green commands do not replace inspection of the theorem statements and status text.

===============================================================================
12. FINAL FREEZE AND PUSH
===============================================================================

After implementation and evidence closeout pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 evidence/status closeout repair 10 candidate complete;
   - original C4 baseline: 8c9212a;
   - all ten blocked candidates, ending at a8a44723;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-10 range: a8a44723..this freeze commit;
   - human C4 Implementation Review pending;
   - production architecture unchanged from the causally closed repair-9 design;
   - ADR-0001 PROPOSED;
   - ADR-0002 REJECTED AS WRITTEN / OPEN;
   - automatic Codex review disabled;
   - C5 forbidden;
   - post-C4 trim forbidden until C4 acceptance.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-evidence-status-closeout-repair-10
   result: tenth BLOCKING result repaired; new human C4 Implementation Review pending

3. Use ordinary impl(...) commits during the closeout.

4. Make exactly one final freeze commit after all theorem, gate, status, residue, and verification work passes:

   review(final): C4 — freeze exact acceptance-evidence candidate

5. Run every final check on that exact commit.

6. If anything fails or any theorem statement/status claim remains weaker or false, repair it and create a new final
   freeze commit. Only the latest passing freeze is the candidate.

7. Push main without force.

8. Notify Rob and report:

   - all baselines and candidate SHAs;
   - repair-10 authority commit;
   - final candidate SHA and ranges;
   - exact files changed;
   - confirmation that the production architecture was not reopened;
   - exact diagnostic-cause theorem;
   - exact outer child-failure/no-local-reason evidence;
   - exact valid-chain success evidence;
   - trace uniqueness evidence;
   - readable gate entries and count;
   - compact status-ledger replacement;
   - full verification;
   - generated-byte identity;
   - residue/no-C5 results;
   - completed behavioral TODO table;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop.

Do not begin C5.

Do not begin the post-C4 trim.
