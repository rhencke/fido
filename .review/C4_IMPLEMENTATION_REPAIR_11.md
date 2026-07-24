Claude Code directive: C4 Implementation Review BLOCKING — final evidence and authority closeout repair 11

Repository:

rhencke/fido

Required clean baseline and eleventh blocked C4 candidate:

3ecf32e3f7b9514070a1025b73231f541990e93c

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
a8a44723250edd776c62dbb362d8fab51c21ab8f

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-final-evidence-authority-closeout-repair-11

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

Post-C4 simplification:

FORBIDDEN until C4 is accepted.

This is Rob's later explicit authorization for one final theorem-statement, gate-comment, and permanent-authority
closeout at the exact clean baseline above.

It does not replace or weaken the binding C4 contract.

Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5. Do not begin the post-C4 trim.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 3ecf32e3f7b9514070a1025b73231f541990e93c.

The production architecture continues to pass review.

No new defect was found in:

- the immutable GoProgram source authority;
- CompilationInput;
- ExprWorkForest;
- WorkMember and SuffixMember;
- ConversionWork and ConversionStep;
- OutcomeAccumulator;
- StepCause;
- OutcomeTrace;
- ForestOutcomeTable;
- the final-to-tail query-preservation path;
- the dependent ExpressionPhase chain;
- fact and diagnostic projection;
- exact sealing;
- rendering, aliases, or generated output.

Do not redesign or refactor those production definitions in this repair.

The candidate remains BLOCKING because repair 10 was an evidence/status closeout and its public theorem statements
and active authority prose are still not exact.

The remaining work is narrow:

1. make the concrete retained-success and retained-failure evidence state every relation the gate prose claims;
2. make the active authority/status/progress/architecture prose describe the current candidate, not repair 7,
   repair 9, or unresolved repair-10 tasks;
3. re-gate the exact statements;
4. run the full verification and freeze.

This is not a production-architecture repair.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE OTHER CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_11.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 final evidence and authority closeout repair 11;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - all eleven blocked candidate SHAs, with 3ecf32e3 as the repair-11 baseline;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_11.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; final evidence/authority closeout active;
   - production architecture disposition: accepted for this repair; no production change authorized;
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
   human_override: C4-final-evidence-authority-closeout-repair-11
   result: BLOCKING at 3ecf32e3; final evidence and authority closeout repair 11 active

   Keep the original C4 contract path and hash.

4. Replace the current-state portion of .review/SOURCE_FOREST_STATUS.md with the concise exact repair-11 state.

5. Commit only these authority changes:

   review(repair): C4 — make final evidence and authority exact

No Rocq theorem, production code, gate, Docker, e2e, generated, plugin, shell, architecture, progress, persona,
life, ADR, or scope-ledger change may enter that authority commit.

6. After that authority commit and after current status preserves the prior repair history, delete:

   .review/C4_IMPLEMENTATION_REPAIR_10.md

in the first implementation commit. Git history is its archive.

Keep:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_11.md;
- .review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md;
- both current ADR files.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 NEXT_STEPS contradicts its own candidate-complete state

.review/NEXT_STEPS.md begins by saying repair 10 is candidate-complete and awaiting human review.

The same active paragraph then says:

  The candidate is BLOCKING only on acceptance-evidence and current-status exactness

and lists the repair-10 defects in present tense:

- closure fixtures are not gated;
- EOConvFail is not connected to DRInvalidConversion;
- public theorems discard exact relations;
- SOURCE_FOREST_STATUS contains false repair-7 authority.

Those statements describe the repair-10 baseline, not the frozen candidate.

Later lines say those defects were repaired and the candidate is pending review.

This active authority pointer is internally contradictory.

Rewrite the opening to state only:

- the production architecture is retained;
- repair-10 evidence work is present;
- the current candidate is blocked by this repair-11 review;
- the exact repair-11 findings below;
- no stale repair-10 task list in present tense.

Historical detail belongs in Git and the repair directives.

2.2 SOURCE_FOREST_STATUS is not a current verification ledger

The file calls itself a compact current ledger but:

- retains the old repair-10 blocking classes in present tense;
- says the final-to-tail fixtures are "NOT in" the gate although they now are;
- says there is no unique trace theorem although one now exists;
- labels its verification section:

    Current verification state (at a8a4472, repair-9 freeze)

  even though the current candidate is 3ecf32e3 with a reported 456/456 gate;
- uses literal `<freeze>` placeholders instead of the contract-approved wording "this freeze commit";
- records the repair-10 candidate as repository HEAD without giving current review disposition.

Rewrite it as current-only.

It must contain:

- C0-C3 accepted;
- C4 contract path/hash;
- original baseline;
- blocked candidate list including 3ecf32e3 as candidate 11;
- repair-11 authority/token;
- current production architecture, concisely;
- current verification result for the final repair-11 freeze;
- current theorem/gate surfaces;
- ADR/scope states;
- C5 and trim prohibition;
- no old unresolved findings;
- no old freeze labeled current verification;
- no literal `<freeze>` placeholder.

The status file may call its own final commit "this freeze commit", per the binding contract. The final report must
give the exact SHA.

2.3 PROGRESS.md still calls repair 7 current

The Source Forest section says:

- seven successive candidates were blocked;
- C4-exact-retained-work-object-repair-7 is applied;
- the current production path is described as that repair.

There have now been eleven blocked candidates, and the live architecture is the repair-9 OutcomeTrace design plus
repair-10 evidence.

This is false permanent project history/current state.

Rewrite that section so it states:

- C0-C3 accepted;
- C4 candidate is pending human review;
- eleven prior candidates were blocked through 3ecf32e3;
- the live architecture is the retained work forest + intrinsic causal trace + exact acceptance evidence;
- no repair number is presented as a permanent architecture name;
- C5 and post-C4 trim remain closed.

Do not append another paragraph while leaving the false repair-7 paragraph intact.

2.4 ARCHITECTURE.md preserves the old C4/C5 alias conflict

The Static Type Universe Arc says:

  uintptr and the predeclared aliases are next

and:

  uintptr + the predeclared aliases are next

But byte/rune source alias identity and resolution are C4 work and are already present in the current candidate.
The binding contract explicitly removed those aliases from C5.

Correct the arc:

- C4: byte/rune source alias resolution;
- C5: uintptr plus rune constants/literals;
- C5 reopens ADR-0001 because uintptr expands target-dependent semantics;
- the post-C4 trim happens before C5.

Do not change the numeric model.

2.5 deep_nested_ok_closure_at does not state the success evidence claimed by the gate

The gate comment calls deep_nested_ok_closure_at an exact direct theorem containing:

- exact ConversionStep;
- tail = final = EOOk opf;
- convert_const success.

Its theorem statement currently returns only:

- current work expression;
- tail operand EOOk opf;
- final operand EOOk opf;
- tail/final query equality.

Its proof obtains:

- the exact convert_const success;
- the exact current final ExprFact;
- the exact target fact query;

then discards them before the theorem statement.

This repeats the exact repair-10 failure class: the proof knows more than the public theorem states.

Fix one of these ways:

A. Strengthen deep_nested_ok_closure_at to return everything from retained_convsuccess_closure:

   - exact current WorkMember;
   - exact current final outcome EOOk f;
   - exact ConversionStep;
   - exact target TypeNameFact query;
   - exact operand SuffixMember;
   - tail operand EOOk opf;
   - final operand EOOk opf;
   - equality of tail and final queries;
   - one convert_const success;
   - exact current ExprFact f.

or:

B. Add a new exact concrete helper with that statement, gate it, and relabel deep_nested_ok_closure_at as an
   operand-closure-only corollary.

Then provide four concrete instantiations for int8/int16/int32/int64 in the deep valid chain.

The accepted concrete theorem must not reduce them to arbitrary wm/opw existential values which discard the
ConversionStep and conversion result.

2.6 deep_fail_innermost_diag does not expose all exact diagnostic-cause relations

deep_fail_innermost_diag correctly proves:

- exact EOConvFail fields;
- exact tail operand EOOk;
- same final operand EOOk;
- convert_const rejection;
- ep_diags is exactly one DRInvalidConversion with those fields.

Its theorem statement does not expose:

- t = tnf_type (type_name_fact_at_table ... exact target ref);
- the exact retained annotated-work entry which supplied outer;
- the generic context facts attached to that retained entry.

The proof obtains t from the retained cause and outer from aewf_items, but the public theorem drops those links.

Strengthen the exact concrete diagnostic theorem to include at least:

- t = tnf_type (type_name_fact_at_table (ep_tnft phase)
      (cw_target_ref (cs_conversion step)));
- an annotated retained member wma such that:
    - In (wma, outer) (aewf_items (ep_awork phase));
    - proj1_sig wma = proj1_sig wm;
- the existing singleton diagnostic equality.

The existing AnnotatedExprWorkForest soundness/same-file/nearest-first/NoDup theorems may supply the context
properties. Gate the exact membership theorem or include the properties in the concrete theorem.

The proof must continue to start from the retained phase outcome/annotation. Do not use local_conv_failure to
reconstruct the reason.

2.7 Gate comments overclaim weaker concrete theorem statements

The readable gate correctly names the new universal theorems and concrete fixtures.

Its comment says deep_nested_ok_closure_at contains convert_const success, which is false.

After theorem strengthening:

- update the comment to match the exact statements;
- gate the exact concrete valid-chain success theorem;
- gate the strengthened exact diagnostic theorem;
- retain the universal success/child/failure/trace theorems;
- keep weaker aggregate shape corollaries only if useful, and label them as corollaries.

The readable gate is the reviewed claim surface. A strong proof hidden in a helper body does not repair a weak
printed theorem statement.

2.8 Freeze/range wording remains placeholder text

NEXT_STEPS and SOURCE_FOREST_STATUS use literal fragments such as:

  8c9212a..<freeze>

The binding contract permits the files to say "this freeze commit" because the commit cannot contain its own SHA.
It does not require a literal placeholder token.

Use:

- full review range: 8c9212a..this freeze commit;
- full repair range: 89b8e54..this freeze commit;
- repair-11 range: 3ecf32e3..this freeze commit.

Report the exact SHA after Git creates the final freeze.

===============================================================================
3. REQUIRED EXACT SUCCESS EVIDENCE
===============================================================================

Add or strengthen a universal-to-concrete theorem family.

3.1 Universal theorem

Keep retained_convsuccess_closure.

Review its statement and ensure it exposes:

- exact current EConvert source view;
- exact current final EOOk f;
- exact ConversionStep;
- exact target fact query;
- exact operand SuffixMember;
- tail operand EOOk opf;
- final operand EOOk opf;
- tail/final query equality;
- one convert_const success;
- f is the exact result fact.

3.2 Concrete helper

Add a helper over a real deep_nested source occurrence which returns the full universal evidence, not a reduced
projection.

3.3 Concrete aggregate

Prove all four conversion occurrences:

- int8(EInt 5);
- int16(int8(...));
- int32(int16(...));
- int64(int32(...));

instantiate the exact helper.

The theorem may be a conjunction of four existential bundles. Each bundle must keep its ConversionStep, target
fact, operand member, tail/final equality, convert_const result, and current final ExprFact.

Keep deep_nested_all_ok as a short shape corollary if useful. It is not the exact acceptance fixture.

===============================================================================
4. REQUIRED EXACT DIAGNOSTIC EVIDENCE
===============================================================================

Strengthen or replace deep_fail_innermost_diag.

It must expose:

- exact current WorkMember;
- exact rest and authenticated tail accumulator;
- exact ConversionStep;
- exact target table query;
- exact operand SuffixMember;
- tail and final operand EOOk opf;
- query equality;
- convert_const rejection;
- exact EOConvFail;
- exact annotated member/context pair;
- exact singleton DRInvalidConversion;
- no second reason.

The exact outer context does not need to be computed as a literal list if the retained annotated-object membership
and generic context well-formedness are in the theorem family.

Gate the exact theorem.

===============================================================================
5. REQUIRED OUTER CHILD-FAILURE EVIDENCE
===============================================================================

Keep retained_childfail_closure and deep_fail_childfail_closure_at.

Ensure the gate comment describes them accurately.

For each outer conversion, accepted evidence must retain:

- exact current work;
- exact ConversionStep;
- exact operand SuffixMember;
- tail/final query equality;
- shared failing operand result;
- current EOChildFail;
- local diagnostic [].

The current strong helper is adequate if gated and if the concrete aggregate is explicitly labeled a weaker
corollary.

Do not claim the weaker aggregate itself retains the relation it discards.

===============================================================================
6. REQUIRED TRACE EVIDENCE
===============================================================================

Keep outcome_trace_unique_step.

Clarify its accepted meaning:

- trace_currents equals ewf_items in order;
- ewf_items keys are NoDup;
- therefore each retained source work item/key has one insertion step.

Do not claim proof-witness identity beyond the WorkMember's retained ExprWork/key identity.

Gate trace_currents_eq and outcome_trace_unique_step.

===============================================================================
7. REQUIRED CURRENT AUTHORITY PROSE
===============================================================================

Update:

- .review/NEXT_STEPS.md;
- .review/REVIEW_REQUEST.md;
- .review/SOURCE_FOREST_STATUS.md;
- PROGRESS.md;
- ARCHITECTURE.md;
- gate/axiom_gate.v comments;
- the relevant GoCompile.v comments.

Rules:

- present tense describes only current code and current review state;
- old defects are either removed or explicitly past tense and brief;
- no repair 7 is called current;
- no old freeze is called current verification;
- no literal `<freeze>` token;
- aliases are C4, not next;
- C5 is uintptr + rune constants/literals;
- C4 remains pending until Rob accepts it;
- post-C4 trim remains closed until acceptance;
- life.md is untouched.

===============================================================================
8. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Delete or rewrite:

- the unresolved repair-10 task paragraph in NEXT_STEPS;
- present-tense old repair-10 findings in SOURCE_FOREST_STATUS;
- stale repair-9 verification heading in current status;
- stale seven-candidate / repair-7-current text in PROGRESS;
- stale alias-next text in ARCHITECTURE;
- gate comments which overclaim deep_nested_ok_closure_at;
- any final report claim not matched by theorem statements.

Run full tracked-tree searches for:

- "The candidate is BLOCKING only on acceptance-evidence";
- "are NOT in the readable assumption gate";
- "there is no unique-trace-step theorem";
- "Current verification state (at `a8a4472`";
- "seven successive candidates";
- "C4-exact-retained-work-object-repair-7 is applied";
- "uintptr + the predeclared aliases are next";
- literal "<freeze>";
- repair 7 ACTIVE;
- old family-specific conversion constructors;
- C5 uintptr/rune implementation.

Historical copies inside the binding repair-11 directive are allowed. Inspect every other hit.

===============================================================================
9. SCOPE DECISIONS
===============================================================================

Do not change the numeric model or approve scope decisions.

Keep:

- ADR-0001: PROPOSED;
- ADR-0002: REJECTED AS WRITTEN / OPEN;
- SR-009: UNRESOLVED EXISTING RESTRICTION;
- every scope-ledger entry PROPOSED unless Rob explicitly accepts it.

Do not begin DecimalFloat decision work.

===============================================================================
10. BEHAVIORAL TODO DISCIPLINE
===============================================================================

Use Claude Code's TODO list.

Each TODO must contain:

- exact theorem/document produced;
- exact retained objects consumed;
- exact statement required;
- weaker prior statement identified;
- gate entry;
- stale prose removed;
- residue search;
- status.

Minimum TODOs:

T1 — strengthen exact concrete retained-success helper
T2 — prove four deep valid conversions retain full success evidence
T3 — strengthen exact EOConvFail-to-diagnostic theorem with target/annotation links
T4 — verify/gate outer child-failure no-local-reason evidence
T5 — correct gate comments and exact printed theorem set
T6 — rewrite NEXT_STEPS current state
T7 — rewrite SOURCE_FOREST_STATUS current-only state and verification
T8 — correct PROGRESS repair history/current architecture
T9 — correct ARCHITECTURE C4/C5 alias timing
T10 — run residue searches
T11 — full verification/freeze/push

A TODO is not complete because a proof body obtains a fact which its theorem statement discards.

===============================================================================
11. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this closeout.

Use this loop:

1. strengthen theorem statements only;
2. reprove their concrete fixtures;
3. align gate comments and entries;
4. rewrite current authority prose;
5. run residue searches;
6. run full verification;
7. inspect exact theorem statements and final current prose;
8. repeat until clean.

Do not redesign the production architecture.

Do not stop for design approval.

Stop only in one of two terminal states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after direct attempts. Report the exact file, theorem,
command, smallest failing case, and why the binding contract and this directive do not decide it.

Ordinary theorem strengthening and prose cleanup are not blockers.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 11 COMPLETE

or

FIDO C4 REPAIR 11 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
12. FINAL VERIFICATION
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
- exact concrete success theorem statements;
- exact concrete diagnostic theorem statement;
- exact child-failure/no-local-reason theorem;
- exact trace uniqueness theorem;
- corrected NEXT_STEPS;
- corrected compact current status ledger and verification state;
- corrected PROGRESS;
- corrected C4/C5 alias timing in ARCHITECTURE;
- full old-constructor/no-C5 search;
- duplicate resolver/spelling search;
- stale-authority residue search;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 3ecf32e3..final.

Green commands do not replace inspection of the theorem statements and active authority prose.

===============================================================================
13. FINAL FREEZE AND PUSH
===============================================================================

After theorem and authority closeout pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 final evidence/authority closeout repair 11 candidate complete;
   - original C4 baseline: 8c9212a;
   - all eleven blocked candidates, ending at 3ecf32e3;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-11 range: 3ecf32e3..this freeze commit;
   - human C4 Implementation Review pending;
   - production architecture unchanged from repair 9;
   - ADR-0001 PROPOSED;
   - ADR-0002 REJECTED AS WRITTEN / OPEN;
   - automatic Codex review disabled;
   - C5 forbidden;
   - post-C4 trim forbidden until acceptance.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-final-evidence-authority-closeout-repair-11
   result: eleventh BLOCKING result repaired; new human C4 Implementation Review pending

3. Use ordinary impl(...) commits during the closeout.

4. Make exactly one final freeze commit after all theorem, gate, authority, residue, and verification work passes:

   review(final): C4 — freeze final exact acceptance candidate

5. Run every final check on that exact commit.

6. If anything fails or any theorem statement/current claim remains weaker or false, repair it and create a new
   final freeze commit. Only the latest passing freeze is the candidate.

7. Push main without force.

8. Notify Rob and report:

   - all baselines and candidate SHAs;
   - repair-11 authority commit;
   - final candidate SHA and ranges;
   - exact files changed;
   - confirmation that production architecture was not changed;
   - exact concrete success evidence;
   - exact diagnostic/annotation evidence;
   - exact child-failure evidence;
   - trace uniqueness evidence;
   - readable gate entries and count;
   - current authority/progress/architecture corrections;
   - full verification;
   - generated-byte identity;
   - residue/no-C5 results;
   - completed behavioral TODO table;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop.

Do not begin C5.

Do not begin the post-C4 trim.
