C4 IMPLEMENTATION REVIEW BLOCKING — REPAIR 12
CURRENT-HEAD INTEGRATED DIRECTIVE

This file supersedes the need to provide the separate repair-12 directive and current-head amendment.
It preserves the full repair requirements and integrates the current Git head handling in one authority.

===============================================================================
CURRENT HEAD AND HISTORY HANDLING
===============================================================================

C4 REPAIR 12 — CURRENT-HEAD AMENDMENT

This amendment supplements:

C4_IMPLEMENTATION_REVIEW_BLOCKING_REPAIR_12.txt

Do not replace or weaken that directive.

Repository:

rhencke/fido

Current branch head:

37c9597f0c2161d69196ace737032370d148a6da

Commit:

review(accept): C4 — accept exact source-type conversion foundation

Disposition of that commit:

The acceptance closeout is superseded. It was documentation-only and did not repair the two blocking defects found
at candidate 48c0b31beb547326b058748a4d38c6cc41013009.

The twelfth blocked implementation candidate remains:

48c0b31beb547326b058748a4d38c6cc41013009

Repair 12 must be implemented on top of current head 37c9597 without resetting, reverting, rewriting, or
force-pushing history.

Before theorem or collection-audit changes:

1. Install .review/C4_IMPLEMENTATION_REPAIR_12.md verbatim from the full repair-12 directive.
2. Correct the acceptance-status documents on top of 37c9597 so they record:
   - the 48c0b31 candidate is BLOCKING;
   - the 37c9597 acceptance closeout is superseded because it changed documentation only and was based on the
     withdrawn green disposition;
   - repair 12 is active;
   - C5 and the post-C4 trim remain forbidden.
3. Use the authority commit required by repair 12:
   review(repair): C4 — make success identity and collection audit exact
4. Continue with the full repair-12 directive exactly as written.
5. The final repair-12 review range is:
   37c9597f0c2161d69196ace737032370d148a6da..final repair-12 freeze
6. Do not count 37c9597 as an implementation candidate. It is a superseded documentation-only acceptance closeout.
7. Do not create repair 13. Repair 12 remains the active repair.

All other baselines, contract hashes, architectural restrictions, theorem requirements, collection-audit
requirements, verification requirements, freeze rules, and C5 prohibitions in the full repair-12 directive remain
unchanged.


===============================================================================
FULL REPAIR 12 DIRECTIVE
===============================================================================

Claude Code directive: C4 Implementation Review BLOCKING — exact success identity and collection-audit closeout 12

Repository:

rhencke/fido

Required clean baseline and twelfth blocked C4 candidate:

48c0b31beb547326b058748a4d38c6cc41013009

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
3ecf32e3f7b9514070a1025b73231f541990e93c

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-final-identity-collection-audit-closeout-repair-12

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

Post-C4 simplification:

FORBIDDEN until C4 is accepted. A separate ruthless trim checkpoint follows human C4 acceptance.

This is Rob's later explicit authorization for a final theorem-identity and collection-audit closeout at the exact
clean baseline above. It does not replace or weaken the binding C4 contract.

Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5. Do not begin the post-C4 trim.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 48c0b31beb547326b058748a4d38c6cc41013009.

The production architecture continues to pass the causal-path review.

Keep all of these results:

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
- no raw operand lookup, recursive semantic rescan, equivalent table rebuild, or post-hoc cause reconstruction;
- one dependent ExpressionPhase object chain;
- total facts and diagnostics projected from the same retained outcome table;
- exact table sealing on successful elaboration;
- exact retained failure-to-diagnostic evidence;
- exact outer child-failure/no-local-reason evidence;
- trace insertion uniqueness;
- all source-name, alias, renderer, diagnostic, and differential results;
- unchanged canonical generated Go bytes;
- no C5 implementation.

No new production-path defect was found.

The candidate remains BLOCKING for two exact closeout defects:

1. The accepted conversion-success theorem family says it returns the exact ConversionStep for source
   EConvert ts x, but its public types instead return an existential ConversionStep ... ts0 x0 with no stated
   equality ts0 = ts and x0 = x.

2. .review/COLLECTION_AUDIT.md declares itself a living current-state inventory, but still names the deleted
   prog_conv_outcomes authority, describes a nonexistent bucket behavior for ExprOutcome storage, combines
   obsolete and current tables in one stale row, and names the nonexistent TFun body as current syntax.

This repair changes theorem statements/proofs, the readable gate, the collection audit, and current authority
prose only.

No production definition, data path, renderer, generator, plugin, Docker path, numeric model, or scope decision
may change.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_12.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 exact success identity and collection-audit closeout 12;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - all twelve blocked candidate SHAs, with 48c0b31 as the current repair baseline;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_12.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; exact success identity and collection-audit closeout active;
   - production architecture disposition: no new production-path defect found; no production change authorized;
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
   human_override: C4-final-identity-collection-audit-closeout-repair-12
   result: BLOCKING at 48c0b31; exact success identity and collection-audit closeout 12 active

   Keep the original C4 contract path and hash.

4. Update .review/SOURCE_FOREST_STATUS.md with a concise exact record of the two findings above.

5. Commit only these authority changes:

   review(repair): C4 — make success identity and collection audit exact

No Rocq theorem change, gate, collection-audit rewrite, permanent architecture prose, Docker, e2e, generated,
plugin, shell, persona, life, ADR, or scope-ledger change may enter that authority commit.

6. After that authority commit and after current status preserves the prior repair history, delete the superseded:

   .review/C4_IMPLEMENTATION_REPAIR_11.md

in the first implementation commit. Git history is its archive.

Keep:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_12.md;
- .review/COLLECTION_AUDIT.md;
- .review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md;
- both current ADR files.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 retained_convsuccess_closure does not expose source-step identity

retained_convsuccess_closure accepts:

  ts x
  ew_expr current = EConvert ts x

but concludes:

  exists ts0 x0,
    step : ConversionStep forest current rest ts0 x0
    ...

It does not conclude:

  ts0 = ts
  x0 = x

and does not return:

  step : ConversionStep forest current rest ts x.

The proof receives the actual StepCause and therefore knows:

  ew_expr current = EConvert ts0 x0

while its input knows:

  ew_expr current = EConvert ts x.

The constructor injectivity needed to identify ts0/x0 with ts/x is available. The theorem discards it.

The gate and permanent prose call the returned value the exact ConversionStep for the source conversion. The
public theorem type does not justify that claim.

2.2 StepCause_ok_conv_inv is the root of the lost identity

StepCause_ok_conv_inv accepts an expected source conversion:

  ew_expr current = EConvert ts0 x0

It then inverts SCConvOk and returns new existential names:

  exists ts x,
    step : ConversionStep ... ts x
    ...

It does not return the SCConvOk constructor's own:

  ew_expr current = EConvert ts x

and does not identify those values with the expected ts0/x0.

Strengthen this theorem at the root.

Preferred result:

  exists (step : ConversionStep forest current rest ts0 x0) opf tc,
    ...

An acceptable alternative keeps existential ts/x but returns and uses:

  ts = ts0 /\ x = x0

The preferred result is cleaner and prevents downstream theorem types from repeating the equality work.

2.3 nested_success_bundle repeats the lost identity

nested_success_bundle ts x says:

  ew_expr current = EConvert ts x

but separately quantifies:

  ts0 x0
  step : ConversionStep ... ts0 x0.

It claims to contain the exact per-conversion success bundle but does not state that the step is for ts/x.

The same defect reaches:

- deep_nested_convsuccess_at;
- deep_nested_chain_success_evidence;
- the readable gate comments;
- current status/progress prose which calls that bundle exact.

The proof may choose the correct witness. The theorem type must authenticate it.

2.4 The living collection audit names a deleted authority

.review/COLLECTION_AUDIT.md says:

  A CURRENT-STATE classification ...

and:

  This is a living current-state inventory, maintained at every checkpoint ...

Its C4 outcome/fact row still names:

  GoCompile.prog_conv_outcomes

That symbol does not exist in the current theory.

The row also claims:

- one "prog_conv_outcomes" bottom-up outcome map;
- "a bucket value prevents overwrite" for occurrence outcomes;
- one combined authority row for outcome, expression-fact, and type-name tables.

The current architecture instead has:

- ExprWorkForest as the ordered retained expression-work enumeration;
- OutcomeAccumulator.oa_map as the standard NodeKeyMapBase identity map for one exact suffix;
- OutcomeTrace as the retained causal construction history;
- ForestOutcomeTable as the exact forest/table-indexed outcome authority;
- ForestExprFactTable / ExprFactTable as the EOOk projection;
- TypeNameFactTable as the separate retained target-resolution table.

The outcome map does not store list buckets. One key maps to one ExprOutcome. Key uniqueness and exact domain
prevent overwrite.

The row is false current documentation.

2.5 The collection audit names nonexistent current syntax

The ordered-source-syntax row says:

  TFun body

No TFun constructor exists in the current AST.

The current top-level function form is:

  DMain : list GoStmt -> GoDecl

The row must say DMain body or another exact current name.

2.6 The collection audit needs a full symbol-existence pass

The stale entries survived eleven rounds because the audit was treated as a conclusion rather than audited as
data.

For every code symbol named as current in .review/COLLECTION_AUDIT.md:

- confirm it exists at the candidate head;
- confirm its described storage role is current;
- confirm the stated backing is exact;
- confirm list order/duplicate claims match the current theorem or constructor;
- mark intentionally absent names explicitly as rejected/future rather than listing them as current storage.

Do not update only the two known strings and leave stale semantics around them.

===============================================================================
3. REQUIRED EXACT SUCCESS IDENTITY
===============================================================================

3.1 Strengthen StepCause_ok_conv_inv

Make StepCause_ok_conv_inv return the ConversionStep for the exact source parameters supplied to the theorem.

Preferred shape:

  Lemma StepCause_ok_conv_inv ... ts x f :
    ew_expr current = EConvert ts x ->
    StepCause ... (EOOk f) ->
    exists (step : ConversionStep forest current rest ts x) opf tc,
      oa_total ... = EOOk opf
      /\ convert_const ... = Some tc
      /\ f = exact current ExprFact.

The proof must:

1. invert SCConvOk;
2. retain its constructor equality ew_expr current = EConvert ts' x';
3. compare it with the theorem premise ew_expr current = EConvert ts x;
4. inject the EConvert constructor;
5. transport/substitute the returned ConversionStep to ts/x;
6. expose the same operand, target, convert_const result, and final fact.

Do not solve this by adding an unrelated source-specification theorem.

This is production-cause identity.

3.2 Strengthen retained_convsuccess_closure

Its result must contain:

  step : ConversionStep forest current rest ts x

not existential ts0/x0.

It must continue to expose:

- exact rest accumulator;
- exact operand SuffixMember;
- tail operand query = EOOk opf;
- final-table operand query = EOOk opf;
- equality of tail and final queries;
- exact target fact query through cw_target_ref;
- one convert_const success;
- exact final ExprFact.

3.3 Strengthen nested_success_bundle

Remove existential ts0/x0.

The bundle must contain:

  step : ConversionStep ... ts x

where ts/x are the bundle parameters.

Keep all other exact evidence.

3.4 Reprove concrete accepted surfaces

Reprove:

- deep_nested_convsuccess_at;
- deep_nested_chain_success_evidence.

Each of the four valid conversions must expose a ConversionStep whose type parameters are definitionally or
propositionally the exact source TypeSyntax and operand GoExpr in that conjunct.

The weaker operand-only corollaries may remain labeled as such.

3.5 Align comments and gate

The readable gate may call the step exact only after the printed theorem statement makes the source-step identity
explicit.

Gate:

- StepCause_ok_conv_inv;
- retained_convsuccess_closure;
- deep_nested_convsuccess_at;
- deep_nested_chain_success_evidence.

Update gate comments to quote the exact statement, not proof-local knowledge.

===============================================================================
4. REQUIRED CURRENT COLLECTION AUDIT
===============================================================================

Rewrite the C4-related rows of .review/COLLECTION_AUDIT.md around the actual current objects.

At minimum, classify these separately:

4.1 ExprWorkForest and AnnotatedExprWorkForest

Contents:

- per-file and flat ExprWork/WorkMember enumerations;
- retained annotation contexts.

Backing:

- list.

Reason:

- source/per-file order is semantic for bottom-up processing, diagnostics, and context;
- NoDup keys are proved;
- these are proof-backed ordered views over one source AST, not identity storage.

4.2 OutcomeAccumulator / ForestOutcomeTable

Contents:

- NodeKey -> ExprOutcome.

Backing:

- NodeKeyMapBase, the standard FMapAVL wrapper.

Reason:

- identity-keyed total result lookup;
- exact domain equals the retained forest/suffix members;
- one entry per unique work key;
- no list bucket and no overwrite fallback.

State that ForestOutcomeTable retains the exact OutcomeTrace paired with its accumulator.

4.3 OutcomeTrace

Contents:

- exact causal insertion history over the retained work order.

Backing:

- intrinsic inductive trace following the source-ordered list.

Reason:

- predecessor order and exact tail object are semantic proof structure;
- it is not a general-purpose collection implementation.

4.4 ForestExprFactTable / ExprFactTable

Contents:

- NodeKey -> ExprFact for EOOk outcomes.

Backing:

- NodeKeyMapBase / FMapAVL.

Reason:

- exact success projection of the same ForestOutcomeTable;
- not an independently computed authority;
- exact domain and sealing facts must use current theorem names.

4.5 TypeNameFactTable

Keep it separate.

Use current builder/query/object names:

- build_type_name_fact_table;
- type_name_fact_at_table;
- public retained query as applicable;
- exact type-name occurrence domain.

Do not describe it as part of a deleted combined prog_conv_outcomes root.

4.6 Current source syntax

Replace TFun body with DMain body.

Keep:

- source_decls;
- DMain statement body;
- SPrintln arguments;
- source_imports / list ImportSpecSyntax, while accurately noting the element type is currently empty.

4.7 Audit result

After the rewrite, run a symbol-existence audit over every current code token named in the collection audit.

Report:

- every current symbol exists;
- every intentionally absent name is labeled absent/rejected/future;
- no deleted production authority appears as current;
- no custom general-purpose collection has returned;
- every retained list has an exact order/repetition/stack/transport/derived-view reason.

The collection audit remains current-only. Historical names belong in Git.

===============================================================================
5. REQUIRED PERMANENT PROSE CLOSEOUT
===============================================================================

Update only the minimum current authority prose:

- .review/NEXT_STEPS.md;
- .review/REVIEW_REQUEST.md;
- .review/SOURCE_FOREST_STATUS.md;
- PROGRESS.md if it names the success bundle;
- gate/axiom_gate.v comments;
- .review/COLLECTION_AUDIT.md.

ARCHITECTURE.md needs no change unless it currently repeats the unlinked success-step claim or collection names.

Requirements:

- no file may say C4 is human-accepted before Rob accepts it;
- no file may call an existentially unrelated step exact;
- the collection audit must describe the candidate head;
- range wording uses "this freeze commit";
- C5 and the trim remain forbidden;
- do not edit life.md.

===============================================================================
6. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Delete or replace:

- existential ts0/x0 from retained_convsuccess_closure;
- existential ts0/x0 from nested_success_bundle;
- proof branches/theorem comments that preserve the weaker shape;
- current collection-audit references to prog_conv_outcomes;
- the false outcome "bucket value prevents overwrite" claim;
- current collection-audit reference to TFun body;
- duplicate/stale combined outcome/fact/type-name table descriptions.

Run full tracked-tree searches for:

- prog_conv_outcomes;
- `TFun` in the current collection audit;
- "bucket value prevents overwrite" attached to ExprOutcome;
- retained_convsuccess_closure followed by existential ts0/x0;
- nested_success_bundle followed by existential ts0/x0;
- gate comments saying exact ConversionStep where the theorem type does not bind it to source ts/x;
- old family-specific conversion constructors;
- raw OutcomeCause / build_outcome_accumulator / FinalMemberCause;
- C5 uintptr/rune implementation;
- duplicate source-name spelling/resolver tables.

Historical wording inside this repair-12 directive is allowed.

===============================================================================
7. SCOPE DECISIONS
===============================================================================

Do not change the numeric model or scope decisions in this repair.

Keep:

- ADR-0001: PROPOSED;
- ADR-0002: REJECTED AS WRITTEN / OPEN;
- SR-009: UNRESOLVED EXISTING RESTRICTION;
- every scope-ledger entry PROPOSED unless Rob explicitly accepts it.

Do not begin DecimalFloat decision work.

===============================================================================
8. BEHAVIORAL TODO DISCIPLINE
===============================================================================

Use Claude Code's TODO list.

Each TODO must contain:

- exact theorem/audit object produced;
- exact prior object or source parameters consumed;
- exact identity relation exposed;
- observable public statement required;
- load-bearing proof;
- weaker prior statement or stale audit entry removed;
- gate entry;
- residue search;
- status.

Minimum TODOs:

T1 — StepCause_ok_conv_inv returns the exact source-parameter ConversionStep
T2 — retained_convsuccess_closure removes existential ts0/x0
T3 — nested_success_bundle removes existential ts0/x0
T4 — all four concrete valid conversions expose exact source-step identity
T5 — readable gate statements/comments match
T6 — rewrite current C4 collection rows around ExprWorkForest/OutcomeAccumulator/OutcomeTrace/ForestOutcomeTable
T7 — separate and correct ForestExprFactTable and TypeNameFactTable rows
T8 — replace TFun with DMain and audit all named current symbols
T9 — current authority/prose/residue closeout
T10 — full verification/freeze/push

A TODO is not complete because the proof can infer ts0 = ts internally.

The theorem statement must expose or eliminate the distinction.

A TODO is not complete because the collection audit's final conclusion remains true in broad terms.

Every current row must be factually current.

===============================================================================
9. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this narrow closeout.

Use this loop:

1. strengthen StepCause_ok_conv_inv at the root;
2. propagate exact source-step identity through universal and concrete success theorems;
3. align the readable gate;
4. rewrite the C4 collection audit around current objects;
5. run the symbol-existence and collection-role audit;
6. update current authority prose;
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

Ordinary equality transport, theorem strengthening, gate work, and collection-audit cleanup are not blockers.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 12 COMPLETE

or

FIDO C4 REPAIR 12 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
10. FINAL VERIFICATION
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
- exact StepCause_ok_conv_inv statement;
- exact retained_convsuccess_closure statement;
- exact nested_success_bundle statement;
- exact four-conversion success fixture;
- collection-audit rows and symbol-existence result;
- standard-collection audit conclusion;
- confirmation that the production architecture did not change;
- full old-constructor/no-C5 search;
- duplicate resolver/spelling search;
- stale collection-authority residue search;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 48c0b31..final.

Green commands do not replace inspection of theorem statements and collection-audit rows.

===============================================================================
11. FINAL FREEZE AND PUSH
===============================================================================

After implementation and audit closeout pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 exact success identity and collection-audit closeout repair 12 candidate complete;
   - original C4 baseline: 8c9212a;
   - all twelve blocked candidates, ending at 48c0b31;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-12 range: 48c0b31..this freeze commit;
   - human C4 Implementation Review pending;
   - production architecture unchanged;
   - exact source-step identity now exposed in the success theorem family;
   - collection audit current and symbol-checked;
   - ADR-0001 PROPOSED;
   - ADR-0002 REJECTED AS WRITTEN / OPEN;
   - automatic Codex review disabled;
   - C5 forbidden;
   - post-C4 trim forbidden until C4 acceptance.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-final-identity-collection-audit-closeout-repair-12
   result: twelfth BLOCKING result repaired; new human C4 Implementation Review pending

3. Use ordinary impl(...) commits during the closeout.

4. Make exactly one final freeze commit after all theorem, gate, audit, status, residue, and verification work
   passes:

   review(final): C4 — freeze exact identity and audit candidate

5. Run every final check on that exact commit.

6. If anything fails or any theorem/audit claim remains weaker or false, repair it and create a new final freeze
   commit. Only the latest passing freeze is the candidate.

7. Push main without force.

8. Notify Rob and report:

   - all baselines and candidate SHAs;
   - repair-12 authority commit;
   - final candidate SHA and ranges;
   - exact files changed;
   - confirmation that production architecture was not reopened;
   - exact source-step success theorem family;
   - exact four-conversion fixture;
   - rewritten current collection audit;
   - symbol-existence audit;
   - readable gate entries and count;
   - full verification;
   - generated-byte identity;
   - residue/no-C5 results;
   - completed behavioral TODO table;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop.

Do not begin C5.

Do not begin the post-C4 trim.

