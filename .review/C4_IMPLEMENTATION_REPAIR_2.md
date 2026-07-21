Claude Code directive: C4 Implementation Review BLOCKING — production-root repair 2

Repository:

rhencke/fido

Required clean baseline:

1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

First blocked C4 candidate:

89b8e54634e7012612a51990756ad29a579c1b0f

Second blocked C4 candidate and required repair baseline:

1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca

C4 contract commit:

b8918641951daa9462e9205b77a5880c1ada2e68

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-typed-reference-single-path-repair-2

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

This is Rob's later explicit authorization to replace the flawed C4 production root. It does not replace or
weaken the binding C4 contract. The current tree is green but the contract is not true.

Do not rewrite or force-push existing commits. Start only from the exact clean baseline above.

Do not request or run Codex review. Do not begin C5.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 1c4a7de.

The first repair did close useful surfaces:

- DiagnosticReason now retains a TypeNameRef.
- Erased invalid-conversion reports retain source target syntax.
- byte/uint8 and rune/int32 erased reports differ by source target.
- the pinned-Go accepted and rejected alias matrix is present;
- stale family-specific renderer helpers were removed;
- permanent architecture prose was improved;
- a review(final) freeze commit now exists.

Keep those results unless this repair needs a direct change.

The remaining defects share one root:

The live production expression pass still works on raw NodeKey arithmetic and recursive source semantics. Typed
references and retained facts are proved beside that path or added later. The implementation therefore still has
more than one semantic route.

Do not patch the current theorem statements while keeping that root. Replace the root and rebuild the affected
proofs.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_2.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 production-root repair 2;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - first blocked candidate;
   - second blocked candidate and current repair baseline;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_2.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; production-root repair active;
   - automatic Codex review: disabled;
   - C5: forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-typed-reference-single-path-repair-2
   result: BLOCKING at 1c4a7de; production-root repair 2 active

   Keep the original C4 contract path and hash. Do not request a review through this file.

4. Update .review/SOURCE_FOREST_STATUS.md with a short exact record of all blocking classes in section 2.

5. Commit only these authority changes:

   review(repair): C4 — rebuild production on retained typed references

No Rocq, Docker, e2e, gate, generated, plugin, shell, or permanent architecture change may enter that authority
commit.

6. After that authority commit and after NEXT_STEPS/STATUS preserve the prior repair history, delete the
   superseded:

   .review/C4_IMPLEMENTATION_REPAIR_1.md

   in the first implementation commit. Git history is its archive. Keep the binding C4 contract and keep this
   repair-2 authority through the next human review.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 Successful production facts run a hidden second semantic pass

The current production outcome_step computes a leaf or conversion ConstInfo, then calls:

  occ_use_resolved (snd ro)

to fill ef_use_resolved.

For a println argument, occ_use_resolved calls:

  resolve_expr_const UsePrintlnArg e

That calls recursive const_info e. For a conversion expression this runs the full raw subtree again and calls
convert_const again, after outcome_step already called convert_const from the operand outcome and target fact.

For a nested conversion used as a println argument, the hidden call repeats every nested conversion.

Thus the current claim "one convert_const per conversion" is false. The outcome map and the recursive
resolve_expr_const path are peer semantic routes.

Production must derive use-context resolution from the ConstInfo that it just computed. It must not call
const_info, resolve_expr_const, resolve_expr, program_typedb, or another raw-expression semantic function to fill
an ExprFact.

2.2 Typed target and operand references are not on the live semantic path

conversion_target_ref and conversion_target_ref_conv exist, but outcome_step does not use them.

The live conversion branch reads:

  find (type_name_key (fst ro)) tnfacts
  find (operand_key (fst ro)) outcomes

The function has no retained index argument and no ExprRef, TypeNameRef, or operand ExprRef value.

This violates the contract and the first repair directive. A proof that raw key arithmetic lands on the same node
does not make the typed reference part of production.

The live conversion step must receive or obtain:

- the conversion ExprRef;
- its exact target TypeNameRef;
- its exact operand ExprRef.

Raw key formulas can support structural proofs. They cannot be the live production interface.

2.3 The type-name map is built by a second compiler visit

elaborate_indexed currently binds:

  blocks  := prog_blocks p
  visit   := concat blocks
  tnfacts := prog_type_name_facts p

But prog_type_name_facts p folds prog_visit p, and prog_visit p computes concat (prog_blocks p). Production thus
recomputes the blocks and visit after it already retained them.

The comment that tnfacts is built from the retained visit is false.

Build the type-name table by folding the let-bound visit value. Do not call a helper from elaborate_indexed when
that helper calls prog_visit p, prog_blocks p, binding_visit, visit_file, or a second AST traversal.

2.4 Impossible structural failures become normal semantic values

Current examples include:

- a missing type-name fact or missing operand outcome becomes EOChildFail;
- conversion_target_ref returning None makes the diagnostic path return [];
- as_expr returning None makes the diagnostic path return [];
- leaf_ci returns CIUntyped (CBool false) for EConvert and calls the branch "unreachable."

These are not exact states.

EOChildFail may mean only that the real operand has a real non-success outcome. It may not mean:

- missing type-name fact;
- missing target reference;
- missing operand reference;
- missing operand table entry;
- wrong-kind reference;
- index/table mismatch.

For every live conversion, those states are impossible and must be removed by a proof-backed total function or a
False_rect branch. Do not map them to a child failure, a fake boolean constant, or no diagnostic.

2.5 Invalid-conversion evidence is still assembled after the semantic step

EOConvFail stores only GoType and ConstInfo. The diagnostic pass later calls conversion_target_ref again and
silently emits nothing if that lookup fails.

The production failure outcome must carry the exact structural evidence that caused it, at least:

- conversion ExprRef;
- target TypeNameRef;
- operand ExprRef;
- resolved target from the retained TypeNameFact;
- operand status from the retained operand ExprFact.

The exact proof fields or record layout are your choice. The diagnostic pass must project this evidence and add
outer context. It must not remint the target or operand reference, redo a fact lookup, resolve the source name,
call convert_const, or call const_info.

2.6 The gated production theorem proves the wrong path

prog_conv_outcome_consumes is stated in terms of:

- type_name_key;
- prog_type_name_facts p;
- prog_conv_outcomes p;
- recursive const_info x.

It does not state that production obtained a TypeNameRef or operand ExprRef. Its successful RHS also contains
occ_use_resolved, which hides the second recursive semantic pass.

elaborate_ok_seals_tnfacts proves equality with prog_type_name_facts p, but that function is the second-visit
builder. It does not prove that the retained visit supplied the sealed map.

occ_expr_diags_conv_sound proves a source-spec conversion failure. It does not prove:

- the reported semantic target came from the stored TypeNameFact at target_ref;
- the operand status came from the stored ExprFact at the exact operand ExprRef;
- the production failure outcome carried those refs and facts.

Replace these gate surfaces. Do not add another theorem around the same raw-key call path.

2.7 The repeated-name requirement is still conditional

repeated_name_distinct_refs assumes two conversion occurrences, two expression refs, and distinct keys. It then
proves a consequence.

The repair directive required a real snapshot fixture containing two equal source type names at two distinct
conversion positions and proofs that the two refs exist.

Add a concrete compiled program with two equal target spellings. Mint and query both real TypeNameRefs. Prove:

- both refs exist;
- their NodeKeys differ;
- their recovered TypeSyntax values are equal;
- their stored TypeNameFact values are equal.

A theorem whose premises assume the two occurrences and distinct keys does not meet this test requirement.

2.8 Current prose and gate comments claim defects are closed

Correct at least these false current statements:

- the elaborate_indexed comment says one retained visit/status path although tnfacts reruns prog_visit;
- the erased-report comment says "NO source syntax" although ErasedDiagnostic now retains source target syntax;
- outcome/gate comments say no const_info rescan although occ_use_resolved performs one;
- SOURCE_FOREST_STATUS and PROGRESS say the live path consumes retained typed refs and one retained visit;
- the gate comment says the production conversion reads its target and operand facts through the required path;
- NEXT_STEPS contains placeholder freeze ranges rather than clear current authority text.

Read each affected block in context. Rewrite it as current fact or delete it.

===============================================================================
3. REPLACE THE PRODUCTION ROOT
===============================================================================

This section states the required model. Choose the smallest proof-friendly Rocq form that satisfies it.

Do not stop for another design check.

3.1 One retained structural input

In elaborate_indexed, compute and bind exactly once:

- idx;
- blocks;
- visit := concat blocks.

All C4 occurrence work must derive from these exact values.

Builder functions used by elaborate_indexed must take visit or blocks as explicit arguments. They must not hide a
call to prog_visit p or prog_blocks p.

Proof specifications may use prog_visit p and prove that the retained visit has the same value. The executable
body may not compute it again.

3.2 A typed work view over the retained visit

Before semantic expression processing, turn each relevant retained visit item into a proof-backed typed view.

For a conversion item, production must hold one value equivalent to:

  conversion ExprRef
  target TypeNameRef
  operand ExprRef

with proofs that:

- the conversion ref erases to that visit node;
- its source view is EConvert target operand;
- target_ref is the direct RConversionTarget child;
- operand_ref is the direct RConversionOperand child;
- target precedes operand;
- type_name_ref_syntax target_ref recovers the exact raw target;
- the operand ref recovers the exact raw operand.

This can be:

- a refined ConversionRef/ConversionOccurrence record;
- a dependent total conversion-children function;
- a transient typed work item built from the retained visit;
- another smaller equivalent dependent form.

It is not a second AST. It must carry references to the one retained snapshot, not copied syntax or semantic
facts.

Partial GoIndex helpers may remain for arbitrary callers. The live production path must use a total proof-backed
form. Impossible None branches must be eliminated, not handled as semantic results.

3.3 Build and seal one TypeNameFactTable value before expressions

Fold the retained visit once into the type-name facts and construct the proof-backed TypeNameFactTable value
before the outcome fold.

Add a total table-level query, equivalent to:

  type_name_fact_at_table :
    TypeNameFactTable p ip -> TypeNameRef p -> TypeNameFact

It must project the stored map entry and use the table's completeness proof to eliminate None.

Production conversion processing must call this query with its retained target TypeNameRef.

On success, ElaborationFacts must store this exact TypeNameFactTable value. Do not wrap or rebuild its map after
the decision.

The public ElaborationFacts query can delegate to this table-level query.

3.4 Use a proof-carrying bottom-up outcome accumulator

The current raw map lookup:

  find operand_key outcomes

must not remain as the production interface.

Use an accumulator that carries enough completeness evidence for the already processed suffix. For a live
conversion, the retained operand ExprRef and the preorder proof must make its outcome a total query.

An acceptable shape is a record with:

- the NodeKey -> ExprOutcome map;
- a proof that every processed expression ref has its exact outcome.

Another dependent form is allowed.

A missing operand entry is impossible. It must not become EOChildFail.

EOChildFail is allowed only when the total operand query returns a real EOConvFail or real EOChildFail.

3.5 Derive use-context resolution from the computed ConstInfo

Replace production use of occ_use_resolved with a function that consumes:

- the occurrence role;
- the already computed ConstInfo.

For example, it may apply resolve_const_info and use_allowsb to that stored status for an RPrintlnArg and return
None for a conversion operand.

It must not inspect the raw GoExpr or call const_info/resolve_expr_const.

Keep a declarative source helper only if useful, name it clearly as a specification, and prove:

  source helper result = result derived from the production ConstInfo

when the expression has that ConstInfo.

For one successful conversion occurrence, the production branch must call convert_const exactly once in its own
body. No helper called by that branch may call convert_const or recursively call const_info.

3.6 Store exact local failure evidence in the outcome

A local invalid-conversion outcome must retain the exact conversion refs and the values read from the exact facts.

It may store projections such as GoType and ConstInfo for stable report payloads, but prove they equal:

- tnf_type (type_name_fact_at_table tnfacts target_ref);
- ef_const_status of the EOOk fact at operand_ref.

The outcome must also retain or prove:

  convert_const target operand_status = None

A successful conversion outcome must store the ExprFact built from the same target fact and operand fact.

Diagnostics then project the local failure outcome and add outer context. No target-ref reconstruction is
allowed in the diagnostic pass.

3.7 Keep one declarative specification, not a peer compiler

The index-free GoTypes const_info/ProgramTyped specification can remain.

Production exactness must relate the typed-reference outcome table to that specification for every live
expression occurrence.

The production builder must not call these raw-expression functions:

- const_info;
- const_info_step with the compiler resolver;
- resolve_expr_const;
- resolve_expr;
- expr_typedb;
- local_conv_failure;
- conv_targets.

They can remain in specification and proof code if useful.

The live conversion branch may call only:

- total typed-reference queries;
- total retained fact/outcome queries;
- GoTypes.convert_const once;
- use-context resolution from the resulting ConstInfo;
- map insertion.

===============================================================================
4. REQUIRED LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems about the functions that elaborate_indexed calls.

4.1 Retained structural values

Prove that:

- the production type-name table builder consumes the let-bound retained visit;
- the production outcome builder consumes that same retained visit;
- no builder used by elaborate_indexed calls prog_visit/prog_blocks again;
- the same retained index mints all conversion, target, and operand refs.

The final report must include a short call-path excerpt, not only an extensional equality theorem.

4.2 Typed conversion children

For every live conversion work item:

- conversion ExprRef is exact;
- target TypeNameRef is exact, direct, and RConversionTarget;
- operand ExprRef is exact, direct, and RConversionOperand;
- target precedes operand;
- source target and source operand recover exactly.

Gate the universal theorem.

4.3 Total fact and outcome queries

Prove:

- each target TypeNameRef has one stored TypeNameFact;
- the table-level query returns that stored entry;
- each processed operand ExprRef has one stored ExprOutcome;
- the accumulator query returns that stored entry;
- wrong-kind and foreign refs cannot be supplied;
- no lookup fallback exists on the production path.

4.4 One semantic call

For every live conversion occurrence, prove the production outcome is exactly:

- EOOk of the one convert_const result, when it succeeds;
- the exact local failure evidence, when it rejects;
- EOChildFail only when the real operand outcome is non-success.

The theorem statement must include the actual conversion ExprRef, target TypeNameRef, operand ExprRef,
TypeNameFact query, and operand outcome/fact query.

Do not state the main theorem only in terms of type_name_key, operand_key, raw map find, or recursive const_info.

4.5 Use-context result from the production status

Prove that ef_use_resolved in every EOOk fact is computed from that same fact's ef_const_status and occurrence
role.

Prove it equals the declarative resolve_expr_const result for the source expression.

The production function itself must not call resolve_expr_const.

4.6 Exact diagnostic evidence

For every production DRInvalidConversion:

- primary is the exact conversion ExprRef from the local outcome;
- target_ref is the exact target TypeNameRef from that same outcome;
- target equals the TypeNameFact query at target_ref;
- operand_ref is the exact operand ExprRef from that same outcome;
- operand_status equals the successful operand ExprFact status;
- convert_const target operand_status = None;
- source target erasure comes through target_ref;
- one reason exists for each innermost local failure;
- no outer reason exists when the child outcome failed;
- ordering, anchors, and outer context remain exact.

The proof must start from the production outcome/diagnostic function, not only local_conv_failure over raw syntax.

4.7 Same object sealed

Prove that the exact TypeNameFactTable value consumed by the outcome builder is the value stored in
ElaborationFacts.

Prove the exact successful expression facts are projections of the same outcome accumulator used by diagnostics.

Value equality with a separately recomputed prog_* function is not enough.

4.8 Concrete repeated-name snapshot

Add and gate the concrete two-occurrence fixture required by section 2.7.

4.9 All prior valid C4 claims

Keep or re-prove:

- all sixteen resolver cases;
- source-distinct/semantic-equal byte and rune aliases;
- type-name table domain and total query;
- wrong-kind/foreign exclusion;
- invalid byte/uint8 and rune/int32 erased-report distinction;
- renderer source spelling and denotation;
- SafeProgram-only public render/materialize path;
- exact acceptance/diagnostic completeness;
- no C5 scope.

===============================================================================
5. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Delete, replace, or demote every current item that supports only the rejected production root.

At minimum inspect:

- outcome_step;
- prog_conv_outcomes;
- prog_conv_outcome_consumes;
- type_name_key and operand_key on the live path;
- conversion_target_ref if it remains partial on the live path;
- occ_use_resolved in production;
- leaf_ci's fake EConvert -> CBool false branch;
- local_conv_failure_om and diagnostic target re-minting;
- elaborate_ok_seals_tnfacts;
- the conditional repeated_name_distinct_refs surface;
- gate comments and entries for the rejected claims.

Key formulas and index-free source specifications may remain only when a real proof still needs them. Rename or
comment them as specifications. Delete them when the rebuilt proof chain no longer uses them.

Run a full tracked-tree search for:

- calls to occ_use_resolved from production;
- calls to resolve_expr_const/const_info from the production builder;
- type_name_key/operand_key in the live outcome path;
- prog_type_name_facts p inside elaborate_indexed;
- conversion_target_ref None => [] in production diagnostics;
- fake leaf semantic values;
- claims of one visit/one convert_const that are not true;
- the old three conversion constructors and semantic target tags in raw syntax;
- duplicate type-name spelling and resolver tables;
- C5 uintptr or rune-literal/rune-constant work.

The frozen C4 contract can describe old constructors as deleted history. Inspect every hit in context.

===============================================================================
6. TESTS AND DIFFERENTIALS
===============================================================================

Keep the full pinned-Go alias matrix now present.

Add or retain Rocq checks that cover:

- accepted and rejected byte/uint8 boundaries;
- accepted and rejected rune/int32 boundaries;
- a successful nested conversion used as a println argument, proving the stored use result comes from its one
  production status;
- a locally failing nested conversion, proving one inner diagnostic and no outer diagnostic;
- a deliberate table/query proof fixture that cannot take the missing-entry path;
- the concrete repeated-name snapshot.

Do not add a runtime counter or claim that tests prove one convert_const call. The source call path and universal
proofs must establish that.

===============================================================================
7. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this repair.

Use this loop:

1. inspect the full C4 production root and all proof users;
2. remove the rejected root before adding replacement proofs;
3. build one coherent replacement layer;
4. run the narrow compile/proof check;
5. repair all failures at their root;
6. run the full required verification;
7. inspect the complete C4 range, repair range, call path, and residue searches;
8. repeat until the final freeze is clean.

Do not stop for:

- design approval;
- an intermediate green module;
- a partial report;
- a large proof count;
- a clean but incomplete commit;
- fear of deleting current proofs;
- a question already decided by this directive or the binding C4 contract.

Past effort has no claim on the design. If the current outcome/fact proof chain blocks the correct model, delete it
and rebuild it.

Stop only in one of two terminal states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after direct repair attempts. Report the exact file,
definition/theorem or command, the smallest failing case, and why neither this directive nor the binding contract
decides it. Proof volume, a large diff, or ordinary repair work is not a blocker.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 2 COMPLETE

or

FIDO C4 REPAIR 2 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
8. FINAL VERIFICATION
===============================================================================

Run from a clean supported environment:

make prove
make e2e
make check
make regenerate
make regen-guard
git diff --check

Run the staged pre-commit check on the complete candidate.

Also report:

- readable assumption gate count and exact result;
- whole-theory audit and self-tests;
- full pinned-Go alias matrix;
- exact generated go.mod and recursive .go byte identity;
- full old-constructor/no-C5 search;
- duplicate type-name spelling/resolver search;
- standard-collection audit;
- the exact elaborate_indexed call path;
- evidence of one retained blocks/visit value;
- evidence of one TypeNameFactTable object built, consumed, and sealed;
- evidence of typed conversion/target/operand refs on the live path;
- evidence that production use resolution consumes the computed ConstInfo;
- evidence that the live conversion branch contains one convert_const call and no recursive semantic helper;
- evidence that impossible lookups cannot return a semantic fallback;
- concrete repeated-name fixture result;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 1c4a7de..final.

A green command proves only what it checks. It does not replace the call-path and universal proof evidence.

===============================================================================
9. FINAL FREEZE AND PUSH
===============================================================================

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 production-root repair 2 candidate complete;
   - original C4 baseline: 8c9212a;
   - first blocked candidate: 89b8e54;
   - second blocked candidate: 1c4a7de;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-2 range: 1c4a7de..this freeze commit;
   - human C4 Implementation Review pending;
   - automatic Codex review disabled;
   - C5 forbidden.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-typed-reference-single-path-repair-2
   result: second BLOCKING result repaired; new human C4 Implementation Review pending

3. Commit the final status and final proof-safe changes as:

   review(final): C4 — freeze single-path typed-reference candidate

4. Run every final check on that exact commit.

5. If a check, call-path audit, proof audit, or residue search fails, repair it, make a new freeze commit, and
   repeat. Only the final passing freeze commit is the candidate head.

6. Push main without force.

7. Notify Rob and report:

   - original C4 baseline;
   - both blocked candidates;
   - repair-2 authority commit;
   - final candidate SHA and all three ranges;
   - exact files changed in repair 2;
   - the deleted production root;
   - the replacement retained-visit and typed-reference model;
   - how the same TypeNameFactTable is built, queried, and sealed;
   - how the operand ExprRef supplies the total stored outcome/fact;
   - how use-context resolution consumes the one computed ConstInfo;
   - how each conversion calls convert_const once;
   - how diagnostics project stored failure evidence;
   - the concrete repeated-name fixture;
   - all verification results;
   - gate count;
   - generated-byte identity;
   - residue/no-C5 results;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop. Do not begin C5.
