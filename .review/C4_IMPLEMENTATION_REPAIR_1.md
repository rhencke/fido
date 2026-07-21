Claude Code directive: C4 Implementation Review BLOCKING repair

Repository:

rhencke/fido

Required clean baseline:

89b8e54634e7012612a51990756ad29a579c1b0f

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-retained-facts-and-diagnostics-repair-1

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

This is Rob's later explicit authorization to repair the blocked C4 candidate. It does not replace or weaken the
binding C4 contract. Do not request or run Codex review. Do not begin C5.

Start only from the exact clean baseline above. Do not rewrite or force-push the existing C4 commits.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

The C4 candidate at 89b8e54 is not accepted.

The following parts are good and should not be reopened without a repair need:

- the proof-carrying IdentifierSyntax domain;
- the closed sixteen-name TypeName class;
- SupportedTypeName retaining IdentifierSyntax plus its matching lexical symbol;
- one raw EConvert TypeSyntax GoExpr;
- KTypeName, TypeNameRef, and the source-order target/operand index layout;
- the compiler-owned sixteen-name predeclared mapping;
- source-spelling rendering;
- byte/rune source identity and semantic alias mapping;
- unchanged canonical generated Go bytes;
- absence of C5 uintptr and rune-literal work.

The remaining defects are contract defects. They are not optional design choices.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_1.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 repair;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - blocked candidate baseline: the full 89b8e54 SHA above;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_1.md;
   - human repair authorization token above;
   - state: C4 Implementation Review BLOCKING; repair active;
   - automatic Codex review: disabled;
   - C5: forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-retained-facts-and-diagnostics-repair-1
   result: BLOCKING at 89b8e54; authorized repair in progress

   Keep the original C4 contract path and hash. Do not request a review through this file.

4. Update .review/SOURCE_FOREST_STATUS.md with a short, exact record of the blocking classes in section 2.

5. Commit only these authority changes:

   review(repair): C4 — require retained fact consumption and source diagnostics

No Rocq, Docker, e2e, gate, generated, plugin, shell, or permanent architecture change may enter this authority
commit.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 The type-name fact table is not on the production semantic path

The contract requires production conversion typing to:

1. obtain the target TypeNameRef from the retained index;
2. read its retained TypeNameFact;
3. read the already-built operand expression fact;
4. call GoTypes.convert_const once;
5. store the expression fact or exact invalid-conversion evidence.

The candidate does not do this.

Current examples include:

- the production status step specializes GoTypes.const_info_step with predeclared_type;
- local_conv_failure and local_conv_failure_sm call predeclared_type inline;
- the diagnostic path calls convert_const on that inline result;
- elaborate_indexed builds status and diagnostics before it has a retained type-name fact map;
- on success, elaborate_indexed calls prog_type_name_fact_table p ip, which rebuilds the table through another
  prog_visit instead of sealing the map used by production;
- the failure path never consumes the type-name fact table.

This makes the new table an output proof object beside the live compiler path. Section 8, section 9, section 15.3,
and the work order in section 19 forbid that split.

2.2 The production expression path does not consume one operand ExprFact authority

The candidate first builds a NodeKey -> option ConstInfo status map and then copies successful values into a
separate ExprFact map. Conversion processing reads the status map, not the operand ExprFact required by the
contract.

C4 requires one production expression outcome path. Do not retain a second ConstInfo fact map beside the final
ExprFact authority merely to reduce the repair.

2.3 Invalid-conversion evidence omits the target TypeNameRef and loses source spelling

DRInvalidConversion currently carries:

- the conversion ExprRef;
- outer conversion refs;
- semantic GoType;
- operand ConstInfo.

It does not carry the target TypeNameRef.

ErasedDiagnostic carries the semantic GoType but no source target spelling. Thus an invalid byte(...) and an
invalid uint8(...) erase to the same target payload. The same defect exists for rune(...) and int32(...).

The C4 contract requires the typed reason to retain the exact target TypeNameRef and requires erased/user-facing
reporting to preserve byte or rune rather than replace it with uint8 or int32.

2.4 The pinned-Go alias differential is incomplete

WitnessAlias and the Docker checks cover only accepted byte(255) and rune(65). WitnessAlias explicitly says the
rejected alias scars are not sent to pinned Go.

The contract requires pinned-Go accepted/rejected evidence for the alias scars. Existing uint8 negative tests do
not replace byte negative tests. Existing int32 behavior does not replace rune boundary tests.

2.5 Current permanent prose still describes deleted code

ARCHITECTURE.md still lists EIntConvert, EFloatConvert, and EComplexConvert as the live GoAST and still describes
the old family-specific GoRender branches. The active master-plan C4.4 prose also calls those nodes "current."

The full tracked-tree no-residue rule applies to current permanent prose, not only code.

The semantic keyword helpers integer_keyword, float_keyword, and complex_keyword, plus their GoRender ASCII
lemmas/examples and gate entries, have no live C4 consumer in the candidate beyond their own tests/gate. A gate
entry is not a consumer. Delete this dead renderer residue unless a real live semantic theorem still needs a
helper after the repair.

2.6 The required freeze process was not completed

The current head is a milestone(root) commit, not the required review(final) freeze commit. NEXT_STEPS still says
"C4 implementation authorized" instead of candidate complete and human review pending. The status files do not
follow section 19.16 through 19.20 of the contract.

The next candidate must use the required freeze process after all repairs pass.

===============================================================================
3. REQUIRED PRODUCTION ARCHITECTURE
===============================================================================

Choose the smallest proof-friendly form that meets this section. Do not stop for another design check.

3.1 One retained visit value

In elaborate_indexed:

- compute blocks once;
- compute visit := concat blocks once;
- build all C4 occurrence data from that same let-bound visit;
- multiple linear folds over the same retained visit are allowed;
- a second AST traversal, a second prog_blocks/prog_visit computation, or a later table rebuild is not allowed.

Proof specifications may mention prog_visit p. The executable elaboration path must use its one retained visit
value.

3.2 One once-built type-name map

Before expression processing:

- fold the retained visit into one NodeKey-keyed TypeNameFact map;
- resolve each KTypeName occurrence through the one GoCompile predeclared resolver;
- do not copy source syntax or source spelling into TypeNameFact;
- use this exact map for production expression processing and failure diagnostics;
- on success, seal this exact map into ElaborationFacts;
- do not call prog_type_name_fact_table p ip or rebuild an equivalent map after the decision.

The public total query must still project the sealed table and must not resolve again.

3.3 Obtain the conversion target through the retained index

Add or use a total, proved structural helper for a live EConvert occurrence. It must provide its exact target
TypeNameRef from the retained index.

Required facts:

- the target ref is KTypeName;
- it is the direct child of the conversion ExprRef;
- its role is RConversionTarget;
- the operand ExprRef is the other direct child with RConversionOperand;
- target precedes operand;
- type_name_ref_syntax recovers the exact raw TypeSyntax.

The production path must use this typed ref. Do not use a raw source-name lookup as a substitute. A proved key
formula may support the helper, but the public production value must be a TypeNameRef minted through GoIndex.

3.4 One production expression outcome path

Build expression results bottom-up from the retained visit.

For EConvert:

- get the target TypeNameRef through the retained index;
- read the TypeNameFact from the once-built type-name map;
- get the operand ExprRef through the retained index;
- read the already-built operand ExprFact from the bottom-up accumulator;
- call GoTypes.convert_const once with tnf_type and the operand fact's ConstInfo;
- on success, store the conversion ExprFact;
- on failure, store or emit exact local invalid-conversion evidence containing the target ref, semantic target,
  and operand status;
- when the operand has no successful fact, do not emit a second outer conversion failure.

Do not keep the current production NodeKey -> option ConstInfo status map followed by a second copy into ExprFact.
The accepted result has one expression outcome/fact authority. A local build outcome may distinguish success,
local invalid conversion, and blocked-by-child, but it must not cause a second semantic pass or a second call to
convert_const.

Diagnostics may add outer-context and canonical-order data later. They must consume the stored local outcome.
They must not call convert_const or the source-name resolver again.

3.5 Specification versus production

The index-free GoTypes specification can remain parameterized by the compiler resolver. Recursive const_info is
allowed as a declarative specification and in proofs.

The production compiler must not call the resolver directly for an EConvert after the type-name fact exists.

Prove one exact theorem from the production occurrence result to the declarative GoTypes result for every live
expression occurrence. The theorem must cover success and local invalid-conversion failure, not only accepted
fixtures.

Allowed direct resolver uses include:

- the GoCompile predeclared mapping itself;
- construction of the once-built TypeNameFact map;
- the index-free specification and exactness theorem statements;
- GoSafe/GoRender proof specifications that call the compiler-owned resolver.

Forbidden direct resolver uses include:

- the production expression fold after type facts are built;
- production local conversion failure detection;
- production diagnostic creation;
- report erasure;
- a fallback when a fact lookup fails.

A failed lookup for a real typed ref is an impossible proof branch, not permission to resolve again.

===============================================================================
4. DIAGNOSTIC REPAIR
===============================================================================

Change the typed invalid-conversion reason to retain at least:

- primary conversion ExprRef;
- target TypeNameRef;
- outer conversion context;
- resolved semantic GoType;
- operand ConstInfo.

The field order and names are your choice.

Build this reason from the production expression outcome and the same once-built type-name map.

Prove:

- the primary ref denotes the exact EConvert;
- the target ref is its exact RConversionTarget child;
- the target source syntax is recoverable through that ref;
- the semantic target equals the stored TypeNameFact at that ref;
- the operand ref is the exact RConversionOperand child;
- the operand status equals its successful ExprFact status;
- GoTypes.convert_const rejects that target/status pair;
- one reason exists for each innermost failing conversion occurrence;
- no reason exists for an outer conversion whose child failed;
- multiplicity, source order, anchors, and outer-context rules remain exact.

Do not copy source text into DiagnosticReason.

Extend the erased/cross-snapshot report with a stable source-target payload for invalid conversions. It can be the
closed TypeName or the exact source spelling string. The erased report must retain both:

- source target identity/spelling;
- resolved semantic GoType.

erase_diagnostic must derive the source payload through the retained target TypeNameRef. It must not reverse-map
the GoType.

Add exact fixtures proving:

- invalid byte(256) reports source target byte and semantic target uint8;
- invalid uint8(256) reports source target uint8 and the same semantic target;
- the two erased diagnostics differ because the source targets differ;
- invalid rune(2147483648) reports rune and semantic int32;
- invalid int32(2147483648) reports int32 and the same semantic target;
- the two erased diagnostics differ because the source targets differ.

Update all report exactness, determinism, erasure, equality, and fixture proofs.

===============================================================================
5. REQUIRED PROOF AND TEST CLOSEOUT
===============================================================================

Keep all existing valid C4 proofs and add or strengthen these surfaces.

5.1 Production fact consumption

Gate theorems that show:

- the production target is obtained as a TypeNameRef;
- production reads the exact stored TypeNameFact;
- production reads the exact operand ExprFact;
- the successful production result equals the index-free GoTypes result;
- the failed production result contains exact invalid-conversion evidence;
- the same type-name map used by production is the map sealed into ElaborationFacts;
- failure diagnostics use that map and do not rebuild or resolve again.

A theorem that only says the public query equals predeclared_type is not enough. The production call path itself
must be tied to the stored entry.

5.2 All sixteen resolver cases

Provide one load-bearing universal theorem or one reviewed closed conjunction that pins all sixteen source-name
mappings. Gate it.

5.3 Repeated equal names at distinct occurrences

Replace the current tautological scar_repeated_uint8 equality with a real snapshot fixture containing two equal
source type names at two different conversion positions.

Prove:

- two TypeNameRefs exist;
- their NodeKeys differ;
- their recovered TypeSyntax values are equal;
- their stored TypeNameFact values are equal.

5.4 Intrinsic exclusions and foreign/wrong-kind facts

Keep the intrinsic unsupported-name proof and the sealed table domain proof. Ensure the final evidence shows that
wrong-kind and foreign keys cannot create or query a type-name fact.

5.5 Pinned-Go alias matrix

Use the pinned Docker Go toolchain. Do not use the host toolchain.

The matrix must include:

Accepted:

- byte(0);
- byte(255);
- uint8(255), with the same result as byte(255);
- rune(-2147483648);
- rune(2147483647);
- int32 cases at the same values;
- the existing representative byte/rune print case may remain.

Rejected with a conversion/type-check diagnostic, not an infrastructure failure:

- byte(-1);
- byte(256);
- rune(-2147483649);
- rune(2147483648);
- matching uint8/int32 cases.

The Rocq side must prove the matching accepted/rejected outcomes. The Docker side may reuse the existing acc_conv
and rej_conv helpers. Remove the WitnessAlias claim that expected Go build failures are not tested.

===============================================================================
6. NO-RESIDUE AND PERMANENT PROSE
===============================================================================

Read the current permanent files in context and fix false current descriptions.

At minimum:

- update the ARCHITECTURE.md GoAST row to the one EConvert TypeSyntax GoExpr path;
- update the ARCHITECTURE.md GoCompile row to say production consumes retained type-name and operand facts;
- update the ARCHITECTURE.md GoRender row to source-spelling rendering;
- update active master-plan prose that calls the deleted family-specific constructors "current";
- update WitnessAlias and Docker comments to the full alias differential;
- update PROGRESS.md, NEXT_STEPS, REVIEW_REQUEST, and SOURCE_FOREST_STATUS to the true repair/freeze state.

Search the full tracked tree for:

- EIntConvert;
- EFloatConvert;
- EComplexConvert;
- current prose that describes semantic target tags in raw conversion syntax;
- current prose that says type-name facts are retained but not consumed;
- duplicate source-name lookup tables;
- dead semantic keyword renderer helpers;
- TByte, TRune, IByte, IRune;
- uintptr or rune-literal/rune-constant implementation.

Historical text inside the frozen C4 contract may name the deleted constructors as the thing C4 had to replace.
Inspect hits in context. Do not alter the binding contract or its hash.

Delete dead semantic keyword helpers and their gate/examples if no live approved proof consumes them. Do not keep
them for possible later work.

===============================================================================
7. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this repair.

Use this loop:

1. inspect the current root and the full affected proof chain;
2. make one coherent change;
3. run the narrow compile/proof check for that change;
4. repair all failures;
5. run the full required verification;
6. inspect the complete diff and residue searches;
7. repeat until the final freeze is clean.

Do not stop for:

- design approval;
- an intermediate green module;
- a partial migration report;
- a large proof count;
- a clean but incomplete commit;
- a question already answered by this directive or the binding C4 contract.

Stop only in one of two states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after reasonable direct repair attempts. Report the exact
file, theorem or command, the smallest failing case, and why the binding contract does not decide it. Do not call
ordinary proof work or a large diff a blocker.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service. If no configured notification method
is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR COMPLETE

or

FIDO C4 REPAIR BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
8. FINAL VERIFICATION, FREEZE, AND PUSH
===============================================================================

Run the full binding-contract verification from a clean supported environment:

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
- full old-constructor/current-prose residue search;
- no-C5 search;
- duplicate lookup/spelling-table search;
- standard-collection audit;
- one retained index/visit call-path evidence;
- one once-built type-name map call-path evidence;
- one expression outcome/fact authority call-path evidence;
- git status --short;
- git log --oneline for both:
  - 8c9212a..final;
  - 89b8e54..final.

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 repair candidate complete;
   - original C4 baseline 8c9212a;
   - blocked candidate baseline 89b8e54;
   - this freeze commit is the new candidate head;
   - full human review range is 8c9212a..this freeze commit;
   - repair range is 89b8e54..this freeze commit;
   - human Implementation Review pending;
   - automatic Codex review disabled;
   - C5 forbidden.

2. Keep REVIEW_REQUEST closed. Set its result to:

   BLOCKING result repaired; new human C4 Implementation Review pending

3. Commit the final status and any final proof-safe changes as:

   review(final): C4 — freeze retained-fact repair candidate

4. Run every final check on that exact commit.

5. If any check or review search fails, repair it, make a new freeze commit, and repeat. Only the final passing
   freeze commit is the candidate head.

6. Push main without force.

7. Notify Rob and report:

   - original C4 baseline;
   - blocked candidate;
   - repair authority commit;
   - final candidate SHA and both ranges;
   - exact files changed in the repair;
   - how production now consumes the retained TypeNameFact and operand ExprFact;
   - how one convert_const result supplies success or exact failure evidence;
   - target-ref and source-spelling diagnostic proofs;
   - the full alias differential;
   - all verification results;
   - gate count;
   - generated-byte identity;
   - residue/no-C5 results;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop. Do not begin C5.
