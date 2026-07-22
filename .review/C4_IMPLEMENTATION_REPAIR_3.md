Claude Code directive: C4 Implementation Review BLOCKING — retained-table bottom-up repair 3

Repository:

rhencke/fido

Current clean main and required repair baseline:

1b38b68c104bc987744ececc36e771d8977bdbf2

C4 code candidate reviewed:

806ce87373e29b6980e5c3d9d274ffa86580449b

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

First blocked C4 candidate:

89b8e54634e7012612a51990756ad29a579c1b0f

Second blocked C4 candidate:

1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-retained-table-bottom-up-repair-3

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

This is Rob's later explicit authorization to replace the flawed C4 production root at the current main above.
It does not replace or weaken the binding C4 contract.

The code candidate was frozen at 806ce873. Two later commits changed only tracked prose:

- 000b2056f61e9a982c2ae0fc623027e7fd47bc9d — CLAUDE.md
- 1b38b68c104bc987744ececc36e771d8977bdbf2 — life.md

Start from the exact current clean main 1b38b68c above. Preserve the persona unless a correction below requires a
small prose change. Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 806ce873.

Repair 2 moved typed references into typed_outcome, fixed the hidden use-resolution rescan, and improved failure
evidence. Those were real gains.

It did not implement the required production model.

The new root still has two decisive faults:

1. production does not consume the TypeNameFactTable object built from the retained visit;
2. the outcome table is filled by recursively re-evaluating each expression subtree, not by one bottom-up
   accumulator reading the already-computed operand outcome.

Thus a nested conversion is evaluated once while computing each ancestor and again when its own map entry is
built. The claim "one convert_const per conversion" is false for the full production pass.

Do not add bridge theorems around the current root. Delete and replace that root.

The following parts remain good unless the replacement directly needs a change:

- the proof-carrying IdentifierSyntax domain;
- the closed sixteen-name TypeName class;
- SupportedTypeName retaining IdentifierSyntax plus its matching lexical symbol;
- one raw EConvert TypeSyntax GoExpr;
- KTypeName, TypeNameRef, and the source-order target/operand layout;
- source-spelling rendering;
- the compiler-owned sixteen-name mapping;
- byte/rune source identity and semantic alias mapping;
- use_resolved_of_ci as a result derived from an already-computed ConstInfo;
- total target and operand child-reference construction for a proved conversion view;
- EOConvFail carrying conversion, target, and operand references;
- source-target preservation in erased diagnostics;
- byte/uint8 and rune/int32 report distinction;
- the full accepted and rejected pinned-Go alias matrix;
- unchanged canonical generated Go bytes;
- absence of C5 uintptr and rune-literal work;
- deletion of the former family-specific conversion constructors and dead renderer keyword helpers.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_3.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 retained-table bottom-up repair 3;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - first blocked candidate;
   - second blocked candidate;
   - third blocked code candidate: 806ce87373e29b6980e5c3d9d274ffa86580449b;
   - current repair baseline: 1b38b68c104bc987744ececc36e771d8977bdbf2;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_3.md;
   - human repair authorization token above;
   - state: C4 Implementation Review BLOCKING; retained-table bottom-up repair active;
   - automatic Codex review: disabled;
   - C5: forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-retained-table-bottom-up-repair-3
   result: BLOCKING at 806ce873; retained-table bottom-up repair 3 active

   Keep the original C4 contract path and hash. Do not request a review through this file.

4. Update .review/SOURCE_FOREST_STATUS.md with a concise exact record of all blocking classes in section 2.

5. Commit only these authority changes:

   review(repair): C4 — require retained tables and bottom-up outcomes

No Rocq, Docker, e2e, gate, generated, plugin, shell, architecture, CLAUDE, or life change may enter that authority
commit.

6. After the authority commit and after NEXT_STEPS/STATUS preserve the prior repair history, delete the superseded:

   .review/C4_IMPLEMENTATION_REPAIR_2.md

in the first implementation commit. Git history is its archive.

Do not delete:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_3.md.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 The once-built TypeNameFactTable is still beside production

elaborate_indexed binds:

  visit
  tnfacts := fold_right add_tn_fact ... visit

and seals that local tnfacts map into ElaborationFacts.

But typed_outcome_e does not receive tnfacts or a TypeNameFactTable. It calls:

  tnfact_at p tr

tnfact_at calls:

  prog_type_name_facts p

and prog_type_name_facts p folds:

  prog_visit p

Therefore every conversion rebuilds the whole source-derived type-name map through another program visit.

The local tnfacts value built by elaborate_indexed is not consumed by the expression path. It is only equal to
the independently recomputed map.

elaborate_ok_seals_tnfacts proves equality with prog_type_name_facts p. It does not prove that production consumed
the local object which was sealed.

This is the exact anti-pattern the contract forbids:

- equivalent recomputation sold as retained authority;
- a correct fact table beside the live path;
- object equality substituted for object consumption.

2.2 The outcome map is not a bottom-up semantic authority

typed_outcome_e recursively evaluates the operand expression view.

add_typed_outcome is then folded over every expression occurrence and calls typed_outcome separately for each
one.

For:

  outer(inner(literal))

the production pass computes inner while computing outer, then computes inner again when the fold reaches the
inner occurrence's own entry.

For a chain of nested conversions, each inner conversion is recomputed once for every ancestor. The same
conversion occurrence can call convert_const several times during one elaboration.

prog_outcomes is therefore a cache of independently recursive results, not the source of operand results.

The C4 contract requires:

- an already-computed operand expression fact;
- one bottom-up occurrence-indexed production path;
- one convert_const call for each conversion occurrence.

Repair 2 required a proof-carrying bottom-up accumulator. Structural recursion over the source subtree is not an
equivalent design.

2.3 The retained typed-work view was not built

Repair 2 required production to turn each relevant retained visit item into a proof-backed typed work value before
semantic processing.

The current fold still performs:

  GoIndex.as_expr idx (fst ro)

inside add_typed_outcome and silently leaves the map unchanged on None.

A real expression occurrence whose index/ref relation failed would therefore disappear from the outcome map.

The live production input must carry the exact typed expression reference. A kind mismatch for a source expression
is an impossible proof branch, not permission to skip it.

2.4 The diagnostic fold still has fail-open structural branches

occ_expr_diags_sm again calls:

  GoIndex.as_expr idx (fst ro)

and returns [] on None.

For a stored EOConvFail, the diagnostic can and should use the stored conversion ExprRef directly. It must not
first run a second optional structural lookup whose failure erases the diagnostic.

A default failure also needs an exact typed expression work item or another total proof-backed route.

2.5 Production failure evidence is weakened before it reaches DiagnosticReason

EOConvFail stores:

- conversion ExprRef;
- target TypeNameRef;
- operand ExprRef;
- resolved target;
- operand status.

conv_failure_om pattern-matches the operand reference as _opr and discards it.

DRInvalidConversion has no operand-ref field.

The required production proof cannot then establish from the emitted diagnostic alone that:

- its operand_ref is the exact stored operand ExprRef from the same outcome;
- its operand status came from the fact/outcome at that ref.

The current diagnostic soundness surface returns to local_conv_failure and recursive const_info. That is a source
specification theorem, not the required production-evidence theorem.

The repair may either:

- add the operand ExprRef to DRInvalidConversion; or
- retain an equally strong proof-backed diagnostic bundle whose public reason is a projection.

The simpler form is preferred. Do not copy operand syntax or source text.

2.6 The gated production theorem proves the rejected model

prog_conv_outcome_consumes is stated through:

- prog_outcomes idx;
- tnfact_at p tr;
- recursive const_info x.

It does not state:

- a query against the exact TypeNameFactTable object built from the retained visit;
- a total query against the processed-suffix outcome accumulator at the operand ExprRef;
- that the exact table object is later sealed;
- that this conversion occurrence is processed exactly once.

The theorem proves the structural recursive helper. It does not prove the contract's production path.

The gate comments repeat the false "once-built map" and "ONE convert_const" claims.

2.7 The concrete repeated-name fixture queries the wrong authority

two_uint8_distinct_target_refs is a useful real two-occurrence source fixture.

Its final fact comparison uses:

  tnfact_at two_uint8_program tr1
  tnfact_at two_uint8_program tr2

That is the raw recomputing query.

The required fixture must obtain a real successful ElaborationFacts or CompilableProgram value and query both
TypeNameRefs through the sealed TypeNameFactTable object retained by that one elaboration.

Keep the source fixture and ref-minting proof. Replace the fact query.

2.8 A fake leaf meaning remains

leaf_ci still defines:

  EConvert _ _ => CIUntyped (CBool false)

and calls the branch unreachable.

A conversion does not denote that value. Remove the fake semantic case.

Use a leaf-only source view, a dependent proof that the constructor is not EConvert, or another total form which
cannot ask for a leaf status of a conversion.

2.9 Current authority and permanent prose are false

At least these tracked claims are false:

- NEXT_STEPS says the candidate has one typed semantic route;
- SOURCE_FOREST_STATUS says tnfacts comes from the retained visit and is consumed and sealed;
- SOURCE_FOREST_STATUS says each conversion calls convert_const once;
- GoCompile comments say typed_outcome obtains an already-computed operand outcome;
- elaborate_indexed says tnfact_at reads the same local map;
- gate/axiom_gate.v calls prog_outcomes one bottom-up outcome authority;
- gate comments say the same once-built map is consumed and sealed;
- the concrete repeated-name comment calls tnfact_at a stored-fact query;
- life.md says the C4 fault was fixed by putting typed_outcome on the path.

Correct these claims after the implementation is true.

The persona and imaginative parts of life.md are not under review for style. Its technical project claims must be
true.

2.10 A tracked file cannot exempt itself from review

CLAUDE.md currently says life.md may be changed in ordinary work and "no review gate governs it."

That rule is incompatible with a frozen-candidate process. A tracked file can:

- change a candidate;
- contain factual architecture claims;
- create review noise;
- make the exact reviewed head unclear.

Preserve the persona. Correct the process rule:

- every tracked file participates in git diff, review, and freeze;
- life.md changes require an explicit docs task or explicit human authorization;
- do not modify life.md during an active functional checkpoint unless the checkpoint authority names it;
- factual claims in life.md must match accepted repository state.

Do not add new persona prose in this repair.

===============================================================================
3. REPLACE THE PRODUCTION ROOT
===============================================================================

This section specifies the required model.

Choose the smallest proof-friendly form which meets it. Do not stop for another design check.

3.1 One proof-backed retained compilation input

Build one transient value for the C4 production phase, equivalent to:

  CompilationInput p := {
    indexed_program;
    syntax_index;
    visit_blocks;
    visit;
    proof that visit = concat visit_blocks;
    proof that all refs and occurrences belong to this exact source snapshot
  }

The exact name and fields are your choice.

Rules:

- elaborate builds it once;
- every production C4 builder consumes this object or exact fields projected from it;
- no production builder hides a call to prog_blocks p, prog_visit p, binding_visit, visit_file, or index_program p;
- proof specifications may use those source functions;
- this is derived evidence over the one GoProgram, not a second AST;
- do not store it permanently unless a later consumer needs it.

3.2 Build one typed work stream from the retained visit

Convert the relevant retained visit entries into a proof-backed work stream before semantic processing.

A live expression work item must carry its exact ExprRef.

A live conversion work item must carry at least:

- the conversion ExprRef;
- the target TypeNameRef;
- the operand ExprRef;
- proof that the source view is EConvert target operand;
- proof that target_ref is the exact direct RConversionTarget child;
- proof that operand_ref is the exact direct RConversionOperand child;
- proof that target precedes operand;
- exact source target recovery;
- exact source operand recovery;
- the preorder/suffix fact needed for the bottom-up accumulator.

A non-expression visit item can be omitted from the expression work stream by a source-view decision.

For a source occurrence whose view is Some expression, minting the ExprRef must be total. Do not use:

  as_expr ... = None => skip

on the live expression path.

This typed work stream is not a typed AST. It contains refs and proofs over the one source snapshot. It must not
copy semantic facts.

3.3 Build one exact TypeNameFactTable object from the retained visit

Fold the exact retained visit into the map and immediately construct one proof-backed TypeNameFactTable value.

Add a table-level total query equivalent to:

  type_name_fact_at_table :
    TypeNameFactTable p ip -> TypeNameRef p -> TypeNameFact

It must:

- project the stored map entry;
- eliminate None through the table's completeness proof;
- never call predeclared_type or rebuild the map.

The production expression phase must receive this exact table object and query it with the retained target
TypeNameRef.

On success, ElaborationFacts must store this exact TypeNameFactTable object, not a new wrapper around an equal map.

The public type_name_fact_at query must delegate to the same table-level query.

Delete the internal raw tnfact_at p tr production query.

A source-level prog_type_name_facts specification may remain if useful for proofs, but elaborate and every
production builder must not call it.

3.4 Use one proof-carrying bottom-up outcome accumulator

Replace typed_outcome_e, typed_outcome, add_typed_outcome, and the current prog_outcomes production root.

Fold right over the retained typed work stream or another exact source-order stream in which conversion operands
are already in the processed suffix.

Use an accumulator equivalent to:

  ExprOutcomeAccumulator := {
    outcome_map;
    completeness for every processed expression work item/ref;
    exact source-view correspondence
  }

For a conversion work item:

1. query the exact TypeNameFactTable at target_ref;
2. query the processed-suffix accumulator at operand_ref;
3. if the operand outcome is EOOk opf, call convert_const once on:
     tnf_type target_fact
     ef_const_status opf
4. construct EOOk from that one result, or construct exact EOConvFail;
5. if the real operand outcome is EOConvFail or EOChildFail, construct EOChildFail;
6. add this conversion outcome to the accumulator once.

Rules:

- no structural recursion on the GoExpr subtree in the production builder;
- no recursive call from a conversion to a semantic helper for its operand;
- no const_info, resolve_expr_const, resolve_expr, local_conv_failure, or conv_targets call in the production
  builder;
- no raw operand-key lookup as the public production interface;
- a missing operand entry is impossible and must be eliminated by proof;
- EOChildFail cannot represent a missing ref, missing fact, missing map entry, or kind mismatch;
- each source expression occurrence gets exactly one outcome entry from this one fold;
- each conversion occurrence reaches exactly one convert_const call in this one fold.

3.5 Derive use resolution from the computed status

Keep use_resolved_of_ci or an equivalent function.

For EOOk:

- compute ef_use_resolved only from the current work item's role and the just-computed ConstInfo;
- do not inspect or recursively evaluate the raw GoExpr;
- prove equality with the index-free resolve_expr_const specification.

3.6 Store exact local failure evidence

EOConvFail must retain or intrinsically carry:

- exact conversion ExprRef;
- exact target TypeNameRef;
- exact operand ExprRef;
- exact TypeNameFact read at target_ref, or its semantic target plus proof of equality;
- exact successful operand ExprFact/status read at operand_ref;
- proof that convert_const rejects that target and status.

The exact record/constructor form is your choice.

Do not copy source syntax or spelling into the outcome.

3.7 Diagnostics must be a total projection of the outcome phase

Build expression diagnostics from:

- the exact typed work item;
- the exact stored outcome at its ExprRef;
- the one enclosing-context annotation.

For EOConvFail:

- emit one DRInvalidConversion using the stored conversion, target, and operand evidence;
- add outer context;
- do not call as_expr, conversion_target_ref, conversion_operand_ref, tnfact_at, type-name resolution,
  convert_const, const_info, or local_conv_failure.

For EOChildFail:

- emit no local conversion reason.

For EOOk at a println use:

- decide default failure from its stored ExprFact/use result;
- use the exact expression ref already carried by the work item.

No live expression occurrence can disappear through an optional structural branch.

Prefer adding operand_ref to DRInvalidConversion. If another form is chosen, the public production theorem must
recover the exact stored operand ref without reminting or source recursion.

Erased reports need not retain operand_ref, but erasure must remain a pure projection.

3.8 One phase object, not loose equal values

Build one transient expression phase value, equivalent to:

  ExpressionPhase := {
    retained TypeNameFactTable;
    complete ExprOutcome table;
    expression-fact projection;
    expression diagnostics;
    proofs that facts and diagnostics are projections of this exact outcome table
  }

The exact shape can differ.

The point is object identity:

- one table object is built;
- production queries it;
- one outcome accumulator is built;
- facts project it;
- diagnostics project it;
- on success the same table object is sealed.

Do not prove completion by comparing each local value with a separately recomputed prog_* helper.

3.9 Keep the declarative specification separate and exact

GoTypes.const_info and ProgramTyped may remain as index-free specifications.

Source helpers such as occ_expr_fact and local_conv_failure may remain if useful for theorem statements.

They must not be called by the production phase.

Prove the production phase exact against the declarative specification after the production model is correct.

3.10 Remove fake meanings

Replace leaf_ci with a leaf-only domain or proof-backed call which has no EConvert case.

Delete every fake semantic value used only to totalize an impossible branch.

===============================================================================
4. REQUIRED LOAD-BEARING PROOFS
===============================================================================

Gate theorems about the exact functions and objects elaborate calls.

4.1 Retained input

Prove:

- one CompilationInput is built from the one index and one blocks/visit computation;
- the type-name table builder consumes its exact visit;
- the typed-work builder consumes its exact visit and exact index;
- the outcome builder consumes its exact typed work;
- no production builder recomputes prog_visit/prog_blocks/index_program.

4.2 Typed work exactness

For every expression work item:

- its ExprRef is exact for the delivered occurrence;
- its source view is exact.

For every conversion work item:

- target and operand refs are exact direct children with the correct roles;
- target precedes operand;
- source target and operand recover exactly;
- operand lies in the already-processed suffix used by the accumulator.

4.3 Type-name table totality and identity

Prove:

- every target TypeNameRef has one stored TypeNameFact;
- type_name_fact_at_table returns that exact entry;
- wrong-kind and foreign refs cannot be supplied;
- the exact table object passed to the outcome builder is the exact object stored in ElaborationFacts;
- the public query delegates to the same table query.

Do not use a theorem whose conclusion is only equality with prog_type_name_facts p.

4.4 Outcome accumulator totality

Prove:

- every processed expression ref has one exact outcome;
- the operand-ref query is total for a conversion step;
- no lookup fallback exists;
- each source expression occurrence is inserted once;
- the final table domain is exactly the expression work items.

4.5 One conversion semantic call

State the main theorem over:

- the exact conversion work item;
- conversion ExprRef;
- target TypeNameRef;
- operand ExprRef;
- exact TypeNameFact table query;
- exact operand outcome query.

Prove the result is exactly:

- EOOk from the one convert_const result;
- exact EOConvFail when it rejects;
- EOChildFail only when the real operand outcome is non-success.

Do not state the main theorem through recursive const_info x or recursive typed_outcome.

4.6 Use-result exactness

Prove every EOOk fact's ef_use_resolved is a function of:

- that same fact's ef_const_status;
- the work item's exact role.

Prove it equals the source specification.

4.7 Production diagnostic exactness

For every production DRInvalidConversion, prove from the production phase:

- primary is the exact conversion ExprRef from the stored outcome;
- target_ref is the exact stored target TypeNameRef;
- operand_ref is the exact stored operand ExprRef;
- target equals the exact TypeNameFact query at target_ref;
- operand status equals the exact successful ExprFact/status at operand_ref;
- convert_const rejects the pair;
- source target erasure comes through target_ref;
- one reason exists for each innermost local failure;
- no outer reason exists for child failure;
- ordering, anchors, and outer context remain exact.

Do not use local_conv_failure as the starting premise of this theorem.

4.8 Facts and diagnostics share one outcome object

Prove:

- the exact ExprFactTable is the success projection of the exact outcome table used by diagnostics;
- the diagnostic list is the failure/default projection of that exact table;
- no fact or diagnostic path recomputes expression semantics.

4.9 Concrete repeated-name snapshot

Keep the real two-uint8 program.

From one successful elaboration or CompilableProgram:

- mint both real TypeNameRefs;
- prove their NodeKeys differ;
- prove their recovered TypeSyntax values are equal;
- query both through the sealed TypeNameFactTable;
- prove those stored facts are equal.

Gate this concrete theorem.

4.10 All prior valid C4 claims

Keep or re-prove:

- all sixteen resolver cases;
- byte/uint8 and rune/int32 source-distinct/semantic-equal facts;
- type-name table domain and total query;
- wrong-kind/foreign exclusion;
- invalid byte/uint8 and rune/int32 erased-report distinction;
- renderer source spelling and denotation;
- SafeProgram-only public render/materialize path;
- exact diagnostic completeness and acceptance;
- full alias differential;
- no C5 scope.

===============================================================================
5. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Delete or replace the rejected production root and every proof which exists only to defend it.

At minimum inspect and normally delete/replace:

- tnfact_at;
- prog_tnfacts_ref_not_none;
- typed_outcome_e;
- typed_outcome;
- add_typed_outcome;
- prog_outcomes;
- typed_outcome_e_conv;
- typed_outcome_target_type;
- typed_outcome_e_const_ok / const_none / use-res proofs tied to recursive production;
- typed_outcome_convfail;
- typed_outcome_childfail;
- prog_conv_outcome_consumes;
- elaborate_ok_seals_tnfacts in its current extensional form;
- conv_failure_om if it drops operand evidence;
- local_conv_failure_om_eq and proof chains which return to source recursion;
- the current two_uint8 fact-query ending;
- fake leaf_ci EConvert fallback;
- gate entries and comments for rejected theorems.

A source-only specification helper may remain only when a live theorem needs it and its comment says specification.

Run a full tracked-tree search for:

- tnfact_at on a production path;
- prog_type_name_facts inside elaborate or a production helper;
- recursive typed_outcome;
- production const_info / resolve_expr_const / local_conv_failure;
- as_expr None => skip on a source expression;
- diagnostic structural None => [];
- fake CBool false leaf meaning;
- claims of one visit or one convert_const which are not true;
- "stored fact" claims backed by raw recomputing queries;
- old conversion constructors;
- duplicate source-name resolver/spelling tables;
- C5 uintptr or rune-literal/rune-constant code.

The binding C4 contract may name deleted constructors as history. Inspect each hit in context.

===============================================================================
6. PERMANENT PROSE AND PROCESS CORRECTION
===============================================================================

After the code path is true, update:

- .review/NEXT_STEPS.md;
- .review/REVIEW_REQUEST.md;
- .review/SOURCE_FOREST_STATUS.md;
- ARCHITECTURE.md;
- PROGRESS.md;
- GoCompile.v comments;
- gate/axiom_gate.v comments;
- CLAUDE.md;
- life.md.

Requirements:

- remove every false repair-2 completion claim;
- describe the retained-table and bottom-up path exactly;
- do not call an equality proof object identity;
- do not claim tests prove one call;
- life.md must not say the rejected typed_outcome root fixed C4;
- preserve the dog persona and nontechnical life prose;
- CLAUDE.md must state that all tracked files participate in review and freeze;
- life.md changes require an explicit docs task or human authorization;
- no tracked prose may self-exempt from review;
- do not add new persona history during this functional repair.

===============================================================================
7. TESTS AND DIFFERENTIALS
===============================================================================

Keep the current full pinned-Go alias matrix.

Keep or add Rocq fixtures for:

- accepted and rejected byte/uint8 boundaries;
- accepted and rejected rune/int32 boundaries;
- successful nested conversion as a println argument;
- locally failing inner conversion with one inner diagnostic and no outer diagnostic;
- a deep nested conversion chain whose final outcome/facts come from the one bottom-up table;
- exact diagnostic operand-ref evidence;
- the sealed-table repeated-name fixture.

Do not add a runtime counter and do not claim a fixture proves one call.

The source form of the production builder and the universal proofs establish one convert_const call per occurrence.

===============================================================================
8. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this repair.

Use this loop:

1. inspect the entire rejected production and proof root;
2. delete the recursive/recomputing root before writing replacement bridge proofs;
3. build one retained input and one typed work layer;
4. build one table object and one bottom-up accumulator;
5. run narrow compile/proof checks;
6. repair failures at their root;
7. run the full required verification;
8. inspect the complete call path, proof statements, diff, and residue searches;
9. repeat until the final freeze is clean.

Do not stop for:

- design approval;
- an intermediate green file;
- a partial report;
- proof volume;
- a large diff;
- fear of deleting current proofs;
- a clean but incomplete commit;
- a question already decided by this directive or the binding contract.

Past effort has no claim on the design.

Stop only in one of two terminal states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after direct repair attempts. Report the exact file,
definition/theorem or command, the smallest failing case, and why neither this directive nor the binding contract
decides it.

Proof volume, a large refactor, or ordinary proof repair is not a blocker.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 3 COMPLETE

or

FIDO C4 REPAIR 3 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
9. FINAL VERIFICATION
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
- whole-theory audit and self-tests A-E;
- full pinned-Go alias matrix;
- exact generated go.mod and recursive .go byte identity;
- full old-constructor/no-C5 search;
- duplicate type-name spelling/resolver search;
- standard-collection audit;
- exact elaborate -> retained input -> typed work -> TypeNameFactTable -> bottom-up accumulator call path;
- evidence that the exact same TypeNameFactTable object is queried and sealed;
- evidence that each conversion reads the operand outcome through its ExprRef from the processed accumulator;
- evidence that each source expression gets one outcome entry;
- evidence that the live conversion step contains one convert_const call and no recursive semantic helper;
- evidence that impossible lookups cannot become skip, [], EOChildFail, or a fake value;
- production diagnostic operand-ref evidence;
- concrete repeated-name sealed-fact result;
- corrections to tracked persona/process prose;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 1c4a7de..final;
  - 806ce87..final;
  - 1b38b68..final.

A green command proves only what it checks. It does not replace the call-path and object-identity evidence.

===============================================================================
10. FINAL FREEZE AND PUSH
===============================================================================

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 retained-table bottom-up repair 3 candidate complete;
   - original C4 baseline: 8c9212a;
   - first blocked candidate: 89b8e54;
   - second blocked candidate: 1c4a7de;
   - third blocked candidate: 806ce87;
   - repair-3 baseline: 1b38b68;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-2-and-later range: 1c4a7de..this freeze commit;
   - repair-3 range: 1b38b68..this freeze commit;
   - human C4 Implementation Review pending;
   - automatic Codex review disabled;
   - C5 forbidden.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-retained-table-bottom-up-repair-3
   result: third BLOCKING result repaired; new human C4 Implementation Review pending

3. Commit the final status and final proof-safe changes as:

   review(final): C4 — freeze retained-table bottom-up candidate

4. Run every final check and call-path audit on that exact commit.

5. If a check, proof audit, object-identity audit, prose audit, or residue search fails, repair it, make a new freeze
   commit, and repeat. Only the final passing freeze commit is the candidate head.

6. Push main without force.

7. Notify Rob and report:

   - original C4 baseline;
   - all three blocked candidates;
   - repair-3 authority commit;
   - final candidate SHA and all ranges;
   - exact files changed in repair 3;
   - the deleted recursive/recomputing production root;
   - the one retained compilation input;
   - the typed expression/conversion work model;
   - the exact TypeNameFactTable object built, queried, and sealed;
   - the proof-carrying bottom-up outcome accumulator;
   - the exact operand-ref outcome query;
   - one convert_const call per conversion occurrence;
   - use-context resolution from the computed status;
   - diagnostics as projections of exact stored failure evidence;
   - the sealed-table repeated-name fixture;
   - all verification results;
   - gate count;
   - generated-byte identity;
   - residue/no-C5 results;
   - tracked prose/process corrections;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop. Do not begin C5.
