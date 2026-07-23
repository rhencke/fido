Claude Code directive: C4 Implementation Review BLOCKING — exact retained work-object repair 7

Repository:

rhencke/fido

Required clean baseline and seventh blocked C4 candidate:

3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

Prior blocked C4 candidates:

89b8e54634e7012612a51990756ad29a579c1b0f
1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca
806ce87373e29b6980e5c3d9d274ffa86580449b
af2fc87e7726a4fc68bb9480c53cf64faa83717b
9d4aff5d94d9aac293ff7fb98a7d9fdd59159022
3b4f40e1f14c501fd76333ec8a8cd3e582ed1598

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-exact-retained-work-object-repair-7

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

This is Rob's later explicit authorization to replace the remaining canonical-recomputation root in the C4
production phase.

It does not replace or weaken the binding C4 contract.

Start only from the exact clean baseline above. Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 3a92d22820705f55093c0e2b3ff18a0f8ad7f4dc.

Repair 6 closed several large defects:

- CompilationInput now stores one let-bound blocks value and one stored flattened visit;
- ExprWork carries an exact ExprRef and conversion child refs;
- one canonical work enumeration exists;
- the outcome fold is bottom-up over expression work rather than raw occurrences;
- ForestOutcomeTable carries direct causes and an exact key domain;
- fact and diagnostic paths use total outcome queries;
- DRInvalidConversion retains the operand ExprRef;
- the deep fixtures query real production outcomes;
- the two-uint8 fixture uses actual successful ElaborationFacts;
- the scope ledger now separates classification from approval;
- ADR-0002 is honestly rejected/open;
- generated output and C5 scope remain unchanged.

Keep those gains unless the correct root requires a direct replacement.

The remaining defect is narrower and decisive:

There is still no ONE proof-carrying ExprWorkForest object passed through production.

The candidate has pure canonical functions named prog_forest/prog_forest_blocks/prog_forest_awork. Each later
phase calls those functions again. ExpressionPhase stores one raw list in ep_work, but outcomes, facts,
annotation, and diagnostics do not consume that field. They independently compute equal lists from input.

The proof-bearing sigma returned by build_forest_blocks is projected to raw lists with proj1_sig; its proof is
recovered later through a separate proj2_sig call.

This is the same prohibited architecture at one final layer:

- exact evidence exists;
- the evidence-bearing object is discarded;
- raw data is recomputed through a canonical helper;
- equality theorems later claim shared provenance.

Do not add another equality theorem around this root.

Build one proof-carrying work-forest object and pass that exact value stage to stage.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_7.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 exact retained work-object repair 7;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - all seven blocked candidates;
   - current repair baseline: the full 3a92d228 SHA above;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_7.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; exact retained work-object repair active;
   - ADR-0001: PROPOSED pending Rob;
   - ADR-0002: REJECTED AS WRITTEN / OPEN; no numeric implementation change authorized;
   - automatic Codex review: disabled;
   - C5: forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-exact-retained-work-object-repair-7
   result: BLOCKING at 3a92d228; exact retained work-object repair 7 active

4. Update .review/SOURCE_FOREST_STATUS.md with a concise exact record of every blocking class in section 2.

5. Commit only these authority changes:

   review(repair): C4 — pass one retained work object end to end

No Rocq, Docker, e2e, gate, generated, plugin, shell, architecture, persona, life, ADR-content, or numeric-model
change may enter that authority commit.

6. After the authority commit and after NEXT_STEPS/STATUS preserve the prior repair history, delete the superseded:

   .review/C4_IMPLEMENTATION_REPAIR_6.md

in the first implementation commit. Git history is its archive.

Keep:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_7.md;
- the current scope ledger;
- ADR-0001 and ADR-0002.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 There is no ExprWorkForest object

The candidate calls prog_forest a retained forest, but it is only:

  concat (prog_forest_blocks input)

and prog_forest_blocks is:

  proj1_sig (build_forest_blocks ...)

The proof returned by build_forest_blocks is discarded. Later theorems call proj2_sig on build_forest_blocks
again to recover equivalence.

No record retains together:

- per-file work blocks;
- the flattened work list;
- flat = concat blocks;
- exact forward and reverse domain;
- unique keys;
- one item per live expression;
- source-order and per-file order;
- conversion operand membership in the processed suffix.

This violates the proof-on-the-path rule.

2.2 build_expression_phase recomputes canonical work instead of passing one value

The phase builder independently evaluates:

- prog_forest input for ep_work;
- build_forest_outcome_table input tnft, which internally calls prog_forest input;
- build_forest_expr_fact_table input tnft ot, whose forest_facts calls prog_forest input;
- prog_forest_awork input, which calls prog_forest_blocks input;
- forest_diags input tnft ot, which calls prog_forest_awork input again.

The local ep_work value is not consumed by any downstream builder.

The same issue exists for annotated work: ep_awork is stored, but ep_diags is computed through a fresh
prog_forest_awork call rather than consuming ep_awork.

Pure equality of repeated function calls is not retained object flow.

2.3 ForestOutcomeTable is indexed by input, not by the exact forest object

ForestOutcomeTable currently has the shape:

  ForestOutcomeTable input tnft

and its domain/cause fields mention the global function:

  prog_forest input

It does not have the shape:

  ForestOutcomeTable forest tnft

Therefore the type does not prove that the table was built from the exact ep_work field retained in the phase.

ep_work_prov only says ep_work = prog_forest input after the fact.

The outcome table must depend on the exact retained work object it consumes.

2.4 The live operand lookup still uses raw child-key arithmetic

A conversion work item carries operand ExprRef opr.

But build_outcomes_forest tests and reads the prior outcome at:

  operand_key (ew_node_ref w)

It later calls conversion_operand_ref_conv to prove that the carried opr has that key.

The live lookup therefore still uses raw key arithmetic, with the typed ref justified afterward.

The semantic step must obtain the exact operand work item from the retained forest and query the processed
accumulator at that work/ref. The raw operand_key formula may support the structural theorem, but it cannot be
the live production lookup.

2.5 ConvRefinement does not carry the complete conversion-work relation

The current ConvRefinement carries:

- target TypeNameRef;
- operand ExprRef;
- target-ref equation;
- target source syntax;
- operand-ref equation.

It does not carry or retain:

- target role RConversionTarget;
- operand role RConversionOperand;
- direct-child facts;
- target-before-operand order;
- operand source view = x;
- the exact operand ExprWork item;
- operand membership in the processed forest suffix.

Those facts are reconstructed later from conversion_*_ref_conv and prog_forest_operand_in_tail.

A conversion semantic step must consume one proof-backed conversion work view which already identifies the exact
operand work item in the suffix.

Do not create a second AST. This is a refinement/view over one retained forest item.

2.6 The annotated work forest is another raw projection

prog_forest_awork is:

  proj1_sig (build_forest_awork_blocks ...)

Its proof is recovered later by another proj2_sig expression.

It is not a retained AnnotatedExprWorkForest object carrying:

- the exact input work forest;
- the same work items;
- the context for each work item;
- same-file context;
- strict-ancestor context;
- nearest-first order;
- no duplicates;
- exact correspondence to the source annotation specification.

Diagnostics consume a newly computed prog_forest_awork, not the ep_awork field.

2.7 ExpressionPhase stores equal results, not a dependent causal chain

ExpressionPhase currently stores raw/list/table components plus provenance equalities:

- ep_work = prog_forest input;
- ep_ot = build_forest_outcome_table input ep_tnft;
- map ep_eft = forest_facts input ep_tnft ep_ot;
- ep_awork = prog_forest_awork input;
- ep_diags = forest_diags input ep_tnft ep_ot;
- ep_tnft = build_type_name_fact_table input.

These equalities point every field to a canonical recomputation. They do not make each field consume the exact
prior field.

In particular:

- ep_ot is not indexed by ep_work;
- ep_eft is not indexed by ep_work and ep_ot;
- ep_awork is not indexed by ep_work;
- ep_diags is not indexed by ep_awork and ep_ot;
- ep_eft_prov is only map equality, not equality of the retained ExprFactTable object to the canonical build.

The claim that a foreign component is unrepresentable is false.

2.8 ep_work is dead as an authority

The phase stores ep_work, but no production field or function reads it.

A field which is retained but not consumed is not an authority.

This is the same failure class as the earlier type-name fact table which existed beside production.

2.9 The direct cause does not retain the exact work/suffix cause

OutcomeCause retains the target ref, operand ref, prior-map lookup, and convert_const result. That is useful.

It is still indexed by raw node/occurrence pairs and a raw prior map. It does not retain:

- the exact conversion work item;
- the exact operand work item;
- proof that the operand work item is in the processed suffix;
- proof that the lookup was performed through that exact work item.

The next cause relation must be forest/work-indexed.

The source-specification bridge may remain separate.

2.10 Production fixtures can query an arbitrary constructible ExprWork

total_forest_outcome_at accepts any ExprWork input, not a membership witness for the retained forest.

Its proof finds an equal-key retained work item through prog_forest_complete.

The deep fixtures construct work through program_work_at and query by that constructed value. They do not
necessarily project the exact stored member out of ep_work.

A total phase query should consume a retained membership handle, a forest-indexed WorkRef, or another exact
member value minted from the retained forest.

Proof-term variants of the same work occurrence need not matter semantically, but the production API must make
membership in the retained work object explicit.

2.11 The scope ledger still overclaims external compiler adequacy

ADR-0001 correctly states:

  GoCompile == go build

is an external adequacy target supported by differential evidence, not a Rocq theorem.

The scope ledger still calls it an EXACT claim/property in SR-001 and SR-002.

Correct every ledger occurrence to distinguish:

- kernel-proved exactness of the formal GoCompile judgment;
- the external adequacy target against pinned cmd/go;
- differential evidence which attacks that target but does not prove it universally.

Do not change ADR-0001's status.

2.12 The current prose overstates the retained-object implementation

NEXT_STEPS, SOURCE_FOREST_STATUS, ARCHITECTURE, PROGRESS, GoCompile comments, gate comments, and the final commit
message claim one retained forest object and dependent provenance which makes foreign components
unrepresentable.

The code has one canonical forest function, not one passed proof-carrying forest object.

Correct all such prose only after the replacement is true.

===============================================================================
3. REQUIRED EXPRWORKFOREST OBJECT
===============================================================================

Create one proof-carrying object equivalent to:

  Record ExprWorkForest (input : CompilationInput p) := {
    ewf_blocks : list (list (ExprWork input));
    ewf_items  : list (ExprWork input);

    ewf_items_are_blocks :
      ewf_items = concat ewf_blocks;

    ewf_blocks_exact :
      map (map work_pair) ewf_blocks =
      map (filter occ_is_expr) (ci_blocks input);

    ewf_items_exact :
      map work_pair ewf_items =
      filter occ_is_expr (ci_visit input);

    ewf_keys_nodup :
      NoDup (map work_key ewf_items);

    ewf_forward_domain :
      every live expression occurrence in ci_visit has exactly one member;

    ewf_reverse_domain :
      every member denotes a live expression occurrence in ci_visit
  }.

The exact names and theorem organization are your choice.

Rules:

- build_expr_work_forest input constructs this object once;
- no public production function projects a raw list from a sigma and discards its proof;
- ewf_items and ewf_blocks are stored fields;
- no later builder calls build_forest_sig/build_forest_blocks/prog_forest/prog_forest_blocks again;
- specification lemmas may compare the fields to filtered source visits;
- this is a proof-backed view over the one AST, not a second AST.

Delete or demote the current raw prog_forest/prog_forest_blocks production roots.

If convenience projections remain, they must project fields from ExprWorkForest, not rebuild the forest.

===============================================================================
4. REQUIRED FOREST MEMBERSHIP AND CONVERSION VIEW
===============================================================================

Define a proof-backed retained member handle, such as:

  WorkMember forest

or use a dependent pair:

  { w : ExprWork input | In w (ewf_items forest) }.

The exact form is your choice.

Use it for total production queries.

For a conversion member, add one total conversion-work view equivalent to:

  ConversionWork forest w := {
    cw_target_ref        : TypeNameRef p;
    cw_operand_ref       : ExprRef p;
    cw_operand_work      : WorkMember forest;
    cw_target_role       : RConversionTarget;
    cw_operand_role      : RConversionOperand;
    cw_target_direct     : exact direct child;
    cw_operand_direct    : exact direct child;
    cw_target_before_op  : source order;
    cw_target_syntax     : exact TypeSyntax;
    cw_operand_expr      : exact raw operand;
    cw_operand_ref_exact : operand_work's ExprRef = cw_operand_ref
  }.

For the bottom-up fold, provide:

  operand_work_in_tail

which returns the exact operand WorkMember in the currently processed suffix.

Do not remint target or operand refs inside the semantic step.

Do not use raw operand_key as the semantic lookup key.

The raw key formula may occur only inside the theorem constructing the conversion view.

===============================================================================
5. REQUIRED OUTCOME TABLE INDEXED BY THE EXACT FOREST
===============================================================================

Replace:

  ForestOutcomeTable input tnft

with an object equivalent to:

  ForestOutcomeTable forest tnft

Its fields must name:

- ewf_items forest;
- exact outcome-map domain = retained forest members;
- direct cause indexed by retained work members;
- total query for retained WorkMember values.

The builder must have the shape:

  build_forest_outcome_table :
    forall forest tnft,
    ForestOutcomeTable forest tnft.

It must fold:

  ewf_items forest

exactly once.

For a conversion step:

1. obtain ConversionWork forest w;
2. obtain the exact operand WorkMember from the processed suffix;
3. query the suffix accumulator through that operand member/ref;
4. query tnft at the carried target ref;
5. call convert_const once;
6. insert one outcome for w.

No call to:

- prog_forest input;
- build_expr_work_forest input;
- operand_key for the live lookup;
- conversion_target_ref;
- conversion_operand_ref;
- prog_forest_operand_in_tail over a separately rebuilt forest.

may occur in the semantic step.

===============================================================================
6. REQUIRED FOREST-INDEXED DIRECT CAUSE
===============================================================================

Replace or strengthen OutcomeCause so its production form is indexed by:

- the exact forest;
- the exact conversion WorkMember;
- the exact processed suffix;
- the exact operand WorkMember;
- the exact target table;
- the exact prior accumulator.

For conversion success, carry directly:

- target fact query at cw_target_ref;
- operand outcome query at cw_operand_work;
- operand EOOk fact;
- one convert_const success;
- exact stored ExprFact.

For local failure, carry directly:

- the same target fact;
- the same operand EOOk fact;
- one convert_const rejection;
- exact EOConvFail fields.

For child failure, carry directly:

- operand outcome is EOConvFail or EOChildFail;
- exact EOChildFail.

The final table may transport a cause from the suffix accumulator to the final map through freshness, but it must
retain the exact work identities and suffix relation.

The source const_info/local_conv_failure bridge remains a separate theorem. It is not production cause.

===============================================================================
7. REQUIRED ANNOTATEDEXPRWORKFOREST OBJECT
===============================================================================

Create one proof-carrying object equivalent to:

  AnnotatedExprWorkForest forest := {
    aewf_items :
      list (WorkMember forest * list ExprRef);

    aewf_exact_members :
      each retained work member appears exactly once in forest order;

    aewf_context_sound :
      every context ref is a strict enclosing conversion;

    aewf_context_same_file;
    aewf_context_nearest_first;
    aewf_context_nodup;

    aewf_spec_exact :
      erasure corresponds to the source annotation specification
  }.

Build it once from:

- the exact forest's ewf_blocks;
- the exact forest's work members;
- the retained input/index.

Do not call build_expr_work_forest or prog_forest_blocks again.

No proj1_sig boundary may discard its proof before diagnostics consume it.

===============================================================================
8. REQUIRED FACT AND DIAGNOSTIC OBJECTS
===============================================================================

8.1 Facts

Create or retain a fact-table object indexed by the exact forest and outcome table, for example:

  ForestExprFactTable forest ot

which contains the public ExprFactTable plus proof that it is the total EOOk projection of ot over ewf_items
forest.

The phase must store this exact object.

Do not settle for:

  eft_map ep_eft = forest_facts ...

as the only provenance relation.

Either:

- index the wrapper by forest/ot; or
- store exact object equality to the builder result.

8.2 Diagnostics

Build diagnostics from:

  AnnotatedExprWorkForest forest
  ForestOutcomeTable forest tnft

The diagnostic builder must accept the exact annotated object as an argument.

It must not call prog_forest_awork/build_forest_awork again.

Store one proof-backed diagnostic projection object or store the exact list with object equality to a builder
which consumed ep_awork and ep_ot.

===============================================================================
9. REQUIRED EXPRESSIONPHASE DEPENDENT CHAIN
===============================================================================

Replace the current parallel-field/equality shape with a dependent chain equivalent to:

  Record ExpressionPhase input := {
    ep_work  : ExprWorkForest input;
    ep_tnft  : InputTypeNameFactTable input;
    ep_ot    : ForestOutcomeTable ep_work ep_tnft;
    ep_awork : AnnotatedExprWorkForest ep_work;
    ep_eft   : ForestExprFactTable ep_work ep_ot;
    ep_diag  : ExpressionDiagnostics ep_awork ep_ot
  }.

The exact order may differ.

The types must encode the causal chain.

Do not keep provenance fields whose only role is to say independently recomputed canonical values are equal.

build_expression_phase must visibly let-bind and pass each exact object:

  let work  := build_expr_work_forest input in
  let tnft  := build_type_name_fact_table input in
  let ot    := build_forest_outcome_table work tnft in
  let awork := build_annotated_work_forest work in
  let eft   := build_forest_expr_fact_table work ot in
  let diag  := build_expression_diagnostics awork ot in
  ...

No downstream builder may take only input when it semantically consumes work.

===============================================================================
10. REQUIRED ELABORATION FLOW
===============================================================================

elaborate_indexed must:

1. build one CompilationInput;
2. build one ExpressionPhase;
3. use the exact ep_tnft object for success;
4. use the exact ep_eft/public fact object for success;
5. use the exact ep_diag list for the decision/failure;
6. build package buckets from the retained input visit;
7. never rebuild the work forest, outcome table, fact table, annotation, or diagnostic projection.

The success constructors must seal exact phase objects, not new records with equal maps.

===============================================================================
11. REQUIRED LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems about the exact production functions.

11.1 Forest construction

Prove:

- build_expr_work_forest is the sole work-discovery call;
- exact forward/reverse domain;
- one member per live expression;
- NoDup keys;
- exact per-file and flat order;
- every conversion member has one exact ConversionWork view.

11.2 No reconstruction closure

Provide a reviewed call-path theorem/audit showing that functions called by:

- build_forest_outcome_table;
- build_annotated_work_forest;
- build_forest_expr_fact_table;
- build_expression_diagnostics;
- build_expression_phase

do not call:

- build_expr_work_forest;
- build_forest_sig;
- build_forest_blocks;
- prog_forest;
- prog_forest_blocks;
- conversion_target_ref/operand_ref in the semantic step;
- operand_key in the semantic lookup.

11.3 Outcome exactness

Prove:

- exact map domain iff retained WorkMember;
- total query only over retained membership;
- one insertion per member;
- conversion reads exact operand member from suffix;
- direct success/fail/child cause;
- one convert_const step per conversion member.

11.4 Annotation exactness

Prove the retained annotated forest has:

- exact same work members;
- exact order;
- sound strict-ancestor contexts;
- same-file;
- nearest-first;
- NoDup;
- source-spec equivalence.

11.5 Shared object flow

Prove from the dependent types or exact object equalities that:

- ep_ot consumed ep_work;
- ep_awork consumed ep_work;
- ep_eft consumed ep_work and ep_ot;
- ep_diag consumed ep_awork and ep_ot;
- the exact ep_tnft/ep_eft are sealed on success;
- no foreign equal-map table can be inserted into the phase.

11.6 Specification bridges

Keep separate theorems proving:

- outcome phase equals const_info/occ_expr_fact specification;
- fact map equals prog_expr_facts;
- diagnostics equal expr_diags;
- decision equals GoCompile.

These are not the sharing evidence.

===============================================================================
12. REQUIRED DIRECT FIXTURES
===============================================================================

Update the deep fixtures so they obtain retained WorkMember values from:

  ep_work phase

rather than constructing arbitrary ExprWork records through a source helper.

Prove directly:

- deep valid forest count and exact member keys;
- every conversion member in the valid chain is EOOk;
- the leaf member is EOOk;
- inner failing conversion is exact EOConvFail;
- each enclosing conversion is exact EOChildFail;
- operand cause points to the exact retained operand member;
- diagnostic list is exactly one stored reason;
- fact table is exactly the EOOk projection of the phase outcome table;
- no nonmember/wrong-kind/foreign key has an outcome.

Keep the source-spec fixtures separately and label them as specifications.

Keep the real successful two-uint8 ElaborationFacts fixture.

===============================================================================
13. SCOPE LEDGER CORRECTION
===============================================================================

Keep all entries PROPOSED unless Rob explicitly accepts them.

Keep:

- ADR-0001 PROPOSED;
- ADR-0002 REJECTED AS WRITTEN / OPEN;
- SR-009 UNRESOLVED EXISTING RESTRICTION.

Search the entire scope ledger for:

  GoCompile == go build
  EXACT
  exact property

Correct the wording so it states:

- internal GoCompile judgment soundness/completeness is kernel-proved;
- equivalence with real pinned cmd/go is an external adequacy target;
- differentials provide evidence and counterexample pressure;
- no universal cmd/go equivalence theorem is claimed.

Do not change the numeric model in this repair.

Do not mark any scope decision ACCEPTED.

===============================================================================
14. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Delete or demote the current canonical-recomputation root.

At minimum inspect and normally replace/delete from the production path:

- prog_forest_blocks as a proj1_sig raw-data authority;
- prog_forest as a rebuilt list authority;
- prog_forest_awork as a proj1_sig raw-data authority;
- build_forest_outcome_table input tnft which internally calls prog_forest;
- forest_facts input tnft ot which internally calls prog_forest;
- forest_diags input tnft ot which internally calls prog_forest_awork;
- ep_work_prov;
- ep_ot_prov in its canonical-recompute form;
- ep_eft_prov as map equality;
- ep_awork_prov;
- ep_diag_prov;
- total_forest_outcome_at over arbitrary ExprWork without retained membership;
- raw operand_key lookup in build_outcomes_forest;
- later conversion_*_ref_conv calls used to rebuild facts omitted from ConvRefinement.

Private recursive helpers may remain only inside the one forest constructor while returning their proof into the
forest object. They must not be callable production authorities.

Run full tracked-tree residue searches for:

- repeated prog_forest/prog_forest_blocks/prog_forest_awork calls in phase builders;
- proj1_sig work/annotation projection before downstream consumption;
- raw operand_key semantic lookup;
- provenance equalities to canonical recomputations;
- claims that current code makes foreign components unrepresentable;
- old conversion constructors;
- duplicate resolver/spelling tables;
- C5 uintptr/rune implementation.

===============================================================================
15. BEHAVIORAL TODO DISCIPLINE
===============================================================================

Use Claude Code's TODO list throughout this repair.

Each TODO must have these columns/fields:

- exact object produced;
- exact prior object consumed;
- production function;
- observable completion condition;
- load-bearing theorem;
- impossible branch removed;
- old path deleted;
- direct production-object fixture;
- residue search;
- status.

A TODO is not complete because a named record or theorem exists.

It is complete only when the production function consumes the exact prior object and every listed evidence item
is present.

Required top-level TODOs:

1. ExprWorkForest object retained with proofs.
2. ConversionWork view carries exact operand WorkMember and suffix proof.
3. Outcome table indexed by exact forest and target table.
4. Live operand lookup uses exact operand member/ref, not operand_key.
5. Annotated work forest indexed by exact forest.
6. Fact object indexed by exact forest/outcome table.
7. Diagnostic object consumes exact annotated forest/outcome table.
8. ExpressionPhase dependent chain has no canonical recomputation fields.
9. Elaboration seals exact phase objects.
10. Direct phase fixtures use retained members.
11. Scope ledger external-adequacy wording corrected.
12. Old roots and false prose deleted.
13. Full verification and one final freeze.

The final report must reproduce the completed table with concrete symbol/theorem/fixture/search evidence.

===============================================================================
16. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this repair.

Use this loop:

1. install authority;
2. create behavioral TODO table;
3. replace raw work projections with ExprWorkForest;
4. thread exact forest through each builder;
5. move operand work/suffix relation into conversion work;
6. replace raw operand-key lookup;
7. retain annotated forest;
8. make phase a dependent chain;
9. update direct fixtures;
10. run narrow proof checks;
11. repair failures at their root;
12. run full verification;
13. inspect complete call path, object flow, diff, TODO evidence, and residue;
14. repeat until the final freeze is clean.

Do not stop for:

- design approval;
- an intermediate green module;
- proof volume;
- a large diff;
- fear of deleting current proofs;
- a clean but incomplete commit;
- a question decided by this directive or the binding contract.

Past effort has no claim on the design.

Stop only in one of two terminal states:

A. COMPLETE

All requirements are implemented, all checks pass on the exact final freeze commit, the commit is pushed, and the
final report is ready.

B. BLOCKED

A concrete conflict outside this authority remains after direct repair attempts. Report the exact file,
definition/theorem or command, the smallest failing case, and why neither this directive nor the binding contract
decides it.

Proof volume, refactor size, or ordinary proof repair is not a blocker.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new notification service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 7 COMPLETE

or

FIDO C4 REPAIR 7 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
17. FINAL VERIFICATION
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
- exact object-flow call path:
    CompilationInput
      -> ExprWorkForest
      -> TypeNameFactTable
      -> ForestOutcomeTable
      -> AnnotatedExprWorkForest
      -> ForestExprFactTable
      -> ExpressionDiagnostics
      -> ExpressionPhase
      -> ElaborationFacts / failure report;
- evidence every arrow passes the exact prior value;
- evidence no builder closure reconstructs the forest/annotation;
- evidence the operand lookup uses the exact retained operand member/ref;
- direct cause evidence for success/failure/child failure;
- retained-member deep fixtures;
- actual-ElaborationFacts two-uint8 result;
- scope-ledger adequacy wording audit;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 1c4a7de..final;
  - 806ce87..final;
  - af2fc87..final;
  - 9d4aff5..final;
  - 3b4f40e..final;
  - 3a92d22..final.

A green command proves only what it checks. It does not replace retained-object and call-path evidence.

===============================================================================
18. FINAL FREEZE AND PUSH
===============================================================================

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 exact retained work-object repair 7 candidate complete;
   - original C4 baseline: 8c9212a;
   - all seven blocked candidates, ending at 3a92d22;
   - repair-7 baseline: 3a92d22;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-7 range: 3a92d22..this freeze commit;
   - human C4 Implementation Review pending;
   - ADR-0001 PROPOSED;
   - ADR-0002 REJECTED AS WRITTEN / OPEN;
   - automatic Codex review disabled;
   - C5 forbidden.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-exact-retained-work-object-repair-7
   result: seventh BLOCKING result repaired; new human C4 Implementation Review pending

3. Use ordinary implementation commit names during the repair.

4. Make exactly one final freeze commit after all work and verification pass:

   review(final): C4 — freeze exact retained work-object candidate

5. Run every final check, call-path audit, dependent-object audit, TODO audit, and scope-ledger audit on that exact
   commit.

6. If any check or audit fails, repair it, make a new ordinary implementation commit, then make a new final freeze
   commit. Only the last passing freeze commit is the candidate head.

7. Push main without force.

8. Notify Rob and report:

   - original C4 baseline;
   - all seven blocked candidates;
   - repair-7 authority commit;
   - final candidate SHA and all ranges;
   - exact files changed;
   - deleted canonical-recomputation root;
   - ExprWorkForest object and exact proofs;
   - ConversionWork/member/suffix relation;
   - forest-indexed OutcomeTable;
   - exact operand-member lookup;
   - retained annotated forest;
   - forest/outcome-indexed fact object;
   - diagnostics consuming exact annotation/outcome objects;
   - dependent ExpressionPhase chain;
   - exact objects sealed by elaboration;
   - direct retained-member fixtures;
   - full behavioral TODO evidence table;
   - all verification results;
   - exact gate count;
   - generated-byte identity;
   - residue/no-C5 results;
   - scope ledger wording correction;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop. Do not begin C5.
