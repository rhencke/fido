Claude Code directive: C4 Implementation Review BLOCKING — retained phase and scope ledger repair 4

Repository:

rhencke/fido

Required clean baseline and fourth blocked C4 candidate:

af2fc87e7726a4fc68bb9480c53cf64faa83717b

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

First blocked C4 candidate:

89b8e54634e7012612a51990756ad29a579c1b0f

Second blocked C4 candidate:

1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca

Third blocked C4 candidate:

806ce87373e29b6980e5c3d9d274ffa86580449b

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-retained-phase-scope-ledger-repair-4

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

This is Rob's later explicit authorization to replace the flawed repair-3 production root and to install the
repository's first explicit unsupported/restricted-scope ledger and target decision record.

It does not replace or weaken the binding C4 contract.

Start only from the exact clean baseline above. Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at af2fc87e7726a4fc68bb9480c53cf64faa83717b.

Repair 3 made useful progress:

- one real bottom-up fold now exists;
- a conversion step reads an operand result from the processed suffix;
- TypeNameFactTable has a total table-level query;
- EOConvFail and DRInvalidConversion retain conversion, target, and operand references;
- use-context resolution comes from the already-computed ConstInfo;
- the fake EConvert leaf value was removed;
- the accepted/rejected alias differential remains complete;
- life.md no longer contains technical project claims.

Those results should remain unless the correct root requires a direct change.

The repair is still architecturally wrong.

The core defect is now exact:

- build_outcomes returns a proof-carrying sigma;
- prog_outcomes_bu immediately discards its proof and exposes only the raw map;
- production facts and diagnostics consume that raw map through partial lookups which silently skip missing data;
- the retained blocks/visit values in elaborate_indexed are ignored by the type-name table and outcome builders;
- the exact causal relation from target fact + operand outcome to invalid-conversion evidence is weakened back to
  recursive source-specification facts.

This is still "proof beside the path."

Do not wrap the current raw-map root in more equality theorems. Replace it with one retained phase object whose
proofs and total queries are the production interface.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_4.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 retained-phase and scope-ledger repair 4;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - first blocked candidate;
   - second blocked candidate;
   - third blocked candidate;
   - fourth blocked candidate and current repair baseline: the full af2fc87 SHA above;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_4.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; retained-phase repair active;
   - unsupported/restricted-scope ledger + ADR-0001 authorized as review governance work;
   - automatic Codex review: disabled;
   - C5: forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-retained-phase-scope-ledger-repair-4
   result: BLOCKING at af2fc87; retained-phase and scope-ledger repair 4 active

   Keep the original C4 contract path and hash. Do not request a review through this file.

4. Update .review/SOURCE_FOREST_STATUS.md with a concise exact record of all blocking classes in section 2.

5. Commit only these authority changes:

   review(repair): C4 — retain phase proofs and record target scope

No Rocq, Docker, e2e, gate, generated, plugin, shell, architecture, persona, or life change may enter that authority
commit.

6. After the authority commit and after NEXT_STEPS/STATUS preserve the prior repair history, delete the superseded:

   .review/C4_IMPLEMENTATION_REPAIR_3.md

in the first implementation commit. Git history is its archive.

Do not delete:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_4.md.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 The retained visit is still ignored by the semantic builders

elaborate_indexed binds:

  blocks := prog_blocks p
  visit  := concat blocks

But it then binds:

  tnft     := prog_tnft
  outcomes := prog_outcomes_c idx

prog_tnft calls:

  prog_type_name_facts p
    -> fold_right ... (prog_visit p)

prog_outcomes_c calls:

  prog_outcomes_bu idx prog_tnft
    -> build_outcomes ... (prog_visit p)

Thus the production root has at least these distinct traversal computations:

- the local blocks/visit used by buckets, facts, and annotation;
- the prog_visit hidden inside prog_tnft;
- the prog_visit hidden inside prog_outcomes_c.

The local tnft variable is not passed to the outcome builder. prog_outcomes_c names the global prog_tnft
definition again.

No CompilationInput value exists.

The comments and status claims that table/outcomes consume the retained visit are false.

Equivalent list values do not turn hidden recomputation into one retained input.

2.2 The proof-carrying accumulator is projected down to a raw map

build_outcomes returns:

  { m : NodeKeyMap ExprOutcome | outcomes_ok idx l m }

This is the right direction.

But prog_outcomes_bu is:

  proj1_sig (build_outcomes ...)

Production keeps only the raw map.

The proof is recovered later by a separate theorem which applies proj2_sig to build_outcomes again. The exact
proof object does not travel with the production value consumed by facts and diagnostics.

There is no OutcomeTable or ExpressionPhase record.

This repeats the root failure:

- a correct proof object exists;
- production throws it away;
- partial code consumes the unproved raw data;
- theorems later prove that the raw data should have been good.

The proof must remain on the path.

2.3 The expression-fact projection is fail-open

add_occ_fact_om performs a raw map lookup.

Its cases include:

- Some (EOOk f) -> add the fact;
- every other result, including a missing outcome entry -> keep the map unchanged.

A missing exact outcome is therefore indistinguishable from a real failed expression.

For a real expression work item, the outcome query must be total. Production must pattern-match the exact
ExprOutcome, not the option returned by a raw map find.

2.4 The diagnostic projection is fail-open

The production diagnostic path still contains all of these suppressions:

- GoIndex.as_expr idx r = None -> [];
- conv_failure_om missing entry -> None;
- arg_default_failure_om missing entry -> None;
- the resulting None paths emit no reason.

For a real expression occurrence, these states are impossible.

A missing ref or outcome must not become "no diagnostic."

The production diagnostic path must consume:

- an exact typed expression work item;
- the total stored outcome for that work item;
- its delivered outer context.

No optional structural lookup may decide whether a real source expression exists.

2.5 The stored invalid-conversion invariant discards the causal fact path

conv_stored_matches receives the correct ingredients:

- target type from type_name_fact_at_table tnft tr;
- operand outcome projection;
- target and operand refs;
- convert_const result.

But outcome_convfail_ev retains only:

- as_expr success;
- a recursive source local_conv_failure;
- target-ref equality;
- operand-ref equality.

It does not retain or prove:

- target = tnf_type (type_name_fact_at_table tnft tr);
- the final outcome table contains EOOk opf at operand_ref;
- operand_status = ef_const_status opf;
- convert_const target operand_status = None as the stored production rejection.

The proof reduces the production cause back to local_conv_failure and recursive const_info.

The main diagnostic soundness theorem then starts from the source specification rather than the production phase.

The exact retained table entry and exact retained operand outcome must survive in the phase invariant.

2.6 The claimed shared phase is only a conjunction of extensional equalities

facts_and_diags_share_outcomes states:

- the raw-map fact fold equals the source-spec fact map;
- expr_diags equals the source-spec diagnostic list.

It does not return or quantify over one retained phase object.

It does not prove that the exact raw map used inside one elaborate_indexed call carries the completeness proof
used by both projections.

It does not eliminate the partial lookup branches in either projection.

This is not the ExpressionPhase required by repair 3.

2.7 The typed work layer still does not exist

build_outcomes mints an ExprRef and conversion children inline while folding raw:

  NodeRef * SourceOccurrence

pairs.

That inline total minting is useful, but the resulting typed work item is not retained or shared with:

- fact projection;
- diagnostic projection;
- enclosing-context projection;
- phase exactness.

Those later paths return to raw pairs and optional as_expr/map lookups.

A single typed work view or an equivalent phase-indexed total query must be the shared structural interface.

2.8 The production proof chain reconstructs a canonical index

The proof helpers prog_visit_operand and prog_visit_type_name call:

  GoIndex.index_program p

to mint references used in the operand/target closure proofs.

The production data refs are minted through the idx passed to build_outcomes, while parts of the totality proof
reconstruct the canonical index and bridge by key equality.

Repair 3 required one exact retained index.

The retained CompilationInput and typed work layer must carry child/suffix proofs from that exact index. A
production builder's proof closure must not hide index_program p.

Specification theorems may compare against the canonical index. The live phase constructor may not reconstruct
it.

2.9 The concrete repeated-name fixture still does not query ElaborationFacts

two_uint8_distinct_target_refs is now a real two-occurrence source fixture and uses the table-level query.

But it queries:

  @prog_tnft two_uint8_program

directly.

It does not obtain the successful ElaborationFacts or CompilableProgram produced by one elaborate call and query:

  ef_type_name_facts facts

The comment calls prog_tnft "the sealed table," but it is the global builder result, not a table projected from
one retained successful elaboration.

Keep the source/ref fixture. Replace the final fact part with a query through actual retained success evidence.

2.10 The required deep nested phase fixture is absent

Repair 3 required a deep nested conversion chain whose final outcome/facts come from the one bottom-up table.

nested_use_single_resolution checks use-result placement. It does not exercise or expose one retained phase
object because no such object exists.

Add the required fixture after the phase exists. Do not claim it proves call count. The source call path and
universal fold theorem prove one convert_const call per occurrence.

2.11 Current gate and permanent prose overclaim the implementation

At least these claims are false:

- prog_outcomes_c is a "proof-carrying" accumulator, although only proj1_sig is retained;
- the type-name table and outcomes use the retained elaborate_indexed visit;
- the local tnft object is passed to outcomes;
- facts and diagnostics consume one proof-carrying phase;
- missing outcomes cannot fail open;
- elaborate_ok_seals_tnfacts proves the table was built from the local retained visit;
- two_uint8_distinct_target_refs queries a table obtained from retained ElaborationFacts.

Correct:

- .review/NEXT_STEPS.md;
- .review/SOURCE_FOREST_STATUS.md;
- ARCHITECTURE.md;
- PROGRESS.md;
- GoCompile.v comments;
- gate/axiom_gate.v comments.

Do not describe a raw map plus later theorem as proof-carrying production data.

2.12 The unsupported/restricted-scope decisions are undocumented

This is a newly authorized review requirement, not a breach of the earlier C4 contract.

The repository contains many explicit exclusions and unsupported cases, but no one reviewed ledger records:

- what kind of boundary each one is;
- why it exists;
- how it is enforced;
- what valid Go programs or environments it excludes;
- what would cause reconsideration.

The first required full decision is the 64-bit target.

"64-bit only" is not a sufficient justification.

Difficulty is not an engineering reason.

===============================================================================
3. REQUIRED RETAINED COMPILATION INPUT
===============================================================================

Build one proof-backed transient input value, equivalent to:

  CompilationInput p := {
    indexed_program;
    syntax_index;
    visit_blocks;
    visit;
    visit = concat visit_blocks;
    visit is the exact traversal of the source snapshot;
    every delivered ref belongs to this exact index/snapshot
  }

The exact names and field order are your choice.

Rules:

- elaborate builds this value once;
- every production C4 builder consumes this object or an exact projection from it;
- no production builder called by elaborate may invoke:
  - prog_blocks p;
  - prog_visit p;
  - binding_visit;
  - Snap.visit_file;
  - GoIndex.index_program p;
- proof specifications may use the canonical helpers and prove equality;
- the executable phase must consume the retained values;
- this is derived evidence over the one GoProgram, not a second AST;
- do not store it permanently unless a later public consumer needs it.

The local visit value must not be dead with respect to table and outcome construction.

===============================================================================
4. REQUIRED TYPED WORK LAYER
===============================================================================

Build one proof-backed typed work enumeration from the retained input before semantic outcome processing.

A live expression work item must carry:

- its exact NodeRef;
- its exact ExprRef;
- its exact SourceOccurrence and source GoExpr view;
- its exact role;
- its position in the retained visit.

A conversion work item must additionally carry:

- exact target TypeNameRef;
- exact operand ExprRef;
- exact direct-child and role proofs;
- target-before-operand order;
- exact source target recovery;
- exact source operand recovery;
- proof that the operand work item lies in the already-processed suffix.

The exact representation can be:

- one dependent ExprWork inductive;
- a record plus a conversion-view refinement;
- another smaller equivalent form.

It must be the structural interface shared by:

- TypeNameFact construction where relevant;
- outcome construction;
- fact projection;
- diagnostic projection.

It must not copy semantic facts or create a typed AST.

For a source occurrence whose view is Some expression, constructing its work item must be total.

===============================================================================
5. REQUIRED TYPE-NAME TABLE OBJECT
===============================================================================

Build the TypeNameFactTable from the exact retained visit/work value.

Use a builder equivalent to:

  build_type_name_fact_table :
    CompilationInput p -> TypeNameFactTable p input

or another dependent form which records exact retained-input provenance.

The total query:

  type_name_fact_at_table

must remain the only production query.

Production must receive the exact table object as an argument.

On success, ElaborationFacts must store that exact object.

Delete the production use of global prog_tnft.

A canonical source-spec prog_type_name_facts function may remain for proofs and fixtures, clearly named as a
specification. It must not be called by elaborate or any production phase constructor.

The final object-identity theorem must quantify over the table object actually constructed in the retained phase,
not merely show equality to a global helper result.

===============================================================================
6. REQUIRED PROOF-CARRYING OUTCOME TABLE
===============================================================================

Keep the proof returned by build_outcomes on the production path.

Use a record or sigma equivalent to:

  ExprOutcomeTable input tnft := {
    outcome_map;
    exact domain over typed expression work items;
    total query for every ExprRef/work item;
    exact outcome relation;
    direct conversion-cause relation
  }

Rules:

- elaborate and the expression phase retain this complete object;
- do not project to a raw map before facts and diagnostics are built;
- a total query consumes an ExprRef/work item and returns ExprOutcome, not option;
- a missing entry is eliminated by the table proof;
- each expression work item is inserted exactly once;
- conversion steps query the operand outcome through the retained operand ExprRef;
- EOChildFail arises only from a real EOConvFail/EOChildFail operand outcome;
- no missing ref/fact/outcome/kind state maps to EOChildFail.

The bottom-up builder must fold the exact retained typed work stream or exact retained visit once.

Each conversion work item reaches one syntactic convert_const call in its one fold step.

No recursive source-semantic helper may evaluate the operand.

===============================================================================
7. REQUIRED DIRECT CONVERSION EVIDENCE
===============================================================================

Strengthen the phase invariant.

For every stored EOConvFail er tr opr t ci, prove directly:

- er is the exact conversion work item's ExprRef;
- tr is its exact target TypeNameRef;
- opr is its exact operand ExprRef;
- type_name_fact_at_table tnft tr = target_fact;
- t = tnf_type target_fact;
- total_outcome_at outcomes opr = EOOk opf;
- ci = ef_const_status opf;
- convert_const t ci = None.

For every stored successful conversion, prove directly:

- the same target fact and operand fact were read;
- the stored ExprFact is built from the one convert_const success;
- ef_use_resolved is derived from that stored ConstInfo and exact role.

For EOChildFail, prove directly:

- the exact operand outcome is EOConvFail or EOChildFail.

local_conv_failure and const_info may remain in index-free specification theorems.

They must not replace the direct production-cause relation.

===============================================================================
8. REQUIRED EXPRESSION PHASE
===============================================================================

Build one transient phase object, equivalent to:

  ExpressionPhase input := {
    type_name_facts : TypeNameFactTable ...;
    outcomes        : ExprOutcomeTable ...;
    expression_facts;
    expression_diagnostics;
    facts are the total success projection of outcomes;
    diagnostics are the total failure/default projection of outcomes;
    same typed work/input provenance throughout
  }

The exact layout can differ.

The key rule is:

- one object is built;
- its table is queried;
- its outcomes are queried;
- facts project it;
- diagnostics project it;
- success seals its table/facts;
- failure returns its diagnostics.

No projection may accept a raw map and silently handle a missing entry.

===============================================================================
9. REQUIRED TOTAL FACT AND DIAGNOSTIC PROJECTIONS
===============================================================================

9.1 Facts

Replace add_occ_fact_om on the production path.

For each exact expression work item:

- query its outcome totally;
- EOOk f contributes f;
- EOConvFail/EOChildFail contributes no ExprFact;
- missing outcome is not a case.

The ExprFactTable must be constructed from this exact projection and retain its proof.

9.2 Diagnostics

Replace the production use of:

- as_expr None => [];
- conv_failure_om option;
- arg_default_failure_om option.

For each exact expression work item:

- query its exact outcome totally;
- EOConvFail emits DRInvalidConversion from the stored refs and direct evidence;
- EOChildFail emits no local reason;
- EOOk at a println use performs default-result reporting from its stored fact/use result;
- all other EOOk outcomes emit no reason.

The delivered outer context is added to the stored local failure.

No structural or outcome lookup may suppress a real reason.

Erasure remains a pure projection.

===============================================================================
10. REQUIRED LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems about the exact functions elaborate calls.

10.1 Retained input

Prove:

- one CompilationInput is built;
- its blocks and visit are the values consumed by all C4 phase builders;
- no production call closure invokes prog_visit/prog_blocks/index_program;
- all refs are minted through its exact retained index.

10.2 Typed work

Prove:

- work domain equals live expression occurrences;
- each work ref/view/role is exact;
- conversion target/operand refs are exact direct children;
- operand is in the processed suffix;
- keys are unique.

10.3 Type-name table

Prove:

- table is built from the retained input;
- total query returns the stored entry;
- wrong-kind and foreign refs cannot be supplied;
- exact table object is passed to outcome construction and later sealed;
- public query delegates to it.

10.4 Outcome table

Prove:

- total query for every expression work item;
- exact domain;
- one insertion per work item;
- operand query is total;
- no fallback exists;
- one conversion step has one convert_const call.

10.5 Direct cause

Gate the direct success/failure/child relation from section 7.

Do not gate only an equality to local_conv_failure.

10.6 Shared phase

Prove facts and diagnostics are projections of the exact retained OutcomeTable object inside one ExpressionPhase.

A conjunction of extensional equalities over a global raw map is not enough.

10.7 Sealed success

Prove ElaborationFacts stores the exact TypeNameFactTable and ExprFactTable objects projected from the phase.

10.8 Concrete fixtures

Keep and strengthen:

- nested use-result placement;
- one inner failure/no outer reason;
- deep nested conversion phase fixture;
- two-uint8 distinct refs with equal facts queried through actual retained ElaborationFacts or CompilableProgram.

10.9 Existing C4 claims

Keep or re-prove all valid alias, resolver, renderer, diagnostic, acceptance, domain, erasure, and no-C5 claims.

===============================================================================
11. UNSUPPORTED AND RESTRICTED SCOPE LEDGER
===============================================================================

Create:

  .review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md

This is a current-only reviewed ledger, not a history dump.

Every explicit "unsupported," "out of scope," "excluded," "unrepresentable frontier," or threat/build/platform
restriction in current tracked prose must have one ledger entry.

Use these classifications:

- REVIEWED TARGET RESTRICTION
- REVIEWED MODEL EXCLUSION
- REVIEWED THREAT-MODEL EXCLUSION
- REVIEWED BUILD-ENVIRONMENT RESTRICTION
- TEMPORARY FEATURE FRONTIER
- REJECTED DESIGN

Each entry must contain:

- stable ID;
- short name;
- classification;
- exact excluded case;
- exact reason;
- why difficulty alone is not the reason;
- benefit obtained;
- valid Go programs/environments lost;
- enforcement points;
- guarantees which rely on it;
- reconsideration triggers;
- linked ADR/contract/roadmap;
- approval state and date.

Rules:

- no unsupported case may exist only in a code comment;
- a temporary frontier must name the foundation or checkpoint needed to remove it;
- a target/model/threat restriction must have a reviewed rationale;
- "hard" or "not implemented" is not a permanent rationale;
- new explicit exclusions require a ledger update in the same checkpoint;
- future holistic reviews may reopen every entry.

Inventory current tracked hits in context.

At minimum classify:

- linux/amd64 and 64-bit int/uint;
- platform filesystem resource limits;
- cooperating-developer / local-verifier-tamper threat boundary;
- host Rocq/build environment;
- major-version module path forms excluded pending imports;
- source-file naming restrictions;
- unrepresented future syntax/features.

Do not turn temporary frontiers into permanent decisions.

===============================================================================
12. ADR-0001 — PINNED 64-BIT TARGET
===============================================================================

Create:

  .review/decisions/ADR-0001-PINNED-64-BIT-TARGET.md

Status during implementation:

  PROPOSED — pending Rob's review with the C4 candidate

The ADR must face the restriction directly.

It must distinguish:

1. Semantic language/constant assumption:
   - Go language version 1.23;
   - int and uint have 64-bit ranges in Ints;
   - int remains type-distinct from int64;
   - uint remains type-distinct from uint64.

2. Operational end-to-end validation target:
   - GOOS=linux;
   - GOARCH=amd64;
   - digest-pinned golang:1.23-alpine image;
   - rendered go.mod language version 1.23.

3. Claims not yet made:
   - no general ABI/layout theorem;
   - no pointer-size theorem until uintptr/pointers land;
   - no portability claim across 64-bit architectures;
   - no 32-bit claim;
   - no claim that all linux/amd64 platform resource limits are modeled.

Required decision analysis:

- Why Fido chooses one exact deployment/validation target now.
- Why this is an intended theorem-domain boundary rather than avoidance of difficult work.
- Why target-parametric int/uint semantics would add a real cross-cutting abstraction now.
- Which current definitions/proofs/tests depend on 64-bit int/uint.
- What valid Go programs or deployment targets are excluded.
- Alternatives considered:
  - 32-bit only;
  - target-parameterized semantics;
  - separate per-target theories;
  - architecture-independent subset with no int/uint boundary dependence.
- Why the chosen option is presently better.
- Exact enforcement:
  - Ints definitions/theorems;
  - Makefile sealed platform;
  - Docker GOOS/GOARCH environment and checks;
  - digest pin;
  - e2e boundary witnesses.
- Any gap between comments and actual enforcement.
- Reconsideration triggers:
  - request to support 32-bit;
  - request to support arm64 or another OS;
  - portable-Go public claim;
  - uintptr/pointer/layout work which needs a richer target model;
  - toolchain/target image change;
  - a proof benefit from a target descriptor which exceeds its cost.

Do not write "64-bit systems" when the operational target is specifically linux/amd64.

Do not call the ADR accepted until Rob accepts it.

===============================================================================
13. LIFE.MD AND PERSONA BOUNDARY
===============================================================================

life.md is now correctly character-only. Preserve its current nontechnical direction.

Correct the overbroad process rule introduced in CLAUDE.md.

The intended rule is:

- life.md is a character-continuity artifact, not technical authority;
- it contains no repository, proof, review, session, LLM, system-prompt, or fourth-wall content;
- Fido may tend it in a dedicated docs(life) commit when doing so does not obscure an active functional candidate;
- Rob may authorize a life change at any time;
- ordinary character prose is not judged as technical architecture;
- mechanically, every commit changes the repository head, so no commit of any kind may be added after a
  functional freeze without creating and reporting a new freeze head.

Do not require the same functional-contract authorization for ordinary life prose.

Do not add technical project history back into life.md.

Do not expand the persona during this repair beyond the smallest process correction.

===============================================================================
14. REQUIRED DELETION AND RESIDUE CLOSEOUT
===============================================================================

Delete or demote the rejected production root.

At minimum inspect and normally delete/replace:

- prog_outcomes_bu returning only proj1_sig;
- prog_outcomes_c as a raw map;
- prog_outcomes_bu_match/proj if replaced by retained table methods;
- add_occ_fact_om on the production path;
- conv_failure_om on the production path;
- arg_default_failure_om on the production path;
- occ_expr_diags_sm on the production path;
- facts_and_diags_share_outcomes in its current extensional form;
- outcome_convfail_ev in its current weakened form;
- local_conv_failure_om_eq_c as a load-bearing production theorem;
- global prog_tnft on the production path;
- global prog_type_name_facts on the production path;
- helpers in the live builder closure which reconstruct index_program p;
- false gate entries/comments.

Specification helpers may remain only when clearly named and genuinely used by source-spec exactness proofs.

Run full tracked-tree searches for:

- production prog_visit/prog_blocks/index_program calls;
- proj1_sig build_outcomes raw-map exposure;
- raw outcome find with skip/None/[];
- as_expr None => [] in production;
- source local_conv_failure used as the main production cause theorem;
- global prog_tnft in retained-success fixtures;
- false "proof-carrying" claims;
- old conversion constructors;
- duplicate resolver/spelling tables;
- C5 uintptr/rune implementation.

===============================================================================
15. TESTS AND DIFFERENTIALS
===============================================================================

Keep the full pinned-Go alias matrix and all valid current fixtures.

Add or strengthen:

- deep nested conversion phase fixture;
- total fact projection fixture;
- total diagnostic projection fixture;
- exact operand-ref/cause fixture;
- sealed-success two-uint8 fixture;
- retained-input call-path evidence;
- target-scope operational audit cited by ADR-0001.

Do not use counters or tests as proof of one convert_const call.

The one-step fold definition plus unique typed work domain proves it.

===============================================================================
16. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this repair.

Use this loop:

1. inspect and delete the raw-map production boundary;
2. build retained CompilationInput;
3. build typed work;
4. build retained TypeNameFactTable from the exact input;
5. build proof-carrying OutcomeTable;
6. build one ExpressionPhase;
7. make facts and diagnostics total projections;
8. strengthen direct cause proofs;
9. install the scope ledger and ADR;
10. run narrow proof checks;
11. repair failures at their root;
12. run the full required verification;
13. inspect call paths, object flow, proof statements, scope records, and residue;
14. repeat until the final freeze is clean.

Do not stop for:

- design approval;
- an intermediate green module;
- proof volume;
- a large diff;
- fear of deleting current theorems;
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

FIDO C4 REPAIR 4 COMPLETE

or

FIDO C4 REPAIR 4 BLOCKED

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
- exact elaborate -> CompilationInput -> typed work -> TypeNameFactTable -> OutcomeTable -> ExpressionPhase path;
- proof that no production builder closure calls prog_visit/prog_blocks/index_program;
- proof that the exact TypeNameFactTable object is built, queried, and sealed;
- proof that the exact OutcomeTable proof object stays on the path;
- total outcome query evidence;
- total fact and diagnostic projection evidence;
- one insert/one convert_const step per conversion work item;
- direct stored failure cause evidence;
- actual-ElaborationFacts two-uint8 result;
- unsupported/restricted-scope ledger inventory;
- ADR-0001 content and enforcement audit;
- life/persona boundary correction;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 1c4a7de..final;
  - 806ce87..final;
  - af2fc87..final.

A green command proves only what it checks. It does not replace the call-path, retained-object, or decision-record
evidence.

===============================================================================
18. FINAL FREEZE AND PUSH
===============================================================================

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 retained-phase and scope-ledger repair 4 candidate complete;
   - original C4 baseline: 8c9212a;
   - first blocked candidate: 89b8e54;
   - second blocked candidate: 1c4a7de;
   - third blocked candidate: 806ce87;
   - fourth blocked candidate / repair-4 baseline: af2fc87;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - full repair range: 89b8e54..this freeze commit;
   - repair-4 range: af2fc87..this freeze commit;
   - human C4 Implementation Review pending;
   - ADR-0001 status: PROPOSED pending Rob;
   - automatic Codex review disabled;
   - C5 forbidden.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-retained-phase-scope-ledger-repair-4
   result: fourth BLOCKING result repaired; new human C4 Implementation Review pending

3. Commit the final status and final proof-safe changes as:

   review(final): C4 — freeze retained-phase candidate

4. Run every final check, call-path audit, retained-object audit, and scope-ledger audit on that exact commit.

5. If any check or audit fails, repair it, make a new freeze commit, and repeat. Only the final passing freeze
   commit is the candidate head.

6. Push main without force.

7. Notify Rob and report:

   - original C4 baseline;
   - all four blocked candidates;
   - repair-4 authority commit;
   - final candidate SHA and all ranges;
   - exact files changed;
   - deleted raw-map/proof-beside-path root;
   - retained CompilationInput;
   - typed work model;
   - retained TypeNameFactTable;
   - proof-carrying OutcomeTable;
   - ExpressionPhase;
   - total fact and diagnostic projections;
   - direct failure cause;
   - sealed-success repeated-name fixture;
   - all verification results;
   - exact gate count;
   - generated-byte identity;
   - residue/no-C5 results;
   - unsupported/restricted-scope ledger;
   - ADR-0001 proposal;
   - life/persona boundary correction;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop. Do not begin C5.
