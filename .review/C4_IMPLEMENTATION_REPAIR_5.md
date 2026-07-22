Claude Code directive: C4 Implementation Review BLOCKING — typed-work, direct-cause, and scope-decision repair 5

Repository:

rhencke/fido

Required clean baseline and fifth blocked C4 candidate:

9d4aff5d94d9aac293ff7fb98a7d9fdd59159022

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

First blocked C4 candidate:

89b8e54634e7012612a51990756ad29a579c1b0f

Second blocked C4 candidate:

1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca

Third blocked C4 candidate:

806ce87373e29b6980e5c3d9d274ffa86580449b

Fourth blocked C4 candidate:

af2fc87e7726a4fc68bb9480c53cf64faa83717b

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Human repair authorization:

C4-typed-work-direct-cause-scope-repair-5

Review result:

BLOCKING

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

This is Rob's later explicit authorization to repair the fifth blocked C4 candidate and to correct the first
unsupported/restricted-scope ledger and ADR proposal.

It does not replace or weaken the binding C4 contract.

Start only from the exact clean baseline above. Do not rewrite or force-push history.

Do not request or run Codex review. Do not begin C5.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C4 is not accepted at 9d4aff5d94d9aac293ff7fb98a7d9fdd59159022.

Repair 4 made substantial and useful progress. Keep these results unless the correct replacement directly needs
one changed:

- one retained CompilationInput value exists;
- type-name facts are built from the retained input rather than a hidden prog_visit call;
- one proof-carrying ExprOutcomeTable value exists;
- one ExpressionPhase value exists;
- the bottom-up conversion step reads its operand from the processed suffix;
- the type-name query is total and consumes the passed table object;
- the retained index is threaded through the conversion child proofs;
- EOConvFail and DRInvalidConversion retain conversion, target, and operand references;
- use-context resolution comes from the already-computed ConstInfo;
- the prior recursive/recomputing raw-map root is deleted;
- the concrete two-uint8 fixture now reaches real successful ElaborationFacts;
- source-target diagnostics and the full byte/rune alias differential remain correct;
- no C5 implementation landed;
- life.md is character-only and its current boundary is acceptable.

The TODO-list experiment improved task coverage. It did not yet fix the definition-of-done problem. The candidate
contains most requested names and artifacts, but several named abstractions do not satisfy the required behavior:

- "typed work" is still raw occurrences plus optional as_expr;
- "exact outcome table" carries completeness but not exact domain;
- "direct cause" is reconstructed from local_conv_failure/const_info rather than carried by the phase;
- "object identity" for ExprFactTable is only map equality after a new record is built;
- "phase fixtures" call the declarative report/specification rather than the phase.

Do not preserve those claims by adding prose or wrapper theorems. Replace the weak boundaries.

===============================================================================
1. INSTALL THIS REPAIR AUTHORITY BEFORE SOURCE CHANGES
===============================================================================

1. Write this directive verbatim to:

   .review/C4_IMPLEMENTATION_REPAIR_5.md

2. Update .review/NEXT_STEPS.md to record:

   - active checkpoint: C4 typed-work/direct-cause/scope-decision repair 5;
   - binding contract path and exact hash above;
   - accepted review basis: .review/REVIEW_BASIS.md;
   - original C4 baseline;
   - first, second, third, and fourth blocked candidates;
   - fifth blocked candidate and current repair baseline: the full 9d4aff5 SHA above;
   - repair authority: .review/C4_IMPLEMENTATION_REPAIR_5.md;
   - human authorization token above;
   - state: C4 Implementation Review BLOCKING; repair 5 active;
   - ADR-0001 and every new scope-ledger disposition remain proposed pending Rob;
   - automatic Codex review: disabled;
   - C5: forbidden.

3. Keep .review/REVIEW_REQUEST.md closed. Record:

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-typed-work-direct-cause-scope-repair-5
   result: BLOCKING at 9d4aff5; typed-work/direct-cause/scope-decision repair 5 active

   Keep the original C4 contract path and hash. Do not request a review through this file.

4. Update .review/SOURCE_FOREST_STATUS.md with a concise exact record of all blocking classes in section 2.

5. Commit only these authority changes:

   review(repair): C4 — require typed work and direct phase causes

No Rocq, Docker, e2e, gate, generated, plugin, shell, architecture, persona, life, scope-ledger, or ADR change may
enter that authority commit.

6. After the authority commit and after NEXT_STEPS/STATUS preserve the prior repair history, delete the
   superseded:

   .review/C4_IMPLEMENTATION_REPAIR_4.md

in the first implementation commit. Git history is its archive.

Keep:

- .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md;
- .review/REVIEW_BASIS.md;
- .review/CODEX_REVIEW_POLICY.md;
- .review/SOURCE_FOREST_MASTER_PLAN.md;
- .review/C4_IMPLEMENTATION_REPAIR_5.md.

===============================================================================
2. BLOCKING FINDINGS
===============================================================================

2.1 No typed expression-work domain exists

The current "typed work interface" is:

  self_mem (ci_visit input)

That is the raw NodeRef * SourceOccurrence visit paired with membership proofs.

The fact projection still calls:

  GoIndex.as_expr (ci_idx input) r

and keeps the map unchanged on None.

The diagnostic projection still calls the same optional as_expr and returns [] on None.

The enclosing-context annotation also calls optional as_expr and does not push a conversion when it returns None.

The later exactness theorems prove that None corresponds to a non-expression for canonical inputs. The production
functions themselves still consume raw occurrences and optional structural conversion. The exact ExprRef,
source view, role, and conversion children are not one shared production value.

This does not meet repair 4 sections 4 and 9.

Build one exact typed work domain. Downstream facts, outcomes, diagnostics, and context annotation must consume it.

2.2 Fact projection retains a fail-open branch

add_work_fact has:

  as_expr ... r = None -> m

For a genuine expression occurrence this state is impossible, but the production function handles it as a normal
"no fact" result.

The correct fact projection takes an ExprWork item and a total outcome. It has no missing-ref or missing-outcome
case.

A proof after the function that the branch was unreachable is not the same as removing the branch from the
production interface.

2.3 Diagnostic and outer-context projection retain fail-open branches

occ_work_diags has:

  as_expr ... r = None -> []

annotate_encl has:

  as_expr ... r = None -> do not push a conversion

These branches can suppress the exact primary diagnostic or an outer conversion context if the structural
relation is absent.

For an inhabited retained CompilationInput the branches are provably unreachable on expression/conversion
occurrences. The phase should consume that proof through typed work rather than treat absence as normal output.

2.4 ExprOutcomeTable is complete but not exact-domain

ExprOutcomeTable carries:

  eot_map
  eot_ok : outcomes_ok ... eot_map

outcomes_ok proves that every visited expression occurrence has some matching entry.

It does not prove that every map entry belongs to exactly one expression work item. A map with all required
entries plus arbitrary foreign/non-expression keys satisfies the carried invariant.

The record therefore does not establish:

- exact domain;
- no extra keys;
- one entry per work item;
- wrong-kind/foreign exclusion.

Repair 4 section 6 and section 10.4 required all four.

2.5 The carried outcome invariant is still source-specification evidence

For EOConvFail, outcome_matches carries outcome_convfail_ev, which records:

- as_expr success;
- a source expression whose local_conv_failure is Some (t, ci);
- target-ref equality;
- operand-ref equality.

It does not carry the production cause:

- the exact stored TypeNameFact queried at the target ref;
- the exact operand outcome queried from the table;
- the operand ExprFact/status from that outcome;
- the exact convert_const rejection.

For EOChildFail, the invariant records only no ExprFact and local_conv_failure = None. It does not carry that the
exact operand outcome is EOConvFail or EOChildFail.

For a successful conversion, it does not carry a first-class relation tying the exact stored target fact and exact
stored operand fact to the one convert_const success.

The proof-carrying table is therefore carrying the wrong proof.

2.6 phase_convfail_cause reconstructs rather than projects the cause

phase_convfail_cause has a strong conclusion, but its proof:

- opens outcome_convfail_ev;
- calls local_conv_failure_char;
- uses recursive source const_info evidence;
- reconstructs target/operand source views;
- proves that the operand must have EOOk by contradiction against source const_info.

The theorem derives the production cause after the fact. It does not project a cause already carried in the
ExprOutcomeTable.

Its comment says it does not reduce to local_conv_failure/const_info; the proof does exactly that.

2.7 No direct success-cause or child-cause theorem exists

Repair 4 section 7 required direct evidence for all conversion outcomes:

- successful conversion;
- local conversion rejection;
- blocked by a real failed child.

Only the reconstructed failure theorem exists.

There is no equally load-bearing theorem stating from the carried phase invariant that:

- a successful conversion read this target fact and this operand EOOk fact and stored this one convert_const
  result;
- EOChildFail read this exact operand outcome and that outcome was EOConvFail or EOChildFail.

2.8 ExpressionPhase does not retain the ExprFactTable object it seals

ExpressionPhase stores only:

  ep_tnft
  ep_ot

ep_facts is a raw map computed as a function.

elaborate_indexed later constructs a fresh:

  mkExprFactTable facts ...

elaborate_ok_seals_facts proves only:

  eft_map stored_table = ep_facts phase

That is map equality. It is not ExprFactTable object identity.

The status and commit report claim the ExprFactTable is sealed by object identity. That claim is false.

Either retain the proof-backed ExprFactTable object in ExpressionPhase and store that exact object, or stop making
an object-identity claim and obtain explicit human approval for the weaker architecture. This directive requires
the exact object.

2.9 The retained TypeNameFactTable lacks input-indexed provenance

build_type_name_fact_table computes its map from ci_visit input, which is good.

But TypeNameFactTable is indexed only by p. Its proof fields are stated over prog_visit p, not the retained input.
ExpressionPhase can therefore be constructed with any TypeNameFactTable p; the type does not record that its table
came from that phase's CompilationInput.

The actual builder chooses the right table, but the permanent type-level/proof boundary does not encode retained
input provenance.

Parameterize the table by the input, or carry and use an exact retained-input provenance field. Source-level
prog_visit exactness can remain a theorem.

2.10 The deep "phase" fixtures do not query the phase

deep_nested_no_diags and deep_fail_one_diag call erased_report and rewrite erased_report_src_eq. They exercise the
declarative source report.

nested_use_single_resolution queries prog_expr_facts, the source specification.

These are valuable specification fixtures. They are not the required retained-phase fixtures.

Add fixtures which construct CompilationInput and ExpressionPhase, query ep_ot/ep_eft/ep_diags directly, and, for
successful programs, query the exact tables retained in ElaborationFacts.

2.11 CompilationInput prose says ci_visit is stored when it is derived

CompilationInput stores ci_ip and ci_blocks. ci_visit is concat ci_blocks, recomputed as a projection.

This is not a second source traversal and may be a reasonable derived-view design. But the current comments and
status call it a stored value, which is false, and repair 4 expressly required a retained visit value.

Choose one exact disposition:

- store ci_visit once with coherence to ci_blocks; or
- keep it as a derived view and record explicit human approval of that deviation because blocks are the sole
  structural authority and visit is only their derived enumeration.

Do not call a derived value stored.

For this repair, prefer storing the let-bound visit because all phase consumers use it and the prior directive
already selected that architecture.

2.12 Scope ledger is incomplete

The ledger says every material live restriction maps to exactly one entry. It omits the bounded DecimalFloat raw
literal domain:

  |coeff| < 10^40
  |exp10| <= 4096

The source comment says the limits were chosen to cover current fixtures "with margin." Pinned Go accepts much
larger literals. This is a material model exclusion and exactly the kind of bound that requires hostile review.

It must not remain only in Floats.v/ARCHITECTURE.md.

Create a separate proposed ledger entry and decision record. Do not accept or remove the bound autonomously in
this C4 repair. Present the options and evidence to Rob.

2.13 SR-006 gives a false reason for the file-name grammar

FilePath.component_ok allows only a lowercase first character and lowercase letters/digits thereafter. It rejects
ordinary compiled Go file names such as:

  foo_bar.go
  Foo.go

not only hidden files, _test.go, GOOS/GOARCH-selected files, testdata, and vendor.

SR-006 says the restriction exists to match go build file-selection logic exactly and lists only ignored/reserved
files as lost. That is false and incomplete.

Split the decision:

- build-selection exclusions which correspond to files/directories go build omits;
- the additional canonical lowercase/alphanumeric source-path subset.

For the second part, either:

- justify it in a proposed ADR with the exact valid Go files lost and why the restriction is minimal; or
- broaden FilePath to admit ordinary safe names and model build suffix selection exactly.

Do not mark it reviewed/accepted by assertion.

2.14 SR-005 does not state the full ModulePath exclusion

The ModulePath grammar excludes more than /vN and gopkg.in forms. It also requires lowercase ASCII, rejects
hyphens and many otherwise valid path characters, requires a dot in the first segment, applies a canonical dot
shape, and has other narrow segment rules.

SR-005's "valid Go lost" and rationale discuss only version suffixes and gopkg.in.

Rewrite the entry to state every material class excluded by the actual grammar. Separate Go-rejected cases from
Go-valid-but-Fido-unrepresentable cases. If retaining the canonical subset, make its rationale and
reconsideration trigger explicit and proposed.

2.15 The ledger self-approves decisions Rob has not reviewed

SR-002 through SR-008 are marked REVIEWED / ACCEPTED as of the day Claude created the ledger.

Some reflect older standing project rules, but the new ledger text, classifications, exact rationale, and scope
have not been reviewed and accepted by Rob merely because related comments existed.

A model must not certify its own trade-offs.

Use one of:

- PROPOSED — pending Rob;
- PREVIOUSLY AUTHORIZED — with an exact human authority/contract citation;
- ACCEPTED — only after Rob explicitly accepts this decision record.

2.16 ADR-0001 is defensible but not accepted as written

The core choice — one linux/amd64 Go 1.23 validation target with concrete 64-bit int/uint — is a defensible
project-domain decision.

The ADR needs these corrections before human acceptance:

- describe GoCompile == go build as the external adequacy target supported by differential evidence, not a
  kernel theorem;
- remove the claim that widening later is necessarily additive; target generalization may require replacing and
  reproving current concrete roots, though that would not make the current single-target theorems false;
- state that C5 activation automatically reopens ADR-0001 because C5 adds uintptr and therefore extends the
  target-dependent semantic surface;
- do not say the target descriptor has no imminent consumer without addressing the planned C5 uintptr work;
- keep the exact linux/amd64, image-digest, Go-language-version, and non-claims distinctions.

ADR-0001 remains PROPOSED.

2.17 Permanent prose and gate comments overclaim the implementation

Correct current claims that:

- the project has a typed work layer when it has only raw membership pairs;
- no as_expr None -> [] or skip branch exists;
- the outcome table has exact domain;
- phase_convfail_cause is projected without source re-derivation;
- ExprFactTable is sealed by object identity;
- the deep fixtures exercise ExpressionPhase;
- the scope ledger is complete;
- all ledger decisions are reviewed/accepted.

2.18 TODO completion criteria were still name-based

The TODO experiment improved coverage but allowed these substitutions:

- create a record named ExprOutcomeTable -> check off exact proof-carrying table;
- create comments named typed work -> check off typed work;
- prove a direct-looking theorem by source re-derivation -> check off direct cause;
- prove map equality -> check off object identity;
- name specification fixtures phase fixtures -> check off phase evidence.

For repair 5, TODO completion must be behavioral and evidenced as required in section 16.

===============================================================================
3. RETAINED COMPILATION INPUT
===============================================================================

Use one transient CompilationInput for the whole C4 production phase.

Preferred shape:

  Record CompilationInput p := {
    ci_ip;
    ci_idx;
    ci_blocks;
    ci_visit;
    ci_blocks_ok;
    ci_visit_blocks;
    ci_visit_source;
  }.

The exact field split can differ, but these values must be available without re-running traversal or flattening
inside each phase consumer.

Rules:

- build_compilation_input is the only production call to prog_blocks/visit_file/index_program below elaborate;
- ci_visit is the exact list every phase builder consumes;
- no builder called from build_expression_phase calls prog_blocks, prog_visit, binding_visit, Snap.visit_file, or
  index_program;
- source helper equality theorems remain specifications;
- all references are minted through ci_idx;
- no duplicate source AST or copied semantic tree is introduced.

If retaining only blocks and deriving visit is judged superior, stop and report that exact architecture conflict
for Rob rather than silently deviating again.

===============================================================================
4. EXACT TYPED WORK DOMAIN
===============================================================================

Build one proof-backed expression-work enumeration from ci_visit before semantic processing.

Use a record/inductive equivalent to:

  ExprWork input := {
    ew_node_ref;
    ew_occurrence;
    ew_expr_ref;
    ew_expr;
    ew_role;
    ew_in_visit;
    ew_occurrence_exact;
    ew_view_exact;
    ew_as_expr_exact;
    ew_erase_exact
  }.

For a conversion, provide a refinement equivalent to:

  ConversionWork input := {
    cw_expr_work;
    cw_target_syntax;
    cw_operand_syntax;
    cw_target_ref;
    cw_operand_ref;
    cw_target_direct_child;
    cw_operand_direct_child;
    cw_target_role;
    cw_operand_role;
    cw_target_before_operand;
    cw_target_source_exact;
    cw_operand_source_exact;
    cw_operand_work_in_suffix
  }.

The exact representation can be smaller, but it must provide the same production facts.

Build an exact-domain work list/table:

- every live expression occurrence has exactly one ExprWork;
- every ExprWork denotes one live expression occurrence;
- no non-expression or foreign key is present;
- work keys are unique;
- every conversion work item has exact target/operand child refs;
- every operand ExprRef has its exact work item in the processed suffix.

The one work builder may inspect a raw occurrence and decide whether it is an expression. It must return an exact
proof-backed work enumeration. After that boundary, production outcomes, facts, diagnostics, and context
annotation must not call as_expr optionally.

===============================================================================
5. INPUT-INDEXED TYPE-NAME FACT TABLE
===============================================================================

Make the retained input provenance explicit.

Preferred form:

  TypeNameFactTable input

or:

  TypeNameFactTable p with a carried proof that its exact map/domain was built from ci_visit input.

Required properties:

- exact domain over type-name work/occurrences from that input;
- total query at a TypeNameRef;
- query returns the stored map entry;
- no resolver call in the query;
- wrong-kind/foreign refs cannot be supplied;
- build_expression_phase receives this exact object;
- the exact object is retained in the phase and sealed into ElaborationFacts.

Do not use a global source builder as production data.

===============================================================================
6. DIRECT OUTCOME-CAUSE RELATION
===============================================================================

Replace outcome_matches/outcome_convfail_ev as the carried production invariant.

Define a direct relation indexed by the exact ExprWork and the exact phase inputs. One possible shape:

  OutcomeCause input work tnft prior_outcomes outcome

with cases equivalent to:

1. Leaf success

   - work is a leaf;
   - the exact literal ConstInfo is constructed once;
   - the stored ExprFact uses that status and use_resolved_of_ci of the exact role.

2. Conversion success

   - work ref/target ref/operand ref are the retained conversion refs;
   - target_fact = type_name_fact_at_table tnft target_ref;
   - total prior outcome at operand_ref = EOOk operand_fact;
   - convert_const (tnf_type target_fact) (ef_const_status operand_fact) = Some tc;
   - stored outcome is the ExprFact made from that one result and exact role.

3. Local conversion failure

   - same exact refs and target fact;
   - exact operand outcome = EOOk operand_fact;
   - convert_const target operand_status = None;
   - EOConvFail stores those exact refs, target, and operand status.

4. Child failure

   - exact operand outcome is EOConvFail ... or EOChildFail;
   - current stored outcome is EOChildFail.

The carried relation must not use these as its causal source:

- local_conv_failure;
- recursive const_info of the conversion subtree;
- conv_targets;
- a resolver call;
- a recomputed child reference.

Afterward, prove a separate exactness theorem from OutcomeCause to the index-free GoTypes/source specification.

===============================================================================
7. EXACT PROOF-CARRYING OUTCOME TABLE
===============================================================================

Strengthen ExprOutcomeTable.

It must carry:

- the outcome map;
- exact domain iff one exact ExprWork has that key;
- one stored entry per ExprWork;
- total query by ExprWork/ExprRef;
- the direct OutcomeCause for each entry;
- no extra key;
- no missing key;
- no wrong-kind/foreign key;
- unique insertion/key relation.

A table with the right required entries plus arbitrary extras must be uninhabitable.

The production builder folds once over the exact typed work order. Each conversion work item uses the total prior
operand query and contains one syntactic convert_const call.

Do not recursively evaluate the operand source expression.

===============================================================================
8. TOTAL ANNOTATED WORK AND DIAGNOSTICS
===============================================================================

Build enclosing contexts over the exact work/input stream without optional expression reminting.

An AnnotatedExprWork may contain:

- exact ExprWork;
- exact outer conversion ExprRefs, nearest-first;
- context soundness/well-formedness proofs.

When a work item is a conversion, push its already-carried ExprRef. Do not call as_expr and handle None.

Diagnostic projection consumes one AnnotatedExprWork and its total outcome:

- EOConvFail -> one DRInvalidConversion from stored refs/direct cause + outer context;
- EOChildFail -> no local reason;
- EOOk println argument -> default failure from the stored fact/use result;
- other EOOk -> no reason.

No missing ref/outcome branch exists.

Prove ordering, multiplicity, anchors, outer context, and erasure from this production projection.

===============================================================================
9. TOTAL FACT TABLE OBJECT
===============================================================================

Build an ExprFactTable object as the total success projection of the exact OutcomeTable over exact ExprWork.

The phase retains that proof-backed ExprFactTable object.

ElaborationFacts stores that exact object:

  ef_expr_facts facts = ep_eft phase

not merely:

  eft_map (ef_expr_facts facts) = ep_facts phase.

Keep the exact domain/completeness proof attached.

===============================================================================
10. ONE EXPRESSION PHASE
===============================================================================

Use a retained phase equivalent to:

  ExpressionPhase input := {
    ep_work;
    ep_annotated_work;
    ep_tnft;
    ep_ot;
    ep_eft;
    ep_diags;
    ep_direct_causes;
    ep_fact_projection;
    ep_diag_projection;
    ep_shared_provenance
  }.

The exact record can be smaller where types already imply fields.

The point is one object flow:

- input builds work;
- input builds one type-name table;
- work + table build one exact outcome table;
- outcome table builds one exact ExprFactTable;
- annotated work + outcome table build diagnostics;
- success stores the exact table objects;
- failure returns the exact diagnostics.

No production projection accepts an unproved raw map or raw occurrence pair.

===============================================================================
11. LOAD-BEARING PROOFS
===============================================================================

Gate direct theorems over the exact functions elaborate calls.

11.1 Input and work

- build_compilation_input stores the exact input values;
- exact work domain/completeness/uniqueness;
- exact conversion child refs and suffix relation;
- no optional as_expr below the work builder;
- no production traversal/index reconstruction.

11.2 Type-name table

- exact input provenance;
- exact domain;
- total query;
- exact object passed into outcome build and sealed.

11.3 Outcome table

- exact domain and no extras;
- total query;
- one entry per work item;
- direct cause for every outcome;
- one conversion fold step and one convert_const call.

11.4 Direct conversion cases

Gate one theorem for each:

- conversion success;
- conversion rejection;
- blocked by failed child.

Each theorem starts from the carried OutcomeCause/total table query. None starts from local_conv_failure or
recursive const_info.

11.5 Source-spec exactness

Separately prove the production outcome equals the declarative GoTypes result for every work item.

11.6 Facts and diagnostics

- total fact projection from the exact outcome table;
- total diagnostic projection from annotated work + exact outcome table;
- no optional structural/outcome lookup;
- exact ExprFactTable and TypeNameFactTable objects retained in ElaborationFacts;
- diagnostic direct cause, anchor, operand, source target, context, ordering, multiplicity, and erasure.

11.7 Foreign/wrong-kind exclusion

Prove for work, type facts, outcomes, and expression facts.

===============================================================================
12. REAL PHASE FIXTURES
===============================================================================

Keep the declarative fixtures, but name them specification fixtures.

Add real phase fixtures which construct:

  input := build_compilation_input ...
  phase := build_expression_phase input

and query:

- typed work enumeration;
- total_outcome_at/total outcome by work;
- ep_eft;
- ep_diags;
- retained ElaborationFacts on success.

Required fixtures:

1. Deep valid four-conversion chain
   - one work item/outcome per expression occurrence;
   - each conversion outcome successful;
   - ep_diags = [];
   - retained ExprFactTable equals ep_eft object.

2. Deep inner failure
   - innermost conversion EOConvFail;
   - each outer conversion EOChildFail;
   - exactly one ep_diags reason;
   - exact stored operand ref/cause.

3. Two uint8 names
   - one actual successful ElaborationFacts;
   - two real TypeNameRefs;
   - distinct keys;
   - equal recovered syntax;
   - equal facts through ef_type_name_facts.

4. Exact-domain negative
   - prove no foreign/non-expression key can be in the OutcomeTable or work domain.

Fixtures do not prove call count. The fold definition and universal direct-cause theorem do.

===============================================================================
13. SCOPE LEDGER REPAIR
===============================================================================

Rewrite .review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md as an honest proposed decision inventory.

Rules:

- no new entry is ACCEPTED merely because Claude wrote it;
- use PREVIOUSLY AUTHORIZED only with an exact human contract/decision citation;
- otherwise use PROPOSED — pending Rob;
- a broad "all future syntax" entry does not replace a separate entry for a material independent restriction;
- each entry states every material valid program/environment lost;
- each rationale distinguishes Go/cmd-go rejection from Fido-only narrowing;
- every magic cap receives its own entry;
- every future review may reopen every decision.

13.1 Decimal literal box

Add a proposed entry for:

  |coeff| < 10^40
  |exp10| <= 4096

Create a proposed ADR using the next available number, with:

- exact source forms lost;
- why current fixture coverage is not a sufficient reason;
- the actual proof/computation/external-toolchain need for a bound;
- alternatives:
  - unbounded canonical decimal syntax;
  - target/toolchain implementation minimum bound;
  - a larger experimentally pinned operational box;
  - retain current box as a deliberate language subset;
- guarantees enabled;
- enforcement;
- experiments;
- reconsideration triggers.

Do not change the numeric model in this repair without Rob's separate decision.

13.2 File paths

Split:

- cmd/go selection exclusions: leading dot/underscore directories/files, _test.go, GOOS/GOARCH/build-tag
  selection if represented, testdata/vendor behavior;
- Fido's extra canonical lowercase/alphanumeric restriction.

State that ordinary names such as foo_bar.go and Foo.go are valid Go source names but currently unrepresentable.

If retaining the extra restriction, create a proposed ADR. Explain why it is minimal. "Matches go build" is not
an acceptable reason for restrictions go build does not impose.

Do not broaden FilePath during this C4 repair without Rob's separate decision.

13.3 Module paths

Rewrite SR-005 to enumerate the actual grammar:

- lowercase-only;
- allowed characters and no hyphen;
- first-segment dot requirement;
- dot shape;
- reserved device names;
- /vN-family exclusion;
- gopkg.in exclusion;
- every other Go-valid-but-Fido-unrepresentable class found by the audit.

Separate Go-invalid cases from deliberate Fido narrowing. If retaining the canonical subset, create or link a
proposed decision record.

13.4 Status audit

Change all unsupported/restricted entries to PROPOSED unless an exact prior human authority is cited.

Do not call the ledger "reviewed" until Rob accepts each disposition or the ledger clearly distinguishes proposed
from accepted.

===============================================================================
14. ADR-0001 REPAIR
===============================================================================

Keep ADR-0001 PROPOSED.

Amend it:

- external Go adequacy is a target backed by pinned differential evidence, not a Rocq theorem;
- target generalization may require replacing/refactoring and reproving current concrete roots; it is not
  guaranteed additive;
- C5 activation automatically reopens ADR-0001 before uintptr is implemented;
- C5 must decide whether uintptr is pinned to 64 under linux/amd64 or whether a target descriptor lands first;
- remove or qualify "no current consumer" in light of the planned C5 uintptr work;
- preserve exact Go 1.23, linux/amd64, image-digest, int/uint identity/range, non-claims, alternatives,
  enforcement, losses, and reconsideration triggers.

Do not set status ACCEPTED. Rob decides after review.

===============================================================================
15. PROSE, GATE, AND RESIDUE CLOSEOUT
===============================================================================

Correct:

- .review/NEXT_STEPS.md;
- .review/REVIEW_REQUEST.md;
- .review/SOURCE_FOREST_STATUS.md;
- ARCHITECTURE.md;
- PROGRESS.md;
- GoCompile.v comments;
- gate/axiom_gate.v comments;
- ledger and ADR prose.

Delete or replace weak surfaces, including as applicable:

- self_mem as the claimed typed work layer;
- add_work_fact on the production path;
- occ_work_diags on the production path;
- optional as_expr use in production annotation;
- outcomes_ok if replaced by exact OutcomeCause/domain evidence;
- outcome_convfail_ev/local_conv_failure-based carried invariant;
- phase_convfail_cause in its reconstructed form;
- facts_and_diags_share_phase if it remains only extensional equalities;
- map-only elaborate_ok_seals_facts;
- specification fixtures mislabeled as phase fixtures;
- false exact-scope ledger statements.

Specification helpers may remain with exact names/comments and no production use.

Search the full tracked tree for:

- production as_expr None -> []/skip;
- raw occurrence pairs sold as typed work;
- OutcomeTable claims without exact domain;
- local_conv_failure/const_info in carried production cause;
- map equality called object identity;
- spec report called phase fixture;
- unsupported restrictions absent from the ledger;
- self-approved decision states;
- old conversion constructors;
- duplicate resolver/spelling tables;
- C5 implementation.

===============================================================================
16. TODO DISCIPLINE FOR THIS EXPERIMENT
===============================================================================

Use the Claude Code TODO list throughout this repair.

Create one TODO per observable requirement, not per requested symbol.

Each TODO must contain:

- production function/object which must change;
- exact behavioral completion condition;
- direct theorem/evidence required;
- impossible branch which must disappear;
- old symbol/path which must be deleted;
- fixture or residue search required;
- final report evidence location.

Bad TODO:

  Add ExprWork.

Good TODO:

  Facts and diagnostics iterate one exact ExprWork domain; below the work builder neither call as_expr or handle
  a missing ExprRef; gate exact work domain/completeness and show old raw-occurrence projections absent.

Do not mark a TODO complete because:

- a record or theorem has the requested name;
- a comment says the property;
- a source-spec equality exists;
- a green build passes;
- a fixture exercises a peer path;
- the old path became dead but was not deleted.

Before final freeze, reproduce the entire completed TODO list in the final report with:

- exact file/symbol;
- exact theorem;
- exact negative branch/residue result;
- exact verification result.

This TODO discipline is experimental for repair 5. Do not make it permanent CLAUDE.md law yet. Rob and the next
human review will decide based on results.

===============================================================================
17. WORK LOOP AND USER NOTIFICATION
===============================================================================

Work continuously through this repair.

Use this loop:

1. install authority and behavioral TODOs;
2. remove the raw-occurrence production projection boundary;
3. build exact typed work;
4. strengthen retained input/table provenance;
5. replace the source-spec carried invariant with direct OutcomeCause;
6. strengthen exact OutcomeTable domain/totality;
7. build total annotated work, fact table, and diagnostics;
8. seal the exact fact objects;
9. add true phase fixtures;
10. repair the scope ledger and proposed ADRs;
11. run narrow proof checks;
12. inspect each TODO against its behavioral condition;
13. run full verification;
14. inspect call paths, proof dependencies, decision records, and residue;
15. repeat until the final freeze is clean.

Do not stop for:

- design approval already decided here;
- an intermediate green file;
- proof volume;
- a large diff;
- fear of deleting current theorems;
- a clean but incomplete commit;
- completion of names without behavior;
- a question answered by this directive or the binding contract.

Past effort has no claim on the design.

Stop only in one of two terminal states:

A. COMPLETE

All implementation requirements are complete, all proposed decision records are written honestly, every check
passes on the exact final freeze, the commit is pushed, and the final evidence report is ready.

B. BLOCKED

A concrete architecture conflict or human decision which this directive does not authorize remains after direct
repair attempts. Report the exact file/symbol/decision, smallest case, attempted options, and why it cannot be
resolved without Rob.

Proof volume, refactor size, or ordinary proof repair is not a blocker.

At either terminal state, send Rob one notification through the notification method already configured for this
Claude Code session. Do not install or configure a new service.

If no configured notification method is available, emit a terminal bell and print exactly one of:

FIDO C4 REPAIR 5 COMPLETE

or

FIDO C4 REPAIR 5 BLOCKED

Then give the final report. Do not send progress notifications.

===============================================================================
18. FINAL VERIFICATION
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

- exact readable assumption-gate count/result;
- whole-theory audit and self-tests A-E;
- full pinned-Go alias matrix;
- generated go.mod and recursive .go byte identity;
- exact retained-input -> typed-work -> input-indexed TypeNameFactTable -> exact OutcomeTable -> ExprFactTable ->
  annotated diagnostics -> ExpressionPhase -> elaborate call path;
- no production traversal/index reconstruction;
- exact work domain and no optional as_expr below the builder;
- exact outcome domain/no extras;
- direct success/failure/child causes carried by the table;
- total fact/diagnostic projections;
- exact ExprFactTable and TypeNameFactTable object retention;
- real phase deep fixtures;
- actual-ElaborationFacts repeated-name fixture;
- scope-ledger completeness search;
- DecimalFloat bound decision proposal;
- FilePath restriction decision proposal/correction;
- ModulePath restriction correction;
- ADR-0001 amendment;
- all decision approval states;
- old-root/no-C5/duplicate-authority residue searches;
- complete TODO evidence table;
- git status --short;
- git log --oneline for:
  - 8c9212a..final;
  - 89b8e54..final;
  - 1c4a7de..final;
  - 806ce87..final;
  - af2fc87..final;
  - 9d4aff5..final.

A green command does not replace call-path, proof-cause, exact-domain, or decision-quality evidence.

===============================================================================
19. FINAL FREEZE AND PUSH
===============================================================================

After implementation commits pass:

1. Update NEXT_STEPS and SOURCE_FOREST_STATUS to state:

   - C4 typed-work/direct-cause/scope-decision repair 5 candidate complete;
   - original C4 baseline: 8c9212a;
   - blocked candidates: 89b8e54, 1c4a7de, 806ce87, af2fc87, 9d4aff5;
   - repair-5 baseline: 9d4aff5;
   - this freeze commit is the new candidate head;
   - full human review range: 8c9212a..this freeze commit;
   - repair-5 range: 9d4aff5..this freeze commit;
   - human C4 Implementation Review pending;
   - every new ADR/ledger decision is PROPOSED pending Rob unless exact prior authority is cited;
   - automatic Codex review disabled;
   - C5 forbidden.

2. Keep REVIEW_REQUEST closed. Set:

   human_override: C4-typed-work-direct-cause-scope-repair-5
   result: fifth BLOCKING result repaired; new human C4 Implementation Review pending

3. Commit final status and proof-safe changes as:

   review(final): C4 — freeze typed-work direct-cause candidate

4. Run every final check and audit on that exact commit.

5. If any check, TODO condition, call-path audit, direct-cause audit, exact-domain audit, scope audit, or residue
   search fails, repair it, make a new freeze commit, and repeat. Only the final passing freeze is the candidate.

6. Push main without force.

7. Notify Rob and report:

   - all baselines and blocked candidates;
   - repair-5 authority commit;
   - final SHA/ranges;
   - exact files changed;
   - deleted weak boundaries;
   - retained CompilationInput;
   - exact typed work;
   - input-indexed TypeNameFactTable;
   - exact-domain ExprOutcomeTable;
   - carried direct outcome causes;
   - exact ExprFactTable;
   - total annotated diagnostics;
   - real phase fixtures;
   - scope-ledger and proposed ADR changes;
   - ADR-0001 status;
   - complete TODO evidence table;
   - all verification/gate/generated/residue results;
   - state: awaiting Rob's human C4 Implementation Review.

Then stop. Do not begin C5.
