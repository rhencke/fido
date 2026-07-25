C4 HOLISTIC IMPLEMENTATION REVIEW — BLOCKING
FCB AMENDMENT A001 + INTRINSIC RETAINED ELABORATION REPAIR 14

Repository:

rhencke/fido

Current repository head:

ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0

Current head commit:

review(campaign): persist spec-closure campaign — directive lineage v1-v12, protocols, live toolkit

C4 implementation candidate under review:

9d5246eedf9e9a3c019b85e9dc65ce9e6f867179

Candidate commit:

review(final): C4 — freeze exact standard work-index candidate

Candidate disposition:

BLOCKING — fourteenth blocked C4 implementation candidate

The additive campaign commit ece4c1 is not an implementation candidate. It changes no .v source, gate,
generated Go, Docker/shell/OCaml, or C4 checkpoint state. Repair work must be implemented on top of ece4c1
without reset, rebase, history rewrite, or force push.

Original C4 baseline:

8c9212a8c814c7a99a5e3ef1970a0ae32425a918

Binding C4 contract:

.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md

Binding C4 contract SHA-256:

9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4

Accepted C4 review basis:

.review/REVIEW_BASIS.md

Repair-13 authority SHA-256:

c9c90f053541d89952517a62cd899e6ef154ad1087f2938805bd4cf9744bc1e0

Live FCB basis consulted:

FIDO FCB v1 set, repository basis
9d5246eedf9e9a3c019b85e9dc65ce9e6f867179

Review finding classification:

NEW — the final static-capability boundary discards the exact causal compiler result.

FCB impact:

REOPENS ARCH-03 (one owner per meaning / authority chain) with new implementation and proof-topology evidence.
The amendment strengthens the public static-capability contract. It does not add a second authority or weaken any
existing guarantee.

Automatic Codex review:

DISABLED

C5:

FORBIDDEN

Post-C4 foundation consolidation / ruthless trim:

FORBIDDEN until C4 is accepted.

===============================================================================
0. REVIEW VERDICT
===============================================================================

C4 is not accepted.

Repair 13 is correct and remains intact:

- one immutable GoProgram source authority;
- one retained CompilationInput;
- one proof-carrying ExprWorkForest;
- one exact standard-map-backed ExprWorkIndex built once from ewf_items;
- no production List.find key lookup;
- exact WorkMember / SuffixMember / ConversionWork / ConversionStep identity;
- one OutcomeAccumulator and intrinsic OutcomeTrace;
- exact final-to-tail causal preservation;
- one dependent ExpressionPhase;
- facts and diagnostics projected from the same exact ForestOutcomeTable;
- exact source TypeSyntax/operand identity in the conversion-success theorem family;
- exact diagnostic field/context identity;
- one convert_const authority;
- unchanged generated Go bytes;
- no C5 implementation.

The new blocker is outside that expression phase.

elaborate_indexed constructs one exact causal chain:

  CompilationInput
    -> ExpressionPhase
      -> ExprWorkForest + ExprWorkIndex
      -> TypeNameFactTable
      -> ForestOutcomeTable + OutcomeTrace
      -> AnnotatedExprWorkForest
      -> ForestExprFactTable
      -> ExpressionDiagnostics

It then discards that chain.

On success, ElaborationFacts retains selected projections:

- the inner ExprFactTable;
- the TypeNameFactTable;
- package buckets;
- validity/preflight proofs;
- root layout;
- build plan.

It does not retain the exact CompilationInput, ExpressionPhase, work forest/index, outcome table/trace, annotated
forest, ForestExprFactTable wrapper, or ExpressionDiagnostics object that established those projections.

On failure, ElaborationFailed and CompileFailure retain only a flattened diagnostic list plus a nonempty proof.

CompilableProgram then retains:

  cp_program
  cp_index
  cp_facts
  cp_prov : elaborate cp_program = ...

The equality is in Prop, is erased, and its right-hand side contains only the already-stripped index/facts result.
It is not the exact causal object and cannot project that object.

The current "object identity" theorems expose the loss by rebuilding:

  build_compilation_input ...
  build_expression_phase ...

and proving the stored projections equal independently recomputed projections.

This is the rejected provenance pattern at the final boundary:

  build exact causal object
    -> discard it
    -> retain selected outputs
    -> rerun builders
    -> use equality as provenance

Future SafeProgram proofs and user extensions cannot consume the exact accepted C4 causal object. They must rebuild it.

No green proof/test command can repair a constructor topology that does not retain the object.

===============================================================================
1. WHY THE FCB MUST BE AMENDED BEFORE IMPLEMENTATION
===============================================================================

The live FCB correctly says:

- one owner per meaning;
- derived views cannot mint facts;
- exact phase-object identity and full CompilableProgram provenance must remain;
- internal compiler forms are built once and no consumer rediscoveries are allowed.

But Architecture Charter v1 §4 also freezes this concrete sketch:

  Record CompilableProgram := {
    cp_program;
    cp_index;
    cp_facts;
    cp_exact : elaborate cp_program = Accepted cp_index cp_facts
  }.

That sketch permits the exact failure now present in the code: copied projections plus equality to rerunning the
elaborator.

It also conflicts with the same Charter's §4.2 and §24 requirements for one built-once phase, no rediscovery, exact
phase identity, and full provenance.

This is new implementation/proof evidence under Governance §5. It requires an explicit living-FCB amendment before
Claude Code changes the public capability boundary.

The amendment does not make internal phase records public language semantics. It requires the opaque static
capability to RETAIN the exact whole compiler result behind its abstraction boundary.

"Not public" does not mean "discarded."

===============================================================================
2. TWO-PHASE AUTHORITY
===============================================================================

This file contains two phases.

PHASE A — FCB Amendment A001
  Human disposition and replacement FCB set.

PHASE B — C4 Repair 14
  Code implementation after A001 is accepted and the live FCB library set is replaced.

Claude Code MUST NOT begin Phase B until all of these are true:

1. Rob explicitly accepts FCB Amendment A001.
2. The accepted amendment artifact is committed in the repository.
3. ChatGPT has generated the coherent replacement FCB set.
4. Rob has replaced the stale FCB project-library copies with that set.
5. The replacement Index and manifest hashes have been verified.

Rob amendment disposition:

  PENDING — empty until Rob acts.

Rob countersign:

  ______________________________________

===============================================================================
PART A — FCB AMENDMENT A001
INTRINSIC STATIC CAPABILITY PROVENANCE
===============================================================================

A001 identifier:

FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE

New information:

The C4 implementation proves that a parts-plus-equality CompilableProgram can discard the exact causal compiler
object while still satisfying all local equations, proofs, gates, and generated-output checks. Equality to a rerun
does not retain data identity or causal history.

Amendment result sought:

The public CompilableProgram remains an opaque static capability. Its hidden representation MUST retain the exact
successful whole-elaboration object by construction. Public total queries are projections from that object.
Equality to rerunning elaborate is permitted only as a separate specification/determinism theorem and is never the
production provenance.

No source, type, execution, trace, scheduler, safety, or rendering authority is added.

-------------------------------------------------------------------------------
A1. AFFECTED FCB FILES
-------------------------------------------------------------------------------

Changed documents:

1. FIDO_FCB_ARCHITECTURE_CHARTER_v1.md -> v2
2. FIDO_FCB_FIXED_POINTS_v1.md -> v2
3. FIDO_FCB_GOVERNANCE_v1.md -> v2
4. FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE_v1.md -> v2
5. FIDO_FCB_ROADMAP_v1.md -> v2
6. FIDO_FCB_HUMAN_REVIEW_INDEX_v1.md -> v2
7. FIDO_FCB_INDEX_v1.md -> v2
8. FIDO_FCB_MANIFEST.sha256 -> regenerated

Unchanged canonical content:

- Closure Ledger CSV/MD rows and dispositions;
- Latitude Ledger TSV/MD rows and dispositions;
- Acceptance Gates;
- Toolchain Evidence;
- Model Operations, except its Index/manifest membership record if regeneration requires a banner/hash update.

The coherent replacement set may retain unchanged v1 files byte-for-byte. Index v2 owns the exact set identity and
must name every included file/version/hash. "Do not mix versions" means do not combine files from different Index
and manifest sets.

No closure row changes.
No latitude row changes.
No acceptance-gate row changes.
No roadmap row reassignment.
No Go-spec meaning change.
No target/toolchain policy change.

-------------------------------------------------------------------------------
A2. ARCHITECTURE CHARTER §4 REPLACEMENT
-------------------------------------------------------------------------------

Replace the concrete parts-plus-equality "permanent shape" with this public contract:

  CompilableProgram is an abstract static capability minted only by the one production elaborator.

  Its hidden representation retains, by construction, the exact successful whole-elaboration object which made the
  program admissible. That retained object includes the exact source index/input, compiler phase objects, causal
  outcome history, package facts, build layout/plan, diagnostic projection, and the success evidence over that same
  object.

  The raw constructor and internal records remain private. Internal phase/work/table forms are not public Go
  semantics, but they are not discarded. They remain the hidden provenance from which the public total queries are
  projected.

  The public interface exposes:
    source
    exact source/index references
    total compiler-fact queries
    accepted layout/build-plan queries
    exact failure/success theorem surfaces needed by later layers

  A public query never reruns elaboration, rediscovers a domain, remints a source reference, or reconstructs an equal
  phase.

  Equality between the retained result and a canonical rerun may be proved as a separate specification or
  determinism theorem. Such equality is not the capability's retained provenance and is not required to recover any
  object.

  A rejected elaboration retains its exact failed whole-elaboration object behind an opaque failure interface.
  Rejected programs cannot mint CompilableProgram, SafeProgram, or DirectoryImage.

Keep the existing exact total-query declarations and blank-identifier rules.

Amend §4.2 to state explicitly:

  Internal compiler objects do not become a second public semantics. The exact objects which justify an accepted or
  rejected result remain retained behind the opaque capability/failure boundary. Opacity restricts access; it never
  authorizes discarding and later rebuilding them.

Keep the later IndexedProgram deletion decision open unless repair 14 proves the wrapper redundant and separately
authorizes deletion.

-------------------------------------------------------------------------------
A3. FIXED POINT UPDATE
-------------------------------------------------------------------------------

Reopen and strengthen ARCH-03.

Add one component:

  fixed_point_id: ARCH-03
  component_id: static-capability-provenance
  baseline_path: FIDO_FCB_ARCHITECTURE_CHARTER_v1.md
  terminal_path: FIDO_FCB_ARCHITECTURE_CHARTER_v2.md
  selector_kind: markdown-section
  selector: ## 4. `CompilableProgram` Is the Static Capability
  protected_projection: normalized-section-text

Parent fixed-point count remains 24.
Component count changes from 41 to 42.

Update ARCH-03's summary to include:

  The static capability retains the exact whole compiler result by construction. A rerun equality is never
  provenance.

No protected component is weakened.

-------------------------------------------------------------------------------
A4. GOVERNANCE UPDATE
-------------------------------------------------------------------------------

Add settled decision D-22:

  D-22 — Opaque capabilities retain their causal objects.

  Standing law:
  When a production stage builds a proof-carrying causal object and publishes an opaque capability or failure
  result, the hidden representation retains that exact object. Selected projections plus equality to recomputation
  are insufficient provenance. Opacity controls access; it does not permit data loss.

  Rationale:
  Equality can establish extensional agreement after the object was discarded, but later proofs cannot consume the
  exact identities, predecessors, and causal history which established the result.

Record A001 in the amendment register with:

- new information: C4 final-boundary implementation fact and proof-topology obstruction;
- reopened fixed point: ARCH-03;
- no closure/latitude/acceptance row changes;
- affected contracts: SC-16, SC-21, SC-22;
- affected checkpoint: C4 acceptance boundary and C5 dependency;
- proof gates: exact retained success core, exact retained failed core, no-reconstruction query surfaces.

Reconcile ADR status:

FCB v1 records ADR-0001 as ADOPTED FOR CURRENT BASIS. The repository's ADR-0001, SR-001, NEXT_STEPS, and status
still say PROPOSED. After Rob accepts A001, update the repository current-state records to:

  ADR-0001 / SR-001: ACCEPTED FOR CURRENT BASIS
  Reopen trigger: C16 or any earlier target/uintptr request

Do not change ADR-0002 / SR-009.

-------------------------------------------------------------------------------
A5. CHECKPOINT AUTHORING GUIDE UPDATE
-------------------------------------------------------------------------------

Add a frozen-contract duty named Whole-result retention:

  If a checkpoint builds a proof-carrying object and publishes a later capability/result, the contract must name
  whether that exact object is retained, how it is indexed, and which total projections later clients receive.
  A copied field set plus equality to rerunning the builder fails this duty.

Add to implementation constraints:

  - Opaque does not mean discarded.
  - Exact whole-result provenance survives every capability boundary.
  - Specification equality never substitutes for retained identity.

Add to acceptance inspection:

  Inspect constructor topology at every publish boundary, not only the inner phase.

-------------------------------------------------------------------------------
A6. ROADMAP UPDATE
-------------------------------------------------------------------------------

Change C5 dependency from:

  Accepted C4 static capability.

to:

  Accepted C4 opaque static capability retaining the exact successful whole-elaboration object by construction,
  with total fact queries as projections and no rerun-based provenance.

Do not change C5 rows, contracts, latitude rows, acceptance gates, or ordering.

-------------------------------------------------------------------------------
A7. HUMAN REVIEW INDEX / INDEX / MANIFEST
-------------------------------------------------------------------------------

Human Review Index v2 must include while open:

  FCB-A001 — accept or reject intrinsic static-capability provenance amendment.
  Effect: C4 repair 14 and C5 remain blocked.

After Rob accepts and the replacement set is generated:

- mark A001 closed with Rob's disposition;
- leave C4-REVIEW open against the next repair-14 candidate;
- update repository basis and source snapshot hash only when a new candidate exists;
- regenerate Index v2 and manifest;
- verify every hash independently;
- replace the entire coherent project-library set in both ChatGPT and Claude projects;
- delete every stale replaced copy.

ChatGPT, not Claude Code, owns generation of the project-library FCB replacement set.

-------------------------------------------------------------------------------
A8. REPOSITORY AMENDMENT ARTIFACT
-------------------------------------------------------------------------------

After Rob accepts A001, commit:

  .review/FCB_AMENDMENT_A001_INTRINSIC_STATIC_CAPABILITY_PROVENANCE.md

It must record:

- old FCB set manifest hash;
- new FCB set manifest hash;
- Rob's exact disposition;
- new information;
- changed files and protected components;
- unchanged ledgers/gates/toolchain files;
- no semantic row reassignment;
- code checkpoint affected: C4;
- implementation authority path below.

Commit message:

  review(fcb): amend static capability to retain exact elaboration provenance

No .v source change belongs in this amendment commit.

===============================================================================
PART B — REPOSITORY CAMPAIGN TOOLKIT HYGIENE
SEPARATE REQUIRED MAINTENANCE, NOT A C4 SEMANTIC CHANGE
===============================================================================

The additive campaign commit is valid as an out-of-band documentation/tooling commit, but it tracks:

  .review/spec-closure-campaign/tools/__pycache__/audit_spec_closure_bundle.cpython-312.pyc

and treats that interpreter-specific derived bytecode as a live campaign artifact in MANIFEST.sha256 and
PROVENANCE.md.

This file is not a source producer, is tied to CPython 3.12, can become stale relative to the .py source, and should
not be a live repository tool authority.

Before using the toolkit to produce the replacement FCB set:

1. Delete the tracked .pyc and empty __pycache__ directory.
2. Add to .gitignore:
     __pycache__/
     *.pyc
3. Remove the .pyc row from campaign MANIFEST.sha256 and PROVENANCE.md.
4. Do not modify frozen directives/, protocol/, or reviews/ bytes.
5. Run from repository root:
     sha256sum -c .review/spec-closure-campaign/MANIFEST.sha256
6. Confirm no tracked .pyc or __pycache__ remains.

Commit separately:

  review(campaign): remove derived Python bytecode from live toolkit

This maintenance commit is not a C4 implementation candidate.

===============================================================================
PART C — C4 INTRINSIC RETAINED ELABORATION REPAIR 14
ACTIVATES ONLY AFTER A001 IS ACCEPTED AND LIVE FCB SET IS REPLACED
===============================================================================

Human repair authorization token:

C4-intrinsic-retained-elaboration-fcb-a001-repair-14

Implementation repository base:

The current main head after:
- ece4c1 campaign persistence;
- campaign bytecode hygiene;
- accepted FCB A001 repository artifact.

Do not reset to 9d5246. The C4 implementation candidate being repaired remains 9d5246; additive documentation/tool
commits are not implementation candidates.

-------------------------------------------------------------------------------
C1. INSTALL REPAIR AUTHORITY
-------------------------------------------------------------------------------

Write this full combined directive verbatim to:

  .review/C4_IMPLEMENTATION_REPAIR_14.md

Update:

  .review/NEXT_STEPS.md
  .review/REVIEW_REQUEST.md
  .review/SOURCE_FOREST_STATUS.md

Record:

- C4 BLOCKING at implementation candidate 9d5246e;
- current repository head and additive out-of-band commits;
- all fourteen blocked implementation candidates;
- FCB A001 accepted and live FCB v2 set installed;
- repair-14 active;
- repair-12/13 results retained;
- C5 forbidden;
- post-C4 trim forbidden;
- Codex disabled.

Correct REVIEW_REQUEST's stale repair-13 result:

  state: closed
  review: Implementation Review
  confirmation: no
  confirmation_used: no
  human_override: C4-intrinsic-retained-elaboration-fcb-a001-repair-14
  result: BLOCKING at 9d5246e; intrinsic retained elaboration repair 14 active

Commit only authority/status changes:

  review(repair): C4 — retain the exact whole elaboration object

Delete .review/C4_IMPLEMENTATION_REPAIR_13.md in the first implementation commit after its history is recorded.

-------------------------------------------------------------------------------
C2. REQUIRED WHOLE-ELABORATION OBJECT
-------------------------------------------------------------------------------

Create one exact proof-carrying whole-elaboration object.

A suitable internal shape is:

  Record ElaborationCore (p : GoProgram) (ip : IndexedProgram p) : Type := {
    ec_input : CompilationInput p;
    ec_input_ip : ci_ip ec_input = ip;        (* omit if definitional/indexed directly *)
    ec_phase : ExpressionPhase ec_input;

    ec_package_refs : PackageMap (list DeclRef);
    ec_package_present : exact domain proof;
    ec_package_len : exact bucket-length proof;
    ec_package_belongs : exact package-membership proof;

    ec_root_layout : PackageMap FreshRootEntryKind;
    ec_root_layout_ok : exact source/layout proof;

    ec_build_plan : FreshBuildDisposition;
    ec_build_plan_ok : exact plan proof;

    ec_raw_diags : list DiagnosticReason;
    ec_raw_diags_exact : exact projection from ec_phase + ec_package_refs;

    ec_diags : list DiagnosticReason;
    ec_diags_exact : exact command ordering / plan projection
  }.

Prefer indexing ElaborationCore directly by the exact CompilationInput or IndexedProgram so coherence is
definitional and foreign pairing is impossible.

Rules:

- build CompilationInput once;
- build ExpressionPhase once from that exact input;
- build package buckets once from ec_input's retained visit;
- build root layout and plan once;
- derive raw and final diagnostics from those exact stored objects;
- no copied peer table or independently rediscovered domain;
- no second AST or typed AST;
- no foreign phase/map/layout/plan/diagnostic pairing;
- no equality to a second builder as internal provenance.

Build it once:

  build_elaboration_core

-------------------------------------------------------------------------------
C3. RESULT CONSTRUCTOR TOPOLOGY
-------------------------------------------------------------------------------

Index the decision by the exact core.

Preferred:

  Inductive ElaborationDecision {p ip} (core : ElaborationCore p ip) : Type :=
  | ElaborationAccepted
      (Hnil : ec_diags core = nil)
      (Hvalid : SourceProgramValid p)
      (Hpreflight : fresh_build_preflight_ok p)
  | ElaborationRejected
      (Hne : ec_diags core <> nil).

  Record ProgramElaboration (p : GoProgram) : Type := {
    pe_indexed : IndexedProgram p;       (* delete if derivable without value *)
    pe_core : ElaborationCore p pe_indexed;
    pe_decision : ElaborationDecision pe_core
  }.

Equivalent smaller shapes are allowed.

Required:

- one exact core survives both branches;
- accepted/rejected decision is indexed by that exact core;
- success and failure cannot substitute an equal recomputed core;
- pe_input, pe_phase, pe_diags, pe_layout, pe_plan are projections;
- no separate pe_result which contains stripped copied values;
- no equality proof is needed to recover core data.

-------------------------------------------------------------------------------
C4. SUCCESS FACTS
-------------------------------------------------------------------------------

Make ProgramFacts / ElaborationFacts an opaque accepted view over the exact retained core.

It must ADD success evidence, not duplicate core data.

Public definitions should project:

  expression fact table
    := feft_table (ep_eft (ec_phase core))

  type-name fact table
    := ep_tnft (ec_phase core)

  outcome table / trace
    := ep_ot (ec_phase core)

  work forest / index
    := ep_work (ec_phase core)

  annotation / diagnostic object
    := ep_awork / ep_diag (ec_phase core)

  package refs
    := ec_package_refs core

  root layout / build plan
    := ec_root_layout / ec_build_plan core

Required:

- exact ForestExprFactTable wrapper remains retained;
- exact ForestOutcomeTable and OutcomeTrace remain retained;
- exact ExpressionDiagnostics remains retained;
- total public fact queries do not rerun any builder;
- a rejected core cannot mint accepted facts.

-------------------------------------------------------------------------------
C5. FAILURE
-------------------------------------------------------------------------------

Failure retains the exact rejected core.

Preferred:

  Record CompileFailure (p : GoProgram) : Type := {
    cfail_indexed : IndexedProgram p;      (* omit if core packages it *)
    cfail_core : ElaborationCore p cfail_indexed;
    cfail_rejected : ElaborationDecision cfail_core = ... or ec_diags core <> nil
  }.

Define:

  cfail_diags := ec_diags cfail_core

Required:

- exact failed phase/trace/work/annotation/package/layout/plan remain retained;
- direct failure-cause queries need no elaborator rerun;
- public API may keep the raw core opaque;
- opacity cannot discard the core;
- no success-facts capability on failure.

-------------------------------------------------------------------------------
C6. COMPILABLEPROGRAM
-------------------------------------------------------------------------------

Implement the amended FCB contract.

CompilableProgram must retain the exact accepted whole-elaboration object behind an opaque constructor.

Preferred internal form:

  Record CompilableProgram : Type := {
    cp_program : GoProgram;
    cp_indexed : IndexedProgram cp_program;
    cp_core : ElaborationCore cp_program cp_indexed;
    cp_accepted : accepted evidence over cp_core
  }.

Or store an exact accepted ProgramElaboration value.

Required:

- cp_index, cp_input, cp_phase, cp_work, cp_trace, cp_facts, cp_diags, cp_layout, cp_plan are projections;
- no cp_prov equality is the production provenance;
- no theorem calls elaborate cp_program to recover any field;
- constructor is sealed;
- total public query interface remains;
- the original GoProgram remains the source/render authority.

A separate theorem may state:

  canonical elaborate agrees with the retained accepted object.

Label it specification/determinism. It must not be required to obtain any retained object.

-------------------------------------------------------------------------------
C7. GO_COMPILE PASS-THROUGH
-------------------------------------------------------------------------------

go_compile must pass the exact ProgramElaboration/core through.

Required shape:

  let pe := elaborate p in
  match pe_decision pe with
  | accepted evidence =>
      CompiledOk (capability containing pe_core pe + evidence)
  | rejected evidence =>
      CompileFailed (failure containing pe_core pe + evidence)
  end

Delete the provenance argument:

  elaborate p = a

from outcome_of_elaboration.

Do not destruct a whole object, copy selected fields, and discard it.

-------------------------------------------------------------------------------
C8. SAFEPROGRAM AND OUTPUT
-------------------------------------------------------------------------------

SafeProgram continues to retain one exact CompilableProgram.

Expose theorem/query surfaces so later safety extensions consume the same:

- input/index;
- phase/work/index;
- outcome accumulator/trace;
- direct causes;
- annotated contexts;
- facts;
- package/layout/plan.

certify must retain the exact cp object.

Rendering remains direct from cp_program/sp_program and must not evaluate elaborate.

DirectoryImage layout/plan theorems use the retained cp-core projections.

-------------------------------------------------------------------------------
C9. NO-RECONSTRUCTION RULE
-------------------------------------------------------------------------------

No production provenance/query theorem over:

- ProgramFacts / ElaborationFacts;
- ProgramElaboration;
- CompilableProgram;
- CompileFailure;
- SafeProgram

may call any of:

- GoIndex.index_program;
- build_compilation_input;
- build_expression_phase;
- build_expr_work_forest;
- build_type_name_fact_table;
- build_forest_outcome_table;
- build_annotated_work_forest;
- build_forest_expr_fact_table;
- build_expression_diagnostics;
- elaborate

to recover an object not retained in that value.

Specification bridges may compare retained objects to canonical source functions. Their names/comments must say
specification, determinism, or adequacy — never provenance/object identity.

-------------------------------------------------------------------------------
C10. DELETE THE RECONSTRUCTION ROOT
-------------------------------------------------------------------------------

Delete or replace when no live consumer remains:

- copied independent ef_expr_facts / ef_type_name_facts / package/layout/plan fields;
- ProgramElaboration index+stripped-result topology;
- ElaborationFailed list-copy topology;
- CompileFailure list-only topology;
- cp_prov as provenance;
- compilable_prov equality-to-elaborate form;
- compilable_index_retained equality-to pe_indexed(elaborate ...) form;
- elaborate_ok_seals_tnfacts rebuilt-phase form;
- elaborate_ok_seals_facts rebuilt-phase form;
- elaborate_ok_seals_tnfacts_from_input rebuilt-input form;
- outcome_of_elaboration's equality parameter;
- elaboration_ok_full / elaborate_ok_whole / elaborate_failed_whole / eta scaffolding whose only purpose is
  reconstructing a discarded whole result;
- fixtures which rebuild phase/core after receiving cp/failure;
- prose/gate claims that equality to recomputation is retained identity.

Keep live source-specification theorems only with clear labels and consumers.

-------------------------------------------------------------------------------
C11. LOAD-BEARING PROOFS
-------------------------------------------------------------------------------

Gate direct theorems for:

1. Core construction
   - one exact input;
   - one exact phase;
   - one package-bucket construction from retained visit;
   - one layout/plan;
   - exact raw/final diagnostics.

2. Decision
   - accepted iff core diagnostics nil;
   - rejected iff core diagnostics nonempty;
   - success iff GoCompile;
   - failure iff not GoCompile.

3. Success retention
   - exact core/input/phase/work/index/outcome trace/annotation/fact/diagnostic/package/layout/plan projections.

4. Failure retention
   - same exact rejected core;
   - exact diagnostics projection;
   - direct conversion/package/build-output cause without rebuild.

5. Capability
   - CompilableProgram retains accepted core;
   - SafeProgram retains same cp/core;
   - foreign core/facts pairing impossible;
   - canonical-rerun equality not needed for any query.

6. Existing C4 guarantees
   - exact standard work index;
   - exact source-step identity;
   - causal success/local-failure/child-failure;
   - final-to-tail query preservation;
   - exact diagnostic/context identity;
   - trace uniqueness;
   - package/layout/plan exactness;
   - alias/render/generated bytes;
   - no C5.

-------------------------------------------------------------------------------
C12. DIRECT FIXTURES
-------------------------------------------------------------------------------

Successful deep program:

Obtain CompilableProgram from go_compile, then prove only by projections from cp:

- exact input and phase;
- exact work forest/index;
- exact outcome table/trace;
- four valid conversion causes;
- exact fact tables;
- empty diagnostics;
- exact package/layout/plan.

No build_* or elaborate call after cp is obtained.

Failed deep program:

Obtain CompileFailure from go_compile, then prove only from cfail retained core:

- exact failed phase;
- innermost EOConvFail direct cause;
- exact operand tail/final result;
- exact DRInvalidConversion and retained context;
- outer EOChildFail causes;
- exact nonempty diagnostics.

No build_* or elaborate call after failure is obtained.

Equal-value/distinct-identity:

Show the repair-13 twin-expression work index and trace through a successful cp core.

SafeProgram:

Show certify preserves identical cp/core/phase/trace by projection.

Output:

Show rendered image realizes layout/plan projected from that same cp core.

-------------------------------------------------------------------------------
C13. STATUS, GATE, AND AUDIT
-------------------------------------------------------------------------------

Update current repository docs to state:

- one intrinsic whole elaboration survives success and failure;
- CompilableProgram retains the exact accepted core behind opacity;
- CompileFailure retains exact rejected core;
- SafeProgram extends the same core;
- specification equality is not provenance;
- repair-13 work index remains;
- FCB A001 is accepted;
- ADR-0001 / SR-001 status matches the accepted FCB basis;
- ADR-0002 remains open/deferred;
- C5 and trim remain forbidden.

Fix REVIEW_REQUEST at the final freeze; it must not remain at the repair baseline.

Update collection audit only to describe the composite core's ownership. It is not a new collection and does not
copy its component maps/lists.

Readable gate comments must match public theorem types.

-------------------------------------------------------------------------------
C14. TODO DISCIPLINE
-------------------------------------------------------------------------------

Use Claude Code's TODO list.

Minimum TODOs:

T1 — accepted FCB A001 artifact and live-set hash handshake
T2 — campaign bytecode hygiene
T3 — exact ElaborationCore
T4 — build core once
T5 — decision indexed by exact core
T6 — accepted facts as core projections
T7 — rejected result retains core
T8 — CompilableProgram retains accepted core
T9 — go_compile passes exact object
T10 — SafeProgram/output retain same object
T11 — direct success fixture
T12 — direct failure fixture
T13 — delete reconstruction theorem/root
T14 — preserve all repair-12/13 guarantees
T15 — gate/docs/residue
T16 — full verification/freeze/push

Each TODO records:

- exact object produced;
- exact prior object consumed;
- constructor topology;
- retained data versus projection;
- forbidden rebuild calls;
- public theorem;
- direct fixture;
- deletion;
- gate entry;
- residue search;
- status.

A TODO is not complete because a rerun proves an equal object exists.

-------------------------------------------------------------------------------
C15. RESIDUE SEARCHES
-------------------------------------------------------------------------------

Search tracked current code/prose for:

- cp_prov;
- pe_indexed (elaborate;
- elaborate (cp_program;
- build_expression_phase (build_compilation_input in final capability/failure proofs;
- elaborate_ok_seals_;
- list-only CompileFailure;
- copied phase tables beside retained core;
- "retains whole elaboration" backed only by Prop equality;
- reconstruct/recompute claims called identity;
- production List.find work lookup;
- raw OutcomeCause / build_outcome_accumulator / FinalMemberCause;
- old conversion constructors;
- duplicate resolver/spelling authority;
- C5 uintptr/rune implementation;
- stale repair-13 REVIEW_REQUEST;
- stale ADR-0001 PROPOSED after accepted FCB disposition;
- tracked __pycache__ or .pyc.

Inspect every hit. Specification bridges and historical amendment text are allowed only when clearly labeled.

-------------------------------------------------------------------------------
C16. WORK LOOP AND NOTIFICATION
-------------------------------------------------------------------------------

Work continuously after Phase B activation:

1. install authority;
2. define core;
3. build once;
4. index decision;
5. retain accepted/rejected object;
6. thread through compile/safety/output;
7. add direct fixtures;
8. delete reconstruction root;
9. update gates/docs;
10. search residue;
11. run narrow proofs;
12. run full verification;
13. inspect exact freeze;
14. repeat until clean.

Stop only:

COMPLETE — all requirements pass on pushed final freeze.

BLOCKED — concrete unresolved conflict outside this authority, with exact file/definition/command and smallest case.

Ordinary dependent-proof work is not a blocker.

At terminal state, use the session's configured notification. If none exists, emit a terminal bell and print:

  FIDO C4 REPAIR 14 COMPLETE

or

  FIDO C4 REPAIR 14 BLOCKED

No progress notifications.

-------------------------------------------------------------------------------
C17. FINAL VERIFICATION
-------------------------------------------------------------------------------

Run on the exact freeze:

make prove
make e2e
make check
make regenerate
make regen-guard
git diff --check
staged pre-commit check

Report:

- readable gate count and axiom result;
- whole-theory audit and self-tests A–E;
- pinned-Go alias matrix;
- generated byte identity;
- exact FCB A001 manifest/hash;
- campaign manifest 38/38 or current exact count after pyc removal;
- exact core and constructor topology;
- one input and one phase construction;
- exact success and failure retention;
- CompilableProgram/SafeProgram same-core evidence;
- zero final-boundary reconstruction;
- direct success/failure fixtures;
- repair-13 index preserved and zero GoCompile List.find;
- collection audit;
- no old constructors/no C5;
- current status/range search;
- git status;
- logs for:
    8c9212a..final
    89b8e54..final
    ece4c1d..final

Green commands do not replace constructor-topology inspection.

-------------------------------------------------------------------------------
C18. FINAL FREEZE
-------------------------------------------------------------------------------

At completion:

- all fourteen blocked implementation candidates end at 9d5246e;
- ece4c1 and campaign/FCB amendment commits remain out-of-band, not candidates;
- this freeze becomes the new candidate head;
- full human C4 review range begins at 8c9212a;
- full repair range begins at 89b8e54;
- repair-14 implementation range begins at the accepted A001/current repository base;
- C4 remains pending human review;
- C5 and trim remain forbidden.

Final freeze commit:

  review(final): C4 — freeze intrinsic retained elaboration candidate

Push without force.

Then stop. Do not begin C5 or the trim.
