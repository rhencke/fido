Claude Code directive: C3 manual closeout, overarchitecture correction, and permanent Codex review reform

Repository:
  rhencke/fido

Frozen snapshot audited by Rob/ChatGPT:
  de6bd759d8fe1977bc196b5aaed04aa60b9560b1

C3 baseline retained:
  fea649389ee52d442373c43ea2bdb3be2eca47db

Binding functional contract:
  .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md
  .review/NEXT_STEPS.md

THIS IS THE ACTIVE C3 CLOSEOUT DIRECTIVE.

It does not restart C3 and does not authorize C4.

Its purposes are:

1. replace the serial stop-hook review process with one holistic Contract Review and one holistic Implementation
   Review;
2. close the material C3 holes found by a manual whole-snapshot audit;
3. delete or simplify machinery that grew around serial Codex findings instead of the right root abstractions;
4. run one complete C3 Implementation Review after the full repair, with at most one bounded confirmation.

Before implementation, copy the supplied files into the repository:

  CODEX_REVIEW_POLICY.replacement.md
    -> .review/CODEX_REVIEW_POLICY.md

  REVIEW_REQUEST.template.md
    -> .review/REVIEW_REQUEST.md

  REVIEW_BASIS.template.md
    -> retain as .review/REVIEW_BASIS_TEMPLATE.md or delete after installing the accepted C3 basis

  C3_REVIEW_BASIS.manual.md
    -> .review/REVIEW_BASIS.md

  MANUAL_C3_AUDIT.md
    -> .review/C3_MANUAL_CLOSEOUT_AUDIT.md

Install the supplied stop-hook prompt in the Codex plugin configuration:

  codex-review-gate.replacement.prompt.md

That prompt is operational configuration, not required to be a certified source file. If the repository tracks
plugin prompts, store the exact text in the existing appropriate location. Do not create a second competing
prompt.

Add a short amendment banner near the top of the active C3 contract and NEXT_STEPS:

  REVIEW-PROCESS AMENDMENT:
  Contract Review and Implementation Review are governed by .review/CODEX_REVIEW_POLICY.md.
  The older checkpoint-specific Codex cadence and attack-list wording below is historical steering and does not
  override the permanent review policy or .review/REVIEW_BASIS.md.

Do not rewrite the 2,000-line functional contract merely to change review procedure.

Update .review/SOURCE_FOREST_STATUS.md to record:

- this manual closeout directive;
- the snapshot SHA above;
- the installed permanent review policy;
- C3's manually accepted review basis;
- the material defects and simplifications below;
- C4 remains forbidden;
- the next substantive Codex barrier is one Implementation Review after all work below is complete.

Commit the policy/basis/directive activation before functional changes:

  review(contract): install holistic Contract and Implementation Review process + activate C3 manual closeout

Then work through this entire directive without requesting Codex after each edit.

Ordinary turns leave:

  .review/REVIEW_REQUEST.md

with:

  state: closed

The stop hook must therefore return immediately rather than running a full review.

===============================================================================
1. PERMANENT REVIEW PROCESS
===============================================================================

The permanent process has exactly two review types:

  Contract Review
  Implementation Review

A confirmation is a bounded continuation, not a third review type.

Contract Review:

- happens after a checkpoint contract is committed and before implementation;
- reviews the full contract, claim surface, required evidence, root abstractions, scope, ambiguities, and
  overreach risks;
- continues after every blocker and returns every independently visible contract defect in one finding set;
- produces a compact accepted .review/REVIEW_BASIS.md;
- does not prescribe line-by-line implementation.

Implementation Review:

- happens only after the full checkpoint implementation is complete and a candidate range is frozen;
- reviews the full checkpoint range against correctness, the latest contract, the accepted basis, and permanent
  architecture/trust rules;
- checks underimplementation and overimplementation;
- independently checks for missing roots, competing authorities, repeated work, fail-open paths, weak/vacuous
  proofs, production/test mismatch, stale residue, and unapproved scope;
- continues after every blocker and returns every independently visible defect in one finding set;
- reports the full blast radius of each root cause, not one occurrence per review round.

When a review blocks:

- repair the complete finding set as one batch;
- run one bounded confirmation;
- classify a newly found item as repair-induced, previously observable and missed, contract ambiguity, new
  repair scope, or outside scope.

Do not lower review strictness. Reduce review cost through completeness.

The current C3 exception:

- implementation already exists;
- Rob requested and accepted the manual audit supplied with this directive;
- .review/REVIEW_BASIS.md is therefore the accepted C3 basis;
- do not run a retroactive open-ended Contract Review for C3;
- after this directive is complete, run one Implementation Review.

===============================================================================
2. RETAIN THE CORRECT C3 FOUNDATIONS
===============================================================================

Do not reopen or replace these roots:

- one raw specification-shaped GoAST;
- standard FilePath-keyed GoFileMap;
- structural, semantic-free GoIndex;
- IndexedProgram with one snapshot-local index;
- NodeKey / FileRef / NodeRef / typed reference identity;
- exact occurrence correspondence and navigation;
- GoTypes as the type and exact-constant authority;
- GoCompile as the sole GoIndex + GoTypes meeting layer;
- standard NodeKey expression fact map;
- standard PackageMap duplicate-preserving main-ref buckets;
- exact snapshot-local diagnostics and erased reports;
- innermost conversion failure primary;
- strict canonical NodeKey diagnostic order;
- factored package declaration uniqueness and main-entry meaning;
- fresh-image literal one-shot go build plan;
- command-output directory precedence;
- retained ElaborationFacts and CompilableProgram provenance;
- immutable authoritative DirectoryImage;
- disposable fresh build root and original-image publication;
- no C4 work.

This closeout is not permission for broad module splitting. Physical decomposition remains C6 work.

===============================================================================
3. FIX THE SECOND SOURCE TRAVERSAL
===============================================================================

Current defect:

  elaborate_indexed let-binds blocks and visit,
  but computes buckets through prog_package_refs idx,
  which recomputes prog_visit p and therefore prog_blocks/visit_file.

Required root:

  Definition prog_package_refs_from_visit idx visit :=
    fold_right (ppkg_step idx) ... visit.

  Definition prog_package_refs idx :=
    prog_package_refs_from_visit idx (prog_visit p).

Use:

  prog_package_refs_from_visit idx visit

inside elaborate_indexed.

Prove once that the canonical convenience form equals the retained-input form on prog_visit. Reuse or transport
all current package-bucket exactness, ordering, membership, diagnostic, and fact theorems.

Audit the complete production path for:

- prog_blocks;
- prog_visit;
- binding_visit;
- Snap.visit_file;
- annotate_program;
- prog_status_map;
- prog_expr_facts;
- package bucket construction.

Final executable claim:

- one prog_blocks p evaluation per elaborate p;
- one Snap.visit_file per represented file;
- every downstream fold consumes the retained blocks or visit;
- no helper hides a second traversal.

Correct every comment, doc, gate note, and performance statement based on this claim.

Do not add memoization, mutable cache, or another retained tree.

===============================================================================
4. MAKE THE FRESH-BUILD RUNNER FAIL CLOSED
===============================================================================

Current defect:

- find errors are suppressed in command substitutions;
- find | while pipelines can hide producer failure;
- the runner can return success after omitting source files.

Replace the runner's observation/copy logic with a checked manifest flow.

Required operation:

1. Accept one authoritative pristine image export.
2. Create a source manifest in a temporary file.
3. Fail if source enumeration fails.
4. Validate every manifest entry against the runner's honest input contract.
5. Create a fresh empty root.
6. Copy every manifest entry with checked mkdir/install operations.
7. Create a fresh-root manifest and fail if enumeration fails.
8. Compare exact relative path sets.
9. Compare every file byte-for-byte.
10. Only then run literal pinned `go build ./...` exactly once.
11. Return the command status and disposable root for the caller's fixture checks.
12. Never copy a post-build byte back.

Use temporary manifest files rather than pipelines whose producer status can disappear.

Do not hide filesystem observation errors. An error is not an empty result.

Keep the runner's accepted input claim narrow and true.

Preferred boundary:

- the caller supplies an authoritative pristine DirectoryImage export;
- the export manifest is exact;
- the runner verifies that exact manifest and materialization;
- the runner does not reimplement the full Fido FilePath grammar in shell.

If the runner also claims to reject arbitrary extras such as .fido, VCS trees, nested modules, or special files,
prove those checks from the manifest logic and cover them. Otherwise remove the broader claim and document that
the runner accepts only certified pristine exports.

Required regressions:

- source enumeration failure;
- fresh enumeration failure;
- copy failure;
- mkdir failure;
- byte mismatch;
- missing source file;
- extra fresh file;
- symlink/special input where the accepted manifest excludes it;
- success with exact image;
- literal Go success/failure remains the returned command class.

All failure cases must occur before Go or return a distinct loud runner failure.

===============================================================================
5. CLOSE THE PUBLICATION-BEFORE-VALIDATION GAP
===============================================================================

Binding product invariant:

  proved DirectoryImage
    -> exact pristine export
    -> fresh literal build validation
    -> sink the original pristine image

Current public `Fido Emit <image> To <root>` decodes and calls Fido_sink.sync directly. Current docs call it the
one general publication command. The canonical sync image is gated later, but the public command is not.

Required outcome:

- no supported or documented public publication path can sink before fresh validation;
- a failed fresh build prevents sink effects;
- successful publication always sinks the original pristine image, never the post-build root;
- every witness and future DirectoryImage uses the same validated publication workflow.

Allowed minimal factoring:

A. Keep the Rocq command as a low-level exact export/transport primitive, rename or document it as internal to
   the validated workflow, and provide one public orchestration wrapper that validates then sinks.

or

B. Replace the public command with a validated orchestration command outside the certified semantic layer,
   while retaining the existing provenance decoder as an internal step.

Do not:

- put Go language semantics in handwritten OCaml;
- invoke Go inside the Rocq proof kernel;
- build in the sink destination;
- make the sink inspect the AST;
- publish post-build bytes;
- create witness-specific publication paths.

Update:

- Makefile targets;
- Docker stages;
- README and architecture docs;
- CLAUDE instructions;
- witness comments;
- plugin comments and command naming where needed.

The real deployed path and the tested path must be the same path.

===============================================================================
6. REMOVE THE OLD SOURCE SEMANTIC AUTHORITY
===============================================================================

Make these the only live source semantic roots:

  PackageDeclsUnique
  MainPackagesHaveEntry
  PackageRulesValid
  SourceProgramValid

Keep the current-fragment theorem:

  PackageRulesValid p
    <->
  every current represented package has exactly one DMain

That theorem explains today's equivalence. It is not a second semantic authority.

Delete or confine:

- AllPackagesOneMain as a public root;
- old ProgValid as a public root;
- old prog_ok package decision as a peer authority;
- old reflection/gate/doc chains that present them as current semantics.

Any retained specification helper must have a name and visibility that cannot be mistaken for production or the
permanent source judgment.

Define source-program reflection directly against SourceProgramValid.

Delete after final call-site audit:

- elaborate_valid_of_no_diags, which returns old ProgValid and is unused;
- generic result;
- bool_sumbool;
- any dead compatibility alias introduced during analysis-to-elaboration migration.

Update all theorem names and gate surfaces to the new authority. Do not preserve stale names merely to avoid
editing callers inside the same repository.

===============================================================================
7. REPLACE STRING-PROOF VOLUME WITH THE MISSING COMPONENT ROOT
===============================================================================

The current executable-name proof grew by 571 lines between the preceding and current snapshot. It introduces a
parallel character-level canonicality system for slash starts, slash ends, double slashes, append behavior,
basename, dirname, split/join, and nonemptiness.

The cmd/go rule is component-based.

Build one canonical proof view from existing intrinsic data:

- ModulePath components;
- package directory/FilePath parent components;
- nonempty slash-free component facts already implied by those intrinsic types.

Then define or characterize:

- package import components;
- final component;
- previous component;
- is_version_element;
- default executable component;
- one bridge to the canonical import-path string.

Requirements:

- one authority, not a new parallel path representation;
- exact current cmd/go fixtures remain;
- universal default executable nonempty theorem remains;
- package_import_path string remains exact;
- ModuleSpec remains an input;
- v0/v1/v2/v10 behavior remains exact;
- delete the redundant str_starts_slash / str_ends_slash / str_no_double_slash proof ecosystem and related
  append/tail machinery once no public theorem needs it;
- the refactor deletes substantially more proof code than it adds.

Prefer a small proof-only component view or existing split functions over a speculative public datatype.

This is the required root-abstraction repair. Do not answer by adding more local string lemmas.

===============================================================================
8. REDUCE THE READABLE GATE TO THE REAL CLAIM SURFACE
===============================================================================

Retain the whole-certified-theory assumption closure audit exactly.

Retain concrete examples and differential tests as compiled tests.

Refocus gate/axiom_gate.v on load-bearing public claims:

- semantic roots and reflections;
- occurrence/source exactness;
- universal fact and diagnostic exactness;
- command-plan exactness;
- capability provenance;
- trust and output bridges;
- universal ordering and determinism;
- external-facing safety/rendering claims.

Remove Print Assumptions entries for:

- concrete fixture-only examples;
- internal helper lemmas;
- superseded weaker statements;
- old exactly-one/analysis authorities;
- local proof scaffolding whose only purpose is a retained public theorem.

The gate count may fall substantially. This is expected.

The final build still asserts:

- every declared readable surface closes;
- whole-theory audit has zero assumptions;
- certified-module coverage is exact;
- adversarial audit self-tests remain green.

Do not add a regex architecture gate.

===============================================================================
9. SHARE BUILDERS OVER EXPLICIT RETAINED INPUTS
===============================================================================

Where readable specification functions and production retained-input functions duplicate the same executable
logic, factor one shared builder.

Required targets:

- package refs over an explicit visit stream;
- fresh build plan over module, package keys, and root layout;
- command-facing diagnostics over an explicit retained plan.

Canonical convenience definitions apply the shared builder to canonical inputs.

Production elaboration applies the same builder to already-retained inputs.

Prove the bridge once.

Keep specification readability and theorem statements. Delete peer executable logic that can drift.

Do not collapse semantically distinct layers merely to reduce line count.

===============================================================================
10. RECONCILE PERMANENT DOCUMENTATION AND STATUS
===============================================================================

Rewrite permanent headers to describe current responsibility, not checkpoint progress.

At minimum:

- remove GoIndex's “C2 in progress” block;
- rewrite GoCompile's header around SourceProgramValid + fresh command preflight + elaborate;
- update Dockerfile's top pipeline comment;
- update dune synopsis;
- update gate comments;
- update GoAST/GoTypes/GoSafe/GoRender/GoEmit projection wording where names or guarantees changed;
- update ARCHITECTURE.md, CLAUDE.md, PROGRESS.md, README.md, Makefile comments, and plugin docs;
- correct the public publication workflow;
- correct collection audit rows after builder changes;
- record the review-policy change without embedding the C3 defect list in permanent Codex guidance.

In SOURCE_FOREST_STATUS.md:

- only the current C3 section remains ACTIVE;
- historical C0/C0A/C0B/C1/C1A/C1B/C2/older-C3 headings become COMPLETE or HISTORICAL;
- preserve useful review history;
- do not add another full plan to the ledger.

C6 may perform larger document compaction and physical module decomposition.

===============================================================================
11. REQUIRED VERIFICATION BEFORE CODEX
===============================================================================

Run the complete repository verification from the final working candidate:

  make check

Confirm:

- Rocq theory builds;
- readable assumption gate exact count;
- whole-theory closure audit;
- module coverage;
- adversarial audit self-tests;
- plugin and transport build;
- fresh runner operational negatives;
- full pinned-Go fresh-image matrix;
- command-precedence cases;
- all supported publication paths fresh-validate first;
- sink tests;
- canonical witness and runtime goldens;
- generated go.mod and recursive .go source bytes identical to authoritative pristine output;
- no post-build byte enters publication;
- staged-tree pre-commit verification from exact staged export;
- no untracked generated/control/temp residue;
- no C4 work.

Run targeted source/call-site audits for:

  analyze
  AnalysisOK
  AnalysisFailed
  CompilationFacts
  AllPackagesOneMain
  ProgValid
  prog_ok
  prog_package_refs
  prog_visit
  Snap.visit_file
  Fido Emit
  Fido_sink.sync
  go build ./...
  Print Assumptions
  ACTIVE

Every surviving occurrence must have one current, justified role.

Record:

- final candidate SHA;
- files and public names changed;
- definitions deleted;
- line-count reduction in GoCompile and gate;
- final gate count;
- all verification results;
- generated source-byte result;
- publication-path audit result.

===============================================================================
12. ONE HOLISTIC IMPLEMENTATION REVIEW
===============================================================================

After all work and verification are complete, freeze the candidate.

Update .review/REVIEW_REQUEST.md:

  state: requested
  review: Implementation Review
  confirmation: no
  contract: .review/NEXT_STEPS.md
  contract_sha: <activation commit>
  review_basis: .review/REVIEW_BASIS.md
  base_sha: fea649389ee52d442373c43ea2bdb3be2eca47db
  head_sha: <candidate SHA>

Commit the request and stop once.

Codex must review the complete C3 range, not the latest turn. The permanent policy requires one complete finding
set after all blockers are known.

If GREEN:

- record the result;
- close REVIEW_REQUEST;
- rerun final verification if the review caused no code changes;
- fast-forward push;
- notify Rob;
- stop;
- do not begin C4.

If BLOCKING:

- record the complete finding set;
- close REVIEW_REQUEST while repairing;
- repair every finding as one batch;
- rerun full verification;
- request a bounded confirmation using the same review type with confirmation: yes and the prior finding record;
- do not invite another unrestricted exploration.

A newly reported item in confirmation must be classified under the permanent policy.

===============================================================================
13. FINAL ACCEPTANCE
===============================================================================

C3 is complete only when:

- the permanent two-review Codex policy is installed;
- ordinary stop turns do not trigger substantive review;
- C3 has one accepted review basis;
- one retained source traversal is true in executable code;
- package buckets consume that retained traversal;
- fresh runner observation and materialization fail closed;
- exact source/fresh manifests and bytes are checked;
- every supported public publication path validates before sink effects;
- publication always uses the original pristine image;
- SourceProgramValid is the only source semantic root;
- old exactly-one/ProgValid/analysis residue is removed or unmistakably historical;
- executable-name proof rests on a component-level root and redundant string scaffolding is deleted;
- readable gate exposes load-bearing claims rather than every fixture/helper;
- whole-theory assumption closure remains complete;
- canonical/retained builders share one logic where practical;
- permanent docs and status are current;
- existing generated source bytes are unchanged;
- full proof/e2e/staged checks are green;
- one holistic Implementation Review is GREEN;
- at most one bounded confirmation was needed;
- fast-forward push succeeds;
- loop stops;
- C4 is not begun.

===============================================================================
14. FORBIDDEN
===============================================================================

Do not:

- restart C3;
- begin C4 or later feature work;
- add a typed/resolved/copied AST;
- add another semantic or compiler authority;
- add a custom collection or sorter;
- add cache/memoization machinery for the traversal defect;
- hide runner errors as absence;
- build in a sink or authoritative tree;
- publish from a post-build tree;
- put Go semantics in handwritten OCaml;
- preserve stale compatibility names with no approved consumer;
- answer the import-path proof problem with more character-level lemmas;
- perform the broad physical module split reserved for C6;
- keep giant C3-specific defect lists in permanent Codex policy;
- run Codex after every repair commit;
- weaken review strictness to obtain GREEN.

If a required repair cannot preserve the accepted C3 functional architecture, record an ARCHITECTURAL CONFLICT,
close the review request, notify Rob, and stop.
