Claude Code final human directive:
C3 weedwhacker closeout — delete the manifest system, restore responsibility boundaries, and shrink the repository

Repository:
  rhencke/fido

Human-reviewed snapshot:
  conflict/status tip 95258b0
  implementation candidate before conflict 42c536e
  uploaded repository snapshot size: 2,007,639 bytes across 65 files

THIS IS THE LATEST HUMAN DECISION.

It supersedes every contrary instruction or option in:

  .review/C3_ARCH_CONFLICT.md
  .review/C3_IMPL_REVIEW_FINDINGS.md
  .review/C3_MANUAL_CLOSEOUT_DIRECTIVE.md
  .review/C3_MANUAL_CLOSEOUT_AUDIT.md
  .review/NEXT_STEPS.md
  any prior human-resolution addendum
  any prose that permits retaining the MD5 / validation-manifest system
  any prose that requires an inaccessible local sink resistant to deliberate extraction
  any prose that requires fixtures to execute through the retained opaque index

Do not begin C4.

The intent is not a narrow patch.  Remove the review-driven machinery that landed in the wrong layer.  Prefer
deletion over another wrapper, proof bridge, marker, checksum, manifest, compatibility path, or explanatory
essay.

Correctness is the first priority.  Clear responsibility and future maintainability are next.  Small size is a
material acceptance goal, but do not minify correct code or weaken a theorem merely to save bytes.

===============================================================================
0. FINAL HUMAN DECISIONS
===============================================================================

0.1 Delete the manifest mechanism completely

Delete BOTH forms:

A. Persisted publication attestation:

  .fido-build-validated
  MD5 generation
  MD5 parsing
  MD5 recomputation
  byte-attestation maps
  manifest bijection checks
  /validated
  manifest COPY between Docker stages
  manifest-specific tests
  manifest-specific documentation

B. Fresh-runner source/fresh path manifests:

  source manifest files
  fresh manifest files
  source/fresh sort + diff
  path-set reconstruction
  manifest-specific find/sort/ls fault injection
  the generic "honest arbitrary input tree" validator built around those inventories

Do not replace MD5 with SHA-256, another hash, a signed file, a token, a nonce, a stamp consumed by fido_apply,
or another self-attested provenance object.

A checksum proves byte equality with a checksum.  It does not prove that validation occurred.  Publication
provenance belongs to the supported workflow graph, not the filesystem sink.

0.2 Docker is the fresh-build runner

The pinned disposable Docker stage is the one production fresh-build runner.

Do not retain a large shell sub-runner that re-validates arbitrary directories.

For certified outputs:

  certified DirectoryImage
      ->
  Fido Materialize into the authoritative pristine Docker layer
      ->
  Docker COPY of that pristine layer into a fresh disposable Go stage/directory
      ->
  literal pinned `go build ./...` exactly once
      ->
  discard the mutated build stage/directory

For handwritten differential fixtures:

  create each fixture in its own new disposable directory
      ->
  run literal pinned `go build ./...` directly there
      ->
  inspect result
      ->
  delete fixture

The authoritative generated layer is never built in place and never copied back from the build workspace.

0.3 Supported-workflow threat model

Use the cooperating-developer / supported-workflow boundary.

The project does not attempt to prevent a deliberate local user from:

- extracting an internal binary from an image;
- compiling a private copy of fido_sink.ml;
- calling an internal module directly;
- editing Dockerfile, Makefile, hooks, verifiers, and publication tools together;
- using `--no-verify`.

Every supported and documented public publication workflow must validate before sink effects.

Current supported publication workflow:

  make regenerate

Current public certified export:

  Fido Materialize

`Fido Materialize` is export, not publication.

Current internal filesystem details:

  fido_apply
  Fido_sink.sync

They are not public product APIs.

Do not create a general arbitrary-DirectoryImage publisher in C3.  There is no current consumer.

0.4 F1 specification/implementation decision

Keep an independent index-free, vm-computable source specification decision for fixtures and proof convenience.

Keep a separate retained-bucket production implementation.

This is allowed when:

- names make the specification role unmistakable;
- production elaborate never calls the specification boolean;
- no public CompilableProgram path trusts the boolean without the proved semantic bridge;
- both reflect the same factored semantic propositions;
- the production path performs no second syntax traversal.

Do not force fixtures through the sealed index.

0.5 Review-round cap

This directive authorizes one complete repair batch and ONE final bounded Implementation Review confirmation.

If that confirmation returns BLOCKING or ARCHITECTURAL CONFLICT:

- close REVIEW_REQUEST;
- record the result;
- notify Rob;
- stop;
- do not repair;
- do not request another review without a later explicit human override.

===============================================================================
1. TARGET RESPONSIBILITY SPLIT
===============================================================================

The final architecture must read plainly:

GoAST:
  source syntax and program image

GoIndex:
  occurrence identity and structural navigation

GoTypes:
  type and constant relations

GoCompile:
  source semantic elaboration
  fresh-build plan matching literal pinned cmd/go behavior
  structured diagnostics
  CompilableProgram evidence

GoRender / GoEmit:
  authoritative pristine source image

Docker build graph:
  fresh disposable materialization
  pinned literal `go build ./...`
  validate-before-publish ordering for supported workflows

Fido Materialize:
  proof-guarded pristine export only

fido_apply:
  tiny internal fixed-source publication adapter

Fido_sink:
  dirty-directory synchronization only

The sink knows nothing about:

- Go validation;
- compiler provenance;
- checksums;
- manifests;
- proof terms;
- ASTs;
- build plans.

The publication adapter knows nothing about:

- validation evidence;
- manifests;
- arbitrary source roots;
- Go semantics.

===============================================================================
2. DELETE THE PERSISTED MANIFEST / ATTESTATION SYSTEM
===============================================================================

Delete all code and tests for:

  `.fido-build-validated`
  `validation_manifest`
  `parse_manifest`
  `SM = Map.Make(String)` used for attestation
  `Digest.string`
  `Digest.to_hex`
  `md5sum`
  `_mkmanifest`
  `/validated`
  "md5 mismatch"
  "attested"
  "attestation"
  "byte-bound validation manifest"
  "validation provenance"
  missing / stale / mismatched / extra-manifest publication tests
  Docker COPY of a validation file into /generated
  apply-CLI checks for a sibling validation file

Delete the related collection-audit row.

Delete the emit-stage `fido-apply` manifest unit-test block.  Sink behavior remains tested by `sink_test`; the
supported publication workflow remains tested by `make regenerate` / the sync image dependency.

Do not preserve dead compatibility parsing.

After the repair, repository search must find no live code occurrence of:

  .fido-build-validated
  validation_manifest
  parse_manifest
  md5sum
  Digest.to_hex
  /validated

Historical Git commits are the archive.  Do not retain a prose museum in the working tree.

===============================================================================
3. DELETE THE FRESH-RUNNER MANIFEST SYSTEM
===============================================================================

Delete the current large shell machinery built around:

  `_sman`
  `_fman`
  source/fresh manifest temp files
  source/fresh sort
  path-set diff
  per-file byte comparison
  arbitrary-tree special-file/symlink/empty-directory validation
  find/ls/sort fault-injection matrix
  omitted/extra-manifest path tests

Reason:

The production input is not an arbitrary hostile directory.  It is a Docker layer produced from the certified
DirectoryImage.  DirectoryImage already owns the file set.  Docker COPY owns exact stage materialization.
Dirty-tree and special-file behavior belongs to Fido_sink tests.

Preferred canonical Docker shape:

  FROM generated-module AS authoritative source layer

  FROM pinned-go-image AS go-e2e
  COPY --from=generated-module /generated/ /e2e/tree/
  RUN cd /e2e/tree && literal pinned `go build ./...`

The go-e2e stage itself is fresh and disposable.  The sole-command executable may overwrite go.mod or source
inside that stage.  That is allowed; no downstream source artifact may copy from the mutated directory.

For multi, empty, bytes, and future certified outputs:

- create one pristine artifact layer per output, or copy each pristine export into a separate fresh directory in
  go-e2e;
- run the literal command once in that directory;
- never reuse a directory for a second build;
- never feed its post-build bytes to publication.

For handwritten Go differential fixtures:

- create them under fresh `/tmp` paths;
- run the literal command directly;
- delete them;
- do not route them through a generic source-tree verifier.

A tiny helper is allowed only when it is materially shorter than direct commands.  If retained, it may do only:

  mktemp -d
  checked `cp -a -- "$src/." "$fresh/"`
  checked `cd`
  pinned literal `go build ./...`
  return the Go status and disposable root/log
  cleanup

It must not:

- enumerate a file manifest;
- hash files;
- compare path sets;
- validate arbitrary hostile filesystem types;
- rebuild the sink threat model;
- exceed roughly 40 clear shell lines.

Prefer direct Docker COPY / direct fixture commands over even that helper.

Retain external tests for the semantic cmd/go cases:

- empty selection;
- source rejection;
- duplicate/missing main;
- multiple packages;
- immediate-child directory collision;
- deeper noncollision;
- vN executable-name behavior;
- ordinary overwrite of go.mod/source in disposable trees;
- command failure precedence;
- future Go oracles already required by the active contract.

Delete tests whose only purpose was defending the removed manifest runner.

===============================================================================
4. SIMPLIFY VALIDATE-BEFORE-PUBLISH
===============================================================================

At the successful end of go-e2e, create one tiny Docker dependency artifact, for example:

  /fresh-build-ok

It is ONLY a Docker DAG edge.

It is not:

- a manifest;
- an attestation;
- a capability;
- consumed by fido_apply;
- copied beside source;
- published;
- described as unforgeable provenance.

Define sync after go-e2e:

  FROM emit AS sync
  COPY --from=go-e2e /fresh-build-ok /fresh-build-ok
  COPY --from=generated-module /generated/ /generated/
  ...

That COPY makes the sync image unavailable unless go-e2e completed successfully.

The sync image publishes the ORIGINAL generated-module layer, never any go-e2e build directory.

Simplify Makefile:

- `make regenerate` builds the `sync` target;
- building `sync` itself forces go-e2e through the Docker dependency;
- remove a separate `e2e` Make prerequisite if it merely runs the same graph twice;
- then run the sync image against `/dest`.

Do not add another marker check inside the application.

===============================================================================
5. REDUCE fido_apply TO THE MINIMUM
===============================================================================

`e2e/fido_apply.ml` should become a tiny internal adapter.

Fixed source:

  /generated

Fixed destination in the sync container:

  /dest

Preferred interface:

  no command-line arguments

At most, accept only the destination.  Do not accept an arbitrary source path.

It should:

1. read `/generated/go.mod`;
2. enumerate `/generated/**/*.go`;
3. call `Fido_sink.sync`;
4. report success/failure.

It should not:

- import Map.Make for validation;
- parse metadata;
- hash bytes;
- inspect a validation file;
- run Go;
- accept arbitrary source roots;
- claim build provenance;
- become a public installed command.

Delete the long threat-model essay from the source header.  A short responsibility statement is enough.

Update `plugin/dune` prose to state simply:

- public plugin command materializes;
- sink module is private to the plugin library;
- sync image compiles its own internal filesystem adapter;
- supported publication is ordered by Docker.

No claim that local extraction is impossible.

===============================================================================
6. KEEP F1 AS SPECIFICATION + PROVED PRODUCTION IMPLEMENTATION
===============================================================================

Rename:

  pkg_all_ok
    ->
  source_spec_package_rules_b

  source_valid_b
    ->
  source_spec_valid_b

Rename related theorem names consistently.

The comments must say:

  source_spec_*:
    readable index-free specification / fixture decision

  retained bucket diagnostics:
    production elaboration implementation

Required direct semantic roots:

  PackageDeclsUnique
  MainPackagesHaveEntry
  PackageRulesValid
  SourceProgramValid

Required direct specification reflections:

  source_spec_package_rules_b = true <-> PackageRulesValid
  source_spec_valid_b = true <-> SourceProgramValid

Required retained implementation exactness:

  redeclaration diagnostics empty <-> PackageDeclsUnique
  missing-entry diagnostics empty <-> MainPackagesHaveEntry
  package diagnostics empty <-> PackageRulesValid
  semantic diagnostics empty <-> SourceProgramValid

Keep:

  current_package_rules_exactly_one

only as the clearly named current-grammar consequence theorem.

Production `elaborate_indexed` must not call `source_spec_*`.

Fixtures may use `source_spec_*`.

Delete comments or APIs that call the specification boolean "shared production decision", "compiler", or
"sole executable authority".

===============================================================================
7. REMOVE DUPLICATE EXECUTABLE BUILDERS
===============================================================================

Define:

  fresh_build_plan p :=
    fresh_build_plan_of
      (prog_module p)
      (selected_package_keys p)
      (root_layout p)

Delete the duplicated match body.

Delete `fresh_build_plan_eq_of` if it becomes reflexive or pointless.

Factor one function over:

  plan
  semantic diagnostics

for command-facing diagnostics, for example:

  command_diagnostics_of p plan semantic_ds

Use the same function from:

- the readable canonical wrapper;
- `elaborate_indexed` with retained plan and retained semantic report.

Delete `command_plan_diags_eq` if it exists only to reconcile two handwritten branches.

A theorem may prove that retained inputs equal canonical inputs.  Do not prove two copied algorithms equal.

Audit the C3 affected surface for other exact duplicate executable definitions.  Delete duplicates.  Do not
create a generic Utils.v dumping ground.

===============================================================================
8. BUILD THE MISSING LOWER PATH-COMPONENT ROOT, THEN DELETE THE PROOF FOREST
===============================================================================

The default executable-name rule is component based:

  use final import-path component
  except final valid vN (N >= 2, no leading zero) uses previous component

GoCompile should not carry hundreds of lines rebuilding path component facts character by character.

First search the pinned Rocq standard library for a suitable split/join component view.

If none fits, add the smallest lower-layer abstraction at the correct path layer.

Preferred public views:

  ModulePath components
  FilePath parent-directory components
  join-components exactness
  nonempty / slash-free component facts

A small shared slash-component module is acceptable only if it:

- depends only on Stdlib strings/lists;
- is used by ModulePath and FilePath or deletes clear duplication;
- remains proof/value plumbing, not collection storage;
- deletes substantially more code than it adds.

Then define:

  package import components
    =
  module components ++ package-directory components

Compute `default_exec_name` directly from the final two components.

Prove one bridge from the selected component to the canonical import-path string.

Delete the GoCompile-local ecosystem that becomes redundant, including as much as applicable:

  string_contains_slash
  local basename/dirname scanners
  local split/join reconstruction
  append cancellation scaffolding
  slash-free transport lemmas
  removelast membership scaffolding
  duplicate component nonempty proofs
  local path-shape facts now owned by ModulePath/FilePath

This is not complete if a component abstraction is added and the old proof forest remains.

Expected result:

- a material net deletion in GoCompile.v;
- the executable-name theorem surface remains exact;
- all required v0/v1/v2/v10 and import-path fixtures remain;
- no generated byte changes.

===============================================================================
9. SOURCE-CODE WEEDWHACKING
===============================================================================

Remove review chronology from permanent source files.

Delete source comments whose main purpose is:

- naming C3 subsection numbers;
- narrating Codex finding numbers;
- recounting prior deleted implementations;
- recording repair rounds;
- defending a design against a superseded review demand;
- repeating architecture already stated in ARCHITECTURE.md.

Keep comments that explain:

- a nonobvious semantic rule;
- a proof invariant;
- a responsibility boundary;
- a counterintuitive external behavior;
- why an apparently simpler implementation is wrong.

Shorten oversized module headers to permanent current responsibilities.

Do not compress Gallina into unreadable one-line proofs.

Delete dead definitions, helper lemmas, compatibility aliases, and proof bridges made obsolete by:

- F1 renaming;
- shared plan builder;
- shared diagnostic builder;
- lower component abstraction;
- manifest removal.

Use the pinned Stdlib before adding another local helper.

Do not retain a function merely because a gate entry names it; update the gate.

===============================================================================
10. REVIEW-FOLDER WEEDWHACKING
===============================================================================

Git history is the archive.  The working tree is for current authority.

Delete these completed, superseded, or resolved files after their live requirements are folded into current
architecture / contract / status:

  .review/C2_PRODUCTION_GOINDEX_PLAN.md
  .review/C3_ARCH_CONFLICT.md
  .review/C3_IMPL_REVIEW_FINDINGS.md
  .review/C3_INDEXED_ANALYSIS_DIAGNOSTICS_PLAN.md
  .review/C3_MANUAL_CLOSEOUT_AUDIT.md
  .review/C3_MANUAL_CLOSEOUT_DIRECTIVE.md
  .review/COLLECTIONS_C1B_PLAN.md
  .review/COLLECTION_FOUNDATIONS_MASTER_PLAN.md

Do not replace them with new long diary files.

Keep the active C3 contract until human approval.

Replace `.review/NEXT_STEPS.md` with a short authority pointer containing only:

- active checkpoint;
- active contract path;
- activation commit/hash;
- review basis path/hash;
- current state;
- explicit later human amendment path/commit if any;
- C4 forbidden.

It must not duplicate the 65 KB contract.

Compact `.review/SOURCE_FOREST_STATUS.md` aggressively.

Keep:

- campaign identity;
- current checkpoint;
- active authority chain;
- one concise table per completed checkpoint:
    contract SHA
    final SHA
    review result
    gate count
    human result
- current unresolved/closing state;
- final C3 commit/review data when complete.

Delete:

- commit-by-commit repair diaries;
- quoted Codex findings already in Git history;
- repeated architectural explanations;
- superseded active labels;
- historical candidate prose.

Target:

  SOURCE_FOREST_STATUS.md <= 20,000 bytes

Compact `.review/SOURCE_FOREST_MASTER_PLAN.md` only where it duplicates completed checkpoint detail.  Preserve
the durable future C4/C5 campaign requirements and campaign closeout rules.

No active requirement may be lost.

===============================================================================
11. ROOT DOCUMENT WEEDWHACKING
===============================================================================

Give each file one job:

ARCHITECTURE.md:
  current normative architecture and guarantees only

CLAUDE.md:
  contributor laws, workflow, review process, and links
  no full architecture copy
  no review history

PROGRESS.md:
  concise completed feature inventory and immediate next frontier
  no architecture restatement
  no repair diary

README.md:
  user-facing purpose, trust statement, and commands

PAINFUL_LESSONS.md:
  only costly traps that remain plausible future errors
  no checkpoint narrative
  no duplicate architecture rules

Remove repeated paragraphs among these files.  Link instead.

Correct all manifest/provenance, publication, F1, and review-round claims.

Targets:

  total of the five root Markdown files <= 110,000 bytes
  CLAUDE.md <= 25,000 bytes
  PROGRESS.md <= 18,000 bytes

These are maintainability targets.  If a required current guarantee cannot fit, keep the guarantee and record the
specific exception.  Do not keep repetition.

===============================================================================
12. DOCKERFILE WEEDWHACKING
===============================================================================

Delete:

- the persisted manifest gate block;
- fido-apply manifest unit tests;
- the source/fresh manifest runner;
- manifest fault injection;
- long comments describing deleted threat models;
- duplicate `e2e` then `sync` orchestration;
- repeated prose already in architecture docs.

Keep:

- pinned toolchain identity;
- proof and assumption gates;
- certified materialization;
- literal fresh `go build ./...`;
- semantic differential matrix;
- witness/golden execution;
- sink adversarial tests;
- content-addressed generated-module;
- sync dependency on go-e2e;
- generated-byte checks.

Prefer short named shell helpers for repeated fixture setup/status checks.

Do not create a new general-purpose shell framework.

Target:

  Dockerfile <= 80,000 bytes

The final Dockerfile should visibly express the stage graph without pages of commentary.

===============================================================================
13. READABLE ASSUMPTION GATE
===============================================================================

Retain the 386-surface reduction or reduce further.

Readable Print Assumptions entries should cover load-bearing public claims:

- semantic roots;
- soundness/completeness;
- identity and provenance;
- ordering/determinism;
- command plan exactness;
- DirectoryImage bridge;
- capability boundaries.

Concrete fixtures must compile and remain covered by the whole-theory assumption audit.

Do not add one readable entry per concrete example.

Delete gate entries for removed helpers and aliases.

Never weaken the whole-theory audit.

===============================================================================
14. REVIEW-PROCESS HARD CAP
===============================================================================

Amend `.review/CODEX_REVIEW_POLICY.md`, stop-hook prompt, and request template.

There remain two review types:

  Contract Review
  Implementation Review

Each has:

  one initial review
  at most one bounded confirmation after one complete repair batch

Hard rule:

> A blocking confirmation ends autonomous work.

After a blocking confirmation:

- close request;
- record;
- notify;
- stop.

Delete any policy line saying a previously visible missed finding is autonomously repaired after confirmation.

A missed finding proves the initial review was incomplete.  It does not authorize an infinite loop.

Required request fields:

  state
  review
  confirmation
  confirmation_used
  human_override

No second confirmation without an explicit later human override.

===============================================================================
15. SIZE ACCOUNTING
===============================================================================

Record baseline before edits using tracked working-tree files.

Human snapshot baseline:

  whole repository:              2,007,639 bytes
  .review:                         595,881 bytes
  five root Markdown files:        165,364 bytes
  Dockerfile:                      105,802 bytes
  GoCompile.v:                     449,039 bytes
  gate/axiom_gate.v:                46,383 bytes
  operational group:               170,905 bytes

Operational group for comparison:

  Dockerfile
  Makefile
  e2e/fido_apply.ml
  plugin/fido_sink.ml
  plugin/g_fido.mlg
  plugin/dune

At closeout, report exact before/after:

- whole repository;
- .review;
- root Markdown;
- all Rocq source;
- GoCompile.v;
- gate;
- Dockerfile;
- operational group;
- file count;
- lines deleted/added where useful.

Required direction:

- whole repository materially smaller;
- `.review` dramatically smaller;
- Dockerfile materially smaller;
- GoCompile.v materially smaller;
- fido_apply reduced to a small adapter;
- no manifest machinery;
- no new explanation files offsetting deletions.

Expected minimum:

  net deletion >= 300,000 bytes from the human snapshot

This is a strong target, not permission to remove a live guarantee.  If the result is less, stop before review
and provide a precise list of the unavoidable retained bytes.  "It was easier to leave the old text" is not an
exception.

Any new abstraction should pay for itself by deleting more code/prose in the same responsibility area.

===============================================================================
16. REQUIRED SEARCH AUDIT
===============================================================================

Before review, run repository-wide searches.

The following must have zero live implementation occurrences:

  .fido-build-validated
  validation_manifest
  parse_manifest
  md5sum
  Digest.to_hex
  _mkmanifest
  /validated
  _sman
  _fman

The following may appear only in this human directive or concise historical resolution text, not current
architecture/workflow claims:

  byte-bound manifest
  validation provenance
  attestation
  inaccessible sink
  unvalidated bytes cannot be published by any direct local invocation

The following old live names must be absent:

  pkg_all_ok
  source_valid_b

The following stale claims must be absent:

  every Go package requires exactly one main
  Fido Emit is a live public command
  C2 in progress
  old checkpoints marked ACTIVE
  full final reports depend only on FilesEqual
  fido_apply accepts arbitrary source roots
  make regenerate separately runs e2e and then rebuilds the same validation graph

Classify actual unrelated uses before deleting text blindly.

===============================================================================
17. VERIFICATION
===============================================================================

Run the complete pinned workflow after all deletions:

  make prove
  make e2e
  make check
  make regenerate
  staged-tree pre-commit verification

Verify:

- readable gate exact count;
- whole-theory assumption audit;
- adversarial audit self-tests;
- pinned literal Go matrix;
- witness goldens;
- sink adversarial tests;
- generated go.mod and recursive `.go` byte identity;
- sync image cannot build unless go-e2e succeeds;
- sync publishes the pristine generated-module, not post-build bytes;
- make regenerate uses only the supported path;
- no manifest file exists;
- no C4 work.

For publication ordering, add a small structural regression, not a new security framework:

- deliberately make go-e2e fail;
- assert `--target sync` cannot complete because of its Docker dependency;
- restore;
- assert sync succeeds and publishes original generated bytes.

Do not test deliberate extraction of internal binaries.  It is outside scope.

===============================================================================
18. FINAL REVIEW REQUEST
===============================================================================

Implement this entire directive as one batch.

This human decision authorizes one final bounded Implementation Review confirmation.

Request fields:

  state: requested
  review: Implementation Review
  confirmation: yes
  confirmation_used: yes
  human_override: C3-weedwhacker-human-decision

The confirmation is bounded to:

- deletion of both manifest systems;
- correct fresh disposable literal Go workflow;
- validate-before-publish ordering for supported workflows;
- F1 specification/production boundary;
- shared builders;
- lower path-component root and deletion of proof scaffolding;
- hard review cap;
- documentation correctness;
- byte-size evidence;
- direct repair-induced defects;
- full verification.

It must not demand:

- deliberate-local-bypass resistance;
- cryptographic provenance;
- a public arbitrary-image publisher;
- fixture evaluation through the opaque index;
- restoration of deleted manifest machinery;
- new C4 features.

After confirmation:

GREEN:
  run final verification;
  push;
  record compact completion;
  notify Rob;
  stop.

BLOCKING or ARCHITECTURAL CONFLICT:
  close REVIEW_REQUEST;
  record;
  notify Rob;
  stop.
  Do not repair or request another review autonomously.

===============================================================================
19. ACCEPTANCE
===============================================================================

C3 closeout is complete only when:

- persisted validation manifest system is deleted;
- source/fresh runner manifest system is deleted;
- no hashes or attestations stand in for validation;
- Docker stage freshness replaces arbitrary-tree runner machinery;
- sync depends structurally on successful go-e2e;
- sync publishes original generated-module bytes;
- fido_apply has fixed source/destination and no manifest logic;
- make regenerate is the only current supported publication workflow;
- Fido Materialize is documented as export only;
- F1 source specification names are clear and production does not call them;
- factored package roots remain exact;
- fresh plan has one implementation;
- command diagnostics have one implementation;
- lower path components replace the GoCompile string proof forest;
- old helper/proof/comment residue is deleted;
- review folder and status are compact;
- root docs are concise and nonduplicative;
- gate remains rigorous;
- repository is at least 300 KB smaller unless a concrete human-worthy exception is recorded;
- generated source bytes are unchanged;
- full verification is green;
- one bounded confirmation is GREEN;
- C4 has not begun.

The desired final feeling is simple:

  every remaining abstraction owns one real responsibility;
  every remaining proof protects one real claim;
  every remaining document has one clear job;
  every remaining byte has earned its place.
