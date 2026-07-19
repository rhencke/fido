★ AMENDMENT (Rob, verbal decision, 2026-07-19) — PLATFORM LIMITS ARE OUT OF SCOPE.
  Fido does NOT model platform-specific filesystem / materialization limits (NAME_MAX, PATH_MAX, disk,
  memory).  For modeling purposes a path is UNLIMITED length.  The "GoCompile accepts EXACTLY what the pinned
  `go build ./...` accepts" invariant, and the "the directory-collision is the ONLY command-level failure"
  claim, are scoped to the SEMANTIC + cmd/go PACKAGE/OUTPUT LOGIC (types, one-main, the default-output
  directory-collision — deterministic from the image, platform-independent).  A default executable name that
  exceeds a platform's NAME_MAX (so `go build` prints "file name too long") is NOT a model bug and is NOT
  rejected by GoCompile — it fails-LOUD during printing / materialization (the OS surfaces ENAMETOOLONG), the
  same way disk-space and memory limits are the platform's domain, not Fido's.  Do NOT add a
  length / NAME_MAX / PATH_MAX check to the grammar, to GoCompile, or to the sink.  This amendment OVERRIDES
  any wording below that implies platform limits are modeled, or that over-long paths are
  unrepresentable / rejected.  Rob's words: "Do not model platform limits because platform limits are
  platform specific... For modeling purposes, the path is unlimited in length.  It's the same reason we're not
  modeling memory limits or disk space limits.  It's not your domain to care about this.  Let the underlying
  platform let you know."

===============================================================================

Claude Code directive: C3 final repair — exact fresh-image parity with literal pinned `go build ./...`

Repository:
  rhencke/fido

Baseline:
  fea649389ee52d442373c43ea2bdb3be2eca47db
  C3 §16 (9th FINAL review): strict canonical diagnostic order via unique keys + singleton buckets

THIS IS A FRESH, SELF-CONTAINED CONTRACT.

It supersedes every earlier proposed C3 repair concerning:

- exactly-one-main semantics;
- analysis-to-elaboration naming;
- output-neutral package builds;
- literal `go build ./...` output behavior;
- ambient dirty-tree build behavior.

Do not combine old repair text with this file.  Use this file alone.

THIS IS THE ONLY ACTIVE C3 CHECKPOINT.

C3's accepted structural implementation is retained.  Do not restart C3.  Do not begin C4.

The production invariant is now exact:

> Every certified DirectoryImage is compiled by materializing that exact image into a fresh, empty, pinned build
> root and invoking the literal pinned command `go build ./...` exactly once.  The build root is disposable and
> is never the sink destination.  Fido's final GoCompile judgment must accept exactly the programs for which
> that production invocation succeeds.

This means both parts matter:

1. Go source/package/compiler validity.
2. cmd/go's own package-pattern and default-output behavior.

The second part is strange but binding.  A sole main package may cause cmd/go to create or overwrite a root
executable.  If the computed output name is an existing directory in the fresh image, the command fails before
the compiler runs.  Fido must model that failure.  If the target is an ordinary regular file, including go.mod
or a root `.go` source file, cmd/go overwrites it after a successful build.  Fido must not reject a case that the
literal command accepts.

The fresh root contains only the authoritative DirectoryImage:

  go.mod
  every rendered `.go` file at its FilePath
  the parent directories implied by those file paths

It contains no:

  .fido
  lock
  temp
  executable from a prior build
  unrelated file
  unrelated directory
  symlink
  special file
  VCS metadata
  workspace file
  nested module
  sink residue

The post-build root is discarded.  It never becomes the source of published bytes.

Before implementation, write this directive VERBATIM to:

  .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md
  .review/NEXT_STEPS.md

If any prior C3 repair plan has already been added to `.review`, put a short top banner on it:

  SUPERSEDED by .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md

Do not delete Git history.  Do not leave an older repair plan as a live competing authority.

Update:

  .review/SOURCE_FOREST_STATUS.md

to record:

- active work: C3 fresh-image literal-build final repair;
- baseline SHA above;
- all existing C3 implementation retained unless this contract says otherwise;
- current package-rule factorization defect;
- current analysis/elaboration vocabulary defect;
- current lack of an exact fresh-image cmd/go plan;
- the fresh build-root invariant;
- C4 remains forbidden;
- this file is the binding completion contract.

Commit the contract before implementation:

  review(contract): C3 — activate fresh-image literal go-build parity

Then continue the current loop.

Do not intentionally stop for Codex until the complete candidate and the pre-Codex audit in this directive are
finished.

Use one exhaustive discovery review over the complete frozen C3 candidate.  Tell Codex to continue after the
first blocker and return every independently visible finding.  Repair the whole batch.  Then run one confirmation
review.  Additional rounds are only for repair-induced defects.

===============================================================================
0. FINAL OUTCOME
===============================================================================

At completion, the certified path is:

  GoProgram p
      |
      v
  IndexedProgram p
      |
      v
  elaborate p
      |
      +-- ElaborationFailed
      |      exact nonempty structured diagnostics
      |
      +-- ElaborationOK
             ElaborationFacts
             exact retained index
             exact retained source facts
             exact retained package facts
             exact fresh-image BuildAllPlan
             proof of GoCompile p
      |
      v
  CompilableProgram
      |
      v
  SafeProgram
      |
      v
  DirectoryImage
      |
      +------------------------------+
      |                              |
      v                              v
  fresh build root               sink/publication
  exact image only               original image only
  literal pinned build           never post-build root
      |
      v
  `go build ./...` once
      |
      v
  discard build root

Required final meanings:

  SourceProgramValid p
    The represented Go source passes the current Go language/compiler/package rules.

  FreshBuildPlan p
    The exact cmd/go package-selection and default-output plan for the fresh DirectoryImage.

  FreshBuildCommandValid p
    The literal pinned `go build ./...` preflight and compiler invocation succeeds in that fresh root.

  GoCompile p
    Source and command conditions required for the literal production invocation to succeed.

For the current represented grammar, the only command-level failure not already caused by source/compiler
invalidity is:

  exactly one selected main package
  AND
  its default output name is an existing root directory in the fresh image

However, command failure precedence matters:

  package loading
  then default-output directory check
  then compilation/linking

The current AST intrinsically avoids package-load failures.  Therefore, for a sole main package whose output
name is an existing directory, Fido reports the build-output collision even if the source also contains a type,
redeclaration, or missing-entry error.  This matches cmd/go's control flow.

Fido does not claim exact equality with:

- cmd/go stderr wording;
- compiler diagnostic scheduling;
- compiler diagnostic count;
- executable bytes;
- cache contents;
- elapsed time.

Fido does claim exact acceptance/rejection for the pinned fresh invocation, within the represented subset.

===============================================================================
1. STANDING LAWS
===============================================================================

Preserve every accepted law:

1. Zero project axioms.
2. No `Admitted`.
3. No forbidden kernel primitives.
4. No fuel.
5. One raw, specification-shaped AST.
6. No typed AST.
7. No resolved AST.
8. No copied compiler tree.
9. No parent links in AST nodes.
10. No author-assigned node identities.
11. Standard mature collections only.
12. One retained structural index per program elaboration.
13. One production semantic elaboration root.
14. Facts and diagnostics decorate occurrence identity.
15. Rendering uses the original AST.
16. DirectoryImage contains original rendered source bytes.
17. Build side effects never become rendered or published source.
18. Failed construction never falls back to empty/success.
19. Duplicate evidence is never silently overwritten.
20. C4 and later features remain forbidden.

Add these laws:

21. Every production `go build ./...` runs in a fresh materialization of exactly one DirectoryImage.
22. No production build runs in a dirty sink destination.
23. The literal command line is not replaced by a cleaner per-package command.
24. The command environment is pinned and free of ambient user Go configuration.
25. A disposable build root may be destroyed by cmd/go; the authoritative image may not.
26. GoCompile predicts the exact one-shot fresh invocation, not a second invocation in the mutated root.
27. Source/compiler validity and cmd/go output planning stay separate even though final acceptance requires both.
28. The final combined result may depend on ModuleSpec; source occurrence facts do not.

===============================================================================
2. CURRENT C3 FOUNDATION — RETAIN
===============================================================================

Do not reopen these accepted decisions:

- GoAST is the source authority.
- GoIndex is structural and semantic-free.
- IndexedProgram carries one retained SyntaxIndex.
- NodeRef identity is exact-program-local.
- NodeKey is FilePath + positive local id.
- visit_file carries validated refs with original syntax.
- prog_blocks retains one visit block per file.
- prog_visit is the one flattened visit stream.
- const_info_step is the one-node semantic step.
- prog_status_map is bottom-up over the retained visit stream.
- expression facts use a standard NodeKey FMapAVL.
- package main-ref buckets use a standard PackageMap.
- enclosing conversion context is one forward pass over retained blocks.
- facts store no source copy.
- diagnostics use exact-snapshot anchors.
- erased source reports support cross-snapshot comparison.
- node-primary source diagnostics use strict NodeKey order.
- CompilableProgram retains its exact index and facts with provenance.
- go_compile projects one retained semantic execution.
- GoTypes imports no GoIndex.
- GoCompile is the sole meeting point of GoIndex and GoTypes.
- GoRender and GoEmit use original source.
- generated source bytes remain unchanged.

The existing one-pass code is the base for this repair.

===============================================================================
3. PINNED PRODUCTION INVOCATION
===============================================================================

The production build contract is one exact environment plus one exact command.

Pinned container:

  golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f

Expected tool identity in that image:

  go1.23.x
  linux
  amd64

The status ledger must record the exact observed:

  go env GOVERSION GOOS GOARCH

Production command line:

  go build ./...

Run from:

  the root of a fresh materialization of the certified DirectoryImage

Pin the environment explicitly:

  GOWORK=off
  GOTOOLCHAIN=local
  GOPROXY=off
  GOSUMDB=off
  GOENV=off
  GOFLAGS=
  GO111MODULE=on
  GOOS=linux
  GOARCH=amd64

Pin the materialization process:

  umask 022
  directories mode 0755
  go.mod mode 0644
  `.go` files mode 0644
  no symlinks
  no special files
  no pre-existing output
  no VCS metadata

Use a writable cache and temporary directory outside the module root.  Cache state may improve speed but must not
change the result.  For the differential matrix, use isolated cache directories where practical.

Do not add `-o`, `-buildvcs=false`, or another flag to the authoritative command.  The exact command remains:

  go build ./...

The clean environment and fresh root remove ambient inputs instead of changing the command.

===============================================================================
4. OFFICIAL CMD/GO BEHAVIOR TO MODEL
===============================================================================

Inspect the pinned Go 1.23 source and help text inside the image.

Load-bearing source paths:

  $GOROOT/src/cmd/go/internal/work/build.go
  $GOROOT/src/cmd/go/internal/load/pkg.go
  $GOROOT/src/cmd/compile/internal/types2/resolver.go
  $GOROOT/src/cmd/link/internal/ld/errors.go

Record the relevant pinned source snippets or line ranges in the status ledger or a short review note.

The behavior to model:

4.1 Package loading comes first

`go build` loads packages and exits on package-load errors before output planning.

Current Fido source cannot express:

- parse errors;
- mixed package names;
- build constraints;
- imports;
- nested modules;
- ignored file classes.

These remain unrepresentable.

4.2 Default output is selected before compilation

After package loading, cmd/go does:

  if exactly one selected package
  and its package name is main
  and no explicit -o
  then set BuildO to DefaultExecName

It then stats that output path.

If it exists as a directory, cmd/go fails immediately:

  go: build output "<name>" already exists and is a directory

The compiler and linker do not run.

4.3 One main package writes an executable

For one selected main package, the default executable name is the last non-major-version component of the
package import path.

Linux adds no suffix.

Examples:

  example.com/m              -> m
  example.com/m/sub          -> sub
  example.com/m/a/b          -> b
  example.com/m/a/v2         -> a
  example.com/m/v2           -> m

4.4 The vN rule is exact

A final path component is a major-version element exactly when it matches Go's pinned `isVersionElement`:

  v2       true
  v3       true
  v10      true
  v100     true

  v0       false
  v00      false
  v01      false
  v05      false
  v1       false
  v1x      false
  v2x      false
  V2       false
  v        false

Definition shape:

- at least two bytes;
- first byte `v`;
- second byte is not `0`;
- exactly `v1` is excluded;
- every byte after `v` is a decimal digit.

Do not reuse ModulePath's different version-suffix exclusion as this rule.

4.5 Multiple packages discard outputs

When `./...` selects two or more packages, cmd/go builds them but does not write default package outputs.

Two valid command packages in separate directories succeed.

4.6 One non-main package discards output

Future non-main package syntax will use this branch.  It needs no `main` entry and writes no default output.

Do not implement non-main source syntax in C3.  Record the branch in the build-plan design.

4.7 Zero packages succeeds

An empty module causes `./...` to match no packages.  cmd/go warns and exits successfully.

Fido's empty program remains accepted.

4.8 Existing regular files are overwritten

For a sole main package, an existing ordinary root file at the computed output name is not a preflight error.

In the fresh image this can be:

- go.mod;
- a root `.go` source file.

After successful compilation/linking, cmd/go replaces it with the executable.

The build root is disposable, so this is allowed.

Do not add a protective semantic rejection.

4.9 Existing directories reject

A nested source path creates root directories.

If the sole command's output name equals one of those root directories, cmd/go rejects before compiling.

This is the command-level failure Fido must model.

4.10 One-shot behavior

A successful build may mutate go.mod or a source file.  The production contract is one invocation in a fresh copy.

Do not model a second `go build` in the same mutated root.

===============================================================================
5. FRESH DIRECTORYIMAGE BUILD ROOT
===============================================================================

Make the fresh build-root boundary explicit and reusable.

The authoritative input is a DirectoryImage, not a sink tree.

The build materializer must create:

  fresh/
    go.mod
    <every image `.go` entry>

No other entry is copied.

The image source may be:

- the generated-module layer;
- another pristine DirectoryImage export;
- a runtime DirectoryImage decoded by the approved transport.

It may not be:

- a directory after sink synchronization;
- a directory after a prior Go build;
- a repository checkout;
- an arbitrary user directory.

The build runner must:

1. Create a new empty temporary root.
2. Set fixed modes.
3. Materialize go.mod byte-for-byte.
4. Materialize each FilePath/byte entry byte-for-byte.
5. Create only required parent directories.
6. Verify the fresh manifest before invoking Go.
7. Verify the fresh bytes against the authoritative input before invoking Go.
8. Run literal `go build ./...` once.
9. Capture exit status and logs.
10. Discard the root after the result and any test inspection.
11. Never copy any post-build byte back to the authoritative image or sink.

For production success, only exit status matters.

For differential fixtures, tests may inspect the disposable post-build tree to prove:

- output created;
- regular file overwritten;
- directory collision left the tree unbuilt;
- multiple-package build wrote no default executable.

Add one reusable implementation.  Do not duplicate shell logic for each witness.

A suitable interface is:

  fido_go_build_all_fresh <authoritative-pristine-tree>

or an equivalent container target.

The wrapper itself must always create the fresh second tree.  Passing an already-fresh path is not permission to
build in place.

===============================================================================
6. AUTHORITATIVE IMAGE MANIFEST
===============================================================================

The runner needs a fail-closed authoritative input format.

Preferred minimum:

- exactly one regular root go.mod;
- zero or more regular `.go` files;
- directories only as parents of those files;
- no empty directories;
- no symlinks;
- no special files;
- no extra regular files;
- no `.fido`;
- no temp suffix;
- no nested go.mod.

Use the canonical pristine DirectoryImage export, not a broad copy of an emit/sink directory.

For each current witness, produce a pristine export:

  witness
  multi-package
  empty
  boundary-bytes

The current canonical generated-module stage already has the right idea for the main witness.  Generalize the
same rule to every output rather than copying sink trees with `.fido` into go-e2e.

Do not treat hidden ignored files as harmless in the authoritative build input.  The contract says the fresh root
contains exactly DirectoryImage, so extra entries are a pipeline error even if Go would ignore them.

===============================================================================
7. ROOT LAYOUT MODEL
===============================================================================

The semantic build plan must be derived from the same layout the fresh materializer creates.

Define a standard-map-backed root layout.

Suggested value:

  Inductive FreshRootEntryKind :=
  | FREGoMod
  | FRESourceFile (path : FilePath)
  | FREDirectory.

Use a mature standard string-keyed map:

  RootEntryMap := PackageMapBase.t FreshRootEntryKind

The key is one root path component.

Build it from:

- key `go.mod` -> FREGoMod;
- every root-level source FilePath -> FRESourceFile;
- the first component of every nested source FilePath -> FREDirectory.

No custom map or association list.

The builder must detect contradictory entry shapes:

- one key as both file and directory;
- go.mod as directory;
- two different regular-file authorities at one key.

Do not silently pick one.

Audit whether FilePath's intrinsic grammar already proves those conflicts impossible.

If it does:

- prove the impossibility;
- keep construction total.

If it does not:

- add a duplicate/conflict-rejecting program-layout validation at the earliest correct source-program builder;
- do not let an unmaterializable DirectoryImage reach compilation;
- preserve standard-map storage;
- add exact negative fixtures.

This is a required audit.  Do not assume prefix compatibility.

Required theorems:

- root entry domain exactness;
- root regular-file exactness;
- root-directory exactness;
- file/directory disjointness;
- layout determinism;
- FilesEqual programs produce equal root source layout;
- materialized DirectoryImage has exactly this root layout.

===============================================================================
8. DIRECTORYIMAGE BRIDGE
===============================================================================

Avoid a gap between a plan over GoProgram and the real emitted image.

Define or prove a bridge at the GoRender/GoEmit boundary:

  directory_image_realizes_fresh_layout

Conceptually:

  root_layout_of_image (rendered DirectoryImage sp)
  =
  fresh_root_layout (sp_program sp)

Also prove:

- image go.mod is the one root go.mod entry;
- image file-map keys are exactly the source program FilePaths;
- no extra image entry exists;
- fresh materialization preserves those keys and bytes before the build;
- build-plan output target classification over the program equals classification over the actual image.

The semantic elaborator may derive the plan from GoProgram because the bridge proves that the later DirectoryImage
realizes the same layout.

Do not make GoCompile import GoRender or GoEmit.

Place the bridge theorem downstream, preserving dependency direction.

===============================================================================
9. PACKAGE SOURCE SEMANTICS
===============================================================================

Fix the current accidental factorization.

The present grammar can express only:

  package main
  func main() { ... }

The old primitive rule:

  every package has exactly one DMain

matches current source acceptance, but combines two independent Go rules.

Define:

  PackageDeclsUnique
  MainPackagesHaveEntry
  PackageRulesValid
  SourceProgramValid

Conceptually:

  Definition PackageDeclsUnique (p : GoProgram) : Prop :=
    forall dir bucket,
      bucket_for dir p = bucket ->
      length bucket <= 1.

  Definition MainPackagesHaveEntry (p : GoProgram) : Prop :=
    forall dir bucket,
      bucket_for dir p = bucket ->
      1 <= length bucket.

  Definition PackageRulesValid p :=
    PackageDeclsUnique p /\ MainPackagesHaveEntry p.

  Definition SourceProgramValid p :=
    ProgramTyped p /\ PackageRulesValid p.

Meaning:

PackageDeclsUnique:
- every current DMain binds package-block identifier `main`;
- at most one prevents package-block redeclaration.

MainPackagesHaveEntry:
- every current package is named main;
- every DMain is intrinsically `func main()` with no type parameters, parameters, or results;
- at least one supplies the command entry.

Prove universally:

  current_package_rules_exactly_one :
    PackageRulesValid p
    <->
    every represented package has exactly one DMain

Prove compatibility with the old source-only ProgValid definition.

Delete the old rule as the semantic root.

The compatibility theorem applies to source/compiler validity only.  Final GoCompile may now reject additional
source-valid programs because literal cmd/go output preflight fails.

Record future rules without implementing syntax:

- non-main packages need no main entry;
- a package-level `func main` in a non-main package is ordinary;
- methods do not bind their method name in the package block;
- a method named main is allowed and is not a command entry;
- init function declarations do not bind `init` and may repeat;
- blank identifier declarations do not bind;
- package-block uniqueness spans top-level const/type/var/function names across files;
- wrong-kind or wrong-signature `main` needs its own future diagnostics.

===============================================================================
10. PACKAGE SELECTION FOR `./...`
===============================================================================

Model the package set selected by the literal pattern in the current represented subset.

The selected package identity is the package directory key:

  root package -> ""
  nested package -> FilePath parent directory

For current source:

  selected packages
  =
  domain of retained package main-ref buckets
  =
  domain of package summaries
  =
  distinct parent directories of represented FilePaths

Use the standard PackageMap domain.

Do not create a list-backed set.

A canonical package enumeration may use standard map elements as a derived list.

Required theorems:

- every represented file contributes to exactly one selected package;
- every selected package has a represented file;
- empty program selects zero packages;
- files in one directory select one package;
- distinct directories select distinct packages;
- construction order does not affect the package set;
- current FilePath restrictions make every represented package visible to `./...`;
- no represented package lies under a Go-ignored directory class;
- no nested module splits the selected set.

===============================================================================
11. PACKAGE IMPORT PATH
===============================================================================

Define the exact import path cmd/go assigns to a selected package in the main module:

  root package:
    ModulePath

  nested package dir:
    ModulePath + "/" + directory key

Use canonical source strings already carried by ModulePath and FilePath.

Required:

- no double slash;
- no trailing slash;
- root case exact;
- nested case exact;
- injective package-dir extension under one ModuleSpec;
- deterministic under equal ModuleSpec + equal package key.

The import path is semantic input to default executable naming.

===============================================================================
12. DEFAULT EXECUTABLE NAME
===============================================================================

Define:

  is_version_element : string -> bool
  default_exec_name : string -> string

Pin the exact Go 1.23 module-aware rule.

`default_exec_name import_path`:

1. Split the import path at its final slash.
2. Let final be the last component.
3. If there is at least one earlier component and final satisfies is_version_element:
   - return the previous component.
4. Otherwise:
   - return final.

Do not use filesystem path cleaning.  Inputs are canonical import paths.

Prove reflection for is_version_element.

Required computed fixtures:

  v0      false
  v00     false
  v01     false
  v05     false
  v1      false
  v2      true
  v3      true
  v10     true
  v100    true
  v1x     false
  v2x     false
  V2      false
  v       false

Required name fixtures:

  example.com/m               -> m
  example.com/m/sub           -> sub
  example.com/m/a/b           -> b
  example.com/m/a/v2          -> a
  example.com/m/v2            -> m
  example.com/main.go         -> main.go
  example.com/go.mod          -> go.mod
  example.com/m/sub/v10       -> sub

Prove result is nonempty for every represented package import path.

Linux/amd64 adds no `.exe` suffix.

===============================================================================
13. FRESH BUILD PLAN
===============================================================================

Define a retained pure plan.

Suggested shape:

  Inductive FreshBuildDisposition (p : GoProgram) :=
  | FBDNoPackages
  | FBDDiscardMultiple
      (packages : list (PackageRef p))
      (count_ge_two : ...)
  | FBDDiscardSingleLibrary
      (package : PackageRef p)
  | FBDWriteSingleMain
      (package : PackageRef p)
      (import_path : string)
      (output_name : string)
      (target : option FreshRootEntryKind).

The current grammar cannot produce the single-library branch.  Keep it out of the live inductive if that would
be speculative.  At minimum, document the future branch and make the current constructor set exact.

For the current grammar:

- zero package domain:
    FBDNoPackages

- package domain cardinal >= 2:
    FBDDiscardMultiple

- package domain cardinal = 1:
    FBDWriteSingleMain

The plan must use:

- retained canonical package map;
- ModuleSpec;
- fresh root layout.

It must not:

- traverse syntax again;
- rebuild GoIndex;
- render source;
- inspect emitted bytes;
- call cmd/go;
- scan a dirty filesystem.

Define:

  fresh_build_preflight_ok : FreshBuildPlan p -> Prop

Current rule:

  target = directory
    false

  target = absent
    true

  target = go.mod regular file
    true

  target = source regular file
    true

  no packages
    true

  multiple packages
    true

The plan should record overwrite/create disposition on success:

  create absent output
  overwrite go.mod
  overwrite source file
  discard outputs
  no packages

This is evidence and diagnostics, not a source rewrite.

===============================================================================
14. CMD/GO PHASE ORDER
===============================================================================

Model the current relevant command order.

The literal command does not first run the whole compiler and then decide where to write.

Relevant current order:

1. Package discovery/loading.
2. If exactly one main package, derive default output name.
3. Stat default output.
4. If it is a directory, fail immediately.
5. Otherwise compile and link packages.
6. If one main package succeeds, create/replace default output.
7. If multiple packages or one non-main package succeeds, discard outputs.

Current AST makes step 1 valid by construction.

Therefore define final acceptance:

  GoCompile p :=
    fresh_build_preflight_ok (fresh_build_plan p)
    /\
    SourceProgramValid p

This conjunction is the acceptance condition.

But diagnostic exposure must follow cmd/go order:

  if fresh build preflight fails:
    report only the output-directory diagnostic

  else:
    report the current semantic/compiler diagnostics

This means a sole package under `sub/` may report only:

  build output "sub" is an existing directory

even when the source also contains:

- invalid conversion;
- duplicate main;
- missing main entry.

That is deliberate.

For multiple packages, there is no default output preflight, so semantic diagnostics remain visible.

Prove:

- preflight failure implies not GoCompile;
- semantic diagnostics are consulted only after preflight success;
- final diagnostics empty iff GoCompile;
- output-collision report has precedence over semantic diagnostics;
- no output-collision diagnostic is emitted for zero or multiple selected packages;
- no output-collision diagnostic is emitted for an absent or regular-file target.

Do not claim exact compiler stderr after preflight success.

===============================================================================
15. STRUCTURED DIAGNOSTICS
===============================================================================

Rename source package diagnostics:

  DCDuplicateMain
    ->
  DCMainRedeclared

  DRDuplicateMain
    ->
  DRMainRedeclared

  DCMissingMain
    ->
  DCMissingMainEntry

  DRMissingMain
    ->
  DRMissingMainEntry

Add:

  DCBuildOutputIsDirectory

  DRBuildOutputIsDirectory
    (package : PackageRef p)
    (output_name : string)

Primary anchor:

  AtPackage package

Payload:

  exact default output name

Soundness:

- exactly one package is selected;
- the package name is main in current source;
- reported package is the sole package;
- reported output name equals default_exec_name of its import path;
- fresh root layout maps that name to FREDirectory;
- cmd/go preflight model rejects;
- GoCompile p is false.

Completeness in current represented scope:

- every fresh preflight failure yields exactly one DRBuildOutputIsDirectory;
- no other command-level preflight failure exists.

Source diagnostic meaning:

DRMainRedeclared:
- package-block identifier `main` is redeclared;
- later declaration primary;
- first canonical declaration related;
- n mains produce n-1 diagnostics in the semantic report.

DRMissingMainEntry:
- represented package named main has no package-level valid `func main()`;
- package anchor;
- empty DMain bucket.

Final report precedence may hide those semantic diagnostics behind a build-output collision.

Keep a separate pure semantic report for theorem use:

  semantic_diagnostics

Define the command-facing report:

  elaboration_diagnostics

as:

  output collision singleton
  OR
  semantic_diagnostics

Never concatenate both branches.

Update:

- erased diagnostics;
- formatter;
- legacy projection;
- exact fixtures;
- gate surfaces;
- docs.

Add a distinct legacy class if compatibility projections remain:

  LCBuildOutput

Do not classify the collision as typing or package-main count.

===============================================================================
16. ELABORATION VOCABULARY
===============================================================================

Apply the agreed naming now.

Rename:

  analyze
    -> elaborate

  analyze_indexed
    -> elaborate_indexed

  AnalysisResult
    -> ElaborationResult

  ProgramAnalysis
    -> ProgramElaboration

  AnalysisOK
    -> ElaborationOK

  AnalysisFailed
    -> ElaborationFailed

  CompilationFacts
    -> ElaborationFacts

  analysis_ok_b
    -> semantic_ok_b or source_program_ok_b

  analyze_valid_of_no_diags
    -> elaborate_valid_of_no_diags

  analyze_result_cases
    -> elaboration_result_cases

  analyze_ok_sig
    -> elaboration_ok_sig

  analyze_ok_full
    -> elaboration_ok_full

  analyze_ok_*
    -> elaborate_ok_*

  analyze_failed_*
    -> elaborate_failed_*

ProgramElaboration fields:

  pe_indexed
  pe_result

ElaborationFacts fields should use a consistent prefix that does not collide with ExprFact:

  elab_expr_facts
  elab_package_refs
  elab_root_layout
  elab_build_plan
  elab_source_valid
  elab_valid

Exact factoring may vary.

Keep:

  GoCompile
  CompilableProgram
  CompileOutcome
  go_compile
  GoCompile.v

The physical module rename remains C6 work.

Provenance becomes:

  cp_prov :
    elaborate cp_program
    =
    mkProgramElaboration cp_index (ElaborationOK cp_facts)

Delete dead generic result/bool helpers if no call site remains.

Do not leave live compatibility aliases for the old analysis names.

===============================================================================
17. ONE RETAINED ELABORATION
===============================================================================

Retain the one-pass C3 implementation.

Conceptual flow:

  elaborate p :=
    let ip := GoIndex.index_program p in
    mkProgramElaboration ip (elaborate_indexed p ip)

  elaborate_indexed p ip :=
    let idx          := indexed_syntax ip in
    let blocks       := prog_blocks p in
    let visit        := concat blocks in
    let status       := one bottom-up status map in
    let package_refs := one package bucket map in
    let expr_facts   := one fact map in
    let root_layout  := one standard root-entry map derived from FilePaths in
    let build_plan   := one pure plan from ModuleSpec + package_refs + root_layout in
    let semantic_raw := current source diagnostics in
    let semantic_ds  := canonical semantic diagnostics in
    let final_ds     :=
      match build_plan with
      | directory collision => singleton build diagnostic
      | _                   => semantic_ds
      end
    in
    if final_ds is empty
    then ElaborationOK exact facts
    else ElaborationFailed final_ds

The one-pass source work stays one-pass.

Root layout and build plan may fold canonical FileMap/PackageMap elements once.  They must not invoke visit_file.

ElaborationFacts on success retain:

- expression facts;
- package main refs;
- root layout or enough exact build-layout evidence;
- FreshBuildPlan;
- SourceProgramValid proof;
- final GoCompile proof.

No facts escape on failure unless the existing public design intentionally exposes a separate non-capability report.  Do not create a typed AST.

===============================================================================
18. DECLARATIVE AND EXECUTABLE EXACTNESS
===============================================================================

Prove:

A. Source semantics

  semantic_diagnostics p ip = []
  <->
  SourceProgramValid p

B. Fresh preflight

  fresh_build_diagnostics p plan = []
  <->
  fresh_build_preflight_ok plan

C. Final command-facing diagnostics

  elaboration_diagnostics p ip plan = []
  <->
  GoCompile p

D. Elaboration success

  exists facts,
    pe_result (elaborate p) = ElaborationOK facts
  <->
  GoCompile p

E. Elaboration failure

  exists ds Hne,
    pe_result (elaborate p) = ElaborationFailed ds Hne
  <->
  ~ GoCompile p

F. Failure precedence

  preflight fails
  ->
  elaboration diagnostics = [DRBuildOutputIsDirectory ...]

G. Semantic branch

  preflight succeeds
  ->
  elaboration diagnostics = semantic diagnostics

H. Compiler projection

  go_compile projects one elaborate result
  and never runs prog_ok or another checker

I. Retention

  every CompilableProgram retains:
    exact program
    exact index
    exact ElaborationFacts
    exact FreshBuildPlan
    provenance from ElaborationOK

J. Downstream image bridge

  every DirectoryImage reachable from CompilableProgram realizes the retained fresh root layout and build plan.

The final equivalence to external cmd/go remains differential evidence, not a Rocq theorem importing Go.

===============================================================================
19. DETERMINISM THEOREMS
===============================================================================

Split source-only and full-command determinism correctly.

Source facts/semantic diagnostics depend only on the file map:

- keyed visit;
- expression facts;
- package buckets;
- semantic diagnostic report.

Retain or rename FilesEqual theorems for those.

FreshBuildPlan also depends on ModuleSpec because package import paths and default executable names use the module
path.

Define a full input equality:

  ProgramInputEqual p1 p2 :=
    prog_module p1 = prog_module p2
    /\
    FilesEqual (prog_files p1) (prog_files p2)

Prove:

- equal program inputs -> equal root layouts;
- equal program inputs -> equal package import paths;
- equal program inputs -> equal FreshBuildPlans;
- equal program inputs -> equal erased final reports;
- equal program inputs -> equal acceptance class;
- permuted file-node construction under the same ModuleSpec -> equal full result.

Do not claim full final-report equality from FilesEqual alone.

Add a counterexample fixture with:

- equal file maps;
- different ModuleSpecs;
- equal semantic diagnostics;
- different output names or output target classes;
- different FreshBuildPlans;
- where feasible, different final acceptance.

Choose valid current ModulePaths.

===============================================================================
20. CURRENT REQUIRED ROCQ FIXTURES
===============================================================================

Keep all accepted C3 source fixtures and update names.

Add:

20.1 Empty image

  no packages
  FBDNoPackages
  preflight succeeds
  SourceProgramValid
  GoCompile
  no diagnostics

20.2 One valid root package, absent output

  module path basename does not match go.mod/source/root dir
  output target absent
  plan writes one executable
  preflight succeeds
  GoCompile

20.3 Sole immediate child package

  file: sub/main.go
  module: example.com/m
  sole package import path: example.com/m/sub
  output name: sub
  fresh root has directory sub
  preflight fails
  final report exactly one build-output-directory diagnostic
  no semantic diagnostic exposed
  not GoCompile

20.4 Immediate child with semantic error

  sub/main.go contains invalid conversion or no DMain
  same output collision
  final report remains only build-output-directory
  proves precedence

20.5 Sole deeper package

  file: a/b/main.go
  output name b
  fresh root directory is a, not b
  target absent
  preflight succeeds
  if source valid, GoCompile succeeds

20.6 Final v2 package path

  file: a/v2/main.go
  import path example.com/m/a/v2
  output name a
  root directory a exists
  preflight fails

20.7 Immediate v2 package

  file: v2/main.go
  import path example.com/m/v2
  output name m
  root directory v2 does not collide with m
  preflight succeeds when m absent

20.8 Multiple main packages

  a/main.go
  b/main.go
  FBDDiscardMultiple
  no output preflight failure
  source-valid program succeeds
  no default a/b executable in external post-state

20.9 Multiple packages with semantic failure

  no default-output collision branch
  semantic diagnostics exposed

20.10 go.mod overwrite

  one root package
  ModulePath final component = go.mod
  output name go.mod
  target regular go.mod
  preflight succeeds
  GoCompile succeeds if source valid
  plan records overwrite

20.11 source overwrite

  root source file main.go
  ModulePath final component = main.go
  output name main.go
  target regular source file
  preflight succeeds
  GoCompile succeeds if source valid
  plan records overwrite

20.12 root source name collision without exact module match

  prove output target lookup is exact string identity.

20.13 Three mains

  semantic report has n-1 MainRedeclared diagnostics
  if a build-output directory collision exists, final report hides them
  if preflight succeeds, final report exposes them

20.14 Missing main entry

  same two branches:
    preflight collision hides;
    preflight success exposes missing entry.

20.15 Reordered construction

  same ModuleSpec
  equal full plan/report/outcome.

20.16 Equal files, different module

  source facts equal
  full plan not necessarily equal.

===============================================================================
21. PINNED EXTERNAL DIFFERENTIAL MATRIX
===============================================================================

Build one reusable test matrix in the exact pinned image.

Every case uses:

- a fresh disposable root;
- exact fixture manifest;
- pinned environment;
- literal `go build ./...` once.

Assert:

- exit status;
- stable error substring where useful;
- expected default output presence/absence;
- expected overwrite class;
- no authoritative source mutation outside the disposable root.

Required external cases:

A. go.mod only
   success, no packages warning, no executable

B. valid root main, absent output
   success, executable created

C. package main with no func main
   failure when output target is not a directory

D. duplicate main in one file
   failure when output target is not a directory

E. duplicate main across files
   failure when output target is not a directory

F. three main declarations
   failure

G. two valid command packages
   success, default outputs discarded

H. valid and invalid package together
   failure

I. empty file plus main elsewhere
   success

J. sole sub/main.go
   failure: build output "sub" exists and is a directory

K. sole sub/main.go with invalid source
   same directory-collision failure class, proving precedence

L. sole a/b/main.go
   success, executable b at root

M. sole a/v2/main.go
   failure: output a is directory

N. sole v2/main.go
   success, executable named after module basename

O. module basename go.mod
   success, go.mod replaced by executable in disposable root

P. module basename main.go with root main.go source
   success, main.go replaced by executable in disposable root

Q. existing absent output
   create

R. existing regular output
   overwrite

S. existing directory output
   reject

T. two init functions plus valid main
   success

U. method named main without package-level main
   missing entry failure

V. method named main plus package-level main
   success

W. wrong-signature main
   failure

X. generic main
   failure

Y. var/type named main
   failure

Z. mixed package clauses
   package-load failure before output preflight

AA. `_test.go` duplicate only
    ignored by build

AB. `_ignored.go` duplicate only
    ignored

AC. package documentation only
    no selected package

AD. two modules with equal file layout but different module basename
    demonstrate different output names/plans

For cases not representable by Fido yet, keep them as pinned future oracles.  Do not add syntax.

For every representable case, compare:

  expected Fido class
  actual literal command exit

The output-neutral command:

  go list ./...
  go build -o /dev/null <each selected package>

may be used only as a diagnostic to distinguish source/compiler validity from output preflight.  It is not the
acceptance oracle.

===============================================================================
22. PRODUCTION RUNNER INTEGRATION
===============================================================================

Centralize the production build call.

Add one reusable wrapper or executable used by:

- canonical generated witness;
- multi-package witness;
- empty module witness;
- boundary-byte witness;
- every future DirectoryImage output;
- CI;
- release validation;
- documented local build path.

Do not keep one raw `go build ./...` body per output.

The wrapper should accept only a pristine authoritative image export.

Recommended operation:

  authoritative image
      |
      v
  validate exact manifest
      |
      v
  make fresh temp root
      |
      v
  materialize exact bytes
      |
      v
  verify pre-build manifest/bytes
      |
      v
  run pinned literal command once
      |
      v
  record status
      |
      v
  discard root

If runtime production uses a container, make the pinned container target the canonical runner.

A host helper may invoke that container.  Do not silently use the host Go installation.

Do not run the build after sinking into a user directory.

Recommended ordering:

  prove/certify
  render DirectoryImage
  pristine export
  fresh build validation
  only then publish/sync original DirectoryImage

A failed build must prevent publication.

If current Fido Emit performs sink effects before the build validation, refactor the pipeline so the authoritative
pristine image is build-validated first.  Do not weaken sink safety.

===============================================================================
23. DOCKERFILE AND ARTIFACT FLOW
===============================================================================

Update the Docker stages so the invariant is visible.

Current good root:

  generated-module
    exact go.mod + `.go`
    no control state

Retain it.

Generalize:

- create pristine exports for multi, empty, bytes, and future witnesses;
- do not feed `/workspace/e2e-*` sink trees directly to the build stage if they contain `.fido`;
- invoke the central fresh-build runner for every pristine export;
- make literal command failure blocking;
- inspect disposable post-build roots for special fixtures;
- preserve the authoritative pristine export for byte comparison.

The canonical generated source artifact must be copied from the pre-build pristine layer, never from a post-build
root.

`make regenerate` and sink sync must consume the original pristine layer.

The build stage may produce a separate status artifact.  It must not alter generated source artifacts.

===============================================================================
24. SOURCE BYTE IDENTITY
===============================================================================

All pre-existing accepted witnesses must render byte-identical go.mod and `.go` files.

New negative/edge fixtures may use distinct generated trees.

For overwrite-success fixtures:

- compare authoritative bytes before build;
- run build in disposable copy;
- prove post-build file became executable;
- discard copy;
- verify authoritative bytes are unchanged.

Do not compare source bytes after running Go in the same tree.

The final closing byte check uses:

  pristine generated-module layer
  versus
  committed go.mod and recursive `.go`

exactly as before.

===============================================================================
25. COLLECTIONS AND PERFORMANCE
===============================================================================

Use standard collections:

- FileMap for source files;
- PackageMap for selected package/package facts;
- NodeKeyMap for occurrence facts/diagnostics;
- PackageMap or another pinned standard string map for root entries.

Lists remain appropriate for:

- canonical derived elements;
- source order;
- diagnostic report order;
- duplicate-preserving main buckets.

Do not invent:

- root-entry association lists;
- package sets as list + NoDup;
- custom sort;
- custom trie;
- custom path map.

Performance requirements:

- one retained syntax visit;
- one standard-map package fold;
- one root-layout fold over canonical file bindings;
- one build-plan lookup;
- no per-package scan of all files;
- no per-output scan of all root entries beyond standard map lookup;
- no rendering in elaboration;
- no cmd/go invocation in Rocq.

Run scale probes for:

- 1, 10, 100, practical 1,000 files;
- 1, 10, 100 packages;
- root-layout construction;
- package-plan construction;
- output target lookup.

Report observations honestly.  Do not claim a machine complexity theorem without proving it.

===============================================================================
26. GATE SURFACES
===============================================================================

Update the readable gate.

Package semantics:

- PackageDeclsUnique reflection;
- MainPackagesHaveEntry reflection;
- PackageRulesValid exactness;
- current_package_rules_exactly_one;
- SourceProgramValid compatibility.

Package selection:

- selected package domain exactness;
- empty selection;
- one-directory coalescing;
- distinct-directory separation;
- construction permutation.

Import path and executable name:

- package_import_path root;
- package_import_path nested;
- is_version_element reflection;
- required vN fixtures;
- default_exec_name exact fixtures;
- nonempty result.

Fresh root layout:

- root layout domain;
- root source exactness;
- root directory exactness;
- file/directory disjointness;
- layout determinism;
- DirectoryImage layout bridge.

Build plan:

- zero package plan;
- multiple package plan;
- single main plan;
- target absent;
- target go.mod regular;
- target source regular;
- target directory;
- preflight reflection;
- overwrite accepted;
- directory collision rejected.

Diagnostics:

- main redeclared soundness;
- n-1 exactness;
- missing main entry soundness;
- build-output-directory soundness;
- build-output-directory completeness;
- preflight precedence;
- semantic branch exactness;
- final diagnostics empty iff GoCompile;
- strict source diagnostic order;
- erased final diagnostic determinism.

Elaboration:

- elaborate OK iff GoCompile;
- elaborate failed iff not GoCompile;
- failure nonempty;
- go_compile projection;
- retained index;
- retained facts;
- retained FreshBuildPlan;
- CompilableProgram provenance.

Determinism:

- FilesEqual source facts/report;
- ProgramInputEqual full plan/report;
- construction permutation full result.

Downstream:

- DirectoryImage realizes plan layout;
- rejected elaboration cannot produce CompilableProgram/SafeProgram/DirectoryImage;
- successful emitted image retains original source bytes.

Remove replaced gate names.  The gate count may change.  It must match exactly.

===============================================================================
27. DOCUMENTATION RECONCILIATION
===============================================================================

Update:

- GoCompile.v permanent header;
- GoAST.v DMain comments;
- GoIndex.v stale C2-progress header;
- GoTypes.v wording;
- GoSafe.v projections;
- GoRender.v / GoEmit.v bridge prose;
- ModulePath.v build-alarm wording;
- Dockerfile;
- dune synopsis;
- Makefile comments/targets;
- ARCHITECTURE.md;
- CLAUDE.md;
- PROGRESS.md;
- README.md;
- PAINFUL_LESSONS.md;
- SOURCE_FOREST_MASTER_PLAN.md;
- SOURCE_FOREST_STATUS.md;
- COLLECTION_AUDIT.md;
- CODEX_REVIEW_POLICY.md;
- axiom gate comments;
- e2e comments.

Permanent architecture wording:

  GoCompile
    exact acceptance model for the pinned one-shot fresh `go build ./...`

  SourceProgramValid
    Go source/compiler/package part

  FreshBuildPlan
    cmd/go package selection and default-output part

  elaborate
    one retained semantic execution producing facts or command-ordered diagnostics

  DirectoryImage
    immutable authoritative source image

  fresh build root
    disposable command workspace

  sink
    publication of the original image, never the post-build tree

Remove live claims that:

- every Go package needs exactly one main;
- duplicate main is a special count rule;
- analysis is the permanent phase name;
- full reports depend only on file maps;
- raw `go build ./...` against any directory is the contract;
- sink destination is the build input;
- output placement is ignored.

Remove stale old checkpoint headings that say ACTIVE.

===============================================================================
28. PAINFUL LESSONS
===============================================================================

Add concise durable lessons.

1. Accidental subset equivalence

  A combined rule can match a narrow grammar while factoring the language incorrectly.  Separate package-block
  name uniqueness from main-package entry validity before adding non-main packages or other declarations.

2. Exact tool contracts include strange side effects

  If production invokes literal `go build ./...`, default executable naming and directory collisions are part of
  acceptance.  Do not replace the command with a cleaner per-package approximation.

3. Freshness is a semantic input

  Cmd/go's result can depend on existing filesystem entries.  Make the build root a fresh materialization of the
  certified image so semantic analysis has a closed input.

4. Never publish a mutated build workspace

  A successful sole-command build may overwrite go.mod or source.  Build only in a disposable copy and publish
  the original DirectoryImage.

5. Match phase order

  Cmd/go checks a sole command's output directory before compiler execution.  A correct report must let that
  preflight failure take precedence over later semantic errors.

Keep each lesson brief and non-repetitive.

===============================================================================
29. PRE-CODEX AUDIT
===============================================================================

Freeze one candidate SHA.

Run a whole-candidate audit before stopping.

A. One authority

- elaborate is the only semantic root.
- go_compile only projects elaborate.
- no analyze entrypoint remains.
- no production prog_ok call.
- no second index.
- no second visit.
- no second package decision.
- no second build-plan decision.

B. Source/package semantics

- exactly-one-main is not primitive.
- uniqueness and entry are separate.
- current equivalence theorem is universal.
- future library/method/init rules are correct.
- diagnostics renamed.

C. Fresh build plan

- package domain exact.
- import path exact.
- vN rule exact.
- output target from standard root map.
- ordinary files accepted.
- directories rejected.
- ModuleSpec included.
- no renderer dependency in GoCompile.
- downstream image bridge exists.

D. Phase order

- output collision checked before semantic diagnostic exposure.
- collision hides later semantic diagnostics for sole package.
- multiple packages expose semantic diagnostics.
- empty package succeeds.

E. Production runner

- one central wrapper.
- exact pinned image.
- exact command.
- GOENV off.
- GOFLAGS empty.
- fresh root every invocation.
- exact manifest.
- no `.fido`.
- no VCS.
- build once.
- post-build root discarded.
- original image published.
- every output uses wrapper.
- no dirty sink build.

F. Tests

- full Rocq fixture set.
- full pinned-Go matrix.
- overwrite fixtures disposable.
- output-neutral build diagnostic only.
- source bytes checked pre-build.

G. Prose

- no live old analysis vocabulary.
- no stale C2 progress.
- no old ACTIVE checkpoint.
- no competing repair plan.
- no file-map-only full-result claim.

H. Trust

- zero axioms.
- readable gate exact.
- whole-theory audit.
- full check.
- staged check.
- byte identity.
- no C4 work.

===============================================================================
30. CODEX FINAL REVIEW
===============================================================================

Commit the complete candidate:

  review(final): C3 — exact fresh-image parity with literal pinned go build all

Run one exhaustive discovery review over:

  a812812d0ae311471c672bde0bbbcea057135ca6
  ..
  candidate

Tell Codex:

> Review the entire frozen C3 checkpoint.  Do not stop after the first blocker.  Return every independently
> visible defect.  Attack source package semantics, cmd/go phase order, package selection, default executable
> naming, vN handling, fresh root layout, regular overwrite, directory collision, one-elaboration authority,
> occurrence facts, diagnostic exactness/order, DirectoryImage bridging, production fresh-materialization
> enforcement, pinned environment, destructive test isolation, collections, performance, gates, docs, and stale
> names.

Codex must specifically look for:

- exactly-one-main still primitive;
- methods treated as package-block names;
- init treated as a binding;
- missing future library rule;
- wrong v0/v1/v2 behavior;
- output name based only on directory, not import path;
- ModuleSpec omitted;
- go.mod/source overwrite rejected;
- existing directory accepted;
- sole sub package accepted;
- a/b package rejected;
- a/v2 rule wrong;
- collision checked after semantic diagnostics;
- semantic errors exposed alongside preflight collision;
- build plan reconstructs index or revisits syntax;
- root layout uses list-backed identity;
- file/dir prefix conflict ignored;
- no DirectoryImage bridge;
- full report claims FilesEqual-only determinism;
- build runs in sink tree;
- wrapper builds input in place;
- wrapper copies `.fido` or extras;
- GOENV/GOFLAGS ambient state;
- host Go used;
- build runs twice in one root;
- post-build tree feeds publication;
- destructive fixture damages authoritative bytes;
- output-neutral command used as authority;
- stale analysis names;
- gate or assumption drift;
- generated source-byte drift;
- accidental C4 work.

Repair the full finding batch.

Run one confirmation review.

After non-stale GREEN:

1. run full `make check`;
2. run the entire pinned fresh-build matrix;
3. run staged-tree verification;
4. verify pristine generated source bytes;
5. verify all production output paths use the fresh runner;
6. update status with:
   - contract SHA;
   - candidate SHA;
   - repair SHAs;
   - review task/timestamp/result;
   - final gate count;
   - toolchain identity;
   - fresh-build matrix result;
   - source-byte result;
   - push result;
   - C3 human disposition pending;
7. fast-forward push;
8. notify Rob;
9. stop the loop;
10. do not begin C4.

===============================================================================
31. FORBIDDEN
===============================================================================

Do not add:

- arbitrary package-name syntax;
- identifiers;
- general declarations;
- methods;
- init syntax;
- imports;
- parameters/results;
- type parameters;
- source spans;
- C4 type names;
- C5 numeric work;
- structural types;
- operations.

Do not:

- build in a sink destination;
- build in a repository checkout;
- build an authoritative tree in place;
- publish from a post-build root;
- normalize literal `go build ./...` into `-o /dev/null`;
- reject regular-file overwrite;
- accept directory collision;
- ignore ModuleSpec in full planning;
- compute plan from rendered text;
- import GoRender/GoEmit into GoCompile;
- add a second checker;
- add a custom collection;
- add a custom sort;
- weaken current proofs;
- split large modules physically;
- change existing generated source bytes;
- claim exact external Go behavior as a kernel theorem;
- claim exact stderr or executable bytes;
- begin C4.

If the actual pinned Go 1.23.2 behavior contradicts this directive, record:

  PINNED-GO CONTRACT CONFLICT

with the exact fixture, command, environment, output, and source path.  Stop.  Do not silently choose the plan over
the observed toolchain.

===============================================================================
32. ACCEPTANCE
===============================================================================

C3 is complete only when:

- C2 remains accepted;
- package uniqueness and entry are separate;
- old exactly-one source rule is only a proved consequence;
- analysis vocabulary is gone;
- elaboration vocabulary is live;
- one retained elaboration remains;
- FreshRootLayout is standard-map-backed and exact;
- layout conflicts are proved impossible or rejected;
- package selection for current `./...` is exact;
- package import path is exact;
- default executable name matches pinned Go;
- vN rule matches pinned Go;
- FreshBuildPlan is retained;
- regular-file create/overwrite succeeds;
- directory collision rejects;
- output collision has cmd/go precedence;
- final diagnostics empty iff GoCompile;
- full plan/report uses ModuleSpec + files;
- DirectoryImage realizes the plan layout;
- every build uses a fresh exact image;
- every build uses the pinned literal command;
- no build uses sink state;
- no post-build byte is published;
- all output types use one runner;
- zero assumptions;
- full gate green;
- full check green;
- pinned matrix green;
- staged check green;
- generated source bytes unchanged;
- exhaustive Codex discovery complete;
- confirmation Codex GREEN;
- fast-forward pushed;
- loop stopped;
- C4 not begun.

===============================================================================
33. FINAL ARCHITECTURE
===============================================================================

Source:

  GoProgram
    ModuleSpec
    FileMap FilePath GoSourceFile

Structure:

  IndexedProgram
    one SyntaxIndex

Semantic source relations:

  GoTypes
    const_info_step
    convert_const
    resolve_const_info
    ProgramTyped

Package source rules:

  PackageDeclsUnique
  MainPackagesHaveEntry
  PackageRulesValid
  SourceProgramValid

Fresh layout:

  RootEntryMap
    go.mod regular
    root source regular
    root directory

Cmd/go plan:

  selected package domain
  package import path
  default executable name
  FreshBuildPlan
    no packages
    discard multiple
    write single main
  preflight:
    regular/absent -> continue
    directory -> fail

Final acceptance:

  GoCompile
    fresh preflight succeeds
    AND
    SourceProgramValid

Semantic execution:

  elaborate
    one index
    one visit
    one status pass
    one fact map
    one package map
    one root layout
    one build plan
    command-ordered diagnostics

Capability:

  CompilableProgram
    original program
    exact index
    exact ElaborationFacts
    exact FreshBuildPlan
    provenance from ElaborationOK

Rendering:

  SafeProgram
    ->
  original source rendering
    ->
  DirectoryImage

Production:

  DirectoryImage
    ->
  fresh exact materialization
    ->
  pinned literal `go build ./...` once
    ->
  discard build root

Publication:

  original DirectoryImage
    ->
  sink

The AST owns source.
GoIndex owns occurrence structure.
GoTypes owns type and constant relations.
GoCompile owns exact fresh-build admission.
GoRender/GoEmit own authoritative source bytes.
The build runner owns the disposable cmd/go workspace.
The sink never supplies the compiler input.
