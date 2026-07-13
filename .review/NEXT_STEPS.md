Claude Code milestone: ModuleSpec, exact empty-program semantics, zero-assumption closure, and restoration of the agreed dirty-directory design

THIS FILE IS THE BINDING MILESTONE CONTRACT.

Before making any implementation change:

1. Create the tracked file `.review/NEXT_STEPS.md` if it does not exist.
2. Copy this directive into `.review/NEXT_STEPS.md` VERBATIM.
   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not “improve” the architecture while copying it.
3. Commit `.review/NEXT_STEPS.md` as the opening commit of this milestone, before implementation.
4. Record that contract commit SHA.
5. Treat `.review/NEXT_STEPS.md` as the binding scope, architecture, threat model, and acceptance contract for every implementation and Codex review in this milestone.

The Codex stop review must judge whether the implementation is airtight against `.review/NEXT_STEPS.md`. Codex must not broaden scope, strengthen the threat model, remove an explicitly required capability, move responsibilities, or select another architecture. If a real defect cannot be fixed while preserving this contract, classify it as an ARCHITECTURAL CONFLICT, notify the user, and stop. Do not redesign autonomously.

After one structural repair attempt in the same subsystem, any second proposed structural redesign is automatically an architectural conflict requiring human review.

This is one bounded, fixes-only milestone.

Stop every Ralph-style, autonomous, recursive, background, or iterative development loop before beginning.

After completing this milestone:

1. Run every required proof, build, differential, transport, filesystem, and end-to-end check.
2. Commit the completed checkpoint.
3. Notify the user through the configured phone/completion-notification channel that the checkpoint is ready for review.
4. Stop.
5. Do not infer or begin a next milestone.
6. Wait for joint review.

Standing project law

Ruthless correctness or ruthless deletion.

Incomplete scope is acceptable. Incorrect, approximate, duplicated, transitional, fail-open, or half-built foundations are not.

Every retained component must be complete and correct in itself and may build only on foundations that are already complete and correct.

The AST is the IR.

There is:

- one raw AST per `.go` file;
- one whole-program value;
- no copied compiled AST;
- no separate typed/target/text IR;
- no tokenizer;
- no token encoder;
- no lexer;
- no parser;
- no AST -> output -> AST round trip;
- no handwritten OCaml semantics, compiler, safety layer, lowering, or renderer.

No language feature growth in this milestone.

Do not add:

- imports;
- standard-library access;
- `fmt`;
- new builtins;
- strings;
- new numeric types;
- new operators;
- user-defined functions beyond the existing raw declaration shape;
- parameters/results;
- control flow;
- pointers;
- slices;
- maps;
- structs;
- interfaces;
- concurrency;
- package clauses in raw AST;
- another AST or IR.

This milestone repairs foundational correctness and the external boundary only.

Current baseline

The current formal shape is worth preserving:

  GoProgram
  -> GoCompile / CompilableProgram
  -> GoSafe / SafeProgram
  -> direct Rocq renderer
  -> DirectoryImage
  -> general Fido Emit transport
  -> dirty-directory filesystem sink
  -> pinned Go `go build ./...` integration alarm

Preserve:

- intrinsic `FilePath`;
- key-generic immutable finite maps;
- one AST;
- whole-program `GoCompile`;
- `SafeProgram` as the permanent safety capability;
- direct parser-free renderer;
- general `Fido Emit` command;
- emit-time assumption-closure validation;
- distinction between proof and integration evidence.

The milestone changes:

1. `GoProgram` gains an intrinsic `ModuleSpec`.
2. Empty source-file maps become valid programs.
3. The complete generated module, including `go.mod`, becomes certified output.
4. Foreign `.go` and foreign/nested `go.mod` files reject dirty-directory emission.
5. The zero-axiom gate becomes a true whole-certified-theory assumption-closure audit.
6. Codex’s central staging architecture is deleted.
7. The agreed local/per-destination-parent staging architecture is rebuilt correctly.
8. Filesystem discovery and cleanup become fail-closed.
9. `go vet` becomes nonblocking diagnostic output only.

1. Adopt ModuleSpec as part of GoProgram

Use this permanent program root:

  Record ModuleSpec := {
    module_path       : ModulePath;
    module_go_version : GoVersion
  }.

  Record GoProgram := {
    prog_module : ModuleSpec;
    prog_files  : fmap FilePath GoFileAST
  }.

`ModuleSpec` is not `TargetConfig`.

It describes the generated Go module itself:

- module import-path prefix;
- module-declared Go language version.

It does not describe ambient execution details:

- no GOOS;
- no GOARCH;
- no filesystem;
- no ABI;
- no scheduler;
- no exact point-release compiler binary;
- no architecture matrix.

The operational integration environment remains pinned separately.

The program authoring model remains conceptually:

  {
    module: ModuleSpec,
    files: dict[FilePath, GoFileAST]
  }

The raw `.go` file AST remains unchanged in responsibility:

- raw declarations only;
- no package clause;
- no imports;
- no package grouping;
- no entry-point flag;
- no resolved symbols/types;
- no copied compilation tree.

2. ModulePath is intrinsic and deliberately narrow

Do not use raw `string` as `module_path`.

Introduce an intrinsic `ModulePath` type with axiom-free decidable equality and a canonical rendering.

Do not attempt to formalize every module path accepted by every Go release.

Choose a deliberately narrow, permanent canonical subset such that every represented `ModulePath`:

- is nonempty;
- contains no whitespace, control bytes, backslash, NUL, `@`, query/fragment syntax, empty component, `.` component, or `..` component;
- has no leading, trailing, or repeated slash;
- uses a small reviewed lowercase-ASCII component grammar;
- is accepted by the pinned Go 1.23 toolchain as a `module` directive;
- can safely serve as the prefix of future closed-world package import paths;
- has one canonical byte rendering.

The exact grammar must be stated and proved through its validator/type.

Add positive and negative kernel fixtures.

Use focused official-Go research and toolchain experiments to confirm that every represented path is accepted.

Do not preserve invalid values and reject them later. Invalid module paths are unrepresentable.

The initial e2e may use a canonical module path such as:

  fido.local/generated

but `ModulePath` should be a real intrinsic type, not a singleton hidden string.

3. GoVersion is a semantic program fact, initially a singleton

Do not use raw string for the module Go version.

Begin with:

  Inductive GoVersion :=
  | Go1_23.

Provide:

- equality if needed;
- canonical rendering to `"1.23"`;
- theorem(s) pinning the exact rendered directive;
- documentation that adding a future constructor is a semantic milestone.

Adding `Go1_24` or any later version in the future requires, in that same reviewed milestone:

- formal treatment of every relevant language/compiler semantic difference for the represented AST;
- rendering support;
- differential fixtures under the matching pinned toolchain;
- no silent reuse of Go1_23 semantics if behavior changed.

Keep exact compiler binary/toolchain pinning outside `ModuleSpec`.

In integration, force the local pinned toolchain and disable automatic toolchain acquisition:

  GOTOOLCHAIN=local
  GOWORK=off

No network/toolchain auto-download may silently satisfy the module directive.

4. Empty GoProgram is valid

Delete the intrinsic nonempty proof from `GoProgram`.

The finite map may be empty.

Required behavior:

- `build_program module_spec []` succeeds.
- Empty `GoProgram` is accepted by `GoCompile`.
- Empty source-file map represents a valid generated Go module containing `go.mod` and no packages.
- Rendering produces `go.mod` and zero `.go` files.
- `go build ./...` over that emitted module is expected to exit successfully even if it warns that no packages matched.
- Emitting an empty program removes every prior Fido-owned generated `.go` file, while retaining/updating the Fido-owned `go.mod`.
- Foreign `.go` or foreign module files still cause refusal before generated-file mutation.

Update declarative and executable compiler theorems so empty-map acceptance is kernel-checked.

Remove:

- `prog_nonempty`;
- nonempty builders/proofs used solely for the old restriction;
- `render_program_nonempty`;
- all documentation that every `DirectoryImage` or source map is nonempty.

Do not introduce a special “empty program” constructor. It is simply the empty finite map under a valid `ModuleSpec`.

5. GoCompile consumes ModuleSpec and the whole source map

`GoCompile` remains whole-program and exact for every representable program.

The permanent intent remains:

  GoCompile accepts
  iff
  `GOWORK=off GOTOOLCHAIN=local go build ./...` accepts the complete rendered module

for every representable current-fragment `GoProgram`.

Rocq does not invoke `cmd/go`; it models the relevant rules independently.

For the current import-free fragment:

- `ModulePath` and `GoVersion` are already valid by construction;
- files group by parent directory;
- each nonempty discovered package is emitted as package `main`;
- each package has exactly one admitted `main` declaration;
- integer literals are representable;
- one invalid file/package rejects the entire program;
- multiple package directories may each contain a valid `main` package;
- the empty file map contains no packages and is accepted;
- imports remain unrepresentable.

Do not grow `CompilationFacts` merely because ModuleSpec exists.

It may remain minimal this milestone, provided:

- it is indexed by the same GoProgram;
- package/name facts used by rendering have one compiler authority;
- no raw AST metadata is introduced;
- documentation does not claim richer symbol/type/package facts than actually exist.

6. Render the complete module, including go.mod

The formal program currently relies on Docker to inject a handwritten `go.mod`. Delete that dishonesty.

Add direct Rocq rendering for the canonical module file.

The canonical generated `go.mod` must be derived solely from `ModuleSpec`.

Conceptual bytes:

  // fido generated.  do not edit.

  module <rendered ModulePath>

  go <rendered GoVersion>

Use the exact Fido generated header as the first line.

Prove at minimum:

- exact header first line;
- exact module-path rendering;
- exact Go-version rendering;
- all bytes satisfy the supported ASCII/canonical spelling constraints;
- rendering depends only on `ModuleSpec`;
- the pinned Go toolchain accepts every represented ModuleSpec in the current supported domain.

Do not add:

- `require`;
- `replace`;
- `exclude`;
- `retract`;
- `toolchain`;
- `godebug`;
- workspaces;
- vendor semantics;
- arbitrary raw directives.

Those remain absent until separately reviewed and modeled.

7. Make DirectoryImage structurally represent the complete module

Replace the current Go-files-only image with a structured module image.

Suggested permanent shape:

  Record DirectoryImage := {
    di_go_mod   : string;
    di_go_files : fmap FilePath string;
    di_prov     : exists sp,
      di_go_mod = render_go_mod sp /\
      di_go_files = render_go_files sp
  }.

Equivalent formulations are acceptable if they preserve the same responsibilities.

Do not weaken `FilePath` so it can represent `go.mod`.

`go.mod` and Go source files have different invariants:

- exactly one module file at root;
- zero or more `.go` files keyed by `FilePath`.

The public construction remains:

  render_program : SafeProgram -> DirectoryImage

The transport projection should expose structured final data, conceptually:

  exact go.mod bytes
  +
  list/map of exact `(relative .go path, contents)`

The sink must not invent `go.mod`.

The emitter must not accept a raw arbitrary project file map.

Update provenance theorems so every `DirectoryImage` is tied to the exact rendered `SafeProgram`, including both module file and Go files.

The emit-time assumption-closure check remains mandatory.

8. General transport remains program-blind

Update `Fido Emit` to typecheck and reduce the new structured `DirectoryImage`.

It may decode only:

- final `go.mod` bytes;
- final FilePath-denoted relative path strings;
- final `.go` contents.

It must not inspect:

- GoProgram;
- ModuleSpec semantics beyond final bytes;
- Go AST;
- CompilableProgram;
- SafeProgram;
- CompilationFacts;
- expressions/statements/declarations;
- behavior or safety proofs.

Preserve exact-constructor checks and fail-loud decoding.

Do not identify constructors by arity alone.

Do not create a witness-specific executable or extraction path.

9. Reject foreign Go and foreign/nested module files for now

The dirty-directory contract is intentionally strict this milestone.

Before staging, replacing, or deleting any generated program file, scan the target root fail-closed.

Allowed:

- no existing `.go`;
- existing Fido-owned generated `.go` files whose exact first line is the generated header;
- no existing root `go.mod`;
- an existing Fido-owned root `go.mod` whose exact first line is the generated header;
- arbitrary foreign non-Go files and directories that do not affect the modeled Go build;
- the owned `.fido` control namespace.

Reject:

- any foreign `.go` regular file anywhere beneath the target root;
- any `.go` symlink or nonregular `.go` entry;
- any foreign root `go.mod`;
- any root `go.mod` symlink/nonregular entry;
- any nested `go.mod` beneath the target root;
- any unreadable/uninspectable directory in the relevant scan;
- any filesystem error that prevents proving the absence of foreign Go/module inputs.

Do not decide foreign ownership by timestamps.

Installed Fido-owned `.go` and `go.mod` ownership remains the exact first-line header plus regular-file/non-symlink checks, rechecked immediately before overwrite/delete.

This strict refusal is deliberate.

Future support for foreign Go cannot be based merely on whether Fido imports it:

- same-directory foreign files automatically participate in a package;
- independent foreign packages can be selected by `go build ./...`;
- foreign initialization and declarations can change behavior.

Future foreign-Go support requires isolation or explicit modeling of every applicable foreign source file. Do not begin that work now.

For an empty desired source map:

- foreign Go/module input present -> reject and preserve everything;
- no foreign Go/module input -> update Fido-owned `go.mod` and remove all Fido-owned `.go`.

10. Replace filesystem query helpers with fail-closed results

Delete helpers that convert every filesystem exception into “missing.”

Only a confirmed `ENOENT` means absence.

Represent/handle filesystem observations as:

- Missing;
- Present metadata;
- Operational error.

Errors such as:

- EACCES;
- EIO;
- ELOOP;
- ENOTDIR;
- permission/search failure;
- malformed/unreadable directory;

must abort the operation.

Recursive discovery must not convert `readdir` failure into an empty directory.

Reading an ownership header must fail closed if the candidate cannot be read reliably.

The sink must never report success while being unable to establish the complete existing foreign/Fido-owned Go-file set.

Add mutation-sensitive tests for unreadable/unsearchable ordinary target directories, not only the staging namespace.

11. Delete Codex’s central staging architecture

Delete the current permanent design:

  <root>/.fido/staging/

Delete:

- the central staging directory;
- central-stage cross-device rejection;
- central-stage recovery logic;
- tests and prose that canonize this as the correct root;
- the current `PAINFUL_LESSONS.md` claim that structured central staging is the final answer.

The central design removed a capability we explicitly require: generated files may live beneath nested mount points inside the chosen target root.

Do not patch central staging to special-case mounts.

Replace it with the agreed architecture:

  one root-owned control namespace + lock
  +
  random local stage directories near each destination parent
  +
  durable root-owned records that identify those local stages

12. Root control namespace and lock

Keep one persistent owned control directory at:

  <root>/.fido/

It must have an exact ownership/version marker.

If `.fido` exists without the expected marker and expected directory shape, abort without modifying it.

Keep one root emission lock under `.fido`.

The lock coordinates cooperating Fido emitters.

Do not claim it protects against arbitrary noncooperating filesystem races.

Use a root-owned record namespace, for example:

  <root>/.fido/stage-records/

Everything inside that exact marked control namespace is Fido-owned by location.

Do not put staged payloads there; only ownership/recovery records.

13. Correct local-stage ownership protocol

For each distinct final parent directory receiving one or more desired files—including root for `go.mod` and root-level `.go` files—create one local stage directory in that parent.

Use a fixed hidden prefix and an OS-generated high-entropy nonce, for example:

  .fido-stage-<nonce>

Do not use OCaml `Random` as the sole nonce source.

Use an OS randomness source appropriate to the pinned Linux operational scope. Fail if secure/random nonce generation fails.

The protocol order is binding:

1. Choose the target parent and high-entropy nonce.
2. Derive the exact local stage relative path.
3. Verify no entry already exists at that local stage path.
4. Atomically create a unique record file under the owned root stage-record namespace using `O_CREAT|O_EXCL`.
5. Write a versioned, strict record that binds:
   - the nonce;
   - the exact canonical relative stage path;
   - the expected stage-parent path;
   - any identity fields required for fail-closed recovery.
6. Close and validate the complete record before creating the local stage directory.
7. Only after the complete record exists, create the local stage directory.
8. If stage-path creation reports a collision, preserve the colliding entry, remove the unused record, choose a new nonce, and retry or abort.
9. Stage only the files whose final parent is that stage’s parent.
10. Remove the record only after the corresponding local stage directory has been completely removed.

Threat model:

- cooperating Fido emitters are serialized by the lock;
- no guarantee against a malicious concurrent process guessing/replacing stage paths;
- high-entropy names prevent ordinary accidental collisions;
- foreign lookalikes without a valid root-owned record are never treated as owned.

Do not classify a local stage as owned by name alone.

Do not classify it by a marker inside the stage alone.

Do not use the public generated-file header as transient-stage ownership.

14. Stage the complete desired image before installation

This requirement is absolute.

The desired image consists of:

- root `go.mod`;
- every desired generated `.go` file.

Before the first final-file rename:

1. Preflight every target path and parent.
2. Create required parent directories carefully.
3. Create every local stage + durable record.
4. Write every desired output completely into its local stage.
5. Close every staged file.
6. Verify every desired output has staged successfully.

Only after the complete image is staged may installation begin.

Do not stage one file and immediately install it before later files are written.

This prevents ordinary staging failures such as disk exhaustion and permissions from creating a mixed generation.

The install/delete phase remains nontransactional across the entire tree. State that honestly.

15. Handled failure cleanup is immediate and verified

On every handled failure:

- attempt cleanup of every local stage created by this invocation;
- remove stage contents without following symlinks;
- remove the stage directory;
- remove its root-owned record only after stage removal succeeds;
- remove newly created parent directories only if still empty and known to have been created by this invocation;
- aggregate body, cleanup, and lock-release errors;
- report cleanup failure prominently;
- do not hide one error behind another.

A handled failure must not intentionally leave residue merely for the next run.

Residue may remain only when:

- the process terminates uncatchably;
- cleanup itself fails;
- lock release fails.

The next run recovers such residue before any final generated-file mutation.

16. Fail-closed stage recovery

After acquiring the lock, enumerate every record in the root-owned stage-record namespace.

Recovery must be record-driven, never a recursive scan for `.fido-stage-*` names.

For each record:

- read and parse it strictly;
- validate version and every path field;
- prove the stage path is under the target root and has the expected hidden stage-name form;
- prove its parent matches the recorded parent;
- reject malformed/unreadable records fail-closed;
- if the recorded stage is confirmed missing, remove the stale record;
- if it is a real non-symlink directory, remove it recursively without following symlinks, then remove the record;
- if the recorded path is a symlink, file, special object, or otherwise inconsistent, abort and preserve it;
- if any recovery operation fails, abort before modifying final generated files.

A partially written record is root-owned by location. Because the implementation must not create the local stage until the complete record is closed successfully, a malformed/partial record may be removed after verifying that no stage was created under an untrusted path.

Do not suppress record/recovery errors.

17. Per-file installation and ownership rechecks

Immediately before overwriting an existing Fido-owned `.go` or root `go.mod`:

- `lstat` again;
- require regular file;
- require non-symlink;
- reopen and verify exact first-line ownership header;
- abort on any change or read error.

Install staged files using rename from the local stage directory in the same parent.

If rename reports cross-device behavior, fail loudly. Do not copy-and-delete.

Because stage and target are siblings under one parent, normal nested mount points are supported without a central-device comparison.

Only after every desired file is installed may stale generated `.go` files be removed.

Immediately before deleting each stale generated file:

- `lstat` again;
- require regular/non-symlink;
- re-read the exact ownership header;
- abort on any mismatch/error.

Never delete foreign files or ordinary directories.

18. Honest filesystem guarantee

Document exactly:

> GoProgram acceptance, SafeProgram certification, and DirectoryImage creation are semantically all-or-nothing. Dirty-directory installation is locked for cooperating emitters, rejects foreign Go/module inputs, stages the complete image locally beside target parents before installation, uses per-file atomic rename in the ordinary same-filesystem case, cleans handled-failure residue immediately, recovers record-owned abandoned local stages before future mutation, and converges on rerun. It is not a portable transactional multi-file filesystem commit and is not hardened against malicious concurrent filesystem mutation.

Do not claim:

- whole-tree atomicity;
- crash-proof lock recovery;
- no possible residue after SIGKILL/power loss;
- adversarial race freedom;
- portability to every filesystem/OS.

19. Replace the zero-axiom root with whole-theory assumption closure

The current global audit rejects only Fido constants whose own body is `Undef`.

That is insufficient.

A retained internal theorem may have an opaque body that depends on an external axiom such as functional extensionality and escape the current whole-project audit unless it is one of the selected public surfaces.

Create one whole-certified-theory assumption-closure audit.

Required algorithm:

1. Identify the exact authoritative set of certified Fido modules from Dune.
2. Collect every global constant belonging to those certified modules.
3. Compute the union of assumption closures for all those constants using Rocq’s assumptions machinery and the opaque-body indirect accessor, equivalent in strength to `Print Assumptions`.
4. Reject any closure entry representing:
   - Axiom;
   - Parameter/global assumption;
   - section/global Variable that remains an assumption;
   - project-disallowed primitive constant;
   - any other unsupported assumption category in the pinned Rocq API.
5. Descend through opaque `Qed` bodies.
6. Catch assumptions reached transitively through internal non-public lemmas.
7. Catch unused axioms in certified modules.
8. Fail closed on audit/query errors.

Keep the selected `gate/axiom_gate.v` `Print Assumptions` checks as a readable public-theorem-surface audit.

Use the same root assumption-closure mechanism for emit-time image provenance where possible, rather than maintaining subtly different assumption definitions.

20. Certified module coverage must be exact

Add a build gate comparing:

- every tracked root certified `.v` module intended for the Fido theory;
- Dune’s authoritative `(modules ...)` list.

No certified module may be tracked but omitted from the theory/audit.

Test-only `.v` files under `e2e/` and `gate/` are outside the certified theory only when explicitly classified as test/gate inputs.

Do not let a new certified module escape the audit merely because Dune was not updated.

21. Remove tracked axiom-bearing negative fixtures

The repository’s policy is zero project axioms.

Do not keep tracked source fixtures containing deliberate `Axiom` or `Admitted` declarations.

Delete tracked axiom-bearing forge fixtures such as the current direct/opaque axiom witnesses.

Generate those negative Rocq source files transiently inside the pinned test environment instead:

- direct axiom-backed image;
- axiom behind opaque `Qed`;
- direct/global assumption case;
- transitive assumption case.

Compile and run them only as temporary adversarial fixtures.

They must not be theory modules and must not remain in the tracked repository.

Section-local parameter tests without project axioms may remain only if useful and accurately classified.

The emit boundary must continue rejecting an assumption-dependent image before any filesystem effect.

22. `go vet` is diagnostic only

The formal compiler contract is `go build ./...` acceptance, not `go vet`.

`go vet` can report false positives or policies outside compiler acceptance.

Therefore:

- a vet nonzero exit must not fail `make check`;
- a vet nonzero exit must not fail e2e;
- GoCompile must not claim to model vet;
- documentation must not list vet as an acceptance guarantee;
- it may run and print diagnostics for human inspection.

Use explicit nonblocking shell behavior, for example:

  if ! go vet ./...; then
    echo "fido: go vet reported diagnostics (nonblocking)"
  fi

`go build ./...` remains the blocking external compiler-acceptance alarm.

23. Integration uses the certified go.mod

Delete handwritten `go.mod` injection from Docker/e2e.

The emitted tree itself must contain the exact Fido-rendered `go.mod`.

Set:

  GOWORK=off
  GOTOOLCHAIN=local
  GOPROXY=off

as appropriate for the current import-free closed-world integration.

The Go stage copies the complete emitted module tree.

Blocking checks:

- exact root `go.mod` exists;
- `go build ./...` succeeds;
- accepted current witnesses run and match reviewed stdout/stderr/exit;
- rendered output is gofmt-stable if that remains a desired nonsemantic canonicality check;
- `go list ./...` matches the expected generated package set.

Nonblocking:

- `go vet ./...`.

24. Empty-program differential and sink tests

Add an empty-program witness using a valid ModuleSpec and an empty source map.

Kernel facts:

- empty build succeeds;
- GoCompile accepts;
- SafeProgram can be constructed;
- render produces valid `go.mod`;
- rendered Go-file map is empty.

Filesystem/e2e behavior:

1. Emit a nonempty generated program to a target.
2. Re-emit an empty program with a valid ModuleSpec to the same target.
3. Verify:
   - Fido-owned generated `.go` files are removed;
   - Fido-owned `go.mod` remains and matches the new image;
   - foreign non-Go files remain untouched;
   - no foreign Go exists;
   - no stage/record residue remains after success;
   - `GOWORK=off GOTOOLCHAIN=local go build ./...` exits successfully;
   - zero packages is accepted.

Do not treat the warning text from `go build ./...` as semantic output; only its acceptance status matters.

25. Foreign-Go and module-collision tests

Add mutation-sensitive tests covering:

- foreign root `.go` -> refuse before generated-file mutation;
- foreign nested `.go` -> refuse;
- `.go` symlink -> refuse;
- unreadable directory that could contain `.go` -> fail closed;
- foreign root `go.mod` -> refuse;
- root `go.mod` symlink/nonregular -> refuse;
- nested `go.mod` -> refuse;
- existing Fido-owned `go.mod` -> replace after ownership recheck;
- existing Fido-owned `.go` -> replace/delete as desired;
- foreign non-Go files -> preserve;
- owned control directory -> use;
- foreign `.fido` control directory -> refuse.

After every refused operation, prove through tests that preexisting generated and foreign final files remain unchanged except for explicitly documented control/lock lifecycle that is successfully cleaned.

26. Local-stage regression tests

Replace central-staging tests with local-stage tests.

Cover:

- multiple desired files in one parent share one local stage;
- files in different parent directories use separate local stages;
- all desired outputs stage before the first install;
- a write failure in a later stage leaves all prior final generated files untouched;
- handled failure removes every local stage and root record when cleanup succeeds;
- cleanup failure keeps the record for recovery and reports both errors;
- crash after complete record but before stage mkdir;
- crash after stage mkdir but before first payload;
- crash after partial payload;
- crash after full staging but before install;
- recovery removes only stages named by valid root-owned records;
- foreign lookalike `.fido-stage-*` with no record is preserved;
- malformed record fails closed;
- record pointing outside root fails closed;
- record/stage identity mismatch fails closed;
- stage-path symlink/non-directory fails closed;
- stage-name collision is preserved and causes retry/abort;
- nested target parent on another mount is not rejected merely because root `.fido` is elsewhere;
- EXDEV on a supposedly local rename fails without copy fallback;
- immediate ownership recheck prevents overwrite/delete after a file becomes foreign;
- success leaves no local stage or record residue.

Use injected operation parameters through the real algorithm for deterministic fault testing.

Do not add ambient environment-controlled destructive behavior to the production sink.

27. Documentation correction

Update all active documentation and source headers:

- `.review/NEXT_STEPS.md` remains the binding contract for this milestone;
- `ARCHITECTURE.md`;
- `CLAUDE.md`;
- `README.md`;
- `PROGRESS.md`;
- `PAINFUL_LESSONS.md`;
- `Makefile`;
- `Dockerfile`;
- `GoAST.v`;
- new ModuleSpec/ModulePath/GoVersion modules;
- `GoCompile.v`;
- `GoSafe.v`;
- `GoRender.v`;
- `GoEmit.v`;
- plugin/sink headers;
- e2e comments;
- assumption-gate comments.

Required truths:

A. Program root

  GoProgram = ModuleSpec + finite map FilePath -> raw GoFileAST.

B. ModuleSpec

  ModulePath and GoVersion are intrinsic program facts, not environment configuration.
  Initial GoVersion support is exactly Go1_23.

C. Empty program

  Empty source-file map is valid.
  It emits go.mod and no `.go` files.
  It is accepted by `go build ./...`.

D. One AST

  No copied compiled tree or separate IR.

E. Complete image

  DirectoryImage contains exact go.mod bytes plus the finite map of Go source bytes.

F. Foreign Go

  Dirty-directory emission rejects every foreign `.go` and every foreign/nested `go.mod` for now.

G. Local staging

  Root `.fido` holds lock + durable stage records.
  Staged payloads live in random local stage directories beside target parents.
  Central `.fido/staging/` is rejected architecture and must not remain in active docs.

H. Failure semantics

  Complete image staged before installation.
  Handled failures clean immediately.
  Crash/cleanup failure recovery is record-driven.
  No transactional whole-tree claim.

I. Axioms

  Whole-certified-theory assumption closure is audited.
  Selected public surfaces remain readable `Print Assumptions` gates.
  No tracked axiom-bearing negative fixtures.

J. Go acceptance

  `go build ./...` is blocking.
  `go vet` is diagnostic only.

K. Operational scope

  Claims about path materialization and filesystem behavior are scoped to the supported Linux/amd64 operational target, not “any target.”

Delete stale claims about:

- nonempty programs/images;
- handwritten go.mod injection;
- central `.fido/staging/`;
- central cross-device target rejection;
- handled failures intentionally leaving stage residue;
- current global audit catching every external axiom dependency;
- tracked axiom fixtures being compatible with zero project axioms;
- vet as a blocking acceptance gate;
- foreign Go being preserved while still promising the dirty merged tree compiles;
- FilePath safety “on any target.”

28. Painful lessons update

Keep `PAINFUL_LESSONS.md` concise.

Replace the current central-staging lesson with the actual durable lesson:

- A reviewer may identify a real defect without owning the replacement architecture.
- The agreed capability—local staging to support nested mount points—must not be silently dropped to satisfy a review.
- Transient local stages need durable root-owned records; markers, public headers, and names alone do not establish crash-safe ownership.
- Complete image staging precedes installation.
- Handled failure cleanup differs from crash recovery.
- Filesystem discovery must distinguish missing from operational failure.
- Dirty foreign Go contradicts a closed-world compile guarantee and must reject until isolated or modeled.
- The module file is part of the generated program and must be represented formally.
- Zero-axiom enforcement means closure over every certified constant, not only direct undefined bodies or selected public endpoints.
- A nonblocking diagnostic must not silently become an unmodeled compiler criterion.
- `.review/NEXT_STEPS.md` is the binding review contract; architectural conflicts escalate rather than trigger invisible redesign.

Do not turn this file into a commit diary.

29. Deletion and culling requirement

Do not be conservative about preserving Codex-driven architecture.

Delete rather than wrap:

- central staging implementation;
- central staging tests;
- central staging documentation;
- central-device rejection;
- current whole-project audit that checks only `Undef` bodies;
- source-text scanner remnants;
- tracked axiom-bearing forge fixtures;
- nonempty-program scaffolding;
- handwritten go.mod injection;
- blocking vet behavior;
- claims made obsolete by this milestone.

Retain only code that naturally belongs to the corrected roots.

30. No unrelated refactoring

Do not:

- grow language breadth;
- redesign CompilationFacts beyond what this milestone needs;
- add imports;
- alter the direct renderer architecture;
- revisit tokens/parsers/IR;
- generalize beyond Go1_23;
- generalize beyond the supported Linux/amd64 operational scope;
- add foreign-Go parsing;
- add a workspace model;
- add `require`/`replace`/external module semantics.

31. Required theorem and gate surface

Add or update axiom-free theorem surfaces for at least:

ModulePath / GoVersion / ModuleSpec

- represented ModulePath values satisfy the canonical validator;
- equality is decidable/sound;
- positive/negative fixtures;
- Go1_23 renders exactly `"1.23"`;
- rendered go.mod has exact header/module/go directive structure.

GoProgram / GoCompile

- empty program constructs successfully;
- empty program is `ProgValid`;
- `go_compile` accepts empty program;
- soundness/completeness still hold for all represented programs;
- nonempty existing compiler cases remain exact.

GoRender / GoEmit

- go.mod header first line;
- go.mod rendering uses the exact ModuleSpec;
- empty source map renders zero `.go` files;
- DirectoryImage provenance covers go.mod and Go files;
- every Go file has the header;
- on-disk Go paths remain unique;
- no false image-nonempty theorem remains.

Assumptions

- whole-certified-theory closure is empty;
- planted external-dependency axiom behind an internal opaque theorem is caught;
- unused certified-module axiom is caught;
- direct and transitive assumptions are caught;
- normal Section-generalized theorem is accepted;
- public surfaces remain closed.

32. Acceptance criteria

The milestone is complete only if all applicable conditions hold.

Binding contract

- This directive was copied verbatim into `.review/NEXT_STEPS.md`.
- The contract was committed before implementation.
- Completion report includes the contract commit SHA.
- Codex reviewed against the file.
- No architectural conflict was silently implemented.

Program/module model

- `GoProgram` contains `ModuleSpec` and `fmap FilePath GoFileAST`.
- `ModulePath` is intrinsic, narrow, and axiom-free.
- `GoVersion` initially has exactly Go1_23.
- No TargetConfig reappears.
- Empty source map is representable.
- One AST per file remains.

Compiler/safety

- Empty program is accepted.
- Existing whole-program package rules remain sound/complete.
- GoSafe/SafeProgram remain the emission capability.
- No feature growth occurred.

Rendering/image

- go.mod is rendered in Rocq from ModuleSpec.
- Docker no longer writes go.mod by hand.
- DirectoryImage includes exact go.mod + Go-file map.
- Empty program image has go.mod and no Go files.
- Provenance covers the complete module image.
- Public emission still requires SafeProgram-derived DirectoryImage.

Foreign-file boundary

- Foreign `.go` anywhere in scope rejects.
- Foreign/nested go.mod rejects.
- Fido-owned prior `.go`/go.mod can be synchronized.
- Foreign non-Go files remain.
- Discovery fails closed.

Local staging

- Central `.fido/staging/` is gone.
- Root `.fido` contains control marker, lock, and stage-record namespace only.
- Payloads stage locally beside target parents.
- Records are atomically created in the owned namespace and bind exact stage paths.
- All desired outputs stage before any install.
- Handled failures clean immediately.
- Recovery is record-driven and fail-closed.
- Foreign lookalikes are preserved.
- Nested mount capability is not intentionally rejected.
- No copy fallback on EXDEV.
- Success leaves no stage/record residue.

Axioms

- Whole-certified-theory assumption closure is checked.
- Internal theorem dependency on external axiom is caught.
- Unused certified axiom is caught.
- Opaque dependency is caught.
- Tracked axiom-bearing negative fixtures are deleted.
- Temporary negative fixtures validate the gate.
- Public Print Assumptions surfaces are closed.
- Certified module coverage matches Dune exactly.

Build/e2e

- One shared Dune cache/build authority remains.
- Emitted go.mod is used.
- `GOWORK=off` and `GOTOOLCHAIN=local` are explicit.
- `go build ./...` blocks on failure.
- `go vet ./...` is nonblocking.
- Empty program build succeeds.
- Existing witness builds/runs vs goldens.
- Foreign-Go/module refusal tests pass.
- Full generated tree, not one hard-coded file, is built.

Documentation

- All active docs match implementation.
- Central staging is not canonized.
- Nonempty claims are removed.
- Zero-axiom claim matches the stronger gate.
- PROGRESS remains compact.
- PAINFUL_LESSONS remains architectural.

33. Completion report

When complete, report:

- contract commit SHA;
- final implementation commit SHA;
- files added, changed, and deleted;
- exact ModulePath grammar;
- GoVersion representation;
- final GoProgram/ModuleSpec definitions;
- empty-program compiler/render/e2e behavior;
- DirectoryImage structure;
- every theorem added or changed;
- full `Print Assumptions` and whole-theory audit results;
- certified-module coverage check;
- tracked axiom-fixture deletions and temporary replacement tests;
- foreign-Go/go.mod refusal behavior;
- final local-stage ownership protocol;
- every stage/recovery/failure/race test;
- exact filesystem guarantee;
- all proof/build/e2e commands and results;
- vet diagnostics, if any, clearly marked nonblocking;
- code deleted because it belonged to Codex’s central-staging architecture;
- every new abstraction and why it is permanent and irreducible;
- every new/materially modified Section and its dependency review;
- Codex dispositions;
- confirmation all autonomous loops stopped.

Do not list a retained correctness flaw as a known limitation.

If this contract cannot be implemented correctly, stop, classify the obstacle as an architectural conflict, notify the user, and wait. Do not replace the architecture.

34. Hard stop

After all criteria pass:

1. Stop every autonomous/Ralph/background/iterative loop.
2. Do not infer or begin the next milestone.
3. Commit the checkpoint.
4. Notify the user through the configured phone/completion-notification channel that the checkpoint is ready for review.
5. Wait.

Bottom line

The repaired permanent path is:

  GoProgram {
    ModuleSpec {
      intrinsic ModulePath,
      Go1_23
    },
    fmap FilePath GoFileAST
  }
  -> exact whole-program GoCompile
  -> SafeProgram
  -> direct Rocq renderer
  -> DirectoryImage {
       exact generated go.mod,
       fmap FilePath exact Go bytes
     }
  -> general transport
  -> foreign-Go-refusing dirty-directory sink
       with root-owned records + local per-parent stages
  -> GOWORK=off GOTOOLCHAIN=local go build ./...

Empty programs are valid.
Foreign Go is rejected.
All desired files stage before installation.
Handled failures clean immediately.
Every certified theorem is assumption-closure clean.
No Codex-driven architecture replacement is allowed.
