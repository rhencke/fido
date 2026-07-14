Claude Code milestone: complete proof audit, delete record staging, simplify dirty emission, and track generated Go from one pristine Buildx layer

THIS FILE IS THE BINDING MILESTONE CONTRACT.

Before making any implementation change:

1. Replace the tracked repository file `.review/NEXT_STEPS.md` with this directive VERBATIM.
   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not “improve” or reinterpret the architecture while copying it.
2. Commit `.review/NEXT_STEPS.md` as the opening commit of this milestone, before implementation.
3. Record that contract commit SHA.
4. Treat `.review/NEXT_STEPS.md` as the binding scope, architecture, threat model, and acceptance contract for every implementation change and Codex stop-review in this milestone.

The Codex stop review must judge whether the implementation is airtight against `.review/NEXT_STEPS.md`.

Codex may identify objective defects. It may not:

- broaden scope;
- strengthen the threat model;
- remove an explicitly required capability;
- move responsibility between layers;
- select another architecture;
- demand feature completeness beyond this milestone;
- redesign the sink into a filesystem database;
- reintroduce staging records, parsers, mount identity tracking, or a central staging directory.

If a real defect cannot be fixed while preserving this contract, classify it as an ARCHITECTURAL CONFLICT, notify the user, and stop. Do not redesign autonomously.

After one structural repair attempt in the same subsystem, any second proposed structural redesign is automatically an architectural conflict requiring human review.

This is one bounded, fixes-only milestone.

Stop every Ralph-style, autonomous, recursive, background, or iterative development loop before beginning.

After completing this milestone:

1. Run every required proof, audit, build, artifact, sink, staged-index, and end-to-end check.
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

No Go-language feature growth in this milestone.

Do not add:

- imports;
- standard-library access;
- `fmt`;
- strings;
- new builtins;
- new primitive types;
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
- another AST or IR;
- workspaces;
- module dependencies;
- `require`, `replace`, `exclude`, `retract`, `toolchain`, or `godebug` directives.

Current permanent roots to preserve

Preserve the current formal program architecture:

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
  -> general Fido Emit transport
  -> filesystem-only dirty-directory sink
  -> pinned Go `go build ./...`

Preserve:

- intrinsic `ModulePath`;
- singleton `GoVersion := Go1_23`;
- intrinsic `FilePath`;
- key-generic immutable finite maps;
- empty programs;
- one AST;
- whole-program `GoCompile`;
- `SafeProgram` as the permanent safety capability;
- direct parser-free renderer;
- exact rendered `go.mod`;
- complete `DirectoryImage`;
- general `Fido Emit`;
- foreign-Go/module refusal;
- `go vet` as diagnostic only;
- `go build ./...` as the blocking external compiler alarm;
- distinction between proof and integration evidence.

Milestone purpose

This milestone seals four remaining roots:

1. `make prove` must enforce the complete whole-certified-theory assumption policy, including inductive assumptions.
2. Delete the stage-record/local-stage-directory subsystem and replace it with a fixed reserved sibling-temporary suffix.
3. Make one normal content-addressed Buildx stage the pristine authority for the canonical generated Go module.
4. Track the canonical generated `go.mod` and recursive `.go` files, and make pre-commit verify the exact staged Git snapshot against that pristine Buildx artifact.

The dirty-directory sink is not a hostile-filesystem package manager.

The intended threat model is:

- one project owner;
- cooperating Fido emitters serialized by one lock;
- stable directory namespace between runs;
- ordinary crashes;
- disk exhaustion;
- permission errors;
- interrupted writes;
- nested mount points that remain mounted;
- no malicious concurrent namespace mutation;
- no arbitrary unmount/remount/backing-store replacement between a crash and recovery.

Mount disappearance, remounting, parent replacement, and hostile concurrent mutation are explicitly outside the guarantee.

Do not add Linux-specific device/inode ownership records.

Do not add a general transaction log.

1. Complete the whole-certified-theory assumption audit

Current defect

The whole-theory audit seeds assumption closure from certified constants only.

That misses assumption categories attached directly to certified mutual inductive declarations when no retained constant references them, including categories represented by Rocq as `Printer.Axiom` variants such as:

- assumed positivity;
- disabled guardedness;
- type-in-type;
- UIP-related reduction;
- indices-not-mattering.

Required authority

Define one assumption-policy function over the complete certified declaration root set:

  CertifiedDeclarations
  -> union of Rocq assumption closures
  -> reject every disallowed assumption category

The root set must include at least:

- every certified Fido constant;
- every certified Fido mutual inductive, seeded through an `IndRef`;
- every surviving global/named assumption in the environment supported by the pinned Rocq API.

Use Rocq’s own assumptions machinery with the opaque-body indirect accessor.

Descend opaque `Qed` bodies.

Reject:

- every `Printer.Axiom _` category, not only ordinary constant axioms;
- every `Printer.Variable`;
- any project-disallowed primitive/assumption category exposed by the pinned Rocq assumptions API.

Do not write a source-text scanner.

Do not duplicate the definition of “disallowed assumption” between proof auditing and emit-time provenance.

Use one shared implementation.

Implementation organization

Prefer the smallest implementation that preserves one authority.

It is acceptable to keep the shared assumptions code in the current plugin if `make prove` can invoke it cleanly.

Do not split a new plugin merely for aesthetic purity.

If code must be factored to avoid duplication, introduce one tiny shared OCaml assumptions module with one permanent responsibility:

> compute and enforce Fido’s assumption policy over supplied Rocq global references.

No filesystem logic belongs in that module.

2. `make prove` is the complete proof gate

`make prove` must run all of:

- Dune theory build;
- certified-module coverage check;
- selected readable `Print Assumptions` surfaces;
- whole-certified-theory assumption-closure audit over constants, inductives, and surviving named assumptions;
- adversarial self-tests for the audit.

A retained internal declaration that depends on an assumption must fail `make prove`, even when it is not a selected public theorem and emission is never run.

`make check` may depend on `make prove`, but the complete proof policy must not exist only in `emit` or `e2e`.

The certified-module coverage gate must remain exact:

  tracked certified root `.v` modules
  =
  Dune `(modules ...)`

Test/gate/e2e `.v` files remain explicitly outside the certified theory.

3. Adversarial proof-audit tests

Generate all assumption-bearing negative fixtures transiently inside the pinned build.

Do not track project `Axiom`, `Parameter`, or `Admitted` fixtures.

At minimum exercise:

A. An unused Fido axiom.

B. An internal theorem whose opaque `Qed` body depends transitively on an external axiom.

C. An unused certified mutual inductive admitted only because positivity checking was disabled, with automatically generated elimination constants suppressed where necessary so the audit must seed the inductive itself.

D. A surviving global/named assumption if the pinned Rocq environment permits one to reach the compiled audit context.

E. A normal `Section` theorem whose variables are correctly generalized and whose closed theorem must be accepted.

The tests must prove:

- constants are audited;
- opaque bodies are descended;
- inductives are audited even when no constant references them;
- ordinary closed Section generalization is not falsely rejected.

Fail closed on Rocq audit/query errors.

Keep the readable selected `gate/axiom_gate.v` surfaces.

4. Replace the operating-law escape hatch

Current active prose still permits Claude to override a plan in favor of what it considers “more correct.”

Delete or replace wording equivalent to:

> Plans are guidance; when a plan conflicts with a stronger proof or more correct formulation, follow the stronger path.

Permanent replacement:

> The current `.review/NEXT_STEPS.md` is binding for the active milestone. If an objective defect cannot be repaired without changing its architecture, scope, guarantees, threat model, responsibility boundaries, or selected algorithm, report an architectural conflict and stop. Do not implement an alternative autonomously.

Apply this consistently in:

- `CLAUDE.md`;
- `ARCHITECTURE.md`;
- review workflow documentation;
- completion/reporting instructions.

5. Delete the entire stage-record subsystem

Delete rather than wrap:

- `.fido/stage-records/`;
- record files;
- record versions;
- record parsing;
- record validation;
- nonce generation;
- OS randomness for stage names;
- local stage directories;
- record-driven recovery;
- record/path consistency checks;
- record-specific fault seams;
- record-specific tests;
- record-specific documentation;
- device/inode/mount-identity ideas;
- central staging remnants.

The current record system was a disproportionate answer to a simple single-owner generation problem.

Do not preserve it as “future scaffolding.”

The permanent control directory becomes exactly:

  <root>/.fido/
    marker
    index.lock   # present only during an active run or after a crash

An existing root `.fido` must have exactly:

- the exact marker;
- optionally `index.lock`;
- no other entries.

Any unexpected root-control entry rejects without modification.

6. Reserve one sibling temporary suffix

Use this exact reserved suffix unless an existing reviewed constant already names an equivalent versioned suffix:

  .fido-tmp-v1

For each final output:

  go.mod
  main.go
  sub/main.go

the sibling temporary is:

  go.mod.fido-tmp-v1
  main.go.fido-tmp-v1
  sub/main.go.fido-tmp-v1

No nonce is needed because the lock serializes cooperating emitters.

No temporary directory is needed.

No record is needed.

The final path is already known by the live synchronization operation; recovery does not need to parse a record.

Ownership convention

A regular non-symlink file whose basename ends in `.fido-tmp-v1` is considered an abandoned Fido temporary.

This convention is public and forgeable.

That is an accepted tradeoff under the actual single-owner/cooperating-process threat model.

A symlink, directory, or special entry with the reserved suffix is not treated as owned:

- refuse;
- preserve it;
- make no generated-file mutation.

Document the convention honestly.

7. Reject nested `.fido` everywhere

The exact root `<root>/.fido/` is the only permitted control namespace.

During recursive inspection, any entry named `.fido` below the root is an error, regardless of type:

- directory;
- symlink;
- regular file;
- special entry.

Reject before generated-file mutation.

Do not skip or descend through nested `.fido`.

Add tests for nested `.fido` as:

- directory;
- symlink;
- regular file.

Preserve each entry on refusal.

8. Keep foreign-Go/module refusal

Before generated-file mutation, recursively inspect the complete target tree fail-closed.

Allowed:

- Fido-owned root `go.mod` (regular, non-symlink, exact header);
- Fido-owned `.go` files (regular, non-symlink, exact header);
- foreign non-Go files/directories that are not reserved control/temp names;
- the exact root `.fido` control directory;
- regular reserved-suffix temporary files, which are collected as abandoned Fido temporaries.

Reject:

- foreign `.go` anywhere;
- `.go` symlink/nonregular entries;
- foreign root `go.mod`;
- root `go.mod` symlink/nonregular entry;
- nested `go.mod`;
- nested `.fido` of any type;
- nonregular reserved-suffix temp entries;
- unreadable/unsearchable directories;
- any filesystem error preventing a complete classification.

Only a confirmed `ENOENT` means missing.

Do not treat permission, I/O, symlink-loop, or non-directory errors as absence.

9. Two-phase abandoned-temp recovery

After acquiring the lock:

Phase 1 — inspect only

- recursively inspect the entire relevant target tree;
- validate foreign-Go/module/control rules;
- collect every regular non-symlink file ending in `.fido-tmp-v1`;
- perform no deletion during traversal.

If any path is invalid or uninspectable:

- reject;
- preserve every collected temp;
- perform no generated-file mutation.

Phase 2 — delete validated abandoned temps

Only after the complete scan succeeds:

- re-`lstat` each collected temp;
- require it is still a regular non-symlink file with the exact reserved suffix;
- delete it;
- fail loud on any mismatch or deletion error.

The lock prevents cooperating emitters from creating new Fido temps concurrently.

No record parsing exists.

10. Preflight the complete desired image

The desired image consists of:

- root `go.mod`;
- zero or more recursive `.go` files from `DirectoryImage`.

Before writing the first temp:

- validate every relative final path;
- reject desired paths inside `.fido`;
- derive every sibling temp path mechanically by suffix append;
- verify every existing final target is either absent or Fido-owned;
- verify every sibling temp path is absent after recovery;
- reject a symlink/nonregular/foreign collision;
- create required parent directories carefully;
- record only parent directories created by this invocation for handled-failure cleanup.

Do not introduce a second weaker path grammar.

The sink’s defensive path validator must accept exactly the canonical path strings emitted from intrinsic `FilePath` for `.go`, plus the distinguished root `go.mod`.

Canonical transport uses forward slashes.

Do not broaden accepted sink paths beyond the formal output domain.

11. Stage the complete image before installation

This requirement remains absolute.

For every desired final file:

1. Create the sibling temp with exclusive creation.
2. Write exact bytes unchanged.
3. Close successfully.
4. Track the temp as created by this invocation.

Do not install any final file until every desired file has staged successfully.

Ordinary staging failures such as disk exhaustion or permissions must leave all previous final generated files unchanged.

No formatter, header mutation, or content repair occurs in the sink.

12. Install by sibling rename

Only after complete staging:

For each desired final target:

- invoke any test seam before the final recheck;
- immediately re-`lstat` the final;
- if present, require regular/non-symlink and exact Fido header;
- rename the sibling temp to the final path;
- fail loudly on cross-device behavior;
- do not copy-and-delete.

Current operational support remains pinned Linux/amd64.

Do not add Linux-specific mount identity tracking.

The algorithm shape is intentionally portable:

- forward-slash transport;
- sibling temp;
- lock;
- rename.

Exact replacement semantics on future operating systems are a future porting milestone.

13. Remove stale generated Go

After every desired file is installed:

- identify prior Fido-owned `.go` files not in the desired path set;
- immediately re-`lstat`;
- require regular/non-symlink;
- re-read the exact header;
- delete only when still provably Fido-owned;
- abort and preserve on any ownership/type/read mismatch.

The empty program removes every Fido-owned `.go` while keeping/updating the generated `go.mod`.

Never delete foreign files or ordinary directories.

14. Handled failure cleanup

On every handled failure:

- attempt to remove every sibling temp created by this invocation;
- recheck that each is a regular non-symlink reserved-suffix file before deletion;
- remove newly-created parent directories only when still empty and known to have been created by this invocation;
- aggregate body, temp-cleanup, parent-cleanup, and lock-release errors;
- never hide the initiating error;
- release the lock when possible.

A handled staging failure must not intentionally leave temp residue for the next run.

A crash, process kill, power failure, disk failure during cleanup, permission failure during cleanup, or lock-release failure may leave:

- `index.lock`;
- sibling temp files.

After the stale lock is deliberately removed, the next run performs two-phase temp recovery and converges.

15. Honest filesystem guarantee

Use this exact meaning:

> GoProgram acceptance, SafeProgram certification, and DirectoryImage creation are semantically all-or-nothing. Dirty-directory installation is locked for cooperating emitters, rejects foreign Go/module inputs and nested `.fido`, inspects the complete tree fail-closed, stages the complete image into reserved sibling temporary files before installation, uses per-file rename in the ordinary same-filesystem case, cleans handled-failure temps immediately, removes validated abandoned suffix-owned temps on a later run, and converges when the directory namespace remains stable. It is not a portable transactional multi-file filesystem commit, not hardened against malicious concurrent mutation, and does not model arbitrary unmount/remount/backing-store replacement between runs.

Do not claim:

- whole-tree atomicity;
- hostile-filesystem safety;
- unforgeable temp ownership;
- recovery after arbitrary mount replacement;
- no possible residue after SIGKILL/power loss;
- portability to every current operating system without a future porting review.

16. Simplify the sink aggressively

The record subsystem deletion should materially reduce code.

Remove dead helpers, datatypes, fault seams, tests, and prose.

The sink should return to a small, auditable filesystem synchronizer.

Do not preserve a high line cap merely because the old record implementation needed it.

Reduce the OCaml-origin gate’s sink size bound to a reviewed value appropriate to the simplified implementation.

Do not optimize for an arbitrary seven-line target; retain only irreducible dirty-directory logic.

17. One pristine generated-module Buildx stage

Create one explicit normal content-addressed Buildx stage whose contract is:

  generated-module
    /generated/go.mod
    /generated/**/*.go

It contains exactly the canonical certified generated module.

It contains no:

- `.fido`;
- lock;
- temp files;
- proof sources;
- test fixtures;
- unrelated repository files.

The canonical module is the current primary witness program, not the multi-package or empty differential fixture.

The stage must be built from authoritative generation inputs:

- certified `.v` sources;
- Dune/project files;
- plugin/transport sources needed to generate;
- pinned toolchain/build inputs;
- canonical witness source.

Committed generated `go.mod` and `.go` files must not be semantic inputs to the generation stage.

Use specific `COPY` instructions so changing only tracked generated outputs invalidates comparison stages but does not force the proof/generation layer to treat those bytes as authority.

Mutable BuildKit cache mounts may accelerate:

- opam downloads;
- Dune `_build`;
- compiler caches.

The authoritative generated module must live in an ordinary image layer, never in a mutable cache mount.

18. Buildx stage reuse

Every canonical-output workflow consumes the same `generated-module` layer:

- Go e2e;
- staged-index verification;
- working-tree regeneration;
- artifact inspection;
- future CI.

Do not regenerate the canonical module independently in each path.

The existing multi-package and empty witnesses remain differential/e2e fixtures and may use related cached proof layers, but they are not the canonical tracked artifact.

Add an artifact target conceptually equivalent to:

  FROM scratch AS generated-artifact
  COPY --from=generated-module /generated/ /

The local exporter may expose that exact tree when needed.

19. Track the canonical generated module at the repository root

Do not introduce `dist/`.

Track:

- root `go.mod`;
- root and recursive generated `.go` files at their natural `FilePath` locations.

The repository should support:

  go build ./...
  go run .

without requiring Rocq, Docker, or Fido merely to inspect/run the already-generated canonical example.

The proof sources remain authoritative.

The tracked Go module is a reviewed derived artifact.

Current repository policy becomes:

- every tracked `.go` belongs to the canonical generated module;
- root `go.mod` is generated and tracked;
- every tracked generated file begins with the exact Fido header;
- handwritten Go inside the generated module is forbidden for now;
- nested `go.mod` remains forbidden.

Delete the old policy:

- `*.go` globally ignored;
- tracked Go prohibited;
- “generated Go is uncommittable.”

20. Git ignore policy

Update `.gitignore`:

Remove:

  *.go

Do not ignore:

- root `go.mod`;
- generated `.go` files.

Ignore only transient control/residue for this repository:

  /.fido/
  **/*.fido-tmp-v1

Do not globally ignore nested `.fido` directories; nested `.fido` is an emission error and should remain visible if it somehow appears.

The exact root `.fido/` is ignored because it is local control state.

Abandoned sibling temps are ignored because they are crash residue and never meaningful source artifacts.

21. Generated-output repository gate

Replace the old no-tracked-Go seal with a generated-output policy gate.

At minimum it must reject:

- tracked `.go` without the exact Fido header;
- tracked root `go.mod` without the exact Fido header;
- tracked nested `go.mod`;
- tracked `.fido` control entries;
- tracked `*.fido-tmp-v1`;
- handwritten/unowned tracked Go.

The exact path/byte equality with fresh certified generation is enforced by the staged-index pre-commit Buildx check below.

Do not preserve both the old prohibition and the new tracked-output model.

22. Working-tree regeneration command

Add one clear command, for example:

  make regenerate

Its job:

- build/reuse the exact `generated-module` Buildx layer from the current working-tree proof inputs;
- synchronize that pristine artifact into the repository root using the same simplified dirty-directory sink;
- never invoke an independent renderer;
- never copy directly over the repository without the sink;
- preserve foreign non-Go files;
- reject foreign Go/module inputs and nested `.fido`;
- update tracked `go.mod` and recursive `.go`;
- remove stale Fido-owned `.go`.

A small production filesystem-only CLI may be added if necessary to apply `/generated` to a destination through `Fido_sink`.

That CLI may:

- read `/generated/go.mod`;
- recursively enumerate `/generated/**/*.go`;
- convert paths to canonical forward-slash relative paths;
- call the same sink.

It may not:

- inspect Rocq terms;
- understand ASTs;
- compile;
- render;
- alter bytes;
- choose semantic paths.

Keep it tiny.

A practical Buildx/Docker flow may be:

- build/load a small sync image that copies `/generated` from `generated-module`;
- run it with the repository root bind-mounted;
- the CLI invokes the same sink against the bind mount.

Do not use a second generation.

23. Pre-commit verifies the exact staged Git snapshot

The hook must verify the proposed commit, not the ordinary working tree.

Required flow:

1. Create one temporary directory.
2. Export the Git index exactly once:

     git checkout-index --all --prefix="$tmp/context/"

3. Use that exported staged tree as the entire Buildx context.
4. Build a `verify-staged-generated` target.
5. That target reuses the `generated-module` layer built from the staged proof/generation inputs.
6. Inside Buildx, compare the staged generated artifacts against `/generated`.

The hook must not:

- read unstaged working-tree source as authority;
- mutate the working tree;
- auto-stage files;
- regenerate twice;
- compare only root-level `*.go`;
- silently pass on a missing generated file.

The comparison is recursive.

Compare:

- staged root `go.mod`;
- every staged `**/*.go` at every depth;

against:

- `/generated/go.mod`;
- every `/generated/**/*.go`.

Verify both:

A. Exact relative path sets.

B. Exact byte contents for every path.

Catch:

- modified generated bytes;
- missing staged generated file;
- newly generated file absent from the index;
- stale staged generated file removed by generation;
- nested generated path mismatch;
- stale `go.mod`.

Report every differing path where practical.

The hook should abort with instructions equivalent to:

  make regenerate
  git add -A -- go.mod ':(top,glob)**/*.go'
  git commit

Do not auto-stage.

24. Buildx cache correctness

The staged verification is only valid when the generated layer cache key depends on the exact staged authoritative inputs.

Ensure the generation stage copies all and only required authoritative inputs.

The generated result must be an ordinary layer.

Do not compare against:

- mutable Dune cache contents;
- an old exported directory;
- the ordinary working tree;
- a “latest successful generation” path;
- a cache mount used as output authority.

Buildx may reuse the generated layer only when its inputs and instructions match the staged snapshot.

25. Prototype guarantee and future CI

Current guarantee:

> A normal Git commit is refused unless the exact staged proof/generation inputs regenerate the exact staged root `go.mod` and recursive staged `.go` path set and bytes through the pinned Buildx certified pipeline.

This is intentionally a prototype-stage guarantee.

`git commit --no-verify` can bypass it.

That limitation must be documented honestly.

Do not add a GitHub Actions/PR CI workflow in this milestone.

Future PR review will run the same staged/generated comparison as a mandatory server-side check.

26. Go e2e consumes the same generated layer

The pinned Go e2e must copy the canonical module from `generated-module`.

It must not independently regenerate or hand-create `go.mod`.

Keep:

  GOWORK=off
  GOTOOLCHAIN=local
  GOPROXY=off

Blocking:

- `go build ./...`;
- canonical witness execution vs reviewed stdout/stderr/exit;
- required path/module discovery checks.

Nonblocking:

- `go vet ./...`.

The e2e should also verify the generated layer contains no `.fido` or temp residue.

27. Simplified sink regression tests

Delete record-specific tests and replace them with tests of the actual suffix design.

At minimum cover:

Clean/dirty sync

- clean sync writes generated go.mod + `.go`;
- Fido-owned files update;
- stale Fido-owned `.go` removes;
- foreign non-Go preserves;
- empty program removes every Fido-owned `.go` and keeps go.mod.

Foreign inputs

- foreign root `.go` rejects;
- foreign nested `.go` rejects;
- `.go` symlink/nonregular rejects;
- foreign root `go.mod` rejects;
- root go.mod symlink/nonregular rejects;
- nested go.mod rejects;
- unreadable directory fails closed.

Control namespace

- exact root `.fido` marker + optional lock accepted;
- foreign root `.fido` rejected;
- unexpected root `.fido` entry rejected;
- nested `.fido` directory rejected and preserved;
- nested `.fido` symlink rejected and preserved;
- nested `.fido` regular file rejected and preserved.

Reserved temp suffix

- abandoned regular root temp is removed after complete successful scan;
- abandoned regular nested temp is removed;
- multiple temps are collected before deletion;
- invalid path elsewhere causes refusal before any collected temp is deleted;
- temp symlink rejected/preserved;
- temp directory rejected/preserved;
- temp special entry rejected/preserved;
- regular foreign file using the reserved suffix is intentionally classified Fido-owned and removed; document this accepted convention.

Complete staging

- every desired sibling temp exists before first install;
- later-stage write failure changes no prior final generated file;
- handled staging failure removes every created temp when cleanup succeeds;
- cleanup failure reports both initiating and cleanup errors;
- crash while writing leaves lock + partial temp;
- crash after complete staging leaves lock + all temps and old finals;
- crash during install may leave mixed finals + remaining temps;
- after stale lock removal, next run removes temps and converges.

Rename/ownership

- sibling temp resides beside each nested final;
- a real nested mount remains supported;
- EXDEV fails with no copy fallback;
- overwrite ownership is rechecked immediately;
- stale-delete ownership is rechecked immediately;
- file becoming foreign before overwrite/delete is preserved and aborts.

Repository artifact

- `generated-module` path set exactly matches tracked generated module after regeneration;
- generated layer has no control/temp files.

28. Proof/build test placement

The complete whole-theory audit and module coverage run in `make prove`.

The staged-index generated comparison runs in pre-commit.

The ordinary full `make check` continues to run:

- complete proof gate;
- transport/sink tests;
- canonical generated-module creation;
- Go e2e;
- existing current-fragment differential tests.

Do not claim `make check` proves external Go adequacy.

29. Documentation rewrite

Update all active documentation and source headers:

- `.review/NEXT_STEPS.md`;
- `ARCHITECTURE.md`;
- `CLAUDE.md`;
- `README.md`;
- `PROGRESS.md`;
- `PAINFUL_LESSONS.md`;
- `.gitignore`;
- `.githooks/pre-commit`;
- `Makefile`;
- `Dockerfile`;
- plugin/sink headers;
- origin gates;
- e2e comments.

Required truths:

A. Proof authority

  Whole-certified-theory auditing includes constants, inductives, and surviving named assumptions.
  It runs in `make prove`.
  Selected public Print Assumptions surfaces remain.

B. Active contract

  `.review/NEXT_STEPS.md` is binding.
  Architectural conflicts stop rather than trigger autonomous redesign.

C. Sink

  One lock + one reserved sibling suffix.
  No records.
  No stage directories.
  No nonce.
  No parser.
  No central staging.
  No mount identity tracking.

D. Threat model

  Cooperating emitters and stable namespace.
  Ordinary crash/disk/permission handling.
  Arbitrary remount/backing-store replacement and malicious concurrent mutation are outside scope.

E. Ownership

  Installed `.go`/go.mod owned by exact header + regular/non-symlink.
  Regular `.fido-tmp-v1` files owned by naming convention.
  Nested `.fido` always rejects.

F. Generated artifact

  One normal Buildx `generated-module` layer is the pristine canonical output authority.

G. Tracked Go

  Root go.mod and recursive generated `.go` are tracked derived artifacts.
  `.v`/proof sources are authoritative.
  No `dist/`.
  No handwritten Go in the canonical module for now.

H. Pre-commit

  Exports the Git index once.
  Builds from the staged snapshot.
  Compares root go.mod + recursive `.go` exact path set and bytes.
  Does not inspect unstaged files or auto-stage.
  Bypassable during prototype stage.

I. Git ignore

  Ignore root `.fido/` and recursive `.fido-tmp-v1`.
  Do not ignore generated Go/go.mod.

J. Future CI

  Explicitly deferred.
  Future PR gate will reuse the same verification target.

Delete stale claims about:

- stage records;
- record-driven recovery;
- nonces;
- local stage directories;
- central staging;
- unforgeable transient ownership;
- device/inode mount identity;
- generated Go being forbidden from Git;
- no tracked `.go`;
- handwritten go.mod injection;
- pre-commit checking the working tree;
- plans being merely advisory;
- arbitrary mount/replacement recovery.

30. Painful lessons update

Keep `PAINFUL_LESSONS.md` concise.

Add/replace the durable lesson:

- File emission became overdesigned when the reviewer’s hostile-filesystem concerns replaced the project’s real single-owner threat model.
- A reserved sibling suffix plus a lock is enough for crash-friendly dirty generation here.
- Public naming-convention ownership is an accepted tradeoff; do not build a transaction log to avoid it.
- Complete-image staging before install handles the practical disk/permission failure class.
- Stable path namespace is an explicit operational assumption.
- The proof gate must seed every certified declaration class, not only constants.
- Generated Go can be tracked safely as a derived artifact when the proposed Git index is regenerated and compared through one pristine Buildx layer.
- Pre-commit is a prototype boundary; mandatory PR CI comes later.
- The binding milestone contract outranks an automated reviewer’s preferred architecture.

Delete record-protocol archaeology that no longer protects against a live temptation.

Git history preserves the details.

31. No unrelated refactoring

Do not:

- grow language breadth;
- redesign ModuleSpec;
- redesign CompilationFacts;
- add imports;
- alter the direct renderer;
- add tokens/parsers/IR;
- generalize beyond Go1_23;
- add external module semantics;
- add CI workflows;
- add hostile-filesystem defenses;
- add mount identity tracking;
- add random temporary naming;
- introduce `dist/`;
- add automatic Git staging.

32. Required proof/gate surfaces

Add or update axiom-free/public gate surfaces only where they state real project invariants.

The whole-theory audit itself is an executable trust gate, not a Rocq theorem.

Required executable proof-audit gates:

- certified constants included;
- certified mutual inductives included;
- surviving named assumptions rejected;
- all `Printer.Axiom` categories rejected;
- all `Printer.Variable` rejected;
- opaque bodies descended;
- unused Fido axiom caught;
- external axiom through opaque internal theorem caught;
- unused assumed-positive inductive caught;
- closed Section theorem accepted;
- certified module coverage exact.

Do not add weak theorem statements merely to increase the gate count.

33. Acceptance criteria

The milestone is complete only if all applicable conditions hold.

Binding contract

- This directive is copied verbatim into `.review/NEXT_STEPS.md`.
- Contract committed before implementation.
- Completion report gives contract commit SHA.
- Codex reviews against it.
- No architectural conflict is silently implemented.

Proof audit

- Whole-certified-theory roots include constants and inductives.
- Surviving named assumptions are checked.
- All disallowed assumption categories reject.
- Audit descends opaque bodies.
- `make prove` runs the complete audit.
- Module coverage runs in `make prove`.
- Transient adversarial tests cover axiom, opaque dependency, unused inductive assumption, variable, and closed Section.
- No tracked axiom-bearing fixtures.

Sink simplification

- Stage-record subsystem is deleted.
- No records, parser, nonce, local stage directory, or central stage remains.
- Root `.fido` contains exact marker + optional lock only.
- Sibling suffix is `.fido-tmp-v1`.
- Complete tree scan is fail-closed and two-phase.
- Nested `.fido` of any type rejects.
- Foreign Go/module rules remain.
- Complete desired image stages before first install.
- Handled failures clean created temps immediately.
- Crash residue converges after stale lock removal.
- EXDEV has no copy fallback.
- Sink is materially smaller and simpler.

Generated Buildx artifact

- One `generated-module` ordinary layer contains exactly canonical go.mod + recursive `.go`.
- No `.fido` or temp residue in the layer.
- Generated outputs are not stored as mutable cache authority.
- Go e2e consumes this layer.
- Working-tree regeneration consumes this layer.
- Staged verification consumes this layer.

Tracked output

- Root go.mod is tracked.
- Canonical recursive `.go` files are tracked.
- No dist directory.
- All tracked Go/module bytes have exact Fido header.
- Old no-tracked-Go seal deleted.
- Generated-output policy gate replaces it.
- `.gitignore` ignores only root `.fido/` and recursive temp suffix for this concern.

Regeneration

- `make regenerate` uses the cached generated layer once.
- It applies the pristine artifact through the same sink.
- It preserves dirty non-Go files.
- It rejects foreign Go/module/nested `.fido`.
- It does not independently render.

Pre-commit

- Exports Git index once.
- Uses exported staged tree as Buildx context.
- Does not use unstaged working tree as authority.
- Compares root go.mod and recursive `.go`.
- Compares exact path sets and exact bytes.
- Missing/new/stale/nested outputs all fail.
- Does not auto-stage.
- Leaves working tree unchanged.
- Gives actionable regeneration/staging instructions.
- Bypassability is documented as prototype policy.

Build/e2e

- `make prove` is complete.
- `make check` remains green.
- Canonical generated module builds/runs directly.
- `go build ./...` blocks on failure.
- `go vet` remains nonblocking.
- Empty and multi-package differential fixtures remain.
- Current witness output/goldens remain correct.

Documentation

- All active docs match implementation.
- `NEXT_STEPS` binding rule is stated.
- Record/staging-directory architecture is gone.
- Threat model is honest and narrow.
- Tracked generated-output policy is clear.
- PROGRESS remains compact.
- PAINFUL_LESSONS remains architectural.

34. Completion report

When complete, report:

- contract commit SHA;
- final implementation commit SHA;
- files added, changed, and deleted;
- exact whole-theory audit root set;
- all assumption categories rejected;
- every transient audit fixture and result;
- confirmation `make prove` runs the complete audit;
- sink line-count/code deletion;
- exact suffix ownership rule;
- nested `.fido` behavior;
- complete sink algorithm and threat model;
- every sink crash/failure/recovery test;
- generated-module Docker stage structure;
- exact files in `/generated`;
- how generation inputs exclude committed generated output as authority;
- `make regenerate` implementation;
- tracked generated files added;
- `.gitignore` changes;
- pre-commit staged-index export command;
- exact recursive comparison algorithm;
- proof that comparison checks path set and bytes;
- all proof/build/e2e/precommit commands and results;
- code deleted because it belonged to stage records;
- every new handwritten OCaml file and why it is irreducible/filesystem-only;
- every new/materially modified Section and dependency review;
- Codex dispositions;
- confirmation all autonomous loops stopped.

Do not retain a correctness flaw as a known limitation.

If this contract cannot be implemented correctly, stop, classify the obstacle as an architectural conflict, notify the user, and wait.

35. Hard stop

After all criteria pass:

1. Stop every autonomous/Ralph/background/iterative loop.
2. Do not infer or begin a next milestone.
3. Commit the checkpoint.
4. Notify the user through the configured phone/completion-notification channel that the checkpoint is ready for review.
5. Wait.

Bottom line

The permanent repaired boundary is:

  complete whole-theory proof audit
    over constants + inductives + surviving assumptions
  +
  GoProgram / SafeProgram / direct renderer unchanged
  +
  one pristine content-addressed Buildx generated-module layer
  +
  tracked root go.mod + recursive generated .go
  +
  staged-index pre-commit comparison
  +
  simple dirty-directory synchronization:

    .fido/marker
    .fido/index.lock

    final-file.fido-tmp-v1
      -> rename to final-file

One lock.
One reserved suffix.
No records.
No parser.
No nonce.
No stage directory.
No mount database.
No dist directory.
No invisible architecture changes.
