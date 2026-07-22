# Unsupported and Restricted Scope — reviewed ledger

**Current-only.** This is a reviewed ledger of every scope restriction that is live in tracked prose *right
now* — not a history dump. When a restriction is lifted, its entry is deleted (git holds the history); when a
new explicit exclusion is introduced, an entry is added in the SAME checkpoint. Every "unsupported / out of
scope / excluded / unrepresentable frontier / threat-or-build-or-platform restriction" in current tracked
prose must map to exactly one entry here — no restriction may live only in a code comment.

Classifications: REVIEWED TARGET RESTRICTION · REVIEWED MODEL EXCLUSION · REVIEWED THREAT-MODEL EXCLUSION ·
REVIEWED BUILD-ENVIRONMENT RESTRICTION · TEMPORARY FEATURE FRONTIER · REJECTED DESIGN.

Rules: "hard" or "not implemented" is never a permanent rationale; a temporary frontier must name the
foundation/checkpoint that removes it; a target/model/threat restriction must carry a reviewed rationale; a
future holistic review may reopen every entry.

---

## SR-001 — Pinned linux/amd64 64-bit validation target

- **Classification:** REVIEWED TARGET RESTRICTION.
- **Exact excluded case:** the certified semantics fix `int`/`uint` to 64-bit ranges (`Ints`), and the
  operational end-to-end validation runs on exactly one target: `GOOS=linux`, `GOARCH=amd64`, the
  digest-pinned `golang:1.23-alpine` image, rendered `go.mod` language `1.23`. 32-bit targets, other
  architectures (arm64, …), and other operating systems are not a validation target and their `int`/`uint`
  word size is not modeled.
- **Exact reason:** a single pinned deployment/validation target lets `GoCompile == go build` be an EXACT,
  differentially-tested claim against one real toolchain, and lets `int`/`uint` be concrete 64-bit types
  (type-distinct from `int64`/`uint64`) with complete value/render/proof surfaces — instead of a
  target-parametric width abstraction threaded through every numeric proof before it earns its keep.
- **Why difficulty is not the reason:** target-parametric `int`/`uint` semantics are a *cross-cutting*
  abstraction (a target descriptor in every constant, conversion, value, and render proof) whose only current
  consumer would be a portability claim Fido does not yet make. The restriction is a deliberate theorem-domain
  boundary, not avoidance — see ADR-0001 for the full option analysis.
- **Benefit obtained:** concrete 64-bit `Ints`; an exact one-target differential for `GoCompile`; no
  premature target-config abstraction; a reproducible pinned e2e.
- **Valid Go / environments lost:** building/running the generated module on 32-bit or non-amd64/non-linux
  targets is outside the validated envelope (the generated Go is not architecture-specific, but no claim is
  made about it there).
- **Enforcement points:** `Ints.v` (`int`/`uint` = 64-bit, distinct from `int64`/`uint64`); `Makefile`
  header (platform pinned linux/amd64); `Dockerfile` go-e2e stage (`GOOS=linux GOARCH=amd64`, explicit
  `[ "$goos" = linux ]` / `[ "$goarch" = amd64 ]` guards); digest-pinned `golang:1.23-alpine`; the e2e
  boundary witnesses.
- **Guarantees relying on it:** `Ints` width theorems; the `GoCompile == go build` differential; the
  rendered `go.mod` language pin.
- **Reconsideration triggers:** a request to support 32-bit, arm64, or another OS; any portable-Go public
  claim; `uintptr`/pointer/layout work needing a richer target model; a toolchain/target image change; a
  proof benefit from a target descriptor that exceeds its cost.
- **Linked:** `.review/decisions/ADR-0001-PINNED-64-BIT-TARGET.md`; `ARCHITECTURE.md` (ModuleSpec is NOT a
  TargetConfig).
- **Approval state:** PROPOSED — pending Rob's review with the C4 candidate (tracks ADR-0001). Date: 2026-07-22.

---

## SR-002 — Platform filesystem / resource limits not modeled

- **Classification:** REVIEWED MODEL EXCLUSION.
- **Exact excluded case:** operating-system path/name/space limits (`NAME_MAX`, `PATH_MAX`, inode/disk/memory
  ceilings). Paths and module paths are modeled at ARBITRARY length with NO magic numeric cap; an over-long
  path is not rejected by the grammar, the model, or the sink.
- **Exact reason:** these limits are platform-specific and not part of the Go-source/`cmd/go` semantic
  domain. `GoCompile == go build` is exact for the semantic and `cmd/go` package/output LOGIC (types, one
  main per package, directory collision) and deliberately EXCLUDES platform fs limits. An over-long path
  fails LOUDLY at the OS boundary (printing/materialization → `ENAMETOOLONG`), never as a silent narrowing in
  the grammar.
- **Why difficulty is not the reason:** a numeric length cap would be *easy* to add — it is rejected because a
  magic cap in a validity/grammar predicate is a HACK that models the wrong domain (a platform limit, not a
  language fact); correctness does not depend on it.
- **Benefit obtained:** the grammar/model stays a faithful language model with no arbitrary constant; failures
  surface at the correct (OS) layer.
- **Valid Go / environments lost:** none at the language level — only that Fido makes no claim about behavior
  once a real filesystem's limit is exceeded (that is the OS's to signal).
- **Enforcement points:** `FilePath.v` and `ModulePath.v` (explicit "ARBITRARY LENGTH — no length cap"
  headers); the OCaml materializer/sink surface OS errors fail-loud rather than pre-checking limits.
- **Guarantees relying on it:** the exactness scope of `GoCompile == go build` (semantic + cmd/go logic, not
  platform fs limits).
- **Reconsideration triggers:** a decision to model a specific deployment filesystem's limits as a
  correctness property (not currently in scope).
- **Linked:** `ARCHITECTURE.md`; memory note `no-magic-numeric-caps`.
- **Approval state:** REVIEWED / ACCEPTED (standing project law). Date: 2026-07-22.

---

## SR-003 — Cooperating-developer / local-verifier-tamper threat boundary

- **Classification:** REVIEWED THREAT-MODEL EXCLUSION.
- **Exact excluded case:** the publication-safety machinery (pre-commit hook, `make check`, the
  validate-before-publish Docker DAG) gives reasonable assurance against ACCIDENTAL stale/unbuilt generated
  output for a COOPERATING developer. It does NOT attempt to resist a DELIBERATE local bypass — extracting a
  built binary, hand-editing the Dockerfile/hooks, `git commit --no-verify`, or otherwise tampering with the
  verifier that runs locally.
- **Exact reason:** the property Fido enforces is "the published bytes were validated by a pinned
  `go build ./...`," expressed as the Docker workflow graph (a failed build makes the `sync` image
  unbuildable). A local actor who controls the machine can always circumvent a local verifier; defending that
  is a different (and much larger) threat model than the prototype-stage guarantee this project makes.
- **Why difficulty is not the reason:** this is a boundary of the STATED guarantee, not an unbuilt feature.
  The hook is intentionally bypassable (`--no-verify`, a documented prototype escape); the design goal is
  accidental-staleness protection, and adding tamper-resistance would change the threat model, not fix a bug.
- **Benefit obtained:** a simple, honest publication guarantee (validated bytes) without a checksum/manifest
  system that could not prove a build succeeded anyway.
- **Valid Go / environments lost:** none — this is about attacker capability, not representable programs.
- **Enforcement points:** the Docker `generated-module`/`sync` stage graph (validate-before-publish);
  `make check` + pre-commit hook (working-tree / staged byte compare); `tools/*-gate.sh`. All at the
  cooperating-developer assurance level.
- **Guarantees relying on it:** the "published == validated bytes" publication claim; the absence of a
  checksum/manifest subsystem.
- **Reconsideration triggers:** a decision to make Fido's publication path resistant to a deliberate local
  adversary (would require a fundamentally different trust base).
- **Linked:** `CLAUDE.md` (Standing technical law §1); `ARCHITECTURE.md` (trust boundary);
  `.review/CODEX_REVIEW_POLICY.md` (local-verifier attacks declared out of scope).
- **Approval state:** REVIEWED / ACCEPTED (declared threat model). Date: 2026-07-22.

---

## SR-004 — Host Rocq / build environment unsupported (buildx-only)

- **Classification:** REVIEWED BUILD-ENVIRONMENT RESTRICTION.
- **Exact excluded case:** proving/building on a developer's host Rocq/OCaml install is not supported. All
  verification runs through pinned Docker buildx (`make check`/`prove`/`e2e`).
- **Exact reason:** a pinned container is the only reproducible, version-exact toolchain; a host install
  varies by machine and cannot back a reproducible axiom-free claim. The pin is the toolchain authority.
- **Why difficulty is not the reason:** supporting arbitrary host toolchains is not a correctness feature —
  it would *weaken* reproducibility. The restriction exists to guarantee the exact pinned toolchain, not
  because host builds are hard.
- **Benefit obtained:** reproducible, version-pinned proofs and e2e; a single toolchain of record.
- **Valid Go / environments lost:** none representable — only developer convenience of a host build.
- **Enforcement points:** `Makefile` (all targets route through buildx); `Dockerfile` pinned base images and
  digests; documented "local host Rocq is NOT supported."
- **Guarantees relying on it:** the reproducibility of every `Print Assumptions`/`Fido Audit Assumptions`
  result and the e2e differential.
- **Reconsideration triggers:** a decision to support and pin a host toolchain as an equal authority (not
  planned).
- **Linked:** `CLAUDE.md` (Workflow & commands); `Makefile`; `Dockerfile`.
- **Approval state:** REVIEWED / ACCEPTED (standing workflow law). Date: 2026-07-22.

---

## SR-005 — Major-version module path forms excluded

- **Classification:** REVIEWED MODEL EXCLUSION.
- **Exact excluded case:** the narrow canonical `ModulePath` (slash-separated lowercase `[a-z][a-z0-9.]*`
  segments) EXCLUDES — does not narrow — otherwise-valid Go module path forms: `/v2`+ major-version suffixes
  and `gopkg.in/…` paths. The mapping to a Go 1.23 `module` directive is exact one-way; the reverse does not
  hold.
- **Exact reason:** the module path is a semantic program fact rendered into `go.mod`; a deliberately narrow,
  canonical, decidable-equality form is modelled exactly and completely, rather than admitting the full
  `cmd/go` module-path grammar (with its version-suffix and vanity-host special cases) ahead of any consumer
  that needs them. Excluding is honest (unrepresentable), narrowing would be plausible-but-wrong.
- **Why difficulty is not the reason:** the excluded forms are excluded as UNREPRESENTABLE, not admitted with
  a conservative approximation — consistent with faithful-or-fail-loud. They return when a real need
  (imports/multi-module) justifies the broader grammar, by proof.
- **Benefit obtained:** an exact, canonical, decidable module-path model with a proven one-way render into a
  real `go.mod`.
- **Valid Go / environments lost:** modules whose path uses a `/vN` major-version element or a `gopkg.in`
  vanity form cannot be represented as the generated module's path.
- **Enforcement points:** `ModulePath.v` (the segment grammar + one-way mapping note); `ARCHITECTURE.md`
  (ModuleSpec row); `GoRender` module-path rendering.
- **Guarantees relying on it:** `ModulePath` decidable equality / canonical render; the exact `go.mod`
  module directive.
- **Reconsideration triggers:** imports or multi-module support that requires representing version-suffixed
  or vanity module paths.
- **Linked:** `ModulePath.v`; `ARCHITECTURE.md`.
- **Approval state:** REVIEWED / ACCEPTED (model faithfulness). Date: 2026-07-22.

---

## SR-006 — Source-file naming restrictions

- **Classification:** REVIEWED MODEL EXCLUSION.
- **Exact excluded case:** the `FilePath` grammar rejects underscores, leading dots, and the `.go` filename
  stems / directory names that `go build` itself ignores or reserves: no hidden files/dirs, no `_test.go`,
  no `testdata`/`vendor` directory components. (A stem like `testdata.go` or `vendor.go` is allowed — only
  the DIRECTORY names are reserved.)
- **Exact reason:** the represented file set is exactly the source files a whole-program `go build ./...`
  compiles. Test files and build-ignored/reserved directories are excluded because they are NOT part of that
  compiled set; representing them would model files the build does not compile.
- **Why difficulty is not the reason:** these are excluded to match `go build`'s own file-selection LOGIC
  exactly, not because parsing them is hard — admitting a `_test.go` file would be a faithfulness bug, not a
  feature.
- **Benefit obtained:** the file map == the `go build ./...` compiled set, keeping the admissibility claim
  exact.
- **Valid Go / environments lost:** test files (`_test.go`), files under `testdata`/`vendor`, and
  hidden/underscore-named files cannot be represented (they are not part of the compiled program anyway).
- **Enforcement points:** `FilePath.v` (`component_ok`, `reserved_dir`, `filename_ok`, `path_ok` + the
  `no_test`/`no_testdata` examples).
- **Guarantees relying on it:** the file map's correspondence to the `go build ./...` compiled set.
- **Reconsideration triggers:** a decision to model test compilation or build-tagged/ignored files as part of
  the program.
- **Linked:** `FilePath.v`; `ARCHITECTURE.md`.
- **Approval state:** REVIEWED / ACCEPTED (model faithfulness). Date: 2026-07-22.

---

## SR-007 — Imports on hold (closed world)

- **Classification:** TEMPORARY FEATURE FRONTIER.
- **Exact excluded case:** no import syntax is representable; the import section of every source file is
  intrinsically empty. A program that imports any package cannot be represented.
- **Exact reason:** the closed-world guarantee (`GoCompile` must resolve every import to a package owned by
  the SAME `GoProgram`, or reject the whole program — no stdlib/cache/network/vendor/workspace/ambient
  escape) is a real property that must be built and proven before import syntax is admitted. Admitting import
  syntax without that resolver would be a fail-open hole.
- **Why difficulty is not the reason:** this is a sequenced frontier, not a permanent decision — the
  foundation is named below and its removal expands expressiveness by proof.
- **Foundation/checkpoint needed to remove:** the imports arc — the owned-package import resolver + the
  closed-world rejection theorem — plus explicit Rob sign-off (imports specifically require approval).
- **Benefit obtained:** a sound closed-world model today; no premature import surface that could admit an
  unresolved/ambient dependency.
- **Valid Go / environments lost:** every program that imports a package (including the standard library).
- **Enforcement points:** `GoAST` (`source_imports` intrinsically empty; no import syntax); `ARCHITECTURE.md`
  Closed-world section; `CLAUDE.md` Standing law §9.
- **Guarantees relying on it:** the closed-world admissibility claim for the current fragment.
- **Reconsideration triggers:** the imports arc landing with its resolver + closed-world proof, under
  explicit sign-off.
- **Linked:** `ARCHITECTURE.md` (Closed world); `CLAUDE.md` §9; memory note `primitives-before-libraries`.
- **Approval state:** REVIEWED / ACCEPTED as a temporary frontier. Date: 2026-07-22.

---

## SR-008 — Unrepresented Go syntax / features (the admitted fragment)

- **Classification:** TEMPORARY FEATURE FRONTIER.
- **Exact excluded case:** the admitted fragment is `SPrintln` over primitive literals (bool, the ten integer
  types, float32/64, complex64/128, exact strings) plus ONE source-shaped `EConvert TypeSyntax GoExpr`
  conversion naming the closed sixteen source names. Everything else is UNREPRESENTABLE (absent from the AST),
  not rejected: other declarations, calls, parameters, non-`main` packages, arithmetic / imaginary-literal /
  `real`/`imag` / NaN / Inf syntax, and conversion targets outside the sixteen names
  (`bool`/`string`/`uintptr`/`any`/`error`/`comparable`/unknown/qualified).
- **Exact reason:** the certified fragment is kept small and grows ONLY by proof principles, never by lists of
  examples. A construct that cannot be modelled exactly is removed from the AST (made unrepresentable) rather
  than admitted with a conservative narrowing — faithful-or-fail-loud.
- **Why difficulty is not the reason:** each excluded construct returns when its exact model + full
  type/value/render/safety proofs land (the expressiveness expands by proof) — the exclusion is a sequencing
  boundary, not a claim that the construct is too hard to ever do.
- **Foundation/checkpoint needed to remove:** each construct has its own future checkpoint that lands its
  exact AST node together with its complete proof surface (per the ARCHITECTURE layer charter and the
  Source-Forest campaign); no construct is admitted ahead of its proofs.
- **Benefit obtained:** every retained layer is complete and correct in itself and builds only on
  already-complete foundations; the axiom-free surface stays honest.
- **Valid Go / environments lost:** the vast majority of Go programs — anything beyond the fragment above.
- **Enforcement points:** `GoAST` (only the fragment's constructors exist); `GoNames` (the closed sixteen-name
  class); `ARCHITECTURE.md` (GoAST row); `CLAUDE.md` (the admitted-fragment paragraph).
- **Guarantees relying on it:** every axiom-free layer theorem is stated over exactly this representable set.
- **Reconsideration triggers:** each future Source-Forest / feature checkpoint that lands a new construct with
  its proofs.
- **Linked:** `ARCHITECTURE.md`; `CLAUDE.md`; `PROGRESS.md`; memory note `campaign-source-forest`.
- **Approval state:** REVIEWED / ACCEPTED as a temporary frontier. Date: 2026-07-22.
