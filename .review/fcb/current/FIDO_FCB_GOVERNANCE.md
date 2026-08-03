# Fido FCB Governance

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`;
> `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`; `FCB-A007-POST-C4-MECHANICAL-SERIES`;
> `FCB-A008-STRICT-CHECKPOINT-SCOPE-AND-M0-CLOSEOUT`, `FCB-A009-COMPLEXITY-FIT`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> C4 and M0 are ACCEPTED; M1 Source Diet is the sole active work and C5 is not authorized; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


Rob authorized completion with best-judgment choices on 2026-07-24. The settled closure of LAT-X004 stands with the reviewers’ shared recommendation: **option (ii), a proved rounding-invariant accepted domain**. ADR-0003 is adopted. ADR-0001 is adopted for the current single target and must reopen at C16. ADR-0002 remains open. ADR-0004 is deferred to C16.

## 1. Authority order

1. **Code and gated theorems** are the sole implementation authority.
2. **Rob’s accepted checkpoint contract and recorded disposition** decide scope and acceptance.
3. **The Git-hosted FCB under `.review/fcb/current/`** is the standing derived reference used to author, implement, and review checkpoints.
4. **Project-library bootstrap shims** locate the Git-hosted FCB. They are not FCB content or authority.
5. **Research, reviews, archaeology, and retired directives** are provenance. They may explain a decision but cannot override a live source.

A model may record `APPLIED`. Only Rob may accept, countersign, reopen, reject, or amend a governing decision. A model must never convert its own confidence into acceptance.

## 2. Permanent governance rules

- One authority owns each meaning. Derived views must prove exact agreement and may not become peers.
- Public-base changes are failures of the architecture unless Rob reopens the relevant fixed point with new information.
- Internal forms are disposable. Keeping a proof-hostile internal shape after a cleaner one is found is a failure under `SC-21`.
- Every `OUT` row states its price. No exclusion may be silent.
- A theorem statement must expose the full accepted guarantee. A stronger proof body does not repair a weak public theorem.
- Candidate status is not acceptance. Green gates are evidence, not a substitute for review of the live path.
- A mature standard collection is required when it fits the semantic role. Project-authored collection storage is forbidden.
- No fuel, gas, bounded-step surrogate, trusted fallback, or parallel shortcut path may enter the certified route.
- Git is the sole canonical FCB store. Model project libraries contain bootstrap shims only and never own or edit FCB bytes.
- Every serious task resolves one exact repository ref, takes every FCB document from that single ref, and never mixes FCB files across refs. Git's content addressing is the integrity mechanism; there is no separate checksum manifest.

## 3. Settled Decisions Register

### D-01 — Sealing graphs are acyclic.

**Standing law:** No artifact may contain its own hash or a hash that depends on it. The realized coverage graph must be checked as a directed acyclic graph.

**Rationale:** This prevents impossible freezes and makes every published identity reproducible.

### D-02 — Specification and pinned-gc authority are ordered.

**Standing law:** Definite Go-spec text owns meaning. Pinned gc owns the accepted target profile and adequacy evidence where the spec grants latitude or is silent. Pinned gc never shrinks a behavior set that the spec requires the model to admit.

**Rationale:** This keeps external fidelity without turning one implementation into a second language specification.

### D-03 — Racy runs use direct STEP-NONDET semantics.

**Standing law:** The model retains the memory model’s permitted racy outcomes. Race history is not stored in `State`; `DataRace` is a derived bad prefix.

**Rationale:** A post-race havoc mode would add state or a second run authority.

### D-04 — Constant-value ownership never moves.

**Standing law:** `LAT-X004` is owned by `SPEC-096`, intrinsic `Compilable.ExpressionFact`, and `SC-05`. The settled policy is the proved rounding-invariant accepted domain.

**Rationale:** Acceptance and value are distinct. The selected policy keeps one deterministic fact without a gc-specific value system.

### D-05 — Provenance outcomes are typed.

**Standing law:** Evidence is `PASS-CONFIRMED`, `PENDING-PROVENANCE`, or `FAIL`. Pending is not green and must remain visible.

**Rationale:** Unconfirmed evidence must not masquerade as a confirmed basis.

### D-06 — Every live directive or contract is self-contained.

**Standing law:** Normative text may cite superseded material only as provenance, never as an imported command.

**Rationale:** One live authority cannot depend on a dead second authority.

### D-07 — The Human-Review Index is discovered.

**Standing law:** Open human acts are generated from canonical rows and statuses, not hand-copied.

**Rationale:** Hand lists go stale and can silently erase unresolved decisions.

### D-08 — Pin the full distribution, not one executable.

**Standing law:** Confirmed toolchain evidence requires verified distribution bytes. A local tree may support pending evidence only.

**Rationale:** `go` delegates to compiler, linker, standard library, and other files under `GOROOT`.

### D-09 — Ownership is change-granular.

**Standing law:** Every substantive change has exactly one owner; files carry the set of owners of their contained changes. Derived governance outputs may use the closed T-0 exception only.

**Rationale:** File-level ownership is too coarse and can hide unrelated edits.

### D-10 — Fixed points protect meaning-bearing projections.

**Standing law:** Protection targets exact clauses, fields, or regions, not whole mutable rows.

**Rationale:** Governance columns and generated metadata may change without weakening the protected meaning.

### D-11 — The selector algebra is closed.

**Standing law:** Selectors, normalization, overlap, and canonical hash input are defined. Their coverage must equal the structural diff.

**Rationale:** A vague selector gives the executor power to weaken preservation.

### D-12 — Inspect archives before extraction.

**Standing law:** Archive paths, entry types, duplicates, headers, modes, timestamps, and expected membership are checked before any file is written.

**Rationale:** Extraction can hide path tricks, duplicate entries, or normalization collisions.

### D-13 — Protection strength is directive-owned.

**Standing law:** The fixed-point registry is derived from frozen normative rows, field for field. The executor cannot choose weaker selectors.

**Rationale:** Preservation cannot depend on the implementer’s judgment after the fact.

### D-14 — Every reviewed artifact begins with a hash handshake.

**Standing law:** The recipient independently verifies the full SHA-256 before review or amendment.

**Scope:** external / non-Git review packages and the historical volley handshakes. It does NOT apply to the
live Git FCB, which is identified by ref and path and carries no documentation checksum (D-23, D-24, A003).

**Rationale:** Reviewing different bytes invalidates every later claim.

### D-15 — Late governance outputs are explicit.

**Standing law:** Artifacts created after the main audit are placed in the sealing graph at their true phase, and the audit never claims to hash future files.

**Rationale:** Late outputs were a recurring source of hidden cycles.

### D-16 — Derived governance ownership is a closed exception.

**Standing law:** Only the named change ledger, file delta, audit, freeze, fixed-point manifest, and SHA manifest receive generated-output ownership by rule.

**Rationale:** A broad exception would erase the one-owner law.

**Scope:** the historical terminal-bundle sealing system. The "SHA manifest" named here is that bundle's, not
the live Git FCB's, which has none.

### D-17 — The requested artifact is the answer.

**Standing law:** When the deliverable is a package, repair and validate the package. Review prose cannot substitute for it.

**Rationale:** Users and later tools act on artifacts, not promises about artifacts.

### D-18 — One live identity tuple governs a versioned artifact.

**Standing law:** Archive name, file name, title, version field, supersedes entry, self-reference, and recorded hash must agree.

**Rationale:** A stale identity field can make two versions appear live at once.

**Scope:** historical and versioned external artifacts. Living FCB files are unversioned and identified by Git
ref and path (A003), so no version field or recorded hash participates in their identity.

### D-19 — Late-output membership has one owner.

**Standing law:** Phase inventory, build order, final-set equation, and verifier use the same exact set of late artifacts.

**Rationale:** Several near-miss freezes came from different lists describing the same phase.

### D-20 — The check-function inventory is closed.

**Standing law:** Every named `check_*` function is declared, implemented once, owned by one tool, and cited by a gate.

**Rationale:** Orphan checks and missing checks both create false confidence.

### D-21 — Provenance facts are internally consistent.

**Standing law:** Version counts, recurrence counts, statuses, and lineage facts are mechanically checked.

**Rationale:** Contradictory provenance makes the audit trail unreliable even when code is unchanged.

### D-22 — Opaque capabilities retain their causal objects.

**Standing law:** When a production stage builds a proof-carrying causal object and publishes an opaque capability or failure result, the hidden representation retains that exact object. Selected projections plus equality to recomputation are insufficient provenance. Opacity controls access; it does not permit data loss.

**Rationale:** Equality can establish extensional agreement after the original object was discarded, but later proofs cannot consume the exact identities, predecessors, and causal history that established the result.

### D-23 — Git is the sole canonical FCB store.

**Standing law:** The live FCB is committed under `.review/fcb/current/` in Git. Model project libraries contain
one bootstrap shim only. Root `CLAUDE.md` gives Claude Code the same bootstrap. A serious task resolves one exact
Git ref; reads `.review/fcb/current/INDEX.md`; takes every file the Index names from that same ref; reads
`.review/NEXT_STEPS.md` from that same ref; and stops on any missing or dangling reference. There is no checksum
manifest to verify — Git content-addresses the bytes. FCB files from different refs may not be mixed.

**Rationale:** Full FCB mirrors in several model libraries create duplicate ownership, manual synchronization
work, and a real risk that different conversations consult different bytes. Git already provides common access,
history, review, and exact identity.

## 4. ADR register

| ADR | Current status | Standing result | Reopen trigger |
|---|---|---|---|
| ADR-0001 — Pinned 64-bit target | **ADOPTED FOR CURRENT BASIS** | Go 1.23, linux/amd64, `GOAMD64=v1`; `int` and `uint` are 64-bit and distinct from fixed-width types. | C16 or any earlier target/`uintptr` request. |
| ADR-0002 — Bounded Float.Decimal domain | **OPEN / DEFERRED** | The current bound remains an explicit unresolved restriction. It gains no new correctness claim. | Before C7 accepts broader floating constants, or when measured proof cost justifies a replacement. <!-- FIDO-HUMAN-ACT:ADR-0002 --> |
| ADR-0003 — Authority ordering | **ADOPTED** | Definite spec text owns meaning; pinned gc owns target acceptance and adequacy where permitted; gc never narrows required formal latitude. | New evidence of a definite spec/toolchain conflict. |
| ADR-0004 — Multi-platform 64-bit set | **DEFERRED TO C16** | No target beyond go1.23.2 linux/amd64 is covered. | C16. <!-- FIDO-HUMAN-ACT:ADR-0004 --> |

## 5. Amendment rule

A settled decision reopens only through Rob and only with new information: a spec fact, a proof obstruction, an implementation fact, or a changed project goal. The amendment must name the affected FCB files, fixed points, closure rows, latitude rows, contracts, checkpoints, and proof gates. The accepted replacement is generated, verified, and committed under `.review/fcb/current/`; Git history retains superseded versions. Project-library shims change only when the repository or stable bootstrap path changes.

### D-24 — Every live documentation reference resolves at one Git ref.

**Standing law:** Every operational path, file, selector, checkpoint authority, and consultation-map entry in the
live FCB resolves within the one exact Git ref used for the task, unless it is explicitly typed as an external
evidence reference with a recorded availability status. A deleted manifest, renamed file, stale self-version, or
dangling repository path is a blocking documentation defect.

The relation is COMPLETE IN BOTH DIRECTIONS, and each direction is enforced:

- every row of `FIDO_FCB_REFERENCES.tsv` resolves in this tree (or is explicitly typed off-tree with a stated
  availability), and its owning document carries exactly one `<!-- FIDO-FCB-REF:<ID> -->` marker on a line that
  also contains that row's exact path;
- every repository-rooted operational path appearing anywhere in the live authority corpus is declared by
  exactly one row.

**The same manifest owns CORPUS MEMBERSHIP.** Each row carries a closed `corpus_role`: an `authority` is a
current normative source, and a `reference` resolves and is owned without becoming one. Only a present,
readable, UTF-8 repository FILE may be an authority — never a directory, a symlink, or an off-tree reference.
Generated human and ledger views are references, because their canonical data source carries the authority. The
scanned corpus IS the set of `authority` rows, so a new authority is scanned by declaring a row, never by
editing a checker. The declarations that ASSIGN authority are themselves checked: the live-file table in the
FCB Index states a role for every file beside the manifest and must agree with it in both directions; the
document `NEXT_STEPS` names after `Authority:`, and the `contract:` and `review_basis:` paths in
`REVIEW_REQUEST`, and the M-series plan the Index names, must all be authorities.

**The PATH UNIVERSE comes from the repository, not from the checker.** A gate that decides which namespaces
exist can only prove the relation over the subset it recognised. The inventory is therefore derived from the
exact snapshot being checked — Git enumeration in a working tree, the exported tree in a snapshot — and no
repository namespace or root file is written into a tool.

**One canonical repository path.** A repository path is POSIX, relative to the root, with no leading slash, no
leading `./` in stored form, no empty, `.` or `..` segment, no backslash and no NUL, and it resolves inside
the root without passing through a symlink. Those rules together ARE canonicality: split-then-join is the
identity, so nothing is left for a separate normalized comparison to catch. Malformed input is REJECTED, never
normalized and accepted, because normalizing lets two spellings name one target. One canonical target has
exactly one row. The same parser governs manifest targets, manifest owners, live-set entries, Index table
cells, and paths found in authority prose.

**How a document NAMES a path.** Four exact forms, all derived from the inventory: a token that IS an existing
repository path; a token rooted at a discovered top-level DIRECTORY, which is how a missing path under a
namespace is found; a dot-prefixed repository name carrying a directory part or an extension; and the explicit
root-relative form, a dot and a slash before the file name. That fourth form is the rule for MISSING ROOT
paths: a bare word is never a path, so an authority that means to name a root file which does not exist must
write it with that prefix or it is indistinguishable from ordinary prose. A slash-containing phrase is not a
path either — a top-level FILE is not a namespace.

That rule binds this document too. Prose may not use the dot-slash form as a placeholder for "some path",
because by this decision that spelling IS a reference to a file of that name.

**External evidence lives in a distinct namespace.** An off-tree row uses an `external:` identity that cannot
parse as a repository path, does not begin with a repository top-level entry, and does not resolve under the
root. Retyping a missing repository file as external evidence can therefore never make it pass.

**An owner marker binds an exact token.** The marker line must carry the row's canonical path delimited on
both sides. One path is never proved by a longer path that contains it: `dune` is not present because
`dune-project` is. <!-- FIDO-FCB-REF:DUNE-PROJECT -->

**The live FCB set is flat and closed.** Every immediate entry of the canonical live directory is a regular
non-symlink file with exactly one manifest row and exactly one live-file table line. A directory, a symlink or
any other entry there is an undeclared subtree, and admitting one silently would be an FCB change made by
accident rather than by amendment.

Validating only the declared rows is not compliance with this decision. A corpus that names a path with no row
at all still sends a reader at nothing, and a gate that inspects only its own chosen rows reports green while it
happens. Neither is a hard-coded scan list compliance: a typed row proves the target EXISTS, and proves nothing
about whether that document's own references are complete. The active repair, the functional contract and the
accepted review basis are exactly where an unscanned authority hides, because they are the documents that
assign the current work.

**Rationale:** Git can be the sole source of truth only when the live corpus is self-consistent and every reader
is sent to an object that exists. Completeness is what makes that a property of the corpus rather than of the
list somebody remembered to write down — and membership has to be data for the same reason the references are.

### D-25 — Names are owned by their scope.

**Standing law:** A module, nested module, record, or other real namespace supplies a concept's domain.
Declarations do not repeat that domain through `Go` prefixes, type-name prefixes, or initialisms such as
`cp_`, `ewf_`, `tnft_`, `di_`. Where two declarations in one Rocq namespace need different names, use full
semantic words or a real subnamespace; never an abbreviation as a pseudo-namespace. Old names receive no
aliases, compatibility modules, deprecated wrappers, or re-exports — Git history is the only compatibility
layer. Cross-namespace use is qualified: `Compilable.Program`, `Typing.Program`, `Syntax.Program` and
`Safe.Program` are distinguished by the namespace that owns them, which also shows the reader where each is
defined.

**Rationale:** Redundant names obscure the authority chain, make qualified names noisy, and let a large
module simulate structure through prefixes. Scope-relative names expose the actual architecture, so a missing
abstraction or a bad module boundary becomes visible instead of hiding behind a prefix.

### D-26 — `Emit.Image` seals authority while its transport carrier remains reducible.

**Standing law:** `Emit.Image` retains the exact `Safe.Program`, exact `go.mod` bytes, exact `.go` file map,
and one opaque `Emit.Mint.Token` indexed by those same values. The raw token constructor is private.
`Emit.Mint.issue` is the sole authority-producing operation. The visible image pack constructor is a reducible
carrier constructor, not a mint: it cannot authorize foreign bytes without an inhabitant of the indexed token
type. `Emit.of_safe` is the canonical production packer; `Emit.of_safe_at` transports the same authority along
the exact source equality and is not a second mint.

No helper may accept arbitrary bytes plus an independently supplied equality or provenance proof. A postulated
token or predecessor remains outside the certified path and must be rejected by the materializer's existing
assumption-closure guard before any filesystem effect.

**Rationale:** Opaque module sealing removes the projection bodies required by the certified term transport's
kernel reduction. Sealing the intrinsic mint authority preserves the one-authority law without moving
rendering into OCaml or weakening payload provenance.

### D-27 — Mechanical debt is removed before the permanent runtime base.

**Standing law:** After C4 acceptance and before C5 checkpoint-definition Step 0, Fido completes M1 through M4
in order. The M-series is mechanical: it may delete dead text and code, measure and reshape build dependencies,
and refactor proof units and tooling, but it may not change Go meaning, the accepted or rejected program sets,
diagnostic results, public correctness guarantees, trust boundaries, or generated bytes.

Git owns archaeology. Source prose states current local facts only and remains only when its removal would make
the nearby code, proof, invariant, or boundary harder to understand correctly.

A fast partial check must identify itself as partial. It never substitutes for the full acceptance gate.

Semantic ownership is not split merely to create parallel work. Build and cache changes require measured
before-and-after evidence and complete cache keys. M4 begins only after M2 and M3 evidence exists and Rob accepts
the exact refactor plan.

**Rationale:** Maintenance cost is a real correctness cost when stale prose obscures current authority, large
serial units delay feedback, or duplicated checks create divergent build paths. Mechanical cleanup must reduce
that cost without weakening evidence or changing semantics.

### D-28 — A checkpoint blocks only on its accepted contract.

**Standing law:** Review the whole current system, but block the active checkpoint only for a defect which
violates its accepted semantic, production, proof, artifact, or required dependency contract. The place where a
defect is discovered does not assign it to that checkpoint.

A wider repository, governance, documentation, tooling, cleanup, performance, or process finding is recorded and
assigned to the earliest mandatory follow-up checkpoint. It may block the active checkpoint only when it makes
that checkpoint's result false, unsafe, unverifiable, unusable, or contrary to an explicit acceptance dependency.

The follow-up assignment is mandatory and must remain visible in Git until disposition. It is not permission to
ignore the finding. It is also not permission to expand the current checkpoint merely because the work is useful.

After acceptance, a checkpoint reopens only on new evidence against its accepted contract. Later hygiene work
cannot retroactively redefine completion.

**Rationale:** Whole-system review prevents local blindness. Strict scope prevents an accepted semantic
checkpoint from becoming the unbounded owner of every useful improvement found nearby.

### D-30 — Complexity must fit the component's real job.

**Standing law:** Make each component as exact and rigorous as its real job requires, but no more complicated
than that job justifies.

A design states the component's real job before proposing machinery. Implementation keeps only machinery which
directly serves that job. Review reports `Complexity fit: PASS` or `Complexity fit: BLOCKED — <plain reason>`.
A new framework, registry, schema, validator hierarchy, compatibility layer or governance surface not already
required by the accepted contract needs Rob's approval before implementation.

No automated gate is created for this judgment. It is a review duty, and a gate around it would be the first
thing the rule forbids.

### D-29 — M0 closes governance after C4 without reopening C4.

**Standing law:** After C4 acceptance and before M1, Fido completes one separately reviewed M0 Governance
Closeout. M0 publishes the C4 disposition, retires repair-state archaeology to Git history, installs the strict
checkpoint-scope law, moves current authority to the M-series, and verifies the existing D-07 and D-24 state
against the accepted snapshot.

M0 changes no Rocq definition, theorem statement, proof body, capability topology, supported or rejected program
set, diagnostic result, extraction path, OCaml transport role, generated byte, or runtime output. It does not
redesign or further harden general-purpose tooling unless the existing tool cannot represent the exact M0 state.

Findings outside this contract are assigned as follows:

```text
source prose, comments, dead files and declarations → M1
build timing, dependency and edit-cost evidence       → M2
auxiliary tool and build-graph architecture           → M3
approved mechanical restructuring                     → M4
```

M0 is separately accepted by Rob. M1 is forbidden until M0 is accepted.

**Rationale:** C4 acceptance and repository governance are both required, but they are different work. M0
preserves the governance duty without using it to extend C4.

## 6. Amendment register

### FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE

| Field | Disposition |
|---|---|
| Amendment | `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` |
| Status | **ACCEPTED** |
| Human owner | Rob |
| Date | `2026-07-25` |
| New information | C4 implementation and theorem topology proved that selected parts plus equality can discard the exact compiler causal object. |
| Reopened fixed point | `ARCH-03` |
| Changed documents | Charter, Fixed Points, Governance, Checkpoint Authoring Guide, Roadmap, Human Review Index, Model Operations, Index, manifest |
| Contracts affected | `SC-16`, `SC-21`, `SC-22` |
| Checkpoint affected | C4 acceptance boundary; C5 dependency |
| Proof gates required | Exact accepted-core retention; exact rejected-core retention; no-reconstruction total queries |
| Closure rows changed | None |
| Latitude rows changed | None |
| Acceptance gates changed | None |
| Target/toolchain policy changed | None |

### FCB-A002-GIT-CANONICAL-FCB-STORAGE

| Field | Disposition |
|---|---|
| Amendment | `FCB-A002-GIT-CANONICAL-FCB-STORAGE` |
| Status | **ACCEPTED** |
| Human owner | Rob |
| Date | `2026-07-25` |
| New information | Full editable FCB mirrors in several model libraries create unnecessary synchronization work and drift risk. |
| Settled decision | Git is the sole canonical FCB store; model libraries contain bootstrap shims only; root `CLAUDE.md` uses the same bootstrap. |
| Changed documents | Every live FCB banner; Index; Governance; Model Operations; Checkpoint Authoring Guide; Human Review Index; manifest |
| Fixed points changed | None |
| Contracts affected | None; distribution and consultation process only |
| Checkpoints affected | None; C4 remains blocked and C5 remains forbidden |
| Closure rows changed | None |
| Latitude rows changed | None |
| Acceptance gates changed | None |
| Target/toolchain policy changed | None |

### FCB-A003-LIVING-DOCUMENTATION

| Field | Disposition |
|---|---|
| Amendment | `FCB-A003-LIVING-DOCUMENTATION` |
| Status | **ACCEPTED** |
| Author | Rob |
| Human owner | Rob |
| Date | `2026-07-25` |
| New information | Once Git was canonical, a per-file SHA-256 manifest and filename version suffixes restated by hand a guarantee Git already provides, and imposed a regeneration duty on every documentation edit. |
| Settled decision | Documentation is living: no version suffixes, no checksum manifest. Blob hash is the version, the commit log is the history, `git rev-parse HEAD:.review/fcb/current` is the identity of the live set. |
| Changed documents | Every live FCB file; Index; stable bootstrap; Governance; Model Operations; Checkpoint Authoring Guide; root `CLAUDE.md`; campaign README and PROVENANCE |
| Fixed points changed | None weakened; ARCH-03's static-capability component paths re-expressed to the unversioned charter filename, distinguished by ref |
| Contracts affected | None |
| Checkpoints affected | None; C4 remains blocked and C5 remains forbidden |
| Closure / latitude / acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |

### FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS

| Field | Disposition |
|---|---|
| Amendment | `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS` |
| Status | **ACCEPTED AS IMPLEMENTED** |
| Author | Claude (external adversarial reviewer) |
| Human owner | Rob |
| Date | `2026-07-25` |
| New information | The first adversarial review of the Git-canonical corpus found A003 only partly applied: dangling version-suffixed paths, a deleted manifest still required by live process text, A003 absent from the register, stale embedded repository bases, and fixed-point paths that resolve to nothing. |
| Settled rule sought | Every operational reference in the live FCB either resolves at the same exact Git ref or is explicitly typed as an external evidence reference with a recorded availability status. |
| Governance decision added | `D-24` |
| Changed documents | Index; Governance; Architecture Charter; Fixed Points; Human Review Index; Model Operations; Checkpoint Authoring Guide; ledger headers; project-library shim; active checkpoint documents |
| Fixed points changed | No count change; components re-expressed so every path resolves or is typed external |
| Contracts affected | None |
| Checkpoints affected | None; C4 was blocked at `9d5246e` when this amendment was accepted, and C5 remains forbidden |
| Closure / latitude / acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |

### FCB-A005-SCOPED-NAME-OWNERSHIP

| Field | Disposition |
|---|---|
| Amendment | `FCB-A005-SCOPED-NAME-OWNERSHIP` |
| Status | **ACCEPTED** |
| Author | the reviewer (A005 scoped naming migration directive) |
| Human owner | Rob |
| Date | `2026-07-26` |
| New information | The theory encoded one scope twice — module domain repeated in declaration names, record type repeated through initials — so readers decoded redundancy and large modules simulated structure with prefixes instead of real namespaces. |
| Settled rule sought | A namespace states its domain once; a declaration names only its role inside that domain; collisions are resolved with the smallest full semantic distinction, never a restored abbreviation. |
| Governance decision added | `D-25` |
| Changed documents | Governance; Index; Human Review Index; Checkpoint Authoring Guide; live prose naming a Rocq symbol |
| Fixed points changed | None |
| Contracts affected | None — no theorem statement or guarantee changes |
| Checkpoints affected | C4 review paused for the migration; the renamed head becomes the sixteenth C4 implementation candidate |
| Closure / latitude / acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |
| Enforcement | `tools/naming-gate.py` via `make names`, wired into `make check` |

### FCB-A006-INTRINSIC-EMIT-IMAGE-MINT

| Field | Disposition |
|---|---|
| Amendment | `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT` |
| Status | **ACCEPTED** — Rob recorded `FCB-A006-intrinsic-emit-image-mint` |
| Author | Primary ChatGPT Fido review thread |
| Human owner | Rob |
| Date | `2026-07-26` |
| New information | The certified transport must kernel-reduce `Emit.transport img`. Opaque module sealing removes the image projection bodies and makes that reduction fail. A transparent carrier with an opaque value-indexed mint witness preserves both computation and intrinsic authority. |
| Settled rule | `Emit.Image` is a reducible carrier retaining the exact `Safe.Program`, exact bytes, and an opaque `Emit.Mint.Token` indexed by those same exact values. The carrier pack constructor is not a mint. `Emit.Mint.issue` is the sole authority-producing operation. |
| Governance decision added | `D-26` |
| Reopened fixed point | `ARCH-11`, only the `Emit.Image` bullet inside Charter §24; every other part of the fixed point remains unchanged |
| Changed documents | Architecture Charter; Fixed Points; Governance; Index; Roadmap; Checkpoint Authoring Guide; Model Operations; Human Review Index; every accepted-amendment banner |
| Contracts affected | `SC-17`, `SC-21`, `SC-22` |
| Checkpoints affected | C4 repair 17 acceptance boundary and the C5 dependency |
| Proof/build gates required | Opaque token-constructor test; foreign-byte construction rejection; postulated-token materialization rejection; positive `nf_all` transport reduction; whole-theory assumption audit; generated-byte identity |
| Closure / latitude / acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |
| OCaml trust boundary changed | None |

### FCB-A007-POST-C4-MECHANICAL-SERIES

| Field | Disposition |
|---|---|
| Amendment | `FCB-A007-POST-C4-MECHANICAL-SERIES` |
| Status | **ACCEPTED** — Rob recorded `FCB-A007-post-C4-mechanical-series` |
| Author | Primary ChatGPT Fido review thread |
| Human owner | Rob |
| Date | `2026-07-26` |
| New information | The repository carries superseded design prose Git already preserves, full builds approach two to three minutes, and no measured account of module cost, dependency fan-out, edit frequency, cache behaviour or duplicated gate work exists. The permanent C5 `Machine` base must not be frozen on top of that debt. |
| Settled sequence | C4 acceptance closeout → M1 Source Diet → M2 Performance Snapshot → M3 Tool and Build Architecture Audit → Rob approves the exact M4 plan → M4 Mechanical Refactor → checkpoint-definition Step 0 → C5 |
| Governance decision added | `D-27` |
| Changed documents | Governance; Index; Roadmap; Checkpoint Authoring Guide; Model Operations; Fixed Points; Human Review Index; every accepted-amendment banner; the new M-series plan under `.review/` |
| Reopened fixed point | None; M1–M4 must preserve every fixed point |
| Contracts affected | None |
| Checkpoints affected | None; C4 remains blocked and C5 remains forbidden. M1–M4 implementation is forbidden until Rob accepts C4 |
| Proof/build gates required | Every M candidate repeats the full acceptance gate: zero assumptions, unchanged public guarantees, unchanged program sets and diagnostics, byte-identical generated Go |
| Closure / latitude / acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |
| OCaml trust boundary changed | None |
| Human act added | `M4-PLAN-APPROVAL` (`DEFERRED`) |

### FCB-A009-COMPLEXITY-FIT

| Field | Disposition |
|---|---|
| Amendment | `FCB-A009-COMPLEXITY-FIT` |
| Status | **ACCEPTED** — Rob recorded `FCB-A009-complexity-fit` |
| Author | Primary ChatGPT Fido review thread |
| Human owner | Rob |
| Date | `2026-08-03` |
| New information | A withdrawn checkpoint reached roughly fifty thousand lines and a self-verifying measurement platform to answer a question a sixty-line shell script answers. Every individual addition was defensible and no rule asked whether the machinery still fit the job. |
| Settled rule | Make each component as exact and rigorous as its real job requires, but no more complicated than that job justifies. |
| Governance decisions added | `D-30` |
| Reopened fixed point | None |
| Contracts affected | Design, implementation and review process only; no semantic contract changes |
| Checkpoints affected | None reopened |
| Closure / latitude / standing acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |
| Proof theorem or generated-byte guarantee changed | None |
| OCaml trust boundary changed | None |
| Human act added | None |

### FCB-A008-STRICT-CHECKPOINT-SCOPE-AND-M0-CLOSEOUT

| Field | Disposition |
|---|---|
| Amendment | `FCB-A008-STRICT-CHECKPOINT-SCOPE-AND-M0-CLOSEOUT` |
| Status | **ACCEPTED** — Rob recorded `FCB-A008-strict-checkpoint-scope-and-M0-closeout` |
| Author | Primary ChatGPT Fido review thread |
| Human owner | Rob |
| Date | `2026-07-27` |
| New information | Requiring all useful repository and FCB infrastructure work to finish before the next checkpoint can enlarge a semantic checkpoint without changing its accepted result. C4 showed that governance hardening can continue indefinitely after the semantic capability is complete. |
| Settled rule | A checkpoint blocks only on defects within its accepted contract or an explicit acceptance dependency. Wider findings are assigned to the earliest mandatory follow-up and cannot silently disappear. M0 performs the post-C4 governance closeout before M1. |
| Governance decisions added | `D-28`, `D-29` |
| Settled sequence | C4 acceptance closeout → M0 Governance Closeout → M1 → M2 → M3 → Rob approves the M4 plan → M4 → checkpoint-definition Step 0 → C5 |
| Reopened fixed point | None |
| Contracts affected | Review and checkpoint-authoring process only; no semantic contract changes |
| Checkpoints affected | C4 is ACCEPTED at `39ea7e3b012ec798c6a756c971c10bb363557ef8` under `C4-ACCEPT-39ea7e3`; M0 was inserted before M1 and is ACCEPTED under `M0-ACCEPT-86a63db`; C5 remains after M4 |
| Closure / latitude / standing acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |
| Proof theorem or generated-byte guarantee changed | None |
| OCaml trust boundary changed | None |
