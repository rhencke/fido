# Fido FCB Governance

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


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

**Standing law:** `LAT-X004` is owned by `SPEC-096`, intrinsic `ExprFact`, and `SC-05`. The settled policy is the proved rounding-invariant accepted domain.

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
| ADR-0002 — Bounded DecimalFloat domain | **OPEN / DEFERRED** | The current bound remains an explicit unresolved restriction. It gains no new correctness claim. | Before C7 accepts broader floating constants, or when measured proof cost justifies a replacement. |
| ADR-0003 — Authority ordering | **ADOPTED** | Definite spec text owns meaning; pinned gc owns target acceptance and adequacy where permitted; gc never narrows required formal latitude. | New evidence of a definite spec/toolchain conflict. |
| ADR-0004 — Multi-platform 64-bit set | **DEFERRED TO C16** | No target beyond go1.23.2 linux/amd64 is covered. | C16. |

## 5. Amendment rule

A settled decision reopens only through Rob and only with new information: a spec fact, a proof obstruction, an implementation fact, or a changed project goal. The amendment must name the affected FCB files, fixed points, closure rows, latitude rows, contracts, checkpoints, and proof gates. The accepted replacement is generated, verified, and committed under `.review/fcb/current/`; Git history retains superseded versions. Project-library shims change only when the repository or stable bootstrap path changes.

### D-24 — Every live documentation reference resolves at one Git ref.

**Standing law:** Every operational path, file, selector, checkpoint authority, and consultation-map entry in the
live FCB resolves within the one exact Git ref used for the task, unless it is explicitly typed as an external
evidence reference with a recorded availability status. A deleted manifest, renamed file, stale self-version, or
dangling repository path is a blocking documentation defect.

**Rationale:** Git can be the sole source of truth only when the live corpus is self-consistent and every reader
is sent to an object that exists.

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
| Checkpoints affected | None; C4 remains blocked at `9d5246e` and C5 remains forbidden |
| Closure / latitude / acceptance-gate rows changed | None |
| Target/toolchain policy changed | None |
