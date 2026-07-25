# Fido FCB Governance v2

> **Derived reference, not authority.** The code and its gated theorems are the sole authority.  
> **FCB version:** `v2` · **Generated:** `2026-07-25`  
> **Supersedes:** `FIDO_FCB_GOVERNANCE_v1.md`  
> **Repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0` · source snapshot SHA-256 `6e25e8be64a77b7d98609c607d48b1d6917b2bf0480d10fa4a92f1a6bb170eff`  
> **Terminal-bundle basis:** SHA-256 `58abd876a0962bde42e5c9fc0365a8431b88b13beb790440e4b52031c7f8aad0` · handoff SHA-256 `fdfc2c235707aeeef58c566f5fd145850ca606df8d693f5cc6bc81f2112eb143`  
> **Amendment basis:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE` · accepted `2026-07-25` · directive SHA-256 `79a8fa3f6d5a861b82259a578eef6123369dbc9567fbd63288b93c1ce1037b8c`  
> Regenerate this document at each checkpoint acceptance. Delete every stale copy from every model library.  
> This library does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


Rob authorized completion with best-judgment choices on 2026-07-24. FCB v2 retains the closure of LAT-X004 with the reviewers’ shared recommendation: **option (ii), a proved rounding-invariant accepted domain**. ADR-0003 is adopted. ADR-0001 is adopted for the current single target and must reopen at C16. ADR-0002 remains open. ADR-0004 is deferred to C16.

## 1. Authority order

1. **Code and gated theorems** are the sole implementation authority.
2. **Rob’s accepted checkpoint contract and recorded disposition** decide scope and acceptance.
3. **The FCB** is the standing derived reference used to author, implement, and review checkpoints.
4. **Research, reviews, archaeology, and retired directives** are provenance. They may explain a decision but cannot override a live source.

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

**Standing law:** `LAT-X004` is owned by `SPEC-096`, intrinsic `ExprFact`, and `SC-05`. FCB v2 retains the proved rounding-invariant accepted domain.

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

**Rationale:** Reviewing different bytes invalidates every later claim.

### D-15 — Late governance outputs are explicit.

**Standing law:** Artifacts created after the main audit are placed in the sealing graph at their true phase, and the audit never claims to hash future files.

**Rationale:** Late outputs were a recurring source of hidden cycles.

### D-16 — Derived governance ownership is a closed exception.

**Standing law:** Only the named change ledger, file delta, audit, freeze, fixed-point manifest, and SHA manifest receive generated-output ownership by rule.

**Rationale:** A broad exception would erase the one-owner law.

### D-17 — The requested artifact is the answer.

**Standing law:** When the deliverable is a package, repair and validate the package. Review prose cannot substitute for it.

**Rationale:** Users and later tools act on artifacts, not promises about artifacts.

### D-18 — One live identity tuple governs a versioned artifact.

**Standing law:** Archive name, file name, title, version field, supersedes entry, self-reference, and recorded hash must agree.

**Rationale:** A stale identity field can make two versions appear live at once.

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

## 4. ADR register

| ADR | FCB v2 status | Standing result | Reopen trigger |
|---|---|---|---|
| ADR-0001 — Pinned 64-bit target | **ADOPTED FOR CURRENT BASIS** | Go 1.23, linux/amd64, `GOAMD64=v1`; `int` and `uint` are 64-bit and distinct from fixed-width types. | C16 or any earlier target/`uintptr` request. |
| ADR-0002 — Bounded DecimalFloat domain | **OPEN / DEFERRED** | The current bound remains an explicit unresolved restriction. It gains no new correctness claim. | Before C7 accepts broader floating constants, or when measured proof cost justifies a replacement. |
| ADR-0003 — Authority ordering | **ADOPTED** | Definite spec text owns meaning; pinned gc owns target acceptance and adequacy where permitted; gc never narrows required formal latitude. | New evidence of a definite spec/toolchain conflict. |
| ADR-0004 — Multi-platform 64-bit set | **DEFERRED TO C16** | No target beyond go1.23.2 linux/amd64 is covered. | C16. |

## 5. Amendment rule

A settled decision reopens only through Rob and only with new information: a spec fact, a proof obstruction, an implementation fact, or a changed project goal. The amendment must name the affected FCB files, fixed points, closure rows, latitude rows, contracts, checkpoints, and proof gates. The old FCB version is then deleted from every live model library after the replacement is generated.

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

