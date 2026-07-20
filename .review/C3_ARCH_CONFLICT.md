# C3 closeout — ARCHITECTURAL CONFLICT report (STOP + await Rob's direction)

**Status:** the autonomous repair→confirm loop is STOPPED at a genuine decision point. Per CLAUDE.md
("if an objective defect cannot be repaired without changing its architecture, threat model, or
responsibility boundaries, report an architectural conflict and stop; do not implement an alternative
autonomously") this needs your direction before I proceed.

## How we got here (all pushed, all `make check` + `make regenerate` GREEN at each candidate)

- Manual closeout (CL-3..CL-10) → candidate `1180b49`.
- **Implementation Review #1** (`fea6493..1180b49`) → BLOCKING, 5 findings F1–F5 → repaired `29872f5`.
- **Confirmation #1** (`1180b49..29872f5`) → BLOCKING; F4 closed, F1/F2/F3 deeper + F5 → repaired `b48b542`.
- **Confirmation #2** (`29872f5..b48b542`) → BLOCKING; F1/F2/F3 residual + F5 → repaired `42c536e`.
- **Confirmation #3** (`b48b542..42c536e`) → BLOCKING; **F3 + F4 CLOSED**; **F1, F2, F5 open**.

Findings converged (F3/F4 closed), but F1 and F2 have been the SAME ask across all three confirmations, and
each round shows they require an architecture/threat-model decision that is yours, not mine.

## The two decisions I need from you

### F2 (the blocker) — the validation-before-publication THREAT MODEL + the sink boundary

The reviewer rejects EVERY marker/checksum I've tried (presence-only, then byte-bound md5 manifest) with the
same core objection: **a checksum file is self-attested — a caller can compute a valid manifest for ANY tree
(even one `go build` rejects) and publish it.** The reviewer's required outcome:

> one enforceable arbitrary-image workflow that **itself** fresh-validates the exact bytes and only then
> invokes an **inaccessible** publication sink; a caller-created checksum cannot stand in for validation.

This conflicts with the established architecture:

- `fido_apply` (the sink CLI) is **filesystem-only by charter** (it walks no Rocq term, no AST, runs no
  programs — enforced by `tools/ocaml-origin-gate.sh`). Making it run `go build ./...` itself violates that
  charter and the origin gate.
- Validation (`go build`) runs in a **separate Go/alpine Docker stage** (`go-e2e`); the sink is **OCaml**.
  They are deliberately different toolchains/stages. Fusing "validate + sink" into one atomic, inaccessible
  step is a transport-boundary redesign.
- The reviewer explicitly frames the remaining gap as a **threat-model question**: must the invariant resist a
  **deliberate local bypass** (someone extracting the binary / hand-writing a manifest), or only **accidental**
  publication of unvalidated output by a cooperating developer (which the current Docker-DAG ordering +
  `make regenerate: e2e` prerequisite + pre-commit hook already give, at the same assurance level the hook
  documents)? The reviewer says declaring the weaker model "needs an authorizing human decision."

**Options (your call):**
- **(A) Cooperating-developer threat model is sufficient.** Authorize it explicitly: the Docker-DAG ordering
  (sync COPYs from go-e2e; `--target sync` is unbuildable without a passing `go build`) IS the boundary; the
  checksum is a byte-integrity aid, not a provenance oracle; delete the "provenance" framing and the caveat,
  and I reconcile the docs to that honest, weaker-but-stated claim. (Smallest change; matches the documented
  pre-commit assurance level and the review policy's "local-verifier attacks out of scope".)
- **(B) Resist deliberate bypass — build the inaccessible validation-embedded orchestrator.** This is a real
  architecture change: e.g. a single stage/tool that materializes → runs pinned `go build` → sinks the
  original bytes, with no independently-runnable sink and no standalone materializer. Needs a decision on WHERE
  `go build` and the OCaml sink co-locate (a combined toolchain image, or the sink calling `go build`, waiving
  the filesystem-only charter), and probably an amended origin gate.
- **(C) Something else** you have in mind.

### F1 — one shared bucket executable vs proven-equivalent views

The reviewer wants the production (retained-bucket) package decision AND the fixture decision to be **one
executable** that decides the two factored rules separately — not two computations (`bucket_diags_elems` for
production, `pkg_all_ok` over `package_summaries` for fixtures) joined by proof bridges, even though I proved
the production side ≡ `PackageRulesValid` directly (`pkg_diags_empty_iff_rules`).

Making fixtures decide over the retained **buckets** changes the deliberately **index-free, vm-computable**
fixture path (`source_valid_b`) into an index-dependent one. Feasible, but it's a design-direction change to a
working, intentional design — I'd like your go-ahead before reworking it (and it's moot if F2 pushes a broader
transport redesign).

## What I did NOT change (awaiting you)

The F1/F2 code stays at `42c536e`. I only: recorded the findings, corrected the docs that contradicted the
code (the byte-binding is real but is byte-integrity, not validation provenance — I removed the "dropped the
caveat / cannot publish unvalidated" overclaims), and added the `SM = Map.Make(String)` row to the collection
audit. `REVIEW_REQUEST` is CLOSED so the stop-hook won't loop.

**C4 remains FORBIDDEN.** Tell me which option for F2 (and whether to rework F1), and I'll implement it as one
batch and re-request the bounded confirmation.
