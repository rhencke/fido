# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.**  A compact ledger — the full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`; commit-level
history is the git log (the archive).

## Anchors & authority
- Campaign master plan installed @`e1138cf`; baseline `5e7efd8adf38473a931a0144ede62b2caa90272a`.
- **Active checkpoint: C3.**  Authority chain: `.review/NEXT_STEPS.md` (pointer) → functional contract
  `.review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md` (sha256 `a13779c2…3814f212`) → accepted basis
  `.review/REVIEW_BASIS.md` → current repair authority `.review/C3_SEMANTIC_PROSE_CLOSEOUT.md`
  (`human_override: C3-semantic-prose-closeout-1`).
- Each C0..C6 checkpoint is activated ONLY by explicit Rob authorization.  **C4 and every later checkpoint
  remain FORBIDDEN.**

## Completed checkpoints (each Codex-GREEN and human-approved; git log has the detail)
| Checkpoint | Scope | Result |
|---|---|---|
| C0 / C0A / C0B | preflight + occurrence-index spike; snapshot-local occurrence identity + total navigation; exact source-occurrence correspondence | GREEN, approved |
| C1 / C1A / C1B | specification-shaped file roots + path-keyed source forest; standard-collection foundations + collection audit; collection-policy enforcement | GREEN, approved |
| C2 | production occurrence index (`GoIndex`), snapshot-local refs, indexed traversal | GREEN, approved |
| C3 (structural) | one retained indexed elaboration, occurrence-keyed facts, structured diagnostics | GREEN @`fea6493`; superseded by the C3 closeout below |

## C3 — Fresh-Image Literal-Build closeout (ACTIVE)
Goal: `GoCompile` accepts exactly what the pinned one-shot `go build ./...` accepts for every representable
rendered program (source typing + package semantics + the cmd/go default-output logic — one main per package,
directory collision — excluding platform filesystem limits); materialize / validate / publish through a fresh
disposable Docker build; keep the tracked generated module byte-exact.

- **Substantive implementation state: complete.**  A serial-review closeout, then Rob's weedwhacker directive
  (delete both manifest systems, Docker as the one fresh-build runner under a cooperating-developer threat
  model, F1 as an index-free source specification plus a separate proved retained-bucket production
  implementation), then the final-cleanup directive (fail-closed fresh-runner state machine + fault tests;
  restored component-based `package_import_path_inj` / `_deterministic`; corrected `semantic_ok_b` /
  `erased_report` claims).  Each phase's bounded confirmation was recorded and closed per its hard cap.  The
  runner, package-import proofs, lower component authority, readable gate (386/386), zero-assumption boundary,
  fresh-image + publication architecture, manifest/checksum deletion, source-specification vs production split,
  generated-byte identity, and size reduction are all CLOSED by review; no C4 work exists.
- **Current repair — `human_override: C3-semantic-prose-closeout-1`** (`.review/C3_SEMANTIC_PROSE_CLOSEOUT.md`):
  a prose-and-authority-only batch closing the one remaining blocking class from the final-cleanup confirmation
  — malformed comments, obsolete phase names, dead file/theorem pointers, and a few false authority statements.
  No executable, proof, gate, collection, or generated-byte change.
- **Candidate SHA:** _pending freeze after the semantic read-through and verification pass._
- **Gate:** 386/386 (unchanged; prose-only batch).
- **Verification:** _pending (`make prove` / `e2e` / `check` / `regenerate` / `regen-guard` + staged, plus the
  change-boundary and symbol/pointer audits)._
- **Final confirmation:** _pending — the one bounded Implementation Review confirmation authorized by this
  override._  A prior revision of this ledger asserted "zero stale/scar hits"; that claim was FALSE (it rested
  on a fixed-token scan) and is withdrawn — no zero-residue claim is made here until the read-through and
  confirmation succeed.
- **Human approval:** pending.  **C4:** forbidden.

## Standing decisions
- **Platform limits out of scope** (Rob, 2026-07-19): Fido models no NAME_MAX/PATH_MAX/disk/memory limit; a
  path is unlimited length for modeling; over-long paths fail loud at OS materialization (ENAMETOOLONG), not in
  the model, grammar, or sink.
- **Two-review policy:** `.review/CODEX_REVIEW_POLICY.md` (Contract Review + Implementation Review; gated by
  `.review/REVIEW_REQUEST.md`).  Each human override authorizes ONE repair batch + at most ONE bounded
  confirmation; a BLOCKING result ENDS autonomous work (no repair or re-request without a new explicit override).
