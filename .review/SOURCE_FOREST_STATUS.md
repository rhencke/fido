# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.**  A ledger, not a plan — the full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`; commit-level
history is the git log (the archive).  Updated at checkpoint boundaries.

## Anchors & authority
- Campaign master plan installed @`e1138cf`; declared/actual baseline `5e7efd8adf38473a931a0144ede62b2caa90272a`.
- **Active checkpoint: C3** (Fresh-Image Literal-Build closeout).  Active authority chain:
  `.review/NEXT_STEPS.md` (pointer) → contract `.review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md`
  (activation `83c398992be5316f7e28fbbe02b94794b85fb34c`, sha256 `a13779c2…3814f212`, basis
  `.review/REVIEW_BASIS.md`) → current repair authority `.review/C3_FINAL_CLEANUP_DIRECTIVE.md`
  (`human_override: C3-final-cleanup-1`).
- Each C0..C6 checkpoint is activated ONLY by an explicit Rob authorization.  **C4 and every later checkpoint
  remain FORBIDDEN** until Rob authorizes.

## Completed checkpoints (each Codex-GREEN and human-approved; details in git log)
| Checkpoint | Scope | Final result |
|---|---|---|
| C0 / C0A / C0B | preflight + occurrence-index spike; snapshot-local occurrence identity + total navigation; exact source-occurrence correspondence | GREEN, approved |
| C1 | specification-shaped file roots + path-keyed source forest (FMapAVL `FilePath` map) | GREEN, approved |
| C1A | standard-collection foundations + repository-wide collection audit (ROOT `cc7a4d7`, FINAL `39be07d`) | GREEN, approved |
| C1B | collection-policy enforcement + plan reconciliation | GREEN, approved |
| C2 | production occurrence index (`GoIndex`), snapshot-local refs, indexed traversal | GREEN, approved (C3 activation 2026-07-18) |
| C3 (structural) | one retained indexed elaboration, occurrence-keyed facts, structured diagnostics; Codex-GREEN @`fea6493` | RETAINED; superseded by the C3 closeout below |

## C3 — Fresh-Image Literal-Build closeout (ACTIVE)
Goal: make `GoCompile` accept exactly what the pinned one-shot `go build ./...` accepts for every representable
rendered program (semantic + cmd/go package/output logic — types, one-main, directory-collision — EXCLUDING
platform fs limits), materialize/validate/publish through a fresh disposable Docker build, and keep the tracked
generated module byte-exact.

- **History (git log has the detail):** the manual whole-snapshot closeout and Implementation Review #1 +
  confirmations #1/#2/#3 each returned BLOCKING and were repaired one batch each.  Rob's C3 WEEDWHACKER
  DIRECTIVE (2026-07-20) then deleted BOTH manifest systems (no checksum system exists), made Docker the ONE
  fresh-build runner (cooperating-developer threat model), kept F1 as an index-free SPECIFICATION decision plus
  a separate proved retained-bucket production implementation, and set a net-deletion target + a review HARD CAP.
  The weedwhacker batch and its `C3-weedwhacker-repair-1` follow-up EACH went to their one bounded confirmation
  and EACH returned BLOCKING; per the hard cap both were closed / recorded / stopped.
- **Current repair — `human_override: C3-final-cleanup-1`** (`.review/C3_FINAL_CLEANUP_DIRECTIVE.md`): ONE batch
  closing the four repair-1 confirmation findings — (1) the fresh-build runner is an explicit fail-closed state
  machine (infrastructure failure never masquerades as a Go outcome; four fault self-tests); (2) the missing
  package-import proofs restored over the component authority (`package_import_path_inj` +
  `package_import_path_deterministic`, both gated); (3) false semantic/workflow comments corrected
  (`semantic_ok_b` = the SOURCE half only; `erased_report` = the source-semantic report, distinct from the full
  `erased_elaboration_report`); (4) the tracked-tree malformed-prose sweep + active-authority files.  Gate
  substitution: removed `package_import_path_InputEqual` (now a corollary of `_deterministic`) +
  `package_import_path_root` (base-case shape), added the two direct claims → readable gate stays **386/386**.
- **Deletions in this batch:** the superseded weedwhacker findings diary and the unreferenced
  `REVIEW_BASIS_TEMPLATE.md` (git history is the archive); compacted `REVIEW_REQUEST` / `NEXT_STEPS` /
  this ledger; pure banner decoration and duplicated charter restatements in the Makefile / Dockerfile /
  `GoCompile` + `GoIndex` headers (the layer charter stays ARCHITECTURE.md, not restated per module).  No
  invariant, theorem, or rationale was deleted to meet a byte number.
- **State during repair:** `.review/REVIEW_REQUEST.md` stays `closed`; the ONE authorized final confirmation is
  requested only after the candidate is frozen and every required check is GREEN (candidate SHA recorded then).
  A BLOCKING result ENDS autonomous work.  C4 remains FORBIDDEN.

## Standing decisions
- **Platform limits OUT of scope** (Rob, 2026-07-19): Fido models no NAME_MAX/PATH_MAX/disk/memory limit; a path
  is unlimited length for modeling; over-long paths fail loud at OS materialization (ENAMETOOLONG), not in the
  model/grammar/sink.
- **Two-review policy:** `.review/CODEX_REVIEW_POLICY.md` (Contract Review + Implementation Review; gated by
  `.review/REVIEW_REQUEST.md`).  The active repair directive's hard cap governs: ONE repair batch + at most ONE
  bounded confirmation per human override; a BLOCKING result ENDS autonomous work (no repair or re-request
  without a new explicit human override).
