# NEXT_STEPS — active authority pointer

- **Active checkpoint:** C3 (Source Forest) — closeout under review.
- **Active contract:** `.review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md`, activation commit `83c3989`,
  content sha256 `a13779c2e55c…`.
- **Review basis:** `.review/REVIEW_BASIS.md`, sha256 `890b0d9ffc18…`.
- **Human amendment (SUPERSEDES every contrary option in the contract and prior addenda):**
  `.review/C3_WEEDWHACKER_DIRECTIVE.md`, committed `9caa929`, sha256 `62c9dbbe707a…`, human_override token
  `C3-weedwhacker-human-decision`.  See that file for the binding decisions; do NOT restate them here.
- **Repair authorization:** `human_override: C3-weedwhacker-repair-1` — repair the five bounded-confirmation
  findings (`.review/C3_WEEDWHACKER_CONFIRMATION_FINDINGS.md`) as ONE batch, then request ONE final bounded
  confirmation; a BLOCKING result ENDS autonomous work.
- **Standing amendment (Rob, 2026-07-19) — PLATFORM LIMITS OUT OF SCOPE:** Fido does NOT model platform-specific
  filesystem/materialization limits (NAME_MAX, PATH_MAX, disk, memory); a path is UNLIMITED length for modeling.
  `GoCompile == go build ./...` is exact for the SEMANTIC + cmd/go package/output logic (types, one-main,
  directory collision), EXCLUDING platform fs limits (over-long paths fail loud at OS materialization,
  ENAMETOOLONG — not in the model/grammar/sink).
- **Current state:** the weedwhacker repair-1 batch is under implementation; live status in
  `SOURCE_FOREST_STATUS.md`.  Do NOT describe any candidate as accepted until a non-stale Codex GREEN.
- **C4 is FORBIDDEN** until explicit Rob authorization.
