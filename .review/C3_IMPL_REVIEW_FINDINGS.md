# C3 Implementation Review #1 — BLOCKING finding set (record for the bounded confirmation)

Review: Implementation Review, non-confirmation, over `fea6493..1180b49`.
Verdict: **BLOCKING** — 5 findings (F1–F5). Complete finding set (completeness declaration present).
Codex task: `task-mrsswimg-5qkc3q` (2026-07-20T05:57Z). No architecture change required; repairs fit the contract.

## F1 — the old exactly-one source authority remains LIVE (competing authority)
A `CONFINED` comment is not a visibility boundary. `AllPackagesOneMain`/`ProgValid`/`prog_ok`/`prog_ok_iff`
remain globally exported under old authoritative names (GoCompile.v:77); `semantic_ok_b` is proved `= prog_ok`
then reflected against `ProgValid` (GoCompile.v:1546); the "direct SourceProgramValid reflection" traverses the
old bridges (GoCompile.v:5744); helpers/fixtures still expose `go_compile_ok_of_prog_ok`/`GoCompile_of_prog_ok`/
`reject_no_compile`/direct `prog_ok` asserts (GoCompile.v:6448+); witnesses use `GoCompile_of_prog_ok`
(WitnessMulti.v:39); the gate retains the old bridge (axiom_gate.v:333).
**Required:** make the factored judgments + their DIRECT executable reflection the SOLE current source authority.
Delete / locally scope / unmistakably RENAME the current-fragment helper; migrate callers/fixtures/theorem
names/gates/docs. Retain ONLY the universal theorem that today's factored rules imply the exactly-one consequence.

## F2 — public publication can still sink BEFORE validation
`Fido Emit` is a standalone public command decoding + calling `Fido_sink.sync` immediately (g_fido.mlg:215), no
validation evidence, no orchestration boundary. Witnesses materialize then immediately emit with no Go between
(Witness.v:120, WitnessMulti.v:49); `make emit` stops after the emit stage which already sank (Makefile:62);
`make regenerate` ordering fixes only that one workflow.
**Required:** ONE enforceable public validate-then-publish workflow for arbitrary DirectoryImages; the low-level
sink/export must GENUINELY be internal / unavailable as a standalone public publication; every witness + target
uses that workflow, validates pristine bytes first, publishes only the original pristine bytes.

## F3 — the fresh runner + negative matrix do not distinguish Go rejection from runner failure
Unchecked ops: manifest `mktemp` (Dockerfile:677), fresh-root create + `chmod` (705), both `sort` (725),
build-log create (737). A failed fresh `mktemp -d` leaves `_fresh` empty → targets like `/./go.mod` (container
root in the root-running stage). `rej_conv` treats every nonzero as Go rejection (864); `expect_reject` same
(931); `_FRESH_BUILD_LOG` not cleared at entry → case K reads the prior collision log (1019). So the negative
conversion set + C/D/E/F/H/S/future cases can pass WITHOUT Go running.
**Required:** check every temp-file/fresh-root/mode/sort/enumeration/materialization/log op before continuing;
expose a DISCRIMINATED outcome separating runner failure from literal-Go status; clear per-run outputs; negative
fixtures must prove Go RAN + produced the expected class; add regressions for the unchecked failures.

## F4 — the readable gate still includes concrete FIXTURE-ONLY surfaces (≥26)
Beyond the removed `Example`-kind, ≥26 fixed-program `Lemma`/`Theorem` fixtures remain gated: 5 GoIndex
regression fixtures (axiom_gate.v:604), report/construction fixtures (654), fact-table fixtures (666),
overflow/conversion/duplicate/simultaneous-failure/mixed-order scars (677) — declared as fixed-program theorems
(GoCompile.v:6903–7193). Plus the old-authority bridge (axiom_gate.v:333).
**Required:** remove these concrete fixture checks + the old-authority bridge from the readable gate; keep them
compiled + covered by the whole-theory audit.

## F5 — current documentation/status certify behavior not provided (reconcile AFTER F1/F2)
ARCHITECTURE.md:264 + CLAUDE.md:94 describe kernel exactness through `prog_ok_iff`; COLLECTION_AUDIT.md:28
retains `prog_ok` as a current proof/spec view; README.md:124 asserts `Fido Emit` runs only after validation
(contradicted by F2); CLAUDE.md:22 says non-standalone but CLAUDE.md:360 documents `make emit` as a direct
sinking target; ARCHITECTURE.md:72 claims every arbitrary-length representable path is safe to materialize
(contradicts the platform-limit amendment — over-long paths must fail loud at materialization);
SOURCE_FOREST_STATUS.md:33 declares all closeout defects resolved (incl. the 4 failed) + still has a historical
"FINAL barrier ACTIVE" label (:297).
**Required:** reconcile all permanent prose/gates/audit rows/status to the ACTUAL authority + public workflow;
historical active labels unmistakably historical.

# ============================================================================================
# Bounded confirmation #1 (Codex task-mrsvhs1y, over repair range 1180b49..29872f5) — BLOCKING
# F4 CLOSED. F1/F2/F3 remain OPEN (deeper). F5 OPEN (depends on F1-F3 + one repair-induced item).
# ============================================================================================

## F1 — OPEN (deeper): the exactly-one decision is still the COMBINED rule, not the two factored roots
- `AllPackagesOneMain` remains globally exported under the old authoritative name (GoCompile.v:87/90).
- `source_valid_b`/`pkg_all_ok` still EXECUTE the combined exactly-one rule (`ps_main_count = 1`), not the two
  factored judgments as SEPARATE roots (GoCompile.v:1527).
- `source_valid_b_iff` reaches `SourceProgramValid` THROUGH `source_valid_b_frag` + `current_package_rules_exactly_one`
  (GoCompile.v:5740) — still a bridge from the old current-fragment computation, NOT a direct executable
  reflection of the two factored judgments.  Fixtures/witnesses still use this second executable decision (6446).
- **Required:** ONE shared executable decision reflecting `PackageDeclsUnique` AND `MainPackagesHaveEntry` as
  SEPARATE roots (each its own decidable half + direct reflection), consumed by elaboration AND fixtures.  The
  exactly-one property may remain ONLY as an unmistakably-named current-fragment CONSEQUENCE theorem — not the
  executable decision, not a peer public authority.  Rename `AllPackagesOneMain`.

## F2 — OPEN (deeper): no enforceable general validate-then-publish; sink not structurally internal
- `Fido Materialize` remains a public side-effecting command accepting an arbitrary destination (g_fido.mlg:211).
- The public Dune library still EXPORTS the module containing `Fido_sink.sync` (plugin/dune:8).
- `fido-apply` is a directly-callable CLI invoking `Fido_sink.sync` (e2e/fido_apply.ml:30) — comments + Make
  prerequisite ordering are NOT an internal capability boundary (Makefile:77).
- `make regenerate` handles only the fixed canonical artifact; there is NO public orchestration for an arbitrary
  approved `DirectoryImage` that exports -> fresh-validates -> publishes its original bytes.
- **Required:** ONE enforceable arbitrary-image validate-then-publish ENTRY POINT, and STRUCTURALLY hide/restrict
  the materializer + sink so neither is independently usable as publication.

## F3 — OPEN (deeper): negative matrix lacks class-specific evidence; injection incomplete
- `rej_conv`/`expect_reject` assert only "Go ran + nonzero" — they do NOT distinguish compiler/package rejection
  from directory collision or another Go failure (except case K) (Dockerfile:865/937).
- The injected `find`/`mktemp`/`sort` regressions always fail their FIRST invocation; they do NOT exercise
  FRESH-root enumeration, fresh-root/build-log allocation, or the SECOND sort (Dockerfile:687/754/771).
- Directory enumeration still uses unchecked `ls -A ... 2>/dev/null` — errors collapse into the "empty directory"
  class (Dockerfile:687).
- **Required:** inject + verify EACH fallible phase independently (counting stubs), check EVERY enumeration
  status, make negative helpers assert CLASS-SPECIFIC evidence from the fresh per-run log.

## F5 — OPEN: docs still certify unresolved behavior (reconcile AFTER F1-F3) + one repair-induced item
- SOURCE_FOREST_STATUS:33/63, README:124, ARCHITECTURE:240 repeat "only live root"/"internal sink"/"general
  enforceable workflow"/complete-runner-regression claims the implementation does not yet provide.
- **repair-induced (classified):** plugin/g_fido.mlg:3 header still says decoded bytes are handed to the
  dirty-directory sink, though the command now calls the pristine materializer.
- **Required:** reconcile docs ONLY after F1-F3 reflect enforceable reality; fix the g_fido.mlg header now.
