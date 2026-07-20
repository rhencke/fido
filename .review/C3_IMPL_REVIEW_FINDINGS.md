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

# ============================================================================================
# Bounded confirmation #2 (Codex task-mrsx8y3d, over repair range 29872f5..b48b542) — BLOCKING
# F4 CLOSED (385 surfaces). F1/F2/F3 each a residual; F5 open (+ GoEmit.v missed).
# ============================================================================================

## F1 — OPEN: PRODUCTION (elaborator) does not consume the shared factored decision
- The factored `pkg_decls_unique_b`/`main_pkgs_have_entry_b` + reflections are correct (GoCompile.v:97/5733),
  BUT the real elaborator decides package validity from `bucket_diags_elems` + diagnostic-list emptiness
  (GoCompile.v:6140); its proof bridge still passes through `pkg_all_ok_one_main` + `current_grammar_one_main`
  (GoCompile.v:2997).  So FIXTURES use the `package_summaries`-based `pkg_all_ok`; PRODUCTION uses the
  retained-bucket diagnostic authority — the factored reflection does NOT root the production decision.
- **Required:** ONE retained-bucket executable package decision, directly reflecting BOTH factored roots,
  shared by elaboration + diagnostics + fixtures.  Exactly-one stays a consequence, not the production bridge.

## F2 — OPEN: publication-before-validation capability remains + repair-induced trust defect
- `Fido Materialize <image> To "<dir>"` is still a public side-effecting writer (g_fido.mlg:227) that writes
  the image to any empty caller dir BEFORE Go validation (fido_sink.ml:348) — standalone publication.
- No general arbitrary-image entry point fresh-validates then publishes.
- repair-induced trust defect: `fido-apply` checks only `Sys.file_exists` (fido_apply.ml:44) — not a regular
  non-symlink marker with exact contents BOUND to the published bytes; the emit-stage regression manually
  creates the marker + publishes before go-e2e (Dockerfile:620).  So an arbitrary tree + any marker-shaped path
  reaches `Fido_sink.sync`.  Declaring deliberate forgery out of scope WEAKENS the binding invariant without an
  authorizing human decision.
- **Required:** ONE enforceable arbitrary-image workflow that fresh-validates the EXACT pristine bytes and
  invokes an INACCESSIBLE publication sink only after success.  A public low-level writer OR a marker-only
  attestation cannot remain a publication bypass (marker must be BYTE-BOUND).

## F3 — recorded items CLOSED, one new: missing "extra fresh file" regression
- The runner detects an EXTRA path (path-set diff) but the tests cover only omitted materialization + byte
  corruption (Dockerfile:816); NO regression injects an EXTRA entry into the fresh root.  The contract requires
  it (C3_MANUAL_CLOSEOUT_DIRECTIVE:266).  (Previously observable, missed by review #1 + confirmation #1.)
- **Required:** add an extra-fresh-file regression.

## F5 — OPEN: docs (+ GoEmit.v missed) still certify unresolved behavior
- **GoEmit.v:11/:52** still name a LIVE `Fido Emit` boundary / claim a `Fido Emit` command exists (missed in
  the F5 sweep; present in the initial candidate).
- SOURCE_FOREST_STATUS:82 declares all repairs complete + "sink un-runnable on unvalidated bytes" (premature).
- ARCHITECTURE:320 + README:126 assert an enforceable single validate-before-publish workflow the public
  materializer + marker-only apply do not yet provide.
- **Required:** reconcile after F1/F2 reflect enforceable reality; fix GoEmit.v now.

# ============================================================================================
# Bounded confirmation #3 (Codex task-mrsyqc1k, over repair range b48b542..42c536e) — BLOCKING
# F3 + F4 CLOSED.  F1/F2 OPEN (architectural/threat-model direction) + F5.
# → ESCALATED to Rob as an architectural conflict (see .review/C3_ARCH_CONFLICT.md).
# ============================================================================================

## F1 — OPEN: package execution still has TWO executable authorities (not one shared bucket decision)
- Fixtures/helpers execute `pkg_all_ok` (package_summaries, GoCompile.v:97); production executes
  `bucket_diags_elems` (bucket lengths, :2988) and `elaborate_indexed` decides via `list_is_nil diags` (:6146).
- `pkg_diags_empty_iff_rules` proves the COMBINED classifier ≡ the two factored Props AFTER execution; it does
  NOT make the separate uniqueness/entry decisions the shared EXECUTABLE root (:3036).  Fixture ctors still use
  `source_valid_b` (:6492).  → two executable views joined by proof bridges; grammar masks it (both ⇒ =1).
- **Required:** ONE executable decision over the retained buckets deciding the two factored rules SEPARATELY,
  consumed by elaboration + diagnostics + fixtures.  [DIRECTION: changes the index-free vm-computable fixture
  decision path — a design-direction decision.]

## F2 — OPEN: the manifest is SELF-ATTESTED, not validation provenance (threat-model decision)
- `fido_apply` never runs the pinned build nor verifies the manifest ORIGINATED from one; it accepts any
  regular manifest whose md5s match the current files, then sinks (fido_apply.ml:59).  The emit-stage test
  computes a manifest locally + publishes BEFORE go-e2e validation (Dockerfile:616/631).  → any Go-rejected
  tree + its freshly-computed manifest can be published; the fido_apply.ml:18 comment leaves forging both tree
  and manifest out of scope — the threat-model weakening the PRIOR confirmation rejected.
- No arbitrary-image public orchestrator does `exact export → fresh Go validation → sink original bytes`
  (contract C3_MANUAL_CLOSEOUT_DIRECTIVE:277); `Fido Materialize` + the directly-callable apply CLI remain
  independently usable.
- **Required:** ONE enforceable arbitrary-image workflow that itself fresh-validates the exact bytes then
  invokes an INACCESSIBLE sink; a checksum file cannot stand in for validation provenance.  [CONFLICT: an
  inaccessible validation-embedded sink conflicts with fido_apply's filesystem-only charter (it runs no
  programs) + the two-stage OCaml-sink / Go-validation design; and whether the validation-before-publication
  invariant must resist a DELIBERATE local bypass (vs the cooperating-developer level the Docker-DAG + hook
  provide) is the THREAT-MODEL decision the reviewer says needs human authorization.]

## F5 — OPEN (after F1/F2) + repair-induced collection-audit omission
- ARCHITECTURE:316 still describes a presence-only marker + "cannot publish unvalidated" + the forgery caveat;
  PROGRESS:183 declares the workflow GREEN; CLAUDE:112 says validation necessarily precedes the sink;
  SOURCE_FOREST_STATUS:99 claims F1/F2 repaired + caveat dropped (contradicts fido_apply.ml, which kept a
  reworded caveat).
- **repair-induced:** COLLECTION_AUDIT omits the new `SM = Map.Make(String)` in fido_apply.ml (:24).
- **Required:** reconcile after F1/F2 are structurally true; add the SM row now.

## F3 — CLOSED (extra-fresh-file regression rejects before Go).  ## F4 — CLOSED (gate 386, only the universal
## pkg_diags_empty_iff_rules added; no fixture surfaces reintroduced).
