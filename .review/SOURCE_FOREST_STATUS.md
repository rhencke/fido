# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored Compilation**

_This is a ledger, not a second plan. The full design lives in `.review/SOURCE_FOREST_MASTER_PLAN.md`.
Updated only at checkpoint boundaries._

## Campaign anchors
- Master-plan commit SHA: `e1138cf` (`milestone(contract): install the Source Forest master campaign + activate checkpoint C0`)
- Declared baseline SHA: `5e7efd8adf38473a931a0144ede62b2caa90272a`
- Actual base SHA: `5e7efd8adf38473a931a0144ede62b2caa90272a` (repository tip matched the declared baseline; no intervening work to preserve)
- Active checkpoint: **C3 — Fresh-Image Literal-Build Final Repair** (2026-07-19).  The structural C3
  implementation (One Retained Indexed Analysis, Occurrence-Keyed Facts, Structured Diagnostics) went
  Codex-GREEN @`fea6493` and is RETAINED; Rob then issued a FRESH, self-contained final-repair contract that
  supersedes the prior C3 vocabulary/semantics for exactly-one-main, analysis→elaboration naming,
  output-neutral builds, literal `go build ./...` output behavior, and ambient dirty-tree builds.  The binding
  completion contract is now `.review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md` (= `.review/NEXT_STEPS.md`,
  installed verbatim); the prior `.review/C3_INDEXED_ANALYSIS_DIAGNOSTICS_PLAN.md` is bannered SUPERSEDED
  (history only, not a live authority).  C0/C0A/C0B, C1, C1A, C1B, C2 all Codex-green AND human-approved.
  **C4 and every later Source Forest checkpoint remain FORBIDDEN.**
- Checkpoint contract commit SHA: `e1138cf` (master plan + C0 `NEXT_STEPS.md` + this ledger installed together)

## C3 — Fresh-Image Literal-Build Final Repair (ACTIVE — C3 MANUAL CLOSEOUT, 2026-07-20)
- **Review-process reform + manual closeout (governs):** the serial per-turn stop-hook Codex process is
  replaced by the PERMANENT two-review policy in `.review/CODEX_REVIEW_POLICY.md` (Contract Review +
  Implementation Review, gated by `.review/REVIEW_REQUEST.md`; ordinary turns leave it `state: closed` so the
  stop hook returns immediately).  Rob/ChatGPT ran a MANUAL whole-snapshot audit of `de6bd759d8fe1977bc196b5aaed04aa60b9560b1`
  (accepted as C3's review basis, `.review/REVIEW_BASIS.md`) and found material C3 holes the serial process
  MISSED — so the earlier "serial-Codex GREEN @`c7168e9`" is SUPERSEDED, not final.  Active closeout directive:
  `.review/C3_MANUAL_CLOSEOUT_DIRECTIVE.md`; supporting evidence `.review/C3_MANUAL_CLOSEOUT_AUDIT.md` (not a
  second contract).  **C4 remains FORBIDDEN.**  The next substantive Codex barrier is ONE holistic
  **Implementation Review** after the entire closeout directive is complete (with at most one bounded confirmation).
- **Material defects the closeout must fix** (over the retained-correct C3 architecture): (1) the production
  elaborator still traverses each file twice — `elaborate_indexed` uses `prog_package_refs idx` (which recomputes
  `prog_visit p`) instead of the RETAINED `visit`; (2) the fresh-build runner is fail-OPEN (find|while pipelines +
  suppressed find errors → can omit source files and return success) — replace with a checked manifest flow;
  (3) the advertised public `Fido Emit` still sinks before fresh-build validation — make one honest public
  workflow validate-before-publish; (4) old `AllPackagesOneMain`/`ProgValid`/`prog_ok` remain live public
  source-validity authorities — `SourceProgramValid` must be the ONLY live root, old rule a proved consequence,
  dead helpers (`elaborate_valid_of_no_diags`/`result`/`bool_sumbool`) deleted; (5) the 571-line character-level
  executable-name string-proof is OVERARCHITECTURE — replace with ONE component-level root over ModulePath/
  FilePath components, DELETE the `str_starts_slash`/`str_ends_slash`/`str_no_double_slash` ecosystem (delete >
  add); (6) the 578-entry readable gate must shrink to load-bearing public claims (whole-theory audit unchanged);
  (7) share canonical/retained builders over explicit inputs; (8) reconcile stale permanent docs/headers/status
  (GoIndex "C2 in progress", dune, GoCompile header, gate names, SOURCE_FOREST_STATUS ACTIVE labels).
- **Active work:** make Fido's `GoCompile` judgment accept exactly the programs for which the pinned one-shot
  production `go build ./...` succeeds; materialize the exact `DirectoryImage` into a fresh disposable root and
  build once; publication validates before any sink effect.
- **Baseline SHA:** `fea649389ee52d442373c43ea2bdb3be2eca47db` (`C3 §16 (9th FINAL review): strict canonical
  diagnostic order via unique keys + singleton buckets`).
- **Contract:** `.review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md` (= `.review/NEXT_STEPS.md`, verbatim) is the
  binding completion contract.  All existing C3 implementation is RETAINED unless the contract says otherwise.
- **Open defects the contract closes:**
  - *Package-rule factorization defect:* the accepted C3 rule "every package has exactly one `DMain`" combines
    two independent Go rules — package-block name uniqueness (`PackageDeclsUnique`) and main-package entry
    validity (`MainPackagesHaveEntry`).  Must be split into `PackageRulesValid` / `SourceProgramValid`, with a
    universal `current_package_rules_exactly_one` equivalence + old-rule compatibility; the old combined rule
    must survive only as a proved consequence.
  - *Analysis/elaboration vocabulary defect:* `analyze`/`analyze_indexed`/`AnalysisResult`/`ProgramAnalysis`/
    `AnalysisOK`/`AnalysisFailed`/`CompilationFacts`/… must be renamed to the `elaborate`/`Elaboration*`
    vocabulary; no live compatibility aliases (physical module rename stays C6).
  - *No exact fresh-image cmd/go plan:* there is no model of cmd/go package selection for `./...`, package
    import path, `default_exec_name` + the exact `isVersionElement` (vN) rule, the fresh `RootEntryMap` layout,
    regular-file overwrite vs directory-collision preflight, or command phase order (load → default-output
    stat → compile).  Must add `FreshBuildPlan` + `fresh_build_preflight_ok` and make
    `GoCompile p := fresh_build_preflight_ok (fresh_build_plan p) /\ SourceProgramValid p`, with
    `DRBuildOutputIsDirectory` taking cmd/go precedence over semantic diagnostics for a sole selected package.
- **Fresh build-root invariant (production law 21–28):** every production `go build ./...` runs in a FRESH
  materialization of exactly one `DirectoryImage` (go.mod + rendered `.go` + implied parent dirs, mode 0644/0755,
  no `.fido`/lock/temp/prior-exe/symlink/special/VCS/workspace/nested-module/sink-residue), under a pinned
  environment (`GOWORK=off GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off GOENV=off GOFLAGS= GO111MODULE=on GOOS=linux
  GOARCH=amd64`), invoked ONCE; the disposable build root is never the sink destination and no post-build byte is
  ever published.  Publication sinks the ORIGINAL image only.
- **C4 remains FORBIDDEN.**  This file's completion contract is `.review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md`.
- **Pinned-Go behavioral confirmation (2026-07-19, NO PINNED-GO CONTRACT CONFLICT).** Probed the exact pinned
  image `golang:1.23-alpine@sha256:383395b794dffa5b53012a212365d40c8e37109a626ca30d6151c8348d380b5f`.
  - Toolchain identity (`go env GOVERSION GOOS GOARCH`): **`go1.23.12` / `linux` / `amd64`**.  (The directive's
    "1.23.2" in §31 is illustrative; the pinned image is 1.23.12 — no conflict, behavior is identical to spec.)
  - Authoritative cmd/go source (pinned `GOROOT=/usr/local/go`):
    - `isVersionElement` — `src/cmd/go/internal/load/pkg.go:1288-1298`: `false` if `len(s)<2 || s[0]!='v' ||
      s[1]=='0' || (s[1]=='1' && len(s)==2)`, then every byte `s[1..]` must be a decimal digit.  Byte-for-byte
      the directive §4.4 rule.
    - `exeFromImportPath` — `pkg.go:1675-1685`: `elem` = last import-path component; if `ModulesEnabled &&
      elem != importPath && isVersionElement(elem)` then `elem` = last component of `Dir(importPath)` (the
      second-to-last); return `elem`.  `DefaultExecName` (`pkg.go:1705-1710`) delegates here for `./...`
      (non-CmdlineFiles) builds.
    - Output preflight — `src/cmd/go/internal/work/build.go:473-545`: `explicitO=false` for `go build ./...`;
      `if len(pkgs)==1 && pkgs[0].Name=="main" && BuildO==""` then `BuildO = DefaultExecName()+ExeSuffix`
      (ExeSuffix="" on linux/amd64); `if BuildO!=""` then `os.Stat(BuildO)`: an existing **directory** (and
      `!explicitO`) → `base.Fatalf("go: build output %q already exists and is a directory", BuildO)` BEFORE any
      compile; otherwise `p.Target = BuildO` (create/overwrite).  For 0 or ≥2 packages `BuildO` stays `""` → no
      output preflight and no default output written.
  - Empirical `go build ./...` under the pinned env (`GOWORK=off GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off
    GOENV=off GOFLAGS= GO111MODULE=on GOOS=linux GOARCH=amd64`), every case matching the directive:
    root `main.go` (mod `example.com/m`) → exit 0, creates `m`; sole `sub/main.go` → exit 1 `build output "sub"
    already exists and is a directory`; sole `sub/main.go` + undefined symbol → exit 1 **same collision message**
    (preflight PRECEDES the compile error); `a/b/main.go` → exit 0, creates `b`; `a/v2/main.go` → exit 1
    collision on `a`; `v2/main.go` → exit 0, creates `m`; `a/main.go`+`b/main.go` → exit 0, no default output;
    module basename `go.mod` → exit 0, **overwrites go.mod** with a 1.5 MB ELF exe (magic `7f454c46`); module
    basename `main.go` (root `main.go`) → exit 0, **overwrites main.go** with an ELF exe; empty module → exit 0
    `warning: "./..." matched no packages`; root `package main` no `func main` → exit 1 link error (target `m`
    absent → preflight passes → link fails); duplicate `func main` → exit 1 compile error.  vN via
    `DefaultExecName`: `v0 v00 v01 v05 v1 v1x v2x V2 v` KEPT, `v2 v3 v10 v100` dropped — exact `isVersionElement`.
  - Probe scripts retained in the session scratchpad (`gobehav.sh`, `overwrite.sh`); this is a one-shot
    investigation, not a repo artifact.
- **ARCHITECTURAL DECISION — platform limits are OUT of scope (Rob, verbal, 2026-07-19).** During §7 I flagged
  a conflict: paths are now UNLIMITED length (Rob's earlier directive removed the 200-byte cap @`fe36e51`), so
  a module basename ≥256 yields a default exec name > the pinned fs `NAME_MAX` (255), and empirically
  `go build ./...` then fails "file name too long" (exit 0 at ≤255, exit 1 at ≥256; `getconf NAME_MAX /tmp` =
  255, `PATH_MAX` = 4096 in the pinned image).  This appeared to conflict with the contract's "GoCompile ==
  build" + "directory-collision is the ONLY command-level failure".  **Rob resolved it: DO NOT model platform
  limits (NAME_MAX/PATH_MAX/disk/memory) — they are platform-specific and not Fido's domain; for modeling a
  path is unlimited length; over-long paths fail-LOUD at printing/materialization (the OS surfaces
  ENAMETOOLONG), like disk/memory limits.**  The "GoCompile == build" invariant is therefore scoped to the
  SEMANTIC + cmd/go PACKAGE/OUTPUT LOGIC (types, one-main, the directory-collision — deterministic from the
  image, platform-independent) and EXCLUDES platform fs limits.  The path-cap removal STANDS; NO NAME_MAX /
  PATH_MAX / length check is added to the grammar, GoCompile, or the sink.  Recorded as a top AMENDMENT banner
  on the contract (`.review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md` = NEXT_STEPS) and in [[no-magic-numeric-caps]].
- **Status:** contract installed verbatim (+ platform-limits amendment banner); prior plan bannered SUPERSEDED;
  pinned-Go behavior empirically confirmed.  Additive Rocq layers landed green + byte-identical: §12
  default_exec_name/is_version_element (`19af953`), §11 import path (`84e12ce`), §10 selection (`46b1ddb`), §7
  layout foundation + FULL pairwise-disjointness audit (`01056e0`/`19c01c6`/`27c43e8`).  Next: §7 RootEntryMap
  construction + exactness → §13 plan/preflight → §9 package-rule split → §15 diagnostics → §16 elaborate rename
  → §17 integration (flips acceptance) → §18/§19 theorems → §8 bridge → §20 fixtures → runner/differential/Docker
  → docs → pre-Codex audit → one exhaustive Codex discovery review.

## C3 — One Retained Indexed Analysis, Occurrence-Keyed Facts, and Structured Diagnostics (COMPLETE — structural C3, Codex-GREEN; superseded by the C3 MANUAL CLOSEOUT above)
- **C2 human disposition: APPROVED by Rob** (2026-07-18, via the C3 activation directive: "Rob has now reviewed
  and APPROVED C2 by issuing this C3 activation directive.  C2 is accepted.  C3 is authorized.").
- Active checkpoint: **C3**.  Baseline SHA: `a812812d0ae311471c672bde0bbbcea057135ca6`
  (`review(final): C2 — record FINAL Codex GREEN disposition (awaiting Rob's approval)`).
- C3's binding OUTCOME: one retained `IndexedProgram p` per analysis (a `Snap.SyntaxIndex p` wrapper built
  exactly once); ONE production analysis execution root `analyze` (with internal `analyze_indexed`);
  occurrence-keyed successful facts (`ExprFactTable` over a standard `FMapAVL NodeKey`, `PackageMap PackageFact`);
  structured diagnostics anchored in the EXACT rejected snapshot (`DiagnosticReason p` / `DiagnosticAnchor p`
  over NodeRef/FileRef/PackageRef/program, four current codes: invalid conversion / default-not-representable /
  duplicate main / missing main); and `go_compile` as a PROJECTION of analysis (never an independent validity
  computation).  C2's `indexed_program_typedb` is subsumed into the analysis root and deleted/confined.
  Generated bytes remain identical; no new Go feature.
- Review cadence: **TWO intentional Codex barriers — ROOT then FINAL** (no human stop between ROOT-GREEN and
  FINAL).  ROOT = retained indexed-analysis root + fact tables + diagnostic core + exactness theorems; FINAL =
  deterministic reporting + downstream integration + residue removal + e2e + docs + byte identity.  ROOT commit
  `milestone(root): C3 —`, repairs `review(root): C3 —`; FINAL commit `milestone(final): C3 —`, repairs
  `review(final): C3 —`.
- ⛔ **C4 and every later Source Forest checkpoint remain FORBIDDEN until C3 is Codex-green, pushed, and
  explicitly approved by Rob.**
- Contract activation SHA: (this commit) `milestone(contract): C3 — activate retained indexed analysis and
  structured diagnostics`.  This directive (`.review/C3_INDEXED_ANALYSIS_DIAGNOSTICS_PLAN.md` =
  `.review/NEXT_STEPS.md`, installed verbatim) is the binding C3 completion contract.
- ROOT commit SHA: `3efd340` (`milestone(root): C3 — one retained indexed analysis root with anchored facts
  and diagnostics`).  Delivered at ROOT: §6 shared `const_info_step`; §14 single bottom-up `const_info_step`
  pass (`occ_statuses`/`file_statuses` proved = the per-node `const_info` spec) feeding an occurrence-keyed
  `prog_status_map` (`prog_status_map_find` / `prog_status_map_find_operand`, the operand at the canonical
  child id `Pos.succ me` via `occs_file_operand`); the fact map AND the diagnostics both READ that map O(1)
  (NO per-occurrence recursive `const_info` rescan; `prog_expr_facts_eq_spec` / `expr_diags_eq_spec` tie the
  single pass to the specifications); §11 per-file → whole-program main-ref buckets (`file_main_refs_length`,
  `package_main_refs_present`/`_bucket_len`, `package_main_at` singleton-on-success, `DRDuplicateMain` /
  `DRMissingMain` anchored); §12/§16 `CompilationFacts` (ExprFactTable + package buckets + exactness) retained
  in `CompilableProgram` (program + SAME index + facts; `cp_ok` projects validity); §18 `go_compile` projects
  `pa_result (analyze p)`.  Gate 486/486 axiom-free; whole-theory audit + self-tests A-E green; generated bytes
  byte-identical.  Removed the now-unused per-file `file_expr_facts`.
- ROOT Codex barrier: **BLOCK** (task-mrqxwoog, non-stale, 5 findings) — C3 ROOT violated the
  one-index/one-analysis contract and exposed incomplete fact/compilation boundaries.  Repaired across
  `4031c30`/`a382fbf` (F1 double-eval → let-bind ip; F2 decision = the diagnostic pass, not a peer
  expr_all_ok/pkg_all_ok, use-resolution reads the status map; F3 go_compile carries the exact diagnostics
  [CompileFailure/CompileOutcome], legacy class a projection of the diagnostics), `b65eac0` (F4 sealed
  [ExprFactTable] with no-foreign-key domain proof + [cf_package_belongs] no-swap + [expr_fact_at] /
  [package_main_at] as facts projections), `7079b96` (F5 one shared [analysis_facts] builder for both
  [analyze]'s AnalysisOK and the witness path; each witness attests [go_compile] succeeds via AnalysisOK).
  Gate 490/490 axiom-free; bytes byte-identical throughout.
- ⚠ ROOT-repair CONSTRAINT (F5, responsibility boundary): the emit reduces [cp_program] to bytes, and
  reducing [go_compile]/[analyze] forces the opaque C2 sealed index (vm-compute RESOURCE-EXHAUSTS), so the
  witness's RENDERED CompilableProgram is built by the shared cheap builder rather than extracted from
  [go_compile]'s reduction; [go_compile] success is attested by proof instead.  Directive §19 keeps
  SafeProgram over a CompilableProgram; the two constructions are observationally identical (differ only in
  the erased validity proof).  A literal "extract the rendered program from go_compile's reduction" would
  require making the C2 sealed index vm-compute-reducible (a C2-layer change) or decoupling GoSafe/GoEmit
  from CompilableProgram (against §19) — flagged for the ROOT re-review / Rob.
- ROOT Codex RE-review #1 of `14749f0`: **BLOCK** (task-mrr0l4ph, non-stale, 3 binding implementation
  defects) — (1) a PARALLEL compilation-capability path (`compilable_of_valid` mints `mkCompilable` outside an
  `AnalysisOK` result — observational equivalence, not provenance); (2) `analyze_indexed` still performs
  MULTIPLE traversal executions (`collect_diagnostics` + `analysis_facts` recompute status/visit/fact/package;
  `file_statuses` traverses source separately from `visit_file`); (3) the required `expr_fact_at` query is
  PARTIAL (returns `option ExprFact`, completeness only conditional on `prog_visit` membership).
- ROOT-repair round #2 (this round) — all three defects closed, gate 491/491 axiom-free, whole-theory audit +
  self-tests A-E green, generated bytes byte-identical:
  - **Defect 1** (`95e57e1`): `CompilableProgram` carries a MANDATORY exact-`AnalysisOK`-provenance field
    `cp_prov : pa_result (analyze cp_program) = AnalysisOK cp_facts` — the stored facts ARE `analyze`'s output,
    there is no way to construct the artifact for a program `analyze` rejects, and no parallel path (`go_compile`
    and the witnesses build it the ONE way, via `compile_outcome_of` / `analyze_ok_sig`; all reasoning routes
    through `analyze_result_cases`, never a dependent-convoy fight).  `cp_program` stays a cheap first-field
    projection so the F5 emit-reduction constraint is preserved.  New gate surface `compilable_prov`.
  - **Defect 3** (`c33fb86`): `expr_fact_at : CompilationFacts p ip -> ExprRef p -> ExprFact` is now TOTAL.
    Crux `prog_visit_const_info_some`: on `ProgramTyped` every VISITED expression occurrence's `const_info`
    succeeds (typed-arg root + downward closure through the occurrence enumeration + `noderef_in_prog_visit`);
    `expr_ref_fact_some` proves the sealed lookup is never `None`, and `fact_of_find` discharges the impossible
    `None`.  New gate surfaces `expr_ref_fact_some` / `expr_fact_at_find` (query PROJECTS the sealed table).
  - **Defect 2** (`47b54e8` part 1 + this commit part 2): `analyze_indexed` let-binds ONE internal pass product
    (index, visit stream, status map, package buckets) and derives BOTH the decision and the successful
    `CompilationFacts` from it — no separate `analysis_facts` (DELETED); the expression facts and diagnostics
    are two linear passes over the SAME `visit`/`status`; `pkg_diag_of_from` threads the retained buckets.  AND
    the status map is now ONE fold over the DELIVERED visit stream (`prog_status_map = fold_right psm_step` over
    `prog_visit`, each conversion reading its operand at `operand_key` from the already-folded tail —
    `psm_fold_find` + `prog_visit_operand_closed` via `visit_file` ordering), REPLACING the `file_statuses`
    source recursion (`occ_statuses`/`file_statuses`/`status_kvs` machinery DELETED; gate 493→491).  `file_statuses`
    no longer traverses source separately from `visit_file`.
- ROOT Codex RE-review #2 of round #2 (`56d82d1`): **BLOCK** (task-mrr5yk8k, non-stale 2026-07-19, 2 binding
  implementation defects) — (A) package collection STILL performs a second traversal: `analyze_indexed` retains
  `visit := prog_visit p` but separately computes `package_main_refs idx`, which folds file bindings and calls
  `file_main_refs` → `Snap.visit_file` AGAIN, so every nonempty program runs >=2 per-file traversals; (B)
  `CompilableProgram` does not RETAIN its index — `cp_index` recomputed `pa_indexed (analyze cp_program)` anew
  rather than projecting a stored value.
- ROOT-repair round #3 (this round) — both defects closed, gate 491/491 axiom-free, whole-theory audit +
  self-tests A-E green, generated bytes byte-identical:
  - **Defect B** (`caa8d24`): `CompilableProgram` now STORES the exact analyzed index in a new field
    `cp_index : GoIndex.IndexedProgram cp_program` pinned by `cp_index_ok : cp_index = pa_indexed (analyze
    cp_program)`; the public index projection returns the RETAINED value (no `index_program` reconstruction),
    while `cp_prov` and the cheap first-field `cp_program` projection (the F5 emit-reduction constraint) are
    preserved.  New gate surface `compilable_index_retained`.
  - **Defect A** (this commit): the package buckets are built as ONE `fold_right ppkg_step` over the RETAINED
    `visit` stream (`prog_package_refs`), never a second `Snap.visit_file`.  Each occurrence contributes to its
    file's package (`occ_pkg` = the file's parent dir): a `DMain` prepends its `DeclRef`; a FILE ROOT (`KFile`)
    INITIALIZES the package entry (so a zero-main package is still represented) without disturbing existing
    mains.  Exactness re-proved over the fold: `prog_package_refs_bucket_len` (bucket length = `pkg_main_count`,
    via the `pkg_declcount` occurrence-count characterization), `_present` (domain = represented packages),
    `_belongs` (no cross-package swap), `_singleton_on_success`.  `pkg_diags` reads the SAME retained buckets
    through `pkg_diag_of_from (prog_package_refs idx)` (defeq to `analyze`'s `pkg_diag_of_from buckets`).
    DELETED the entire second-traversal machinery (`package_main_refs`/`_rev`, `file_main_refs`,
    `binding_main_refs`, `mref_step`/`mref_foldl_*`, `list_dir_reflen*`, `decl_collect_*`).  Gate surfaces
    swapped `package_main_refs_*`/`file_main_refs_length` -> `prog_package_refs_*`.
- ROOT Codex RE-review #3 of round #3 (`d2771aa`): **BLOCK** (task-mrr7wpgk, non-stale 2026-07-19, 2 binding
  implementation defects) — (1) compiled artifacts REBUILD the index: `go_compile`/`compilable_of_valid`
  populated `cp_index` by separately evaluating `pa_indexed (analyze p)` (a re-projection reconstructing
  `index_program p`), rather than binding ONE evaluated analysis; (2) package acceptance still runs a PEER
  legacy counter: `analyze_indexed` classified via `package_summaries`' `ps_main_count` (the FM.fold /
  `file_main_count` computation) using the retained bucket only for anchors, and missing-main anchors rescanned
  file bindings through `package_present_b`.
- ROOT-repair round #4 (this round) — both defects closed, gate 491/491 axiom-free, whole-theory audit +
  self-tests A-E green, generated bytes byte-identical:
  - **Defect 1** (`46abb8d`): the `CompilableProgram` record now indexes its facts BY the retained index
    (`cp_facts : CompilationFacts cp_program cp_index`) and carries a HOMOGENEOUS whole-analysis provenance
    `cp_prov : analyze cp_program = mkProgramAnalysis cp_index (AnalysisOK cp_facts)` (no index transport; the
    separate `cp_index_ok` is dropped, derivable).  Both builders DESTRUCTURE `analyze p` exactly once:
    `outcome_of_analysis` (for `go_compile`) matches the whole `ProgramAnalysis`, binding its retained `ip` and
    result, so `cp_index` IS that bound `ip`; `analyze_ok_full` (for `compilable_of_valid`) matches once and
    rules the Failed branch impossible via a NON-dependent `analysis_ok_flag`.  `cp_program` stays the direct
    first-field projection (F5 preserved).  `compilable_prov` restated as the whole-analysis equation;
    `compilable_index_retained` derived from it.
  - **Defect 2** (this commit): the package DECISION now reads ONLY the retained buckets.  `pkg_diags`
    enumerates `PM.elements (prog_package_refs idx)` and classifies each bucket by LENGTH
    (`bucket_diags_elems` / `pkg_diag_of_bucket`: >=2 -> `DRDuplicateMain`, 0 -> `DRMissingMain`, 1 -> ok); the
    missing-main `PackageRef` is built from the bucket's OWN domain membership (`bucket_key_present`, via
    `prog_package_refs_present`) — NO `package_present_b` / `package_summaries` rescan in the computation.
    `analyze_indexed` folds the SAME retained `buckets` into the diagnostics (defeq to `collect_diagnostics`).
    `package_summaries` (and `pkg_all_ok`/`AllPackagesOneMain`) survive ONLY in the erased equivalence proof
    `pkg_diags_empty_iff` (bucket length = `pkg_main_count` = `ps_main_count`).  Deleted the now-dead
    `pkg_diag_of_from` / `bool_sb` / `summary_elem_present`.
- ROOT Codex RE-review #4 of round #4 (`e4eb9e1`): **BLOCK** (task-mrr9d6sp, non-stale 2026-07-19, 1 binding
  implementation defect) — `compilable_of_valid` had THREE independent occurrences of `analyze_ok_full p H`
  (one per `mkCompilable` argument), so `cp_index`, `cp_facts`, and `cp_prov` came from three reruns of
  `analyze p` rather than one retained execution (C3 §§1/13/18/28).
- ROOT-repair round #5 (this round) — defect closed, gate 491/491 axiom-free, whole-theory audit + self-tests
  A-E green, generated bytes byte-identical:
  - **Defect** (this commit): `compilable_of_valid` now `let`-binds the ONE `analyze_ok_full p H` execution
    (and its `projT2`) and projects all three `mkCompilable` arguments from that single binding.  `cp_program`
    stays the direct first-field projection (F5); the architecture is unchanged.
- ROOT Codex RE-review #5 of round #5 (`5d9bd5b`): **ALLOW / GREEN** (task-mrr9nut0, non-stale 2026-07-19
  T03:59:09Z > HEAD `5d9bd5b` T03:58:30Z) — "no blocking implementation defects or architectural conflicts
  within the C3 ROOT scope and declared threat model."  **The C3 ROOT barrier is Codex-GREEN.**
- FINAL barrier ACTIVE (ROOT-GREEN @`5d9bd5b`; no human stop between ROOT-GREEN and FINAL).  Progress:
  - **FINAL 1** (`b299263`): §17 erased-diagnostic reports FOUNDATION — snapshot-independent `ErasedAnchor` /
    `ErasedDiagnostic` + `erase_diagnostic` (code + key-only anchors + stable target-type payload, no source
    syntax) + `erased_report` (empty iff analysis accepts) + intra-snapshot preservation lemmas.
  - **FINAL 2** (`70c783c`): §19/§26 removed the C2 `indexed_program_typedb` PEER whole-program executable
    from GoTypes (kept the shared leaf `occ_arg_typedb` + `occs_file_typedb_eq`); GoCompile's `analyze` is the
    ONE indexed whole-program traversal; `prog_ok`/`program_typedb` are spec/proof-only.  Gate 491->489.  Docs
    reconciled (CLAUDE/ARCHITECTURE/PROGRESS/COLLECTION_AUDIT).
  - REMAINING: §17 cross-snapshot FilesEqual/permutation erased-equality theorems (feasible via `visit_file_snd`
    + the source-occurrence/local-id correspondence; a substantial pipeline-wide proof); §16 canonical order
    theorem; §22/§23 diagnostic + fact-query e2e fixtures; §24 report formatting; §27 gate surfaces for the
    erasure; §20 exactness-surface gate audit; §29 remaining docs + collection audit; then the FINAL Codex
    barrier.
- FINAL Codex barrier RE-review #1 of `d6f8e22`: **BLOCK** (task-mrrathsz, non-stale 2026-07-19, 4 blocking
  defects — a concrete FINAL work list):
  1. **nested diagnostic context discarded** (§8/§15/§22.8): `float64(int8(128))` must report the inner `int8`
     conversion as primary and the outer conversion as related; both diagnostic paths built
     `DRInvalidConversion er [] ...` (empty `outer_context`).  Thread enclosing conversion refs + add the nested
     scar theorem.
  2. **three mains -> too few diagnostics** (§8): n mains require n-1 `DRDuplicateMain`, each later main related
     to the first; `pkg_diag_of_bucket` emitted only one (`d1 :: d2 :: _ => [DRDuplicateMain d2 d1]`).
  3. **required diagnostic/determinism proof boundary absent** (§9/§17/§20/§27): need code-specific soundness,
     nested/duplicate/missing-main exactness, canonical ordering, `FilesEqual`/permutation erased-report
     equality, and fact-enumeration determinism — PROVED and GATED.
  4. **stale permanent docs + collection audit** (§29): ARCHITECTURE/CLAUDE/PROGRESS still claim coarse
     `CompileError`/`ErrTyping` + "no CompilationFacts"; the collection audit omits the C3 NodeKey fact maps /
     diagnostic + package buckets / report enumeration.
- FIRST FINAL review (`task-mrrathsz`) — defects 1, 2, 4 + defect-3 part 1 CLOSED: n-1 `DRDuplicateMain`
  (`2164d51`); coarse-error prose reconciled + `COLLECTION_AUDIT.md` rows (`867a1d2`); nested `outer_context`
  (`183b560`); §9 code-specific soundness (`355c79a`).
- SECOND FINAL review (`task-mrrevblb`) found THREE deeper blocking defects — ALL now CLOSED:
  - **Defect 1 (one-pass) DONE** (`6bffa5c`, `b3a0aa6`): the FIRST fix's `enclosing_conv_refs` re-ran
    `visit_file` + `node_at` PER diagnostic (§14/§28 violation, quadratic).  Replaced by the ONE-PASS
    `annotate_encl`: a single forward pass carries the open-conversion stack (nearest-first) over the RETAINED
    file stream; `occ_expr_diags`/`_sm` take the delivered `outer` context as a parameter; `analyze_indexed`'s
    diag fold consumes `annotate_program`.  No per-diagnostic `visit_file`/`node_at`.  All dead
    `enclosing_conv_refs`/`is_conversion_node`/`is_ancestor_of` machinery DELETED.
  - **Defect 3 (soundness) DONE** (`c83e732`, `b3a0aa6`): the soundness surfaces now DENOTE their code
    end-to-end — `occ_expr_diags_conv_sound` (primary is the occurrence's own ExprRef; syntax IS the explicit
    conversion to the reported target of operand x via `conv_targets`; operand status is x's exact ConstInfo;
    `convert_const` genuinely rejects), `occ_expr_diags_default_sound` (genuine println arg; exact `CIUntyped
    c`; Go default), `pkg_diags_dup_sound` (same package + genuine top-level func main via `noderefof_kind`).
  - **Defect 2 (determinism) DONE** (`2ebee01`..`8c61216`): the §17 cross-snapshot theorems, all gated —
    `erased_report_FilesEqual` (FilesEqual programs, whose diagnostics live in DIFFERENT dependent snapshot
    types, produce the IDENTICAL erased report; expr half factors through `annotate_source` + the pkg half
    through the keyed source buckets via `ppkg_erased_find` + PackageMap `elements_Equal`/`map_elements`),
    `erased_report_build_permutation` (construction-list permutation -> same report), and
    `prog_expr_facts_enum_FilesEqual` (successful-fact enumeration determinism, a fold-map fusion over the
    keyed stream).  Gate 494 -> **502/502**.
- THIRD FINAL review (`task-mrrl5jtg`, non-stale 2026-07-19) found THREE deeper blocking defects — ALL now CLOSED:
  - **Defect 1 (nested-scar WF strengthened) DONE**: the §9 nested scar now proves — beyond conversion syntax +
    local interval containment — that every `outer_context` ref is SAME-FILE, NEAREST-FIRST (strictly descending
    local id), and DUPLICATE-FREE (`NoDup`).  `annotate_encl_ctx_wf`/`annotate_program_ctx_wf` +
    `expr_diags_conv_scar_wf`, gated; the annotation stack already satisfied them (`estack_wf` invariant), no
    algorithm change.
  - **Defect 2 (dup precedence + distinctness) DONE** (`7c803a6`, `7804806`): package buckets are the strictly
    NodeKey-ascending subselection of the sorted visit stream — `prog_visit_key_sorted` (whole stream sorted by
    canonical NodeKey) + `ppkg_dir_sorted` (every bucket sorted + each ref a stream occurrence) ->
    `pkg_diags_dup_precedence`: every `DRDuplicateMain later earlier` has `key earlier < key later` AND
    `earlier <> later` (NodeKey strict-order irreflexivity).  So a package's kept main is the UNIQUE
    smallest-key one.  Gated.
  - **Defect 3 (concrete structured fixtures) DONE** (`a78760c`, `719a005`): because the occurrence index is an
    OPAQUE sealed module (`Snap : SNAP_SIG`) the analysis does not reduce, so each fixture pins the REAL index
    and states its claim THROUGH the proven soundness/determinism/emptiness bridges, with NON-VACUITY from the
    computable type checker (`*_empty_iff`).  Gated concrete fixtures: §22.15 reordered-construction determinism
    (report + class + fact enumeration); §22.13 empty program; §22.8 nested `float64(int8(128))` scar +
    non-empty report; §22.9/§22.11 three-mains precedence/distinctness + non-empty report; §22.12 missing-main +
    non-empty report; §23 `fact_query_fixture` (exact `resolved_type_at`/`resolved_constant_at`, no rerounding)
    via the general `expr_fact_at_exact`; §22.16 `println(1,1)` occurrence-keyed (no dedup by syntax value).
- FOURTH FINAL review (`task-mrrnyaen`, non-stale 2026-07-19) found the §22/§23 fixtures materially WEAKER than
  the binding claims — CONDITIONAL on an already-existing diagnostic (`outer=[]` satisfied them vacuously),
  proving neither counts nor exact anchors.  CLOSED (`b27d23f`, `359f2f2`): the erased report AND the fact table
  are PURE SOURCE FUNCTIONS of the file map (`annotate_source` / `keyed_buckets`∘`source_keyed_visit` /
  `keyed_facts`), so although the sealed index does not reduce, the erased report and fact enumeration DO
  `vm_compute`.  New `erased_report_src` + `erased_report_src_eq` (`erased_report p idx = erased_report_src
  (prog_files p)`) turn each fixture into an EXACT computed list (exact COUNT, exact NodeKey/package ANCHORS,
  exact target PAYLOADS, exact fact VALUES).  The full §22.1-22.16 + §23 suite is now EXACT + non-vacuous +
  gated: default int/float/complex overflow; invalid int8/fractional/nonzero-imag/wrong-kind conversion; nested
  `float64(int8(128))` (ONE diagnostic, int8 primary, float64 related, target int8); three mains (EXACTLY TWO
  duplicates, both related to the first); duplicate mains across files (canonical path order); missing main;
  empty program; simultaneous failures (four diagnostics in canonical order); reordered-construction
  determinism; `println(1,1)` (two entries, equal values, distinct keys); and the exact per-occurrence facts of
  `float64(int(5))`.
- FIFTH FINAL review (`task-mrrp0wev`, non-stale 2026-07-19) found two blocking defects — BOTH CLOSED (`bced8c0`):
  - **Defect 1 (dependency ownership)**: GoTypes still imported GoIndex and retained the C2 aggregate helper
    surface (`occ_arg_typedb` + the `occs_*_typedb_eq` chain).  MOVED the whole occurrence/traversal bridge to
    GoCompile (the SOLE GoIndex+GoTypes meeting point); GoTypes now imports NO GoIndex and owns the
    type/constant relation only (keeping just index-free `forallb_ext_in`/`forallb_map_snd`).  Gate surface
    `GoTypes.occs_file_typedb_eq` -> `GoCompile.occs_file_typedb_eq`.
  - **Defect 2 (weak §23 outer fixture)**: `fact_program_outer_arg` proved only the resolved type + that some
    resolution exists (any float64 satisfied it).  Strengthened to pin the EXACT value (resolved GoConst
    `CFloat` 5/1, `CITyped (TFloat F64)`) + a new `fact_program_outer_fact` asserting the COMPLETE exact
    `ExprFact` (full proof-carrying float64 TypedConst + exact resolved constant).  Both gated.
- SIXTH FINAL review (`task-mrrppjse`, non-stale 2026-07-19) — two permanent-doc rows contradicted the C3
  state; CLOSED (`8a7f1cf`): the ARCHITECTURE.md GoCompile row (retained `CompilationFacts`) + the
  COLLECTION_AUDIT.md analysis-fold row (`GoCompile.occ_arg_typedb`).
- SEVENTH FINAL review (`task-mrrpyt2j`, non-stale 2026-07-19) found a §16 CANONICAL-ORDER defect — CLOSED
  (`29c32c5`): `collect_diagnostics = expr_diags ++ pkg_diags` put a duplicate-main (node-primary) AFTER an
  invalid-conversion whose NodeKey sorts later.  Node-primary diagnostics (invalid-conversion, defaulting,
  duplicate-main) now accumulate into a standard `NodeKeyMapBase.t (list DiagnosticReason)` (code-ordered bucket)
  and flatten in canonical NodeKey order, THEN the package-primary (missing-main) list.  `analyze_indexed`'s
  one-pass `diags` applies the SAME transform (defeq `collect_diagnostics`).  Proved: generic `bucket_flatten`
  + empty-iff; the value-map COMMUTE (so the erased report stays a source function — determinism + vm-computable
  fixtures preserved); MEMBERSHIP (`collect_diagnostics_In` — a reordering, exactly the diagnostics of
  `expr_diags ++ pkg_diags`, preserving the legacy-class projection); the §16 `mixed_order_erased` fixture
  (duplicate-main `a/q.go:3` precedes invalid-conversion `z/main.go:5`); + the nonblocking GoCompile comment.
- EIGHTH FINAL review (`task-mrrrlyma`, non-stale 2026-07-19) found the §16 bucketing used a forbidden
  project-authored sorter (`sorted_insert`) and lacked a UNIVERSAL canonical-order proof — CLOSED (`2a417de`):
  removed `sorted_insert` (a node-primary diagnostic is PREPENDED to its bucket; the stdlib `Mergesort` functor
  can't instantiate for the parametric `DiagnosticReason p`, and the contract requires a sort ONLY for a
  non-singleton bucket — each occurrence emits at most one node diagnostic, so buckets are singletons); new
  gated UNIVERSAL theorem `collect_diagnostics_node_canonical` — the report's node-primary diagnostics are
  `StronglySorted` by non-decreasing NodeKey via the standard NodeKeyMap's key-sorted `elements`
  (`bucket_value_key` + `flat_map_snd_bucket_sorted` + `node_keyed_self`).
- NINTH FINAL review (`task-mrrsmyxn`, non-stale 2026-07-19) found the §16 canonical-order theorem TOO WEAK
  (the `≤` `nk_le_opt` order permits arbitrary reordering among equal-key diagnostics) and the claimed
  singleton-bucket theorem missing — CLOSED: proved the actual node-keyed INPUT has UNIQUE keys
  (`collect_node_input_nodup` — the expr keys are NoDup, the pkg keys are NoDup, and the two sets are DISJOINT
  because an occurrence is an expression XOR a decl, via `node_ref_key_inj` + the kind refinement), hence every
  bucket is a SINGLETON (`collect_node_buckets_singleton`), hence the flattening is STRICTLY ascending with no
  ties — new gated theorem `collect_diagnostics_node_strict` (`StronglySorted` by `nk_lt_opt`, replacing the
  `≤` `collect_diagnostics_node_canonical`, now deleted along with its `nk_le_opt`/`flat_map_snd_bucket_sorted`/
  `bucket_flatten_key_sorted`/`StronglySorted_all` chain).  Also deleted the unused `diagnostic_code_index` +
  `diagnostic_code_eq_dec` (no within-bucket code sort exists — buckets are singletons).
- Status: **C3 FINAL barrier — all defects from ALL NINE FINAL reviews CLOSED; one-pass hot path +
  end-to-end diagnostic soundness + cross-snapshot determinism + the COMPLETE EXACT §22.1-22.16/§23 fixture
  suite + §16 STRICT NodeKeyMap-canonical diagnostic order (unique keys → singleton buckets → strict order,
  no project-authored sort) + clean GoIndex/GoTypes/GoCompile dependency ownership all proved + gated
  (535/535); `make check` green on the working tree; generated bytes byte-identical throughout.  Awaiting the
  FINAL Codex re-review.**

## C1B — Collection Policy Enforcement and Source Forest Plan Reconciliation (COMPLETE)
- Baseline SHA: `79e80fdb4e63d00d4e97d8638f94a05408b51ea8` (`review(final): C1A — record both-barrier Codex GREEN
  disposition; C1A complete`).
- C1A's standard-collection IMPLEMENTATION direction is RETAINED (mature pinned-stdlib `FMapAVL`/`FMapPositive`
  maps + OCaml `Map`/`Set` + `GlobRef.Set`, not project-authored storage).  C1B is a policy/plan/prose
  reconciliation, not a re-implementation.
- Human holistic review found, on top of the accepted C1A code: stale binding architecture in the master plan
  (live `GoFileSet = list + NoDup`, hidden slots, file-list scans, slot-keyed outer indexes, root-local-ID-zero
  language); one FAIL-SOFT occurrence constructor (`OccurrenceSpike.forest_of_ok` → empty on `None`); one
  FAIL-SOFT e2e program constructor (`WitnessMulti.multi_program` → `empty_program` on `None`); one
  membership-only list in the sink test (`e2e/sink_test.ml` faults `List.mem`); omitted scale/computation
  probes; overstated `FMapAVL` proof/balance/complexity claims; and stale high-authority prose
  (GoAST/GoCompile/GoEmit headers, PAINFUL_LESSONS lessons 2 and 14, package-clause responsibility text).
- Scope (this directive, binding): install the permanent standard-collection LAW (no roll-your-own when a
  mature standard collection exists; thin domain wrappers allowed, storage/generic-algorithms forbidden;
  escalate if none fits); a repository-wide `.review/COLLECTION_AUDIT.md`; rewrite the binding master plan to
  the CURRENT map architecture (delete superseded `GoFileSet`/slot/scan/root-0 pseudo-code, no "history"
  banners); delete the fail-soft constructors (proof-backed total extraction instead); fix the sink-test
  membership list to a standard set; record honest scale probes; correct `FMapAVL`/`FMapFullAVL` wording; add
  a Codex collection-review criterion; retain ALL C0/C0A/C0B/C1/C1A theorem surfaces; every generated byte +
  behavior UNCHANGED.  ⛔ C2 is FORBIDDEN until C1B is human-approved.
- Review cadence: ONE exhaustive final Codex barrier (no semantic-root stop unless a real architectural
  conflict is discovered); commit `milestone(final): C1B — enforce standard-collection policy and reconcile
  future plans`; repairs `review(final): C1B —`.  This directive is the binding contract.
- Contract activation SHA: `06a1efa` (`milestone(contract): C1B`).
- Scale / computation probes (§8): TRANSIENT probes were added to the emit stage, RUN in the pinned Buildx
  container (`ocaml/opam:debian-12-ocaml-5.3`; `rocq-core 9.2.0` / `rocq-stdlib 9.1.0`) via `make emit`, and
  then REVERTED (no permanent fixture).  Method: for N ∈ {1, 10, 100, 1000} a generator emits N distinct
  `dNNNN/main.go` file roots; the OCaml probe (`ocamlfind ocamlopt probe.ml`) builds `Map.Make(String)` +
  `Set.Make(String)` and queries every key (`Sys.time`); the Rocq probe (`rocq c -Q _build/default Fido`)
  `Time`s five `Eval vm_compute in` transactions — `build_program` (FileMap build), `find_file` (FileMap find),
  `package_summaries` (PackageMap aggregation), `file_bindings` (canonical `elements` transport enumeration),
  and `NodeMapBase.find` over an N-entry `PositiveMap`.
  - OCaml Map+Set (machine-native), build / query-all(find+mem):
    n=1 0.000002/0.000001 s · n=10 0.000004/0.000002 s · n=100 0.000017/0.000015 s · n=1000 0.000238/0.000205 s
  - Rocq under `vm_compute` (secs), FileMap-build / FileMap-find / PackageMap-agg / elements-enum / PositiveMap-find:
    n=1    0.024 / 0.001 / 0.000 / 0.001 / 0.000
    n=10   0.029 / 0.001 / 0.006 / 0.011 / 0.000
    n=100  0.879 / 0.011 / 0.360 / 0.100 / 0.000
    n=1000 75.24 / 0.136 / 26.556 / 1.075 / 0.018
  Observations (honest): the OCaml standard collections are near-linear and sub-millisecond even at 1000.
  Single Rocq lookups (`find_file`, `PositiveMap.find`) stay fast at every size (≤0.14 s).  The WHOLE-MAP Rocq
  build/aggregation grows SUPERLINEARLY under `vm_compute` (build 0.024→75 s, agg 0→27 s) — this is NOT the
  AVL/positive-map machine cost and NOT an asymptotic theorem: `vm_compute` reduces the map operations
  SYMBOLICALLY over proof-carrying terms (each `FilePath` key carries a `path_ok` proof), so the wall-clock is
  dominated by the reducer building/traversing large syntactic terms, not by O(log n) machine steps (the
  machine-native OCaml numbers show the true shape).  Semantic proofs remain the correctness authority; the
  before/after STRUCTURAL evidence (baseline `75d24b2`): the linear association-list first-match (`FMap`) and
  the nested per-file O(files²) package scan (`main_count_in_dir`) are DELETED and replaced by standard-map
  lookups and a single `FM.fold` package aggregation (`package_summaries`), proved order-independent + exact.
- Final candidate SHA: `cfc7e45` (`milestone(final): C1B`).  Delivered: collection LAW in CLAUDE.md rule 10 +
  ARCHITECTURE.md + Codex review criterion (§1/§10.6/§10.7); `.review/COLLECTION_AUDIT.md` classifying every
  current Rocq/OCaml collection (§4); `SOURCE_FOREST_MASTER_PLAN.md` rewritten to the current map architecture
  (GoFileMap, FileRef by map membership, SyntaxIndex = FileMap(FilePath, FileIndex=PositiveMap), root ID 1, no
  hidden slots / no file-list scan; obsolete GoFileSet/slot pseudo-code removed; collection law for future
  scopes) (§5); the two FAIL-SOFT constructors DELETED — `forest_of_ok` (fixtures now a directly-built standard
  map PROVED = `forest_of`'s `Some` result: `forest_of_single`/`fs_a_built`/`fs_b_built`/`fs_two_built`) and
  `WitnessMulti.multi_program` (proof-backed total extraction: `multi_builds` + `multi_program_built`) (§6);
  `sink_test` fault membership `List.mem` -> the sink's shared `Set.Make(String)` (§7); transient OCaml Map/Set
  scale probe run in the pinned container and reverted, results recorded above (§8); honest FMapAVL/FMapFullAVL
  wording + GoAST/GoCompile/GoEmit headers + PAINFUL_LESSONS 2/14 (§9/§10).  Gate 427 -> **428/428**
  (`forest_of_single`); all C0/C0A/C0B/C1/C1A theorem surfaces retained.
- Final Codex result / repair SHAs: FINAL candidate `cfc7e45` was BLOCKED across FOUR exhaustive review rounds,
  each repaired (all prose/plan/audit/probe, no code-semantics change):
  - `task-mrpjcjmd` (4 findings) → `review(final): C1B` **`4e44ba4`** — stale GoAST header; obsolete master-plan
    `fmap` pseudo-code + trie/array "choose one"; the four required Rocq scale probes actually run; the
    collection audit completed (GoSafe + fido_apply rows).
  - `task-mrpjxsaf` (2 findings) → **`4a574b0`** — residual path-on-`GoFileNode` / "path-keyed set" / "backing
    list" across GoAST + master-plan + PROGRESS; "C2 may swap the physical table" removed (C2 RETAINS the
    selected `FMapPositive`; sealing hides constructors/ops, not the collection choice).
  - `task-...` (1 finding) → **`b0036db`** — master-plan §4.2 conceptual local-ID `0 = file root` → root `1`.
  - `b0036db` reviewed **GREEN** (createdAt 2026-07-17T23:30:44Z — NON-STALE, ~2 min after the `b0036db` commit
    at 23:28:28Z): "ALLOW: C1B is GREEN…".  The disposition was recorded (`9604075`), but a subsequent stop-gate
    re-review of the fuller diff (through the disposition commit) surfaced a FIFTH round:
  - `9604075` **BLOCK** (2 findings) → `review(final): C1B` **`54fc8fb`**: (1) the binding master-plan C2
    activation gate (Part 14) said "after human approval of C1"; C1/C1A complete is NOT sufficient — corrected
    to require Rob's explicit authorization after C1B is accepted.  (2) source/compiler responsibility prose
    still contradicted the implemented source-owned package clause (ARCHITECTURE GoAST row + GoCompile §,
    README raw-file paragraph, CLAUDE FilePath sentence) — reconciled: the package clause (and future import
    declarations) are SOURCE syntax (`source_package`/`source_imports`); package GROUPING, entry status, and
    import RESOLUTION are compilation results.
  - `6b926ac` **BLOCK** (1 finding) → `review(final): C1B` **round-6**: the ARCHITECTURE GoRender responsibility
    row (line 218) still described GoRender as rendering a "derived package clause", contradicting the
    source-owned contract (the prose body at lines 144-145 was already correct).  Reconciled: GoRender renders
    the SOURCE-owned package clause from the file's OWN `source_package` via `render_package_clause`
    (`PkgMain` → `main`), NOT a derived/deduced name.
  - `6737d64` **round-6 repair** — the ARCHITECTURE GoRender responsibility row (line 218) still called it
    "the derived package clause"; reconciled to SOURCE-owned (`render_package_clause`, `PkgMain` → `main`).
    A repo-wide sweep then confirmed no other package-clause / source-vs-compiler contradiction remains.
- Verification result (`make check`): **green on the working tree** at `6737d64` (proof 428/428 + whole-tree
  e2e incl. sink dup/perm + generated byte-compare); the pre-commit hook re-ran the full STAGED verification
  on every commit and passed.  Generated bytes byte-identical across the whole C1B arc.
- Push result: `79e80fd..06a1efa` (contract) + `06a1efa..cfc7e45` (final) + `cfc7e45..b0036db` (three repairs)
  + `b0036db..9604075` (disposition) + `9604075..54fc8fb` (round-5) + `54fc8fb..6737d64` (round-6) — all pushed
  to `main`, fast-forward.
- **C1B COMPLETE and ACCEPTED**: Rob's C2 activation directive (2026-07-18) records the human disposition
  **"C1, C1A, and C1B are accepted"** — C1B is GREEN/ACCEPTED.  The two docs-only tail commits (`54fc8fb`,
  `6737d64`) on top of the accepted baseline `9604075` are consistent C1B prose reconciliations; they change no
  C1B meaning.
- Human disposition: **ACCEPTED by Rob (2026-07-18, C2 activation directive: "C1, C1A, and C1B are accepted").**

## C2 — Production Occurrence Index, Snapshot-Local References, and Indexed Traversal (COMPLETE)
- C1B human disposition: **ACCEPTED / GREEN** (Rob's C2 activation directive, 2026-07-18).
- Active checkpoint: **C2**.  C2 IS NOW AUTHORIZED by Rob.
- Baseline SHA: `9604075843c609f0f2cc616d810ebb62e0b607ec` (`review(final): C1B — record FINAL Codex GREEN
  disposition; C1B complete`).  (Working tip at activation is `6737d64`; the two docs-only C1B tail commits
  on top of the baseline change no C1B meaning.  The Codex FINAL diff for C2 is measured from `9604075`.)
- C2 purpose: **production occurrence identity, efficient navigation, and indexed traversal over the exact
  source snapshot** — one production structural module `GoIndex.v` that derives, from one immutable
  `GoProgram`, a canonical file-local occurrence identity, a certified structural index (outer
  `FMapAVL FilePath FileIndex`, inner `FMapPositive positive NodeMeta`), snapshot-indexed validated
  `FileRef`/`NodeRef` + kind-refined refs, total metadata/kind/role/file/children queries, optional parent only
  for the file root, exact parent/child/ancestry navigation, canonical preorder enumeration, and an indexed
  traversal that supplies the ORIGINAL syntax fragment and its canonical reference together, with a universal
  source/index exactness theorem.  Current Go behavior and every generated byte remain UNCHANGED.
- Two accepted nonblocking C1B review notes folded into the C2 activation commit: (1) `.review/COLLECTION_AUDIT.md`
  is a living current-state inventory — C2 updates it when `OccurrenceSpike.v` is deleted and `GoIndex.v`
  becomes the production authority; (2) the audit's standard-collection prohibition tightened from "generic
  algorithm" to "generic **collection** algorithm" (Fido owns legitimate compiler algorithms; only collection
  machinery is forbidden).
- Review cadence: **ROOT barrier, then FINAL barrier** (no human stop between ROOT-GREEN and FINAL).  ROOT
  commit `milestone(root): C2 —`, repairs `review(root): C2 —`; FINAL commit `milestone(final): C2 —`, repairs
  `review(final): C2 —`.
- `OccurrenceSpike.v` is temporary: deleted from the production theory by FINAL once `GoIndex.v` subsumes all
  accepted C0/C0A/C0B theorem surfaces + fixtures; no parallel spike authority may remain.
- ⛔ **C3 is FORBIDDEN until Rob reviews and explicitly approves C2.**
- Contract activation SHA: `7bcd6fb` (`milestone(contract): C2 — activate production occurrence index and
  indexed traversal`).  This directive (`.review/C2_PRODUCTION_GOINDEX_PLAN.md` = `.review/NEXT_STEPS.md`) is
  the binding C2 completion contract.
- ROOT candidate SHA: `6847cc4` (`milestone(root): C2`).  ROOT repairs: `42650dd` (sealed-reference
  soundness/equality + canonical-ref enumeration + reachability), `ed3a05e` (FileRef source soundness / index
  reuse / enumeration reachability / gating), `326e275` (§3 import boundary + §10 outer-index exactness gated).
- ROOT Codex result: **ALLOW / GREEN** on `326e275` (review 2026-07-18T14:38:12Z — NON-STALE, ~32 s after the
  `326e275` commit at 14:37:40Z): "C2 ROOT is GREEN; no blocking implementation defects or architectural
  conflicts remain within the declared scope and threat model."  → §25 FINAL integration proceeds directly (no
  human stop between ROOT and FINAL).
- FINAL candidate SHA: `29f08d6` (`milestone(final): C2 — integrate snapshot-local NodeRef through the source
  forest`).  FINAL repairs: `021c441` (round 1 — no per-node source recovery), `74a7385` (round 2 — single-pass
  traversal), `54adaaf` (round 3 — consume the snapshot index (role) + delivered syntax).
- FINAL Codex result: **ALLOW / GREEN** on `54adaaf` (review `task-mrqks9jm`, createdAt 2026-07-18T16:22:44Z —
  NON-STALE, ~51 s after the `54adaaf` commit at 16:21:53Z): "C2 FINAL is GREEN; no blocking implementation
  defects or architectural conflicts remain."
- Closing verification on `54adaaf`: `make check` (working tree) GREEN — proof axiom-free with the whole-theory
  audit; readable gate **446/446**; certified-module coverage OK; adversarial self-tests A-E; `Fido Emit` +
  sink + pinned-Go `go build ./...` vs goldens; working-tree generated `go.mod` + recursive `.go` **byte-match**
  the pristine `generated-module` artifact.  Pre-commit staged-tree verification GREEN on every FINAL commit.
  Fast-forward pushed (`74a7385..54adaaf`).
- **C2 DISPOSITION: FINAL Codex GREEN; awaiting Rob's human review and explicit approval.**  ⛔ C3 remains
  FORBIDDEN until Rob reviews and explicitly approves C2.
- Status: **C2 COMPLETE — FINAL Codex-GREEN, awaiting Rob's approval** (ROOT is Codex-GREEN) — `GoIndex.v` was grown bottom-up in fully-proven,
  always-green commits (each kept `make check`/pre-commit GREEN and generated bytes byte-identical).  ROOT
  landed:
  - **Pillar 1** (`88729f3`, `milestone(wip)`): the sealed standard-`FMapPositive` node table, the current
    occurrence universe (SyntaxKind/NodeRole/NodeMeta), the one-pass per-file index builder over the real
    grammar (file root / package clause id 2 / declarations / statements / println arguments / conversion
    operands; `source_imports` structurally consumed; root id 1), the INDEPENDENT table-free source-occurrence
    specification, and the load-bearing UNIVERSAL per-file source/index exactness theorem + its §9 A..H
    consequences.
  - **Pillar 2** (`3c6b888`, `milestone(wip)`): the structural navigation invariants — `build_file_wf`; root
    canonical / no-parent / unique-parent; interval-jump direct children (sound + complete + source-ordered,
    O(#children) no descendant scan); O(1) preorder-interval ancestry (sound + complete); canonical
    enumeration (sound/complete/NoDup); builder branches only on SHAPE (no structural-equality dedup);
    metadata stores no subtree copy.
  - **Pillar 3a** (`29218b6`, `milestone(wip)`): the snapshot-indexed **sealed reference layer over the exact
    `GoProgram`** — decidable `NodeKey` identity; the sealed `Snap` module (raw constructors + outer map
    hidden, `Fail Check` negatives): `SyntaxIndex`/`FileRef`/`NodeRef`, `index_program`, validated minting
    (`file_of_path`/`ref_of_key`), the TOTAL query API, reference/file/key identity, parent-child inverse both
    ways, source-ordered NoDup children, ref-level ancestry (sound+complete), non-circular source-membership
    minting, and the EXACT source-occurrence correspondence lifted through the sealed API.
  - **Pillar 3b** (`6847cc4`, the ROOT commit): §13 typed/kind-refined refs (`NodeRefOf` + `FileNodeRef`/
    `PackageClauseRef`/`DeclRef`/`StmtRef`/`ExprRef` + validated refiners; sound/complete/mismatch; kind tied
    to the exact source occurrence; erased-key identity) and the §21/§22 regressions over the real grammar
    (`println(1,1)` two-equal-args distinct-ref; same-shape/different-payload per-snapshot recovery + equal
    erased index data + non-interchangeable ref types; same-file/different-`ModuleSpec` identical index data +
    non-interchangeable types; the mutation-sensitive fixture pinning exact per-occurrence metadata + source
    views through the universal theorem).
  - ROOT gate 534/534 axiom-free; whole-theory audit covers GoIndex; generated bytes byte-identical throughout.
  - **§25 FINAL** (after ROOT-GREEN, no human stop) — COMPLETE:
    - **`OccurrenceSpike.v` DELETED** — removed from `dune`, the gate, and the repo; `GoIndex` subsumes all its
      accepted C0/C0A/C0B surfaces over the real grammar (no parallel spike authority remains); docs reconciled
      (CLAUDE / PROGRESS / COLLECTION_AUDIT).
    - **§19 indexed traversal** (`milestone(wip)` `d53ad70`, single-pass in round 2): the `occs_file` occurrence
      stream + interval bounds + `occs_file_sound`/`_complete`/`_exact`/`_sorted`/`_nodup` (the readable
      denotational spec), the single-pass `walk_*` implementation (`walk_file = occs_file`, one structural pass,
      no boundary rescan), and the ref-level `Snap.visit_file` (which RUNS `walk_file`, pairing each validated
      `NodeRef` with its ORIGINAL `SourceOccurrence`) with `visit_file_view`/`_complete`/`_order`/`_nodup` and
      `visit_file_snd` (the projection IS `occs_file`).
    - **§20/§25 minimal integration**: the GoTypes typing layer now consumes the §19 traversal —
      `indexed_program_typedb` folds `Snap.visit_file`'s DELIVERED `(NodeRef, syntax)` pairs, taking each
      per-occurrence decision FROM THE DELIVERED SYNTAX FRAGMENT (never recovering it from a reference — no
      `node_at`/`source_occurrence_of_ref` round-trip on the hot path, so the whole-file cost is one traversal,
      not one source recovery per node) and delegating to the SAME `expr_typedb`/`const_info` resolver; it is
      proved EQUAL to the existing `program_typedb` (`indexed_program_typedb_eq`), with the per-file
      `indexed_source_file_typedb_eq` and `occs_file_typedb_eq` beneath it.  No semantic kernel is modified, so
      `ProgramTyped`/`ProgValid`/`go_compile`/package summaries/GoSafe/GoRender/GoEmit are untouched and every
      generated byte is unchanged; GoAST gains one reusable `file_bindings_find` bridge.
    - Gate now **446/446** axiom-free, coverage OK, whole-theory audit covers GoIndex + the GoTypes integration,
      self-tests A-E green; generated bytes byte-identical.  Docs reconciled: CLAUDE / ARCHITECTURE (GoIndex
      layer prose + responsibility row + gated-family entry) / PROGRESS / COLLECTION_AUDIT / this ledger.
  - FINAL candidate SHA: `29f08d6` (`milestone(final): C2`).  FINAL repairs:
    - **round 1** `review(final): C2` (`021c441`) — Codex flagged that the indexed typing traversal DISCARDED
      its paired source fragment and performed repeated source recovery through `node_at` (an O(file)
      `source_occurrence_of_ref` per node = O(file²)/file).  Fixed: removed the `node_at`/`source_occurrence_of_ref`
      round-trip — the syntax now comes from the DELIVERED `SourceOccurrence` of each `visit_file` pair (round 3
      restores index consumption for the ROLE without any recovery).  Gate still 446/446; bytes byte-identical.
    - **round 2** `review(final): C2` — Codex flagged that the traversal itself remained QUADRATIC on nested
      conversions / long sibling runs because `occs_*` recomputes each occurrence's boundary with a per-node
      `end_expr`/`end_stmt`/`end_decl`/`next_*` subtree RESCAN.  Fixed: added the single-pass `walk_*` family —
      each function RETURNS the next-free local id, so a parent reads its child's subtree end from the returned
      cursor and a sibling starts at it, with NO boundary rescan (one structural pass per file, one occurrence
      each).  `walk_file_eq` proves `walk_file = occs_file`, so every exactness/order/NoDup theorem transfers;
      `occs_*` is retained as the readable denotational SPECIFICATION and `visit_file` now RUNS `walk_file`.
      Gate still 446/446 axiom-free; whole-theory audit + self-tests A-E green; bytes byte-identical.
    - **round 3** `review(final): C2` — Codex flagged that after round 1 `indexed_program_typedb` no longer
      constructed/consumed the snapshot index and discarded every paired reference (a source-only fold).  Fixed
      by the SYNTHESIS satisfying rounds 1+3 together: the per-occurrence decision takes the ROLE from the index
      THROUGH the reference — `Snap.node_role idx (fst rocc)`, an outer-FileMap + inner-PositiveMap lookup in the
      PRECOMPUTED `si_outer idx` (built once by the let-bound `index_program p`; NOT a source scan, NOT a
      rebuild) — and the SYNTAX from the DELIVERED occurrence `view_expr (snd rocc)` (NO `node_at` /
      `source_occurrence_of_ref` recovery).  So the index is genuinely consumed, the paired reference is
      consumed, and there is still no per-node source recovery.  `indexed_program_typedb_eq` (= `program_typedb`)
      re-proved via `node_role_matches_source` + `visit_file_view`.  Gate 446/446; bytes byte-identical.

## C0 — preflight cleanup and occurrence-index proof spike
- Review cadence: one intentional final Codex stop only (small, isolated checkpoint)
- Root candidate SHA: n/a (C0 has no root review)
- Root Codex result / repair SHAs: n/a
- Final candidate SHA: `cf91bc9` (`review(final): C0` — second repair; `a3a4d53` was the first candidate)
- Final Codex result / repair SHAs: first review of `a3a4d53` BLOCKED with four findings — (1) child
  enumeration scanned every descendant instead of jumping per child; (2) the `NodeTable` trie was public, not
  hidden behind an abstract interface; (3) the equal-leaves theorem only compared raw keys, without building
  validated references or a source recovery relation; (4) `containing_file` returned only the path, not a
  validated file-root reference.  ALL FOUR addressed across two repair commits — opaque
  `NodeTable` module; `thm9` via `occ_file` recovery + `NodeRef` construction; `containing_file` FileRef +
  `thm6`; and for child enumeration, a first pass used an interval-jump over a materialized id list, which a
  re-review correctly flagged as still O(#descendants) traversal — the final fix is the LIST-FREE
  `child_enum` cursor recursion above (O(#children) steps and lookups).  Generated bytes remain unchanged.
  Codex **ALLOW / GREEN** on `cf91bc9` (review `task-mrnwhwyy`, 2026-07-16T19:27Z — "C0 is GREEN", non-stale).
- Verification result (`make check`): PASS — working tree green (pinned proof 321/321 axiom-free surfaces incl.
  the whole-theory audit over `OccurrenceSpike`; whole-tree `go build ./...` vs goldens incl. the new
  complex-underflow scalar-conversion scar on both sides; working-tree generated go.mod + `.go` byte-match the
  pristine artifact — generated bytes UNCHANGED)
- Push result: fast-forward pushed to `main` (`5e7efd8..cf91bc9`)
- Human disposition: **pending Rob's review** (Codex green; loop stopped and Rob notified — do NOT begin C1
  without explicit authorization)

### C0 decision record (Part 12)
- Selected `LocalNodeId` representation: **file-local `positive` preorder ids**, 1-based, `root_id = 1`
  (`xH`).  Abstract to callers via the `NodeKey`/`NodeTable` API; a file's occurrences are numbered
  `1 .. fi_count` by one canonical preorder pass.
- Selected `NodeTable` representation: **a certified positive-key radix trie**, candidate A — but sealed
  behind an ABSTRACT `NodeTable` module (`Module Type NODE_TABLE` + opaque ascription): callers see only
  `table`/`empty`/`get`/`set` and the three laws (`get_empty`/`get_set_same`/`get_set_other`).  (C1A replaced
  the original C0 project-authored trie with the STANDARD `FMapPositive.PositiveMap` (`Collections.NodeMapBase`);
  the sealing hides the standard map's CONSTRUCTORS and RAW operations — NOT the choice of collection — so C2
  RETAINS this selected standard positive map and does not swap it for another representation.)  EMPTY
  assumption closure, decidable-key ergonomics.
- Selected metadata fields: `NodeMeta { nm_kind : SyntaxKind ; nm_parent : option positive ;
  nm_role : NodeRole ; nm_subtree_end : positive }`.  No syntax-subtree copy (thm14); `subtree_end` powers the
  O(1) preorder-interval ancestor test and interval-scoped child enumeration.  `first_child`/`next_sibling`
  were deliberately NOT added (Master Plan 4.10 "do not add fields by reflex").
- Build / query complexity (STRUCTURAL SHAPE, not a proved machine-cost theorem — these describe the standard
  positive-map operation counts and the removal of AST search/re-scan; Fido proves the semantic laws, not a
  kernel O(log n) result): **build** — one preorder pass, each occurrence inserted exactly once
  by one standard-map `NodeTable.set`, no re-scan, no append-to-end, no index reconstruction
  (thm_builder_no_structural_search shows the builder reads only tree SHAPE); **containing file O(1)**
  projection for the path plus a validated file-root `FileRef` (`containing_file`, thm6); **parent / kind /
  meta lookup O(log n)** `NodeTable.get`, never an AST search; **ancestor test O(log n) lookup + O(1)**
  interval arithmetic (thm13 sound+complete); **direct children** enumerated by a LIST-FREE
  cursor recursion (`child_enum`, a `Function` on the decreasing measure `limit+1 - cursor`): it looks up only
  the id at the cursor and, after each node, jumps the cursor straight to `subtree_end+1` — it never
  constructs or traverses the skipped descendant ids, so BOTH the lookup count AND the number of recursive
  steps are O(#direct children), never O(#descendants).  Proved correct both ways (thm4 sound+complete,
  thm11 sorted) via the tiling lemmas `first_child`/`next_child`, themselves derived from the existing subtree
  invariants.
- Rejected alternatives + reasons: **(B) primitive dense array** (`PArray`/`Uint63`) — O(1) lookup but built
  on KERNEL PRIMITIVES, forbidden by standing law rule 4 (no kernel primitive); its trust story is a kernel
  extension outside pure CIC, incompatible with the zero-axiom policy regardless of speed.  **(C) association
  `list` table** — trivial to prove but a forbidden O(n) list-scan node-table lookup (Master Plan 4.8); not
  selected merely for proof convenience.
- Proof-spike commit SHA: `a3a4d53` (introduced) → `9a2e85e`, `cf91bc9` (review repairs); module
  `OccurrenceSpike.v` — DELETED when the production `GoIndex` lands in C2.
- Undecided minor choice named: whether the production C2 index keys ONE global trie by a packed
  `(file, local)` key or keeps a per-file table behind a path-keyed outer map — deferred to C2 (the ownership /
  identity architecture itself IS decided: file-local preorder ids + validated `NodeRef` + derived trie index).

## C0A — exact snapshot-local occurrence identity and total navigation (COMPLETE)

C0 reached Codex-green at `cf91bc9`, but a subsequent human holistic review found a deeper, foundational
architectural defect that Codex's scoped review did not surface. C0A corrects it; C1 stays forbidden until
C0A is human-approved. The earlier C0 Codex-green result and the C0 findings/repair ledger above are
preserved as history — not rewritten.

- Correction baseline SHA: `11fd1a1`
- Directive: installed VERBATIM as `.review/NEXT_STEPS.md`
- The defect (three coupled parts):
  1. **Source/index coupling** — `NodeRef` was indexed by a free-standing `SyntaxIndex` value, so two
     different source forests with identical paths and tree shape but different literal payloads compute the
     same index and share the same `NodeRef` type. A reference must belong to the exact immutable source
     snapshot, not merely to index data. `SyntaxIndex`, `FileRef`, and `NodeRef` must be indexed by the exact
     `TForest`.
  2. **API honesty** — `ref_meta`/`containing_file` returned `option`, `node_kind` invented `KFile`, and
     `children_of` silently dropped a child on rebuild failure. Structurally guaranteed queries must be TOTAL
     (only `parent_of` stays optional — a root has no parent). No impossible-case fallback may manufacture a
     plausible semantic answer.
  3. **Complexity accounting** — ordinary navigation performed a linear `file_of` scan over
     `SyntaxIndex := list FileIndex`, so the ledger overstated parent/kind/meta lookup as O(log n). Navigation
     from an existing `NodeRef` must not scan the file list; it uses the `FileRef`'s hidden slot into an outer
     `NodeTable`.
- Review cadence: at most two intentional Codex stops — ROOT barrier (`milestone(root): C0A —`, repairs
  `review(root): C0A —`) then FINAL barrier (`milestone(final): C0A —`, repairs `review(final): C0A —`).
- Root candidate SHA: `0e6b739` (`milestone(root): C0A`)
- Root Codex result / repair SHAs: `5176e7b` (`review(root): C0A` — routed `ref_of_key` validity through the
  precomputed index; ROOT Codex **GREEN** on `5176e7b`, review `task-mro187cp`, non-stale)
- Final candidate SHA: `357430b` (`milestone(final): C0A` — first FINAL candidate)
- Final Codex result / repair SHAs: first review of `357430b` BLOCKED (review `task-mro2cq4e`,
  2026-07-16T22:17Z, non-stale) with three findings — (1) `si_ok` proved only that REAL slots hold their
  build, so a spurious entry at an unoccupied slot still satisfied the invariant (one-directional, fail-open);
  (2) `file_of_path_complete`/`ref_of_key_complete` assumed an EXISTING handle, so minting completeness was
  circular (never established minting FROM a source occurrence); (3) the structural family (ancestry,
  enumeration) was not restated over the corrected API, and the two-file / duplicate-path / erased-index
  fixtures were absent.  ALL THREE repaired in `review(final): C0A` (`c74cb0a`) — see below.  Generated bytes UNCHANGED.  Codex
  **ALLOW / GREEN** on `c74cb0a` (review `task-mro3iu33`, 2026-07-16T22:47Z — "C0A at c74cb0a has no blocking
  implementation defects or architectural conflicts", non-stale: reviewed after the `c74cb0a` commit).
- Verification result (`make check`): PASS on the working tree — pinned proof 361/361 axiom-free surfaces incl.
  the whole-theory audit over `OccurrenceSpike`; e2e emitted + `go build ./...` vs goldens; working-tree
  generated go.mod + recursive `.go` byte-match the pristine artifact (generated bytes UNCHANGED — the spike is
  isolated from the emit pipeline).  The pre-commit hook re-ran the SAME full gate on the STAGED `c74cb0a`
  snapshot and passed.
- Push result: fast-forward pushed to `main` (`cf91bc9..c74cb0a` C0A range: `milestone(contract)` →
  `milestone(root)`/`review(root)` → `milestone(final)`/`review(final)`).
- Human disposition: **pending Rob's review** (Codex green; loop stopped and Rob notified — do NOT begin C1
  without explicit authorization).

### C0A decision record (filled at the ROOT barrier; navigation-proof family completes at FINAL)
- Path-unique `TForest` shape: `Record TForest { forest_files : list TFile ; forest_paths_unique :
  NoDup (map tf_path forest_files) }` — duplicate paths are unrepresentable, so a path names at most one file.
- `SyntaxIndex fs` representation + correspondence (final invariant): `Record SyntaxIndex fs
  { si_outer : NodeTable FileIndex ; si_ok : si_outer = outer_of fs }` — the outer table IS the canonical
  build of the exact snapshot (exact presence AND absence: `outer_get_exact` gives every file slot its
  `build_file f` and every non-slot `None`), so no spurious/foreign entry can satisfy the invariant;
  `index_forest fs` is the only builder (constructor sealed).  (History: this landed at the C0A ROOT barrier
  as the one-directional `forall slot f, forest_file_at fs slot = Some f -> get slot si_outer = Some
  (build_file f)`, which the C0A FINAL Codex review correctly flagged as fail-open — see finding 1 below — and
  which was strengthened to `si_outer = outer_of fs`.)
- `FileRef fs` representation + hidden-slot role: `Record FileRef fs { file_ref_slot : positive (HIDDEN) ;
  file_ref_file : TFile ; file_ref_at : forest_file_at fs file_ref_slot = Some file_ref_file }`.  The slot is
  a private optimization handle (never rendered, never the public key); the public identity is `file_ref_path`.
- `NodeRef fs` representation: `Record NodeRef fs { node_ref_file : FileRef fs ; node_ref_local : positive ;
  node_ref_valid : valid_localb (file_ref_file node_ref_file) node_ref_local = true }` — indexed by the EXACT
  snapshot `fs`; `node_ref_key = (file_ref_path, local)`, slot NOT in the key.
- Outer / per-file table design: an abstract slot-keyed outer `NodeTable FileIndex` (`outer_of`, one `set` per
  file), each entry the built per-file index (path + trie + count).  Both `NodeTable`s are the sealed radix trie.
- Corrected query complexities: build O(files·log files + Σ nodes·log nodes/file); containing-file O(1)
  projection off the `NodeRef`; `ref_meta`/`node_kind`/`node_role`/`subtree_end` = ONE outer slot lookup
  (O(log files)) + ONE per-file lookup (O(log nodes/file)) — **no file-list scan**; ancestor O(log)+O(1);
  direct children one file-index acquisition then the list-free O(#children) `child_enum` jump.
- Raw-key minting cost (`ref_of_key` / `file_of_path`): `ref_of_key` takes the `SyntaxIndex fs` and validates
  THROUGH its precomputed outer table (via `valid_in_index` + `si_ok`) — it does NOT rebuild the per-file index.
  Cost O(files + log files + log nodes-per-file): one `find_slot` file-list scan (path -> slot) + one outer-slot
  lookup + one per-file lookup.  This is the separate minting boundary; the hot path from an existing `NodeRef`
  never uses it.  (ROOT review `task-mro0ytwl` found the first version rebuilt `build_file` via `valid_localb`;
  fixed to route validity through the index.)
- Sealing: `Module Snap : SNAP_SIG` hides the raw `mkFileRef`/`mkNodeRef`/`mkSyntaxIndex` and the slot; only
  the validated minting/navigation API + theorems are exposed.
- Deleted fallback/option/filter branches: `node_kind`'s `KFile` fallback; `ref_meta`/`containing_file`'s
  `option` results; `children_of`'s silent child-drop — all replaced by TOTAL functions (via `option_get` off a
  proven-present option / `refine_children` off `child_enum` soundness).  Only `parent_of` stays `option`
  (root has no parent).
- Same-shaped / different-source + repeated-equal-leaf regression: `fs_a` (leaves 5) vs `fs_b` (leaves 6, same
  paths/shape) — `Fail Definition reg_cross_snapshot : NodeRef fs_b := rleaf_a5` (type-level separation);
  `node_at` recovers `TLeaf 5` in `fs_a` and `TLeaf 6` in `fs_b`; the two equal `TLeaf 5` leaves of `fs_a` have
  DISTINCT references (distinct keys).  All axiom-free (gate 351/351, whole-theory audit).

### C0A FINAL theorem family (completed at the FINAL barrier — restated over the source-indexed API)
All exposed through `Snap`'s signature (raw constructors stay hidden) and gated axiom-free.  Structural
family (per-file, retained from C0 over the corrected API): `thm1..thm4`, `thm7` (enum sound/complete/NoDup),
`thm11` (children source-sorted), `thm13` (interval ancestry sound+complete), `thm14` (meta stores no
subtree), `thm_builder_no_structural_search`, `child_enum` (list-free O(#children) jump).  New reference-level
family:
- Source snapshot / file roots: `forest_slot_unique` (path uniqueness — a path names ≤1 slot, from the
  `NoDup` field), `file_of_path_complete` (file lookup total+complete: a file's own path mints exactly its
  handle), `file_ref_path_inj` (FileRef path equality decides file occurrence equality).
- Index/source exactness: `outer_get_at` + `si_ok` (`index_forest` describes exactly its `fs`), `build_file_wf`
  (every occurrence one metadata entry and back), type-level cross-snapshot separation (`Fail
  reg_cross_snapshot`).
- Node references: raw ctor hidden (module ascription); `ref_of_key_sound` + `ref_of_key_complete`;
  `node_ref_key_inj` (NodeKey equality reflects reference equality within one snapshot);
  `reg_equal_leaves_distinct` (repeated equal fragments → distinct refs).
- Total queries: `thm_node_kind` (indexed kind, no fallback), `thm_node_role`, `thm_ref_meta_built`,
  `thm_containing_file`, `thm_parent_root` (= None), `thm_parent_nonroot` (Some valid), children carry no
  dropped/invalid reference (`refine_children` off `child_enum` soundness).
- Navigation: `thm_child_parent` AND `thm_parent_child` (parent/child inverse, BOTH directions at the NodeRef
  level), `thm_parent_same_file` + `thm_children_same_file` (parent/child share the FileRef),
  `thm_containing_file` (containing-file recovery), `thm_builder_deterministic` (pure builder → identical
  index for equal source).
- Performance-shape surfaces (from the code structure, not a cost model): navigation from a `NodeRef` uses one
  outer-slot lookup + one per-file lookup and NO `find_slot`/file-list scan; `child_enum` materializes no
  descendant list and calls `pos_seq` nowhere in enumeration; query functions never re-call `index_forest`;
  both `NodeTable`s are the sealed radix trie (no list-backed table); `index_forest` is built once per snapshot.
- Master-plan reconciliation (§12): `.review/SOURCE_FOREST_MASTER_PLAN.md` §4.3/§4.7 now state the
  snapshot-indexed `NodeRef` carrying a validated `FileRef`, the total API with only `parent_of` optional, the
  no-file-list-scan navigation invariant, the separate raw-key minting boundary with its own cost, and the
  no-semantic-fallback rule.

#### FINAL-repair additions (review `task-mro2cq4e` → `review(final): C0A`)
- EXACT index/source correspondence (finding 1): `si_ok` strengthened from the one-directional "real slots
  hold their build" to `si_outer = outer_of fs` (the table IS the canonical build).  `thm_index_describes_forest`
  (over the exposed `index_at`) proves BOTH directions — every file slot holds exactly that file's build AND
  every non-slot holds nothing — so no spurious/foreign entry can satisfy the invariant.  The exactness drives
  the query API (`si_ok_at` powers `ref_fi_some`/`valid_in_index_eq`).  Per-file "one occurrence ↔ one meta"
  stays `build_file_wf`.
- NON-CIRCULAR minting completeness (finding 2): `file_of_path_source` (a real slot mints a `FileRef` by its
  path) and `ref_of_key_source` (a valid occurrence mints a `NodeRef` by its key) — established FROM source
  membership with the constructors hidden, via `find_slot_complete`/`forest_find_complete`/`file_of_path_find`
  (the earlier `file_of_path_complete`/`ref_of_key_complete` remain as the round-trip direction).
- Structural family restated over the corrected API (finding 3): `thm_children_of_source_order`
  (`StronglySorted Pos.lt` over the enumerated child locals) and `thm_children_of_nodup` (children as
  `NodeRef`s are `NoDup`); a NodeRef-level ancestor test `is_ancestor_ref` (O(1) preorder-interval arithmetic)
  proved SOUND and COMPLETE against `RefAncestor` (the exposed transitive closure of `parent_of`) in
  `thm_ref_ancestry`.
- §9 fixtures added + gated: `reg_index_data_equal` (`outer_of fs_a = outer_of fs_b` — same-shape snapshots
  have literally equal index DATA after erasing the source index, since the metadata builder discards leaf
  payload), `reg_dup_path_rejected` (any file duplicated violates the `NoDup` path invariant → duplicate paths
  UNREPRESENTABLE), and `reg_two_file` (a two-file forest, both files mintable to distinct-path handles).
- Gate: 361/361 axiom-free readable surfaces; whole-theory audit + self-tests A-E green; generated bytes still
  byte-identical.

## C0B — exact source-occurrence correspondence (COMPLETE)

C0A reached Codex-green at `c74cb0a` (pushed `46a9d65`), but a subsequent human review found one remaining
under-specification.  C0B corrects it; C1 stays forbidden until C0B is human-approved.  The C0/C0A
Codex-green history and their findings/repair ledgers above are preserved — not rewritten.

- Correction baseline SHA: `46a9d65092a58dacb805f34acd2ad1269886a54e` (the C0A completion tip; contains the
  completed, Codex-green C0 and C0A proof spikes)
- Directive: installed VERBATIM as `.review/NEXT_STEPS.md`
- The under-specification: the index is proved structurally consistent with `build_file`
  (`si_outer = outer_of fs`; each file slot holds `build_file f`) AND `build_file`'s tables are proved
  structurally well-formed (canonical intervals, nested parents, valid subtree ends, correct ancestry and
  child enumeration).  But the universal theorem family does NOT yet prove that the metadata stored at local
  ID N is the metadata of the EXACT source occurrence at local ID N — a structurally-consistent-but-
  semantically-wrong labeling (a leaf marked `KDecl`, swapped `RChild 0/1`, shifted decl/stmt indexes) would
  not necessarily fail the existing theorems.  C0B closes that gap with an INDEPENDENT (table-free,
  builder-independent) source-occurrence specification and a universal exactness theorem
  (`build_file_source_exact`) pinning kind/role/parent/subtree-end, both presence and absence, lifted through
  the sealed `NodeRef` API (`ref_meta_matches_source`).  It also removes the public raw-slot `index_at` leak
  and reconciles three stale docs (root-ID=1, the final `si_ok` invariant, source-recovery complexity).
- Review cadence: at most two intentional Codex stops — ROOT (semantic-root:
  `milestone(root): C0B —`, repairs `review(root): C0B —`) then FINAL (`milestone(final): C0B —`, repairs
  `review(final): C0B —`).
- Contract activation SHA: `6273673` (`milestone(contract): C0B` — directive verbatim + status)
- Root candidate SHA: `32cb310` (`milestone(root): C0B`)
- Root Codex result / repair SHAs: Codex **ALLOW / GREEN** on `32cb310` (review `task-mrodoyrf`,
  2026-07-17T03:28Z — "GREEN — no blocking implementation defects or architectural conflicts in the C0B
  semantic-root candidate", non-stale; no root repair needed).  After root GREEN, continued directly to final
  integration (no progress stop).
- Final candidate SHA: `2ea38b5` (`milestone(final): C0B` — first FINAL candidate)
- Final Codex result / repair SHAs: first review of `2ea38b5` BLOCKED (review `task-mroeedsj`,
  2026-07-17T03:53Z, non-stale) with two findings — (1) the sealed API pinned only the erased-view metadata
  (`occurrence_meta` drops `occurrence_view`), so the public contract permitted an occurrence carrying an
  unrelated fragment with correct structural metadata; `source_occ_of_ref_eq` and a universal `node_at`
  agreement were not exposed, and the per-kind source-view surfaces were not gated; (2) `node_parent_matches_
  source` pinned the parent metadata but no public theorem connected the source parent local ID to the
  reference `parent_of` returns.  Repaired in `review(final): C0B` — exposed + gated `source_occ_of_ref_eq`,
  `node_at_matches_source_view`, `node_parent_ref_matches_source`, and the per-kind source-VIEW fixtures
  `wf_src_{root,decl0,stmt0,bin,leaf}`.  Gate 386 -> 394 axiom-free; generated bytes UNCHANGED.  Codex
  **ALLOW / GREEN** on `92a910b` (review `task-mroeta8a`, 2026-07-17T04:03Z — "C0B at 92a910b has no blocking
  implementation defects or architectural conflicts", non-stale: reviewed after the `92a910b` commit).
- Verification result (`make check`): PASS on the working tree — pinned proof 394/394 axiom-free surfaces
  incl. the whole-theory audit over `OccurrenceSpike`; e2e emitted + `go build ./...` vs goldens; working-tree
  generated go.mod + recursive `.go` byte-match the pristine artifact (generated bytes UNCHANGED — the spike is
  isolated from the emit pipeline).  The pre-commit hook re-ran the SAME full gate on the STAGED `92a910b`
  snapshot and passed.
- Push result: fast-forward pushed to `main` (`46a9d65..92a910b` C0B range: `milestone(contract)` →
  `milestone(root)` → `milestone(final)` → `review(final)`; ledger `305d6cb`).
- Human disposition: **ACCEPTED by Rob (2026-07-17, review disposition GREEN).**  C0, C0A, and C0B are all
  accepted; the occurrence architecture is considered foundationally correct and its decisions frozen (see the
  master plan).  Rob authorized activating **C1** exactly as defined in the master plan.  Two non-blocking
  cleanups folded into the first C1 commit (no separate checkpoint): (1) refresh any doc still on an older
  proof-surface count / campaign state; (2) state that proof-only source recovery is not a hot-path guarantee
  (ordinary compilation receives syntax + `NodeRef` together — already in master plan §4.11).

### C0B decision record
- Independent source specification: `SyntaxView : SyntaxKind -> Type` (`ViewFile`/`ViewDecl`/`ViewStatement`/
  `ViewExpression`) reuses the ORIGINAL syntax fragment (no parallel/copied grammar, no persistent second
  AST, no copied syntax in metadata); `SourceOccurrence { occurrence_kind ; occurrence_view ;
  occurrence_parent ; occurrence_role ; occurrence_subtree_end }`; `occurrence_meta` projects to `NodeMeta`.
  `source_occurrence_at : TFile -> positive -> option SourceOccurrence` (via `occ_expr'`/`occ_stmt'`/
  `occ_stmts'`/`occ_decl'`/`occ_decls'`) covers every toy occurrence with exact role/parent/subtree in source
  order.  It is table-free and builder-independent (uses ONLY the source syntax + the boundary functions
  `end_expr`/`end_stmt`/`next_stmts`/`end_decl`/`next_decls`/`count_file`; NEVER `NodeTable`/`build_*`/
  `FileIndex`/`ref_meta`/`node_kind`/`parent_of`/`children_of`/`child_enum`).
- Universal theorem: `build_file_source_exact : forall f local, NodeTable.get local (fi_table (build_file f))
  = option_map occurrence_meta (source_occurrence_at f local)` — every id, no NodeRef, no validity assumption,
  presence AND absence.  Consequences A-H: `source_occurrence_meta`, `meta_source_occurrence`,
  `source_absence`, `source_occurrence_unique`, `source_kind_exact`, `source_role_exact`,
  `source_parent_exact`, `source_subtree_end_exact`.  Proof via `build_expr_get`/`build_stmt_get`/
  `build_seq_stmt_get`/`build_decl_get`/`build_seq_decl_get` + interval frame lemmas.
- Sealed lift (§6): `source_occurrence_of_ref : NodeRef fs -> SourceOccurrence` TOTAL (no fallback, via
  `option_get` off validity); `ref_meta_matches_source` (the permanent public theorem) + `node_kind_/
  node_role_/node_parent_/node_subtree_end_matches_source`.  `node_at` REDEFINED as `view_expr ∘
  source_occurrence_of_ref` (the OLD `occ_*`/`occ_file` expression-only recovery authority DELETED — one
  source-recovery authority).
- Abstraction (§7): public `index_at` REMOVED from `SNAP_SIG` (retained INTERNAL for the exactness proof);
  negatives `Fail Check Snap.{index_at, mkSyntaxIndex, mkFileRef, mkNodeRef, si_outer, file_ref_slot}`.
- Mutation fixtures (§8): `wf` (2 decls, first with 2 stmts incl. a nested binary); `wf_meta_*` pin the exact
  stored meta at ids 1..11 + `wf_meta_absent` at 12, each derived from `build_file_source_exact` (never by
  unfolding the builder); sealed-API `reg_ref_kind_a5`/`reg_ref_role_a5`/`reg_ref_parent_a5` via the
  `*_matches_source` theorems; `reg_node_at_a`/`reg_node_at_b` restate fs_a/fs_b payload recovery through the
  new view API.  Mutation-sensitivity: a leaf mislabeled `KDecl`, swapped `RChild 0/1`, a shifted decl/stmt
  index, or a wrong parent/subtree makes `build_file_source_exact` unprovable — the universal theorem (and
  every `wf_meta_*`/`*_matches_source` corollary) is what rejects each category.
- Docs (§9): master plan §4.11 (honest O(file-size) source-recovery + one spec), §4.7 (public storage
  abstraction: no public `index_at`, exactness via validated refs), §4.12 theorem 1 (root ID = 1) and new
  theorem 15 (exact per-occurrence correspondence, a C2 acceptance criterion); this C0A headline `si_ok`
  record rewritten to `si_outer = outer_of fs`.
- Gate: 386/386 axiom-free readable surfaces; whole-theory audit + self-tests A-E green.

## C1 — specification-shaped file roots and path-keyed source forest (COMPLETE)

C0/C0A/C0B accepted by Rob (occurrence architecture frozen); C1 activated exactly as defined in the master
plan (Part 3 + Part 8 + Part 13).  C2 stays forbidden until C1 is human-approved.

- Baseline SHA: `305d6cb` (C0B completion tip; `d06ad5a` recorded the C0B acceptance)
- Directive: installed as `.review/NEXT_STEPS.md` (the master-plan C1 checkpoint definition)
- Scope: replace `map[path, declaration-list]` with path-bearing file roots (`GoSourceFile`/`GoFileNode`/
  `GoFileSet`/`GoProgram`); move the package clause into source syntax (delete `cf_pkg_name`); one path
  authority; path-uniqueness + lookup laws; migrate the whole pipeline (GoCompile/GoSafe/GoRender/GoEmit +
  witnesses/empty/multi/directory image/pre-commit/docs/gate); NO occurrence index (that is C2), NO new Go
  feature, NO broadened package/import semantics; generated bytes BYTE-IDENTICAL.
- Review cadence: two intentional Codex stops — ROOT (`milestone(root): C1 —`, repairs `review(root): C1 —`)
  then FINAL (`milestone(final): C1 —`, repairs `review(final): C1 —`).
- Contract activation SHA: `7fd8c09` (`milestone(contract): C1`)
- Root candidate SHA: `de1909a` (`milestone(root): C1`)
- Root Codex result / repair SHAs: Codex **ALLOW / GREEN** on `de1909a` (review `task-mroiibf1`,
  2026-07-17T05:43Z — "C1 ROOT has no blocking implementation defects or architectural conflicts within the
  declared scope", non-stale; no root repair needed).  After root GREEN, continued directly to final
  integration (no progress stop): the pipeline migration was already complete, so FINAL is the docs/gate
  reconciliation + final byte-verify.
- Final candidate SHA: `a5e9895` (`milestone(final): C1` — first FINAL candidate)
- Final Codex result / repair SHAs: first review of `a5e9895` BLOCKED (review `task-mroizvrb`,
  2026-07-17T06:00Z, non-stale) — `build_program` retained the pre-C1 `(path, declarations)` adapter instead
  of the master-plan §3.5 signature `ModuleSpec -> list GoFileNode -> option GoProgram`.  Repaired in
  `review(final): C1` — `build_program` now takes `list GoFileNode` straight through `fileset_of_list`; added
  the convenience node builder `main_file_node`; `WitnessMulti` constructs `GoFileNode` roots via it.  make
  check GREEN; generated bytes UNCHANGED.  Codex **ALLOW / GREEN** on `946822f` (review `task-mroj92tj`,
  2026-07-17T06:06Z — "GREEN — no blocking implementation defects or architectural conflicts found in C1
  through 946822f", non-stale: reviewed after the `946822f` commit).
- Verification result (`make check`): PASS on the working tree — theory + gate 403/403 axiom-free (whole-theory
  audit); e2e emitted the witness/multi/EMPTY trees + `go build ./...` vs goldens; working-tree generated
  go.mod + recursive `.go` byte-match the pristine artifact (generated bytes BYTE-IDENTICAL — behavior
  preserved across the source-forest migration).
- Push result: pending
- Push result: fast-forward pushed to `main` (`305d6cb..946822f` C1 range: `milestone(contract)` →
  `milestone(root)`/`review(root)` → `milestone(final)`/`review(final)`).
- Human disposition: **pending Rob's review** (Codex green; loop stopped and Rob notified — do NOT begin C2
  without explicit authorization).

### C1 root landing (records + path authority + package clause + full pipeline migration)
- `GoAST.v`: `PackageClauseSyntax` (`PkgMain` only), `ImportSpecSyntax` (EMPTY type → `source_imports`
  intrinsically `nil`), `GoSourceFile { source_package ; source_imports ; source_decls }`,
  `GoFileNode { file_path ; file_source }`, `GoFileSet { file_members ; file_paths_unique }`; `GoProgram`'s
  `prog_files : GoFileSet`.  DELETED `GoFileAST := list GoDecl`.  File-set API + laws: `find_file`
  (sound/complete/functional), `file_paths`, `file_member`, `FilesEqual` (equivalence),
  `dup_path_unrepresentable`, `fs_empty`/`fs_singleton`/`fileset_of_list`.  ONE path authority (the path lives
  on the node; no parallel outer key).  `prog_entries` is a DERIVED `(path, decls)` view; `fileset_fmap`
  renders the forest keyed by path.
- `GoCompile.v`: DELETED `CompilationFacts`/`cf_pkg_name`; `GoCompile p := ProgValid p` (no facts record, no
  unused placeholder); `CompilableProgram { cp_program ; cp_ok }`.  `GoSafe.v`: deleted `sp_pkg_name`.
- `GoRender.v`: `render_package_clause` renders the SOURCE-owned package clause (`PkgMain` → `main`);
  `render_file` over `GoSourceFile` — byte-identical output.  `GoEmit.v`: `render_map = fileset_fmap
  render_file`; deleted `sp_pkg_name_main`.  Witnesses migrated (`mkCompilable X valid`).
- Construction API (Master Plan §3.5, the FINAL Codex repair): `build_program : ModuleSpec -> list GoFileNode
  -> option GoProgram` takes specification-shaped file roots through `fileset_of_list` (no internal path/decl
  synthesis); convenience `main_file_node`/`singleton_program`; `WitnessMulti` builds `GoFileNode` roots.
- No temporary adapter / second file authority introduced.  Gate: 403/403 axiom-free (C1 file-set laws added).

## C1A — Standard Collection Foundations and Repository-Wide Collection Audit (COMPLETE)

C1 reached Codex-green (`946822f`, pushed `75d24b2`), but Rob's holistic review found a repository-wide
COLLECTION-MODEL defect: the public file "set" is an exposed list + `NoDup`; the generic `FMap.v` is a linear
association list; package compilation repeatedly scans file lists (O(files²)); and the occurrence spike
contains a hand-written positive-key trie.  Those are not acceptable as permanent compiler foundations.  C1A
corrects it repository-wide.  The C0/C0A/C0B/C1 Codex-green history and their ledgers above are PRESERVED —
not rewritten.  C2 remains FORBIDDEN until C1A is Codex-green, pushed, and human-approved.  This directive is
the binding completion contract.

- Correction baseline SHA: `75d24b22dfa5131738d2ede8a0e1d7bf567891b2` (the C1 completion tip)
- Directive: installed VERBATIM as `.review/COLLECTION_FOUNDATIONS_MASTER_PLAN.md` and `.review/NEXT_STEPS.md`
- Scope: replace EVERY project-authored collection with a mature pinned-stdlib implementation — `GoProgram`
  stores a real `FileMap.t GoSourceFile` (path is the key, not stored in the value); DELETE `FMap.v` and the
  `GoFileSet` list+NoDup; replace the OccurrenceSpike positive-key trie with `FMapPositive` and the toy forest
  with a `FileMap` (delete hidden file slots); package grouping via a `PackageMap` (one pass, not O(files²));
  `DirectoryImage` uses the standard `FileMap` with a canonical derived transport list; the OCaml sink uses
  `Map`/`Set` for desired outputs / stale checks / abandoned temps; `g_fido` audit roots use
  `Names.GlobRef.Set`.  Lists remain ONLY for source/execution order, multiplicity, rollback stacks, or
  DERIVED map/set enumerations.  Duplicate-rejecting map construction proved sound AND complete (both
  directions — closing the C1 human-review finding).  All behavior + every generated byte UNCHANGED.  New
  permanent PAINFUL_LESSONS entry (#14).  Collection selection (FMapAVL vs FMapFullAVL, FMapPositive) recorded
  at the ROOT barrier per §2.
- Review cadence: two intentional Codex stops — ROOT (`milestone(root): C1A —`, repairs `review(root): C1A —`)
  then FINAL (`milestone(final): C1A —`, repairs `review(final): C1A —`).
- Contract activation SHA: `75d24b2` (baseline).
- Selected collection modules + reason (§2 pinned-container spike, `FMapAVL`/`FMapPositive` both confirmed
  available in the pinned rocq-stdlib 9.1.0 image):
  - general ordered-key finite map (file/package maps): **`FSets.FMapAVL`** — Rocq's mature standard-library
    ordered finite map; the standard implementation uses AVL-tree operations.  Fido PROVES the functional map
    semantics it consumes; Fido does NOT claim a project kernel theorem for the AVL balance invariant or a
    machine-level O(log n) complexity.  Chosen over `FMapList` (a standard association-list map, whose
    linear-scan cost is the very defect C1A removes).  `FMapFullAVL` is the standard library layer that
    packages/proves the AVL balance invariant on top — it is NOT redundant; it is the appropriate candidate IF
    formally-packaged balance ever becomes part of Fido's proved contract (do not switch merely for wording).
    Keyed by `String_as_OT` (packages) and by a new `FilePath_OT` ordered key (files).
  - positive-key finite map (per-file local-node index): **`FSets.FMapPositive.PositiveMap`** — Rocq's mature
    standard positive-key map from certified-compiler work; Fido relies on its structural key-bit traversal
    shape and does NOT claim a new machine-cost theorem.  Chosen over a project radix trie (the collection law
    forbids Fido authoring any collection) and `PArray`/`Uint63` (kernel primitives, forbidden by standing law
    rule 4).
  All wrapped in `Collections.v`: `FileMapBase`/`FileMapFacts`/`FileMapProps`, `PackageMapBase`/`PackageMapFacts`,
  `NodeMapBase` — thin re-exports that instantiate standard functors and prove no tree/list-backed collection.
- Root candidate SHA: **this commit** (`milestone(root): C1A`).
- Root barrier state — ALL ROOT criteria met and locally proof-green:
  - `Collections.v` exists, axiom-free; `FilePath_OT` ordered-key facts (`fp_str_inj`, `lt_trans`,
    `lt_not_eq`, `compare`, `eq_dec`) proved; standard `FileMap`/`PackageMap`/`PositiveMap` wrappers exist.
  - `FMap.v` DELETED (removed from `dune (modules …)` and the repo; gate surfaces retargeted).
  - `GoProgram.prog_files : GoFileMap = FileMapBase.t GoSourceFile` — the path is the KEY, never stored in the
    mapped value; `GoFileNode` is construction/view only; `filemap_of_nodes` is the duplicate-rejecting builder,
    SOUND + COMPLETE (`filemap_of_nodes_success_iff_unique` / `filemap_of_nodes_none_iff_duplicate`).
  - Whole pipeline migrated off the list authority: `GoTypes.ProgramTyped`/`program_typedb` over map bindings;
    `GoCompile.package_main_counts` via a `PackageMap` one-pass `FM.fold` (no O(files²) re-scan);
    `GoSafe`/`GoEmit.render_map = FM.map render_file`; `DirectoryImage.di_go_files : FileMapBase.t string`;
    the transport list is the canonical `FileMapBase.elements` enumeration (order-only list, not authority).
  - `OccurrenceSpike` uses standard maps, NO hidden slot: `NodeTable` now wraps `Collections.NodeMapBase`
    (custom radix trie DELETED); `TForest := FileMapBase.t TSourceFile` (list + `NoDup` + 1-based slots +
    `build_outer` outer trie all DELETED); `outer_of = FileMap.map build_file`; `FileRef` carries path + source
    + a `find path fs = Some source` membership proof; the C0/C0A/C0B occurrence + navigation theorem family
    recompiles over the new maps (erased-index equality restated as semantic `FileMap.Equal`; duplicate-path
    negative restated as map key-functionality).
  - Gate axiom-free: readable Print-Assumptions gate green; whole-theory `Fido Audit Assumptions` green over
    the new module set (`… Collections GoAST … OccurrenceSpike`); self-tests A–E pass.
  - Behavior + EVERY GENERATED BYTE UNCHANGED: `make check` green, including `generated-compare OK — the root
    go.mod + recursive .go byte-match the pristine build (exact path set + bytes)`.
- Root Codex result / repair SHAs: ROOT candidate `cc39433` reviewed — **2 findings** (`review(root): C1A`):
  (1) **builder exactness missing** — `filemap_of_nodes` had only the success/failure characterization
  (success⟺unique, none⟺dup), never a POSITIVE proof of what the built map contains → added
  `filemap_of_nodes_maps_to` (on success every input node maps to its own source; a duplicate FAILS the build,
  never silently overwrites) + `filemap_of_nodes_mapsto_source` (every binding comes from an input node) —
  together pinning the map EXACTLY to the input forest; both gated.  (2) **silent overwrite in the occurrence
  snapshot constructor** — `OccurrenceSpike.forest_of` folded `add` over the node list, so a duplicate path
  would SILENTLY DROP the earlier source (the exact §6 anti-pattern) → made `forest_of` a duplicate-REJECTING
  fixpoint (`mem` then `add`, `None` on repeat, mirroring `filemap_of_nodes`), added the `forest_of_dup_rejected`
  theorem (a same-path pair builds to `None`), routed the §9 fixtures through a total `forest_of_ok` extraction,
  and gated `forest_of_dup_rejected`.  Repair verified: `make check` green incl. byte-compare.  Repair SHA
  `cc7a4d7`.  **ROOT Codex re-review GREEN** (task `task-mrpb612l-nvzalx`, createdAt 2026-07-17T19:05:44Z —
  NON-STALE, 49 s after the `cc7a4d7` commit at 19:04:55Z): "ALLOW: C1A ROOT repair is GREEN; no blocking
  defects or architectural conflicts remain."  → FINAL integration proceeds directly (§14, no progress stop).
- Final candidate SHA: **this commit** (`milestone(final): C1A`).  FINAL integration delivered (all axiom-free,
  gated 427/427, bytes byte-identical, `make check` green):
  - §6 builder exactness/order-independence: `filemap_of_nodes_find` (the full find-characterization),
    `_duplicate_rejects` + `_duplicate_different_source_rejects`, `_permutation` (permuted nodes → `FilesEqual`),
    `build_program_some_iff_unique`.
  - §7 map-based typing order-independence: `ProgramTyped_Equal`, `program_typedb_Equal`,
    `program_typedb_build_permutation`.
  - §8 map-based package grouping: introduced `PackageSummary` + one-pass `package_summaries` (`FM.fold` into a
    `PackageMap`) with the EXACT fold characterization (`package_summaries_find`) → `file_in_package`,
    `package_no_empty`, `package_summary_main_count` (count = sum), `package_summaries_empty`, and
    order-independence `package_summaries_Equal` (via `FileMapProps.fold_Equal`) + `_build_permutation`;
    refactored `AllPackagesOneMain`/`prog_ok`/`prog_ok_iff` onto it; `GoCompile_Equal`, `prog_ok_Equal`,
    `go_compile_class_Equal` + `_build_permutation` (accept/error class invariant under insertion order).
  - §9 rendering: `source_imports_nil` + a structural `render_imports` eliminator (renderer consumes the
    empty import field); `render_map_domain`, `render_map_binding` (exact bytes), `render_map_Equal`,
    `di_go_file_entries_Equal`, `di_transport_order_independent`; `Collections.filemap_elements_Equal`
    (extensionally-equal maps enumerate identically, via `OrdProperties.sort_equivlistA_eqlistA`).
  - §11 OCaml: `plugin/fido_sink.ml` keys desired outputs in a `Map.Make(String)` (rejecting a duplicate path
    before any effect; canonical path-sorted install order independent of transport order) and uses
    `Set.Make(String)` for stale-target + abandoned-temp membership (lists remain only for the rollback
    stacks); `plugin/g_fido.mlg` audit roots use `Names.GlobRef.Set`; new sink `dup`/`perm` fixtures.
  - §12: docs reconciled (CLAUDE/ARCHITECTURE/PROGRESS/dune synopsis/gate comments/Makefile/Dockerfile +
    a master-plan §3.3 correction banner); PAINFUL_LESSONS #14 added and lesson 3 de-praised of the carried NoDup.
  - Gate 398 → **427/427** surfaces (the new order-independence/exactness theorems all gated); whole-theory
    audit + self-tests A–E green with the `GlobRef.Set` collection.
- Final Codex result / repair SHAs: **FINAL Codex review GREEN, no repair** (task `task-mrpc...` createdAt
  2026-07-17T20:08:55Z — NON-STALE, ~2 min after the `39be07d` commit at 20:06:58Z): "ALLOW: C1A FINAL is
  GREEN; no blocking implementation defects or architectural conflicts found within the declared scope and
  threat model."
- Verification result (`make check`): **ROOT + FINAL — green on the working tree** (proof 427/427 + whole-tree
  e2e incl. sink dup/perm + generated byte-compare); re-run green after FINAL push.
- Push result: ROOT `75d24b2..cc39433` + repair `cc39433..cc7a4d7`; FINAL `cc7a4d7..39be07d` — all pushed to
  `main`, fast-forward.
- **C1A COMPLETE**: both barriers Codex-GREEN (ROOT `cc7a4d7` task `task-mrpb612l`, FINAL `39be07d`), pushed,
  Rob notified, loop stopped (cron `fd0d06b5`).  **⛔ C2 remains FORBIDDEN until Rob explicitly authorizes it.**
- Human disposition: **pending Rob's review** (Codex green at both barriers; loop stopped + Rob notified — do
  NOT begin C2).
