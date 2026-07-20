> ⚠ SUPERSEDED — the unresolved findings recorded here are superseded by the human cleanup directive
> `.review/C3_FINAL_CLEANUP_DIRECTIVE.md` (`human_override: C3-final-cleanup-1`).  This diary is scheduled for
> deletion once the directive + the compact `SOURCE_FOREST_STATUS.md` ledger fully capture the result; git
> history is the review archive.

# C3 weedwhacker — bounded Implementation Review confirmation: BLOCKING

Codex task `task-mrtdwfu9-bs4li9`, frozen range `95258b0..2ba541e`, over the weedwhacker batch
(`9caa929` 1/2 + `2ba541e` 2/2).  Authorized by `human_override: C3-weedwhacker-human-decision`.

**Result: BLOCKING — 5 findings, all valid.**  Per the §14 HARD CAP (`.review/CODEX_REVIEW_POLICY.md`), this
blocking confirmation ENDS autonomous work: closed `REVIEW_REQUEST`, recorded here, Rob notified, STOPPED.
NO repair and NO re-request without a NEW explicit human_override token.  Codex confirmed no architectural
conflict — the amendment validly supersedes the earlier F1/F2 demand; the defects below are within-arch.

## Findings

1. **Repair-induced — the §8 lower path-component root was NOT actually implemented.**  `default_exec_name`
   (GoCompile.v:4784) still reparses strings via `ModulePath.split_slash`; package import paths remain string
   concatenations (GoCompile.v:4867); the char/slash split/join/cancellation/reconstruction scaffolding
   remains through GoCompile.v:5117; `default_exec_name_nonempty` (GoCompile.v:5122) still depends on that
   proof forest.  The only lower-layer addition is `split_slash_nonempty`/`split_slash_app`
   (ModulePath.v:100) — there is still NO canonical module/file component authority or component-based
   package-import construction.  GoCompile.v is 451,659 bytes, +2,620 vs the directive baseline, contrary to
   the required material reduction.  Required: a canonical lower-layer component representation + its
   nonempty/slash-free facts, compositional package-import construction, ONE string bridge, delete the
   superseded local proof forest.

2. **Repair-induced — the fresh negative-test runner can FAIL OPEN.**  The runner (Dockerfile:~619) does not
   reset its output root / `_FRESH_BUILD_LOG` before fallible ops; an infrastructure failure returns status 2,
   indistinguishable from an expected Go rejection, leaving the previous case's log.  `rej_conv`
   (Dockerfile:~702) and `expect_reject` (Dockerfile:~773) accept ANY nonzero status then grep a possibly-stale
   log, so a failed setup after a similarly-classified rejection can pass without running the current Go case.
   Affects all negative conversion + matrix cases (collision, redeclaration, missing-import, package-conflict).
   Required: reset per-case state before fallible setup; distinguish runner-infra failure from a Go rejection;
   require a current-run log before accepting a negative case.

3. **Repair-induced — the readable gate exceeds the explicit ≤386 cap.**  `gate/axiom_gate.v` has 387 `Print
   Assumptions` entries (added 2 direct-rule surfaces at :331, removed only 1).  The dynamic count check accepts
   the new total and does not enforce the fixed cap.  Required: keep the load-bearing F1 exactness surfaces,
   remove one genuinely-redundant readable surface, count ≤386.

4. **Repair-induced — F5 reconciliation + the mandated source weedwhack are INCOMPLETE.**  Obsolete review
   chronology remains: `C3`/`C3-FRESH`/`C3-CR2-D4`/`F1` comments (GoCompile.v:4861/5011/5994), F2 chronology in
   witnesses (e2e/Witness.v:126), F2-era wording + a deleted "byte-gated sink" (plugin/g_fido.mlg:166).
   Contradictory authority prose: GoCompile.v:1579 calls `semantic_ok_b` the elaboration-native decision though
   production elaboration decides from RETAINED diagnostics (obscures the spec/production split);
   tools/ocaml-origin-gate.sh:10 describes an obsolete `Fido Emit` boundary + wrongly says the bridge invokes
   the sink; plugin/dune:12 says the apply CLI itself checks a marker (the ordering is the Docker DAG); some
   workflow docs still use prohibited manifest-era "attestation"/"validation provenance" language.
   `.review/NEXT_STEPS.md:6` omits the basis hash + amendment commit, has duplicate prose beyond the compact
   pointer, and still describes the frozen candidate as being implemented.  `git diff --check` reports trailing
   whitespace at GoCompile.v:5785.  Required: describe permanent runtime/proof roles without chronology;
   distinguish specification predicates from retained production diagnostics; correct the materialization +
   Docker-DAG descriptions; remove manifest-era terminology; restore the exact compact NEXT_STEPS pointer.

5. **Previously observable and missed by the initial review — the basis records the wrong contract hash.**
   `.review/REVIEW_BASIS.md:6` records contract SHA-256 `da376212…`, but the binding contract's actual content
   SHA-256 (now and at activation `83c3989`) is `a13779c2e55c…`.  Not an architectural conflict (contract
   identifiable via path + activation commit), but an invalid exact-authority claim; its omission makes the
   initial review incomplete.  Required: correct or explicitly reaccept the basis metadata.

## Closed / not-charged (Codex)

F1 spec/production split functionally present; shared fresh-plan + diagnostic construction exists; both
manifests + hash machinery removed; public path is `Fido Materialize` (the helper builds its own generated copy,
takes only the destination arg); whole repo shrank ~460 KB (satisfies the reduction requirement); NO C4
syntax/semantics/new-AST/type/manifest-replacement/collection-expansion.  Docker verification could not be
independently rerun in the review environment (no Docker socket) — not charged as a defect.

## Repair (human_override: C3-weedwhacker-repair-1) — candidate `627caf3`

All five findings repaired as ONE batch; make prove + e2e + check GREEN (pre-commit hook re-verified the staged
state), generated bytes byte-identical, gate 386 axiom-free, whole-theory audit + self-tests A-E pass.

1. **CLOSED — real lower path-component authority.**  `ModulePath.mp_segments` (+ nonempty/single-component/
   join-inverse facts) and `FilePath.dir_components` (+ `parent_dir_components_nonempty` + split/join/single
   facts) are the lower-layer authorities.  `GoCompile.package_import_components := mp_segments ++ dir_components`
   is composed; `default_exec_name` is computed DIRECTLY over those components (no build-then-reparse);
   `package_import_path` is the ONE string bridge (their "/"-join).  Deleted the local char/slash scan +
   split/join/reconstruction forest.  GoCompile.v 451,659 → 441,816 (−9,843; −7,223 below the directive
   baseline); no generated-byte change.
2. **CLOSED — negative Go differentials fail-closed.**  `fresh_go_build` resets outputs on entry, returns
   sentinel 125 with `_FRESH_GO_RAN=0` + empty log on a setup/infra failure, and sets the flag + this-run's log
   only after `go build` runs.  Every judge calls `require_go_ran`; rejections require a NON-EMPTY current-run
   log.  Fault self-tests added (setup/command-not-run distinguished; stale-output cleared).
3. **CLOSED — gate ≤386.**  Dropped the superseded `pkg_diags_empty_iff` gate line (kept as an internal lemma,
   audited); the direct-factored-root `pkg_diags_empty_iff_rules` stays gated.  Count = 386.
4. **CLOSED — chronology + prose.**  All checkpoint/finding/§-section chronology stripped from tracked
   code/ops COMMENTS (code untouched); `semantic_ok_b` re-described (a decidable specification/decision boolean
   proved = GoCompile; production elaboration decides from RETAINED diagnostics); g_fido/plugin-dune/ocaml-gate/
   Dockerfile wording corrected; trailing whitespace fixed; NEXT_STEPS made a compact pointer with the basis
   hash + amendment commit + accurate state.
5. **CLOSED — basis hash.**  `REVIEW_BASIS.md` records the actual contract sha256 `a13779c2e55c…`; active
   authority pointers audited.

## Repair-1 bounded confirmation (Codex `task-mrths3jz`, range `714f930..627caf3`): BLOCKING

Authorized by `human_override: C3-weedwhacker-repair-1`.  Codex confirmed NO architectural conflict.  Disposition
of the five prior findings: #3 (gate 386) CLOSED, #5 (basis hash) CLOSED+verified; #1 (component root) structural
but a repair-induced proof regression blocks; #2 (fail-open runner) NOT closed; #4 (chronology/prose) NOT closed.
**Result: BLOCKING — 4 findings, all valid.**  Per the §14 HARD CAP this ENDS autonomous work: closed
REVIEW_REQUEST, recorded here, Rob notified, STOPPED.  NO repair / re-request without a NEW explicit human_override.

1. **Repair-induced — Trust/fail-open defect (runner STILL can fail open).**  `fresh_go_build` (Dockerfile:620)
   resets `_FRESH_GO_RAN`/`_FRESH_BUILD_LOG` but NOT the caller output var (e.g. `FR`) — a setup failure leaves
   the prior root value.  More importantly (Dockerfile:626-628) it runs `( cd "$_fresh" && go build ./... )`
   then UNCONDITIONALLY sets `_FRESH_GO_RAN=1`: a failed `cd` / exec / pre-Go failure is classified as a Go run.
   Concretely dangerous for the collision cases — `expect_reject` accepts a `directory` regex, and a shell `cd`
   "No such file or directory" gives a nonempty current log that satisfies that class.  The fault tests exercise
   only the earlier `cp` failure, not stale output-root state or a post-copy/pre-Go failure.  Required: reset
   every published output on entry; make the run marker distinguish successful ENTRY into the fresh root AND
   actual Go execution from all runner failures; add a fault test for that boundary; all negative judges reject
   infrastructure results.
2. **Repair-induced — Proof/evidence gap (deleted binding claims).**  The contract
   (C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md:814) REQUIRES package-import INJECTIVITY and DETERMINISM under equal
   ModuleSpec + package key.  The repair DELETED `package_import_path_inj` and `package_import_path_deterministic`
   (thinking them unused); the component impl (GoCompile.v:4864) retains only root/nested/nonempty facts;
   `package_import_path_InputEqual` is NOT an injectivity replacement.  Required: restore injectivity +
   determinism over the composed component representation, WITHOUT restoring the string-reparse forest.
3. **Repair-induced — Documentation contradiction/stale residue (finding-4 not closed).**  NEXT_STEPS.md:18 still
   says the frozen repair is "under implementation" (contradicts the request + ledger); GoCompile.v:1579 claims
   `semantic_ok_b` is EXACTLY `GoCompile` though it proves only the SOURCE half (excludes the fresh-build
   preflight); PROGRESS.md:45 still describes the OLD `default_exec_name_c` over `ModulePath.split_slash`;
   mechanical token deletion left malformed/scarred comments at GoCompile.v:111,1574-1575,1595,1972,2631,3186,
   3293,4132,5434,5606,6612,6640,6821; Dockerfile:677; Floats.v:536; gate/axiom_gate.v:440;
   plugin/fido_sink.ml:52,464; e2e/sink_test.ml:75; e2e/WitnessNeg.v:2; plugin/g_fido.mlg:166.  Required:
   reconcile these SEMANTICALLY with permanent current-role prose, not mechanical token removal.
4. **Previously observable + missed by the prior confirmation — stale residue (blast radius incomplete).**
   Dockerfile:776 still has a `§C0` comment; the directive-PROHIBITED "validation provenance" language remains
   in ARCHITECTURE.md:305,491 / CLAUDE.md:78 / PROGRESS.md:64; g_fido.mlg:169-170 keeps the unqualified,
   threat-model-incompatible claim an image "cannot be sunk before it is validated"; materialize failures still
   use the old `fido emit:` prefix (g_fido.mlg:25-94) and dune-project:6,11 still advertises the "Fido Emit
   transport plugin".  These existed before the repair and should have been in the prior review's blast radius.

Codex CLOSED/preserved: F1 composition (mp_segments+dir_components, forest deleted), spec/production split
(production elaborate_indexed does not call source_spec_*), both manifests deleted (no checksum/self-attestation),
`Fido Materialize` the sole Rocq export, sync depends on go-e2e + copies pristine bytes, go.mod/main.go
byte-identical to 95258b0, repo −450,325 below baseline, GoCompile.v −7,223 below its baseline, gate 386, no C4.
Dockerfile 83,567 (over the 80,000 target but −22 KB below the 105,802 baseline) — treated NONBLOCKING.
