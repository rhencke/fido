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
