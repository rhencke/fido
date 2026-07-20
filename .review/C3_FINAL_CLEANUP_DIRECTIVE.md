Claude Code directive:
C3 final bounded cleanup after the blocked weedwhacker confirmation

Repository:
  rhencke/fido

Human override token:
  C3-final-cleanup-1

Current frozen state:
  REVIEW_REQUEST is closed after the bounded Implementation Review confirmation returned BLOCKING.
  The supplied snapshot records the candidate range 714f930..627caf3 and the stopped state at 627caf3/b704025.

Binding functional contract:
  .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md
  sha256:
    a13779c2e55c679e461e857d019eeae6adef27b0666876ed0cac92833814f212

Accepted review basis:
  .review/REVIEW_BASIS.md

This directive is a later explicit human authorization.  It permits:

  one complete repair batch
  one final bounded Implementation Review confirmation

It does not reopen C3 architecture or authorize C4.

Before implementation:

1. Write this directive VERBATIM to:

     .review/C3_FINAL_CLEANUP_DIRECTIVE.md

2. Add a short supersession banner to:

     .review/C3_WEEDWHACKER_CONFIRMATION_FINDINGS.md

   stating that the unresolved findings are superseded by this human cleanup directive.

3. After the new directive is committed and the required findings are represented here and in the compact status
   ledger, delete `.review/C3_WEEDWHACKER_CONFIRMATION_FINDINGS.md`.  Git history is the review archive.

4. Update `.review/NEXT_STEPS.md` to point to this directive as the current repair authority.

5. Keep `.review/REVIEW_REQUEST.md` CLOSED during implementation.  Record:

     human_override: C3-final-cleanup-1
     confirmation_used: no

6. Commit the authorization before changing implementation:

     review(contract): C3 — authorize final bounded cleanup

Then repair every item below as one batch.

===============================================================================
0. SCOPE AND DISPOSITION
===============================================================================

Current disposition:

  BLOCKING

The remaining findings are finite:

1. The fresh-build runner can call a pre-Go failure a real Go run.
2. Two contract-required package-import proof claims are missing.
3. Several current authority and semantic comments are false.
4. Mechanical chronology deletion left malformed prose throughout the tracked tree.

No new architectural decision is needed.

Preserve every confirmed win:

- one raw AST;
- one retained index;
- one retained source visit;
- factored package semantics;
- independent readable source specification and retained production implementation;
- one production `elaborate`;
- shared fresh-plan and command-diagnostic builders;
- exact fresh-image cmd/go model;
- no manifest or checksum system;
- `Fido Materialize` as the sole public Rocq export;
- fixed `/generated` internal publication adapter;
- supported publication ordered through the Docker DAG;
- standard collections;
- readable gate currently 386/386;
- zero project assumptions;
- generated source bytes unchanged;
- more than 400 KB already removed;
- no C4 work.

Do not reopen:

- checksum or manifest provenance;
- deliberate-local-bypass resistance;
- forcing vm-computable fixtures through the retained index;
- physical module reorganization;
- platform path/resource limits;
- any C4 feature.

===============================================================================
1. FIX THE FRESH-BUILD RUNNER STATE MACHINE
===============================================================================

The current `fresh_go_build` runs:

  ( cd "$_fresh" && go build ./... )
  _rc=$?
  _FRESH_GO_RAN=1

That marks the command as run even when `cd` fails or the Go executable cannot launch.

A directory-collision judge may then accept the shell's own "can't cd ... directory" text as the expected Go
failure class.

Fix the function as a small explicit state machine.

Required entry state, set BEFORE every fallible operation:

  _FRESH_GO_RAN=0
  _FRESH_BUILD_LOG=
  caller output variable=""

The caller output variable must be cleared by the function, not merely by each caller.

Required result classes:

A. Infrastructure failure

Examples:

- mktemp failure;
- source copy failure;
- log creation failure;
- fresh root missing after copy;
- `cd` failure;
- `go` not found or not executable;
- command launch failure.

Required result:

  return reserved infrastructure status 125
  _FRESH_GO_RAN=0
  _FRESH_BUILD_LOG=
  caller output variable remains empty
  temporary root/log cleaned when they were created

B. Actual pinned Go invocation

Only after:

- the fresh root exists;
- changing to it succeeds;
- the pinned `go` executable is available;
- the shell successfully launches the fixed `go build ./...` command.

Required result:

  _FRESH_GO_RAN=1
  _FRESH_BUILD_LOG=<this invocation's fresh log>
  caller output variable=<this invocation's fresh root>
  return the actual Go status

Within the pinned fixed invocation, shell launch statuses 126/127 are infrastructure failures, not Go semantic
outcomes.

Exact implementation may vary.  Keep it small.  Do not rebuild the deleted general manifest runner.

Every negative judge must:

1. call `fresh_go_build`;
2. call `require_go_ran` before interpreting status or log text;
3. reject infrastructure status;
4. use only the current invocation's nonempty log;
5. check the expected diagnostic class.

Required fault tests:

1. setup/copy failure:
   - Go not run;
   - status 125;
   - no log;
   - no output root.

2. stale-result clearing:
   - a real rejected Go run produces a log;
   - the next infrastructure failure clears log, run flag, and output root.

3. post-copy/pre-Go root loss:
   - remove or invalidate the fresh root after copy but before `cd`;
   - status 125;
   - Go not run;
   - a directory-collision judge refuses to treat it as a Go rejection.

4. command unavailable/launch failure:
   - simulate unavailable or non-launchable `go`;
   - status 125;
   - Go not run;
   - no semantic judge accepts it.

The tests must exercise the actual helper used by every fixture.

Do not make expected Go stderr byte-exact.  Stable class checks remain correct.

===============================================================================
2. RESTORE THE MISSING PACKAGE-IMPORT PROOF BOUNDARY
===============================================================================

The component design is now correct and must remain:

  ModulePath.mp_segments
  FilePath.dir_components
  package_import_components =
      module components ++ package-directory components
  default_exec_name_c over components
  package_import_path as one String.concat bridge

Do not restore the deleted basename/dirname/string-scanning proof forest.

Restore the two missing universal claims.

A. Injective package-directory extension under one ModuleSpec

Required public theorem, or an exactly equivalent stronger theorem:

  package_import_path_inj :
    forall ms dir1 dir2,
      package_import_path ms dir1 = package_import_path ms dir2 ->
      dir1 = dir2

The proof must use the component authority.

A suitable proof route is:

- prove the slash split of the joined package import path recovers `package_import_components`;
- cancel the common `ModulePath.mp_segments` prefix;
- obtain equality of `FilePath.dir_components`;
- use `FilePath.dir_components_concat` to recover equality of directory keys.

Do not introduce local basename/dirname parsing.

B. Determinism under equal ModuleSpec and package key

Required public theorem, or equivalent:

  package_import_path_deterministic :
    forall ms1 ms2 dir1 dir2,
      ms1 = ms2 ->
      dir1 = dir2 ->
      package_import_path ms1 dir1 = package_import_path ms2 dir2

Keep `package_import_path_InputEqual` if it remains useful for full-program determinism, but it does not replace
the direct API claim.

Also provide the component-level exactness lemmas needed to keep these proofs short and reusable.  Do not create
a second component representation.

Gate both load-bearing claims.

The readable gate must remain EXACTLY:

  386/386

To make room:

- replace weaker or derived package-import gate entries where appropriate;
- remove two genuinely redundant, helper-only, fixture-only, superseded, or weaker surfaces;
- do not remove source/command soundness, completeness, provenance, ordering, or DirectoryImage bridge roots;
- do not weaken the whole-theory assumption audit.

Document the gate substitutions in the compact status entry.

===============================================================================
3. CORRECT CURRENT SEMANTIC AND WORKFLOW CLAIMS
===============================================================================

This is not a line-number update.  Rewrite the prose to describe the current permanent architecture, or delete
it when the code is self-explanatory.

Do not restore obsolete checkpoint numbers, directive section numbers, or old line references.

Correct these substantive claims.

-------------------------------------------------------------------------------
3.1 `semantic_ok_b`
-------------------------------------------------------------------------------

`semantic_ok_b` reflects the SOURCE half:

  SourceProgramValid

It is not exactly `GoCompile`.

`GoCompile` also requires fresh-build preflight.

Rewrite every current comment or document that says or implies:

  semantic_ok_b = GoCompile

Correct meaning:

  semantic_ok_b
    readable source-specification decision

  semantic diagnostics
    retained production realization of the same source semantics

  fresh build preflight
    separate command condition

  GoCompile
    source semantics plus fresh-build preflight

-------------------------------------------------------------------------------
3.2 `erased_report`
-------------------------------------------------------------------------------

`erased_report` maps:

  semantic_diagnostics

It is empty exactly when the SOURCE semantic report accepts.

It is not the full command-facing elaboration result.

The full report is:

  erased_elaboration_report

Correct names/comments so readers cannot confuse them.

Do not rename a sound public symbol merely for style unless the current name is materially misleading and every
call site is updated.  At minimum, make the distinction explicit and exact.

-------------------------------------------------------------------------------
3.3 Supported publication boundary
-------------------------------------------------------------------------------

Do not claim:

  an image cannot be sunk before validation

That is stronger than the accepted cooperating-developer threat model.

Correct claim:

- there is no public Rocq sink command;
- `Fido Materialize` exports a certified pristine image;
- the supported `make regenerate` Docker workflow runs fresh validation before its internal apply stage;
- internal sink/apply implementation details can be deliberately invoked or reconstructed by a local user, which
  is outside the threat model.

Keep legitimate proof provenance language for:

- typechecking the image;
- assumption-closure checking;
- DirectoryImage origin.

Delete the dead phrase:

  validation provenance

from current permanent prose.  A checksum does not prove build success, and no checksum system exists.

-------------------------------------------------------------------------------
3.4 Path-component authority
-------------------------------------------------------------------------------

Update prose that says executable naming uses:

  ModulePath.split_slash

The public lower authority is:

  ModulePath.mp_segments
  FilePath.dir_components
  package_import_components

`split_slash` may remain an internal constructor/proof helper in the path modules.  Do not describe it as the
compiler's semantic authority.

-------------------------------------------------------------------------------
3.5 OCaml boundary
-------------------------------------------------------------------------------

Correct `tools/ocaml-origin-gate.sh`.

The bridge:

  plugin/g_fido.mlg

does not call the dirty-directory sink.

It:

- typechecks the DirectoryImage transport;
- checks assumption closure;
- decodes the final transport;
- materializes a pristine export.

The internal sink is used by:

- sink tests;
- the fixed-source internal apply adapter.

Correct the allowlist description without adding a new policy layer.

-------------------------------------------------------------------------------
3.6 Materialization naming
-------------------------------------------------------------------------------

Update:

  dune-project

from "Fido Emit transport plugin" to a current description such as:

  certified materialization plugin

Update all `plugin/g_fido.mlg` error prefixes:

  fido emit:

to:

  fido materialize:

or one neutral current prefix where appropriate.

There is no public `Fido Emit` command.

-------------------------------------------------------------------------------
3.7 Compiler phase vocabulary
-------------------------------------------------------------------------------

Where comments refer to the current whole-program compiler phase or ElaborationOK, use:

  elaboration

not:

  analysis

Generic mathematical or local type analysis in `GoTypes` may keep the ordinary English word "analysis."

Update witness comments that say "successful analysis" when they mean successful elaboration.

===============================================================================
4. FULL TRACKED-TREE PROSE REPAIR
===============================================================================

The prior chronology deletion removed tokens without repairing sentences.

Perform one semantic read-through and cleanup of current tracked source and authority prose:

- root `.v` files;
- Dockerfile;
- Makefile;
- dune-project;
- plugin files;
- e2e files;
- tools;
- ARCHITECTURE.md;
- CLAUDE.md;
- PROGRESS.md;
- README.md;
- PAINFUL_LESSONS.md only where current wording is false or obsolete;
- `.review/NEXT_STEPS.md`;
- `.review/REVIEW_BASIS.md`;
- `.review/SOURCE_FOREST_STATUS.md`;
- `.review/REVIEW_REQUEST.md`;
- `.review/COLLECTION_AUDIT.md`;
- gate comments.

Historical contracts may retain their original contract text unless they are still active authority.  Do not
rewrite Git history.

Fix or delete every malformed fragment in the current files.

The current snapshot includes examples such as:

  C1/ —
  directive /
  at )
  /—
  //—
  (/)
  **/—
  (*:
  for ;
  #a DUPLICATE
  #PERMUTED
  §C0
  after removed
  ANALYSIS EXACTNESS
  ANALYSIS VARIABLE
  successful analysis

This list is not exhaustive.

Required method:

1. Search the full tracked tree for known malformed tokens and stale vocabulary.
2. Read each hit in context.
3. Rewrite the whole sentence as current timeless prose, or delete it.
4. Do not merely remove the matched token.
5. Run `git diff --check`.
6. Run a trailing-whitespace scan.
7. Run the stale-term scan again.

Suggested final zero-hit search over CURRENT source/docs/authority files, excluding historical frozen contracts
where the exact historical wording is part of the record:

  C1/ —
  directive /
  /—
  //—
  (/)
  **/—
  (*:
  for ;
  #a DUPLICATE
  #PERMUTED
  §C0
  after removed
  ANALYSIS EXACTNESS
  ANALYSIS VARIABLE
  successful analysis
  validation provenance
  Fido Emit transport plugin
  fido emit:
  under implementation
  confirmation is REQUESTED

Do not ban ordinary words globally.  Inspect context.

Retain useful:

- Go specification references;
- current theorem names;
- permanent invariants;
- concise rationale for non-obvious proofs and safety checks.

Delete:

- project checkpoint chronology from permanent implementation comments;
- dead review instructions;
- prose that only repeats nearby code;
- empty or damaged decorative headings;
- duplicated architecture summaries.

===============================================================================
5. REPAIR ACTIVE AUTHORITY STATE
===============================================================================

`.review/NEXT_STEPS.md` currently says the prior repair is under implementation.

Replace it with a short current pointer:

- active checkpoint C3;
- active functional contract path and full hash;
- current cleanup directive path;
- accepted review basis path and hash;
- human override `C3-final-cleanup-1`;
- current state during repair;
- C4 forbidden.

Do not restate the contract.

`.review/REVIEW_BASIS.md` still contains manifest-era evidence language.

Replace claims such as:

  fail-closed fresh runner with exact manifest and byte checks
  fail-open manifest observation

with the current no-manifest boundary:

- fail-closed fresh disposable copy and command-state classification;
- exact DirectoryImage/generated-layer bridge;
- supported Docker validate-before-publish ordering;
- no checksum or manifest substitute.

Do not broaden the threat model.

`.review/SOURCE_FOREST_STATUS.md` currently says the prior confirmation is requested.

Keep the ledger compact.

Record:

- prior final confirmation BLOCKING;
- this human override and its finite four-part repair;
- candidate SHA when frozen;
- gate count;
- verification result;
- final confirmation result.

Do not append a long turn-by-turn diary.  Git history is the detailed archive.

`.review/REVIEW_REQUEST.md` is currently several kilobytes of history.

During repair, reduce it to:

- machine fields;
- one short prior-result note;
- rules.

Use:

  state: closed
  review: Implementation Review
  confirmation: yes
  confirmation_used: no
  human_override: C3-final-cleanup-1

When the candidate is frozen, request the authorized confirmation with:

  state: requested
  review: Implementation Review
  confirmation: yes
  confirmation_used: yes
  human_override: C3-final-cleanup-1

After the result, close it.

Delete `.review/C3_WEEDWHACKER_CONFIRMATION_FINDINGS.md` after this directive and the compact ledger fully capture
the unresolved result.

Do not add a replacement review diary.

===============================================================================
6. SIZE AND MAINTAINABILITY
===============================================================================

Supplied-snapshot byte baseline:

  whole repository:          1,565,977
  root Rocq source:            980,629
  gate/axiom_gate.v:            46,253
  Dockerfile:                   83,567
  .review:                     229,700
  five root Markdown files:   109,976
  GoCompile.v:                441,816
  readable surfaces:              386

Correctness is the first requirement.

This cleanup must also remain net-negative after adding this directive.

Required:

- whole repository smaller than 1,565,977 tracked bytes;
- readable gate exactly 386;
- no new review diary;
- no replacement prose of comparable size;
- no restored string-proof forest;
- no new runner framework;
- generated source bytes unchanged.

Target:

  at least 15 KB further net deletion

The target is achieved through:

- deleting the superseded findings file;
- compacting REVIEW_REQUEST and status;
- deleting broken/redundant comments;
- replacing false prose with shorter exact prose;
- removing redundant gate surfaces to add the two required roots.

Do not minify Gallina, compress proofs into unreadable scripts, or delete useful invariants merely to meet a
number.

Report before/after bytes for:

- GoCompile.v;
- ModulePath.v + FilePath.v;
- all root Rocq source;
- gate;
- Dockerfile and operational code;
- `.review`;
- root prose;
- whole repository.

===============================================================================
7. VERIFICATION
===============================================================================

Before review, run all required checks from the exact candidate:

  make prove
  make e2e
  make check
  make regenerate
  make regen-guard
  staged pre-commit verification
  generated go.mod byte comparison
  recursive generated `.go` byte comparison
  `git diff --check`
  full tracked-tree stale/prose search

Required final evidence:

- readable gate 386/386;
- whole-theory assumption audit GREEN;
- adversarial audit self-tests GREEN;
- pinned Go matrix GREEN;
- fresh-runner fault tests GREEN;
- source bytes byte-identical;
- supported publication DAG GREEN;
- staged tree GREEN;
- no untracked generated/control/temp residue;
- no C4 work;
- before/after size table.

Freeze one candidate SHA only after every check is green.

Commit naming may use:

  review(final): C3 — close runner, proof-boundary, and prose findings

===============================================================================
8. ONE AUTHORIZED FINAL CONFIRMATION
===============================================================================

This human override authorizes exactly one bounded Implementation Review confirmation.

Open `.review/REVIEW_REQUEST.md` only after the candidate is complete and frozen.

Confirmation scope:

1. Fresh-runner infrastructure/Go classification is fail-closed.
2. `package_import_path_inj` and direct determinism claims exist, are component-based, and are gated.
3. The gate remains exactly 386 and all trust checks remain green.
4. The false semantic/workflow claims are corrected.
5. The tracked-tree malformed prose sweep is complete.
6. Active authority files report the true state.
7. Confirmed architecture and source bytes remain unchanged.
8. The final tree remains smaller than the supplied snapshot.
9. Direct repair-induced defects only.

The confirmation must not reopen:

- manifests or checksums;
- deliberate local-bypass resistance;
- fixture execution through the retained index;
- physical reorganization;
- C4;
- already confirmed fresh-build semantics.

After the confirmation:

GREEN:

- rerun the final required checks if the candidate changed during review;
- update the compact status ledger;
- close REVIEW_REQUEST;
- fast-forward push;
- notify Rob;
- stop.

BLOCKING or ARCHITECTURAL CONFLICT:

- close REVIEW_REQUEST;
- record the complete result compactly;
- notify Rob;
- stop;
- do not repair;
- do not request another review without a later explicit human override.

===============================================================================
9. ACCEPTANCE
===============================================================================

This cleanup is complete only when:

- infrastructure failures cannot masquerade as Go rejections;
- caller output state is cleared on entry and failure;
- post-copy/pre-Go and launch-failure tests pass;
- package import-path injection is proved;
- package import-path determinism is proved;
- both claims use the component root;
- no deleted character proof forest returns;
- gate is 386/386;
- `semantic_ok_b` is described only as source semantics;
- `erased_report` is described only as the semantic report;
- supported publication prose matches the cooperating-developer boundary;
- no dead validation-manifest vocabulary remains in current prose;
- current path-component authority is named correctly;
- OCaml materialization/sink responsibilities are accurate;
- no public Fido Emit wording or error prefix remains;
- compiler-phase prose uses elaboration;
- malformed mechanical-deletion scars are gone;
- active authority files report the true current state;
- superseded findings diary is deleted;
- all checks are green;
- generated source bytes are unchanged;
- final tree is smaller than the supplied snapshot;
- the one authorized confirmation is GREEN;
- C4 has not begun.
