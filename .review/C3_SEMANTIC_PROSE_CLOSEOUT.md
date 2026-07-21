Claude Code directive:
C3 semantic-prose closeout after the blocked final-cleanup confirmation

Repository:
  rhencke/fido

Human override token:
  C3-semantic-prose-closeout-1

Current stopped state:
  The final-cleanup bounded confirmation returned BLOCKING.
  REVIEW_REQUEST is closed.
  Claude correctly stopped and did not repair autonomously.

Binding functional contract:
  .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md
  exact sha256:
    a13779c2e55c679e461e857d019eeae6adef27b0666876ed0cac92833814f212

Accepted review basis:
  .review/REVIEW_BASIS.md

This is a later explicit human authorization for:

  one prose-and-authority repair batch
  one final bounded Implementation Review confirmation

It does not authorize executable, semantic, proof, collection, gate, generated-byte, or C4 changes except where
this directive explicitly permits current comments or active review documents to be corrected.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

The current implementation is substantively complete.

The prior confirmation CLOSED:

- the fresh-build runner state machine and fault boundary;
- package-import-path injection;
- package-import-path determinism;
- the lower component authority;
- the 386/386 readable assumptions gate;
- zero-assumption and proof boundaries;
- fresh-image and publication architecture;
- manifest/checksum deletion;
- source-specification versus retained-production separation;
- generated-source byte identity;
- repository size reduction;
- no C4 scope creep.

Do not reopen any of those.

The remaining BLOCKING class is:

> Current permanent prose and active authority files contain malformed comments, obsolete phase names,
> dead file pointers, wrong theorem names, and a few materially false statements.

This is cosmetic in implementation effect, but false authority prose is still a milestone blocker.

No line number in this directive is normative.  Line numbers are only coordinates in the supplied snapshot and
will move during edits.

The task is not to update old line references or restore deleted checkpoint labels.

The task is:

- read every affected comment and active authority passage in context;
- rewrite it as concise, timeless, current prose;
- or delete it when the code is already clear.

Do not merely delete matched tokens.

===============================================================================
1. INSTALL THIS AUTHORITY
===============================================================================

Before editing:

1. Write this directive VERBATIM to:

     .review/C3_SEMANTIC_PROSE_CLOSEOUT.md

2. Update `.review/NEXT_STEPS.md` to identify:

     active checkpoint: C3
     functional contract path + exact hash above
     accepted review basis path
     current repair authority: .review/C3_SEMANTIC_PROSE_CLOSEOUT.md
     human override: C3-semantic-prose-closeout-1
     state: prose-only repair in progress
     C4: forbidden

3. Keep `.review/REVIEW_REQUEST.md` CLOSED during work:

     state: closed
     review: Implementation Review
     confirmation: yes
     confirmation_used: no
     human_override: C3-semantic-prose-closeout-1

4. Commit:

     review(contract): C3 — authorize semantic prose closeout

5. Once this directive and the compact status ledger preserve the current unresolved result, DELETE these
   superseded repair documents:

     .review/C3_WEEDWHACKER_DIRECTIVE.md
     .review/C3_FINAL_CLEANUP_DIRECTIVE.md

   Git history is their archive.

Do not delete:

  .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md
  .review/REVIEW_BASIS.md
  .review/CODEX_REVIEW_POLICY.md
  .review/SOURCE_FOREST_MASTER_PLAN.md

===============================================================================
2. HARD CHANGE BOUNDARY
===============================================================================

This batch is prose-only.

Allowed changes:

- comments in `.v`, `.ml`, `.mlg`, `.sh`, Dockerfile, Dune, and Makefile;
- Markdown and active `.review` authority files;
- deletion of the two superseded repair documents named above;
- compacting current review/status prose;
- current error-message prefixes only where they still falsely name a deleted public command, provided no
  control flow, type, protocol, or result changes.

Forbidden changes:

- Gallina definitions;
- theorem statements;
- proof bodies;
- OCaml control flow;
- shell control flow;
- Docker executable instructions;
- Dune module/package behavior;
- Make targets;
- gate `Print Assumptions` commands;
- collection representation;
- generated Go bytes;
- public capabilities;
- review policy semantics;
- functional contract requirements;
- any C4 work.

If a prose correction appears to require a code or theorem change, record an unexpected conflict and stop.

The readable gate must remain:

  386/386

The functional contract file must remain byte-identical and retain its exact hash:

  a13779c2e55c679e461e857d019eeae6adef27b0666876ed0cac92833814f212

Because the functional contract is frozen, do not edit its stale internal historical vocabulary or dead pointer.
Resolve its current authority through NEXT_STEPS and this directive instead.

===============================================================================
3. REVIEW METHOD — READ, DO NOT TOKEN-WHACK
===============================================================================

The repeated failure came from treating prose cleanup as a grep substitution task.

Use this process.

For each touched source or authority file:

1. Read the whole module header or surrounding comment block.
2. State privately what the code or authority actually does now.
3. Rewrite the comment in present tense.
4. Remove checkpoint chronology and repair history.
5. Read the rewritten paragraph again as English.
6. Inspect the full file diff, not only search hits.

After file-level edits:

- run a broad search for malformed markers and stale terms;
- inspect every hit in context;
- do not declare zero residue based only on one literal token list;
- perform a final sentence-level read-through of every changed comment and every active authority document.

A search result is a prompt to read.  It is not proof that the prose is correct.

===============================================================================
4. SOURCE MODULE COMMENT REPAIR
===============================================================================

Repair the current permanent comments in all root certified modules.

The following are known examples, not the complete set.

-------------------------------------------------------------------------------
4.1 Collections.v
-------------------------------------------------------------------------------

The module header contains the broken parenthetical:

  `( pinned-stdlib research + wrapper module.)`

Delete it or replace it with one concise complete sentence.

The header should state only:

- Fido uses mature pinned standard collections;
- this module instantiates thin wrappers and needed facts;
- Fido implements no general collection storage;
- performance claims remain honest.

Do not retain repair-history prose.

-------------------------------------------------------------------------------
4.2 Floats.v
-------------------------------------------------------------------------------

Fix the malformed comment opener:

  `(**: representability ...`

Use a normal Rocq documentation comment.

Read the surrounding paragraph so the sentence is complete.

-------------------------------------------------------------------------------
4.3 Complexes.v
-------------------------------------------------------------------------------

Replace historical headings:

  PART C
  PART D
  PART F

with semantic headings such as:

  complex type authority
  exact untyped complex constants
  runtime and typed complex values

Do not restore checkpoint part letters elsewhere.

-------------------------------------------------------------------------------
4.4 GoIndex.v
-------------------------------------------------------------------------------

Rewrite current comments containing campaign or future-work chronology, including phrases such as:

  reference layer that follows this milestone
  directive
  directive consequences
  navigation theorem set (directive)
  downstream indexed analysis

Use timeless descriptions of:

- total extraction for validated references;
- the structural index builder;
- exact navigation;
- the indexed traversal;
- downstream semantic elaboration.

The compiler phase is:

  elaboration

not:

  analysis

when referring to `GoCompile.elaborate`.

Generic mathematical use of “analysis” is not forbidden.

Also update any header or comment that still presents C2 as an active construction milestone.

-------------------------------------------------------------------------------
4.5 GoRender.v
-------------------------------------------------------------------------------

Rewrite repair-history phrases, including:

  the repair
  the milestone forbids
  ROOT correspondence
  Float cases are added in Part B
  ★ROOT

Describe current facts only:

- bare constants remain untyped;
- explicit conversions produce typed constants;
- the certified renderer uses independent denotation readers, not a general parser;
- rendered values correspond exactly to current semantic values.

Delete comments that only tell the history of how a bug was fixed.

-------------------------------------------------------------------------------
4.6 GoCompile.v
-------------------------------------------------------------------------------

Perform a complete comment read-through.

Known malformed or stale examples include:

  `(* / —`
  `(** / —`
  `index elaboration ()`
  `directive's exists form`
  unfinished text such as `are all defined at (`
  unfinished text such as `are defined at (`
  stale root/final chronology
  malformed section heads such as `/—`, `//—`, `(/)`, `**/—`
  `FRESOURCEFILE`
  current phase labels using ANALYSIS
  comments saying `successful analysis`

Required current vocabulary:

  SourceProgramValid
    source typing and package semantics

  semantic_ok_b
    readable source-specification decision

  semantic_diagnostics
    retained production report for source semantics

  FreshBuildPlan / fresh preflight
    cmd/go command condition

  GoCompile
    source semantics plus fresh preflight

  elaborate / ElaborationResult / ElaborationFacts
    the production semantic phase and result

  erased_report
    erased semantic report

  erased_elaboration_report
    erased full command-facing report

Do not say or imply:

  semantic_ok_b is exactly GoCompile
  erased_report emptiness is exactly full elaboration acceptance
  full command reports depend only on the file map
  current fixtures are part of a ROOT or FINAL campaign phase

Correct the typo:

  FRESOURCEFILE

to the actual constructor/type spelling:

  FRESourceFile

where the prose refers to that root-layout entry.

Replace damaged decorative section markers with plain semantic headings or delete them.

Do not change any definition, theorem, proof, or example.

-------------------------------------------------------------------------------
4.7 Other certified modules
-------------------------------------------------------------------------------

Read all remaining root `.v` module headers and comments for:

- broken punctuation caused by chronology deletion;
- stale C0/C1/C2/C3 part labels;
- “analysis” where the current compiler phase is elaboration;
- comments that describe deleted public `Fido Emit`;
- comments that point to deleted repair documents;
- comments that repeat obsolete exactly-one-main architecture.

Do not rewrite valid historical Go specification citations or useful semantic rationale.

===============================================================================
5. OPERATIONAL COMMENT REPAIR
===============================================================================

Read and correct comments in:

  Dockerfile
  Makefile
  dune-project
  plugin/g_fido.mlg
  plugin/fido_sink.ml
  e2e/fido_apply.ml
  e2e/sink_test.ml
  e2e/Witness*.v
  tools/*.sh
  plugin/dune
  e2e/dune

Known malformed examples include:

  `disposable copy — )`
  `#a DUPLICATE`
  `#PERMUTED`
  `§C0`
  empty parentheticals
  `(*:`
  `( attempts every temp)`
  `after removed`

Repair or delete the full sentence.

Required current responsibility prose:

Fido Materialize:

- the sole public Rocq transport/export command;
- checks type and assumption closure;
- decodes the certified DirectoryImage;
- writes a pristine export;
- does not publish into a dirty destination.

Fresh validation:

- happens in the supported Docker workflow;
- uses the pristine source artifact and a disposable copy;
- runs literal pinned `go build ./...`;
- does not publish the mutated build root.

Publication:

- the supported `make regenerate` workflow depends on successful validation;
- internal `fido_apply` reads fixed `/generated`;
- the sink performs filesystem synchronization only;
- deliberate local extraction or reconstruction of internal tools is outside the cooperating-developer threat
  model.

Do not claim:

  an image cannot possibly be sunk before validation

Do say:

  every supported public publication workflow validates before sink effects

The OCaml-origin gate description must accurately distinguish:

- certified materialization bridge;
- internal filesystem sink;
- sink test driver;
- fixed-source internal apply adapter.

`dune-project` must describe a:

  certified materialization plugin

not a:

  Fido Emit transport plugin

Any remaining user-facing error prefix:

  `fido emit:`

must become:

  `fido materialize:`

only where the message belongs to the current materialization command.

Do not alter error conditions or control flow.

===============================================================================
6. ROOT DOCUMENTS
===============================================================================

Give each document one job.

-------------------------------------------------------------------------------
6.1 ARCHITECTURE.md
-------------------------------------------------------------------------------

Keep current normative architecture only.

Correct:

- source semantics versus fresh-build preflight;
- semantic report versus full elaboration report;
- fresh validate-before-publish supported workflow;
- no checksum/manifest mechanism;
- no public `Fido Emit`;
- component authority for executable naming;
- current elaboration vocabulary.

Remove:

- repair chronology;
- deleted-review-plan references;
- dead “validation provenance” wording;
- duplicated workflow explanations already stated elsewhere.

Accurate ordinary proof provenance language may remain.

-------------------------------------------------------------------------------
6.2 CLAUDE.md
-------------------------------------------------------------------------------

Keep contributor rules and stable workflow constraints.

Remove the stale pointer:

  `.review/C3_WEEDWHACKER_DIRECTIVE.md` §0.3

Replace it with a short stable statement of the cooperating-developer threat model, or point to the permanent
architecture/review policy.

Remove checkpoint chronology such as:

  GoIndex.v (Source Forest C2)

Use module responsibility, not campaign era.

Do not turn CLAUDE.md into a second architecture document.

-------------------------------------------------------------------------------
6.3 PROGRESS.md
-------------------------------------------------------------------------------

Describe landed scope and the next blocked frontier.

Do not point the active campaign to the superseded:

  .review/C3_FINAL_CLEANUP_DIRECTIVE.md

Point readers through:

  .review/NEXT_STEPS.md
  .review/SOURCE_FOREST_STATUS.md

Update executable-name wording to name:

  ModulePath.mp_segments
  FilePath.dir_components
  package_import_components

not `ModulePath.split_slash` as the semantic authority.

Once the final confirmation is pending, say so accurately.  Do not describe C3 as accepted before GREEN.

-------------------------------------------------------------------------------
6.4 README.md
-------------------------------------------------------------------------------

Keep user-facing purpose and supported commands.

Ensure it names:

- `Fido Materialize`, not `Fido Emit`;
- `make regenerate` as the supported publication workflow;
- the fresh pinned build check;
- no unsupported direct-sink guarantee.

Avoid internal review chronology.

-------------------------------------------------------------------------------
6.5 PAINFUL_LESSONS.md
-------------------------------------------------------------------------------

Do not rewrite it wholesale.

Keep costly lessons that remain live risks.

Correct only wording that is now false, points to deleted machinery, or repeats detail better owned by
ARCHITECTURE.md.

Do not add another prose-cleanup lesson.

===============================================================================
7. ACTIVE .review AUTHORITY REPAIR
===============================================================================

-------------------------------------------------------------------------------
7.1 NEXT_STEPS.md
-------------------------------------------------------------------------------

Keep it short.

After the repair is complete but before confirmation, it should state:

- active checkpoint: C3 semantic-prose closeout;
- frozen functional contract path + exact hash;
- accepted review basis path;
- current directive path;
- human override token;
- candidate state;
- C4 forbidden.

Do not restate contract or review history.

-------------------------------------------------------------------------------
7.2 REVIEW_BASIS.md
-------------------------------------------------------------------------------

Remove the dead pointer:

  `MANUAL_C3_AUDIT.md`

That file does not exist.

The accepted findings are already recorded in the basis itself and in Git history.

Ensure the basis uses current names and no manifest-era evidence claims.

Do not expand it.

-------------------------------------------------------------------------------
7.3 SOURCE_FOREST_MASTER_PLAN.md
-------------------------------------------------------------------------------

This remains a live architectural plan and must use current permanent terms.

Make a focused semantic update, not a rewrite.

Replace stale current-direction vocabulary:

  CompilationFacts
    -> ElaborationFacts

  AnalysisResult
    -> ElaborationResult

  AnalysisOK
    -> ElaborationOK

  AnalysisFailed
    -> ElaborationFailed

  analyze
    -> elaborate

  one analysis root
    -> one elaboration root

  analysis snapshot
    -> elaboration snapshot

Update the active C3 section to describe:

- occurrence-anchored diagnostics;
- occurrence-keyed ElaborationFacts;
- one elaboration root;
- `go_compile` as a projection of `elaborate`;
- no typed AST;
- current Contract Review / Implementation Review process, not obsolete ROOT/FINAL review stages.

Delete or rewrite the old C3 root/final review subsections.  Do not keep a third review process in the master
plan.

Correct the determinism claim.

Source-only facts and semantic diagnostics:

  depend only on FilesEqual file maps

Full fresh-build plan and command-facing elaboration report:

  also depend on ModuleSpec
  require ProgramInputEqual or the current equivalent

Do not say all diagnostics depend only on GoFileMap.

This file may retain C0-C6 roadmap structure, but current architectural names must be correct.

-------------------------------------------------------------------------------
7.4 SOURCE_FOREST_STATUS.md
-------------------------------------------------------------------------------

The current file contains a detailed prose-failure diary, including the malformed tokens themselves.

Replace it with a compact status record:

- active checkpoint and functional contract;
- accepted review basis;
- current override;
- substantive implementation state;
- final prose batch candidate SHA;
- gate count;
- verification result;
- final confirmation result;
- human approval pending or granted;
- C4 status.

Do not preserve line-by-line confirmation chronology.  Git history is the archive.

Do not claim:

  zero stale/scar hits

until the final semantic read-through and confirmation are complete.

-------------------------------------------------------------------------------
7.5 REVIEW_REQUEST.md
-------------------------------------------------------------------------------

Keep machine fields and a short scope note only.

During repair:

  state: closed
  review: Implementation Review
  confirmation: yes
  confirmation_used: no
  human_override: C3-semantic-prose-closeout-1

At the barrier:

  state: requested
  confirmation_used: yes

After result:

  state: closed

Do not append a review diary.

-------------------------------------------------------------------------------
7.6 COLLECTION_AUDIT.md
-------------------------------------------------------------------------------

Repair the current diagnostic row.

It must refer to actual symbols:

  semantic_diagnostics
  semantic_diagnostics_node_strict
  semantic diagnostic node buckets
  main-redeclared diagnostics
  missing-main-entry package diagnostics

Do not cite the nonexistent:

  collect_diagnostics_node_strict

Do not describe a current symbol as `GoCompile.collect_diagnostics` if that symbol no longer exists.

Remove checkpoint-section archaeology such as:

  C3 §16/§17
  C3 §5/§10
  C3-fresh §7/§18-I
  §19/§26

Replace it with current collection roles and theorem names.

Read every table row for current symbol existence and current responsibility.

Do not expand the table.

-------------------------------------------------------------------------------
7.7 Frozen functional contract
-------------------------------------------------------------------------------

Do not edit:

  .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md

Its exact accepted hash must remain:

  a13779c2e55c679e461e857d019eeae6adef27b0666876ed0cac92833814f212

Its body contains historical terminology and a dead closeout pointer.  The frozen hash and accepted review basis
take priority; current authority is resolved by NEXT_STEPS and this directive.

Do not mutate the contract merely to clean prose.

===============================================================================
8. BROAD SEMANTIC READ-THROUGH
===============================================================================

The known list is not exhaustive.

Perform a final read-through of:

- every changed module header;
- every changed section comment;
- every current root document;
- every active `.review` authority document;
- every changed Docker/OCaml/shell comment.

Searches should include, but not be limited to:

  malformed comment openers and closers
  empty parentheses
  dangling slashes before em dashes
  checkpoint labels in permanent code
  references to deleted files
  references to nonexistent symbols
  old phase names
  Fido Emit
  validation provenance
  exactly-one-main as a primitive rule
  file-map-only claims about the full command result
  under implementation
  confirmation requested
  ACTIVE labels for completed checkpoints

Do not ban all occurrences mechanically.

Examples of valid context:

- a frozen historical contract may contain old terminology;
- generic type or constant analysis in GoTypes is ordinary English;
- a negative statement that there is no public Fido Emit may be accurate;
- proof provenance is a valid concept even though validation-provenance checksums were deleted.

The final test is whether a future author can read each current sentence and form the correct model.

===============================================================================
9. SIZE
===============================================================================

Supplied snapshot:

  whole repository: approximately 1,566,637 bytes
  readable gate: 386

This pass must remain net-negative.

Deleting the two superseded repair directives should remove more than 50 KB before adding this directive.

Required final result:

- whole repository smaller than the supplied snapshot;
- `.review` materially smaller;
- no new review diary;
- no replacement prose of equal size;
- frozen functional contract unchanged;
- gate exactly 386;
- generated source bytes unchanged.

Target:

  at least 30 KB net deletion from the supplied snapshot

Do not shorten useful semantic explanation merely to hit the target.  Most savings should come from deleting
superseded repair files, compacting status/request prose, and removing broken or repetitive comments.

Report before/after bytes for:

- root Rocq source;
- Docker/operational files;
- gate;
- root Markdown;
- `.review`;
- whole repository.

===============================================================================
10. VERIFICATION
===============================================================================

Because this is prose-only, add a mechanical change-boundary audit.

Before review:

1. Run:

     git diff --check
     make prove
     make e2e
     make check
     make regenerate
     make regen-guard
     staged pre-commit verification

2. Confirm:

     gate = 386/386
     whole-theory audit GREEN
     generated go.mod byte-identical
     all generated `.go` byte-identical
     no C4 work

3. Inspect the diff and prove:

     no Gallina definition changed
     no theorem statement changed
     no proof body changed
     no executable OCaml branch changed
     no shell/Docker executable instruction changed
     no gate command changed

4. Run a current-symbol audit for every theorem/symbol named in:

     ARCHITECTURE.md
     CLAUDE.md
     PROGRESS.md
     COLLECTION_AUDIT.md
     SOURCE_FOREST_MASTER_PLAN.md
     REVIEW_BASIS.md

5. Run a file-pointer audit for every `.review/*.md` path named in active authority files.

6. Perform the semantic sentence read-through after all scans pass.

Do not write “zero residue” into authority prose before this entire sequence succeeds.

Freeze one candidate SHA.

===============================================================================
11. ONE FINAL BOUNDED CONFIRMATION
===============================================================================

This override authorizes exactly one bounded Implementation Review confirmation.

Open REVIEW_REQUEST only after the candidate is frozen.

Use:

  state: requested
  review: Implementation Review
  confirmation: yes
  confirmation_used: yes
  human_override: C3-semantic-prose-closeout-1

Confirmation scope is strictly:

1. No executable, theorem, proof, gate, or generated-byte change.
2. Known malformed comments are repaired.
3. Current comments are coherent English when read in context.
4. Material semantic/workflow claims are exact.
5. Active authority files point to existing current authorities.
6. Active documents cite existing theorem and symbol names.
7. Master-plan vocabulary and determinism boundaries are current.
8. Collection audit names current symbols and roles.
9. Superseded repair documents are deleted.
10. Status/request files state the true current state.
11. Gate remains 386.
12. Repository remains smaller.
13. Direct repair-induced prose defects only.

The confirmation must not reopen:

- runner correctness;
- package-import proofs;
- component architecture;
- fresh-build semantics;
- publication architecture;
- source-specification/production split;
- collections;
- assumption-gate design;
- C4;
- previously confirmed code.

After confirmation:

GREEN:

- close REVIEW_REQUEST;
- update compact status;
- rerun any check affected by the review repair;
- fast-forward push;
- notify Rob;
- stop.

BLOCKING or ARCHITECTURAL CONFLICT:

- close REVIEW_REQUEST;
- record the complete result compactly;
- notify Rob;
- stop;
- do not repair or request another review without a later explicit human override.

===============================================================================
12. ACCEPTANCE
===============================================================================

This closeout is complete only when:

- no behavioral or proof code changed;
- the functional contract hash is unchanged;
- malformed comments are gone;
- no current authority points to a missing file;
- no current document cites a nonexistent theorem;
- `semantic_ok_b` is described as source-only;
- `erased_report` is described as semantic-only;
- full command determinism includes ModuleSpec;
- compiler-phase prose uses elaboration;
- current executable-name prose uses the component authority;
- materialization and sink responsibilities are exact;
- no stale public Fido Emit wording remains except accurate negative statements;
- collection audit uses current symbols;
- master plan uses current C3 architecture and review process;
- active status is compact and true;
- superseded repair directives are deleted;
- gate remains 386/386;
- all checks are green;
- generated source bytes are unchanged;
- repository is smaller than the supplied snapshot;
- one final bounded confirmation returns GREEN;
- C4 has not begun.
