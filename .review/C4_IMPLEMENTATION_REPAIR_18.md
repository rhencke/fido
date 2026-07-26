# C4 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 18

## Authority and use

Rob is the final human authority. Rob's delivery of this file to Claude Code records the C4 review disposition below and authorizes only the repair stated here.

Human implementation authorization token:

```text
C4-returned-cause-human-index-coherence-repair-18
```

This file is the complete Claude-facing directive for this review. Implement it exactly. Do not substitute a nearby result, weaken a contract, preserve an old path for convenience, or treat green commands as acceptance.

If implementation evidence conflicts with an accepted FCB contract, fixed point, ADR, gate, or this directive, stop at that boundary and report:

- the exact conflicting text;
- the exact code or proof evidence;
- why both cannot hold;
- the smallest proposed amendment;
- the work that remains blocked pending Rob's decision.

Do not work around a governing conflict.

## Exact review basis

Review basis:

- uploaded archive: `fido-main - 2026-07-26T152946.676.zip`;
- archive SHA-256: `5e2c00ff858fc715f3c250f81d33c75c715fd6f6f7a0d07ced90a9698519339f`;
- documentation-only freeze represented by the archive: `e15232d3ef894c2f478e36c736cd701533e224fe`;
- exact implementation candidate frozen by that commit: `92fc04e264b56d575e2fd1d65ae5d7940c93dc84`;
- repository: `rhencke/fido`;
- live FCB root: `.review/fcb/current/` at that exact ref;
- active checkpoint authority read from that ref: `.review/NEXT_STEPS.md`;
- open questions read from that ref: `.review/OPEN_QUESTIONS.md`.

The archive has no `.git` directory. The candidate and freeze identities above were resolved against Git. Do not treat the archive file name or modification times as identity.

Candidate `92fc04e264b56d575e2fd1d65ae5d7940c93dc84` is **BLOCKING**. It is the nineteenth blocked C4 implementation candidate. Freeze `e15232d3ef894c2f478e36c736cd701533e224fe` is documentation only and is not a separate candidate.

C4 is not accepted. C5, checkpoint-definition Step 0, post-C4 features, broad source cleanup, and proof-module partitioning remain forbidden.

C4 repair 18 is the sole next implementation task.

Implement on the current `main` head only after confirming that it is either the exact freeze above or a documentation-only descendant which names that exact candidate. Do not reset, rebase, rewrite history, force-push, or discard accepted A001 through A006 work. If an intervening commit changes Rocq, OCaml, gates, generated artifacts, or another live execution path, stop and report the new functional review basis before editing.

---

# Review disposition

Repair 17 made substantial real progress. Preserve all of it:

- the A006 authority commit landed before implementation;
- `Emit.Mint.Token` is opaque and indexed by the exact `Safe.Program`, exact `go.mod` bytes, and exact `.go` file map;
- `Emit.Mint.issue` is the sole authority-producing operation;
- `Emit.Image` remains a reducible transport carrier whose pack constructor is not a mint;
- the old raw `Emit.MakeImage` path is deleted;
- `Safe.Program` is now abstract and `Safe.certify` is its one production mint;
- `Compilable.Core`, `Compilable.Program`, `Compilable.Failure`, and `Compilable.Facts` remain sealed;
- the legacy collapsed result peer and its support closure are deleted;
- the naming gate now parses record fields before judging their case and fails closed on selected-file read or decode errors;
- the detailed conversion and failure fixtures were generalized from hard-coded builder calls to arbitrary retained `Input` and `Phase` objects;
- generated `go.mod` and `main.go` remain byte-identical to the reviewed baseline;
- the host `linux/amd64`, `GOAMD64=v1`, `CGO_ENABLED=0` Go build and reviewed-output comparison passed in this review environment.

This is not churn. The architecture is materially better.

The candidate remains blocked for three classes of defect:

1. the public returned-object fixture topology still does not state the full repair-17 guarantee over one exact returned accepted object and one exact returned rejected object;
2. accepted Governance D-07 is still unimplemented even though the live Human Review Index says its generator is due before the next accepted checkpoint;
3. the live FCB and current project documents still contradict one another, contain dangling operational paths, and overclaim that the corpus states one truth.

No new FCB amendment is required. Repair 18 implements and enforces accepted A001 through A006, Governance D-07, D-22 through D-26, and the already accepted repair-17 contract. If Claude concludes one of those must change, stop and request a reviewer-authored amendment.

---

# Blocking finding 1 — the returned-object theorem statements still understate and split the accepted guarantee

## The defect

Repair 17 did the right first step: it restated seventeen causal declarations and two bundles over arbitrary retained `Input` and `Phase` objects, then instantiated them at values projected from returned capabilities and failures.

The final public theorem topology still does not match the repair contract.

The repair-17 definition of done requires:

```text
5. the accepted direct fixture exposes the full retained forest, index, outcomes, trace, four causes, facts,
   package object, layout, plan, raw/final diagnostics, Safe retention, and Emit consumption through the
   returned cp.

6. the rejected direct fixture exposes the full retained forest, index, outcomes, trace, conversion and child
   causes, predecessor outcome, annotation context, singleton reason, package object, layout, plan, and
   raw/final diagnostics through the returned fail.
```

The candidate instead spreads the accepted evidence across independent existential theorems:

- `Compilable.deep_nested_capability_retains_elaboration` binds one existential `cp`;
- `Compilable.deep_nested_capability_retains_causes` binds another existential `cp`;
- `Emit.accepted_path_emits_from_returned_capability` binds another existential `cp` and safety result;
- the equal-value/distinct-occurrence theorem binds another capability.

Those theorems may all be true of the deterministic result of `compile`, but the public theorem statements do not retain one exact returned `cp` across the whole accepted guarantee. A reader cannot destruct one theorem and obtain the complete C4 accepted witness required by the contract.

The rejected evidence is likewise split between:

- `Compilable.deep_fail_capability_retains_rejected_causes`;
- `Compilable.deep_fail_capability_retains_rejected_elaboration`;
- helper claims over the retained phase.

No one theorem exposes the complete rejected guarantee through one exact returned `fail`.

## The cause objects are still weakened in the public statement

`nested_success_bundle` existentially returns:

- a work member;
- a suffix list;
- an accumulator for that suffix;
- a `ConversionStep`;
- operand and current facts.

Its proof obtains those values from `retained_convsuccess_closure` over `phase_ot ph`, but its statement does not retain or name the exact `RetainedMemberCause` projected by `total_forest_outcome_cause` from the exact `Outcomes.outcomes_trace` object. It restates selected consequences of the retained cause.

That is not the same public guarantee as:

- this exact work member's cause is the cause projected from this exact retained trace;
- this exact suffix split is the one retained in that cause;
- this exact prior accumulator is the authenticated predecessor retained by that cause;
- this exact `StepCause` reads the operand through the exact retained suffix membership;
- this exact tail-to-final preservation is the one carried by that cause.

Do not create another cause record to fix this. `RetainedMemberCause` already owns the fact. The public fixture must expose or pattern-match the exact existing cause object.

## The index and outcome claims are still local rather than whole-object claims

`nested_index_bundle` proves selected key lookups for the four conversion operands. It does not itself state the full two-way exactness of the retained `WorkIndex` over all retained work items.

The accepted returned-object theorem names `phase_ot` through point queries, but it does not expose the exact retained `Outcomes` object and its exact `outcomes_trace` as part of the one aggregate accepted result.

The rejected aggregate cause theorem states:

- phase diagnostics are nonempty;
- the phase diagnostic list has length one;
- the innermost failure and outer child-failure claims hold.

It does not state through the one returned `fail`:

- the exact retained raw diagnostic list;
- the exact retained final diagnostic list;
- the exact singleton `InvalidConversion` reason and exact diagnostic code in both required projections;
- the exact retained work index and its two-way domain;
- the exact retained `Outcomes` and `Trace` objects;
- each exact `RetainedMemberCause` object.

`deep_fail_capability_retains_rejected_elaboration` proves only `failure_diagnostics fail <> nil`, not the exact singleton final diagnostic required by the contract.

## The freeze overclaims the theorem surface

The freeze text says the direct returned-object fixtures carry:

- the outcome table and trace;
- the work index exact both ways;
- all exact causal history;
- exact raw and final diagnostics;
- safety retention and emission.

That is stronger than any one public theorem statement in the candidate. The fact that the proofs use retained objects internally does not repair a theorem statement which omits the accepted guarantee.

Green proofs cannot upgrade a weaker theorem statement.

## Required root repair

Create one accepted root proposition or record indexed by one exact returned capability. It must not mint a new authority. It is a proof view over the existing capability.

A suitable shape is equivalent to:

```coq
Record AcceptedFixture (cp : Compilable.Program) : Prop := {
  accepted_fixture_source : Compilable.source cp = deep_nested_program;

  accepted_fixture_input : ...;
  accepted_fixture_phase : ...;
  accepted_fixture_forest : ...;
  accepted_fixture_index_exact : ...;
  accepted_fixture_outcomes : ...;
  accepted_fixture_trace : ...;

  accepted_fixture_int8_cause :
    exact retained cause projected from the retained trace;
  accepted_fixture_int16_cause :
    exact retained cause projected from the retained trace;
  accepted_fixture_int32_cause :
    exact retained cause projected from the retained trace;
  accepted_fixture_int64_cause :
    exact retained cause projected from the retained trace;

  accepted_fixture_expression_facts : ...;
  accepted_fixture_type_name_facts : ...;
  accepted_fixture_package_refs : ...;
  accepted_fixture_layout : ...;
  accepted_fixture_plan : ...;
  accepted_fixture_raw_diagnostics : core_raw_diagnostics (core cp) = nil;
  accepted_fixture_final_diagnostics : core_diagnostics (core cp) = nil;
  accepted_fixture_distinct_occurrences : ...
}.
```

The exact Rocq record form may differ, but the ownership may not. Use the most basic existing retained object for each field. Do not copy facts into a peer authority.

Then prove one root theorem equivalent to:

```coq
Theorem deep_nested_compile_fixture :
  exists cp Hcp,
    Compilable.compile deep_nested_program = Compilable.Compiled cp Hcp
    /\ AcceptedFixture cp
    /\ Safe.certify cp retains that exact cp and core
    /\ Emit.of_safe (Safe.certify cp) consumes that exact accepted path.
```

Because `Emit` depends on `Safe` and `Compilable`, the final end-to-end theorem may live in `Emit.v`. If a lower module cannot name later layers, use this dependency-respecting split:

1. `Compilable` defines `AcceptedFixture cp` and proves it for the exact `cp` returned by one compile branch.
2. `Emit` proves one final theorem which destructs that exact Compilable theorem once, retains the same `cp`, certifies that `cp`, emits from that safety value, and carries `AcceptedFixture cp` unchanged.

Do not prove the final statement by independently invoking `compile_complete` again in `Emit` and then claiming it is the same witness. Pass the exact existential witness and its proof object through the theorem application.

## Exact accepted cause requirement

For each of the four conversion occurrences, the accepted fixture must expose the exact existing cause object projected from the exact retained trace.

Use a statement equivalent to:

```coq
let ph := phase (core cp) in
let wm := exact retained member for the source occurrence in ...
let cause := total_forest_outcome_cause (phase_ot ph) wm in
accepted_conversion_cause cause exact_source_ts exact_source_x ...
```

The statement must tie the cause to:

- `phase_ot ph`;
- `outcomes_trace (phase_ot ph)`;
- the exact work member at the exact source occurrence;
- the exact suffix split retained in `cause`;
- the exact prior accumulator retained in `cause`;
- the exact `ConversionStep` retained in `cause`;
- the exact operand `SuffixMember` retained in that step;
- the exact prior operand outcome;
- the exact tail-to-final preservation proof;
- the one `Typing.convert_constant` result;
- the exact current `ExpressionFact`.

A helper predicate may destruct the existing sigma and state these projections. It may not independently existentially choose a foreign suffix or accumulator which merely satisfies equal equations.

## Exact accepted index and outcomes requirement

The one accepted fixture must name:

- `phase_work (phase (core cp))` as the exact retained forest;
- `forest_index` of that forest as the exact retained standard index;
- the existing global two-way index exactness theorem or record field over every retained member and every present key;
- `phase_ot (phase (core cp))` as the exact retained outcomes object;
- `outcomes_trace` of that exact object as the exact retained causal trace;
- the exact outcome-domain theorem over the complete forest, not only four selected lookups.

Selected lookup fixtures may remain only when they test a distinct property not implied by the root exactness theorem. Delete any peer whose only purpose is to repeat a projection already carried by the accepted root fixture.

## Required rejected root

Create one rejected root proposition or record indexed by one exact returned failure. A suitable shape is equivalent to:

```coq
Record RejectedFixture (fail : Compilable.Failure deep_fail_program) : Prop := {
  rejected_fixture_core : ...;
  rejected_fixture_input : ...;
  rejected_fixture_phase : ...;
  rejected_fixture_forest : ...;
  rejected_fixture_index_exact : ...;
  rejected_fixture_outcomes : ...;
  rejected_fixture_trace : ...;

  rejected_fixture_innermost_cause :
    exact retained cause projected from the retained trace;
  rejected_fixture_outer_causes :
    each exact retained child-failure cause;
  rejected_fixture_predecessor :
    exact retained predecessor operand outcome and preservation;
  rejected_fixture_annotation :
    exact retained annotation context;

  rejected_fixture_package_refs : ...;
  rejected_fixture_layout : ...;
  rejected_fixture_plan : ...;
  rejected_fixture_raw_diagnostics :
    failure_raw_diagnostics fail = [exact InvalidConversion reason];
  rejected_fixture_final_diagnostics :
    failure_diagnostics fail = [exact command-ordered InvalidConversion reason];
  rejected_fixture_rejected : failure_diagnostics fail <> nil
}.
```

Then prove one root theorem equivalent to:

```coq
Theorem deep_fail_compile_fixture :
  exists fail,
    Compilable.compile deep_fail_program = Compilable.Rejected fail
    /\ RejectedFixture fail.
```

The exact singleton reason must include the exact diagnostic code and exact retained source reference required by the current diagnostic type. Do not weaken it to `length = 1`, `<> nil`, `exists reason`, or a source recomputation.

## Builder prohibition

After the exact `cp` or `fail` is obtained, neither root fixture statement nor proof may use these to recover its evidence:

```text
build_elaboration_core
build_compilation_input
build_expression_phase
Index.index_program
elaborate
program_visit
program_package_refs
any source fact-table builder
```

It may use general theorems whose statements are over the retained object itself. Search both theorem statements and proof bodies.

## Gate requirement

Gate the final aggregate accepted and rejected theorem surfaces directly.

The readable gate must not describe a group of separate helper theorems as though they establish one returned-object guarantee. Its comments must match the exact theorem statement.

Add a machine-checkable claim-to-theorem inventory, described under the closure audit below, so future freeze prose cannot claim more than the gated public statement.

---

# Blocking finding 2 — Governance D-07 is accepted, due, and still not implemented

## Governing contract

Governance D-07 states:

> Open human acts are generated from canonical rows and statuses, not hand-copied.

The current `FIDO_FCB_HUMAN_REVIEW_INDEX.md` explicitly says:

- it is temporarily hand-maintained;
- the current file does not satisfy D-07;
- the surviving generator is only a historical terminal-bundle stub;
- the living-FCB generator is due before the next accepted checkpoint;
- D-07 is not weakened.

C4 would be the next accepted checkpoint. Therefore C4 cannot be accepted while that disclaimer remains true.

The previous instruction that this task was “deferred nonblocking” governed repair-17 implementation scope. It does not grant an exception to the acceptance condition written in the live FCB.

Do not amend or soften D-07. Implement it.

## Single authority for open human acts

Add this canonical live file:

```text
.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv
```

It is the one current data authority for the list of open human acts. The generated Markdown Human Review Index is a view of this file plus validated source anchors. No other current file hand-copies the full list.

Use this exact header:

```text
id	status	required_human_act	source_path	source_anchor	source_owner	effect
```

Use one row for each current open human act. At repair-18 installation the rows are:

```text
C4-REVIEW
ADR-0002
ADR-0004
TOOLCHAIN-PROVENANCE
FIXED-POINT-EXTERNAL-EVIDENCE
FCB-SHOWROOM
```

Do not hard-code those IDs in the generator. They are data rows.

A closed act is removed from the live TSV. Git history and the owning ADR, governance row, fixed-point record, or accepted review commit preserve the disposition. Do not add a second closed-history table to the generated index.

## Source anchors

Each row names one owning source file and one exact anchor token.

Place exactly one anchor of this form in that owning source:

```text
<!-- FIDO-HUMAN-ACT:<ID> -->
```

Examples:

```text
<!-- FIDO-HUMAN-ACT:C4-REVIEW -->
<!-- FIDO-HUMAN-ACT:ADR-0002 -->
```

The generator must verify:

- `source_path` is a relative path inside the exported repository root;
- it contains no `..` traversal;
- it resolves to a regular file in the exported tree;
- it is not a symlink;
- it is readable UTF-8;
- the exact named anchor occurs once and only once;
- the row's `source_owner` is nonempty;
- the row's `effect` is nonempty.

The anchor validates ownership and discoverability. It is not a second status field. The TSV owns the current status and current human act text.

## Generator

Add one current generator/checker, for example:

```text
tools/human-review-index.py
```

Required modes:

```text
python3 tools/human-review-index.py --root . --write
python3 tools/human-review-index.py --root . --check
```

The exact name may differ only if a current tool namespace requires it. There must be one implementation, not a write script plus a separate checker with copied logic.

The tool must:

1. read the TSV as UTF-8;
2. require the exact header and exact field count;
3. reject blank IDs, blank fields, embedded tabs, embedded newlines, and malformed rows;
4. reject duplicate IDs;
5. enforce a closed status vocabulary declared once in the tool;
6. sort or require canonical order by ID, but not silently rewrite disorder in `--check` mode;
7. validate every source path and anchor as above;
8. generate the complete bytes of `FIDO_FCB_HUMAN_REVIEW_INDEX.md` deterministically;
9. in `--write` mode, replace the tracked Markdown only after all inputs validate;
10. in `--check` mode, compare exact bytes and fail when the tracked Markdown omits a row, retains a removed row, changes a field, changes order, or contains extra prose;
11. fail with the exact input path and reason on every read, decode, parse, path, anchor, or output mismatch;
12. never catch a selected-file error and continue;
13. never infer open acts by searching prose or Git history;
14. never contain a list of current act IDs.

## Generated Human Review Index

The generated file must include:

- a generated-file notice naming `FIDO_FCB_HUMAN_ACTS.tsv` and the generator;
- the exact table columns now in use;
- one generated row per TSV row;
- no temporary hand-maintained disclaimer;
- no `## Closed` history section;
- no hand-authored current rows.

The generated file remains in `.review/fcb/current/` and remains listed by the FCB Index.

## Working-tree and staged gates

Add Makefile targets equivalent to:

```text
human-review-index
human-review-index-check
```

`human-review-index` regenerates the tracked file.

`human-review-index-check` checks without writing.

Wire `human-review-index-check` into `make check` for the working-tree snapshot.

Wire the same checker into the pre-commit hook over the exact staged exported tree, before Docker or another later gate. It must receive the exported tree root, not read unstaged files from the host repository.

A staged TSV edit without the matching generated Markdown must fail. A staged generated-Markdown edit without the matching TSV must fail. An untracked nonignored TSV or source file selected by the exported snapshot rules must be handled under the same fail-closed rules.

## Permanent adversarial controls

Keep permanent controls for at least:

- a TSV row added while the generated Markdown omits it;
- a TSV row removed while the generated Markdown retains it;
- a duplicate ID;
- a malformed field count;
- an invalid status;
- a blank required act;
- a missing source file;
- a path containing `..`;
- a symlink source path;
- a nonregular source path;
- a missing anchor;
- a duplicate anchor;
- invalid UTF-8 in the TSV;
- invalid UTF-8 in a selected source file;
- a selected source file read failure;
- stale extra prose or a stale extra row in the generated Markdown;
- a positive canonical fixture.

Where root privileges make a mode-`000` file readable, the test must use a deterministic failing input method rather than silently skip the control. A skipped negative control is a failed test unless the suite names and validates an equivalent deterministic control.

Mutation-test the checker by restoring at least the two core false-green classes:

- omission of a live TSV row from generated output;
- retention of a removed TSV row in generated output.

The tests must fail for the intended reason.

## Historical stub

The old generator under `.review/spec-closure-campaign/` is historical campaign provenance. It may remain only when current code and documentation do not call it and its file clearly states that it is not the living-FCB generator.

Do not copy its old schema. Do not add a compatibility wrapper which routes the new command to it.

## Required FCB updates for D-07 implementation

No amendment is needed. Update the live corpus to record implementation of existing D-07:

- `FIDO_FCB_INDEX.md`: add the TSV to the live file set and describe the Markdown as generated;
- `FIDO_FCB_MODEL_OPERATIONS.md`: state the exact generator/check consultation and publication rule;
- `FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md`: require current human acts to be added to the TSV with one owning anchor and regenerated before review;
- `FIDO_FCB_HUMAN_REVIEW_INDEX.md`: regenerate it and remove the temporary disclaimer;
- `.review/NEXT_STEPS.md`: remove the deferred D-07 task and record the implemented gate;
- root `CLAUDE.md`: tell Claude to edit the TSV and owning source anchor, then regenerate; never hand-edit generated rows;
- Makefile and pre-commit documentation: name the actual gate.

Do not duplicate the current act list in those documents.

---

# Blocking finding 3 — the live corpus does not state one truth and violates D-24

## Current contradictions

The freeze claims the corpus states one truth. It does not.

At the same exact ref:

- `.review/NEXT_STEPS.md` and `FIDO_FCB_INDEX.md` name candidate `92fc04e...` as complete and awaiting review;
- `.review/REVIEW_REQUEST.md` says `state: closed`, says the candidate awaits review, then says repair 17 is active, Q-08 is open, and no review is requested;
- `FIDO_FCB_ROADMAP.md` still names `12b1bc...` as the current blocker, says repair 17 is active, and contains an unfinished sentence;
- `PROGRESS.md` and `.review/SOURCE_FOREST_STATUS.md` still name old candidates and repair states as current;
- `PROGRESS.md` and `.review/SOURCE_FOREST_STATUS.md` misdescribe C5 as `uintptr` plus rune constants/literals, while the FCB Roadmap defines C5 as the permanent Machine base;
- `.review/SOURCE_FOREST_STATUS.md` carries an old `523/523` gate count while the freeze claims `540/540`;
- `.review/C4_IMPLEMENTATION_REPAIR_17.md` contains an A006 supersession note but its literal definition of done still requires `Emit.Image` to be abstract and every raw image constructor inaccessible;
- source and gate comments still refer to the deleted “legacy compile class” and “legacy classification.”

A document cannot claim “one current truth” while retaining these conflicts.

## D-24 dangling paths

Governance D-24 says every operational path in the live FCB must resolve at the same exact Git ref unless it is explicitly typed as external evidence with an availability status.

The current corpus violates that rule:

1. `FIDO_FCB_ARCHITECTURE_CHARTER.md` directs work to missing path:

   ```text
   .review/C4_IMPLEMENTATION_REPAIR_6.md
   ```

2. `FIDO_FCB_TOOLCHAIN_EVIDENCE.md` names absent path:

   ```text
   .review/spec-closure-campaign/evidence-sandbox
   ```

The first must be removed or replaced with a live current path. It must not be retained as an operational command merely because Git history once had such a file.

The second must be typed accurately. If it is an ephemeral or external evidence root, store a neutral placeholder such as `{SANDBOX}` and state its availability class. Do not name an absent repository path as though it exists.

## Other live FCB defects

Repair all of these in the same coherence pass:

### Governance

- Move the D-25 naming rationale directly under D-25. It currently appears after the D-26 rationale.
- Order amendment register entries A001 through A006 numerically.
- Do not change their accepted substance.

### Checkpoint Authoring Guide

- Put §3a before §3b.
- Retain both A005 naming duty and A006 reducible-carrier duty.

### Architecture Charter

- Replace the stale statement that `uintptr` waits for acceptance of ADR-0001. ADR-0001 is already adopted for the current basis. The correct rule is that `uintptr` requires reopening ADR-0001 or adopting a replacement scope/target decision and paying its full inclusion price.
- Remove the present-tense statement that active repair 17 must satisfy the C4 obligation.
- Remove the missing repair-6 operational path.
- Replace any statement that ADR-0001 is unresolved.
- Keep ADR-0002 open/deferred.

### Closure Ledger

The canonical CSV and generated Markdown entries for `SPEC-X003` / `PRE-22` use stale inclusion-price text which says to accept or disposition ADR-0001. Update the canonical CSV to say:

> Reopen ADR-0001 or adopt a replacement target decision, then pay the full `uintptr` representation, typing, lowering, target-adequacy, and proof price.

Regenerate the Markdown from the canonical CSV. Do not hand-edit the generated view.

### FCB Index

- List the new Human Acts TSV.
- Describe the Human Review Index as generated, not as a blocked-C4 hand-maintained view.
- State the repair-18 current boundary during implementation and the next candidate during freeze.

### Root/current documents

Use this ownership rule:

- `.review/NEXT_STEPS.md` owns the current checkpoint and candidate state.
- `FIDO_FCB_HUMAN_ACTS.tsv` owns the current set of open human acts.
- the generated Human Review Index is the view of that TSV.
- the Roadmap owns checkpoint order and stable dependencies, not a second detailed repair narrative.
- Git history owns old candidate lists and superseded repair narratives.

Apply it as follows:

- `.review/REVIEW_REQUEST.md`: make the request state internally consistent. During repair it may say blocked/closed with no review requested; at freeze it must say open or pending review, name one exact candidate, and contain no stale Q-08 or repair-17 text.
- `FIDO_FCB_ROADMAP.md`: state only the current C4 boundary and stable next sequence. Remove the unfinished sentence and stale repair narrative.
- `PROGRESS.md`: stop owning current candidate state. Turn it into a durable proof/feature inventory or replace current-state prose with a pointer to NEXT_STEPS. Correct C5.
- `.review/SOURCE_FOREST_STATUS.md`: stop owning current candidate hashes, active repair numbers, gate counts, and next-checkpoint definitions. Retain only durable source-forest facts which have no better owner, or delete the file if NEXT_STEPS, PROGRESS, the FCB, and Git history fully subsume it.
- `.review/C4_IMPLEMENTATION_REPAIR_17.md`: when repair 18 is installed, remove repair 17 from the live tree. Git history is its archive. Do not keep a superseded contract beside the live one.
- `ARCHITECTURE.md`: correct C5 and A006 prose. It must not claim a private carrier constructor where A006 seals the token authority.
- `CLAUDE.md`: describe the D-07 generated Human Review Index workflow and current authority paths without copying candidate state.
- `gate/Assumptions.v` and `Compilable.v`: delete stale comments which call deleted code a “legacy compile class” or “legacy classification.”
- e2e and Docker comments: make claims match the exact current constructor and mint topology.

Delete current-only prose which adds no rule and merely repeats NEXT_STEPS. Do not perform the broad post-C4 comment cleanup in this repair.

## D-24 path gate

Add a fail-closed current-FCB reference check rather than relying only on review searches.

It must:

- read the live file set from the FCB Index or a single canonical file list;
- inspect operational repository paths in the current FCB;
- require each repository path to exist as the stated regular file or directory in the exact exported tree;
- permit external or ephemeral paths only through an explicit typed field and status, not a prose guess;
- fail on missing, renamed, symlinked, or path-traversal targets;
- run in working-tree and staged-export modes;
- include negative controls for a missing path, renamed path, deleted manifest, path traversal, symlink, and falsely externalized repository path.

Do not attempt to parse every backticked phrase as a path with ad hoc exceptions. Use an explicit current-reference manifest or typed reference fields owned by the FCB Index/Model Operations. One root object must own the list.

A suitable form is a current TSV such as:

```text
.review/fcb/current/FIDO_FCB_REFERENCES.tsv
```

with fields equivalent to:

```text
id	kind	path	availability	owner
```

where `kind` is closed, for example `repository-file`, `repository-directory`, `external-evidence`, or `ephemeral`. If you introduce this file, add it to the FCB Index and generate/check any view from it. Do not create a second untyped path authority.

If the existing FCB structure already has one more basic object which can own these typed references, use that instead and state why it is the root.

---

# FCB and review state for repair 18

No new amendment is required.

When this directive is installed:

1. add `.review/C4_IMPLEMENTATION_REPAIR_18.md` verbatim;
2. delete `.review/C4_IMPLEMENTATION_REPAIR_17.md` from the live tree;
3. update `.review/NEXT_STEPS.md` so:
   - `92fc04e264b56d575e2fd1d65ae5d7940c93dc84` is BLOCKING;
   - it is the nineteenth blocked C4 candidate;
   - `e15232d3ef894c2f478e36c736cd701533e224fe` is its documentation-only freeze;
   - repair 18 is the sole active C4 work;
   - C4 is not accepted;
   - C5 and all post-C4 work remain forbidden;
4. set the `C4-REVIEW` Human Acts row to the same blocked state;
5. update the FCB Index current boundary to the same state;
6. make `.review/REVIEW_REQUEST.md` state that no review is requested while repair 18 is active.

This installation commit is an authority/documentation commit. It must not change Rocq, OCaml, generated bytes, or gate behavior except for installing the directive and current state.

At the final freeze:

- the Human Acts row becomes `PENDING` and names the one exact implementation candidate;
- the generated Human Review Index reflects that row;
- NEXT_STEPS and the FCB Index name the same candidate;
- REVIEW_REQUEST requests the human C4 review consistently;
- C4 remains unaccepted;
- only Rob may accept it.

---

# Mandatory closure audit for the process experiment

This repair is the agreed one-round closure-process experiment. Do not freeze after fixing only the three named classes. Perform the whole-system audit below.

## 1. Claim-to-theorem matrix

Add a tracked review artifact under `.review/` for the repair, for example:

```text
.review/C4_REPAIR_18_CLAIM_THEOREM_MATRIX.tsv
```

It is not a new semantic authority. It is a review gate mapping each acceptance claim to the public object which actually states it.

Use fields equivalent to:

```text
claim_id	claim_text	owner_file	public_surface	fixture_or_client_test	gate	status
```

Include every load-bearing claim in:

- repair-18 definition of done;
- the C4 functional contract;
- A001 retained provenance;
- A005 naming;
- A006 mint authority;
- the final NEXT_STEPS completion prose;
- the freeze commit completion prose.

For each claim:

- name the exact public theorem, record field, module signature, negative client test, or generated gate which establishes it;
- reject a row whose public surface is only a proof-body fact not present in its statement;
- reject a row which combines separate existential witnesses but claims one exact object;
- reject a row whose gate comment says more than the named theorem;
- reject `status=closed` without all columns resolving;
- validate file paths and exact declaration/test names;
- fail when a named surface is deleted or renamed;
- fail on duplicate claim IDs;
- do not use `N/A` for a load-bearing claim without a written unsupported-boundary reason.

Add a checker and wire it into working-tree and staged checks. The checker need not understand Rocq types. It must at least verify exact named-surface presence and prevent a completion claim with an empty or dangling evidence cell. Human review will judge theorem strength.

The final report must walk the matrix and quote the exact aggregate accepted and rejected theorem statements.

## 2. Public constructor and mint audit

Inspect every public path which can create:

- `Compilable.Core`;
- `Compilable.Program`;
- `Compilable.Failure`;
- `Compilable.Facts`;
- `Safe.Program`;
- `Emit.Mint.Token`;
- `Emit.Image`.

Confirm:

- raw authority constructors remain unavailable;
- `Compilable.compile`, `Safe.certify`, and `Emit.Mint.issue` are the intended mints;
- the visible `Emit.Image` carrier pack still requires the exact token and is not described as private;
- no arbitrary-byte helper accepts equality as provenance;
- no compatibility alias or old constructor name survives;
- every negative client fixture fails for the intended reason;
- every positive public path compiles.

## 3. Reconstruction audit

After a capability or failure is returned, search every production theorem, fixture, safety path, render path, and emit path for:

```text
build_elaboration_core
build_compilation_input
build_expression_phase
Index.index_program
elaborate
program_visit
program_package_refs
```

Classify every hit. No returned-object guarantee may recover its evidence through one of these builders or an equality to their result.

Do not accept a zero-count search without reading the declarations which own the retained facts.

## 4. Semantic-peer and compatibility audit

Search for and delete any remaining:

- collapsed outcome peer;
- old result classifier;
- second diagnostic authority;
- second source or typed tree;
- second runtime or evaluator path;
- compatibility alias, wrapper, notation, or module;
- consumer-free fixture or theorem retained only for a deleted path.

Do not delete a required theorem merely to reduce counts. State its current consumer or gate.

## 5. Documentation and reference audit

From one exact staged exported tree:

- read the stable FCB bootstrap;
- read every file the Index names;
- run the D-07 human-act generator check;
- run the D-24 typed-reference check;
- read NEXT_STEPS and OPEN_QUESTIONS;
- search all current documents for old candidate hashes and active repair numbers;
- classify every historical hit;
- reject present-tense stale state;
- verify every current operational path resolves;
- verify current state appears only in its owning root and generated views.

## 6. Full execution-path audit

Run and report:

- naming gate in working-tree mode;
- naming gate in staged-export mode;
- Human Review Index generator check in both modes;
- FCB reference check in both modes;
- claim-to-theorem matrix check in both modes;
- full Rocq/Dune proof build;
- readable assumption gate;
- whole-theory assumption audit;
- all adversarial audit self-tests;
- all sealed-constructor and mint controls;
- extraction and plugin build;
- all Docker targets in the accepted path;
- OCaml materializer and sink tests;
- pinned Go whole-tree build and run against reviewed goldens;
- regeneration;
- regeneration guard;
- format check;
- exact generated-byte comparison;
- exact staged hook without `--no-verify`.

A green aggregate command is evidence. Report the named sub-gates and counts as well.

---

# Independent review evidence to preserve and re-run

This review environment independently established:

- the uploaded archive SHA-256 named above;
- the archive's generated `go.mod` and `main.go` are byte-identical to the prior reviewed upload;
- `go.mod` SHA-256 is `d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa`;
- `main.go` SHA-256 is `b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de`;
- the pinned host Go build command succeeded;
- the built program exited zero and matched reviewed stdout and stderr;
- the naming gate passed its 47 controls and the reviewed direct probes;
- the theory still has 16 root Rocq modules;
- `gate/Assumptions.v` names 540 readable assumption surfaces.

This environment did not contain Rocq, Dune, Docker, or the OCaml build toolchain. Therefore the reported proof, extraction, materializer, Docker, whole-theory assumption, and staged-hook results must be rerun by Claude from the exact repair-18 candidate. Do not cite the repair-17 report as a substitute.

---

# Required deletion and simplification

Repair 18 is not the broad post-C4 cleanup. Still apply the standing deletion law inside the changed area.

Delete:

- live repair-17 authority after repair 18 is installed;
- split aggregate fixtures made obsolete by the one accepted/rejected root fixtures;
- stale gate entries and comments for deleted fixture peers;
- the Human Review Index hand-maintained disclaimer and closed-history section;
- the deferred D-07 task after its gate is live;
- duplicate current-state narratives;
- dangling operational references;
- stale legacy-class comments;
- any temporary mechanism probe or demo.

Do not add:

- compatibility aliases;
- old theorem wrappers;
- a second cause record;
- a second human-act list;
- a second reference list;
- a second generator implementation;
- TODOs or placeholders;
- C5 types, states, labels, transitions, or run relations;
- the broad comment cleanup;
- proof-module partitioning.

---

# Definition of done

Repair 18 is complete only when all of the following are true.

## Returned-object theorem topology

1. One accepted root theorem returns one exact `cp` from one exact `compile` branch.
2. That same `cp` carries the complete accepted fixture guarantee.
3. The complete accepted guarantee names the exact retained forest, exact full index and two-way domain, exact outcomes, exact trace, four exact retained cause objects, exact facts, package object, layout, plan, exact empty raw/final diagnostics, and equal-value/distinct-occurrence fact.
4. Each accepted conversion cause is tied to the exact `RetainedMemberCause` projected from the exact retained trace, including exact predecessor accumulator, suffix membership, step, operand outcome, final preservation, conversion result, and final fact.
5. The same exact `cp` is passed through `Safe.certify` and `Emit.of_safe`; no second compile witness is introduced.
6. One rejected root theorem returns one exact `fail` from one exact rejected compile branch.
7. That same `fail` carries the exact forest, full index, outcomes, trace, exact failure and child cause objects, exact predecessor outcome, annotation context, package object, layout, plan, exact singleton raw diagnostic, and exact singleton final diagnostic.
8. No returned-object root theorem or proof reconstructs a peer core, phase, index, visit, package map, or fact table.
9. Split or weaker aggregate peers with no distinct current purpose are deleted.
10. The final accepted and rejected theorem statements are directly gated.

## D-07

11. `FIDO_FCB_HUMAN_ACTS.tsv` exists and is the one current human-act data authority.
12. Each open act has one validated owning source anchor.
13. The Human Review Index is deterministic generated output from the TSV.
14. Its temporary disclaimer and closed-history section are gone.
15. The generator fails closed on malformed data, stale output, missing and extra rows, path errors, anchor errors, read/decode errors, and duplicates.
16. Working-tree and staged-export checks both enforce exact generated bytes.
17. Permanent adversarial and mutation controls pass.
18. No current tool hard-codes the list of open act IDs.
19. The historical campaign stub is not on a live path.

## D-24 and documentation

20. Every live FCB operational repository path resolves at the exact ref or is explicitly typed external/ephemeral with a status.
21. The missing repair-6 path is gone.
22. The absent evidence-sandbox path is no longer presented as a repository path.
23. The typed reference gate runs in working-tree and staged-export modes with negative controls.
24. Governance D-25 and D-26 rationales are under the right decisions.
25. Amendment register entries are ordered A001 through A006.
26. Checkpoint Guide §3a precedes §3b.
27. The Charter states ADR-0001's accepted status correctly and removes active repair-17 prose.
28. The Closure Ledger canonical CSV carries the corrected `uintptr` inclusion price and its Markdown view is regenerated.
29. NEXT_STEPS, the FCB Index, generated Human Review Index, Review Request, Roadmap, OPEN_QUESTIONS, PROGRESS, status documents, architecture, source comments, and gate comments state one current truth.
30. NEXT_STEPS alone owns detailed current checkpoint state; the Human Acts TSV alone owns open human acts.
31. No current document claims C4 acceptance.
32. No current document says C5 is `uintptr` plus rune literals.
33. No current comment refers to a live legacy compile class or legacy classification.
34. Repair 17 is absent from the live authority tree after repair 18 is installed.

## Process-experiment closure audit

35. The claim-to-theorem matrix exists, validates, and has no dangling or empty load-bearing row.
36. Every final completion claim maps to an exact public surface and gate.
37. Public constructor/mint, reconstruction, semantic-peer, documentation/reference, and live execution path audits are complete and reported.
38. No “all findings closed” claim appears before the matrix and all exact checks pass.

## Proof, build, artifact, and scope gates

39. All retained proof surfaces are assumption-free.
40. The whole-theory audit and all adversarial controls pass.
41. Every negative client test fails for the intended reason; every positive public path compiles.
42. Extraction, plugin, OCaml materializer, sink, and Docker paths pass.
43. The pinned Go whole-tree build and reviewed run pass.
44. Regeneration and regeneration guard pass.
45. Formatting and naming pass.
46. Generated `go.mod` and `.go` files are byte-identical to the reviewed baseline.
47. The exact staged exported snapshot passes every hook gate without bypass.
48. No C5, checkpoint-definition Step 0, broad cleanup, proof partitioning, or post-C4 feature work is present.
49. The final freeze names one implementation candidate and one documentation-only freeze if needed.
50. The final candidate remains unaccepted pending Rob's human review.

Green commands are necessary evidence. They are not sufficient. Before freezing, read the public theorem statements, constructor topology, mint paths, exact generated human-act view, typed reference set, and every final completion claim by hand.

---

# Execution cadence and notification

Use:

```text
/loop 3m
```

Continue implementing, checking, auditing, simplifying, and rereading this directive until every required item is complete or a real blocker prevents further work.

Do not stop for:

- routine progress reports;
- green intermediate checks;
- partial completion;
- one closed finding while another remains;
- a documentation-only state which still contradicts code;
- a request to accept C4 without the D-07 gate;
- a freeze whose prose is stronger than its public theorem statements.

When complete or genuinely blocked, use the notification tool to notify Rob.

If complete, report:

- exact implementation candidate SHA;
- exact documentation-only freeze SHA, if separate;
- commit list and purpose;
- the full accepted root theorem statement;
- the full rejected root theorem statement;
- how each exact retained cause is tied to the retained trace;
- Human Acts TSV rows and generated-index check results;
- D-24 typed-reference inventory and check results;
- claim-to-theorem matrix path and closed row count;
- proof/gate counts;
- constructor and mint negative client inventory;
- generated artifact hashes;
- full command results;
- FCB/current-document files changed;
- confirmation that C4 remains unaccepted pending Rob's review.

If blocked, report:

- the exact failed obligation;
- the smallest reproducer;
- the exact theorem, constructor, generator, or reference topology involved;
- the exact FCB text which conflicts;
- why the accepted contract cannot be met;
- the precise human decision required;
- the last good commit.

Do not improvise another architecture.
