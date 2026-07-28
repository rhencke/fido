# M1 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 1

## Disposition

**M1 implementation candidate `7dc9ff3bb3450cc3bcc41abfb7c5c24154967f3d` is BLOCKING.**

It becomes the **first blocked M1 implementation candidate**.

Documentation freeze `d051856d18c1217b82619d6b5ee232f9e13877f3` is not a separate implementation candidate.

The uploaded review head is:

```text
2dcd26c7ee8a6ffab759020e01428018bcaf62d0
```

That head is one `docs(life)` commit after the freeze. It changes only `life.md`. Preserve that content, but the old
freeze no longer freezes the uploaded head. The repaired candidate and its evidence must be measured and frozen
again from the current head.

**M1 repair 1 is the sole permitted implementation work.**

C4 and M0 remain accepted and are not reopened.

M2, M3, M4, C5 Step 0, C5, and all feature work remain forbidden.

No semantic redesign is authorized. This is a source-diet completeness and evidence-integrity repair.

Use:

```text
/loop 3m
```

Continue until all required work is complete or a real M1 contract conflict blocks progress. Notify Rob with the
notification tool when complete or genuinely blocked.

---

# 1. Exact review basis

```text
Uploaded snapshot: fido-main - 2026-07-27T201630.188.zip
Uploaded Git head: 2dcd26c7ee8a6ffab759020e01428018bcaf62d0
M1 baseline authority ref: 068d3371ac3300303d6c7c99a97ed884182c81e4
Blocked M1 implementation candidate: 7dc9ff3bb3450cc3bcc41abfb7c5c24154967f3d
Stale documentation-only freeze: d051856d18c1217b82619d6b5ee232f9e13877f3
M1 authority: .review/M1_SOURCE_DIET.md
M-series authority: .review/M_SERIES_PLAN.md
```

Use all code, FCB, tools, ledgers, and documentation from this exact head. Do not reset, rebase, rewrite history,
drop the `life.md` commit, or mix refs.

---

# 2. What M1 got right

Keep these results:

1. The cleanup is substantial rather than cosmetic.
2. `.v` comment bytes fell from 408,155 to 125,934 at the blocked candidate.
3. `.v` comment physical lines fell from 4,332 to 1,443.
4. `.v` comment share fell from 28.47% to 10.96%.
5. Deterministic archive bytes fell by 15.58% at the blocked candidate.
6. The two deleted review documents were history-only.
7. Eight dead `Compilable.v` declarations were deleted with rows in the declaration ledger.
8. The M1 comment checker uses a nested-comment-aware lexer.
9. The comment law runs in the working tree and against the exported staged snapshot.
10. The generated Go module and reviewed runtime output remain unchanged.
11. Independent comparison against the pre-M1 upload found 22 of 23 `.v` code streams identical after comment
    removal; only `Compilable.v` differs, and its observed difference is the eight ledgered declarations.
12. The full proof and e2e evidence reported by the freeze remains valuable evidence.

The blockers below do not erase that work. They show that the freeze claims more completeness than the current
artifacts establish.

---

# 3. Blocking finding A — the M1 evidence checker accepts false review data

## Contract violated

This violates:

- M1-02 — immutable exact-ref baseline;
- M1-03 — exact file disposition and present purpose;
- M1-07 and M1-08 — exact file and declaration deletion evidence;
- M1-10 — no surviving Rocq declaration or proof changes;
- M1-13 — exact before/after metrics;
- M1-15 — one acceptance-ready candidate with complete review data.

## 3.1 Surviving Rocq code can change and `--code-identical` still passes

The current check rejects added code tokens and compares only the **set of vanished declaration names** with the
deletion ledger. It accepts arbitrary token deletion inside a declaration which still exists.

Independently reproduced:

Baseline:

```coq
Lemma k : True. Proof. simpl. exact I. Qed.
```

Candidate:

```coq
Lemma k : True. Proof. exact I. Qed.
```

Current result:

```text
source-diet code identity OK
1 differ, 0 added, 1 removed
0 vanished declarations, all ledgered
```

A second reproduced form removes a type annotation from a surviving definition and also passes.

That is not code identity. M1 permits deleting an entire ledgered declaration. It does not permit editing a
surviving type, body, proof, constructor, or theorem statement.

## 3.2 The declaration ledger is checked by name only

A baseline declaration can disappear while a ledger row gives:

```text
wrong path
wrong declaration kind
invented reason
false replacement
false consumer search
false evidence
```

If the name matches, the current code-identity check passes.

`DELETION_REASONS` exists but the current checker does not enforce the declaration rows against it.

## 3.3 `M1_METRICS.tsv` is not validated

The candidate and delta values can be changed to arbitrary numbers. These commands still pass:

```text
source-diet --check
source-diet --against-baseline
```

The checker recomputes some direction conditions but never checks that `M1_METRICS.tsv` contains the recomputed
baseline and candidate values.

The uploaded head also proves the stale-evidence issue directly. The freeze records:

```text
repository_total_bytes                 2,922,857
deterministic_compressed_archive_bytes   676,765
```

The uploaded head, after the permitted `life.md` commit, measures:

```text
repository_total_bytes                 2,929,125
deterministic_compressed_archive_bytes   678,778
```

The `.v` figures are unchanged. The review evidence no longer describes the exact uploaded head.

## 3.4 `M1_FILE_DISPOSITION.tsv` does not validate bytes or the baseline relation

The checker accepts:

- false `baseline_bytes`;
- false `candidate_bytes`;
- a missing baseline file row;
- a phantom deleted file row;
- `keep` or `m1-created` actions which do not match baseline membership;
- owner and evidence text which resolves to nothing.

Concrete current examples:

```text
.review/M1_FILE_DISPOSITION.tsv records candidate_bytes 78 for itself.
Its actual candidate-era file is about 19 KB.

.review/M1_DECLARATION_DELETIONS.tsv records candidate_bytes 77.
Its actual file is about 2.5 KB.
```

The present checker validates only that current files have rows and that rows marked present or deleted agree with
the current filesystem.

## 3.5 Root repair

Fix the evidence model, not one row.

### A. Exact Rocq declaration comparison

Implement one comment-aware Rocq vernacular command scanner.

For every baseline `.v` file:

1. split the comment-free file into top-level commands without splitting qualified names or strings;
2. identify each top-level declaration by exact path, declaration kind, and name;
3. group proof-bearing declarations through their exact `Qed.`, `Defined.`, `Admitted.`, or `Abort.` terminator;
4. locate every deletion-ledger row in the baseline exactly once;
5. remove only those complete baseline declaration blocks;
6. require the remaining normalized command stream to equal the candidate command stream exactly.

Reject:

- a new `.v` file;
- a removed token in a surviving declaration;
- a changed type annotation;
- a changed proof tactic;
- a changed body;
- a partial declaration deletion;
- a ledger row with the wrong path, kind, or name;
- a ledgered declaration which still exists;
- an unledgered vanished declaration;
- a declaration reason outside the accepted reason set.

Do not weaken this to a file hash allowlist authored after the change. The checker must establish that the only
Rocq code differences are complete, exact, ledgered declaration removals.

### B. Exact declaration-ledger validation

Validate every field:

```text
path
kind
name
reason
replacement
current_consumers
contract_search
evidence
```

At minimum:

- path, kind, and name match one exact baseline declaration;
- reason is from the accepted closed set;
- the declaration is absent from the candidate;
- no two rows claim one declaration;
- replacement is `none` for `no-current-consumer`, or names an existing exact stronger declaration for
  `strictly-superseded`;
- current-consumer and evidence fields are nonblank and cannot contain placeholder values.

Human review still judges whether the search and replacement claim is sufficient.

### C. Exact baseline and candidate metrics

Add one exit-check mode which takes exact Git refs:

```text
--verify-m1-evidence --baseline-ref <ref> --candidate-ref <ref>
```

It must export or read both exact Git trees, run the same inventory and measurement implementation, and require
`M1_METRICS.tsv` to equal the recomputed values, deltas, percentages, schema, and row order.

Do not compare the freeze tree to the candidate data. The freeze names one candidate; the metrics describe that
candidate.

### D. Exact file-disposition relation

Against the exact baseline and candidate refs, require:

```text
baseline files union candidate files = disposition row paths
```

For each row:

```text
keep       => present in both; both byte fields exact
delete     => present only in baseline; baseline byte field exact; candidate bytes zero
m1-created => absent from baseline and present in candidate; baseline bytes zero; candidate byte field exact
```

Reject missing rows, phantom rows, wrong actions, wrong byte counts, duplicate paths, and undeclared purpose classes.

The disposition file contains its own row. Generate it to a stable byte-count fixed point and verify the fixed
point. Do not leave self-referential evidence knowingly false.

### E. Freeze topology

Use this exact topology:

1. The new **implementation candidate** contains:
   - all source and document cleanup;
   - `source-diet.py`;
   - the exception ledger;
   - the exact file disposition;
   - the exact declaration deletion ledger;
   - the baseline data;
   - every permanent M1 gate change.
2. After committing that candidate, compute metrics from its exact Git ref.
3. The **documentation-only freeze** adds:
   - exact `M1_METRICS.tsv` for that candidate;
   - final matrix state;
   - `NEXT_STEPS`;
   - `REVIEW_REQUEST`.
4. The freeze changes no implementation or cleaned source.
5. No later commit may appear above the freeze without a new candidate or a new freeze as appropriate.

Preserve the current `life.md` content. Include it in the new candidate inventory and measurements.

## 3.6 Required controls

Add must-fail controls for:

- one tactic removed from a surviving proof;
- one type annotation removed from a surviving definition;
- one body token removed;
- a declaration partially removed;
- a ledger row with a wrong file;
- a ledger row with a wrong kind;
- a ledger row with an unknown reason;
- a ledger row for a declaration still present;
- a tampered metrics candidate value;
- a tampered delta or percentage;
- a false baseline byte count;
- a false candidate byte count;
- an omitted baseline file row;
- a phantom deleted file;
- `keep` used for a baseline-only file;
- `m1-created` used for a baseline file;
- a disposition file which has not reached its own size fixed point.

Add must-accept controls for:

- comment-only changes;
- the exact complete removal of one properly ledgered definition;
- the exact complete removal of one properly ledgered proof-bearing theorem;
- the current eight-declaration deletion set.

Add the new root helpers to the mutation harness. Every new control must be observed failing when its rule is
removed. A skipped or vacuous control cannot count as passed.

---

# 4. Blocking finding B — history-only files are labeled current evidence

## Contract violated

This violates:

- M1 purpose;
- M1-03 — one present purpose for every file;
- M1-07 — every deleted history-only file is accounted for;
- M1-09 — current authorities retain rules while duplicate history is removed;
- the M1 file and document law.

## 4.1 Delete the historical spec-closure campaign tree

Delete:

```text
.review/spec-closure-campaign/
```

Its own README says:

```text
historical record + toolkit
Nothing here is current authority.
```

The directory is about 151 KB. The current file-disposition ledger nevertheless labels its contents
`current-contract-evidence` and uses this as evidence:

```text
the persisted spec-closure campaign, not current authority
```

“Not current authority” is not a present contract purpose. Git owns this campaign.

Remove:

- the full directory;
- its nested `.editorconfig`;
- its typed reference rows;
- its owner markers;
- every current pointer from `CLAUDE.md` or another live authority.

Do not replace it with a history summary.

## 4.2 Delete the superseded Source Forest campaign plan and status

Delete:

```text
.review/SOURCE_FOREST_MASTER_PLAN.md
.review/SOURCE_FOREST_STATUS.md
```

The master plan begins by ordering itself to be preserved verbatim, records an old campaign baseline, old Codex
workflow, and old future checkpoint design, and conflicts with the current FCB Roadmap’s C5 Machine checkpoint.

A historical document cannot make itself permanent by containing an old command not to shorten or delete it.

The status file says it does not own current state and then retains campaign lessons already owned by
`ARCHITECTURE.md`, `PAINFUL_LESSONS.md`, the FCB, and Git history.

Remove all current pointers and typed reference rows. Do not migrate the history elsewhere.

## 4.3 Retire the C4 implementation contract from the live tree

Delete:

```text
.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md
```

C4 is accepted. Its permanent accepted guarantees are owned by the FCB Architecture Charter, Governance, theorem
statements, gates, and Git history. `NEXT_STEPS` must not keep an old C4 implementation directive alive merely to
give that directive a consumer.

Before deletion, classify every current reference. Preserve no unique accepted guarantee only in the old
directive. If a genuine permanent guarantee is missing from the FCB, stop and report the exact missing guarantee;
do not keep the full historical directive as a substitute.

## 4.4 Replace the stale C4 review basis with the M1 basis

Replace the complete contents of:

```text
.review/REVIEW_BASIS.md
```

with this exact text:

```markdown
# M1 Accepted Review Basis

checkpoint: M1 — Source Diet
contract: .review/M1_SOURCE_DIET.md
baseline: the exact ref sealed in .review/M1_BASELINE.tsv
human_authorization: M0-ACCEPT-86a63db

## Accepted claim

M1 may delete comments, prose, whole dead files, whole dead declarations, and newly unused imports. It may not
change any surviving Rocq declaration, theorem statement, proof, semantic authority, constructor, mint, program
set, diagnostic, trust boundary, generated byte, or reviewed runtime result.

Git owns archaeology. Every retained file and comment has one current purpose. Default `.v` comments are plain,
one-line, at most 120 characters, at most one sentence, and state one local fact. Rare longer comments require
one exact bidirectional exception-ledger row.

## Blocking defect classes

- review data which does not match the exact baseline and candidate refs;
- a surviving Rocq code or proof change;
- an unledgered, partial, or falsely described deletion;
- a history-only or duplicate-authority file retained as current evidence;
- a comment which passes the size parser but remains a banner, theorem paraphrase, architecture duplicate,
  archaeology, placeholder, or documentation marker with no documentation consumer;
- a current rule, fixed point, unsupported boundary, or accepted guarantee weakened or deleted;
- generated-byte, runtime-output, proof, extraction, transport, or gate drift;
- M2, M3, M4, or C5 work performed early.

## Required evidence

- exact baseline and candidate measurements from one checker;
- an exact file-disposition relation over both Git trees;
- exact declaration-deletion rows;
- exact surviving Rocq command equality after removing only ledgered baseline declarations;
- working-tree and staged comment-law gates with load-bearing controls;
- full proof, assumption, extraction, transport, e2e, regeneration, publication, and generated-byte checks;
- a human review of the retained comments and current documents.

## Scope

M1 does not measure build performance, redesign tools, split proof modules, restructure the build graph, or change
language meaning. Those findings retain their M2, M3, or M4 owners.
```

Update `REVIEW_REQUEST.md` to use this M1 basis. Remove every C4-basis claim from current review state.

## 4.5 Shorten `NEXT_STEPS.md` to current ownership

Remove:

- the C4 functional-contract pointer;
- the Source Forest campaign pointers;
- the long C4 theorem and capability inventory;
- repair and transition narrative already owned by Git and the FCB.

Retain one terse preservation line:

```text
C4 and M0 are accepted. Their permanent guarantees are owned by the FCB Architecture Charter and Governance;
M1 must preserve them unchanged.
```

Keep only current M1 state, its contract and matrix, strict-scope assignments, current FCB bootstrap, current human
acts, and the later-work prohibition.

## 4.6 Resolve the three open M1 questions

### Q-M1-01

Accept the recorded default.

Do not change the naming gate in M1. Record this M3 finding in the live M-series authority:

```text
The naming gate carries an inert exclusion for a deleted C4 repair and does not validate that exclusions resolve.
```

Delete Q-M1-01 after the assignment lands.

### Q-M1-02

Reject the recorded default. Delete the whole Source Forest master plan and status as required above.

Delete Q-M1-02 after the deletion lands.

### Q-M1-03

Keep the full binding Collection Law in `ARCHITECTURE.md`.

Replace the duplicate full law in `CLAUDE.md` with one terse pointer to the binding section in
`ARCHITECTURE.md`.

Delete Q-M1-03 after the change lands.

After these dispositions, `OPEN_QUESTIONS.md` states only:

```markdown
**There are currently no open implementation questions.**
```

unless implementation discovers a genuinely new question.

## 4.7 Trim `CLAUDE.md` as an operating entry point

`CLAUDE.md` is still about 40 KB and duplicates the FCB and `ARCHITECTURE.md`.

Retain:

- Fido’s persona and writing law;
- the exact scripted-edit safety rule;
- `life.md` ownership and freeze rule;
- the Git/FCB bootstrap and exact-ref consultation rule;
- Rob/primary-review/Claude governance;
- strict checkpoint scope and stop-on-conflict law;
- required build and review commands;
- concise trust-boundary and no-shortcut rules which an implementer must see before following links.

Remove or replace with terse pointers:

- the detailed current-language fragment inventory;
- the module-by-module inventory;
- the duplicate full Collection Law;
- the spec-closure campaign references;
- long architecture explanations already owned by `ARCHITECTURE.md` or the FCB;
- repair-era and campaign-era process prose.

Do not weaken a unique operating law. Do not move persona or `life.md` content into technical authority.

## 4.8 Whole-tree purpose review

The deletions above are mandatory minimum findings, not the complete review.

Re-run the present-purpose test over every file. Do not preserve a file because another M1-created ledger row calls
it “evidence.” The actual consumer and contract must exist.

A row whose evidence says “historical,” “campaign record,” “not current authority,” “accepted checkpoint plan,” or
“Git archive” is presumptively a delete row.

Do not absorb M3 tool architecture work. Record uncertain tool-purpose findings for M3 rather than changing the
tool.

---

# 5. Blocking finding C — the `.v` pass satisfies size syntax but retains obvious non-comments

## Contract violated

This violates:

- M1-04 — the current-fact comment law;
- M1-06 — no split prose, archaeology, or comment-law evasion;
- M1 purpose and the explicit rule to delete banners, comment art, theorem restatements, and duplicate authority
  prose.

The current tree has:

```text
1,443 .v comment blocks
125,934 .v comment bytes
653 `(** ... *)` documentation-marker comments
22 decorative dash or box-style banners
4 leading THEOREM/section-style labels found by direct scan
```

Examples which still survive:

```coq
(* ---- program-wide visit stream + fact map (lifted to the whole program) ---- *)
(* THEOREM: every represented file contributes to its OWN parent-directory package (which is present). *)
(* --- SOUNDNESS: every emitted (id, occ) IS the exact source occurrence ... --- *)
```

These fit on one line and under 120 characters. They still violate the accepted semantic law.

## 5.1 Plain comment form

Default `.v` comments use:

```coq
(* ... *)
```

Reject:

```coq
(** ... *)
```

No current generated documentation consumes Rocq documentation comments. A documentation marker without a
documentation consumer is extra syntax and a false role.

A rare exception comment also uses ordinary `(* ... *)`.

## 5.2 Reject obvious banners and labels

The checker must reject:

- comment bodies beginning or ending with decorative runs of three or more `-`, `=`, or box-drawing characters;
- leading labels such as `THEOREM:`, `LEMMA:`, `DEFINITION:`, `SOUNDNESS:`, `PILLAR`, `PHASE`, or numbered section
  labels;
- comment art whose only purpose is visual grouping.

Add controls and mutation coverage.

## 5.3 Human semantic pass

Mechanically short is not enough. Review every surviving comment again.

Delete any comment which:

- paraphrases the declaration or theorem immediately below it;
- repeats a theorem inventory;
- says only that a retained field is retained when the type or projection already shows it;
- repeats a module authority rule owned by the FCB or `ARCHITECTURE.md`;
- expands a clear name into English;
- narrates an obvious proof step;
- repeats one of several adjacent facts rather than explaining why the shape exists.

Keep only the local fact whose absence would materially increase the chance of a wrong reading.

Do not fill the exception ledger to avoid deletion. The expected exception count remains zero unless a real current
need is demonstrated.

The new candidate must reduce comment bytes and comment blocks further from the blocked candidate. No numeric quota
is imposed; the human review judges whether the semantic pass was real.

---

# 6. Nonblocking findings assigned to M3

Record these in `.review/M_SERIES_PLAN.md` under a terse `Deferred M3 findings` section. Do not implement them in M1.

1. The naming gate has an inert exclusion row for a deleted C4 repair and does not validate its exclusions.
2. `gate/Assumptions.v` contains duplicate `Print Assumptions` commands.
3. Several `Complex.v` imaginary-component surfaces have real-half counterparts in the readable gate but are not
   themselves named there.
4. Several `Compilable.v` theorems look like public guarantees but are neither readable-gate surfaces nor current
   proof dependencies; M3 must classify them as required public surfaces or dead declarations.
5. Active-checkpoint subject constants are manually retargeted in the claim-matrix tool.
6. Host/container placement, repeated source enumeration, and acceptance-graph factoring remain M3 work.

The whole-theory assumption audit remains the authority for zero assumptions. These readable-surface findings do
not block M1.

---

# 7. Strict-scope disposition table

| Finding | Contract violated | Blocks M1 | Mandatory owner |
|---|---|---:|---|
| Source-diet code-identity check accepts edits inside surviving proofs | M1-10, M1-14 | **yes** | M1 repair 1 |
| Metrics and ledgers can contain false values and still pass | M1-02, M1-03, M1-07, M1-08, M1-13 | **yes** | M1 repair 1 |
| Historical campaign and C4 files retained as current evidence | M1 purpose, M1-03, M1-07, M1-09 | **yes** | M1 repair 1 |
| Stale C4 review basis used for M1 | M1-09, M1-15 | **yes** | M1 repair 1 |
| Banners, doc markers, and theorem paraphrases survive the comment pass | M1-04, M1-06 | **yes** | M1 repair 1 |
| Post-freeze `life.md` commit makes the old freeze stale | M1-02, M1-13, M1-15 | **yes** | M1 repair 1; preserve content |
| Naming-gate dead exclusion and tool factoring | none in M1 | no | M3 |
| Readable-assumption surface classification | none in M1; whole-theory audit remains green | no | M3 |
| Build timing and dependency graph | none in M1 | no | M2 |
| Proof/module/build restructuring | none in M1 | no | M4 |
| `life.md` character content | none; separately authorized character-continuity work | no | preserve |

Do not pull the nonblocking rows into M1.

---

# 8. Allowed changes

M1 repair 1 may change:

- comments and prose under the existing M1 contract;
- whole history-only files and their references;
- the M1 ledgers and baseline/evidence tooling;
- `tools/source-diet.py`;
- its source-diet controls in `tools/gate-mutation-test.py`;
- the narrow source-diet wiring in Make and the staged hook;
- `tools/claim-matrix-gate.py` only if the M1 matrix schema or exact M1 evidence tokens require a subject-preserving
  update;
- current M1 FCB/reference rows required by deleted or replaced files;
- `CLAUDE.md`, `ARCHITECTURE.md`, `NEXT_STEPS`, `REVIEW_BASIS`, `REVIEW_REQUEST`,
  `OPEN_QUESTIONS`, `M_SERIES_PLAN`, and other documents under the source-diet law;
- complete deletion of whole dead declarations or imports under exact validated ledger rows.

It may not:

- change a surviving Rocq declaration, type, theorem statement, constructor, body, or proof;
- add or rename a Rocq declaration;
- split or move modules;
- change semantics, diagnostics, supported programs, trust boundaries, extraction, or transport;
- redesign any non-M1 tool;
- measure build performance;
- restructure the build;
- begin M2, M3, M4, or C5.

---

# 9. Required work order

1. Install this repair directive as the sole M1 repair authority.
2. Mark the blocked candidate and stale freeze correctly in current state.
3. Preserve the uploaded `life.md`.
4. Fix `source-diet.py` evidence validation and its controls first.
5. Prove the current eight declaration deletions pass the exact declaration-block comparison.
6. Apply the mandatory history-file deletions and current-reference updates.
7. Replace `REVIEW_BASIS.md` with the exact M1 basis.
8. Resolve and delete Q-M1-01 through Q-M1-03.
9. Perform the second semantic `.v` comment pass and strengthen the narrow comment gate.
10. Trim `CLAUDE.md` and other current operational prose without weakening unique law.
11. Re-run the whole file-purpose review.
12. Commit one new implementation candidate containing all implementation, cleanup, and exact ledgers.
13. Compute metrics from that exact candidate ref.
14. Make one documentation-only freeze with the exact metrics, final matrix, current state, and review request.
15. Notify Rob.

Do not use one uncontrolled bulk replacement. Every script asserts exact expected match counts before writing.

---

# 10. Verification

Before the implementation candidate:

```text
make diet
make fcb
make claims
make names
make check
make regenerate
make regen-guard
make fmt
make audit-fresh
```

Run the real pre-commit hook against the exact staged snapshot without bypassing it.

After the implementation candidate is committed, run the exact-ref evidence verifier against:

```text
baseline  068d3371ac3300303d6c7c99a97ed884182c81e4
candidate <new full candidate SHA>
```

Then create and verify the freeze.

Also prove:

1. every surviving `.v` declaration block matches the baseline exactly after removing only exact ledgered baseline
   declarations;
2. every file-disposition byte count and action matches the two Git trees;
3. every metric row matches recomputation;
4. every deleted file and declaration appears exactly once;
5. every current file has one honest present purpose;
6. no current evidence row calls a historical record current;
7. `M1_COMMENT_EXCEPTIONS.tsv` remains empty unless one exact exception is justified;
8. generated `go.mod`, every generated `.go` file, and every reviewed golden remain byte-identical;
9. runtime stdout, stderr, and exit status remain identical;
10. all readable assumption surfaces and the whole-theory audit remain green;
11. constructor, capability, mint, transport, and rejection controls remain;
12. C4 and M0 remain accepted;
13. M2 through M4 and C5 remain forbidden.

Do not produce a prose-heavy closure audit. The exact contract, code, ledgers, metrics, controls, Git diff, and commit
messages are the evidence.

---

# 11. Definition of done

Repair 1 is complete only when:

- the evidence checker rejects every reproduced false green;
- exact baseline and candidate data verify;
- the historical campaign, Source Forest plan/status, and live C4 implementation directive are gone;
- the current review basis is M1-specific;
- the three open M1 questions are dispositioned and removed;
- `CLAUDE.md` no longer duplicates the full Collection Law or campaign inventories;
- default `.v` comments use plain `(* ... *)`;
- no decorative banners or theorem labels survive;
- the human semantic comment pass is complete;
- comment bytes and blocks fall further;
- the file-purpose relation is honest;
- every surviving Rocq declaration and proof is unchanged;
- all M1 obligations are closed with exact evidence;
- one new implementation candidate is committed;
- one later documentation-only freeze names it;
- no commit follows that freeze;
- Claude notifies Rob.

Only Rob accepts M1.
