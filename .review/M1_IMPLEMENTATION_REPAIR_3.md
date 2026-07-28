# M1 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 3

## Disposition

**M1 implementation candidate `8ad80e6614bff64b493bbdd1db937f4640eda252` is BLOCKING.**

It becomes the **third blocked M1 implementation candidate**.

Documentation freeze `8e55ed1efbc430a815c9ce2d4f4a8f1365ba59ed` is not a separate implementation candidate.

**C4 and M0 remain accepted.** This review does not reopen either checkpoint.

**M1 repair 3 is the sole permitted implementation work.**

M2, M3, M4, C5 Step 0, C5, and all feature work remain forbidden until Rob accepts M1.

No semantic, proof, language, extraction, rendering, transport, or generated-output redesign is authorized. This is
one M1 gate-lifetime repair: the permanent source-comment policy must survive M1 without turning M1’s temporary
review baseline into a permanent ban on later work.

Use:

```text
/loop 3m
```

Continue until this directive is complete or a real M1 contract conflict blocks progress. When complete or
genuinely blocked, notify Rob with the notification tool.

---

## 1. Exact review basis

```text
Uploaded snapshot: fido-main - 2026-07-28T153552.565.zip
Uploaded Git head: 8e55ed1efbc430a815c9ce2d4f4a8f1365ba59ed
M1 implementation candidate: 8ad80e6614bff64b493bbdd1db937f4640eda252
Documentation-only freeze: 8e55ed1efbc430a815c9ce2d4f4a8f1365ba59ed
M1 baseline authority ref: 068d3371ac3300303d6c7c99a97ed884182c81e4
Previous blocked M1 candidates:
  7dc9ff3bb3450cc3bcc41abfb7c5c24154967f3d
  71e70de20e11495ccb829130b6c021d9b00ce59c
M1 authority: .review/M1_SOURCE_DIET.md
Accepted review basis: .review/REVIEW_BASIS.md
```

Use every code, FCB, gate, ledger, and document from this exact ref. Do not reset, rebase, rewrite history, drop
commits, or mix refs.

Preserve `life.md` byte-for-byte. It is separately authorized character-continuity content and is not M1
technical prose.

---

## 2. What repair 2 got right

Keep every result below.

1. The exact Rocq command comparison now distinguishes a declaration from adjacent `Hint`, `Arguments`, `Opaque`,
   `Transparent`, instance, scope, import/export, section, and control commands.
2. The corrected checker found a real case in the tree and proved the command remained present.
3. Every surviving top-level Rocq command matches the baseline after removing only the eight exact ledgered
   declarations.
4. Candidate-owned evidence is immutable in the freeze.
5. The implementation candidate’s metrics file is header-only.
6. The documentation-only freeze changes only its closed overlay.
7. The README now states the accepted A006 image topology.
8. The duplicate module and tool inventory left `CLAUDE.md`.
9. The stale repository measurement left `.editorconfig`.
10. File-purpose rows now state distinct present roles.
11. The second semantic `.v` comment pass reduced the tree further.
12. The generated module and reviewed runtime output remain unchanged.
13. The reported forced-uncached proof and end-to-end runs remain valid evidence.

Independent review of the uploaded freeze found:

```text
source-diet self-test                         green
source-diet snapshot policy check             green
D-07 Human Acts controls and generated view   green
D-24 reference controls and relation          green
closure-ledger generated view                 green
claim-matrix controls and all required rows   green
A005 naming snapshot check                    green
OCaml-origin gate                             green
generated-output gate                         green
pinned-target Go build                        green
runtime stdout, stderr, and exit               exact goldens
```

The reviewer also compared the accepted pre-M1 `.v` tree to the uploaded freeze with the repaired command model:

```text
23 .v files: every surviving declaration identical; 8 complete ledgered removals
```

Generated hashes remain:

```text
go.mod   d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa
main.go  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

Rocq, Dune, Docker, extraction, the plugin, and the real staged hook are not installed in the reviewer runtime.
The freeze’s committed forced-uncached evidence remains the evidence for those paths. The mutation harness was
not rerun to completion in the reviewer runtime; the freeze records the complete run.

---

# 3. Blocking finding — M1’s temporary exit evidence became a permanent repository freeze

## 3.1 Contract violated

This violates:

- M1 strict scope: the baseline, metrics, file-disposition, and declaration-deletion ledgers are temporary review
  evidence;
- M1 canonical-data law: Git history owns candidate evidence after acceptance, while only the comment-exception
  ledger is permanent;
- M1 purpose: remove maintenance cost without preventing later accepted work;
- M1-03, M1-11, M1-12, M1-14, and M1-15;
- the M-series dependency: M2 must be able to add its measured report, and later checkpoints must be able to add
  proved Rocq declarations.

This is not M3 tool factoring. It is a direct defect in the permanent path M1 installs and a required dependency
for leaving M1.

## 3.2 Current permanent path

`make check` depends on `diet`.

The current `diet` target runs:

```text
source-diet.py --self-test
source-diet.py --check
source-diet.py --against-baseline
source-diet.py --disposition-exact baseline
source-diet.py --code-identical baseline
```

The staged pre-commit path runs:

```text
source-diet.py --self-test
source-diet.py --check
source-diet.py --disposition-exact baseline
```

`--check` itself loads `M1_FILE_DISPOSITION.tsv` and checks every current file against it.

This means the ordinary permanent build path does not enforce only the accepted source-comment law. It also
enforces the historical M1 candidate boundary forever.

## 3.3 Consequences reproduced independently

Adding a valid future M2 report file to a copy of the accepted tree fails immediately:

```text
.review/M1_FILE_DISPOSITION.tsv:
current file has no disposition row: .review/M2_BUILD_OBSERVATORY.md
```

Adding a valid new Rocq declaration fails the permanent code-identity relation because that declaration did not
exist at the M1 baseline.

The permanent direction check also requires repository bytes to remain below the M1 baseline and the M1-specific
zero conditions to remain true under the original metric interpretation.

Therefore:

- M2 cannot add its report without falsifying or rewriting M1 evidence;
- later checkpoints cannot add a Rocq declaration;
- every future file must masquerade as an M1-created file in an M1 ledger;
- temporary M1 evidence cannot retire to Git history;
- `make check` enforces “the repository never moves beyond M1.”

A checkpoint-exit proof is not a permanent language law.

## 3.4 Why the existing exception does not save this

The contract says candidate-owned evidence may remain after acceptance “unless a live gate still needs one.”

Do not use that clause to preserve this topology. A gate created only to keep temporary M1 evidence alive does
not manufacture a present purpose for that evidence. The permanent comment gate needs the comment law and the
comment-exception ledger. It does not need the M1 baseline, metric table, file-disposition table, deletion
ledger, candidate identity, or code freeze.

---

# 4. Required end state

## 4.1 Permanent source-diet policy

The permanent source-diet path must enforce only the continuing policy:

1. enumerate the exact working tree or exported staged snapshot and fail closed;
2. reject zero `.v` files;
3. lex nested Rocq comments and strings correctly;
4. enforce the one-line, 120-character, one-sentence current-fact law;
5. reject the permanent prohibited comment classes;
6. check `M1_COMMENT_EXCEPTIONS.tsv` in both directions;
7. fail on unreadable or invalid source;
8. run its permanent self-tests and permanent mutation controls.

It must permit:

- a new non-`.v` file;
- a new `.v` module;
- a new declaration in an existing `.v` file;
- a larger repository;
- a changed theorem or proof authorized by a later checkpoint;
- a later checkpoint’s own evidence files;

provided the new `.v` comments obey the permanent comment law.

The permanent path judges comments. Rocq and the active checkpoint judge new code.

## 4.2 Permanent commands

After repair 3:

```make
diet:
	python3 tools/source-diet.py --self-test
	python3 tools/source-diet.py --check
```

`make check` may continue to depend on `diet`.

The staged hook runs the staged copy of those same two permanent modes against the exported staged tree.

Remove these M1-exit modes from `make diet` and from the staged hook:

```text
--against-baseline
--disposition-exact baseline
--code-identical baseline
```

Do not replace them with another baseline, allowlist, compatibility switch, or checkpoint-name conditional.

## 4.3 M1-only exit evidence

M1 still needs exact review evidence before acceptance.

Retain one explicit, review-only command:

```text
python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref <new candidate>
```

That command continues to prove:

- the baseline seal;
- exact baseline and candidate metrics;
- exact file disposition;
- exact deletion ledger;
- exact surviving Rocq commands;
- candidate-owned evidence immutability;
- the closed freeze overlay;
- the required M1 metric direction.

It is invoked for the M1 candidate and freeze. It is not a prerequisite of ordinary `make check`, a later
checkpoint, or an ordinary staged commit after M1 acceptance.

## 4.4 Self-test and mutation separation

Separate permanent policy controls from M1 exit-evidence controls.

A permitted shape is:

```text
--self-test       permanent source-comment policy controls
--m1-self-test    M1 baseline/candidate/freeze evidence controls
```

`--verify-m1-evidence` may run `--m1-self-test` itself or the freeze procedure may run both explicitly.

The permanent `make diet`, `make check`, and hook run only the permanent controls.

`tools/gate-mutation-test.py` must likewise distinguish:

- permanent source-comment helpers, which remain in the normal mutation run;
- M1 exit-evidence helpers, which run only in the explicit M1 review-evidence run.

Do not leave M1-only mutations in the permanent FCB gate merely to give M1-only helpers a consumer.

Do not refactor the general mutation architecture. M3 owns that. Add only the narrow grouping needed to make the
lifetime boundary true.

## 4.5 Permanent `--check` must not consult temporary M1 files

`source-diet.py --check` must not read or validate:

```text
.review/M1_BASELINE.tsv
.review/M1_METRICS.tsv
.review/M1_FILE_DISPOSITION.tsv
.review/M1_DECLARATION_DELETIONS.tsv
.review/M1_OBLIGATION_MATRIX.tsv
the M1 candidate ref
the M1 freeze state
```

It reads:

```text
the current .v files
.review/M1_COMMENT_EXCEPTIONS.tsv
```

and any permanent policy data explicitly accepted by the current contract.

Rename the exception ledger later only under a separately reviewed current-authority edit. Do not add that churn
to repair 3.

---

# 5. Acceptance-closeout compatibility

Repair 3 must leave M1 in a state where Rob’s later M1 acceptance closeout needs no functional gate edit.

After Rob accepts M1, the closeout can retire temporary M1 evidence to Git history:

```text
.review/M1_BASELINE.tsv
.review/M1_METRICS.tsv
.review/M1_FILE_DISPOSITION.tsv
.review/M1_DECLARATION_DELETIONS.tsv
.review/M1_OBLIGATION_MATRIX.tsv
.review/M1_IMPLEMENTATION_REPAIR_3.md
```

The M1 contract and review basis may retire when the M2 authority commit removes their last live references.
`M1_COMMENT_EXCEPTIONS.tsv` remains because the permanent comment gate consumes it.

The closeout must not need to change:

```text
tools/source-diet.py permanent policy behavior
Makefile diet/check wiring
.githooks/pre-commit permanent policy behavior
```

M1-only replay modes inside `source-diet.py` may remain dormant until M3 classifies or deletes them. Record that
tool-internal cleanup for M3; do not expand repair 3 into a general tool split.

## 5.1 Required transition controls

Add must-accept controls proving the permanent policy passes when:

- all temporary M1 evidence files are absent;
- a new non-`.v` checkpoint report exists;
- a new `.v` file exists with compliant comments;
- an existing `.v` file contains a new declaration with compliant comments;
- repository bytes increase.

Add must-fail controls proving:

- a new `.v` comment violates the permanent comment law;
- an exception row is missing or orphaned;
- the permanent path still calls a baseline, disposition, deletion, metric, candidate, or freeze check;
- the staged permanent path still calls one of those checks.

Add M1-only controls proving the explicit exit verifier still rejects:

- a changed surviving proof;
- an unledgered declaration deletion;
- false metrics;
- false file disposition;
- a freeze edit outside the closed overlay.

Every new helper is mutation-proved under the correct permanent or M1-only group. A skipped or vacuous control
cannot count as passed.

---

# 6. Contract and matrix changes

Update `.review/M1_SOURCE_DIET.md` to state the lifetime boundary directly:

> The permanent source-diet gate enforces the `.v` comment policy and exception relation only. Baseline,
> metric-direction, file-disposition, deletion-ledger, code-identity, candidate, and freeze checks are M1 exit
> evidence. They run for M1 review and do not constrain later accepted checkpoints.

Remove any text suggesting that a self-created live gate may preserve temporary candidate evidence after M1.

Reopen at least:

```text
M1-03
M1-11
M1-12
M1-14
M1-15
```

Close them only when the permanent path, M1-only path, transition controls, candidate, and freeze all exist.

The candidate/freeze ownership rules from repair 2 remain unchanged.

No FCB amendment is required. Governance D-27, D-28, and the accepted M1 contract already require a mechanical
cleanup which permits the mandatory later sequence.

---

# 7. Nonblocking finding — stable prose must name identities

Rob expressly directed that this rule enter the next review and **must not block M1**.

Add this stable finding to `.review/M_SERIES_PLAN.md` under Deferred M3 findings, using the ID:

```text
M3-FRAGILE-PROSE
```

Exact rule:

> Stable prose names identities, not mutable positions or hand-maintained cardinalities. Prefer stable IDs,
> declaration names, typed paths, anchors, canonical registries, and exact Git objects. Tools may report current
> counts and line numbers as diagnostics. A numeric cardinality belongs in normative prose only when the
> cardinality itself is fixed and machine-checked.

M3 must audit:

- copied current file, row, control, surface, component, and obligation counts;
- source or document line-number references;
- “first N lines” and other positional assumptions;
- list-position identity;
- prose which restates a count already owned by a registry or generated view.

This finding is real but nonblocking for M1.

The current freeze demonstrates the risk: its hand-written commit summary reports repository, archive, and review
byte counts which disagree with the exact generated `M1_METRICS.tsv`. The canonical generated table is the review
evidence; the immutable commit prose is not current authority. Do not rewrite history and do not block M1 on that
prose.

Prefer:

```text
all required obligations
the exact repository inventory
the entries in <canonical registry>
the declaration named <stable name>
the anchor <stable ID>
```

over copied counts or positions.

Do not add a generic number scanner. M3 must classify actual ownership and replace fragile identity with stable
identity.

---

# 8. Strict-scope disposition table

| Finding | Contract violated | Blocks M1 | Mandatory owner |
|---|---|---:|---|
| Permanent `make diet` freezes bytes and Rocq commands at the M1 baseline | M1 temporary-evidence law; M1-11, M1-14, M1-15; required M2 dependency | **yes** | M1 repair 3 |
| Permanent staged hook requires the M1 file-disposition relation | same | **yes** | M1 repair 3 |
| M1-only mutation checks remain in the permanent gate path | M1 temporary-evidence law; M1-12 | **yes** | M1 repair 3 |
| Copied counts, line positions, and list positions in prose or tools | none required for M1 acceptance by Rob’s direction | no | M3-FRAGILE-PROSE |
| Source-diet tool contains dormant M1 replay modes after acceptance | none in M1 once permanent paths are separated | no | M3 tool audit |
| Build timing and dependency cost | none in M1 | no | M2 |
| General host/container placement and gate factoring | none in M1 | no | M3 |
| Proof-module split, cache layout, and build-graph refactor | none in M1 | no | M4 after plan approval |
| `life.md` content | none; separately authorized character continuity | no | preserve unchanged |

Do not pull the nonblocking rows into repair 3.

---

# 9. Allowed changes

Repair 3 may change only what is required to separate permanent source-comment policy from M1 exit evidence:

```text
tools/source-diet.py
tools/gate-mutation-test.py
Makefile
.githooks/pre-commit
.review/M1_SOURCE_DIET.md
.review/M1_IMPLEMENTATION_REPAIR_3.md
.review/M1_OBLIGATION_MATRIX.tsv
.review/M_SERIES_PLAN.md
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
.review/M1_METRICS.tsv
.review/M1_FILE_DISPOSITION.tsv, only if exact candidate bytes require regeneration
typed reference rows and owner markers required by the active repair transition
```

The freeze may touch only the accepted closed overlay.

Do not change:

- any surviving `.v` source, comment, declaration, theorem, proof, constructor, or notation;
- any OCaml source;
- Docker or Dune;
- generated Go or goldens;
- `README.md`, `CLAUDE.md`, `.editorconfig`, or other already-completed M1 prose;
- `life.md`;
- semantic or proof architecture;
- M2, M3, M4, or C5 implementation.

The new M3 finding is a plan assignment only.

---

# 10. Candidate and freeze topology

## Implementation candidate

The new implementation candidate contains:

- the permanent/M1-only mode separation;
- permanent Make and hook wiring;
- grouped permanent and M1-only controls;
- the exact M1 candidate-owned evidence;
- the active repair directive;
- an open matrix and closed review request;
- header-only metrics.

## Documentation-only freeze

After committing the candidate:

1. run the permanent working-tree and staged policy paths;
2. run the complete explicit M1 evidence suite against the baseline and exact candidate;
3. generate exact metrics from the two refs;
4. close the matrix;
5. update `NEXT_STEPS` and `REVIEW_REQUEST`;
6. add the one nonblocking M3 assignment if it did not land in the candidate;
7. commit only the closed freeze overlay.

Nothing may follow the freeze.

---

# 11. Verification

Run:

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

Run the real staged pre-commit hook without bypassing it.

Run the M1-only evidence controls and exact verifier explicitly:

```text
python3 tools/source-diet.py --m1-self-test

python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref <new candidate>
```

If a different exact flag name is retained, keep the same separation and document it.

Also prove:

1. `make diet` contains no M1 baseline, metric, disposition, deletion, code-identity, candidate, or freeze check.
2. The staged source-diet path contains none of those checks.
3. Removing the temporary M1 evidence files in a fixture leaves the permanent source-diet gate green.
4. Adding a clean M2 report file leaves the permanent gate green.
5. Adding a clean future `.v` declaration leaves the permanent gate green.
6. A bad new `.v` comment fails both permanent modes.
7. The explicit M1 exit verifier still establishes all current M1 evidence.
8. All surviving Rocq commands remain identical to the baseline after the eight ledgered deletions.
9. Generated bytes and runtime observations remain exact.
10. The whole-theory assumption audit and readable surfaces remain green.
11. C4 and M0 remain accepted.
12. M2 through M4 and C5 remain forbidden.
13. `life.md` remains byte-identical.

Do not create a prose-heavy closure audit. The exact contract, controls, ledgers, command output, Git diff, and
commit messages are the evidence.

---

# 12. Definition of done

Repair 3 is complete only when:

- the permanent source-diet path enforces only the permanent comment policy;
- M1 exit evidence is explicit and review-only;
- future files and Rocq declarations are not rejected merely because they postdate M1;
- temporary M1 evidence can retire after acceptance without any functional gate edit;
- permanent and M1-only controls are separated and mutation-proved;
- the exact existing M1 evidence remains green;
- `M3-FRAGILE-PROSE` is recorded as nonblocking;
- no forbidden source or semantic change occurs;
- one exact implementation candidate is committed;
- one later documentation-only freeze names it;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M1.
