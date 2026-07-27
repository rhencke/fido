# C4 IMPLEMENTATION REVIEW — BLOCKING

## Repair 20: make A005 and D-24 complete, then close C4

Repository:

```text
rhencke/fido
```

Uploaded review snapshot:

```text
fido-main - 2026-07-26T200915.283.zip
```

Documentation freeze:

```text
cc63a78c3729772b9114b20e653942cda23cc53a
```

Exact implementation candidate reviewed:

```text
0ffdc5f7019204a868d75ef709a16fb69a9979d5
```

Disposition:

```text
BLOCKING
```

Candidate `0ffdc5f7019204a868d75ef709a16fb69a9979d5` is the twenty-first blocked C4
implementation candidate. Freeze `cc63a78c3729772b9114b20e653942cda23cc53a` is documentation only and is
not a separate candidate.

C4 remains unaccepted. Rob alone accepts C4.

Repair 20 is the sole C4 implementation task. C5, checkpoint-definition Step 0, M1–M4 implementation, broad
cleanup, proof partitioning, and feature work remain forbidden until the sequence authorized below permits them.

This directive also installs the already accepted post-C4 M-series authority. Installing that authority is
required even though C4 is blocked. Implementing M1–M4 remains forbidden until C4 is accepted.

---

# 1. Governing authority

Use one exact Git ref for every file consulted.

Read, from the same ref:

```text
.review/fcb/current/INDEX.md
.review/fcb/current/FIDO_FCB_INDEX.md
.review/fcb/current/FIDO_FCB_GOVERNANCE.md
.review/fcb/current/FIDO_FCB_ARCHITECTURE_CHARTER.md
.review/fcb/current/FIDO_FCB_FIXED_POINTS.md
.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv
.review/fcb/current/FIDO_FCB_REFERENCES.tsv
.review/fcb/current/FIDO_FCB_ROADMAP.md
.review/fcb/current/FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md
.review/fcb/current/FIDO_FCB_MODEL_OPERATIONS.md
.review/NEXT_STEPS.md
.review/OPEN_QUESTIONS.md
.review/REVIEW_REQUEST.md
```

The binding decisions remain:

```text
A001 / D-22 — intrinsic static-capability provenance
A002 / D-23 — Git-canonical FCB storage
A003          — living documentation
A004 / D-24 — complete Git-resolvable living corpus
A005 / D-25 — scoped name ownership
A006 / D-26 — intrinsic Emit image mint
D-07          — generated Human Review Index
```

This review additionally records Rob’s accepted amendment:

```text
FCB-A007-POST-C4-MECHANICAL-SERIES
```

Human acceptance token:

```text
FCB-A007-post-C4-mechanical-series
```

The source human direction, in the authoritative primary review thread, was:

> Next round let's install the M series in the repo regardless of review.

Rob then confirmed the resulting sequence and strict comment rule. No further human confirmation is required to
install A007.

---

# 2. Executive finding

Repair 19 made real progress and retained the correct C4 architecture.

The review found no new need to redesign:

- `Compilable.Core`;
- `Compilable.Program`;
- `Compilable.Failure`;
- `Compilable.Facts`;
- `Safe.Program`;
- `Emit.Mint.Token`;
- `Emit.Image`;
- the one compile path;
- accepted and rejected retained-object roots;
- exact source occurrence and cause retention.

The accepted and rejected fixture topology now retains the exact source locals, exact keys, exact work members,
exact cause objects, exact diagnostics, and one exact returned capability or failure. The seal controls now load
the module and public sentinel before probing the hidden name. The generated Go remains byte-identical.

Two closure claims are still false-green:

1. D-24 does not scan all current authority documents.
2. A005 does not detect a multiline UpperCamelCase `Local Notation`.

Both defects were reproduced against the exact candidate. They are enforcement defects, but each disproves a
public completion claim and therefore blocks C4.

No FCB amendment is required for either repair. A004, A005, D-24, D-25, and the repair-19 contract already
require the correct result.

---

# 3. Evidence independently checked

The following host-feasible checks passed against the uploaded snapshot:

```text
make names
make fcb
make claims
tools/ocaml-origin-gate.sh
tools/generated-output-gate.sh
GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build ./...
the generated executable against reviewed stdout/stderr/exit goldens
```

Generated hashes remained:

```text
go.mod   d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa
main.go  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

The review environment does not contain Docker, Rocq, Dune, the OCaml compiler, or the pinned EditorConfig
executable. The reported full proof, extraction, Buildx, plugin, fresh e2e, formatting, and staged-hook results
remain candidate evidence and must be rerun by Claude under the pinned environment.

---

# 4. BLOCKER A — D-24 still scans a hard-coded subset of authority

## 4.1 The false claim

Governance D-24 requires a complete relation in both directions:

1. every typed reference row resolves and has one bound owner marker;
2. every operational repository path in the live authority corpus has exactly one typed row.

Repair 19 also requires the current repair directive, closure audit, obligation matrix, functional contract,
accepted review basis, open questions, and review request to be correctly typed.

The current gate validates manifest rows correctly, but it defines the scanned authority corpus in Python as a
hard-coded list:

```python
CORPUS_GLOBS = ('.review/fcb/current/*.md',)
CORPUS_FILES = (
    '.review/NEXT_STEPS.md',
    '.review/OPEN_QUESTIONS.md',
    '.review/REVIEW_REQUEST.md',
    'CLAUDE.md',
)
```

The active repair directive is explicitly named as `Authority:` by `NEXT_STEPS`, but the gate does not scan it.
The functional contract and accepted review basis are also outside the scanned set.

A typed row proves that a path exists. It does not prove that the target document’s own operational references
are complete.

## 4.2 Reproducer

A temporary copy of the exact snapshot was changed by appending one undeclared, nonexistent review-rooted path
to the active repair directive.

The gate returned success:

```text
fido: fcb-reference gate OK — 53 declared reference(s): 51 resolve in this tree,
2 explicitly typed off-tree; every row has one bound owner marker;
17 live authority document(s) name no undeclared operational path
```

The injected path was never read.

This directly violates repair-19 obligations 20, 21, and 24 and Governance D-24.

## 4.3 Root repair — one manifest owns both references and authority membership

Keep one typed-reference manifest. Do not add a second hand-maintained authority list.

Extend the canonical reference schema with one closed field:

```text
corpus_role
```

The complete schema becomes:

```text
id
kind
path
availability
owner
owner_anchor
corpus_role
```

Allowed `corpus_role` values:

```text
authority
reference
```

Rules:

- `authority` is valid only for a present, readable UTF-8 repository file.
- `reference` validates existence and ownership but does not make the target a current authority document.
- off-tree and directory rows must be `reference`.
- the reference manifest itself is an `authority`.
- every current normative FCB source is an `authority`.
- generated human or ledger views may be `reference` when their canonical data source is the authority.
- `NEXT_STEPS`, `OPEN_QUESTIONS`, `REVIEW_REQUEST`, and `CLAUDE.md` are authorities.
- the active repair directive named by `NEXT_STEPS` is an authority.
- the functional contract and accepted review basis named by `REVIEW_REQUEST` are authorities.
- the accepted M-series plan installed by A007 is an authority.
- closure audits, obligation matrices, generated views, and other evidence are classified by their real role.
  Do not label evidence as authority merely to increase the count.

`corpus_documents` must be derived from manifest rows with `corpus_role = authority`.

Delete `CORPUS_GLOBS` and `CORPUS_FILES` as the semantic authority for corpus membership. The code may retain the
single stable bootstrap path needed to load the manifest, but it may not retain a parallel list of current
authority documents.

## 4.4 Required structural checks

The gate must also validate the declarations which assign authority:

- every path in the FCB Index live-file table has the role stated by that table;
- the document named after `Authority:` in `NEXT_STEPS` has an `authority` row;
- the `contract:` and `review_basis:` paths in `REVIEW_REQUEST` have `authority` rows;
- the M-series plan has an `authority` row;
- an authority role cannot point to a directory, symlink, undecodable file, missing file, or off-tree target;
- removing or downgrading one required authority row fails;
- adding a new authority row causes its target to be scanned without a Python source edit.

The relation remains complete in both directions:

```text
MANIFEST -> TARGET
AUTHORITY TARGET -> MANIFEST
```

## 4.5 Required controls

Add must-fail controls for:

1. a dangling operational path injected into the active repair authority;
2. a dangling operational path injected into the functional contract;
3. a dangling operational path injected into the accepted review basis;
4. the active repair row marked `reference`;
5. the contract row marked `reference`;
6. the review-basis row marked `reference`;
7. an authority row whose target is a directory;
8. an authority row whose target cannot be decoded;
9. an authority row whose target cannot be read;
10. a newly added authority file containing an undeclared path.

Add a must-accept control showing that a valid newly added authority file is discovered and scanned with no
change to Python constants.

Each control must pin the reason for failure. A generic nonzero exit is not enough.

The working-tree check and exported staged-snapshot hook must use the same manifest-derived authority set.

## 4.6 Live-document cleanup

The active Repair 20 authority must contain current instructions only.

Do not carry superseded repair-document paths, old closure audits, or synthetic missing-path examples as live
prose. Git history owns them. Gate self-tests may create synthetic paths inside temporary test data.

Rewrite or type every path-like phrase in the functional contract and review basis. Do not weaken the scanner
with an exception list to preserve ambiguous prose.

---

# 5. BLOCKER B — A005 misses multiline `Local Notation`

## 5.1 The false claim

Repair 19 correctly deleted all live UpperCamelCase local aliases and added this class rule:

> A certified Rocq module may not introduce an UpperCamelCase `Local Notation`.

The implementation checks that rule one physical line at a time:

```python
re.match(r"\s*Local\s+Notation\s+([A-Z][A-Za-z0-9_']*)\s*:=", line)
```

Every negative control also places `Local Notation`, the alias name, and `:=` on one line.

## 5.2 Reproducer

A temporary copy of a certified module was given this declaration:

```coq
Local Notation
  HiddenAlias := nat (only parsing).
```

Both the naming self-tests and snapshot scan reported success.

The declaration is valid statement-shaped input for the gate, violates the accepted class rule, and is invisible
only because the checker validates a line rather than the Rocq statement.

## 5.3 Root repair

Use the existing stripped-code statement stream. Do not add another line scanner.

Parse every `Local Notation` statement before validating its alias name.

The extractor must accept layout variation first, then judge the identifier:

- indentation before `Local`;
- a newline between `Local` and `Notation`;
- a newline between `Notation` and the identifier;
- a newline between the identifier and `:=`;
- supported Rocq attributes before the declaration;
- ordinary spacing and comments already removed by the lexical pass.

The class check then rejects an UpperCamelCase identifier.

Do not make extraction conditional on the first character already satisfying the rule. That was the constructor
and record-field failure mode and must not recur.

Lowercase resolver-specialized executable notations remain allowed.

## 5.4 Required controls

Add must-fail controls for at least:

```coq
Local Notation
  HiddenAlias := nat (only parsing).
```

```coq
Local
Notation HiddenAlias := nat (only parsing).
```

```coq
Local Notation HiddenAlias
  := nat (only parsing).
```

```coq
  Local Notation
    HiddenAlias
      := nat (only parsing).
```

Add must-accept controls for lowercase multiline notations in the same layouts.

Add repository-level mutation controls which insert a multiline alias into a tracked certified module and run:

```text
working-tree mode
snapshot mode
```

Both must fail naming the alias and the exact file.

The self-test count must include only executed controls. No control may skip and count as passed.

---

# 6. C4 surfaces which must not regress

Repair 20 must preserve the current architecture and proof topology.

## 6.1 Static provenance

- one exact retained `Compilable.Core`;
- input, phase, package refs, layout, plan, raw diagnostics, and final diagnostics built once;
- accepted and rejected decisions indexed by that exact core;
- no equality to rerunning a builder as provenance;
- no independently constructible peer core.

## 6.2 Capability topology

- `Compilable.compile` remains the sole `Program` and `Failure` mint;
- accepted `Facts` remain an exact view of the accepted core;
- `Safe.certify` remains the sole `Safe.Program` mint;
- `Emit.Mint.issue` remains the sole image-authority mint;
- `Emit.Image` remains a reducible carrier, not an arbitrary-byte authority;
- every raw authority constructor remains inaccessible.

## 6.3 Returned-object fixtures

- one accepted root over one exact returned `cp`;
- one rejected root over one exact returned `fail`;
- exact source locals 11, 9, 7, and 5 remain in the public propositions;
- exact retained work members, keys, occurrences, causes, predecessors, outcomes, trace, and diagnostics remain;
- safety and emission consume the same accepted capability;
- no prohibited builder enters either root.

## 6.4 No peer or compatibility path

- no legacy result classifier;
- no shape-only cause peer beside exact occurrence facts;
- no old alias, wrapper, re-export, or compatibility module;
- no consumer-free theorem kept because a gate names it;
- no second source, typed AST, compiler, evaluator, diagnostic authority, or rendering path.

## 6.5 Generated and external behavior

- generated `go.mod` and `.go` bytes remain byte-identical;
- reviewed stdout, stderr, and exit stay exact;
- extraction and OCaml remain transport-only;
- no C5 or M-series implementation enters this repair.

---

# 7. Accepted FCB Amendment A007 — Post-C4 Mechanical Series

## 7.1 Amendment identity

```text
FCB-A007-POST-C4-MECHANICAL-SERIES
```

Status:

```text
ACCEPTED
```

Human owner:

```text
Rob
```

Acceptance token:

```text
FCB-A007-post-C4-mechanical-series
```

Date:

```text
2026-07-26
```

Author:

```text
Primary ChatGPT Fido review thread
```

## 7.2 New information

The current repository carries a large amount of source prose, proof text, and ad hoc build tooling. Much of the
prose records superseded design history which Git already preserves. Full builds approach two to three minutes,
and the project lacks one measured account of module cost, dependency fan-out, edit frequency, cache behavior,
and duplicated gate work. Auxiliary tools and Make/Buildx duties have accumulated without one owned build
architecture.

This mechanical debt raises review cost, model-token cost, feedback time, and the risk that stale prose hides
the current system. The permanent C5 `Machine` base should not be frozen on top of that avoidable debt.

## 7.3 Settled sequence

After C4 acceptance, and before checkpoint-definition Step 0 for C5, execute:

```text
C4 acceptance closeout
→ M1 Source Diet
→ M2 Build Observatory
→ M3 Tool and Build Architecture Audit
→ Rob approves the exact M4 plan
→ M4 Mechanical Refactor
→ checkpoint-definition Step 0
→ C5 Machine base
```

While C4 remains unaccepted:

```text
M1, M2, M3, and M4 implementation are forbidden.
```

Installing this amendment and the M-series plan now does not authorize their implementation.

## 7.4 Governance D-27 — exact standing law

Add:

### D-27 — Mechanical debt is removed before the permanent runtime base.

**Standing law:** After C4 acceptance and before C5 checkpoint-definition Step 0, Fido completes M1 through M4
in order. The M-series is mechanical: it may delete dead text and code, measure and reshape build dependencies,
and refactor proof units and tooling, but it may not change Go meaning, the accepted or rejected program sets,
diagnostic results, public correctness guarantees, trust boundaries, or generated bytes.

Git owns archaeology. Source prose states current local facts only and remains only when its removal would make
the nearby code, proof, invariant, or boundary harder to understand correctly.

A fast partial check must identify itself as partial. It never substitutes for the full acceptance gate.

Semantic ownership is not split merely to create parallel work. Build and cache changes require measured
before-and-after evidence and complete cache keys. M4 begins only after M2 and M3 evidence exists and Rob accepts
the exact refactor plan.

**Rationale:** Maintenance cost is a real correctness cost when stale prose obscures current authority, large
serial units delay feedback, or duplicated checks create divergent build paths. Mechanical cleanup must reduce
that cost without weakening evidence or changing semantics.

## 7.5 Amendment effects

| Field | Disposition |
|---|---|
| Governance decision | Add `D-27` |
| Roadmap | Insert M1–M4 between C4 closeout and C5 Step 0 |
| Fixed points | None reopened; M1–M4 must preserve all fixed points |
| Closure rows | None changed |
| Latitude rows | None changed |
| Acceptance-gate rows | None changed |
| Go meaning | Unchanged |
| Accepted/rejected program sets | Unchanged |
| Diagnostics | Unchanged |
| Public theorem guarantees | Must not weaken |
| Generated Go | Byte-identical through M1–M4 |
| Target/toolchain policy | Unchanged |
| OCaml trust boundary | Unchanged |
| Human act | Add deferred `M4-PLAN-APPROVAL` |
| New live authority | `.review/M_SERIES_PLAN.md` |

Create the accepted amendment record under the existing amendment directory.

---

# 8. M-series plan to install now

Create `.review/M_SERIES_PLAN.md` as a current authority and bind it in the typed reference manifest.

The plan must contain the following contracts.

## 8.1 M1 — Source Diet

Purpose:

```text
Remove every non-load-bearing byte without reducing accuracy, proof strength, or current comprehension.
```

Git owns history. Current source must not explain what the code used to be.

### Default `.v` comment law

Apply to every tracked `.v` file, including proof gates and e2e fixtures:

- one physical line;
- at most 120 characters, including comment delimiters;
- at most one sentence;
- one current local fact;
- no repair, migration, candidate, former-name, or historical narrative.

Adjacent comment blocks separated only by whitespace count as one logical block. Claude may not split a
paragraph into many short comments.

Comments which only restate a name, definition, theorem statement, or obvious proof step are deleted.

Section banners, comment art, theorem inventories, consumer lists, repeated “one authority” claims, and prose
which belongs to the FCB are deleted.

### Rare exception law

A longer comment survives only when it explains one of these current needs:

```text
invariant-not-expressed-by-type
trust-or-effect-boundary
non-obvious-proof-plan
rocq-limitation-forcing-shape
```

Each exception:

- is attached to one named declaration or module;
- has one row in a canonical checked exception ledger created by the M1 contract;
- uses at most four physical lines;
- keeps every line at or below 120 characters;
- states why the type, theorem statement, or name cannot carry the fact;
- contains no archaeology.

The gate is bidirectional:

- an exception comment without a row fails;
- a row without its exact comment fails;
- a row whose declaration no longer exists fails;
- duplicate ownership fails;
- an over-limit exception fails.

A large exception ledger is evidence that M1 failed.

### File and declaration law

Delete every file, definition, theorem, fixture, alias, wrapper, script, report, and abstraction which is not:

1. on the certified correctness path;
2. enforcing a proved restriction or live governance rule;
3. defining an explicit unsupported boundary;
4. required evidence for a current accepted contract.

A gate entry does not give a theorem purpose.

Do not minify proofs, shorten good names, hide structure in broad automation, or merge distinct concepts to
reduce bytes.

### M1 evidence

Capture before and after:

- total tracked bytes;
- bytes by file and file kind;
- `.v` comment bytes;
- `.v` non-comment bytes;
- live-document bytes;
- tool/build bytes;
- declaration and theorem counts;
- compressed archive size;
- every deleted file and declaration with its exact disposition;
- every surviving comment exception.

There is no arbitrary byte quota. Every byte must earn its place.

M1 is a separate reviewed candidate.

## 8.2 M2 — Build Observatory

M2 measures. It does not restructure.

Run in the pinned environment and record:

- cold full-build wall and CPU time;
- warm no-change time;
- common incremental times after touching each root module;
- per-module Rocq compile time;
- Dune dependency graph;
- critical path;
- downstream rebuild set for each module;
- Docker stage timing and cache hit/miss state;
- extraction, plugin, Go, e2e, and every policy-gate time;
- peak memory where practical;
- repeated work across Make targets, Buildx stages, and the hook.

Analyze Git history over the accepted implementation range:

- edit frequency by file;
- files changed together;
- common edit shapes;
- weighted rebuild cost: edit frequency multiplied by downstream build cost;
- large serial units;
- false dependencies and broad imports;
- proof families which can check independently without splitting semantic ownership.

Distinguish:

```text
partial edit feedback
full acceptance
cold build
warm build
no-op build
```

Under one minute for the common edit loop is a goal, not permission to omit evidence.

M2 produces evidence and recommendations only. It is a separate reviewed candidate.

## 8.3 M3 — Tool and Build Architecture Audit

Inventory every:

- Python tool;
- shell tool;
- Make target;
- pre-commit action;
- Docker stage;
- Dune alias;
- Rocq gate;
- extraction step;
- generated-output check;
- staged-snapshot check.

For each, record:

- exact purpose;
- contract or policy enforced;
- inputs and outputs;
- environment;
- dependencies;
- cache inputs;
- failure behavior;
- negative controls;
- overlap with other checks;
- current owner.

Delete or propose consolidation for:

- duplicate scanners;
- weaker checks subsumed by stronger ones;
- repeated source-enumeration logic;
- host checks whose policy logic belongs in the pinned Buildx environment;
- targets which rebuild the same theory or artifact independently;
- helpers with no distinct invariant;
- ad hoc branches outside one acceptance graph.

Host work may read the Git index and export the exact staged snapshot. Proof and policy logic normally runs in
the pinned environment against that snapshot.

M3 must produce the exact proposed M4 graph and refactor plan. It does not implement the plan.

M3 is a separate reviewed candidate.

## 8.4 M4 — Mechanical Refactor

M4 starts only after Rob accepts the exact plan produced by M3.

The intended shape is:

```text
one exact source or staged snapshot
→ one pinned theory build
→ independent proof, assumption, transport, policy, and e2e branches
→ one full acceptance join
```

Requirements:

- one semantic owner for every definition and authority;
- split proof modules only where measured dependency savings exist;
- no duplicate definition or semantic peer;
- no cache key omits a real source, toolchain, flag, target, or environment dependency;
- no cached artifact from another snapshot is accepted;
- Make is a small user interface, not a second build graph;
- partial targets state that they are partial;
- the final whole-theory audit remains global;
- generated bytes remain exact;
- full before-and-after M2 measurements are repeated.

M4 is a separate reviewed candidate.

## 8.5 M-series acceptance gates

Every M candidate preserves:

- zero assumptions;
- all accepted public theorem guarantees;
- constructor and mint topology;
- exact accepted and rejected provenance;
- supported and rejected program sets;
- exact diagnostic results;
- extraction and transport behavior;
- OCaml transport-only status;
- negative client controls;
- generated Go bytes;
- reviewed runtime output;
- working-tree and staged-snapshot enforcement.

---

# 9. Required A007 repository changes

In the first documentation-only authority commit:

1. Install this Repair 20 directive as the sole active C4 repair.
2. Install the accepted A007 amendment record.
3. Add Governance D-27 and the A007 register row.
4. Create `.review/M_SERIES_PLAN.md`.
5. Update every accepted-amendment banner through A007.
6. Update the FCB Index live boundary and consultation map.
7. Update the Roadmap sequence.
8. Update the Checkpoint Authoring Guide with the M-series mechanical-change rules.
9. Update Model Operations with the sequencing and authority rules.
10. Update Fixed Points to state that A007 reopens none and M1–M4 preserve all.
11. Add the M-series plan to the typed reference manifest as an authority.
12. Add `M4-PLAN-APPROVAL` to `FIDO_FCB_HUMAN_ACTS.tsv` with status `DEFERRED`.
13. Regenerate the Human Review Index.
14. Update `NEXT_STEPS` so Repair 20 is the sole active implementation and M1–M4 remain forbidden.
15. Update `REVIEW_REQUEST` so no review is requested while Repair 20 is active.
16. Retire superseded repair and completion artifacts to Git history.
17. Keep `OPEN_QUESTIONS` current; do not add an answered M-series question.

This authority commit changes no Rocq, OCaml, Go, generated bytes, or gate behavior.

Run the current documentation and staged gates on that commit. Then begin Repair 20 implementation.

---

# 10. Repair 20 obligation matrix

Create one current matrix with stable obligation IDs.

At minimum:

```text
R20-D24-AUTHORITY-MANIFEST
R20-D24-ACTIVE-REPAIR-SCANNED
R20-D24-CONTRACT-SCANNED
R20-D24-REVIEW-BASIS-SCANNED
R20-D24-DYNAMIC-AUTHORITY-DISCOVERY
R20-A005-MULTILINE-LOCAL-NOTATION
R20-A005-WORKING-TREE-MUTATION
R20-A005-SNAPSHOT-MUTATION
R20-A007-INSTALLED
R20-NO-SEMANTIC-REGRESSION
R20-GENERATED-BYTES
R20-WHOLE-THEORY-ASSUMPTIONS
```

A row closes only when its exact public surface, adversarial control, and gate exist.

`REVIEW_REQUEST` may not move to requested while any row is open.

The matrix gate must verify definition sites and executable controls, not comments which mention their names.

---

# 11. Whole-system closure audit before freeze

After the two repairs turn green, audit the whole system again.

Inspect:

1. every public constructor and mint;
2. exact accepted and rejected retained-object flows;
3. every cause theorem’s public identity fields;
4. all builder and reconstruction calls after a capability is returned;
5. every compatibility or collapsed-result peer;
6. all live aliases and notations, including multiline statements;
7. every current authority document and its operational paths;
8. every tool, Docker, Make, Dune, extraction, OCaml, and staged path;
9. generated artifacts and runtime goldens;
10. all A007 documentation, without implementing M1–M4;
11. every completion claim against its exact theorem or executable control.

Run an uncached proof and pinned-Go e2e for the final audit.

The audit report must state what was observed in this candidate. It may not copy counts from an earlier repair.

Do not freeze merely because `make check` is green.

---

# 12. Required gates

Before freeze:

```text
make names
make fcb
make claims
make prove
make e2e
make check
make regenerate
make regen-guard
make fmt
make audit-fresh
the exact staged pre-commit hook without --no-verify
```

Also verify:

- working tree unchanged after regeneration;
- generated hashes equal the reviewed baseline;
- no untracked nonignored policy file escapes a gate;
- no M1–M4 implementation landed;
- no C5 type, relation, or feature landed.

---

# 13. Execution loop

Use:

```text
/loop 3m
```

Continue implementing, checking, auditing, and correcting until every Repair 20 and A007 installation obligation
is complete or a real blocker prevents progress.

Do not stop for:

- routine progress reports;
- partial completion;
- a green intermediate check;
- the A007 authority commit alone;
- one repaired false-green while the other remains;
- a candidate whose closure prose is stronger than its controls.

When complete or genuinely blocked, use the notification tool to notify Rob.

If blocked, report:

- the exact failed obligation;
- the smallest reproducer;
- the exact type, theorem, parser, gate, or authority topology involved;
- the exact governing FCB text;
- why the required design cannot satisfy it;
- the precise human decision required.

Do not improvise another architecture or weaken A004, A005, A007, D-24, D-25, or D-27.

---

# 14. Definition of done

Repair 20 is complete only when:

## A007

- A007 and D-27 are installed in Git;
- `.review/M_SERIES_PLAN.md` exists as a typed current authority;
- all FCB banners and affected documents include A007;
- `M4-PLAN-APPROVAL` appears in canonical human acts and the generated view;
- the Roadmap has the exact M-series sequence;
- `NEXT_STEPS` states that M1–M4 implementation remains forbidden until C4 acceptance;
- no M-series implementation has begun.

## D-24

- authority membership comes from the canonical typed manifest, not a hard-coded Python list;
- the active repair, functional contract, accepted review basis, M-series plan, and current FCB sources are scanned
  according to their real role;
- every authority target is readable, present, and UTF-8;
- every authority target’s operational paths have exactly one row;
- dynamic authority discovery works without a source edit;
- all required adversarial controls execute and pin their failure reason;
- working-tree and staged modes use the same authority relation.

## A005

- multiline UpperCamelCase `Local Notation` is detected as a statement;
- all layout variants are covered;
- lowercase multiline executable notations remain accepted;
- repository-level working-tree and snapshot mutations fail;
- no skipped control counts as passed.

## C4

- all Repair 19 retained results remain intact;
- the whole current theory is assumption-free;
- all constructor and mint controls are non-vacuous;
- all current documents state one truth;
- generated Go is byte-identical;
- full proof, extraction, Docker, OCaml, e2e, regeneration, formatting, and staged gates pass;
- no C5 or M-series implementation is present;
- the closure audit makes no claim stronger than its cited theorem or test;
- Claude notifies Rob that the candidate is frozen for human review.
