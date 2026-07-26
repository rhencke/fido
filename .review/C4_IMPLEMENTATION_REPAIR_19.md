# C4 IMPLEMENTATION REVIEW — BLOCKING

## Repair 19: complete A005, retain exact source occurrence in the public cause theorems, make the negative controls non-vacuous, and make D-24 complete

Repository:

```text
rhencke/fido
```

Uploaded review snapshot:

```text
fido-main - 2026-07-26T180259.867.zip
```

Exact implementation candidate under review:

```text
50c3bcc5b8eb2e47074352f5c9f0124e71509396
```

Documentation-only freeze:

```text
2b848871c7faf4a9586c8b20b4896e1ec543987c
```

Disposition:

```text
BLOCKING — twentieth blocked C4 implementation candidate
```

The documentation-only freeze is not a separate implementation candidate.

Original C4 baseline:

```text
8c9212a8c814c7a99a5e3ef1970a0ae32425a918
```

Binding functional contract:

```text
.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md
```

Accepted review basis:

```text
.review/REVIEW_BASIS.md
```

Governing accepted FCB amendments and decisions:

```text
A001 / D-22 — intrinsic static-capability provenance
A002 / D-23 — Git-canonical FCB storage
A003          — living documentation
A004 / D-24 — Git-resolvable living corpus
A005 / D-25 — scoped name ownership
A006 / D-26 — intrinsic Emit image mint
D-07          — discovered Human Review Index
```

C4 is not accepted.

C5, checkpoint-definition Step 0, post-C4 features, the broad source cleanup, and proof-module partitioning remain forbidden.

Automatic Codex review remains disabled.

---

# 0. Human disposition

Repair 18 made substantial progress and kept the core design intact.

Keep these results:

- `Compilable.Core`, `Program`, `Failure`, and `Facts` remain sealed.
- `Compilable.compile` remains the one static-capability mint.
- the core retains the exact input, phase, package map, layout, build plan, raw diagnostics, and final diagnostics;
- accepted and rejected paths retain the exact core;
- `Safe.Program` is sealed and `Safe.certify` is its mint;
- A006’s opaque, value-indexed `Emit.Mint.Token` remains the image authority;
- the reducible `Emit.Image` carrier remains distinct from the mint;
- `LegacyClass` and its result-classification closure remain deleted;
- the accepted and rejected root fixtures now bind one returned object each;
- D-07 now has a canonical Human Acts TSV and a generated Human Review Index;
- the generated Go bytes remain unchanged;
- the reported full proof, Docker, OCaml, extraction, e2e, regeneration, and staged checks are green.

The one-round closure experiment also found and deleted three dead theorem surfaces. That was useful.

The candidate is still blocked for six concrete reasons:

1. A005 is still incomplete. The exact fake local type and judgment aliases that the naming migration rejected remain live in `Compilable.v`, `Safe.v`, and `Render.v`, and the naming gate has no rule or control for them.

2. The accepted and rejected cause proofs use exact source locals internally but erase those identities from their public predicates. The theorem proof knows `int8` is local 11, `int16` is local 9, `int32` is local 7, and `int64` is local 5. The public fixture states only that some work member has a matching expression shape. That is a weaker theorem.

3. The constructor-opacity controls for `Safe` and `Emit` are vacuous. The shared `sealed` helper imports only `Syntax` and `Compilable`; it never loads `Safe` or `Emit`. Tests Y, Z, AA, AE, AF, and AG can therefore pass because the module itself is absent, not because its raw constructor is sealed.

4. The naming-gate unreadable-file self-test can print `SKIP`, count that skipped test as one of the five read/enumeration controls, and then report all 47 controls passed.

5. The D-24 reference manifest is not complete and the gate does not test completeness. The live authority names several operational repository paths which have no row. Adding a new dangling operational path to the FCB Index leaves the current gate green.

6. A stale `legacy-class` comment remains, and `deep_nested_ok_closure_at` remains as an explicitly weaker, consumer-free theorem whose only listed consumer is its assumptions-gate line. A gate is not a semantic purpose.

These are closure and enforcement defects. No new FCB amendment is needed. A004, A005, D-24, D-25, the repair-18 contract, and the standing deletion rule already require the correct result.

Repair 19 is the sole next C4 task.

---

# 1. Independent review evidence

The following checks were run directly against the uploaded snapshot.

## Checks which passed

```text
python3 tools/human-review-index.py --self-test
python3 tools/human-review-index.py --check
python3 tools/fcb-reference-gate.py --self-test
python3 tools/fcb-reference-gate.py
python3 tools/closure-ledger-view.py --check
python3 tools/claim-matrix-gate.py --self-test
python3 tools/claim-matrix-gate.py
sh tools/ocaml-origin-gate.sh .
sh tools/generated-output-gate.sh .
```

The generated Go also passed a direct host build under:

```text
GOOS=linux
GOARCH=amd64
GOAMD64=v1
CGO_ENABLED=0
```

The built program matched:

```text
e2e/golden.stdout
e2e/golden.stderr
e2e/golden.exit
```

Reviewed generated-byte baseline:

```text
go.mod   d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa
main.go  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

## Checks which exposed false greens

The naming-gate self-test printed:

```text
SKIP  unreadable-file control: this platform still reads a 0o000 file (running as root?) — the condition cannot be expressed here
fido: naming-gate self-test OK — 47 controls (... 5 enumeration/read fail-closed) ✓
```

The skipped control was counted as passed.

Direct probes of the naming checker returned no violation for:

```coq
Local Notation TypedProgram := (Typing.Program f) (only parsing).
Local Notation Resolve := (Typing.Resolve f) (only parsing).
Local Notation Stmt := (Typing.Stmt f) (only parsing).
```

A temporary copy of the repository was then changed by appending this live instruction to the FCB Index:

```markdown
**Operational review:** read `.review/NO_SUCH_OPERATIONAL_FILE.md`.
```

The current D-24 gate still reported:

```text
fido: fcb-reference gate OK — 27 declared reference(s): 25 resolve in this tree, 2 explicitly typed off-tree ✓
```

The gate validates declared rows. It does not prove that every operational reference was declared.

## Checks not independently rerun here

This review environment does not contain Docker, Rocq, Dune, or the OCaml toolchain. Therefore the reported full proof, extraction, plugin, materializer, Docker, and staged-hook results remain candidate evidence rather than an independent rerun by the reviewer.

Claude Code must rerun all of them before the next freeze.

---

# 2. Install repair-19 authority before implementation

Write this directive verbatim to:

```text
.review/C4_IMPLEMENTATION_REPAIR_19.md
```

Then make one authority/current-state commit containing documentation and authority data only.

## Required current state

Update `.review/NEXT_STEPS.md` so it alone states:

- candidate `50c3bcc5b8eb2e47074352f5c9f0124e71509396` is BLOCKING;
- it is the twentieth blocked C4 implementation candidate;
- freeze `2b848871c7faf4a9586c8b20b4896e1ec543987c` is documentation-only;
- repair 19 is the sole active C4 work;
- the exact six blocker classes in section 0;
- C4 is not accepted;
- C5, checkpoint-definition Step 0, post-C4 work, broad cleanup, and proof partitioning remain forbidden;
- A001 through A006 remain accepted;
- Governance owns D-01 through D-26.

Update `.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv`:

```text
C4-REVIEW    BLOCKED
```

Its required act must say that Rob will review the repair-19 candidate after it is frozen. Regenerate the Human Review Index with the one generator.

Update:

```text
.review/fcb/current/FIDO_FCB_INDEX.md
.review/REVIEW_REQUEST.md
.review/OPEN_QUESTIONS.md
```

Required state:

- FCB Index: candidate `50c3bcc...` is blocked and repair 19 is active.
- Review Request: `state: closed`; no implementation review is requested while repair 19 is active.
- Open Questions: no open implementation question unless implementation finds a real ambiguity not settled by this directive or the FCB.

Update `FIDO_FCB_REFERENCES.tsv` so its repair-directive row points to repair 19.

Delete these live repair-18 artifacts in the same authority transition:

```text
.review/C4_IMPLEMENTATION_REPAIR_18.md
.review/C4_REPAIR_18_CLAIM_THEOREM_MATRIX.tsv
.review/C4_REPAIR_18_CLOSURE_AUDIT.md
```

Git history is their archive. Do not keep stale completion evidence beside an active repair.

Suggested authority commit:

```text
review(authority): C4 — install repair 19 as the sole active work
```

No `.v`, Docker, OCaml, generated Go, executable gate logic, or implementation change belongs in that authority commit.

---

# 3. Blocking finding A — A005 still has fake local namespaces

## Current defect

These declarations remain live:

```coq
Compilable.v:
Local Notation TypedProgram := (Typing.Program predeclared_type) (only parsing).
Local Notation Resolve      := (Typing.Resolve predeclared_type) (only parsing).
Local Notation Stmt         := (Typing.Stmt predeclared_type) (only parsing).
Local Notation Decl         := (Typing.Decl predeclared_type) (only parsing).
Local Notation File         := (Typing.File predeclared_type) (only parsing).
Local Notation SourceFile   := (Typing.SourceFile predeclared_type) (only parsing).

Safe.v:
Local Notation Resolve :=
  (Typing.Resolve Compilable.predeclared_type) (only parsing).

Render.v:
Local Notation Resolve :=
  (Typing.Resolve Compilable.predeclared_type) (only parsing).
```

`Stmt`, `Decl`, `File`, and `SourceFile` have no live use. They are dead aliases.

`TypedProgram` and `Resolve` hide the namespace which owns those judgments. They recreate the old unqualified surface inside another module.

A005 and D-25 say the opposite:

- the owning namespace supplies the domain;
- cross-module use is qualified;
- old names receive no aliases, wrappers, or re-exports;
- Git history is the only compatibility layer.

The current naming gate accepts all of these declarations and has no negative control for the class.

## Required repair

Delete all eight UpperCamelCase local notation aliases.

Delete the four unused aliases outright:

```text
Stmt
Decl
File
SourceFile
```

Replace every use of `TypedProgram` with the qualified specialized form:

```coq
Typing.Program predeclared_type
```

Replace each `Resolve` use with the qualified specialized form at the exact resolver:

```coq
Typing.Resolve predeclared_type
```

or:

```coq
Typing.Resolve Compilable.predeclared_type
```

as appropriate to the module.

Do not replace them with another alias, abbreviation, notation, wrapper, module re-export, or compatibility name.

Lower-case parsing notations for resolver-specialized executable functions may remain only where they have a current use and do not hide a public type or judgment namespace. Delete any unused lower-case notation found during the same local audit.

Update comments and theorem prose. Current comments which say `[TypedProgram]` as though it were the public judgment must say the real qualified surface.

Where prose uses `Admissible` to mean the former module or layer rather than the current proposition, replace it with `Compilable` or plain “compilation.” Do not mechanically replace genuine references to the current `Compilable.Admissible` proposition.

## Required gate repair

Make this a general A005 rule, not a list that catches only today’s eight names:

> A certified Rocq module may not introduce an UpperCamelCase `Local Notation` which erases another Fido module’s ownership of a public type, family, or judgment.

The simplest current enforcement is to reject every UpperCamelCase local notation in certified Fido modules. There are no legitimate live examples after this repair. A future exception requires review rather than an allowlist added for convenience.

Add must-fail controls for at least:

```coq
Local Notation TypedProgram := (Typing.Program f) (only parsing).
Local Notation Resolve := (Typing.Resolve f) (only parsing).
Local Notation Stmt := (Typing.Stmt f) (only parsing).
Local Notation SourceFile := (Typing.SourceFile f) (only parsing).
```

Add a must-accept control for a lower-case, used, resolver-specialized executable notation.

Add a repository assertion that no UpperCamelCase local notation remains in any certified `.v` file.

Working-tree mode and staged-snapshot mode must both enforce it.

Add the deleted alias names to a retired-surface rule only where that does not reject the real qualified declarations `Typing.Resolve`, `Typing.Stmt`, and so on. Match the alias declaration, not the semantic word everywhere.

---

# 4. Blocking finding B — the public cause theorems erase exact source occurrence identity

## Current accepted-side defect

`deep_nested_chain_success_evidence` proves its four branches by looking up exact source locals:

```text
int8   local 11
int16  local 9
int32  local 7
int64  local 5
```

But its public result is:

```coq
nested_conversion_cause input ph ts x
```

and that predicate says only:

```coq
exists wm, accepted_conversion_cause ... wm ts x
```

Its own comment admits that it names source shape, not occurrence.

Therefore the proof knows the exact occurrence and the theorem forgets it.

`AcceptedFixture` repeats that weakened predicate in all four cause fields.

A syntactically equal conversion at another source occurrence would satisfy the same public field. That is not exact occurrence provenance.

## Current rejected-side defect

`deep_fail_outer_childfail` uses exact source locals:

```text
int16  local 9
int32  local 7
int64  local 5
```

but `deep_fail_outer_childfail_claim` exposes only an existential work member with matching expression shape.

`deep_fail_innermost_diag_claim` carries exact retained references inside its diagnostic, but its public statement does not tie the failing work member to the exact source occurrence at local 11.

Again, the proofs know more than the theorem statements.

## Required root repair

Retain the existing cause authority:

```text
total_forest_outcome_cause
accepted_conversion_cause
rejected_conversion_cause
childfail_conversion_cause
```

Do not create a second cause object.

Add exact occurrence-indexed fixture predicates which state the source occurrence, retained work member, and retained cause together.

A suitable accepted shape is equivalent to:

```coq
Definition accepted_conversion_at
    (input : Input deep_nested_program)
    (ph : Phase input)
    (local : positive)
    (ts : Syntax.TypeExpr)
    (x : Syntax.Expr) : Prop :=
  exists occ
         (wm : WorkMember (phase_work ph)),
      Index.source_occurrence_at deep_nested_src local = Some occ
   /\ Index.view_expr occ = Some (Syntax.Convert ts x)
   /\ work_occurrence (proj1_sig wm) = occ
   /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))
        = Index.MakeKey (FilePath.Make "main.go" eq_refl) local
   /\ accepted_conversion_cause (phase_ot ph) wm ts x.
```

The exact spelling may differ, but all five ownership facts must remain in the public proposition.

Use the existing `member_at_in_forest` theorem. It already returns:

- `work_occurrence ... = occ`;
- `work_expr ... = e`;
- exact key equality to `Index.MakeKey path local`.

Do not rediscover or recompute occurrence identity.

Define rejected equivalents for:

- the exact innermost rejected cause at local 11;
- each exact child-failure cause at locals 9, 7, and 5.

The diagnostic reason, annotation context, source key, work member, `ConversionStep`, suffix, predecessor accumulator, operand membership, prior outcome, final preservation, and diagnostic lists must all remain in one scope where required.

## Exact accepted fields

`AcceptedFixture` must state:

```text
int8  cause at exact local 11
int16 cause at exact local 9
int32 cause at exact local 7
int64 cause at exact local 5
```

It is not enough for the proof to use those numbers. They must occur in the public field types or in an equivalent exact `ExprRef` identity which uniquely carries them.

## Exact rejected fields

`RejectedFixture` must state:

```text
innermost int8 failure at exact local 11
int16 child failure at exact local 9
int32 child failure at exact local 7
int64 child failure at exact local 5
```

The final phase, raw, and command-ordered diagnostic lists must remain equal to the exact singleton `InvalidConversion` reason whose refs come from that exact local-11 retained cause.

## Delete the weaker peers

Delete after replacement:

```text
nested_conversion_cause
```

Delete or replace any shape-only rejected helper which no longer has a distinct current consumer.

Do not leave a theorem which states only “some retained member has this expression shape” beside the exact occurrence theorem.

## Required proof and matrix surfaces

Gate the exact occurrence-indexed predicates and both root fixtures.

The repair-19 obligation matrix must have distinct rows for:

```text
accepted int8 local 11
accepted int16 local 9
accepted int32 local 7
accepted int64 local 5
rejected int8 local 11
rejected int16 local 9
rejected int32 local 7
rejected int64 local 5
```

Each row must name:

- the public fixture field;
- the occurrence-indexed cause predicate;
- the concrete source local or exact retained `ExprRef`;
- the assumptions surface;
- the concrete fixture.

Do not describe a shape-only theorem as per-occurrence evidence.

---

# 5. Blocking finding C — Safe and Emit opacity tests do not load Safe or Emit

## Current defect

The shared Docker helper writes:

```coq
From Fido Require Import Syntax Compilable.
Definition probe := <qualified hidden term>.
```

That prelude is used for every `sealed` test.

It is valid for `Compilable.*`.

It is not valid evidence for:

```text
Emit.Mint.Issue
Emit.Mint.TokenRepresentation
Emit.MakeImage
Safe.Make
Safe.ProgramRepresentation
Safe.Certificate.Make
```

`Compilable` cannot import its downstream modules `Safe` or `Emit`. Those tests can fail because the module prefix was never loaded. The accepted error pattern includes generic “not found” messages.

The positive control later imports the full pipeline. It does not repair the individual negative fixtures.

The code may be sealed correctly. The current tests do not prove it.

## Required repair

Make every negative fixture prove that the module under test loaded successfully before probing the hidden term.

Use a two-stage helper or equivalent:

1. Compile the exact import prelude plus a known public sentinel from the same module. This stage must succeed.
2. Compile the same prelude and sentinel plus the raw hidden term. This stage must fail for that hidden term.

Suitable sentinels include:

```text
Compilable.compile
Safe.certify
Emit.Mint.issue
Emit.of_safe
```

The second-stage error check must identify the hidden component. It must not accept failure to load the module, failure to resolve the sentinel, syntax error, load-path error, or another unrelated failure.

A simple safe prelude may import the complete public chain for all controls:

```coq
From Fido Require Import Syntax Compilable Safe Emit.
```

Do not rely on transitive loading which the dependency graph cannot provide.

## Required adversarial controls

Add a control which deliberately omits `Safe` or `Emit`. The helper must reject that test fixture as invalid evidence rather than count it as a sealed constructor.

Add a control with a transient public constructor. The helper must fail its own expectation when the probed constructor is reachable.

Keep the positive public-path control.

Update the claim matrix and closure audit. They may cite a constructor-opacity control only after the exact module-loaded sentinel and hidden-name failure are both established.

---

# 6. Blocking finding D — the naming-gate self-test counts a skip as a pass

## Current defect

The unreadable-file control uses:

```text
chmod 000
```

When the gate runs as root, the file remains readable.

The self-test then prints `SKIP`, does not increment the failure count, includes the skipped case in:

```text
5 enumeration/read fail-closed
```

and reports all controls passed.

That is a false completion count.

## Required repair

Refactor the selected-file read path so the self-test can inject a deterministic read failure.

For example, make `run` accept one internal reader function, defaulting to the real UTF-8 reader. In the control, inject a reader which raises `OSError` only for `unreadable.md`.

Requirements:

- the control must execute under every user, including root;
- the gate must fail;
- the error must name `unreadable.md`;
- the error must identify a read failure;
- no `SKIP` branch remains;
- a skipped or unconstructible control is itself a self-test failure;
- the printed control count is computed from controls actually executed, not a hard-coded total.

Keep the invalid-UTF-8 control as a distinct case.

Add a mutation control which replaces the read exception with a successful read and proves the negative case then fails to fail.

Working-tree and staged-snapshot modes must use the same read implementation.

---

# 7. Blocking finding E — D-24 checks declared rows but does not prove complete declaration

## Current defect

`FIDO_FCB_REFERENCES.tsv` has 27 rows.

The gate validates those rows. It intentionally does not inspect live authority documents for undeclared operational references.

Current live authority names operational paths with no manifest row, including:

```text
.review/C4_REPAIR_18_CLOSURE_AUDIT.md
.review/C4_REPAIR_18_CLAIM_THEOREM_MATRIX.tsv
.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md
.review/OPEN_QUESTIONS.md
.review/REVIEW_BASIS.md
.review/REVIEW_REQUEST.md
ARCHITECTURE.md
PROGRESS.md
```

The exact set will change when repair 19 retires repair-18 artifacts. The defect is not the current list alone. The manifest has no completeness relation to the corpus.

The current gate also checks only that an `owner` value names a readable file. It does not prove that the owner contains or owns the stated operational reference.

The following adversarial mutation currently passes:

```markdown
**Operational review:** read `.review/NO_SUCH_OPERATIONAL_FILE.md`.
```

That disproves CLAIM-15 as written.

## Required root repair

Keep one typed-reference manifest. Do not add a second reference list.

Extend each manifest row with a stable owner anchor, for example:

```text
owner_anchor
```

Each owning current document must contain exactly one matching marker:

```html
<!-- FIDO-FCB-REF:<ID> -->
```

The marker must be adjacent to, or syntactically bind, the exact normalized path in that row.

The gate must prove both directions:

1. Every manifest row has exactly one valid owner marker and the declared path resolves or is correctly typed off-tree.
2. Every operational repository path in the live authority corpus is bound to exactly one manifest row and marker.

## Live authority corpus to scan

At minimum:

```text
.review/fcb/current/*.md
.review/NEXT_STEPS.md
.review/OPEN_QUESTIONS.md
.review/REVIEW_REQUEST.md
CLAUDE.md
```

Generated views may be checked through their canonical sources where that avoids duplicate ownership, but no operational instruction may evade the check merely because it appears in a generated view.

## Operational path syntax

Scan fail-closed for repository path forms rooted at:

```text
.review/
tools/
gate/
e2e/
plugin/
```

and the exact root operational files:

```text
CLAUDE.md
ARCHITECTURE.md
PROGRESS.md
Makefile
Dockerfile
dune
```

Normalize a directory’s optional trailing slash.

Do not add a growing exception list. A string that looks like one of these repository-rooted operational paths is either:

- a typed manifest reference with one owner marker; or
- a blocking untyped reference.

Historical amendment files may quote old paths as historical data, but the live current FCB must not direct work through an untyped historical path.

## Required current rows

After repair-19 names are final, include every live operational reference, including at least:

```text
repair-19 directive
repair-19 closure audit
repair-19 obligation matrix
C4 functional contract
review basis
open questions
review request
NEXT_STEPS
stable FCB bootstrap
live FCB set
root Claude bootstrap
all tools and gates which current FCB text directs a reader to execute
```

Do not add rows for a file merely because it exists. Add rows because a current authority directs work to it.

## Required controls

Add must-fail controls for:

- an unmanifested nonexistent `.review/...` path inserted into the FCB Index;
- an unmanifested existing `tools/...` path;
- a manifest row whose owner has no marker;
- a duplicate owner marker;
- a marker whose visible path differs from the manifest path;
- one operational path claimed by two rows;
- a repository path falsely typed as external;
- read and decode failure in an owner document;
- staged export missing a referenced target.

The exact mutation above must fail.

Update D-24 prose in the FCB Index, Governance, Model Operations, and Checkpoint Authoring Guide so it describes the complete two-way relation rather than row validation only.

No amendment is required. This implements accepted D-24.

---

# 8. Blocking finding F — stale and weaker residue remains

## Stale comment

Delete or correct this live comment in `Compilable.v`:

```text
needed for the order-independent legacy-class projection
```

There is no legacy class. The live closure audit and NEXT_STEPS both claim those comments are gone.

## Weaker consumer-free theorem

Delete:

```text
deep_nested_ok_closure_at
```

and its assumptions-gate line and explanatory gate prose.

The theorem is explicitly described as weaker than `deep_nested_convsuccess_at` and the cause-owned predicates. It has no current in-theory consumer. Its only named consumer is its assumptions-gate entry.

Being gated does not give a theorem a semantic purpose.

Add it to the deleted-surface enforcement table so it cannot return unnoticed.

Do not delete `deep_nested_all_ok` merely because it is short. It has a distinct outcome-shape role. Review its stated purpose and keep it only if that exact role remains current and named.

Run a scoped search for all remaining references to the removed legacy classifier and to theorem surfaces deleted in repairs 17 through 19. Classify each hit. Do not rely on a zero-count report without reading declarations.

---

# 9. Replace the repair-18 completion matrix with repair-19 obligation evidence

The repair-18 matrix helped catch misspelled names. It did not and could not judge theorem strength.

It also cited:

- shape-only cause predicates as exact per-occurrence proof;
- vacuous `Safe` and `Emit` constructor controls;
- an incomplete D-24 manifest;
- a naming self-test which counted a skip as passed.

Do not delete the idea. Tighten its claim.

Create:

```text
.review/C4_REPAIR_19_OBLIGATION_MATRIX.tsv
```

Use stable repair-obligation IDs rather than broad prose claims.

At minimum include distinct rows for:

```text
R19-A005-NO-UPPER-LOCAL-TYPE-ALIASES
R19-ACCEPT-INT8-LOCAL-11
R19-ACCEPT-INT16-LOCAL-9
R19-ACCEPT-INT32-LOCAL-7
R19-ACCEPT-INT64-LOCAL-5
R19-REJECT-INT8-LOCAL-11
R19-REJECT-INT16-LOCAL-9
R19-REJECT-INT32-LOCAL-7
R19-REJECT-INT64-LOCAL-5
R19-SEAL-COMPILABLE-MODULE-LOADED
R19-SEAL-SAFE-MODULE-LOADED
R19-SEAL-EMIT-MODULE-LOADED
R19-NAMING-READ-CONTROL-EXECUTED
R19-D24-MANIFEST-TO-CORPUS
R19-D24-CORPUS-TO-MANIFEST
R19-NO-WEAKER-CAUSE-PEER
R19-GENERATED-BYTES
R19-WHOLE-THEORY-ASSUMPTIONS
```

Each row must name:

- exact public surface;
- exact concrete fixture or client test;
- exact executable gate;
- exact expected failure reason where the obligation is negative;
- status.

The matrix gate may verify existence and syntax. It must continue to state plainly that it does not prove theorem strength.

The freeze report must not say the matrix proves more than that.

---

# 10. Repair-19 whole-system closure audit

Do not freeze when the six named findings first turn green.

Create at final freeze:

```text
.review/C4_REPAIR_19_CLOSURE_AUDIT.md
```

Audit the current whole system.

## Public constructor and mint audit

Inspect every path which can construct:

```text
Compilable.Core
Compilable.Program
Compilable.Failure
Compilable.Facts
Safe.Program
Emit.Mint.Token
Emit.Image
```

For each negative client test, prove that the module loaded and a public sentinel resolved before the hidden constructor was probed.

## Public theorem topology audit

Read the final types, not only their proofs.

Confirm:

- one exact accepted returned object;
- one exact rejected returned object;
- exact source occurrence identity in each concrete cause field;
- exact retained cause object;
- exact predecessor accumulator and suffix;
- exact diagnostic reason and refs;
- no equality to a rebuilt peer;
- no shape-only theorem described as occurrence evidence.

## A005 audit

Inspect:

- every UpperCamelCase local notation;
- every alias or wrapper which hides another module’s public type or judgment;
- comments which present an old module name as current;
- compatibility re-exports;
- deleted-surface return.

## D-24 audit

Inject an undeclared path into a temporary live owner document. The gate must fail.

Confirm every current operational path has:

- one typed row;
- one exact owner marker;
- one resolved target or explicit off-tree status.

## Semantic-peer audit

Find and disposition:

- weaker peers;
- collapsed outcome peers;
- compatibility views;
- duplicate diagnostic or cause authorities;
- theorems kept only because they are gated;
- comments whose only subject was deleted code.

## Full execution-path audit

Run:

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
```

Run the pre-commit hook on the exact staged exported snapshot without `--no-verify`.

Verify extraction, OCaml plugin, materializer, sink, generated-mode gate, whole Go tree, all goldens, and generated-byte identity.

Record exact command results and current surface counts. Do not copy a prior count.

---

# 11. Required FCB and current-document closeout

No FCB amendment is required.

Update the existing corpus to match the repaired implementation.

At final freeze:

- `NEXT_STEPS.md` alone owns candidate state.
- `FIDO_FCB_HUMAN_ACTS.tsv` owns the open C4 review act.
- the Human Review Index is regenerated.
- the FCB Index names the frozen candidate only at review freeze.
- `REVIEW_REQUEST.md` becomes `state: requested`.
- `OPEN_QUESTIONS.md` states no open implementation question unless one truly remains.
- the typed reference manifest includes and binds every live repair-19 operational path.
- the Roadmap continues to own checkpoint order.
- Git history owns repair-18 narratives.

Delete the live repair-19 directive only after C4 is accepted or superseded by a later repair. Until then it is current authority.

The implementation candidate and documentation-only freeze must remain distinct.

---

# 12. Scope restrictions

Do not start:

- C5;
- checkpoint-definition Step 0;
- runtime `Machine` types;
- states, starts, labels, results, runs, traces, fairness, deadlock, or scheduling;
- post-C4 features;
- the broad source-comment cleanup;
- proof-module splitting or build parallelization;
- a general repository reorganization;
- a new compatibility path;
- a new FCB amendment.

Fix only the root causes and adjacent residue required to close C4.

Do not shorten names, compress proofs, or merge distinct concepts merely to reduce byte count in this repair.

---

# 13. Definition of done

Repair 19 is complete only when all of the following are true.

## A005

1. No UpperCamelCase local type or judgment notation remains in certified source.
2. `TypedProgram`, `Resolve`, `Stmt`, `Decl`, `File`, and `SourceFile` do not survive as local aliases.
3. Cross-module public type and judgment references are qualified.
4. The naming gate rejects this alias class with non-vacuous controls.
5. Current comments use the real owner names.

## Exact occurrence causes

6. Accepted `int8`, `int16`, `int32`, and `int64` cause fields retain exact source locals 11, 9, 7, and 5.
7. Rejected `int8`, `int16`, `int32`, and `int64` cause fields retain exact source locals 11, 9, 7, and 5.
8. Each exact local is tied to the retained work member, retained occurrence, retained key, and retained cause object.
9. The exact source identity appears in the public proposition, not only its proof.
10. Shape-only cause peers are deleted.
11. The accepted and rejected root fixtures remain over one exact returned object each.
12. No builder or equality-to-rerun enters those roots.

## Negative controls

13. Every constructor-opacity fixture first proves its module and public sentinel loaded.
14. `Safe` and `Emit` hidden-name tests cannot pass because those modules were absent.
15. A reachable-constructor mutation makes the sealed-test helper fail.
16. The positive public pipeline remains usable.
17. The naming unreadable-file control always executes.
18. No skipped control is counted as passed.

## D-24

19. Every manifest row has one validated owner marker.
20. Every operational path in the live authority corpus has exactly one typed manifest row.
21. An undeclared path injected into a live owner document fails the gate.
22. A row/path/owner mismatch fails.
23. Working-tree and staged-snapshot modes enforce the same reference set.
24. The current repair directive, closure audit, obligation matrix, contract, review basis, open questions, and review request are correctly typed.

## Deletion and coherence

25. `deep_nested_ok_closure_at` and its gate residue are gone.
26. The stale legacy-class comment is gone.
27. No old result classifier or compatibility surface returns.
28. The repair-19 obligation matrix names real, non-vacuous evidence.
29. The repair-19 closure audit makes no claim stronger than its cited theorem or test.
30. All live current documents state one coherent candidate state.

## Full gates

31. The whole certified theory is assumption-free.
32. Proof, extraction, Docker, OCaml, materializer, sink, e2e, regeneration, staged, and formatting gates pass.
33. The generated Go bytes remain exactly:

```text
go.mod   d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa
main.go  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

34. No C5 or post-C4 work has begun.
35. C4 remains unaccepted until Rob’s next human review.

---

# 14. Required execution loop

Use:

```text
/loop 3m
```

Continue implementing, checking, reading theorem types, running adversarial controls, and correcting the whole current system until every requirement above is complete or a real blocker prevents further work.

Do not stop for:

- routine progress reports;
- green intermediate checks;
- one fixed finding while another remains;
- a partial authority update;
- a matrix whose cited test is vacuous;
- a proof whose statement omits what its body knows;
- a reference manifest which validates only its own chosen rows;
- a skipped self-test;
- documentation-only completion while code or gates remain wrong.

When complete or genuinely blocked, use the notification tool to notify Rob.

If blocked, report:

- the exact obligation ID;
- the smallest reproducer;
- the exact theorem type, constructor path, gate, or FCB rule involved;
- the exact error;
- why the accepted contract cannot be met;
- the precise human decision required.

Do not improvise another architecture.

At completion, freeze one exact implementation candidate and one documentation-only review freeze. Notify Rob only after the whole-system closure audit and exact staged hook are complete.
