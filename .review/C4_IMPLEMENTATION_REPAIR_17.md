# C4 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 17

## Authority and use

Rob is the final human authority. Rob's delivery of this file to Claude Code records the C4 review disposition below and authorizes only the repair stated here.

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

- uploaded archive: `fido-main - 2026-07-26T125736.743.zip`;
- archive SHA-256: `5773b5085d7ece62d8342db2520dd177d7d2e00ccb38775389203cc76546b0ed`;
- exact candidate named by the archive: `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c`;
- repository: `rhencke/fido`;
- live FCB root: `.review/fcb/current/` at that exact ref;
- active checkpoint authority read from that ref: `.review/NEXT_STEPS.md`;
- open questions read from that ref: `.review/OPEN_QUESTIONS.md`.

Candidate `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c` is **BLOCKING**. It is the eighteenth blocked C4 implementation candidate. C4 is not accepted. C5, post-C4 features, the broad source cleanup, and proof-module partitioning remain forbidden.

C4 repair 17 is the sole next implementation task.

Implement on the current `main` head only after confirming that it is either the exact reviewed ref or a documentation-only descendant which freezes that ref. Do not reset or rewrite history. If any intervening commit changes Rocq, OCaml, gates, generated artifacts, or another live execution path, stop and report the new functional review basis before editing.

## Review disposition

Repair 16 made real progress and closed several prior defects:

- `Compilable.Core` is now abstract outside its sealed implementation.
- `MakeCore`, `CoreRepresentation`, `build_elaboration_core`, `MakeElaboration`, and the internal mint helpers are absent from the client interface and covered by negative client compilation tests.
- `build_elaboration_core` now folds package references directly from its retained `input_visit`.
- package diagnostics now consume the exact retained package-reference map.
- the accepted and rejected aggregate fixtures no longer state equality to `build_elaboration_core`.
- all 51 lower-case constructors found by the repaired parser were renamed.
- the generated Go program still builds and its output matches the reviewed goldens.

These results must not regress.

The candidate is still blocked for five reasons:

1. the direct accepted and rejected capability fixtures omit the required retained outcome, trace, cause, annotation, raw-diagnostic, safety, and emission evidence;
2. the A005 naming gate remains false-green for upper-case record fields and silently skips selected text files which cannot be read as UTF-8;
3. `Emit.Image` has a public raw constructor although the live FCB says its constructor is private and repair 16 claimed it was already sealed;
4. the public `LegacyClass` / `legacy_compile_class` compatibility projection remains as a coarse, collapsed outcome peer despite an exact structured report already existing;
5. the live FCB, checkpoint documents, architecture prose, source comments, and review request do not state one current truth.

No new FCB amendment is needed for the normal repair. A001, A005, Governance D-22 through D-25, Charter §§1, 3, 4, 22, 24 and 25, and the current no-compatibility law already decide the required result. If Claude believes one of those contracts must change, stop and propose the exact amendment instead of retaining the defect.

---

# Blocking finding 1 — the direct capability fixtures still do not prove the retained causal result

## Current defect

Repair 16 required complete accepted and rejected fixtures over the actual values returned by `Compilable.compile`.

The current accepted theorem begins at `Compilable.v:11576`:

```coq
Theorem deep_nested_capability_retains_elaboration : ...
```

It proves:

- the returned capability and source;
- retained input and phase projection identities;
- expression and type-name fact object identities;
- retained package references;
- layout and plan;
- final diagnostics are empty;
- work-forest length is five.

It does **not** prove through that returned `cp`:

- the retained exact work index;
- the retained outcome table and trace;
- the four conversion causes at their exact source occurrences;
- the exact raw diagnostic list;
- `Safe.certify` retaining the same capability and core;
- `Emit.of_safe` consuming that exact accepted path.

The current rejected theorem begins at `Compilable.v:11657`:

```coq
Theorem deep_fail_capability_retains_rejected_elaboration : ...
```

It proves projection equalities, retained package references, layout, plan, nonempty diagnostics, and work count. It does **not** prove through the returned `fail`:

- the exact retained work index;
- the retained outcome table and trace;
- the innermost conversion-failure direct cause;
- the exact prior operand outcome;
- the enclosing child-failure causes;
- the exact retained annotation context;
- the exact singleton `InvalidConversion` reason;
- the exact raw diagnostic list.

The detailed cause fixtures still live later in `Compilable.v` as statements over freshly constructed values containing repeated calls to:

```text
build_compilation_input
build_expression_phase
Index.index_program
```

Examples include `nested_success_bundle`, `deep_nested_convsuccess_at`, `deep_nested_chain_success_evidence`, `deep_fail_innermost_diag`, and the child-failure closure fixtures. They prove facts about a canonical rebuilt phase, not about `phase (core cp)` or `phase (failure_core fail)`.

`gate/Assumptions.v` gates the aggregate capability fixtures and the builder-based cause fixtures as separate theorem families. Its prose calls the cause family accepted public evidence, but no theorem connects those causes to the returned capability or failure. The gate therefore overstates what its theorem statements establish.

This is not repaired by the fact that both objects are deterministic or extensionally equal. The public fixture must expose the causal evidence through the exact object returned by production.

## Required repair

Rebuild the fixture layer from the retained objects outward.

First state the reusable cause, trace, index, annotation, and diagnostic theorems over the most basic retained object which owns each fact. They should be polymorphic over an actual `Core`, `Phase`, `WorkForest`, `Outcomes`, or returned capability/failure as appropriate. Do not state the reusable theorem over a hard-coded call to a builder.

Then instantiate those theorems through:

```text
cp
core cp
program_input cp
program_phase cp
facts cp
accepted cp
```

and:

```text
fail
failure_core fail
failure_input fail
failure_phase fail
failure_package_refs fail
failure_layout fail
failure_plan fail
failure_raw_diagnostics fail
failure_diagnostics fail
rejected fail
```

### Required accepted fixture

Obtain the exact `cp` by destructing `compile deep_nested_program` through `compile_complete` or an equivalent helper whose statement does not mention a builder.

After `cp` exists, the fixture statement and proof must not call or mention these as a way to recover its data:

```text
build_elaboration_core
build_compilation_input
build_expression_phase
Index.index_program
elaborate
program_visit
program_package_refs
a source fact-table builder
```

The returned-object theorem must establish, through `core cp` and its projections:

- exact retained input;
- exact retained phase;
- exact retained work forest;
- exact retained standard work index and its two-way domain;
- exact retained outcome table;
- exact retained causal trace;
- each of the four conversion success causes at the exact source conversion occurrence;
- each exact operand predecessor in the retained suffix and the final-table preservation fact;
- the one `Typing.convert_constant` step attached to each retained conversion cause;
- exact expression and type-name fact objects;
- exact retained package-reference object;
- exact retained root layout and build plan used by the decision;
- exact empty raw diagnostics;
- exact empty final diagnostics;
- the concrete retained work count;
- `Safe.certify cp` retaining the identical `cp` and `core cp`;
- `Emit.of_safe (Safe.certify cp)` consuming that path;
- the equal-valued twin expressions remaining distinct retained occurrences.

The theorem may use a source equation carried by the returned `Compiled` branch to transport a property of `core cp`. It may not use that equation to replace `core cp` with an independently rebuilt peer.

### Required rejected fixture

Obtain the exact `fail` by destructing `compile deep_fail_program` through `compile_rejected_of_inadmissible` or an equivalent builder-free theorem.

After `fail` exists, the fixture statement and proof must not call or mention:

```text
build_elaboration_core
build_compilation_input
build_expression_phase
Index.index_program
elaborate
```

as a way to recover the failed object.

The returned-object theorem must establish, through `failure_core fail` and its projections:

- exact failed input and phase;
- exact retained work forest and standard work index;
- exact retained outcome table and causal trace;
- the innermost conversion-failure direct cause;
- the exact target reference, operand reference, operand status, and failed conversion step;
- the exact prior operand outcome and its preservation into the final table;
- every enclosing child-failure cause;
- the exact retained annotated-work object and outer context;
- exact raw diagnostics;
- the exact singleton `InvalidConversion` reason and exact final diagnostic order;
- exact retained package references, layout, and plan used by rejection;
- nonemptiness directly from `rejected fail`;
- no copied diagnostic list.

### Delete the obsolete concrete reconstruction fixtures

Once the direct capability fixtures provide the complete evidence, delete any concrete builder-based fixture, bundle, wrapper theorem, or repeated hard-coded type expression whose only purpose was to prove the same fact over a rebuilt phase. Keep a general theorem only when it has a distinct current proof purpose and is stated over the retained object type.

Do not retain old and new fixture families in parallel. Git history is the archive.

When practical, compile the final returned-object fixtures as a client which imports only the sealed public API. The type checker should prevent the fixture from naming internal builders. Do not create a compatibility export to make the client compile.

Update `gate/Assumptions.v` so it gates the complete returned-object theorems and does not describe builder-based peers as capability evidence.

---

# Blocking finding 2 — the A005 naming gate is still false-green

## Current defect A — upper-case record fields are invisible

`tools/naming-gate.py` parses record fields with:

```python
re.findall(r"[{;]\s*([a-z_][A-Za-z0-9_']*)\s*:", body)
```

The parser accepts only a field whose first character is already lower-case. The later rule which rejects an upper-case field can therefore never see an upper-case-first field.

The reviewed gate returns no violation for both of these invalid declarations:

```coq
Record Good := MakeGood { BadField : nat }.
Record Good := MakeGood { good : nat; BadField : nat }.
```

It correctly rejects `badField` only because that name starts lower-case and gets parsed. This is the same pre-validation parser defect which previously hid lower-case constructors.

The current tree happens not to contain an upper-case record field. That does not make the gate sound. The gate claims to enforce the rule and can accept a proposed commit which violates it.

## Current defect B — selected unreadable text is silently omitted

`run()` contains:

```python
try:
    text = path.read_text(encoding='utf-8')
except (UnicodeDecodeError, OSError):
    continue
```

A selected Markdown, source-comment, gate, hook, or other text file can therefore fail to decode or fail to read and vanish from the gate. The Rocq coverage check catches a skipped expected `.v` file, but it does not catch skipped documentation or other selected text.

A complete synthetic snapshot containing all required roots plus a `bad.md` with bytes:

```text
The GoCompile layer is live.\xff
```

returns success with no violation. A fail-closed naming gate must reject the unreadable selected file and name its path.

## Required repair

1. Parse a general Rocq field identifier first:

   ```regex
   [A-Za-z_][A-Za-z0-9_']*
   ```

   Then apply the field casing rule. Do not filter invalid names out in the parser.

2. Add must-reject controls for:

   ```coq
   Record Good := MakeGood { BadField : nat }.
   Record Good := MakeGood { good : nat; BadField : nat }.
   ```

3. Add must-accept controls for valid first and later lower-snake-case fields.

4. Treat every `UnicodeDecodeError` and `OSError` for a selected file as an enumeration/gate failure. Print the exact path and error. Do not guess that the file is binary after the selection logic classified it as text.

5. Add a self-test which constructs a complete snapshot with an invalid-UTF-8 selected prose file and proves snapshot mode fails.

6. Add a self-test for an unreadable selected file where the platform permits it. The test must fail closed or explicitly skip only when the platform cannot express the condition; it must never report the gate itself successful because the file was skipped.

7. Preserve the current constructor controls, Dune/root Rocq coverage, working-tree enumeration checks, staged-snapshot mode, untracked nonignored file coverage, and staged-hook enforcement.

8. Change the self-test success message from “negative controls” to “controls” or another accurate term. The set includes must-reject, must-accept, and enumeration controls.

9. Run a full current-tree residue scan after fixing the parser. Rename any newly visible declaration; do not add an allowlist merely because a violation is numerous.

A parse failure, decode failure, read failure, missing expected file, or unclassified declaration cannot mean “no violation.”

---

# Blocking finding 3 — `Emit.Image` authority — SUPERSEDED BY ACCEPTED AMENDMENT A006

This finding asked for a private `Emit.Image` constructor under Charter §22. That is impossible while the
certified transport kernel-reduces `Emit.transport img`: opaque module ascription removes the projection
bodies the reduction needs. Isolated by experiment during this repair (`Module Images : IMAGE` fails
materialization with *"expected a directory-entries list"*; `Module Images <: IMAGE` — same signature,
checked, representation not hidden — emits correctly).

Accepted amendment **`FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`** (Rob, `2026-07-26`; Governance `D-26`) settles
the topology and replaces this finding. The binding contract is now:

- `Emit.Mint.Token` is opaque and indexed by the exact `Safe.Program`, exact `go.mod` bytes and exact `.go`
  file map; its raw constructor is private and `Emit.Mint.issue` is the sole authority-producing operation;
- `Emit.Image` is a REDUCIBLE carrier retaining the exact `Safe.Program`, the exact bytes and that exact
  token; its visible pack constructor is not a mint, because it cannot be applied without an inhabitant of
  the indexed token type;
- the image stores no duplicate equality-proof authority fields — exactness is derived from the token;
- `Emit.of_safe` is the canonical packer and `Emit.of_safe_at` transports the same authority along the exact
  source equality; `MakeImage` is deleted with no alias, notation, wrapper or compatibility constructor;
- the full required topology, the mandatory proof-of-mechanism test, and the permanent controls are specified
  in the accepted disposition and recorded in
  `.review/fcb/amendments/FCB_AMENDMENT_A006_INTRINSIC_EMIT_IMAGE_MINT.md`.

Definition-of-done items 13, 14 and 20 below are superseded accordingly: what must be inaccessible is the raw
TOKEN constructor, not the carrier pack constructor, and no current document may describe the carrier
constructor as private.

---

# Blocking finding 4 — the coarse legacy result peer still survives

## Current defect

`Compilable.v` still publishes:

```coq
Inductive LegacyClass :=
| LegacyOk
| LegacyTyping
| LegacyPackageMainCount
| LegacyBuildOutput.

legacy_class_of_diags
legacy_compile_class
compile_class
compile_class_spec
compile_class_input_equal
compile_class_build_permutation
```

The source and `ARCHITECTURE.md` call this a “legacy coarse class” and a compatibility projection. It collapses the structured `Outcome` and exact `DiagnosticReason` list into four tags.

It has no production consumer. Its remaining consumers are fixture statements, invariance theorems, gate entries, and documentation about the compatibility view.

The exact structured authority already exists. In particular, `erased_report_build_permutation` proves equality of the exact cross-snapshot report under file-node permutation. The legacy class adds no fact which the structured outcome/report cannot state more exactly.

This violates the standing rules against compatibility paths, collapsed semantic outcomes, and public peers retained only for old theorem shapes. The old C3 plan's conditional wording — “if compatibility projections remain” — is not authority to keep one after the project adopted the no-compatibility law.

## Required repair

1. Delete `LegacyClass`, `legacy_class_of_diags`, `legacy_compile_class`, `compile_class`, and their constructors.

2. Restate every live fixture over one of:

   - the exact `Compilable.Outcome` branch;
   - the exact retained `failure_diagnostics`;
   - the exact `DiagnosticCode` / `DiagnosticReason` list;
   - `erased_elaboration_report` where cross-snapshot equality is required.

3. Retain `erased_report_build_permutation` or the strongest exact current theorem as the order-independence authority. Do not replace it with another coarse enum.

4. Delete `diag_is_typing`, `diag_is_package`, `diag_is_build_output`, `existsb_*` helpers, and related lemmas if their only surviving purpose was to implement or prove the legacy class. Keep a helper only when an exact structured diagnostic theorem still consumes it.

5. Replace examples such as:

   ```coq
   legacy_compile_class (compile p) = LegacyTyping
   compile_class p = LegacyTyping
   ```

   with exact returned-failure and exact diagnostic assertions.

6. Remove the legacy-class gate entries and replace them only with load-bearing exact report/outcome theorems. Do not preserve the readable assumption count with aliases.

7. Delete present-tense compatibility prose from `ARCHITECTURE.md`, gate comments, and source comments. Git history records the old projection.

8. Add the deleted names to the retired-surface gate so the compatibility peer cannot return under another repair.

No replacement compatibility enum, wrapper, alias, re-export, or deprecated theorem family is permitted.

---

# Blocking finding 5 — the current corpus and source prose do not state one truth

## Current contradictions

At the reviewed ref:

- `.review/NEXT_STEPS.md`, `FIDO_FCB_INDEX.md`, and the Human Review Index say candidate `12b1bc...` is complete and awaiting review.
- `.review/REVIEW_REQUEST.md` is still `state: closed`, says `deda8bd...` is blocking, and says repair 16 is active and no review is requested.
- `FIDO_FCB_ROADMAP.md` still names `deda8bd...` as the current blocker and repair 16 as the sole active work.
- `PROGRESS.md` and `.review/SOURCE_FOREST_STATUS.md` still name `deda8bd...` and repair 16 as current.
- the Architecture Charter still says the active repair 16 must satisfy the C4 retention obligation.
- `FIDO_FCB_MODEL_OPERATIONS.md` begins its consultation sequence with the corrupted sentence:

  ```text
  Typing.Resolved one exact repository ref.
  ```

  It must say `Resolve one exact repository ref.`

- `Compilable.v` still says `[Core] deliberately stays TRANSPARENT` and that `MakeCore` is not a forgery surface, directly contradicting the implemented sealed `Core`.
- the Docker sealed-test comment still says an `Elaboration` is assemblable from any core, which is false after repair 16.
- `CLAUDE.md` still presents the pipeline as `Admissible -> Property` rather than the current module scopes `Compilable -> Safe`.
- `ARCHITECTURE.md` still uses retired layer headings, cites the deleted `Compilable.compile_projects_elaborate`, says `Emit.MakeImage` is public, and preserves the legacy compile-class peer.

The FCB Index and Human Review Index also overclaim that all repair-16 findings are closed. Findings 1 and 2 above are not closed, and the whole-system review found the pre-existing `Emit.Image` and legacy-class defects.

## Required current state after this review

Install this directive verbatim as the active repair authority, using the repository's established current-only naming convention. Retire the repair-16 authority from the live tree once repair 17 is installed; Git history is the archive.

Update the live corpus so every current document agrees on all of these facts:

- `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c` is BLOCKING;
- it is the eighteenth blocked C4 implementation candidate;
- repair 17 is the sole active C4 work;
- package-reference provenance from the retained visit is closed and must not regress;
- `Compilable.Core` sealing is closed and must not regress;
- constructor residue was renamed, but the naming gate still has the field-parser and unreadable-text holes;
- returned-object fixtures remain incomplete at the causal-history boundary;
- `Emit.Image` construction is not sealed and must be repaired under Charter §22;
- the legacy coarse result peer must be deleted;
- C4 is not accepted;
- only Rob can accept C4;
- C5, post-C4 features, broad source cleanup, and proof partitioning remain forbidden;
- A001 through A005 remain accepted;
- Governance D-01 through D-25 remains the current range;
- no Closure row, Latitude row, Acceptance Gate row, roadmap assignment, target policy, accepted program set, Go-language meaning, or generated byte changes in repair 17.

At minimum inspect and update, where affected:

```text
.review/fcb/current/INDEX.md
.review/fcb/current/FIDO_FCB_INDEX.md
.review/fcb/current/FIDO_FCB_GOVERNANCE.md
.review/fcb/current/FIDO_FCB_ARCHITECTURE_CHARTER.md
.review/fcb/current/FIDO_FCB_FIXED_POINTS.md
.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md
.review/fcb/current/FIDO_FCB_ROADMAP.md
.review/fcb/current/FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md
.review/fcb/current/FIDO_FCB_MODEL_OPERATIONS.md
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
.review/SOURCE_FOREST_STATUS.md
.review/OPEN_QUESTIONS.md
PROGRESS.md
ARCHITECTURE.md
CLAUDE.md
Compilable.v
Emit.v
Dockerfile
gate/Assumptions.v
```

Do not edit every listed file mechanically. Change only affected current claims. Delete stale current-state prose instead of adding a second history narrative.

Do not amend the FCB to legalize public `Emit.MakeImage`, the legacy class, an incomplete capability fixture, or a fail-open gate. The existing FCB already requires their repair.

---

# Verification and gates

## Independent evidence from this review

The review runtime independently established:

- archive SHA-256 as recorded above;
- `python3 tools/naming-gate.py --root . --snapshot` reports green on the candidate;
- the adversarial upper-case-field probes return no violation;
- a complete synthetic snapshot with an invalid-UTF-8 selected Markdown file returns no violation;
- there are no lower-case constructors left in the current Rocq scope;
- there are no current upper-case/camel-case record fields in the current Rocq scope;
- `tools/ocaml-origin-gate.sh` passes;
- `tools/generated-output-gate.sh` passes;
- Python tools compile and shell scripts pass `sh -n`;
- pinned-shape Go execution with Go 1.23.2, `GOOS=linux`, `GOARCH=amd64`, `GOAMD64=v1`, and `CGO_ENABLED=0` builds successfully;
- stdout, stderr, and exit status match `e2e/golden.stdout`, `e2e/golden.stderr`, and `e2e/golden.exit`;
- reviewed generated hashes are:

  ```text
  d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa  go.mod
  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de  main.go
  ```

The review runtime did not contain Docker, Rocq, Dune, OCaml, or the EditorConfig executable, so it could not independently rerun `make prove`, `make check`, extraction/materialization, the staged hook, or `make fmt`. Claude's reported green run is evidence, not acceptance.

## Required proof and execution gates

Run all of these against the final exact working tree:

```text
make names
make prove
make e2e
make check
make regenerate
make regen-guard
make fmt
```

Then stage the exact candidate and run the repository pre-commit hook against the exported staged snapshot. Do not use `--no-verify` for the candidate freeze.

The final proof gate must include:

- complete Dune theory build;
- exact root-module coverage;
- readable `Print Assumptions` coverage for every retained load-bearing public surface;
- whole-theory assumption closure over constants, inductives, and named assumptions;
- adversarial assumption self-tests;
- negative client tests for `Compilable` constructors and builders;
- negative client tests for `Emit.Image` constructors;
- a positive client using only `compile -> Safe.certify -> Emit.of_safe`;
- complete returned-object accepted, rejected, and twin-occurrence fixtures;
- corrected naming-gate controls and enumeration/read-failure tests.

A changed readable-surface count is acceptable only when declarations were truly deleted, replaced, or added. Zero assumptions is mandatory. Do not preserve a count with aliases or dead theorem copies.

## Required searches

Classify every surviving occurrence; do not rely on a zero count alone.

```text
rg -n 'build_elaboration_core|build_compilation_input|build_expression_phase|Index\.index_program|\belaborate\b' \
  Compilable.v gate e2e Safe.v Emit.v Render.v

rg -n 'MakeImage|ImageRepresentation|Emit\.MakeImage|of_safe_at' .

rg -n 'LegacyClass|LegacyOk|LegacyTyping|LegacyPackageMainCount|LegacyBuildOutput|legacy_compile_class|legacy_class_of_diags|compile_class' .

rg -n 'Core.*TRANSPARENT|MakeCore.*proof obligation|Elaboration.*assemblable from any core|compile_projects_elaborate' .

rg -n '12b1bc|deda8bd|repair 16|repair-16|repair 17|repair-17|C4.*BLOCK|C4.*accepted' \
  .review .review/fcb/current PROGRESS.md ARCHITECTURE.md CLAUDE.md

rg -n 'Admitted|admit|Axiom|TODO|FIXME|fallback|compatib|legacy|placeholder|fuel|gas' \
  --glob '*.v' --glob '*.ml' --glob '*.mlg' --glob '*.py' --glob '*.sh' --glob 'Dockerfile' --glob 'Makefile' .
```

Expected classifications:

- internal builders may occur only inside their sealed implementation, general implementation proofs which own them, and clearly marked history/negative tests;
- no direct returned-object fixture may reconstruct through them;
- no external `Emit.Image` constructor occurrence may survive except a negative test proving it is unreachable;
- no legacy class declaration or consumer may survive;
- axioms may occur only in transient adversarial test text whose required outcome is rejection;
- no production fuel, fallback, compatibility path, placeholder, or trusted semantic shortcut may survive.

## Generated artifacts

The final candidate must preserve exactly:

- `go.mod` path and bytes;
- every generated `.go` path and byte;
- generated header first line;
- reviewed stdout;
- reviewed stderr;
- reviewed exit status;
- fresh `go build ./...` success under the pinned target;
- validate-before-publish ordering;
- transport-only handwritten OCaml boundary.

No post-hoc rewrite, formatting pass, or regenerated-equivalent byte stream is acceptable. Compare the tracked candidate against a pristine image materialized from the same staged proof inputs.

---

# Definition of done

Repair 17 is complete only when all of the following are true in one exact candidate ref:

1. package references are still built from the retained input visit.
2. package diagnostics still consume the exact retained package-reference object.
3. `Compilable.Core`, its representation, constructor, builder, and mint helpers remain sealed.
4. accepted and rejected capability values still retain the exact judged core.
5. the accepted direct fixture exposes the full retained forest, index, outcomes, trace, four causes, facts, package object, layout, plan, raw/final diagnostics, Safe retention, and Emit consumption through the returned `cp`.
6. the rejected direct fixture exposes the full retained forest, index, outcomes, trace, conversion and child causes, predecessor outcome, annotation context, singleton reason, package object, layout, plan, and raw/final diagnostics through the returned `fail`.
7. no direct fixture states, proves, or uses equality to an independently rebuilt core or phase.
8. obsolete concrete builder-based fixture peers are deleted.
9. the naming gate parses and rejects upper-case record fields regardless of position.
10. the naming gate fails on every selected file read/decode error.
11. the naming gate's new adversarial controls prove both failures.
12. working-tree and staged-snapshot naming modes remain enforced.
13. `Emit.Image` is abstract to clients.
14. every raw image constructor and arbitrary-byte image helper is inaccessible.
15. `Emit.of_safe` is the canonical public image mint from the exact accepted safety path.
16. the materializer's assumption-closure guard remains effective without a public raw image constructor.
17. `LegacyClass` and every compatibility projection/alias built around it are deleted.
18. all affected fixtures use exact outcomes and structured diagnostics.
19. no stale source comment claims `Core` is transparent or an elaboration is client-assemblable.
20. no current document says `Emit.MakeImage` is public.
21. `FIDO_FCB_MODEL_OPERATIONS.md` says `Resolve one exact repository ref.`
22. the FCB Index, Roadmap, Human Review Index, NEXT_STEPS, Review Request, status documents, architecture, and source comments state one current repair-17 truth.
23. A001 through A005 and D-01 through D-25 remain intact.
24. C4 remains unaccepted pending a new human review by Rob.
25. C5, broad cleanup, proof partitioning, and post-C4 work remain forbidden.
26. all retained proof surfaces are assumption-free.
27. all negative client constructor tests fail for the intended absent-name reason.
28. the positive public pipeline client compiles.
29. the whole pinned Go e2e passes against the reviewed goldens.
30. generated Go and `go.mod` are byte-identical to the reviewed baseline.
31. the exact staged snapshot passes every hook gate.
32. the final freeze names one implementation candidate and does not claim C4 acceptance.

Green commands are necessary evidence. They are not sufficient. Before freezing, inspect the public constructor topology, the actual returned-object theorem statements, the image mint boundary, the naming parser's full input domain, and all live current-state documents by hand.

---

# Execution cadence and notification

Use `/loop 3m` to continue implementing, checking, simplifying, and re-reading this directive until every required item is complete or a real blocker prevents further progress.

Do not stop for routine progress reports, green intermediate checks, partial completion, or a desire for confirmation. Commit coherent steps as needed, but continue the loop until the final candidate is frozen or work is genuinely blocked.

When complete or blocked, use the notification tool to notify Rob.

If complete, report:

- exact implementation candidate SHA;
- exact documentation-only freeze SHA, if separate;
- commits and purpose;
- proof/gate counts;
- negative client test inventory;
- direct accepted/rejected fixture theorem names and what each statement exposes;
- image-sealing test inventory;
- naming-gate adversarial controls;
- deleted legacy surfaces;
- generated artifact hashes;
- full command results;
- FCB/current-document files changed;
- confirmation that C4 remains unaccepted pending Rob's review.

If blocked, report the exact conflicting contract or failed obligation, the evidence, the last good commit, and the exact human decision required. Do not improvise around the blocker.
