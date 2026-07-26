# Fido C4 Implementation Review — BLOCKING — Repair 16 Directive

## Authority and use

Rob is the final human authority.

Rob's delivery of this file to Claude Code records the review disposition and authorizes only the repair stated here. Claude Code must implement this directive exactly. If implementation evidence conflicts with an accepted FCB contract, fixed point, ADR, gate, or this directive, stop at that boundary and report the exact conflict. Do not weaken the contract, improvise around it, or substitute a nearby result.

Install this file verbatim as:

```text
.review/C4_IMPLEMENTATION_REPAIR_16.md
```

C4 repair 16 is the sole next implementation task. C5, post-C4 features, the broad source cleanup, and proof-module partitioning remain forbidden until C4 is accepted.

## Exact review basis

Uploaded archive:

```text
fido-main - 2026-07-26T110412.844.zip
```

Archive freeze head:

```text
25bcd7aa6b53f1e506a32c5077990a884bea8574
```

Implementation candidate frozen by that documentation-only head:

```text
deda8bd91dbfebf75895c8786732a4ed9d7952f2
```

The freeze head is one documentation-only commit above the implementation candidate. Review findings about implementation apply to `deda8bd91dbfebf75895c8786732a4ed9d7952f2`. Review findings about current documentation apply to the uploaded freeze head.

The candidate is **BLOCKING**. It is the seventeenth blocked C4 implementation candidate. Repair 16 must begin from the current head. Do not reset, rebase, rewrite history, or discard retained repair-13, repair-14, repair-15, A001, or A005 work.

## Review disposition

Repair 15 made substantial, real progress. It did not close C4.

Four blocking defects remain:

1. package facts and package diagnostics still begin from reconstructed values rather than the exact retained visit and retained package map;
2. `Compilable.Core` and `make_core` remain public by design, contrary to the accepted opaque whole-result boundary;
3. the A005 naming gate misses lower-case constructors and therefore reports a false green over live residue;
4. the accepted and rejected "projection-only" fixtures still recover their result through equality to a rebuilt core.

The live FCB corpus also contradicts itself about the current C4 state and must be made coherent as part of the repair.

No new FCB amendment is needed for the normal repair. A001, A005, D-22, D-25, and repair 15 already require the correct result. If Claude believes a transparent, publicly constructible `Core` must remain, that is a direct contract conflict. Stop and report the exact affected Charter section, Governance decision, repair contract section, and public theorem need. Do not silently retain the weaker boundary.

## Real progress that must not regress

Keep all of the following:

- `Compilable.Core` stores the input, expression phase, package references, root layout, fresh-build plan, raw diagnostics, and final diagnostics.
- The accepted decision is indexed by the exact core it judges.
- `Compilable.Program` retains the accepted core.
- `Compilable.Failure` retains the rejected core rather than a copied diagnostic list.
- `Compilable.Facts` is an accepted view tied to the exact accepted core and acceptance evidence.
- `Compilable.compile` is the sole production mint for accepted and rejected capability values.
- The stripped `Result` / `ElaborationOK` / `ElaborationFailed` peer is gone.
- The independent `compilable_of_valid` / `elaboration_ok_core` capability builder is gone.
- The repair-13 exact `WorkIndex`, overwrite-free build, exact two-way domain, total lookup, and absence of production keyed `List.find` scans remain.
- Exact source-step identity remains. Do not replace exact retained steps with existentially equal or recomputed steps.
- `Safe.Program` retains the same accepted capability and core.
- `Emit.Image` remains sealed and emission continues from the accepted production capability.
- Working-tree and staged-snapshot naming modes remain.
- Staged-hook enforcement remains.
- The whole-theory assumption audit and adversarial self-tests remain.
- Generated `go.mod` and recursive `.go` bytes remain byte-identical.
- `Index.Program` remains during this repair. Do not delete it or turn it into a peer authority.

Do not repair any finding by restoring an old name, compatibility alias, compatibility module, wrapper, fallback, copied view, or second semantic path.

---

# Blocking finding 1 — package provenance still starts from a rerun

## Current defect

`Compilable.v` already has the correct explicit builder:

```coq
program_package_refs_from_visit idx visit
```

But the convenience function is:

```coq
program_package_refs idx :=
  program_package_refs_from_visit idx (program_visit p)
```

`build_elaboration_core` currently builds the package map through that convenience function:

```coq
let refs := program_package_refs (index input)
```

That calls `program_visit p` again instead of consuming the exact `input_visit input` object retained in the core input.

The constructor then stores an equality which proves that the independently rebuilt package map equals the map that would have been built from the retained visit. The stored values are extensionally connected, but the production causal chain still begins from a rerun.

The same defect remains in package diagnostics. `package_bucket_diagnostics` accepts only an index and internally calls `program_package_refs idx`. The core's raw diagnostic builder therefore does not consume the exact `refs` object already retained in that core. It reconstructs a package map for diagnostics.

A001 rejects this pattern. Equality to a canonical rerun can be a specification or determinism theorem. It is not production provenance.

## Required repair

Make the production construction chain direct:

```text
retained Input
  -> exact input_visit
  -> exact package refs built from that input_visit
  -> exact package proofs about that stored map
  -> exact package diagnostics built from that stored map
  -> raw diagnostics
  -> final diagnostics
  -> Decision over that same Core
```

At minimum:

1. In `build_elaboration_core`, build `refs` with the exact retained visit:

   ```coq
   let refs :=
     program_package_refs_from_visit
       (index input)
       (input_visit input)
   ```

2. Refactor package diagnostics so the production function accepts the exact package map and the proof data it needs. A shape equivalent to this is acceptable:

   ```coq
   package_bucket_diagnostics_from_refs
     refs
     refs_present
     refs_len
     refs_belongs
   ```

   The exact argument list may differ, but the function must consume the retained `refs` object. It must not call `program_package_refs`, `program_visit`, `program_blocks`, `visit_file`, or another package-map builder.

3. Build raw diagnostics from:

   ```coq
   phase_diags ph
   ++ package_bucket_diagnostics_from_refs refs ...
   ```

4. Store the exact `refs`, exact raw diagnostics, and exact final diagnostics produced in that one `let` chain.

5. Make the construction laws for the built core reduce by `reflexivity` where the values are directly retained. Do not add a new equality-to-rerun bridge and call it retention.

6. A theorem such as:

   ```coq
   core_package_refs_canonical
   ```

   may remain as a separate specification theorem proving the retained map agrees with the canonical source-level function. No production query, capability fixture, diagnostic builder, or later proof may need that theorem to recover the stored object.

7. If `program_package_refs` and `package_bucket_diagnostics` have no distinct current specification consumer after this refactor, delete them. Do not keep convenience wrappers for possible future use.

## Required checks

Add load-bearing theorem surfaces which show:

- the built core's package map is definitionally the result of folding its own retained visit;
- the built core's package diagnostics consume its own retained package map;
- the raw diagnostic list contains the exact phase diagnostics and the exact diagnostics built from that retained map;
- no package-map builder is called after the exact map has been retained;
- accepted and rejected queries project the same package object that the decision used.

Gate those surfaces in `gate/Assumptions.v` and in the whole-theory audit.

Search all production and fixture paths for:

```text
program_package_refs (
package_bucket_diagnostics (
program_visit
program_blocks
visit_file
```

Classify every surviving occurrence. A canonical specification theorem may use a source function. Production construction, queries, capability fixtures, `Safe`, `Render`, `Emit`, witnesses, and client code may not rebuild the package object.

---

# Blocking finding 2 — `Core` and `make_core` remain public

## Current defect

`Compilable.v` states that `Core` deliberately remains transparent and that `make_core` is a proof obligation rather than a forgery surface.

That is not the accepted contract.

The FCB Architecture Charter says:

- the static capability retains the exact whole elaboration;
- raw constructors and internal records remain private;
- internal work, phase, map, trace, and diagnostic forms remain retained but hidden;
- public queries project from the retained object;
- rejected elaboration retains the exact failed object behind an opaque failure interface.

Repair 15 also named `make_core` among the raw constructors that must not remain available to a client.

The current negative client fixtures prove that clients cannot call `make_program`, `make_failure`, and `make_facts`. They do not prove that `make_core` and the raw whole-elaboration representation are inaccessible.

A client cannot mint `Program` directly, so the current `Program` seal is real. But a client can still construct an independently built peer `Core`. That is the exact topology A001 was written to prevent.

## Required repair

Seal the whole-elaboration representation.

The required public result is:

- clients may name `Compilable.Core p` only if a public query or theorem needs that abstract type;
- clients may receive the exact core through `Compilable.core cp` and `Compilable.failure_core fail`;
- clients may use approved total query functions over that abstract core;
- clients cannot call `make_core`;
- clients cannot use record syntax or raw field construction to assemble a `Core`;
- clients cannot obtain a capability by pairing an independently built core with a proof;
- clients cannot obtain a failure by pairing an independently built core with a rejection proof;
- clients cannot obtain accepted facts by pairing arbitrary maps with an accepted proof.

Use a Rocq module signature, sealed implementation module, or an equivalent abstract boundary. The concrete record can remain available inside the implementation. It must not escape the public interface.

Do not solve this with:

- a renamed public constructor;
- a private-looking prefix;
- a notation;
- a compatibility wrapper;
- `Arguments` changes;
- comments which say clients should not call it;
- a test which merely avoids calling it.

The constructor and raw representation must be absent from the client-visible interface.

## Public query boundary

Expose only the query and theorem surfaces the current code and FCB need. These can include abstract-core queries equivalent to:

```coq
core_input
phase
core_package_refs
core_layout
core_plan
core_raw_diagnostics
core_diagnostics
```

The exact names may remain where they satisfy A005. They must be functions exported by the sealed interface, not raw record projections which expose a public constructor topology.

Keep:

```coq
core : forall cp : Program, Core (source cp)
failure_core : forall {p}, Failure p -> Core p
```

when those are needed for exact retained-object theorems. The returned `Core` must be abstract.

Seal `build_elaboration_core` as an internal production constructor unless a distinct current specification surface truly needs to call it. Public capability fixtures and external clients must not be able to use it as a reconstruction root.

## Required negative client fixtures

Add separate client-level checks which fail unless all of the following are inaccessible:

- the concrete `Core` constructor;
- record construction of `Core`;
- any raw `Program` constructor;
- any raw `Failure` constructor;
- any raw accepted-`Facts` constructor;
- the internal mint which accepts an arbitrary `Elaboration`;
- any helper which accepts an arbitrary core plus proof and returns `Program` or `Failure`.

Add positive controls which show a client can still:

- call `Compilable.compile`;
- destruct `Outcome`;
- query the exact accepted core through a returned `Program`;
- query the exact rejected core through a returned `Failure`;
- pass the accepted capability to `Safe.certify`;
- emit through the accepted `Safe.Program`.

The negative fixtures must run in `make prove` and the staged build. Add them to the load-bearing gate inventory.

---

# Blocking finding 3 — the A005 naming gate is false-green for constructors

## Current defect

The snapshot naming gate reports success.

Direct negative tests show that it accepts both of these declarations:

```coq
Record BadRecord := make_bad_record { value : nat }.
Inductive Bad := make_bad : Bad.
```

The parser causes the hole:

- inductive constructors are extracted only when the first character is already uppercase;
- record constructors are extracted only when the first character is already uppercase;
- the casing check does not classify `constructor` as an UpperCamelCase declaration kind.

The gate therefore cannot see the invalid constructors which it is supposed to reject.

An independent scan of the uploaded snapshot found 51 lower-case constructors. They include:

```text
make_constant
make_decimal
make_value
make_typed_constant
make_file
make_file_node
make_module_spec
make_program
make_identifier
make_supported_type
pack_resolved
make_package_summary
make_package_ref
make_erased
make_expression_fact
make_type_name_fact
make_type_name_facts
make_input
make_work
make_work_index
make_forest
make_conversion
make_conversion_step
make_accumulator
make_outcomes
make_expression_fact_table
make_annotated_work
make_expression_facts
make_diagnostics
make_phase
make_core
make_facts
make_elaboration
make_failure
make_image
make_meta
make_occurrence
make_key
make_file_ref
make_node_ref
make_syntax
```

The full scan found 51 occurrences across the root Rocq modules. Do not rely only on this list. Fix the gate first, then let the corrected gate produce the authoritative residue.

There is also stale live-role prose:

- `Compilable.v` still begins with `Admissible —`;
- `Safe.v` still begins with `Property —`.

Those headers present retired module names as the current file role.

## Required repair

1. Parse constructors without assuming they already satisfy the casing rule.

   Constructor extraction must accept a general Rocq identifier, then validate its case. Do not use an uppercase-only regular expression as the parser.

2. Apply the UpperCamelCase rule to every inductive, variant, and record constructor.

3. Add fail-closed self-tests for at least:

   ```coq
   Record GoodType := make_bad { value : nat }.
   Inductive GoodType := make_bad : GoodType.
   ```

4. Add must-accept controls for valid UpperCamelCase constructors.

5. Run the corrected gate over every tracked and untracked nonignored Rocq source in working-tree mode and over the exact staged exported snapshot in staged mode.

6. Rename every lower-case constructor reported by the corrected gate. Use the role within its module. Do not add aliases or re-exports for the old constructor names.

7. Update all constructor calls, pattern matches, proof scripts, generated interfaces, fixtures, gates, comments, and documentation in one coherent migration.

8. Rewrite stale source headers and current prose so they name the current module and current roles. Historical old names may appear only in clearly marked history where they are still needed. Prefer deletion because Git already keeps history.

9. Delete:

   ```text
   .review/C4_REPAIR_15_RENAME_LEDGER.tsv
   ```

   Its own header says to delete it before final freeze. Git history retains the migration.

10. Keep the naming gate fail-closed when file enumeration, snapshot export, parsing, or self-tests fail.

## Required proof against recurrence

The naming gate's own test suite must fail if constructor parsing regresses.

Add a repository-level check which confirms that the gate examined every root `.v` file declared by Dune and every other Rocq fixture or gate file in its stated scope. A parse failure or unclassified declaration must not silently become "no violation."

Do not claim A005 complete until the corrected gate passes against:

- the working tree;
- the exact staged snapshot;
- its must-reject controls;
- its must-accept controls;
- the full live repository.

---

# Blocking finding 4 — direct capability fixtures still reconstruct through builder equality

## Current defect

Repair 15 required accepted and rejected fixtures which query only the returned objects.

The current accepted fixture:

```text
deep_nested_capability_retains_elaboration
```

obtains a `Program`, but its work-forest count is then carried through `Hcore`, an equality to:

```coq
build_elaboration_core ... (Index.index_program ...)
```

The helper theorem used for that count separately builds an input, phase, index, and forest.

The current rejected fixture:

```text
deep_fail_capability_retains_rejected_elaboration
```

puts this reconstruction equality in its public theorem statement:

```coq
failure_core fail =
  build_elaboration_core
    deep_fail_program
    (Index.index_program deep_fail_program)
```

It then rewrites through that equality to prove layout, plan, and diagnostic facts.

These may describe a canonical specification run. They do not prove that a client can obtain the complete result from the returned capability or failure itself.

## Required repair

Rewrite the direct production fixtures around the actual `compile` outcome.

### Accepted fixture

Obtain the capability through:

```coq
program_of_admissible
```

or an equivalent helper which destructs `compile p` once and returns the exact `cp` from its `Compiled` branch.

After `cp` exists, the fixture must prove every claim from:

```text
cp
source cp
core cp
program_input cp
program_phase cp
facts cp
accepted cp
```

and general theorems about those projections.

The fixture statement and proof must not use:

```text
build_elaboration_core
build_compilation_input
build_expression_phase
Index.index_program
elaborate
program_visit
a source fact-table builder
```

to recover the capability's data.

Required accepted fixture content:

- the exact retained input;
- the exact retained phase;
- the retained work forest and exact standard work index;
- the retained outcome table and trace;
- all four conversion causes at their exact source occurrences;
- the exact expression and type-name fact objects;
- the exact package-reference object;
- the exact root layout and build plan used by the accepted decision;
- the exact empty raw and final diagnostic lists;
- `Safe.certify` retaining the identical capability and abstract core;
- `Emit.of_safe` consuming that accepted path;
- equal-valued twin expressions remaining distinct retained occurrences;
- the concrete deep-chain work count, stated and proved over `core cp`, not over a rebuilt core.

If a new general theorem is needed, state it over an actual equation:

```coq
compile p = Compiled cp Hcp
```

and conclude a property of `core cp`. Its public statement must not return equality to an independently rebuilt core.

### Rejected fixture

Destruct the actual `compile p` result and obtain the exact returned `fail`.

Then prove every result from:

```text
fail
failure_core fail
failure_input fail
failure_phase fail
failure_package_refs fail
failure_layout fail
failure_plan fail
failure_diagnostics fail
rejected fail
```

The fixture statement and proof must not call or mention:

```text
build_elaboration_core
build_compilation_input
build_expression_phase
Index.index_program
elaborate
```

as a way to recover the failed object.

Required rejected fixture content:

- exact failed input and phase;
- exact work forest and index;
- exact outcome table and causal trace;
- innermost conversion-failure direct cause;
- exact prior operand outcome;
- enclosing child-failure causes;
- exact retained annotation context;
- exact singleton `InvalidConversion` reason;
- exact retained package refs, layout, and plan used by the rejected decision;
- final diagnostics projected directly from `failure_core fail`;
- a proof that rejection is nonempty from `rejected fail`;
- no copied diagnostic list.

### Enforce the client boundary

Place the projection-only fixtures in a separate client module when practical. That module must import only the public sealed API. If internal builders are private, the type checker itself then enforces the no-reconstruction rule.

Gate the accepted, rejected, and twin-occurrence fixture theorems in `gate/Assumptions.v`.

Delete or restate `compile_accepted_shape` and `compile_rejected_shape` if their only purpose is to expose equality to a rebuilt core. A canonical equality theorem may remain only when it has a distinct specification purpose, is named as such, and is not used by production queries, capability extraction, `Safe`, `Emit`, or the direct fixtures.

---

# Blocking finding 5 — the current FCB corpus contradicts itself

## Current defect

The current FCB Index and `.review/NEXT_STEPS.md` say repair 15 is complete against `deda8bd...`.

The live Roadmap still says:

- repair-13 candidate `9d5246e...` is the current blocker;
- repair 14 is the next work;
- the sequence is repair 14, human review, then C5;
- the accepted-amendment banner omits A005.

The live Architecture Charter still says the active defect belongs to repair 13 and that repair 14 must establish whole-result retention.

This is not one coherent current corpus.

The FCB Index also overclaims that:

- all A005 names are complete and gated;
- `Core` is fully sealed;
- all three prior blocker classes are closed.

Those claims are false while the findings above remain.

## Required repair

Update every current authority together so one exact ref states one current truth.

At minimum inspect and update:

```text
.review/fcb/current/INDEX.md
.review/fcb/current/FIDO_FCB_INDEX.md
.review/fcb/current/FIDO_FCB_GOVERNANCE.md
.review/fcb/current/FIDO_FCB_ARCHITECTURE_CHARTER.md
.review/fcb/current/FIDO_FCB_FIXED_POINTS.md
.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md
.review/fcb/current/FIDO_FCB_ROADMAP.md
.review/fcb/current/FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
.review/SOURCE_FOREST_STATUS.md
.review/OPEN_QUESTIONS.md
PROGRESS.md
ARCHITECTURE.md
CLAUDE.md
```

Do not edit every file merely because it is listed. Inspect each one and change only affected current claims. The final corpus must state:

- `deda8bd...` is blocked by this review;
- `25bcd7...` is its documentation-only freeze, not a separate implementation candidate;
- repair 16 is the sole active C4 work;
- C4 is not accepted;
- C5 and post-C4 work remain forbidden;
- A001 through A005 remain accepted;
- D-01 through D-25 remain the current Governance range;
- the remaining defects are exact retained package provenance, abstract `Core`, complete constructor naming enforcement, direct capability fixtures, and document coherence;
- the sixteen earlier blocked candidates plus `deda8bd...` are recorded correctly;
- no current document describes repair 13 or repair 14 as the active work;
- no current document says repair 15 is complete after this review;
- no current document claims a gate or seal stronger than the code provides.

Git history is the archive. Remove stale current-state narratives instead of retaining multiple present-tense histories.

No Closure row, Latitude row, Acceptance Gate, roadmap row assignment, target policy, accepted program set, Go-language meaning, or generated byte may change in repair 16.

---

# Verification requirements

## Proof and assumption gates

Run and keep green:

```text
make prove
```

This must include:

- full Dune theory build;
- readable `Print Assumptions` gates for all load-bearing public surfaces;
- exact module coverage;
- whole-certified-theory audit over constants, inductives, and named assumptions;
- adversarial assumption self-tests;
- capability and constructor opacity client tests;
- direct accepted and rejected capability fixtures;
- corrected naming-gate self-tests.

The exact readable-surface count may change only because repair 16 deletes, renames, or replaces real surfaces. Zero assumptions is mandatory. Do not preserve a count by gating aliases or dead theorem copies.

## Working-tree and staged checks

Run:

```text
make check
```

Run the pre-commit hook against the exact staged snapshot.

The staged snapshot must independently enforce:

- naming;
- constructor opacity;
- module coverage;
- generated output path set and bytes;
- generated file modes;
- OCaml transport boundary;
- no foreign Go;
- no nested module;
- whole proof build and assumption closure as required by the current hook contract.

No enumeration command may fail open. No gate may scan zero files and report success.

## End-to-end and generated output

Keep green:

```text
go build ./...
```

under the pinned target:

```text
GOOS=linux
GOARCH=amd64
GOAMD64=v1
CGO_ENABLED=0
```

Keep witness standard output, standard error, and exit status equal to the reviewed goldens.

Regenerate through the sole supported path. Confirm that tracked `go.mod` and every tracked generated `.go` file are byte-identical to the pre-repair-16 baseline.

Repair 16 must not change generated Go bytes.

## Required searches

Before freeze, search the exact working tree and staged snapshot for:

```text
make_core
make_program
make_failure
make_facts
build_elaboration_core
build_compilation_input
build_expression_phase
Index.index_program
program_package_refs
package_bucket_diagnostics
program_visit
Admissible —
Property —
C4 repair 14
repair-13 implementation candidate
9d5246e
C4_REPAIR_15_RENAME_LEDGER
```

Do not blindly require zero occurrences. Classify each survivor.

Allowed examples:

- an internal concrete constructor inside a sealed implementation;
- a clearly named canonical specification theorem;
- a historical Git-facing statement which is explicitly marked as history and still has a current purpose;
- the blocked-candidate ledger.

Forbidden examples:

- client-visible raw constructor;
- production reconstruction;
- direct fixture reconstruction;
- stale present-tense current state;
- compatibility alias;
- a temporary ledger which ordered its own deletion.

Record the classification in the implementation report.

---

# Scope restrictions

Repair 16 must not include:

- C5 work;
- runtime machine work;
- broad source-comment deletion;
- source-file module partitioning;
- proof-check parallelization;
- new language features;
- new accepted programs;
- new diagnostic classes;
- target changes;
- `uintptr`;
- a compatibility layer;
- aliases for renamed constructors;
- a new general abstraction not required to close a finding;
- removal of `Index.Program`;
- a weaker theorem statement disguised as cleanup;
- arbitrary bounds, fuel, gas, or step budgets.

The broad source cleanup and proof-unit partition are still desired. They must be separate post-C4 candidates:

1. first, a ruthless source cleanup with no build-topology change;
2. then, measured proof-unit partition and a single-build parallel Docker DAG.

Do not mix either into this correctness repair.

The existing profiling path does not count as proof parallelization. Do not expand it during repair 16.

---

# Definition of done

Repair 16 is complete only when all of the following are true:

1. `build_elaboration_core` builds package refs directly from its own retained `input_visit`.
2. Package diagnostics consume that exact retained package map.
3. No production or direct fixture path rebuilds package refs after retention.
4. `Core` is abstract to clients.
5. `make_core` and the raw whole-elaboration record are unavailable to clients.
6. `Program`, `Failure`, and `Facts` remain sealed.
7. `compile` remains the sole capability mint.
8. Accepted and rejected fixtures use only the returned objects and public projections.
9. No direct fixture states or uses equality to `build_elaboration_core`.
10. The corrected naming gate recognizes constructors regardless of their current case.
11. Every live constructor obeys A005 casing and naming.
12. No old constructor alias or compatibility export remains.
13. Stale `Admissible —` and `Property —` file-role headers are gone.
14. The temporary repair-15 rename ledger is deleted.
15. Working-tree and staged naming checks fail closed.
16. Negative client tests prove the raw core constructor is unavailable.
17. Full proofs and the whole-theory assumption audit are green.
18. Extraction, OCaml, Docker, sink, and e2e paths are green.
19. Generated Go bytes are unchanged.
20. The complete live FCB and review corpus states one current repair-16 boundary.
21. C4 remains unaccepted pending a new human review by Rob.
22. C5 and post-C4 work remain forbidden.

A green build without these topology results is not completion.

---

# Required implementation order

Use this dependency order:

1. Install this directive and update `NEXT_STEPS` to make repair 16 the sole active work.
2. Fix explicit retained package construction and package-diagnostic consumption.
3. Seal `Core` and its constructor.
4. Rewrite capability fixtures against the public returned objects.
5. Fix constructor parsing in the naming gate.
6. Add constructor negative controls.
7. Apply the complete constructor rename with no aliases.
8. Delete the temporary repair-15 rename ledger.
9. Repair stale source prose.
10. Run focused Rocq and gate checks.
11. Run the full proof, assumption, extraction, Docker, e2e, regeneration, and staged checks.
12. Update all current FCB and review documents coherently.
13. Freeze one implementation candidate.
14. Add one documentation-only freeze only if needed to record the candidate and request Rob's review.

Do not mark C4 accepted.

---

# Required report back

Return one concise implementation report which gives:

- implementation candidate SHA;
- documentation-only freeze SHA, if any;
- exact files changed;
- exact package-provenance construction before and after;
- exact public interface used to hide `Core`;
- negative client tests added;
- corrected naming-gate parser rule;
- total constructor residue found and renamed;
- direct accepted and rejected fixture theorem names;
- any canonical specification equality retained and its distinct purpose;
- every classified surviving use of the reconstruction-related search terms;
- proof and assumption results;
- working-tree naming result;
- staged-snapshot naming result;
- extraction and OCaml result;
- Docker and sink result;
- e2e result;
- generated-byte comparison;
- documentation files updated;
- confirmation that C5, broad cleanup, and proof partition were not started;
- any exact conflict which prevented full implementation.

Do not report "green" as a substitute for the required topology.
