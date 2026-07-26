# Fido — status

A concise inventory of what is DONE and the immediate frontier. Architecture lives in `ARCHITECTURE.md`;
contributor law in `CLAUDE.md`; live campaign status in `.review/SOURCE_FOREST_STATUS.md`; commit-level history
in the git log.

## GREEN — proved axiom-free (every gated `Print Assumptions` surface + the whole-theory audit)

One authority per layer, over the ONE `Syntax.Program`; every layer axiom-free in the pinned container.

- **`FilePath.T`** — intrinsic canonical relative paths (lowercase components + `.go` basename); decidable eq;
  `FilePath.parent` package key; strange paths UNREPRESENTABLE. Public component authority: `dir_components`
  (+ `dir_components_concat`), over the internal `split_slash` helper.
- **`Collections`** — the ONE standard-collection foundation: thin wrappers over pinned-stdlib `FMapAVL`
  (`FileMap` over the `FilePath.T` key, `PackageMap` over `String`) and `FMapPositive` (`NodeMap`);
  Fido authors no map/set. `Collections.file_path_text_inj`, `Collections.file_elements_equal` axiom-free.
- **`Integer`** — the ten-member `Integer.Kind` family + the ONE representability/range/keyword authority
  (`int`/`uint` pinned 64-bit, distinct from `int64`/`uint64`).
- **`Float`** — the ONE float-format authority (axiom-free over `SpecFloat`): F32/F64; exact canonical-rational
  `Float.Constant`; single-round `Float.round_ieee` (F32 directly at binary32); proof-carrying `Float.Value`; the
  bounded finite-decimal `Float.Decimal`; the double-round scar.
- **`Complex`** — the ONE complex authority over `Float`: C64/C128 via the `Complex.component_kind` mapping;
  exact `Complex.Constant`; intrinsic `Complex.TypedConstant`; general runtime `Complex.Value` (pairs of `Float.Value`,
  may be -0/inf/NaN); `Complex.Decimal`; `Complex.round_typed` (each component once).
- **`ModulePath.T`** — intrinsic narrow canonical module path; decidable eq; public component authority
  `ModulePath.segments` (+ `ModulePath.text_concat`); invalid paths UNREPRESENTABLE. **`Version`** — singleton `Go1_23`, renders "1.23".
- **`Syntax`** — `ModuleSpec` + `Syntax.Program := { Syntax.module_spec ; Syntax.files : Syntax.Files }` (may be empty); the map
  KEY is the path; a construction/view `Syntax.FileNode` = `FilePath.T` + source-owned `Syntax.MainPackage` clause + empty imports
  + `Syntax.declarations`; the sound/complete/exact duplicate-rejecting `Syntax.files_of_nodes`; `Syntax.Main`, `Syntax.Println`,
  `Syntax.BoolLiteral`/`Syntax.IntegerLiteral`/`Syntax.NegatedIntegerLiteral`/`Syntax.StringLiteral` (exact bytes)/`Syntax.FloatLiteral`/`Syntax.ComplexLiteral` + ONE source-shaped `Syntax.Convert Syntax.TypeExpr`
  conversion over the closed sixteen source names (the fourteen numeric + `byte`→uint8 / `rune`→int32 aliases).
- **`Index`** — the ONE structural occurrence-identity + navigation authority derived from one immutable
  `Syntax.Program` (imports only `Syntax`/`Collections`/`FilePath.T`): canonical file-local `positive` ids; sealed
  `Table`; the universal `index_file_source_exact`; sealed snapshot-indexed refs; the `visit_file`
  single-pass indexed traversal.
- **`Typing`** — the ONE type authority, EVIDENCE over the raw AST (no typed AST): `Typing.SemanticType` = {`Typing.BoolType`,
  `Typing.IntegerType`, `Typing.FloatType`, `Typing.ComplexType`, `Typing.StringType`}; exact untyped `Typing.Constant`; intrinsic dependently-typed
  `Typing.TypedConstant`; the ONE `Typing.convert_constant` authority; `Typing.ConstantInfo`/`Typing.resolve_constant_info`/`Typing.ConstantRepresentable`;
  `Typing.Program` map-based (respects `FilesEqual`).
- **`Admissible`** — EXACT whole-program admissibility for the pinned one-shot `go build ./...`:
  `Admissible p := fresh_build_preflight_ok p /\ SourceProgramValid p`; `SourceProgramValid := Typing.Program /\
  PackageRulesValid` (the FACTORED `PackageDeclsUnique` + `MainPackagesHaveEntry`). The readable index-free
  SPECIFICATION decision (`source_spec_valid_b`/`source_spec_package_rules_b`, for fixtures) reflects the
  factored roots directly; the PRODUCTION decision is the retained-bucket diagnostic pass, whose redeclaration /
  missing-entry / all-package diagnostics are empty IFF `PackageDeclsUnique` / `MainPackagesHaveEntry` /
  `PackageRulesValid`. The ONE `elaborate` builds one `Index.Program` + `Compilable.Elaboration`; `Compilable.compile`
  projects it (sound/complete, class-invariant under file order). Default executable name is component-based:
  cmd/go's rule (`default_exec_name_c`) applied DIRECTLY to `package_import_components`
  (`ModulePath.segments` ++ `FilePath.dir_components`, no string reparse); the import-path string is their
  `/`-join, injective in the package directory (`package_import_path_inj`). Structured `DiagnosticReason` in the exact snapshot;
  the three diagnostic layers each have an emptiness characterization; a failed preflight takes precedence.
- **`Property`** — real `Safe.Value`; `value_type`; `Safe.ValueWellFormed`; PARTIAL `eval_expr` (projects the stored canonical
  runtime value, rounded once at conversion); resolved-eval well-formedness + type preservation; `Safe.Program`.
- **`Render`** — direct renderer + source-owned package clause + go.mod; strings/floats/complexes each via ONE
  canonical spelling with an INDEPENDENT decoder + round trip; header exact first line; all-ASCII.
- **`Emit`** — provenance-gated `Emit.Image` (go.mod + `.go` map, carrying a proof both came from rendering
  one `Safe.Program`); rendered map has the same key domain + exact bytes as the source; `Emit.of_safe`.

## GREEN — executed (integration evidence, never proof)

- **Transport + validate-before-publish.** `Fido Materialize` (the SOLE Rocq transport vernac) guards provenance
  in one four-step decode (typecheck the image, reject a non-empty assumption closure, decode only the final
  `(go.mod, entries)` transport, hand to the writer) and writes the authoritative pristine into a fresh
  disposable root. There is NO public `Fido Emit`; the publication sink (`Sink.sync`) is a PRIVATE plugin
  module, reached only from `sink_test` + the tiny internal `make regenerate` apply adapter (fixed source
  `/generated`, no arbitrary root, no Go, no hashing). Validate-before-publish is the Docker DAG: building the
  `sync` image COPYs go-e2e's `/fresh-build-ok`, so a failed pinned `go build ./...` makes `sync` unbuildable;
  it publishes the ORIGINAL generated-module bytes. No checksum system exists (a checksum cannot prove a build
  succeeded); cooperating-developer threat model (the pre-commit hook's level), no deliberate-bypass resistance.
- **The sink** (`plugin/sink.ml`) — the foreign-Go-rejecting sibling-temp dirty-directory synchronizer:
  rejects foreign Go/module + nested `.fido`, stages into reserved `<final>.fido-tmp-v1` temps, installs by
  atomic rename, two-phase-recovers abandoned temps fail-closed. Exercised on dirty/adversarial trees.
- **Tracked artifact + pinned Go.** One content-addressed `generated-module` Buildx layer holds the pristine
  canonical module; the tracked root `go.mod` + recursive `.go` are verified byte-exact against it by `make
  check` (working tree) and the pre-commit hook (staged). The digest-pinned `golang:1.23-alpine` runs
  `GOWORK=off GOTOOLCHAIN=local GOPROXY=off go build ./...` over the whole tree, the witness vs reviewed
  goldens, the multi-package differential, no-main/dup-main + out-of-range/non-integer/wrong-type conversion
  rejection fixtures, and the directory-collision matrix — each through the tiny `fresh_go_build` helper: a
  fail-closed state machine that runs `go build ./...` once in a fresh disposable copy and returns the reserved
  status 125 (with no run flag, no log, no output root) for every setup / `cd` / launch failure, so an
  infrastructure failure can never be read as a Go rejection (four fault self-tests).
- **Zero project axioms**, enforced two ways in `make prove`: the count-checked `gate/Assumptions.v` (Print
  Assumptions on public surfaces) AND the Rocq-native `Fido Audit Assumptions` whole-certified-theory closure
  audit (constants + inductives + named assumptions), with a module-coverage gate and adversarial self-tests A-E.

## Source Forest campaign (ACTIVE)

Multi-checkpoint C0..C6; C0..C2 complete + human-approved; C3 (fresh-image literal-build closeout) ACCEPTED by
Rob; **C4 (source type names, compiler resolution, unified `Syntax.Convert`, `byte`/`rune` source aliases) — NOT yet
accepted; `deda8bd91dbfebf75895c8786732a4ed9d7952f2` is BLOCKING and repair 16 is the sole active C4
work** (seventeen candidates have now blocked at human Implementation Review; the withdrawn GREEN
disposition and its documentation-only acceptance commit `37c9597` are superseded — C4 is not human-accepted
until Rob accepts it). Repair 13's work index is retained and correct. The static-capability boundary now
retains the exact causal elaboration object (FCB amendment A001 / D-22): ONE `Compilable.Core` holds the input,
the phase, the package buckets, the root layout, the fresh-build plan and both diagnostic lists, each stored
with the proof that it IS the canonical value; the decision is indexed by that core; success and failure both
retain it; and `Compilable.Program` / `Compilable.Failure` / `Compilable.Facts` are SEALED, so
`Compilable.compile` is the only mint. The
production expression path is ONE `Compilable.Phase`
built from ONE retained `Compilable.Input` and driven by ONE proof-carrying retained work forest OBJECT — the
`Compilable.WorkForest` record (`build_expr_work_forest`; its stored `Compilable.forest_blocks`/`Compilable.forest_items` with `Compilable.forest_items = concat
Compilable.forest_blocks`, forward/reverse domain (`Compilable.forest_forward`/`Compilable.forest_reverse`) + key-NoDup (`Compilable.forest_keys_nodup`) + order +
operand-in-suffix (`Compilable.forest_operand_in_tail`) all carried as FIELDS; `build_forest_blocks` PRIVATE inside, its proof
returned INTO the record — no `proj1_sig` discard).  The ordered item list carries the SOURCE ORDER and nothing
else: the IDENTITY role is the SEPARATE carried field `Compilable.forest_index : Compilable.WorkIndex Compilable.forest_items` (repair 13) — a
pinned-stdlib `KeyMap` (`FMapAVL`) map built ONCE by `build_work_index` from the already-built list,
TOTAL and overwrite-free because it DEMANDS `Compilable.forest_keys_nodup` as a proof argument, tied to that exact list by the
bidirectional `Compilable.index_exact` (so a foreign map is not pairable, and a duplicate-keyed list has no index), with
`Compilable.index_domain`/`Compilable.index_key_inj` DERIVED.  `index_member_at`/`forest_index_member_at` are the TOTAL member queries —
ONE `KeyMap.find`; the deleted `forest_member_at` `List.find` scan of `Compilable.forest_items` is gone, and no keyed
list scan remains in the work-member lookup path.  Each item is an `Compilable.Work` carrying its own `ExprRef` + a total
`Compilable.Conversion` view (exact operand `WorkMember` + target-before-operand SOURCE order `Compilable.conversion_target_before_op`,
processed-suffix membership being the SEPARATE `Compilable.forest_operand_in_tail`), which the outcome fold, the facts,
the annotation, and the diagnostics ALL consume by RECEIVING the exact object as a parameter (no second work
discovery, no reminted conversion ref).  The PROOF-CARRYING `Compilable.Outcomes forest tnft`
(`build_forest_outcome_table` folding `Compilable.forest_items` into the INTRINSIC CAUSAL OBJECT — the proof-carrying
`Compilable.Accumulator` `Compilable.outcomes_acc` PAIRED WITH the `Compilable.Trace` `Compilable.outcomes_trace` that BUILT it, indexed by `Compilable.outcomes_acc` so
the accumulator and its causal predecessor chain are NOT freely pairable; the per-member RETAINED cause is a
PROJECTION of the trace `total_forest_outcome_cause` → each member's `RetainedMemberCause` (exact suffix split
`Compilable.forest_items = prefix ++ current :: rest` + the AUTHENTICATED prior `Compilable.Accumulator` for `rest` + the
member/suffix-indexed `StepCause` producing the FINAL outcome + the tail-to-final QUERY PRESERVATION) — plus its
EXACT domain `Compilable.outcomes_dom` (`Compilable.accumulator_domain`) = membership in `Compilable.forest_items` (`Compilable.outcomes_domain_iff_forest`, non-expression key
absent `Compilable.outcomes_nonexpr_absent`); the source spec reached per member by the SEPARATE match
`total_forest_outcome_at_matches` (`trace_match`)) CONSUMES the once-built
`Compilable.TypeNameFacts` object, querying the table at each conversion's retained target ref (the TOTAL
`total_forest_outcome_at` / `type_name_fact_at_table`, no fallback), reading its operand's ALREADY-COMPUTED
outcome THROUGH the exact operand `SuffixMember` of the processed tail (`Compilable.step_operand_suffix`, tail-membership
`Compilable.forest_operand_in_tail`; TOTAL `Compilable.accumulator_total acc_rest` by `Compilable.accumulator_covers`, no raw `find`/fallback), and calling
`Typing.convert_constant` ONCE per conversion (no `index_program` reconstruction in
the phase closure); the TOTAL fact projection (`forest_facts`) and the TOTAL diagnostic projection (the retained
`Compilable.Diagnostics` object's stored list via `forest_awork_diags` over the retained `Compilable.AnnotatedWork`
OBJECT `build_annotated_work_forest` — members ARE `Compilable.forest_items` in order (`Compilable.annotated_members`), `Compilable.annotated_diag_fold` ties
them to the one-pass `annotate_program` so diagnostics CONSUME the object (no `proj1_sig` discard, no
re-annotation), plus context soundness/same-file/nearest-first/nodup; keyed by each work's OWN `Compilable.work_expr_ref`, NO
`as_expr` and NO fail-open `None` branch) both read that SAME `Compilable.Outcomes` inside the one phase, which
RETAINS the whole flow as a DEPENDENT CHAIN of objects — `Compilable.phase_ot : Compilable.Outcomes Compilable.phase_work Compilable.phase_type_name_facts`, `Compilable.phase_awork
: Compilable.AnnotatedWork Compilable.phase_work`, `Compilable.phase_fact_table : Compilable.ExpressionFacts Compilable.phase_work Compilable.phase_ot`, `Compilable.phase_diag :
Compilable.Diagnostics Compilable.phase_awork Compilable.phase_ot` — each TYPED by the exact prior object it consumes, NO provenance-equality
field (the causal chain is the dependent types, shown definitionally by `phase_ot_consumes_work` etc.), so a
foreign component is UNREPRESENTABLE by type mismatch (`Compilable.phase_facts = Compilable.fact_table_map (Compilable.expression_facts_table Compilable.phase_fact_table)`;
`facts_and_diags_share_phase`, object identity — no fail-open `find`); the `Compilable.ConversionFailure` outcome carries the exact
conversion / target / operand refs (the operand ref a field of `Compilable.InvalidConversion`, projected without re-mint)
with its cause PROJECTED from the retained `Compilable.Trace` keyed by the WORK member (`total_forest_outcome_cause`
returning each member's exact `RetainedMemberCause` = suffix split + the AUTHENTICATED tail `Compilable.Accumulator` +
the `StepCause` producing the FINAL outcome + the tail-to-final query preservation, so a foreign tail accumulator
cannot satisfy it; projected axiom-free by `Compilable.conversion_failure_cause_yields_step` / `Compilable.child_failure_cause_yields_member` /
`Compilable.conversion_success_cause_yields_step`, each reading the operand outcome THROUGH the exact operand `SuffixMember` via `Compilable.accumulator_total
acc_rest`; `final_operand_outcome` closes the operand into the final table), and the phase's `Compilable.TypeNameFacts`
and `Compilable.ExpressionFactTable` are reached through `Compilable.Facts` by object
identity (`compilable_retains_tnfacts` / `compilable_retains_expr_facts`, projections of the retained core);
direct production-object phase fixtures
query `total_forest_outcome_at` at REAL `WorkMember`s from `Compilable.phase_work` and project the retained cause with FINAL-TO-TAIL
CLOSURE (innermost `Compilable.ConversionFailure` whose retained cause reads the operand's `Compilable.ExpressionSuccess` through the exact operand `SuffixMember`
AND closes it into the final table `deep_fail_innermost_convfail`, CONNECTED to the exact stored `Compilable.InvalidConversion`
diagnostic `deep_fail_innermost_diag`; the outer `Compilable.ChildFailure` operands are failures in the final table
`deep_fail_outer_operands_final_fail`; the valid-chain conversions' operands are `Compilable.ExpressionSuccess` in the final table
`deep_nested_chain_operands_final_ok`; exact forest count, no foreign/wrong-kind key); full pinned-Go accept/reject alias matrix.
The universal acceptance evidence (`retained_convsuccess_closure` / `retained_childfail_closure` +no-local-reason /
`retained_convfail_diag` returning the exact retained annotated member / `outcome_trace_unique_step`) AND the exact
concrete evidence (`deep_nested_convsuccess_at` + `deep_nested_chain_success_evidence`, stating the full per-conversion
success bundle for all four valid conversions — with the returned `ConversionStep` at the EXACT SOURCE `ts`/`x`
identity, no existential `ts0`/`x0` (repair 12); `deep_fail_innermost_diag`, stating the exact target fact query `t =
Compilable.fact_type (type_name_fact_at_table (Compilable.phase_type_name_facts phase) (Compilable.conversion_target_node_ref (Compilable.step_conversion step)))`, the exact retained annotated
member, and the stored singleton) are gated in the readable assumption gate, together with the repair-13 work-index
surfaces (build/exactness/freshness, the total queries, foreign- and wrong-kind-key exclusion, the deep-nested index
fixture `deep_nested_chain_index_evidence`, and the equal-expression/distinct-key fixture `twin_expr_index_distinct`).
**C4 is NOT yet human-accepted — BLOCKING
at `9d5246e`, intrinsic retained elaboration repair 14 active (authority installed; implementation not begun)**
(the withdrawn GREEN disposition and its documentation-only acceptance commit `37c9597` are superseded). The
authority chain is in `.review/NEXT_STEPS.md`; scope in `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` + `ADR-0001`
PROPOSED + `ADR-0002` REJECTED-AS-WRITTEN/OPEN. Live status: `.review/SOURCE_FOREST_STATUS.md`.
Each checkpoint is activated ONLY by explicit Rob authorization. C5 (= `uintptr` + rune constants/literals) and the
separate post-C4 foundation consolidation / ruthless trim remain FORBIDDEN until C4 is accepted.

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- `byte`→uint8 / `rune`→int32 SOURCE ALIASES are LANDED in C4 (source-name resolution; distinct source, equal
  semantic type). `uintptr` + exact rune constants/literals are the next type phase (C5 — needs explicit
  sign-off). Bool, the ten integer types, F32/F64, C64/C128, and exact strings are LANDED as static constant roots.
- The first construct that can panic or not terminate — `Property` grows a real `Panicked`/`Outcome` distinction,
  introduced together with the constructor (`Property` stops being `True`).
- Imports — a complete closed-world resolution model (every import resolves to an owned package in the same
  `Syntax.Program`, or reject the whole program). Needs explicit sign-off.
- Integer/float/complex ARITHMETIC — operators, wrapping, division/bitwise/shifts, no-overflow exactness, IEEE
  operations — come AFTER the type roots (an operational-foundation milestone; NOT started).

## Build-trust tasks

Done: base + Go images digest-pinned; the opam retry loop fails closed; one shared Dune cache builds theory +
plugin; zero project axioms enforced two ways (above). Still open: pin/snapshot the opam repo + verify installed
package versions.
