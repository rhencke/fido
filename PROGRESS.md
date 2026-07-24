# Fido — status

A concise inventory of what is DONE and the immediate frontier. Architecture lives in `ARCHITECTURE.md`;
contributor law in `CLAUDE.md`; live campaign status in `.review/SOURCE_FOREST_STATUS.md`; commit-level history
in the git log.

## GREEN — proved axiom-free (every gated `Print Assumptions` surface + the whole-theory audit)

One authority per layer, over the ONE `GoProgram`; every layer axiom-free in the pinned container.

- **`FilePath`** — intrinsic canonical relative paths (lowercase components + `.go` basename); decidable eq;
  `fp_parent` package key; strange paths UNREPRESENTABLE. Public component authority: `dir_components`
  (+ `dir_components_concat`), over the internal `split_slash` helper.
- **`Collections`** — the ONE standard-collection foundation: thin wrappers over pinned-stdlib `FMapAVL`
  (`FileMapBase` over the `FilePath` key, `PackageMapBase` over `String`) and `FMapPositive` (`NodeMapBase`);
  Fido authors no map/set. `fp_str_inj`, `filemap_elements_Equal` axiom-free.
- **`Ints`** — the ten-member `IntegerType` family + the ONE representability/range/keyword authority
  (`int`/`uint` pinned 64-bit, distinct from `int64`/`uint64`).
- **`Floats`** — the ONE float-format authority (axiom-free over `SpecFloat`): F32/F64; exact canonical-rational
  `FloatConst`; single-round `round_float_sf` (F32 directly at binary32); proof-carrying `FloatValue`; the
  bounded finite-decimal `DecimalFloat`; the double-round scar.
- **`Complexes`** — the ONE complex authority over `Floats`: C64/C128 via the `complex_component_type` mapping;
  exact `ComplexConst`; intrinsic `TypedComplexConst`; general runtime `ComplexValue` (pairs of `FloatValue`,
  may be -0/inf/NaN); `DecimalComplex`; `round_typed_complex` (each component once).
- **`ModulePath`** — intrinsic narrow canonical module path; decidable eq; public component authority
  `mp_segments` (+ `mp_string_concat`); invalid paths UNREPRESENTABLE. **`GoVersion`** — singleton `Go1_23`, renders "1.23".
- **`GoAST`** — `ModuleSpec` + `GoProgram := { prog_module ; prog_files : GoFileMap }` (may be empty); the map
  KEY is the path; a construction/view `GoFileNode` = `FilePath` + source-owned `PkgMain` clause + empty imports
  + `source_decls`; the sound/complete/exact duplicate-rejecting `filemap_of_nodes`; `DMain`, `SPrintln`,
  `EBool`/`EInt`/`ENeg`/`EString` (exact bytes)/`EFloat`/`EComplex` + ONE source-shaped `EConvert TypeSyntax`
  conversion over the closed sixteen source names (the fourteen numeric + `byte`→uint8 / `rune`→int32 aliases).
- **`GoIndex`** — the ONE structural occurrence-identity + navigation authority derived from one immutable
  `GoProgram` (imports only `GoAST`/`Collections`/`FilePath`): canonical file-local `positive` ids; sealed
  `NodeTable`; the universal `index_file_source_exact`; sealed snapshot-indexed refs; the `visit_file`
  single-pass indexed traversal.
- **`GoTypes`** — the ONE type authority, EVIDENCE over the raw AST (no typed AST): `GoType` = {`TBool`,
  `TInteger`, `TFloat`, `TComplex`, `TString`}; exact untyped `GoConst`; intrinsic dependently-typed
  `TypedConst`; the ONE `convert_const` authority; `ConstInfo`/`resolve_const_info`/`ConstRepresentable`;
  `ProgramTyped` map-based (respects `FilesEqual`).
- **`GoCompile`** — EXACT whole-program admissibility for the pinned one-shot `go build ./...`:
  `GoCompile p := fresh_build_preflight_ok p /\ SourceProgramValid p`; `SourceProgramValid := ProgramTyped /\
  PackageRulesValid` (the FACTORED `PackageDeclsUnique` + `MainPackagesHaveEntry`). The readable index-free
  SPECIFICATION decision (`source_spec_valid_b`/`source_spec_package_rules_b`, for fixtures) reflects the
  factored roots directly; the PRODUCTION decision is the retained-bucket diagnostic pass, whose redeclaration /
  missing-entry / all-package diagnostics are empty IFF `PackageDeclsUnique` / `MainPackagesHaveEntry` /
  `PackageRulesValid`. The ONE `elaborate` builds one `IndexedProgram` + `ProgramElaboration`; `go_compile`
  projects it (sound/complete, class-invariant under file order). Default executable name is component-based:
  cmd/go's rule (`default_exec_name_c`) applied DIRECTLY to `package_import_components`
  (`ModulePath.mp_segments` ++ `FilePath.dir_components`, no string reparse); the import-path string is their
  `/`-join, injective in the package directory (`package_import_path_inj`). Structured `DiagnosticReason` in the exact snapshot;
  the three diagnostic layers each have an emptiness characterization; a failed preflight takes precedence.
- **`GoSafe`** — real `GoValue`; `value_type`; `ValueWF`; PARTIAL `eval_expr` (projects the stored canonical
  runtime value, rounded once at conversion); resolved-eval well-formedness + type preservation; `SafeProgram`.
- **`GoRender`** — direct renderer + source-owned package clause + go.mod; strings/floats/complexes each via ONE
  canonical spelling with an INDEPENDENT decoder + round trip; header exact first line; all-ASCII.
- **`GoEmit`** — provenance-gated `DirectoryImage` (go.mod + `.go` map, carrying a proof both came from rendering
  one `SafeProgram`); rendered map has the same key domain + exact bytes as the source; `render_program`.

## GREEN — executed (integration evidence, never proof)

- **Transport + validate-before-publish.** `Fido Materialize` (the SOLE Rocq transport vernac) guards provenance
  in one four-step decode (typecheck the image, reject a non-empty assumption closure, decode only the final
  `(go.mod, entries)` transport, hand to the writer) and writes the authoritative pristine into a fresh
  disposable root. There is NO public `Fido Emit`; the publication sink (`Fido_sink.sync`) is a PRIVATE plugin
  module, reached only from `sink_test` + the tiny internal `make regenerate` apply adapter (fixed source
  `/generated`, no arbitrary root, no Go, no hashing). Validate-before-publish is the Docker DAG: building the
  `sync` image COPYs go-e2e's `/fresh-build-ok`, so a failed pinned `go build ./...` makes `sync` unbuildable;
  it publishes the ORIGINAL generated-module bytes. No checksum system exists (a checksum cannot prove a build
  succeeded); cooperating-developer threat model (the pre-commit hook's level), no deliberate-bypass resistance.
- **The sink** (`plugin/fido_sink.ml`) — the foreign-Go-rejecting sibling-temp dirty-directory synchronizer:
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
- **Zero project axioms**, enforced two ways in `make prove`: the count-checked `gate/axiom_gate.v` (Print
  Assumptions on public surfaces) AND the Rocq-native `Fido Audit Assumptions` whole-certified-theory closure
  audit (constants + inductives + named assumptions), with a module-coverage gate and adversarial self-tests A-E.

## Source Forest campaign (ACTIVE)

Multi-checkpoint C0..C6; C0..C2 complete + human-approved; C3 (fresh-image literal-build closeout) ACCEPTED by
Rob; C4 (source type names, compiler resolution, unified `EConvert`, `byte`/`rune` source aliases) — ELEVEN
successive candidates have been BLOCKING at human Implementation Review (the current repair-11 baseline is the
repair-10 freeze `3ecf32e`, and repair 11 is a theorem-statement/gate-comment/authority-prose closeout, not an
architecture change). The production expression path is ONE `ExpressionPhase`
built from ONE retained `CompilationInput` and driven by ONE proof-carrying retained work forest OBJECT — the
`ExprWorkForest` record (`build_expr_work_forest`; its stored `ewf_blocks`/`ewf_items` with `ewf_items = concat
ewf_blocks`, forward/reverse domain (`ewf_forward`/`ewf_reverse`) + key-NoDup (`ewf_keys_nodup`) + order +
operand-in-suffix (`ewf_operand_in_tail`) all carried as FIELDS; `build_forest_blocks` PRIVATE inside, its proof
returned INTO the record — no `proj1_sig` discard), each item an `ExprWork` carrying its own `ExprRef` + a total
`ConversionWork` view (exact operand `WorkMember` + target-before-operand SOURCE order `cw_target_before_op`,
processed-suffix membership being the SEPARATE `ewf_operand_in_tail`), which the outcome fold, the facts,
the annotation, and the diagnostics ALL consume by RECEIVING the exact object as a parameter (no second work
discovery, no reminted conversion ref).  The PROOF-CARRYING `ForestOutcomeTable forest tnft`
(`build_forest_outcome_table` folding `ewf_items` into the INTRINSIC CAUSAL OBJECT — the proof-carrying
`OutcomeAccumulator` `fot_acc` PAIRED WITH the `OutcomeTrace` `fot_trace` that BUILT it, indexed by `fot_acc` so
the accumulator and its causal predecessor chain are NOT freely pairable; the per-member RETAINED cause is a
PROJECTION of the trace `total_forest_outcome_cause` → each member's `RetainedMemberCause` (exact suffix split
`ewf_items = prefix ++ current :: rest` + the AUTHENTICATED prior `OutcomeAccumulator` for `rest` + the
member/suffix-indexed `StepCause` producing the FINAL outcome + the tail-to-final QUERY PRESERVATION) — plus its
EXACT domain `fot_dom` (`oa_domain`) = membership in `ewf_items` (`fot_domain_iff_forest`, non-expression key
absent `fot_nonexpr_absent`); the source spec reached per member by the SEPARATE match
`total_forest_outcome_at_matches` (`trace_match`)) CONSUMES the once-built
`TypeNameFactTable` object, querying the table at each conversion's retained target ref (the TOTAL
`total_forest_outcome_at` / `type_name_fact_at_table`, no fallback), reading its operand's ALREADY-COMPUTED
outcome THROUGH the exact operand `SuffixMember` of the processed tail (`cs_operand_suffix`, tail-membership
`ewf_operand_in_tail`; TOTAL `oa_total acc_rest` by `oa_covers`, no raw `find`/fallback), and calling
`convert_const` ONCE per conversion (no `index_program` reconstruction in
the phase closure); the TOTAL fact projection (`forest_facts`) and the TOTAL diagnostic projection (the retained
`ExpressionDiagnostics` object's stored list via `forest_awork_diags` over the retained `AnnotatedExprWorkForest`
OBJECT `build_annotated_work_forest` — members ARE `ewf_items` in order (`aewf_members`), `aewf_diag_fold` ties
them to the one-pass `annotate_program` so diagnostics CONSUME the object (no `proj1_sig` discard, no
re-annotation), plus context soundness/same-file/nearest-first/nodup; keyed by each work's OWN `ew_expr_ref`, NO
`as_expr` and NO fail-open `None` branch) both read that SAME `ForestOutcomeTable` inside the one phase, which
RETAINS the whole flow as a DEPENDENT CHAIN of objects — `ep_ot : ForestOutcomeTable ep_work ep_tnft`, `ep_awork
: AnnotatedExprWorkForest ep_work`, `ep_eft : ForestExprFactTable ep_work ep_ot`, `ep_diag :
ExpressionDiagnostics ep_awork ep_ot` — each TYPED by the exact prior object it consumes, NO provenance-equality
field (the causal chain is the dependent types, shown definitionally by `phase_ot_consumes_work` etc.), so a
foreign component is UNREPRESENTABLE by type mismatch (`ep_facts = eft_map (feft_table ep_eft)`;
`facts_and_diags_share_phase`, object identity — no fail-open `find`); the `EOConvFail` outcome carries the exact
conversion / target / operand refs (the operand ref a field of `DRInvalidConversion`, projected without re-mint)
with its cause PROJECTED from the retained `OutcomeTrace` keyed by the WORK member (`total_forest_outcome_cause`
returning each member's exact `RetainedMemberCause` = suffix split + the AUTHENTICATED tail `OutcomeAccumulator` +
the `StepCause` producing the FINAL outcome + the tail-to-final query preservation, so a foreign tail accumulator
cannot satisfy it; projected axiom-free by `StepCause_convfail_inv` / `StepCause_childfail_inv` /
`StepCause_ok_conv_inv`, each reading the operand outcome THROUGH the exact operand `SuffixMember` via `oa_total
acc_rest`; `final_operand_outcome` closes the operand into the final table), and the phase's `TypeNameFactTable`
and `ExprFactTable` are sealed into `ElaborationFacts` by object
identity (`elaborate_ok_seals_tnfacts` / `elaborate_ok_seals_facts`); direct production-object phase fixtures
query `total_forest_outcome_at` at REAL `WorkMember`s from `ep_work` and project the retained cause with FINAL-TO-TAIL
CLOSURE (innermost `EOConvFail` whose retained cause reads the operand's `EOOk` through the exact operand `SuffixMember`
AND closes it into the final table `deep_fail_innermost_convfail`, CONNECTED to the exact stored `DRInvalidConversion`
diagnostic `deep_fail_innermost_diag`; the outer `EOChildFail` operands are failures in the final table
`deep_fail_outer_operands_final_fail`; the valid-chain conversions' operands are `EOOk` in the final table
`deep_nested_chain_operands_final_ok`; exact forest count, no foreign/wrong-kind key); full pinned-Go accept/reject alias matrix.
The universal acceptance evidence (`retained_convsuccess_closure` / `retained_childfail_closure` +no-local-reason /
`retained_convfail_diag` returning the exact retained annotated member / `outcome_trace_unique_step`) AND the exact
concrete evidence (`deep_nested_convsuccess_at` + `deep_nested_chain_success_evidence`, stating the full per-conversion
success bundle for all four valid conversions; `deep_fail_innermost_diag`, stating the exact target fact query `t =
tnf_type (type_name_fact_at_table (ep_tnft phase) (cw_target_ref (cs_conversion step)))`, the exact retained annotated
member, and the stored singleton) are gated in the readable assumption gate (repair 11 — a theorem-statement,
gate-comment, and authority-prose closeout only; the production architecture is unchanged and pending Rob's human C4
Implementation Review).  Frozen for Rob's human Implementation
Review (the current authority chain is in `.review/NEXT_STEPS.md`; scope in
`.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` + `ADR-0001` PROPOSED + `ADR-0002` REJECTED-AS-WRITTEN/OPEN). Live
status: `.review/SOURCE_FOREST_STATUS.md`.
Each checkpoint is activated ONLY by explicit Rob authorization; C5 and later remain FORBIDDEN.

## NEXT — the frontier (pour roots before floors; do NOT add breadth for its own sake)

- `byte`→uint8 / `rune`→int32 SOURCE ALIASES are LANDED in C4 (source-name resolution; distinct source, equal
  semantic type). `uintptr` + exact rune constants/literals are the next type phase (C5 — needs explicit
  sign-off). Bool, the ten integer types, F32/F64, C64/C128, and exact strings are LANDED as static constant roots.
- The first construct that can panic or not terminate — `GoSafe` grows a real `Panicked`/`Outcome` distinction,
  introduced together with the constructor (`GoSafe` stops being `True`).
- Imports — a complete closed-world resolution model (every import resolves to an owned package in the same
  `GoProgram`, or reject the whole program). Needs explicit sign-off.
- Integer/float/complex ARITHMETIC — operators, wrapping, division/bitwise/shifts, no-overflow exactness, IEEE
  operations — come AFTER the type roots (an operational-foundation milestone; NOT started).

## Build-trust tasks

Done: base + Go images digest-pinned; the opam retry loop fails closed; one shared Dune cache builds theory +
plugin; zero project axioms enforced two ways (above). Still open: pin/snapshot the opam repo + verify installed
package versions.
