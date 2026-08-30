Review: implementation

# C4 sealed data-bearing Result — the retained causal-root repair

`Compilable/Analysis.v` now seals a data-bearing `AN.Result p` that physically RETAINS one `ResultData p`
(opaque `Module ResultSeal : RESULT_AUTHORITY`; `analyze` packs `result_data p`; public `data_of_result r`
is the direct field read of the SUPPLIED `r`, never `result_data`). The sole public mint-computation law is
`analyze_observe_data : data_of_result (analyze p) = result_data p`. `result_unique` and the arbitrary
`data_of_result_canonical` are deleted; every `res_*` projection and every Result-indexed fact/ref/diagnostic/
boundary/issue observes the exact supplied `r`.

`Compilable.v` now uses a one-parameter, branch-neutral `Compilation p` that retains exactly one `AN.Result p`
(`CompilationR { retained_result }`); `Program`/`Rejection`/`Outside` each retain exactly that Compilation plus
branch evidence (`pr_source_disp : disposition p = Compiled` is the sole permitted classification equality).
`compile` binds `r := AN.analyze p` once, builds one `mkComp r`, decides the disposition, and puts that same
Compilation in every branch. Every report/result reader is a structural projection of its supplied object
(`Program/Rejection/Outside -> stored Compilation -> stored Result -> stored ResultData`); no reader reacquires
analysis from `p`. The deleted `compilation_data`, `compilation_canonical`, `elaborate`, the two-parameter
topology, `admissible_forces_compiled`, and the `*_result_canonical` route are gone.

Sealed operations are NOT required to reduce under raw `vm_compute`. Concrete computation crosses the Analysis
seal ONLY through `compile_observe_data : data_of_result (outcome_result (compile p)) = result_data p`
(a compiled-program observation first uses `compiled_program_preserves_data`), then computes the transparent
right-hand side; a Result-indexed view additionally uses only the existing generic relational lemmas
(`missing_main_packages`, `collision_ref_none`, `fact_rows_rows`, `result_issues_class_split`, the `d*_iff`
family). `disposition_observe_data` bridges concrete dispositions.

Immediate migrations: `e2e/WitnessProvenance.v` (sole mint law + direct projections, uniqueness/canonicity
witnesses removed), `e2e/WitnessRejectPrelude.v` (observation-level helpers replace the Result-equality
`retained_via_*`), `e2e/WitnessRejectA..D.v` (dispositions and readers to the sanctioned route; every fixture
and expected observation preserved), and the forced disposition-proof migration in the Emit witnesses.

Preservation: dispositions, diagnostics/boundaries/issue order/ordinals/causes/requirements/report views, every
`Emit.Image`, `Emit.transport`, plugin materialization, generated path set, golden bytes, stdout/stderr/exit,
`go.mod`, and `e2e/golden.*` are unchanged. Every new load-bearing theorem is assumption-free.

Evidence obligations: the reproducible-command evidence apparatus (§9), the candidate-bound cold/warm
performance pairs and evidence-only successor (§11), and the frozen candidate + content-addressed evidence
archive accompany the candidate.

Terminal states for the authoring work order: `CANDIDATE_READY_FOR_REVIEW` or `BLOCKED_FOR_ROB`.
