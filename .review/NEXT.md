# ASSUM-GATE — the readable assumption surface

Baseline: 6a6402eb1d41f3e93c4dc70ce92dc57e72622589
Review: contract

Goal:
Settle what `gate/Assumptions.v` is for, then make its printed claim equal what it verifies.

What is true now, read from the tree at the baseline:
- `gate/Assumptions.v` declares 540 `Print Assumptions` surfaces over 535 distinct theorems;
- exactly five are declared twice, all in `Compilable`: `capability_is_compile_outcome`, `capability_source`,
  `forest_count_source`, `member_at_in_forest`, `occurrence_expr_diags_conv_sound`;
- `Complex.v` proves six real/imaginary theorem pairs; four imaginary twins are ungated while the matching
  real twin is gated: `typed_runtime_imaginary_coherent`, `_not_neg_zero`, `_not_nan`, `_not_inf`;
- the Dockerfile prover stage asserts declared == closed. A duplicate inflates both sides equally and an
  ungated theorem was never declared, so neither defect is visible to it;
- it prints `540/540 surfaces closed`, which reads as 540 theorems and is 535.

The blocking question, which contract review must answer first:
The whole-theory `Fido Audit Assumptions` already covers every constant, inductive and named assumption,
including all four ungated twins. `DECISIONS.md` records it as strictly stronger, at 1.7 s against ≈77 s, and
carries `ASSUMPTION-GATE-PLACEMENT` as OPEN with three options. Repairing the declared set is only the right
work under one of them. Under the others the file shrinks to a stated rule or stops being a build gate, and
the nine row edits are wasted or wrong.

So this task cannot start until Rob picks an option. It is not a repair waiting for approval; it is a
question about what the file is for, and the row-level defects above are the evidence that nothing currently
answers it.

Change, once the option is chosen:
- make the declared set follow one stated rule, or remove the readable gate;
- make the printed claim name what was actually verified;
- leave `Fido Audit Assumptions`, the module-coverage check and the adversarial self-tests exactly as they
  are — they are the axiom-freedom authority and are not in scope.

Preserve:
- zero project axioms, and the whole-theory audit as the authority for that claim;
- every semantic, proof, provenance, generated-byte, runtime and toolchain guarantee;
- the certified modules in `dune (modules ...)`; `gate/Assumptions.v` is a gate, not a certified module.

Done:
- the gate's declared set is derivable from a stated rule, or the gate is gone;
- no printed count overstates the number of distinct theorems behind it;
- `ASSUMPTION-GATE-PLACEMENT` moves from OPEN to a recorded decision;
- `make prove` and `make check` green; `make audit-fresh` observes it rather than reporting a cache hit.

Stop:
- the chosen option would weaken or duplicate the whole-theory audit;
- a stated rule cannot be written without new machinery, which needs Rob's approval first;
- removing the readable gate would drop a guarantee the audit does not already make.
