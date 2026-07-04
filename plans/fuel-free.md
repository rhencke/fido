# Fuel-free semantics — migration plan

GOAL (boss directive): no fuel, gas, step budget, or bound under any name, anywhere —
definitions, theorems, examples, helpers. Semantics states meaning directly; termination is
structural or well-founded; genuine partiality is modeled honestly. No `exists fuel` bridge
theorems. LOCALS 5c is parked behind this arc (its fixtures would be written against the
runner this arc replaces).

## Inventory (complete, 2026-07-04)

1. **cmd.v** — `run_defers fuel` + `run_cmd fuel` + `run_cmd_terminates : … exists fuel oc,
   run_cmd fuel c w = Some oc` (a GATED surface, and the forbidden §7 shape) +
   `run_defers_terminates` + the `cmd_sz`/`defers_sz` measure scaffolding.
2. **cmd_unified.v** — the bridge quantifies over completing `run_cmd fuel` runs;
   `run_defers_out` et al. are fuel-inducted.
3. **GoSemSafe.v** — `run_cmd 1` exact-output lemmas; panic-free soundness ends in
   `exists fuel w', run_cmd fuel c w = Some (ORet tt w')` (§7 shape).
4. **GoSem.v** — every runtime fixture and `GoSemRequiredCategoryCoverage` field is
   `run_cmd 5 c w = Some …`.
5. **GoPrint.v** — `z_digits fuel` / `digit_fuel` (adaptive, proven-sufficient — still fuel);
   feeds the LIVE extracted printer (plugin/printer.ml). builtins.v `n_dec_aux` is the same
   pattern.
6. **builtins.v** — `run_blocks_fuel` (the goto-CFG runner): genuinely partial — a CFG can
   loop forever, so NO total function exists; this is the one honest-partiality site.

## The core insight (stage 1)

`go` (body evaluation, defer COLLECTION) is already structural and fuel-free. Fuel exists
only because the flat defer-stack representation loses structure. Go's defers are
FUNCTION-scoped — a deferred call's own defers run at ITS return — so the interpreter can be
defer-compositional: `run_cmd (CDfr d c') w` = run `c'` (with its defers), then run `d` as
its own scope from the resulting world, then combine (a returning defer keeps the active
outcome and advances the world; a panicking defer replaces the active panic). Same LIFO
order, same panic threading, FULLY STRUCTURAL (nested recursion through `CRead`'s
continuation is guard-accepted; `Cmd` is a well-founded tree, so a self-referential command
is unrepresentable). Divergence is impossible in `Cmd` — the total structural evaluator IS
the semantics; no second (relational) universe is forked.

## Stages (each keeps `make check` green)

1. **cmd.v**: define the structural `run_cmd {A} (c : Cmd A) (w : World) : option (Outcome A)`
   (option = heap-absence ONLY, never exhaustion). DELETE `run_defers`, the fuel parameter,
   `run_defers_terminates`, `cmd_sz`/`defers_sz`. RESTATE the gated surface as
   `run_cmd_total_no_heap : no_heap c = true -> exists oc, run_cmd c w = Some oc`
   (totality, no bound). Keep `go` only while still load-bearing for downstream proofs.
2. **cmd_unified.v**: bridge restated — "completing" = `run_cmd c w = Some oc`, no fuel
   quantifier; fuel-inducted lemmas become structural on `Cmd`.
3. **GoSemSafe.v**: `run_cmd 1 …` → `run_cmd …`; the gate soundness ends in
   `exists w', run_cmd c w = Some (ORet tt w')`.
4. **GoSem.v**: all `run_cmd 5 c w` fixtures and record fields → `run_cmd c w` (statement
   change only; `vm_compute` proofs unchanged).
5. **Digit printers**: `z_digits`/`n_dec_aux` → well-founded recursion on the numeric value
   (`Acc` erases in extraction → plain OCaml recursion; printer.ml regenerated; golden must
   stay byte-identical). The fuel-premise lemmas restate as unconditional equations.
6. **run_blocks (honest partiality)**: replace `run_blocks_fuel` with execution by recursion
   on a TERMINATION CERTIFICATE — a small-step relation on (block-index, world) configs plus
   `Acc`-based evaluation (`run_blocks start blocks (H : Terminates …) : IO unit`). Each CFG
   demo supplies its concrete termination derivation (deterministic step relation — built by
   tactic walk, no bound). The plugin erases the proof argument (arity update, fail-closed).
   A diverging CFG then has NO certificate and cannot be run — partiality made honest.
7. **Docs + sweep**: PROGRESS gates list (`run_cmd_terminates` → the new name),
   SPEC_CONFORMANCE, MIGRATION.md row citations, repo-wide `fuel` word sweep (comments
   included; main.v:2867's user-level decreasing-counter demo comment reworded), memory.

Deletion, not preservation: no old runner kept, no equivalence theorem to the fuel version,
no bounded helper survives as a "test convenience".

## Risks

- Stage 1 rewrites the proof base of cmd_unified/GoSemSafe (fuel induction → structural).
- Stage 5 touches the verified printer + its extraction (byte-identical golden required).
- Stage 6 changes a plugin-recognized op's arity (negtest the fail-closed path).
