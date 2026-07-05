# Fuel-free semantics — remaining sites

GOAL (boss audit, P0): no fuel, gas, step budget, or bound under any name, anywhere.
LANDED (8cbe20d + follow-up): cmd.v (structural run_cmd + unwind_defers derivations +
eval_cmd, equivalence both directions, gated; real no_heap totality), cmd_unified.v
(derivation bridge, mode_or motive), GoSemSafe.v (no exists-fuel), GoSem.v/GoSemDenote.v
(unbounded fixtures).  LOCALS 5c stays parked behind this arc.

## Remaining

1. **GoPrint.v** — LEXER DONE: `lex` is Acc-structural on input length and the ENTIRE
   lemma suite is stated over `lex` itself (`lex_acc_pi` proof-irrelevance + the
   `lex_eq_*` one-step unfold equations; no budget premise, no auxiliary evaluator).
   REMAINING: the parser — `parse_gty fuel`, the mutual expression-parser fuel,
   `parse toks := parse_expr (3 * length toks + 4) ...`, the esize budget machinery —
   replace with structural / well-founded recursion (WF on (tokens, phase)), same
   proof-irrelevance/unfold-equation recipe.  If a form resists a fuel-free
   restatement, SHRINK the accepted subset rather than keep a budget (boss
   2026-07-05: expressiveness may be sacrificed; fuel is not ironclad).  The
   round-trip theorems keep their statements; the budget premises disappear.
   printer.ml regenerates; golden byte-identical.
2. **builtins.v** (`n_dec_aux` LANDED — the shared digits.v authority): `run_blocks_fuel`/`block_fuel`
   (the goto-CFG runner — genuine partiality): replace with a step relation +
   termination-certificate execution (Acc-based); each CFG demo supplies its concrete
   derivation; the plugin erases the proof argument (arity update, fail-closed;
   plugin/go.ml knows the current names).
3. **plugin/printer.ml / plugin/go.ml**: regenerate / update after 1-2 so no fuel
   remnant survives in extracted or trusted code.
4. **Word sweep**: repo-wide `fuel` grep must come back empty (comments included).
