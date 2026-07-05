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
   REMAINING: the parser — inventory (2026-07-05):
   - `parse_gty fuel` (~1386) + `parse_gty_S` + `tsize`/`tsize_le_len` budget; the
     round-trip's `tsize c <= F` premises (`parse_gty_roundtrip`, `parse_convty_roundtrip`)
     and the `S (length toks)` instantiations (`parse_gty_print_ty`, `parse_conv_print`).
   - the 10-way mutual `parse_expr/parse_primary/parse_atom/parse_postfix/parse_args(_tl)/
     parse_elems(_tl)/parse_map_elems(_tl)/parse_climb` on fuel (~1728-1905) +
     `parse toks := parse_expr (3 * List.length toks + 4) 0 toks` + the `*_S` unfold
     lemmas (~3291-3342) + the `esize`/`length_gtokens_ge_esize`/`lspine_fuel3`/`all_Pexpr`
     budget layer + `parse_expr_TReturn_None`'s `S (S (S f))` arithmetic.
   Replace with structural / well-founded recursion — WF measure lexicographic
   (List.length toks, phase-rank) with every token-consuming call strictly shorter and
   the same-length calls strictly phase-descending (expr → climb/primary → atom →
   postfix/args) — then the same proof-irrelevance/unfold-equation recipe as the lexer:
   `parse_*_pi` by strong induction on the measure, `parse_eq_*` one-step equations at an
   `Acc_intro (fun y _ => wf y)` certificate, restate the round-trip layer budget-free
   (the `esize` machinery DELETES — it existed only to size the budget).  If a form resists a fuel-free
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
