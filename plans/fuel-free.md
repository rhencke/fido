# Fuel-free semantics — remaining sites

★STEERING MEMO IS LAW (boss, 2026-07-05; full text:
`/home/rhencke/.claude/uploads/195aa470-10b2-4d8e-a054-896e00718775/59081153-claude_fuel_removal_steering.txt`
— re-read it before working this arc):
1. SEMANTIC FUEL FIRST — builtins' `run_blocks_fuel`/`block_fuel := 1000` outranks all
   remaining parser cleanup (it CHANGES SEMANTICS: emitted Go may diverge while the model
   caps out).  Authority = relational `blocks_eval` (Inductive) + coinductive
   `blocks_diverge`; do NOT build an unfueled total runner for divergent CFGs; per-demo
   termination certificates; out-of-range label lookup must NEVER default to Done.
2. The executable expression parser is NOT sacred — prefer relational/canonical-token
   proofs (`parses_expr : Inductive`, `gtokens_inj`) over rescuing it with WF recursion;
   the guarantee is printed syntax faithful+recoverable, not "a parser succeeds".
   (The merged-worker WF design below stays as the fallback if the executable parser
   earns its keep.)
3. Gates: during migration a NO-GROWTH gate on fuel-shaped terms in certified .v files;
   zero-tolerance after.  Certified modules never import demos/bounded runners.

GOAL (boss audit, P0): no fuel, gas, step budget, or bound under any name, anywhere.
LANDED (8cbe20d + follow-up): cmd.v (structural run_cmd + unwind_defers derivations +
eval_cmd, equivalence both directions, gated; real no_heap totality), cmd_unified.v
(derivation bridge, mode_or motive), GoSemSafe.v (no exists-fuel), GoSem.v/GoSemDenote.v
(unbounded fixtures).  LOCALS 5c stays parked behind this arc.

## Remaining

1. **GoPrint.v** — LEXER DONE: `lex` is Acc-structural on input length and the ENTIRE
   lemma suite is stated over `lex` itself (`lex_acc_pi` proof-irrelevance + the
   `lex_eq_*` one-step unfold equations; no budget premise, no auxiliary evaluator).
   TYPE PARSER DONE (59aeabb): `parse_gty` is Acc-structural on token length (the result
   carries its suffix bound for the map arm's second call); `parse_gty_roundtrip` is
   premise-free; `parse_convty` fuel-free.  REMAINING:
   - the 10-way mutual `parse_expr/parse_primary/parse_atom/parse_postfix/parse_args(_tl)/
     parse_elems(_tl)/parse_map_elems(_tl)/parse_climb` on fuel (~1728-1905) +
     `parse toks := parse_expr (3 * List.length toks + 4) 0 toks` + the `*_S` unfold
     lemmas (~3291-3342) + the `esize`/`length_gtokens_ge_esize`/`lspine_fuel3`/`all_Pexpr`
     budget layer + `parse_expr_TReturn_None`'s `S (S (S f))` arithmetic.
   DESIGN (settled 2026-07-05, supersedes the lexicographic sketch — no phase rank
   is needed at all):
   (a) A single `{struct a}` Acc fixpoint REQUIRES every recursive call on a strictly
       smaller certificate, so the same-length dispatch chain expr -> primary -> atom
       cannot stay three mutual functions.  MERGE it: one worker `parse_e (mode : PMode)`
       (MAtom | MPrimary | MExpr; k for the climb) whose body inlines atom, then
       (mode >= MPrimary) the postfix fold, then (mode = MExpr) the climb.  The mode is
       consumed at entry — every recursive call (into MExpr/MAtom) is on STRICTLY fewer
       tokens, so the whole mutual block (worker + postfix + climb + args/elems/map
       lists + tails) is Acc-structural on token length ALONE.
   (b) Sequential calls need the previous call's suffix bound, so the workers return
       STRONG results: `{r | length r < length input}` for the consuming phases
       (atom/primary/expr/args/elems/map_elems), `<=` for the possibly-empty folds
       (postfix/climb/*_tl).  The body's `parse_gty` calls switch to a bound-carrying
       `parse_gty_b := parse_gty_acc _ (lt_wf _)` (the public `parse_gty` becomes its
       projection) — the public face already threw the bound away, and the conversion
       arms need it for their next call.
   Then the lexer recipe verbatim: certificate proof-irrelevance by strong induction on
   length, one-step unfold equations at the `Acc_intro (fun y _ => lt_wf y)` certificate
   (the sig proofs evaporate there), public `parse_atom/parse_primary/parse_expr/parse`
   as projections, the round-trip layer restated budget-free, and the WHOLE budget layer
   (`esize`, `length_gtokens_ge_esize`, `lspine_fuel3`, `pops_fuel`, `all_Pexpr`'s fuel
   threading, `tsize` once nothing sizes with it) DELETES.  If a form resists a fuel-free
   restatement, SHRINK the accepted subset rather than keep a budget (boss
   2026-07-05: expressiveness may be sacrificed; fuel is not ironclad).  The
   round-trip theorems keep their statements; the budget premises disappear.
   printer.ml regenerates; golden byte-identical.
2. **builtins.v — NOW FIRST (steering memo §CURRENT PRIORITY)**: `run_blocks_fuel`/`block_fuel`
   (the goto-CFG runner — genuine partiality): replace with a step relation +
   termination-certificate execution (Acc-based); each CFG demo supplies its concrete
   derivation; the plugin erases the proof argument (arity update, fail-closed;
   plugin/go.ml knows the current names).
3. **plugin/printer.ml / plugin/go.ml**: regenerate / update after 1-2 so no fuel
   remnant survives in extracted or trusted code.
4. **Word sweep**: repo-wide `fuel` grep must come back empty (comments included).
