# Fuel-free semantics — remaining sites

★STEERING MEMO: `plans/fuel-removal-steering.txt` is the ORIGINAL directive (verbatim,
with a fulfilled-status note); THIS file is the one current authority.
STATUS: semantic fuel is DELETED (7e5f754) — `blocks_eval` (Inductive) +
`blocks_diverge` (CoInductive) are the authoritative CFG semantics; the fueled
runner, its cap, and the silent missing-block default are gone; `run_blocks` is an
emission-only marker.  NOT YET DONE: per-demo pairing — every live `run_blocks`
demo must either carry a `blocks_eval`/`blocks_diverge` fact built from ITS OWN
block list (shallow-IO demos) or be explicitly classified outside shallow CFG
semantics (deep-IO, e.g. the defer demos, whose blocks fail-loud under run_io);
a classification gate for that pairing lands with it.
GATE AUTHORITY: `plugin/fuel-gate.sh` is the mechanical authority for the fuel gate
(header = the classes, selftest = the executable spec); this file only summarizes it.  The executable expression
parser is not sacred: prefer relational/canonical-token proofs (`parses_expr`,
`gtokens_inj`); the merged-worker WF design below is the fallback.

GOAL (boss audit, P0): no fuel, gas, step budget, or bound under any name, anywhere.
LANDED (8cbe20d + follow-up): cmd.v (structural run_cmd + unwind_defers derivations +
eval_cmd, equivalence both directions, gated; real no_heap totality), cmd_unified.v
(derivation bridge, mode_or motive), GoSemSafe.v (no exists-fuel), GoSem.v/GoSemDenote.v
(unbounded fixtures).  LOCALS 5c stays parked behind this arc.

## Remaining

1. **builtins.v — LANDED (7e5f754)**: `blocks_eval`/`blocks_diverge` authoritative;
   `run_blocks_fuel`/`block_fuel`/`block_nth`/the exhaustion lemma DELETED (the
   missing-block default died by deletion); `run_blocks` = emission-only marker
   (`run_blocks_never_ret`); fuel gate wired in BOTH Makefile and the Dockerfile
   prover stage; manifest ratcheted to GoPrint.v 22 / builtins.v 2 / main.v 3 /
   GoSem.v 1.  REMAINING here: the per-demo pairing + classification gate (see
   STATUS above).
2. **GoPrint.v** — LEXER DONE: `lex` is Acc-structural on input length and the ENTIRE
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
3. **plugin/printer.ml / plugin/go.ml**: regenerate / update after 1-2 so no fuel
   remnant survives in extracted or trusted code.
4. **Word sweep**: repo-wide `fuel` grep must come back empty (comments included).
