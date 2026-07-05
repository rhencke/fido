# Fuel-free semantics — remaining sites

★STEERING MEMO (binding; versioned at `plans/fuel-removal-steering.txt` — read it first):
SEMANTIC fuel outranks parser cleanup — builtins' `run_blocks_fuel`/`block_fuel := 1000`
CHANGES SEMANTICS (emitted Go may diverge while the model caps out), and `block_nth`
maps a missing label to `ret Done` (silent success on invalid control flow).  Both are
LIVE today and are the item-1 target below.  The REPLACEMENT must be: a relational
`blocks_eval` (Inductive) + a coinductive `blocks_diverge` as the authoritative
semantics, per-admitted-program termination certificates, NO unfueled total runner for
divergent CFGs, and label lookup that can never default to success.  The executable
expression parser is not sacred: prefer relational/canonical-token proofs
(`parses_expr`, `gtokens_inj`); the merged-worker WF design below is the fallback.
REQUIRED GATE — IMPLEMENTED AND WIRED: `plugin/fuel-gate.sh` (called by `make check`
via the `fuel-gate` target; its fixture SELFTEST runs on every check).  Semantics:
identifier-and-context scoped over the root .v files with comments stripped —
class A unconditional budget identifiers (fuel, gas, run_blocks_fuel, block_fuel,
countdown, allowance, step_limit, steps_left, max_steps, max_depth, depth_limit,
cycle_limit, iteration_cap, max_iter, max_iterations, run_for, parse_bound);
class B nat-typed budget BINDERS in parens (budget/limit/need/capacity/bound and
step/steps USED AS an execution-cap parameter); class C top-level nat cap
constants named *fuel*/*limit*/*budget*/*cap*.  Small-step RELATION declarations
(`Inductive step/steps/ustep`) match no class — proven by the selftest's PASS
fixture; the FAIL matrix detects block_fuel := 1000, Fixpoint run_blocks_fuel,
run_blocks := run_blocks_fuel block_fuel, max_steps/countdown/allowance
parameters, parser need/limit/capacity/bound/parse_bound counters, steps_left,
max_iter/max_iterations, Fixpoint run (steps : nat), and loop_cap.  Ratchet: a PER-FILE occurrence MANIFEST (`plugin/fuel-gate.baseline`) — counted
per occurrence, not per line, so a new identifier cannot hide on a matching line
or behind a deletion in another file; bless is DOWN-ONLY (refuses on growth).
Manifest at landing: GoPrint.v 22 (parser fuel), builtins.v 12 (run_blocks_fuel/
block_fuel), main.v 3 (CFG demos), GoSem.v 1 — every entry dies with the purge;
zero-tolerance = an empty manifest.  Still to add with the builtins landing: the
Dockerfile prover-stage call (the script is the ONE authority; Makefile calls it
today).  Certified modules
must never import demos or bounded runners.

GOAL (boss audit, P0): no fuel, gas, step budget, or bound under any name, anywhere.
LANDED (8cbe20d + follow-up): cmd.v (structural run_cmd + unwind_defers derivations +
eval_cmd, equivalence both directions, gated; real no_heap totality), cmd_unified.v
(derivation bridge, mode_or motive), GoSemSafe.v (no exists-fuel), GoSem.v/GoSemDenote.v
(unbounded fixtures).  LOCALS 5c stays parked behind this arc.

## Remaining

1. **builtins.v — FIRST (semantic fuel)**: `run_blocks_fuel`/`block_fuel`
   (the goto-CFG runner — genuine partiality): replace with a step relation +
   termination-certificate execution (Acc-based); each CFG demo supplies its concrete
   derivation; the plugin erases the proof argument (arity update, fail-closed;
   plugin/go.ml knows the current names).
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
