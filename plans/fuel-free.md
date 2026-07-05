# Fuel-free semantics — remaining sites

★THIS file is the ONE active steering document for the fuel purge.  The boss's
original memo is archived verbatim in `LESSONS.md` (archaeology); its SEMANTIC-FUEL
priority (CFG runner, invalid-label default, gates, lexer) is fulfilled — the
remaining items it mandated (expression-parser fuel, extraction/trusted-code
cleanup, word sweep) are ACTIVE, tracked below.
STATUS: semantic fuel is DELETED (7e5f754) — `blocks_eval` (Inductive) +
`blocks_diverge` (CoInductive) are the authoritative CFG semantics; the fueled
runner, its cap, and the silent missing-block default are gone; `run_blocks` is an
emission-only marker.  CFG LAYER LANDED: `blocks_step` (the structural
one-step transition), `blocks_jump_wf` (admissibility in OUTCOME terms only —
every block's run on every world is Done, a panic, or an in-range Jump;
membership decided by outcomes, never by markers) and `blocks_jump_wf_progress`
(class-wide never-stuck: conclude or an explicit step; no per-demo machinery).
`be_jump`/`bd_jump` CONSUME `blocks_step` directly — the transition shape
exists exactly once, with no separate composition lemma.  The emitter's rejections of non-literal starts
and out-of-range entry/jump targets in the run_blocks arm are the TRUSTED
syntactic mirror of the literal/range part only.  The shallow relations claim
nothing about emitted deep-IO behavior (that is the deep run_cmd story); a
future core class excluding specific block shapes needs a real
constructor/type boundary.  Demos/golden stay sanity checks, never evidence.
GATE AUTHORITY: `plugin/fuel-gate.sh` is the mechanical authority for the fuel gate
(its class definitions are the spec; the selftest is a regression matrix derived from
the same variables); this file only summarizes it.  The executable expression
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
   prover stage; manifest ratcheted to GoPrint.v 22 / main.v 3 (builtins.v and
   GoSem.v are at zero).  The holistic CFG layer is IN: `blocks_jump_wf` +
   `blocks_jump_wf_progress` (class-wide, outcome-only; no per-demo machinery).
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
   ★DECISION (2026-07-05, per the memo's preference + "holistic proofs or nothing"):
   go RELATIONAL, not WF-executable.  Blast radius CONFIRMED self-contained to
   GoPrint.v (no other file consumes parse/parse_str).  Build:
   (1) `Inductive parses : nat -> list Token -> GExpr -> list Token -> Prop` (the
       precedence-climbing grammar as derivation rules; the k index is the CLIMB
       PRECEDENCE, not a budget);
   (2) `gtokens_parses : forall e ctx rest, parses 0 (gtokens ctx e ++ rest) e rest`
       (rework of the existing roundtrip induction — derivations instead of fuel);
   (3) DETERMINISM: `parses_det : parses k t e r -> parses k t e' r' -> e = e' /\ r = r'`;
   (4) `gtokens_inj` + `gprint_inj` from (2)+(3); the disjointness lemmas via
       inversion (a TReturn-led list admits no derivation);
   (5) DELETE the executable parse/parse_expr mutual block (parse_gty stays — already
       fuel-free); esize/length_gtokens_ge_esize/lspine_fuel3/pops_fuel/all_Pexpr and
       the *_S unfold lemmas die with it; rt_* Examples become derivation examples or
       drop (demos are sanity checks, not evidence).
   Manifest target after: GoPrint.v 0; then main.v's 3, then done.
   FALLBACK ONLY — the superseded merged-worker WF design:
   (settled 2026-07-05, no phase rank needed):
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
4. **Word sweep** — the MECHANICAL target is the fuel-gate manifest reaching EMPTY
   over its scanned scope: the certified root .v files AND plugin/*.ml (the gate
   scans both; archaeology is never scanned).  Non-code surfaces (Makefile,
   Dockerfile, shell scripts, docs) are OUT of the gate by design — it is
   code-level, never a prose linter, and its own name contains the word — their
   cleanup is a manual closeout item with an obvious definition of done: no budget
   identifier names anything in them except the gate's own artifacts.
