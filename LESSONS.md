# Lessons learned

Hard-won, expensive mistakes. Read before repeating the pattern.

## SRaw — never bolt a raw/opaque escape hatch onto a "verified" structured AST (2026-06-28)

The "verified printer" AST carried `SRaw : { s | raw_ok s } -> SAtom` — an arbitrary
validated string. Anything the AST couldn't represent was smuggled through as text, so the
round-trip theorem was vacuous for most of the surface: the old string printer plus a
validator, wearing a "verified" label. Five review iterations NARROWED the hatch (one more
structured node each time) instead of deleting it — net growth, parallel foundations, hatch
still live. The wholesale teardown proved the whole overlay removable byte-identically: the
trusted `pp_expr` had been doing the real work all along.

**Rules.** (1) Never add a raw/opaque/string-rescue constructor to a structured AST — the
AST must be *unable* to represent unstructured syntax. (2) Build structured-or-fail-loud:
an unrepresentable construct is REJECTED, never preserved as text. (3) "Verified printer"
is honest only with NO text hatch — otherwise call it a trusted string printer. (4) When
you catch yourself narrowing a hatch across iterations, stop and DELETE it. The
replacement (lexer + recursive-descent parser + hatch-free `GExpr`, machine-checked
round-trip) became the `GoAst`/`GoPrint` spine.

## Removing a concept: sweep code + docs + gate + your own words in ONE pass (2026-06-29)

Removing `ptype`'s free-identifier "deferral" model from the CODE took one commit; purging
the CONCEPT took ~7 more review rounds — stale comments, doc lists, my own "the deferred
hatch was removed" narrative (a "removed X" sentence still teaches X), a case-sensitive
recurrence gate, a cross-line phrase split, an orphaned helper.

**Rules.** (1) Active docs/comments state ONLY the live invariant; never narrate a removed
model — history goes here. (2) A stale-spelling gate must be case-insensitive,
whitespace-normalized, proximity-based for multi-token phrases, self-tested on
must-catch/must-spare fixtures, and its own comments minimal data. (3) Sweep everything in
the FIRST pass: code, every doc, replacement wording, gate prose, orphaned helpers.

## A verified LEXER's "exact" means a PROVEN reverse-image theorem (2026-06-29)

`unescape` totally decoded malformed escapes (fail-open); the option-valued fix then
accepted a SUPERSET of the printer image while docs said "exactly". The forward round-trip
`parse (print x) = x` proves the image is accepted, not that nothing else is. Make
accepted == emitted a proven bijection: forward `unescape_opt (esc_string s) = Some s` AND
reverse-image `unescape_opt body = Some s -> body = esc_string s`. "Exact" asserted in
prose ≠ proven.

## Never guess a target-language semantics — test it before encoding it (2026-07-01)

A gate rule written from *guessed* gc behavior (constant OOB slice index) bounced three
reviews; a five-line `go build` settled it in two minutes (gc allows a constant
OOB-positive slice index; it panics at run time; Go constructs a WHOLE literal before
selecting). Write the smallest concrete program and run the pinned toolchain (`make
go-verify`) before encoding any boundary. Corollary: an evaluator helper's accept-set must
be sealed to the gate's own checks with the inclusion proved.

## The runtime-tier arc: five compact lessons (2026-07-02)

(1) The spec's per-construct order/typing shape comes FIRST — map-literal assignment order
is unspecified (denote a panic only when order-independent); shifts are heterogeneous
(never a one-carrier dispatcher). (2) ONE evaluation authority, rec-parametrized up front
(`reval_val_with`) — a second value world drifts. (3) Dispatch tables and boxing functions
get their OWN seals, same commit: fully qualified + a total per-op case-table theorem.
(4) An arc is complete only against what the GATE ADMITS (node kind × width), not the
witness list; absence claims are pinned, never prose. (5) Witness succession is one
commit: flip every dependent pin + a repo-wide stale-claim sweep.

## The typed-runtime tier (2026-07-02)

(1) Outcome TRICHOTOMY per slice — value/panic/absent each proved before a case is
"decided". (2) Shape splits derived from `ptype`'s own classification. (3) An exported
helper carries its own invariant (the width seal lives inside `typed_operand`). (4) gc is
ground-truthed via `make go-verify` BEFORE modelling. (5) Flipping an absent pin sweeps
its dependents in the same commit. (6) Heterogeneous ops need their own dispatch. (7) Read
constants off the GATE's own values — a differently-bounded re-read is a side-condition
leak.

## relooper.v removed (2026-07-04)

relooper.v was removed when the project pivoted from CFG-to-Go recovery to direct
GoAst-certified emission as the TARGET architecture; recover from git if a future CFG
frontend needs it. It was proof-only with zero live dependents. The trusted plugin's own
CFG structurer (`run_blocks` in plugin/go.ml, gap #10) is a separate thing — still live,
still feeding `main.go` until AST-first certified emission replaces it.

## The GoSem split fused RuntimeInt+Agg (2026-07-03)

Planned four files; the real topology is three — the tier seals and slice/map class proofs
compute through the same `Local` evaluator core, so a finer cut either re-opens the
float-boundary bypass or demands sealed-equation kits. `Local` users must share a file; a
split is a reviewability win, not a weight-loss win.


---

## Archaeology: the fuel-removal steering memo (FULFILLED — historical record only)

The boss's fuel-removal directive, preserved verbatim below (including its repo
note).  Its priorities were executed and its relation sketches are SUPERSEDED by
the landed definitions in `builtins.v` (`blocks_step` as the one transition
authority, consumed by `be_jump`/`bd_jump`).  Nothing in this section steers
current work; the only active steering document is `plans/fuel-free.md`.

```text
[REPO NOTE — added when versioning this memo; body below is the boss's VERBATIM text.
STATUS 2026-07-05: the memo's CURRENT PRIORITY sections are FULFILLED — semantic fuel
(run_blocks_fuel/block_fuel/block_nth) is DELETED (7e5f754), blocks_eval/blocks_diverge
are the authority, the lexer is WF, and the fuel gate is live in make check and the
Docker prover stage.  This memo no longer steers current work: the one current
authority is plans/fuel-free.md.  The memo's blocks_eval/blocks_diverge SKETCH below is
superseded by the landed shape: be_jump/bd_jump consume the single blocks_step transition
relation rather than restating its premises.
The MECHANICAL gate derived from it is plugin/fuel-gate.sh (its class definitions are the spec):
identifier/context-scoped over BUDGET-shaped terms only.  Relational small-step
semantics (step/steps/ustep) are the PRESCRIBED architecture (see "Use small-step
semantics where useful" below), never gate targets; the memo's word lists are to be
implemented per that spec, not as a bare word grep.]

FIDO / GENERATED-GO CORRECTNESS: FUEL REMOVAL STEERING MEMO

This memo is for Claude/Codex or any other coding agent working on fuel removal and certified correctness. Treat this as project law for the current cleanup. Do not reinterpret it into a weaker rule.


CORE POSITION

No fuel.

No gas. No arbitrary step budget. No max-depth parameter. No cycle cap. No bounded runner used as proof scaffolding. No renamed equivalent.

This is not the softer rule "fuel is allowed if disciplined." For this project, fuel has already shown that it grows, normalizes itself, and becomes semantic wallpaper. It must be removed from the certified correctness path, not explained, deodorized, renamed, or pushed one layer down.

A bounded run is not a proof. A statement like "the program ran for N steps and reached state Y" is test evidence unless N is derived from a formal theorem and connected to an unfueled semantics. In this project, do not use that route in the certified path. Use unfueled semantics instead.

We are not trying to prove arbitrary Go programs terminate. We are not trying to solve the halting problem. We are defining a closed, generator-controlled subset of Go for which termination, divergence, and semantic correctness claims can be made honestly.

The central question is:

    What is the largest useful class of generated Go programs for which every accepted program has a formal correctness story?

The central question is not:

    How many examples can we generate that appear to work?


DEMOS AND EXAMPLES

Demos are useful, but they are not proofs.

Demos should be reserved for high-level integration and log-diffed regression tests. They may show that the whole pipeline still hangs together: generation, plugin behavior, emitted Go, logs, formatting, expected output, and integration wiring.

Demos must not define semantics, justify termination, justify divergence, certify a language construct, or substitute for formal guarantees. A demo can illustrate a theorem-backed feature. It cannot make an unsupported feature supported.

A list of working examples is not a correctness argument. It is test evidence. Examples may motivate a proof principle, but they do not replace one.

Any demo-only behavior must remain outside the certified correctness path. If a construct is demonstrated but lacks unfueled semantics, generator admissibility, and checked correctness/termination/divergence arguments, it belongs in the unsupported frontier, not the supported subset.


ACCEPTABLE CERTIFIED ARCHITECTURE

The certified path should be built from:

1. Unfueled formal semantics.
   Use relational big-step semantics for terminating behavior where appropriate. Use small-step semantics where useful. Use coinductive or invariant-based relations for divergence. Do not use a total bounded evaluator as the semantic authority.

2. Generator admissibility.
   Prove that generated programs stay inside the supported subset. Unsupported constructs must be rejected, not approximated.

3. Termination or divergence evidence.
   For loops, recursion, repeated computation, CFG jumps, or other potentially nonterminating constructs, the generator/analyzer must provide checkable evidence: structural recursion, a well-founded measure, a ranking function, a finite-state argument, an invariant plus decreasing measure, or a formal divergence certificate.

4. Semantic preservation.
   Prove that lowering/generation preserves the intended semantics for the supported subset.

5. Explicit unsupported frontier.
   If a construct does not yet have a formal story, it is unsupported. Do not slip it into the certified path behind examples, fuel, or a partial runner.

The LLM may propose code and certificates. Rocq decides. The repo shape and CI gates must make incorrect shortcuts hard to add.


DO NOT DO THESE THINGS

Do not introduce a parameter named fuel, gas, budget, steps, max_steps, limit, depth, countdown, allowance, or anything morally equivalent.

Do not keep a bounded evaluator in the certified path and claim it is non-authoritative if certified theorems still depend on it.

Do not preserve old fuel machinery under a new name.

Do not make "out of fuel" a semantic result.

Do not make nontermination mean "did not halt before N."

Do not make invalid control flow silently become normal return.

Do not rely on demos, examples, or golden logs to justify semantics.

Do not keep legacy/demo/scaffolding code unless it is clearly one of:

    - certified path,
    - proved restriction,
    - explicitly unsupported frontier,
    - high-level integration/log-diffed test outside proof claims.

Do not use a total function type to pretend to model behavior that may diverge. If divergence is possible, the authoritative semantics should be relational, coinductive, partial, or certificate-indexed as appropriate.


CURRENT PRIORITY: SEMANTIC FUEL FIRST

The most dangerous remaining fuel-shaped code is semantic fuel, not syntax proof noise.

The builtins / CFG / block-running machinery is higher priority than parser cleanup if it currently says something like:

    run_blocks_fuel ...
    block_fuel := 1000
    run_blocks := run_blocks_fuel block_fuel

This is not merely a proof convenience. It changes the semantics. Emitted Go may loop forever, while the Rocq model eventually returns or panics after an arbitrary cap. That cannot remain in the certified correctness path.

Remove or quarantine semantic fuel first.


CFG / GOTO / BLOCK SEMANTICS GUIDANCE

A total function like:

    run_blocks : nat -> list (IO Next) -> IO unit

is suspicious if the block graph can diverge. The type IO unit is total in the sense that it returns an Outcome. Fuel was likely used to patch this type mismatch.

Do not try to be clever and implement an unfueled total run_blocks for possibly divergent CFGs. That is the wrong shape.

Use unfueled relations for the authoritative semantics. For example, the certified model should be closer to:

    Inductive blocks_eval (blocks : list (IO Next))
      : nat -> World -> Outcome unit -> Prop :=
    | be_done :
        nth_error blocks pc = Some b ->
        run_io b w = ORet Done w' ->
        blocks_eval blocks pc w (ORet tt w')
    | be_panic :
        nth_error blocks pc = Some b ->
        run_io b w = OPanic v w' ->
        blocks_eval blocks pc w (OPanic v w')
    | be_jump :
        nth_error blocks pc = Some b ->
        run_io b w = ORet (Jump pc') w' ->
        pc' < List.length blocks ->
        blocks_eval blocks pc' w' out ->
        blocks_eval blocks pc w out.

And for real nontermination, use a coinductive or equivalent formal divergence relation, for example:

    CoInductive blocks_diverge (blocks : list (IO Next))
      : nat -> World -> Prop :=
    | bd_jump :
        nth_error blocks pc = Some b ->
        run_io b w = ORet (Jump pc') w' ->
        pc' < List.length blocks ->
        blocks_diverge blocks pc' w' ->
        blocks_diverge blocks pc w.

The exact definitions may differ, but the principle is not optional: termination and divergence must be unfueled.

Also check label/block lookup behavior. A function like block_nth that returns normal Done for an out-of-range label is a quiet escape hatch. Invalid control flow should be impossible by admissibility proof, rejected, or represented as an explicit invalid state/error. It should not silently become successful return.

Recommended split:

    - Demo/emission CFG constructs may exist only as integration machinery outside proof claims.
    - Certified CFG constructs require formal semantics and a checked termination/divergence/correctness story.

Do not preserve an uncertified run_blocks : IO unit as the authoritative semantics for possibly divergent control flow.


GOPRINT / LEXER / PARSER GUIDANCE

The syntax/printing file may contain fuel-shaped parser or lexer machinery. This is less semantically dangerous than CFG fuel, but it still must be removed rather than normalized.

For lexing, well-founded recursion over the input string length is acceptable. Structural recursion over syntax or token lists is acceptable. A decreasing measure is acceptable. An execution budget is not.

A good shape is:

    Fixpoint lex_acc (s : string) (a : Acc lt (String.length s)) ...
    Definition lex (s : string) := lex_acc s (lt_wf (String.length s)).

A bad shape is:

    lex_aux fuel s
    lex with enough fuel
    parse with F > expression_size

Delete the old bridge once downstream lemmas are ported. Do not keep it as an alternate authority.

For parsing/printing proofs, avoid preserving a heroic executable parser solely because it already exists. The guarantee we likely need is not "we have a general parser that succeeds with enough budget." The guarantee is that printed generated syntax is faithful, canonical, unambiguous, and structurally recoverable.

Prefer structural/canonical-token proofs such as:

    lex (gprint 0 e) = Some (gtokens 0 e)

plus injectivity or relational grammar facts such as:

    gtokens_inj : gtokens 0 e1 = gtokens 0 e2 -> e1 = e2

or:

    Inductive parses_expr : nat -> list Token -> GExpr -> list Token -> Prop := ...

    Theorem gtokens_parses :
      forall e rest, parses_expr 0 (gtokens 0 e ++ rest) e rest.

The exact theorem shape can change. The important rule is that printer correctness and injectivity should rest on structural syntax/token reasoning, not parser fuel.

Do not rename parser fuel into "allowance," "need," "capacity," or "parse bound." If the proof vocabulary still says "this succeeds because the budget is large enough," it is still the wrong architecture for this project.

Printer proofs may use structural recursion over syntax and input text. They may not use an execution budget.


REPOSITORY HYGIENE AND CI GATES

LLM review is not enough. Fuel already slipped through despite aggressive review. The repo needs mechanical law.

During active migration:

    - Add a no-growth gate for fuel-shaped terms.
    - The count of fuel/gas/budget/step/depth/max-iteration terms in certified files must never increase.
    - Any remaining occurrence must be attached to an explicit removal task.

After migration:

    - Add a zero-tolerance gate for fuel-shaped terms in certified files.
    - Ban fuel, gas, budget, steps, max_steps, max_depth, depth_limit, cycle_limit, run_for, bounded evaluator, and obvious equivalents.
    - Keep any historical discussion outside the certified tree, or remove it entirely to avoid teaching future agents the wrong pattern.

Also enforce import direction:

    - Certified modules must not import demos.
    - Certified modules must not import bounded runners.
    - Certified modules must not import legacy scaffolding.
    - Demo/integration modules may depend on certified artifacts, not the other way around.

Every touched file should be classifiable as one of:

    - certified path,
    - proved restriction/admissibility,
    - unsupported frontier,
    - high-level integration/log-diffed test,
    - temporary migration file scheduled for deletion.

If a file does not fit one of those buckets, challenge its existence.


EXPECTED MIGRATION ORDER

1. Remove or quarantine semantic fuel first.
   CFG/block execution fuel is more dangerous than parser proof fuel because it changes the meaning of programs.

2. Fix invalid-control-flow defaults.
   Out-of-range labels or missing blocks must not silently become successful return.

3. Replace total potentially-divergent runners with unfueled relations.
   Use terminating and diverging relations. Add certificates for admitted programs.

4. Finish lexer migration to well-founded or structural recursion.
   Delete old fuel-based lexer definitions and sufficient-fuel lemmas once replaced.

5. Replace parser round-trip fuel proofs with structural/canonical-token proofs where possible.
   Preserve the real guarantee: emitted syntax is faithful and recoverable.

6. Reclassify demos as integration/log-diffed tests only.
   Update comments/docs so future agents do not cite them as proof evidence.

7. Add hard gates.
   No fuel growth during migration. Zero fuel-shaped terms in certified files after migration.


NORTH STAR

Do not make the old fuel architecture palatable. Remove the need for it.

For syntax, use structural/well-founded recursion or relational canonical-token proofs.

For CFG behavior, use unfueled terminating and diverging relations, plus checked certificates for admitted programs.

For demos, keep them as high-level integration/log-diffed tests only.

A bounded run is not a proof.

A renamed bound is still fuel.

A total function that pretends to represent divergent behavior is a type-level lie.

Strong guarantees cannot be made from a list of examples.

The goal is not apparent expressiveness. The goal is maximum expressiveness under machine-checked guarantees.
```
