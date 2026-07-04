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
