# Lessons learned

Hard-won, expensive mistakes. Read before repeating the pattern.

## SRaw — never bolt a raw/opaque escape hatch onto a "verified" structured AST (2026-06-28)

**What happened.** The Go expression printer was lifted into Rocq as a structured AST
(`SAtom` / `GoAtom` / `GoExpr`) with print/parse round-trip theorems — a "verified printer."
But the AST carried one escape-hatch constructor, `SRaw : { s | raw_ok s = true } -> SAtom`:
an arbitrary *validated string*. Any construct the structured AST could not represent was
smuggled through `SRaw` as text — *validated* by `raw_ok`, not *constructed*.

**Why it was wrong.** A printer AST with a raw-string hatch is not a verified printer — it is
the old string printer plus a validator. The round-trip theorem `parse(print s) = s` is real
but **vacuous for the hatch**: it proves the printer reproduces text it never structured. `SRaw`
let plausible-but-wrong Go (anything `raw_ok` happened to accept) flow through the "verified"
path. The verification value was illusory for everything the hatch carried — which, because the
AST was incomplete, was most of the surface.

**The failure mode that cost five iterations.** Every review demanded `SRaw` die. Each iteration
*narrowed* it instead — added one more structured constructor (`SApply` for calls, `SHexLit` for
hex ints, `EUnary` for prefix ops, `SConvert` / `SForceCall`) so `raw_ok` could reject one more
shape. This felt like progress but:

- It **added** code (new AST nodes + printers + parser arms + round-trip proofs) while the hatch
  stayed live — net file size *grew*.
- It built **parallel foundations** (a second token parser, a statement AST) next to the live bad
  structure — duplication, not simplification.
- The hatch never actually died: there was always one more shape (func-lit bodies, hex floats)
  that "legitimately" needed it, dressed up as a "documented bounded hatch."

Narrowing an escape hatch is not deleting it. "Documented bounded hatch" is a euphemism for
"still there."

**The teardown.** When finally deleted wholesale, the entire verified-expression-printer (the AST,
`SRaw`, `raw_ok`, the ~370-reference `scan_*` machinery, `build_atom` / `build_apply`, the
round-trip proofs, and every feature built to narrow the hatch) came out as **pure removable
overlay** — proven byte-identical. The plugin's original *trusted OCaml string printer* (`pp_expr`)
had been doing the real work the whole time; the verified AST only intercepted binop-operand
parenthesization. The teardown cut the verified-printer file 7144 → 1527 lines and `printer.ml`
4053 → 1475 at that moment, with the golden output **unchanged at every step** (teardown-instant figures).
The experiment added complexity and a false "verified" claim, and contributed zero verification value.

**The rule.**

1. **Never add a raw / opaque / string-rescue constructor to a structured AST.** The AST must be
   *unable to represent* unstructured syntax. If it can hold a raw string, it is not verified.
2. **Build structured-or-fail-loud.** If a construct cannot be represented structurally yet,
   REJECT it mechanically (rule 2 `unsupported` / abort) — never preserve it as text.
3. **A "verified printer" claim is honest only** if the AST is total over the supported surface
   with NO text hatch. Until then, call it what it is: a *trusted string printer*.
4. **When you catch yourself NARROWING a hatch across iterations, stop and DELETE it.** One
   structural deletion beats ten foundation slices. Adding a parallel foundation while the bad
   one stays live is net negative.

**The replacement.** A from-scratch Wirth-style frontend — `lex : string -> tokens`, recursive-descent
`parse : tokens -> GExpr`, a clean `GExpr` AST with **no raw constructor**, and a machine-checked
`parse (lex (gprint e)) = e` round-trip — was built and then split into the AST-first spine `GoAst`
(syntax) + `GoPrint` (printer / parser / proofs). It has no hatch to delete later, because the AST
cannot represent one.

## Removing a concept: sweep code + docs + gate + your own words, in ONE pass (2026-06-29)

**What happened.** The `GoSafe.ptype` gate's free-identifier "deferral" model (the `PtUnk`
category) was removed from the CODE in one commit — free identifiers became `ptype (EId _) = None`,
only the predeclared `nil` (`PtNil`) admitted. But purging the *concept* then took **~7 more
stop-review rounds**, each a real residual the previous fix missed:
active comments still said "scope deferred to GoSem" / "bool/deferred"; `ARCHITECTURE.md`/`PROGRESS.md`
still listed `PtUnk` / "DEFERRED operand"; my own purge-fix wrote "the deferred-identifier escape
hatch **was removed**" (a "removed X" narrative still teaches X); the recurrence-gate I added was
case-sensitive ("Deferred identifier" bypassed it), then missed a cross-LINE split ("DEFERRED\noperand"),
then missed "deferred **left** operand" (word between the tokens); the gate's OWN comments narrated the
dead model; and the regression edit orphaned a now-dead helper (`gs_x`).

**Why it cost so much.** Each round fixed the one instance the reviewer pointed at, instead of
exhaustively sweeping the whole surface at once. Every fix was correct; the *process* was the waste.

**The rules.**

1. **Active docs/comments state ONLY the live invariant.** Never narrate a removed model — even
   "X was removed" actively *teaches* X and is a "duplicate authority" that can justify re-opening
   the hole. A false or stale semantic claim in active guidance BLOCKS review even when the code is
   sound. History goes to `LESSONS.md` (this file), not active `.v`/`ARCHITECTURE`/`PROGRESS`.
2. **A recurrence (stale-spelling) gate must be robust on every axis at once:** case-INSENSITIVE;
   whitespace/newline-NORMALIZED (a line-local grep misses a phrase wrapped across lines); SENTENCE-
   PROXIMITY for multi-token concepts (`deferred[^.]{1,40}operand` — not adjacent-only, which misses
   "deferred LEFT operand"; not unbounded `.*`, which false-positives on normalized text); SELF-TESTED
   in-script on must-catch and must-spare fixtures; and its OWN comments are minimal denylist DATA, not
   a narration of the dead concept.
3. **When you remove a concept, sweep it ALL in the first pass:** the code, EVERY doc, your own
   replacement wording, the gate's own prose, case-folding, line-wrapping, and any helper/scaffolding
   the edit orphaned. A piecemeal purge cascades.

## A verified LEXER's "exact" means a PROVEN reverse-image theorem, not a documented superset (2026-06-29)

**What happened.** Adding the `EStr` string-literal node, the lexer's `unescape` was a TOTAL function
that decoded malformed escapes (`"\q"`, `"\xZZ"`, raw newline) into a valid `EStr` instead of rejecting
them (fail-OPEN — rule 2 violation). Fixed to option-valued `unescape_opt` (fail-closed). But then it
accepted a *superset* of the printer image (uppercase `\xAF`, raw control bytes, `\x41`=`'A'` which the
printer emits raw) while the docs claimed it accepted "exactly what `esc_string` emits."

**The rule.** For a round-trip lexer, the forward round-trip `parse (print x) = x` is necessary but NOT
sufficient for an "exact"/accepted==emitted claim — it only says the printer's image is *accepted*, not
that *nothing else* is. Make accepted == emitted a **proven bijection**: keep the forward
`unescape_opt (esc_string s) = Some s` AND prove the **reverse-image** theorem
`unescape_opt body = Some s -> body = esc_string s`. Tighten the decoder until that theorem holds
(here: restrict raw bytes and `\xHH` to exactly `esc_byte`'s output), and have the gate DEFER its
exactness claim to the live theorem, not to phrase-grep. "Exact" asserted in prose ≠ "exact" proven.
