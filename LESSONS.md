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
parenthesization. The teardown cut `goprint.v` 7144 → 1527 lines and `printer.ml` 4053 → 1475 at that
moment, with the golden output **unchanged at every step** (the from-scratch `Module Front` rebuild has
since regrown `goprint.v` past 3.6k — those are the teardown-instant figures, not the current size).
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

**The replacement (in progress).** `Module Front` in `goprint.v` is a from-scratch Wirth-style
frontend — `lex : string -> tokens`, recursive-descent `parse : tokens -> GExpr`, a clean `GExpr`
AST with **no raw constructor**, and a machine-checked `parse (lex (gprint e)) = e` round-trip. It
is being built to eventually replace the trusted OCaml `pp_expr` — this time with no hatch to
delete later, because the AST cannot represent one.
