# The canonical relational grammar — the syntax AUTHORITY (CLAUDE.md "Syntax authority")

GOAL: the intended syntax authority is a RELATIONAL canonical grammar with parser-free
token injectivity — printer correctness proved against the GRAMMAR, the executable
parser demoted to derived tooling.  Target shapes (CLAUDE.md "Syntax authority"):
`CanonExpr : nat -> GExpr -> list Token -> Prop` (+ CanonStmt/CanonProgram),
`gprint_expr_canonical`, `canon_expr_unique`, `lex_gprint_expr` (likewise per layer).

WHAT EXISTS (in GoPrint.v): the token type + the fuel-free Acc lexer; `gtokens ctx e` (the
executable canonical token assignment); the RELATIONAL grammar `CanonTy`/`CanonExpr` +
`canon_ty_tokens`/`canon_expr_tokens` (token-functionality) + `gprint_expr_canonical` (printer
canonicity) + `lex_gprint_expr` (lexical faithfulness, `lex (gprint ctx e) = Some (gtokens ctx e)`
composed with the canonical derivation); `canon_ty_unique` — type-level token uniqueness, PARSER-FREE
via `gttokens_ty_inj`; and the Phase-3b toolkit toward expression uniqueness (`bd`/`gtokens_balanced`,
the `last0`/`bdip`/`fsep` split lemmas, `no_depth0_sep`, `gtokens_args_inj`, `gtokens_pairs_inj`, the
paren/bare operand discrimination `bare_not_paren_group`/`gtparen_inj`, the operator-token
injectivities `op_token_inj`/`prefix_token_inj`, the type-skipper `skip_gty`).  STILL OPEN: the complete-list
`gtokens_inj` (⇒ `canon_expr_unique`).  Until it lands, `gprint_inj` still routes
through `gtokens_parse` + `parse_print_roundtrip` (the executable-parser round-trip) and the
statement layer (`print_stmt_inj`/`print_program_inj`) is still STRING injectivity — so EXPRESSION
injectivity remains parser-derived (Phase 3c reproves `gprint_inj` off `gtokens_inj`; the parser is
retired to derived tooling LAST, Phase 5).

## The architecture (the parser-free uniqueness discipline)

⛔ `canon_expr_unique` must be proved DIRECTLY on the token functions (the complete-list
`gtokens_inj`, structural induction on `e1` with a `last0` bracket split — full design in
"Phase 3b/3c" below) — NEVER via `gtokens_parse`: deriving uniqueness from the parser's would reinstate
the parser as the foundation, the exact inversion CLAUDE.md forbids.  The executable
parser is re-based LAST as derived tooling (`parse_sound`/`parse_complete` against the
relation).

★STATUS: Phases 1+2 LANDED — CanonTy (CTy* ctors, avoiding the ConvTy CT* namespace) +
the 5-way mutual CanonExpr/CanonArgs/CanonArgsTl/CanonPairs/CanonPairsTl with SPLIT paren
productions; the Minimality/Combined schemes; canon_ty_tokens + canon_expr_tokens (token-
functionality) + gttokens_ty_canonical + gprint_expr_canonical + lex_gprint_expr, all in
the printer gate.  Phase 3a LANDED (9759804) — canon_ty_unique (type-level token uniqueness)
PARSER-FREE: canon_ty_tokens functionality + gttokens_ty_inj (leading-token discrimination,
the nominal_type_ident keyword-exclusion killing GTNamed collisions, UIP-on-bool for TyName
sig equality, and the sqd/firstdip/balanced_rb_split bracket-balance toolkit splitting TMap's
children).  Phase 3b SLICE 1 LANDED — the three-bracket balance toolkit (bd/bd_app/bd_up/
bd_app_pass/bd_op_token/bd_prefix_token/bd_gtparen/gttokens_ty_bd + arg/pair balance lemmas)
and gtokens_balanced (every canonical expression token list is uniformly bracket-balanced),
gated.  Phase 3b SLICE 2 (the complete-list gtokens_inj; canon_expr_unique = canon_expr_tokens +
gtokens_inj; design pinned below) is split into sub-slices 2a–2k building toward the crux:
Phase 3b SLICE 2a LANDED — the `last0`
group-split tool (`last0`/`last0_group` + `nd`/`nd_add`/`bd_nd`/`bd_prefix_defined`/`last0_aux_inv`),
gated; found: the closer hypothesis is unnecessary — the final token is at depth-before 1, so it
never records a best.  Phase 3b SLICE 2b LANDED — `bdip`/`bdip_app_nodip`/`balanced_close_split`
(cancel a balanced prefix before a matched closer; the inner-list / paren-peel tool), gated.
Phase 3b SLICE 2c LANDED — `fsep`/`fsep_app_none`/`fsep_balanced_sep`/`sep_split` (the depth-0
separator split for comma/colon lists; `TComma`/`TColon` are depth-neutral so `bdip` can't find
them), gated.  Phase 3b SLICE 2d LANDED — `no_depth0_sep` (`fsep (gtokens ctx e) d = None` at ANY
start depth: a single expression exposes no depth-0 separator; helpers `bd_gtokens_d`/`bd_ty_d`/
`bd_gtparen_d`/`bd_args_d`/`bd_pairs_d`, `fsep_prefix_token`/`fsep_op_token`/`fsep_ty_none`/
`fsep_gtparen`/`fsep_args`/`fsep_pairs`), gated; the args/pairs `fsep` sublemmas are stated at start
depth `S d` (their top-level separators sit at depth ≥ 1, where `fsep` — recording only at depth 0 —
skips them).  Phase 3b SLICE 2e LANDED — `gtokens_args_inj` (argument-list injectivity: equal
`gtokens_args` lists are equal arg lists, given element injectivity carried as a `Forall`; peels the
first element off the first top-level `TComma` via `sep_split`+`no_depth0_sep` and recurses,
discriminating lengths via `no_depth0_sep`/`fsep`; helpers `app_cons_nonnil`/`gtokens_nonnil`/
`gtokens_args_nonnil`/`gtokens_args_single`/`gtokens_args_cons2`), gated.  Phase 3b SLICE 2f LANDED —
`gtokens_pairs_inj` (the map-pair analogue: `k TColon v` pairs comma-joined; peels one pair with TWO
`sep_split`s — first on `TColon` for the key, then on `TComma` for the value — then recurses; helpers
`gtokens_pairs_tl_cons`/`gtokens_pairs_nonnil`/`gtokens_pairs_single`/`gtokens_pairs_cons2`), gated.
Phase 3b SLICE 2g LANDED — the paren/bare operand discrimination: `bare_not_paren_group` (a bare
non-operator expression's tokens NEVER equal a single paren group `TLP :: g ++ TRP :: nil`, by THREE
paths — leading-token mismatch for atoms/`EConv`/lits; `last0` (`= 0` for the group vs an interior
depth-0 token, via `last0_group`) for `EIndex`/`ESlice`/`ECall`/`EAssert`; last-token `TId f`≠`TRP`
via `app_inj_tail` for `ESel`) +
`gtparen_inj` (the operand step: `gtparen` injective given the operand's injectivity IH; bare/bare and
paren/paren via `balanced_close_split`, the mismatch via `bare_not_paren_group`; helpers
`gtparen_nonnil`/`last0_paren_group`), gated.
Phase 3b SLICE 2h LANDED — `op_token_inj`/`prefix_token_inj` (each maps its ops to DISTINCT tokens, so
injective on its own domain), gated; ⚠ but they OVERLAP each other — `op_token BSub = prefix_token
UNeg = TMinus` (likewise `TStar` mul/deref, `TAmp` and/addr, `TCaret` xor/xor) — so a depth-0
`TMinus`/`TStar`/`TAmp`/`TCaret` may be binary OR unary; the EBn split must be found by prefix/infix
POSITION (a binary op follows a COMPLETE operand), never by token identity.
Phase 3b SLICE 2i LANDED — `skip_gty` (a PURE token type-skipper: returns the tokens after ONE type,
does NOT build a `GoTy`, so a token utility not a type-parser; `Acc`-recursive on length, the `map[K]V`
key-then-value skip non-structural) with TWO gated theorems: `skip_gty_types` (EXACTNESS:
`skip_gty (gttokens_ty t ++ rest) = Some rest`, by induction on `t`; the `forall a` subsumes
`Acc`-proof-irrelevance) and `skip_gty_lt` (SOUNDNESS/progress: `Some rest ⇒ length rest < length
toks` — a skip consumes ≥ 1 token, the well-foundedness the scan will recurse on) — the scan's
type-context foundation (handles the pointer-`TStar` hazard by skipping whole types).
LANDED (slice 2j): ★the EBn OPERATOR-PRECEDENCE LOCATOR
`eb_find` — the rightmost-minimal-precedence depth-0 infix op as a suffix split, prefix/infix
disambiguation by operand-complete state, type-leads skipped whole via `skip_gty_acc`'s strict sig.
LANDED (slice 2k-c): ★the OPERAND LAW
`eb_operand` — the depth-0 dual of `eb_depth`: a whole `gtokens ctx e` block at a depth-0 FROM-position
is consumed, leaving the suffix scan combined with the node's own top operator (`eb_top ctx e`); the
`EBn`-unwrapped recursive-combine split is proved via the crux algebra (`eb_infix_combine`,
`eb_combine_left_absorb`) + `eb_top_prec`.  LANDED (slice 2k-d): ★the top-level `eb_find` correctness at
`suffix = nil`, in its GENERAL form `eb_find_gtokens : eb_find (gtokens ctx e) = eb_top ctx e` (`eb_operand`
at the empty suffix collapses the combine — the block's tokens locate their own top operator: `Some (R,o)`
for an unwrapped `EBn o _ r`, `None` for every primary / prefix `EUn` / paren-WRAPPED `EBn`).  This is the
`gtokens_inj` EBn DISCRIMINATOR (equal token lists ⇒ equal `eb_top` ⇒ same operator + same right split).
`eb_find_inner` (the `EBn`-node instance `eb_find inner = Some (gtokens (S prec o) r, o)`) is now a
4-line corollary.  The two operator-bearing same-constructor DIAGONALS of `gtokens_inj` are LANDED, both
FULL: `gtokens_inj_ebn` (the EBn diagonal — `gtokens_ebn_inner`'s unwrapped-inner recursion (equal inner
lists ⇒ equal op+operands, via `eb_find_inner` + the operand IHs + `app_inv_tail`) promoted PAST the
ctx-wrapper: `eb_find_gtokens` turns the token equality into `eb_top ctx e1 = eb_top ctx e2`, so a
wrapped-vs-unwrapped mismatch is a `None=Some` contradiction and same-wrapping strips to equal inner lists)
and `gtokens_eun_inner` (the EUn diagonal — EUn's tokens don't depend on ctx: equal tokens ⇒ equal unop +
operand, via `prefix_token_inj` + `bare_not_paren_group` + the operand IH).  The first cross-discriminator
`nonatom_len` is also LANDED (`unop_needs_paren e = true -> 2 <= length (gtokens ctx e)` — atoms print to
one token, every other form to ≥2; the atom row/column of the destruct-`e2` matrix), as are the first two
POSTFIX diagonals `gtokens_inj_esel` (base + fixed 2-token tail, `app_inj_tail` + `gtparen_inj`) and
`gtokens_inj_eindex` (base + bracket group, `last0_group` pins the base-prefix length + `app_eq_length`).
STILL TO WRITE: the
`gtokens_inj` ASSEMBLY — the LARGE remaining bulk (the diagonals + `nonatom_len` are a small fraction): the primary
diagonals (atoms/postfix/composites) and, HARDEST, the ~14×13 cross-constructor
discrimination.  Since `gtokens` is not prefix-free, most constructor pairs need a real discriminator; the
LENGTH one (atom vs everything) is landed as `nonatom_len`, but the rest (`eb_top` for `EBn`, `last0`/
last-token for the delimited forms) and probably further discrimination sub-lemmas remain — the genuine
remaining crux, not a mechanical wiring pass.  Then
`canon_expr_unique`.
(The arbitrary-SUFFIX
determinism lemma was found FALSE — see the design.)

## Phases (each: green, golden byte-identical, gated, reviewed)

1. **CanonTy + CanonExpr (the relations).**  Mutual inductives mirroring `gtokens`'
   arms as PRODUCTIONS — `CanonTy : GoTy -> list Token -> Prop` (EConv's conversion type REUSES it
   as `CanonTy (convty_ty c)`; there is NO separate `CanonConvTy`),
   `CanonExpr : nat -> GExpr -> list Token -> Prop` with
   `CanonArgs : list GExpr -> list Token -> Prop` and
   `CanonPairs : list (GExpr * GExpr) -> list Token -> Prop` for the three
   list-bearing constructors.  The precedence index is `gtokens`' `ctx` nat.
2. **Token-functionality + printer canonicity.**
   `canon_expr_tokens : CanonExpr ctx e ts -> ts = gtokens ctx e` (induction on the
   derivation); `gprint_expr_canonical : CanonExpr ctx e (gtokens ctx e)` (structural);
   `lex_gprint_expr : lex (gprint ctx e) = Some ts /\ CanonExpr ctx e ts` (compose with
   `gtokens_lex`).
3. **★`canon_expr_unique`** (the meat): `CanonExpr ctx e1 ts -> CanonExpr ctx e2 ts ->
   e1 = e2`, parser-free — via `canon_expr_tokens` + the COMPLETE-list `gtokens_inj`
   (structural induction on `e1`, delimited groups split by `last0` (the last depth-0 position)).  Full design + the ruled-out dead ends (balanced-prefix cancellation; the FALSE
   arbitrary-suffix determinism lemma) in the "Phase 3b/3c" section below.  Slices 1–2k-d (the
   `bd` balance toolkit + `gtokens_balanced`; the `last0`/`bdip`/`fsep` split lemmas;
   `no_depth0_sep`; `gtokens_args_inj`; `gtokens_pairs_inj`; the paren/bare operand discrimination
   `bare_not_paren_group`/`gtparen_inj`; the operator-token injectivities
   `op_token_inj`/`prefix_token_inj`; the type-skipper `skip_gty`; slice 2j the EBn locator `eb_find`;
   slice 2k-c the OPERAND LAW `eb_operand` — the depth-0 dual of `eb_depth`; slice 2k-d
   `eb_find_gtokens` — the EBn discriminator, `eb_find_inner` its corollary) are LANDED +
   gated; `gtokens_inj` itself is the open crux.  The EBn precedence substrate is fully landed
   (`eb_find_gtokens : eb_find (gtokens ctx e) = eb_top ctx e`, the EBn discriminator; `eb_find_inner` its
   corollary), plus the two operator-bearing DIAGONALS of `gtokens_inj`, both FULL: `gtokens_inj_ebn` (the
   EBn diagonal — `gtokens_ebn_inner`'s unwrapped-inner recursion promoted past the ctx-wrapper, mismatch
   discriminated via `eb_find_gtokens`) and `gtokens_eun_inner` (the EUn diagonal), plus the first
   cross-discriminator `nonatom_len` (atom vs everything, by length) — but these are a small
   fraction.  The LARGE remaining bulk is the `gtokens_inj` ASSEMBLY: the primary
   diagonals (atoms/postfix/composites), and, hardest, the ~14×13 cross-constructor discrimination (not
   prefix-free ⇒ most pairs need a real discriminator; the assembly
   will likely surface further discrimination sub-lemmas — the genuine remaining crux, not mere wiring).
4. **CanonStmt/CanonProgram** + the same trio over the statement printer (the
   statement layer's `lex_gprint_stmt` does not exist yet — build the statement
   `gtokens` analogue first).
5. **Re-base the parser as derived tooling**: `parse_sound : parse ts = Some (e, nil)
   -> CanonExpr 0 e ts`, `parse_complete` (its converse via canon_expr_tokens +
   gtokens_parse — legitimate HERE because the parser is the SUBJECT, not the
   foundation); rewrite GoPrint's header authority claims; the PROGRESS gate list
   gains the canonical surface (one manifest-gated `Print Assumptions`).

## Phase 3b/3c — the expression uniqueness proof (design, pinned before coding; the balance/split
## toolkit, the type-skipper, and the whole EBn precedence scan are now LANDED — the SUBSTANTIAL
## `gtokens_inj` assembly (the only remaining primary diagonals are the four ATOM rows —
## every operator/postfix/composite diagonal is done (`EBn`/`EUn` + `ESel`/`EIndex`/`EAssert`/`ESlice`/
## `ECall` + `EConv`/`ESliceLit`/`EMapLit`) — plus the ~14×13 cross-discrimination) + `canon_expr_unique`
## remain, see the slice log above)

TARGET (mirrors the type layer exactly): `canon_expr_unique ctx e1 e2 ts` = `canon_expr_tokens`
on both sides + a PARSER-FREE `gtokens_inj : forall ctx e1 e2, gtokens ctx e1 = gtokens ctx e2
-> e1 = e2`.  (`canon_ty_unique` already has this shape via `gttokens_ty_inj`.)  Everything
below is proved on the token FUNCTIONS, never via `parse`/`gtokens_parse`.

Why the naive prefix argument FAILS: postfix forms share their operand's leading tokens —
`gtokens ctx (ESel (EId i) f) = TId i :: TDot :: TId f :: nil` has `TId i :: nil`
(= `gtokens (EId i)`) as a proper prefix.  So leading-token discrimination alone cannot
separate `EId` from `ESel`/`EIndex`/`ECall`/… ; segmentation must come from BRACKET BALANCE.

TOOLKIT (generalize the type-layer `sqd`/`firstdip`/`balanced_rb_split` from ONE bracket kind
to the THREE expression bracket kinds — parens `TLP`/`TRP`, square `TLB`/`TRB`, brace
`TLC`/`TRC`):
- `bd : list Token -> nat -> option nat` — NET all-kinds depth (openers {TLP,TLB,TLC} +1,
  closers {TRP,TRB,TRC} -1, None on a below-zero dip).  `bd_app` like `sqd_app`.
- `gtokens_balanced : forall ctx e, bd (gtokens ctx e) 0 = Some 0` (structural on `GExpr_ind'`
  + `args`/`pairs` sublemmas) — every canonical expr token list is uniformly balanced.
  ⚠ TARGET is the COMPLETE-list `gtokens_inj` (no suffix).  The arbitrary-SUFFIX generalization
  `gtokens ctx e1 ++ s1 = gtokens ctx e2 ++ s2 -> e1 = e2 /\ s1 = s2` is **FALSE** — take
  `e1 = EId x, s1 = [TDot; TId f]` and `e2 = ESel (EId x) f, s2 = []`: both sides are
  `[TId x; TDot; TId f]` yet `e1 <> e2`.  (`gtokens` is NOT prefix-free, so no continuation-
  passing determinism lemma exists.)  `gtokens_inj` holds only because a COMPLETE token list
  leaves nothing for the operand to over-consume.
- Split machinery.  ⚠ "balanced prefix cancels" is FALSE (`gtokens 0 (EId x) = [TId x]` is a
  balanced proper prefix of `gtokens 0 (EBn Add (EId x) (EId y))`).  The valid split for the
  delimited-group forms is `last0 L` = the index of the LAST TOKEN of `L` whose bracket-depth-
  BEFORE it is 0 — equivalently the GREATEST `i` with `i < length L` (STRICT) and
  `bd (firstn i L) 0 = Some 0`.  ⚠ the strict `i < length L` is LOAD-BEARING: `L` is a COMPLETE
  balanced list, so `bd (firstn (length L) L) = bd L 0 = Some 0` too — WITHOUT the strict bound
  `last0` would be `length L`, not `length P`.  On the shared complete list `L = P ++ OPEN ::
  body ++ CLOSE :: nil` (`P`/`body` balanced): the framing `OPEN` sits at index `length P` with
  depth-before 0; every later token has depth-before ≥1 (from `OPEN`, `body` from depth 1 stays
  ≥1, `CLOSE` at depth-before 1) and `i = length L` is excluded — so `last0 L = length P`.  An
  INTERNAL depth-0 opener inside `P` (operand is itself an `EIndex`) is harmless: it is an EARLIER
  index, and `last0` takes the LAST.  Both decompositions of the same `L` give
  `length P_a = length P_b`, then `app_eq_length` splits.  (`last0` — a forward depth scan
  recording the last depth-0 TOKEN index, so a token index is always < length L — and
  `last0_group : last0 (P ++ OPEN :: body ++ CLOSE :: nil) = length P` are LANDED + GATED (slice 2a),
  via `nd`/`nd_add`/`bd_nd`/`bd_prefix_defined`/`last0_aux_inv`.  NOTE the closer
  hypothesis turned out unnecessary — the final token is at depth-before 1, so it never records a
  best; the split holds for any final token.  The `app_eq_length`-based split COROLLARY is trivial.)
- `bdip` (all-kinds first-dip) + `bdip_app_nodip` + `app_eq_length` give `balanced_close_split`
  (any closer `cl`): `ts1 ++ cl::r1 = ts2 ++ cl::r2`, `ts1`/`ts2` balanced ⇒ `ts1=ts2 /\ r1=r2`.
  ROLE: after `last0` isolates the group `OPEN :: body ++ CLOSE :: nil` and the `OPEN` is stripped,
  `balanced_close_split cl:=CLOSE` peels the `body` token list (balanced) off the final `CLOSE`.
- The comma/colon-joined ELEMENTS inside `body` (ECall args, ESliceLit elems, EMapLit pairs,
  ESlice's `lo:hi`) are NOT split by `balanced_close_split` (`TComma`/`TColon` are depth-neutral,
  not closers).  They need `gtokens_args_inj`/`gtokens_pairs_inj` — list injectivity by induction
  on the element list, splitting at the TOP-LEVEL (depth-0-within-the-group) `TComma`/`TColon`
  via a first-depth-0-separator lemma, resting on `no_depth0_sep` (LANDED): no expression's `gtokens 0 e`
  contains a depth-0 `TComma`/`TColon` (they occur only inside nested groups, at depth ≥1), so the
  first top-level separator delimits the first element.  (`last0`/`last0_group`,
  `bdip`/`balanced_close_split`, `fsep`/`sep_split`, `no_depth0_sep`, `gtokens_args_inj`, and
  `gtokens_pairs_inj` LANDED + gated.)

`gtokens_inj` by structural induction on `e1` (`GExpr_ind'`), `destruct e2`, per pair — on
COMPLETE lists (no suffix):
- Atoms (EId/EInt/EStr/EHex): single-token; the head token separates the four atoms; a longer form
  (even one sharing the head token, e.g. a bare-atom-based `ESel`) is ruled out by `nonatom_len` (length
  ≥ 2 for every non-atom) — LANDED.
- Fixed-tail postfix ESel: strip the 2-token tail `TDot :: TId f` (equal, since the whole lists
  are equal) ⇒ `f_a=f_b` and `gtparen e0_a = gtparen e0_b`; then the operand step.  LANDED as
  `gtokens_inj_esel`.
- Delimited-group forms (EIndex/ESlice/ECall/EConv/EAssert/ESliceLit/EMapLit): end in a CLOSER;
  `last0` pins the operand/type prefix length, `app_eq_length` isolates the group, `OPEN` stripped
  + `balanced_close_split cl:=CLOSE` peels `body`, then the single sub-expr (EIndex) recurses
  directly / the multi-element `body` splits via `gtokens_args_inj`/`gtokens_pairs_inj` (EIndex has
  one index, ESlice one `lo:hi` colon, ECall/lits a comma list, EMapLit colon+comma pairs); recurse
  on each.  EConv/lits lead with a TYPE (`canon_ty_unique`); `[]`/`map` lead tokens discriminate.
  The EIndex/EAssert/ESlice/ECall instances are LANDED (`gtokens_inj_eindex`/`gtokens_inj_eassert`/
  `gtokens_inj_eslice`/`gtokens_inj_ecall`), as are the type-led composites (`gtokens_inj_econv`/
  `gtokens_inj_eslicelit`/`gtokens_inj_emaplit` — `convty_ty_inj` recovers the ConvTy for EConv).
- Operand step `gtparen e0_a = gtparen e0_b -> e0_a = e0_b` (COMPLETE): `destruct op_needs_paren`
  both sides — bare/bare and paren/paren strip to `gtokens 0 e0_a = gtokens 0 e0_b` ⇒ IH; the
  paren/bare MISMATCH is impossible (a complete bare `gtokens 0 e` cannot equal a single
  `TLP…TRP`-wrapped group) — `bare_not_paren_group` via `last0`.  This whole operand step
  (`bare_not_paren_group` + `gtparen_inj`) LANDED in slice 2g.
- EUn: leading `prefix_token o` (injective on unops) fixes `o`; `unop_paren` P/N by the `TLP`;
  then the operand step.  A prefix operator, so no infix issue.
- ★EBn was the HARDEST case — genuine OPERATOR-PRECEDENCE disambiguation, NOT a bracket scan.  The
  design below is now REALIZED: the scan is `eb_find`/`eb_find_acc` (slice 2j) proved correct by the
  operand law `eb_operand` → `eb_find_gtokens` (slices 2k-c/2k-d) — this paragraph explains WHY the
  landed scan is correct; `gtokens_inj`'s EBn case just applies it.
  `inner = gtokens p el ++ op_token o :: gtokens (S p) er` (`p = binop_prec o`) can carry SEVERAL
  depth-0 operators (`a+b*c` ⇒ `[a;+;b;*;c]`), so "the op at top balance level" does NOT locate the
  split.  The top operator is the RIGHTMOST depth-0 operator of MINIMAL precedence, justified by the
  ctx-wrapping invariants: `el` at ctx `p` wraps prec `< p` ⇒ its depth-0 ops have prec ≥ p; `er` at
  ctx `S p` wraps prec `≤ p` ⇒ its depth-0 ops have prec `> p`; `op_token o` has prec `p` ⇒ the
  minimal depth-0 precedence is `p`, achieved rightmost by `op_token o` (left-associative).  This is
  done by the operator-precedence scan `eb_find` + the wrapping bounds (`eb_top_prec`) + `op_token`/
  `prefix_token` injectivity (`op_token_inj`/`prefix_token_inj` LANDED, slice 2h) — the sub-arc is now
  CLOSED (`eb_find`/`eb_operand`/`eb_find_gtokens` LANDED, gated).  ⚠ TOKEN OVERLAP: `op_token` and
  `prefix_token` SHARE `TMinus`/`TStar`/`TAmp`/`TCaret` (BSub/UNeg, BMul/UDeref, BAnd/UAddr, BXor/UXor),
  so "depth-0 operator" is ambiguous at the token level — the scan classifies by prefix/infix POSITION
  (an infix op follows a COMPLETE operand; a unary prefix leads an operand), the parser's job reproved
  structurally.  `Nat.ltb (binop_prec o) ctx` P/N split by the leading `TLP` as usual.
  THE SCAN (LANDED as `eb_find_acc`, slice 2j): a left-to-right fold tracking (a) bracket depth `bd`, (b)
  an OPERAND-COMPLETE state — an operator token counts as INFIX only after a complete operand
  (atom/closer/finished postfix chain), so a leading `TMinus`/`TStar`/`TAmp`/`TCaret` reads unary, not
  binary — and (c) the RIGHTMOST depth-0 position of MINIMAL `infix_op` precedence.  ⚠ TYPE-CONTEXT
  HAZARD (review 47): `gttokens_ty` emits pointer types as `TStar :: …`, and type-led operands splice
  type tokens at EXPRESSION depth 0 — `ESliceLit`'s element type after `[]` (`a * []*int{}`) and
  `EMapLit`'s value type after `map[K]` — so a `TStar` INSIDE such a type is a POINTER star, not `BMul`.
  (`TMinus`/`TAmp`/`TCaret` never occur in types; only `TStar` does; `EAssert`'s type sits inside
  `TLP…TRP` at depth ≥ 1, safe.)  `eb_find_acc` therefore ALSO tracks TYPE-CONTEXT — a region entered
  ONLY by an expression-level type-LED form: `[]` (`ESliceLit`/`CTSlice`), `map` (`EMapLit`/`CTMap`),
  `chan` (`CTChan`) — and closed at the value delimiter `{` or `(`; a `TStar` counts as type syntax
  ONLY once inside such a scan.  ⚠ do NOT list a bare `*` as an opener (review 48): a depth-0 `TStar` at
  OPERAND-START is unary deref (`prefix_token UDeref`), not a type — cf. `*b * c` — and there is no
  bare-pointer conversion (`ConvTy` = slice/chan/map only, `GoAst.v:201`) and no `[N]` arrays (`GoTy`
  has no array ctor).  With type-context tracked, the invariants hold — and these two invariants are now
  REALIZED by the operand law `eb_operand` (INV-L `gtokens p el`: its depth-0 non-type infix ops have prec
  ≥ p and it ends operand-complete; INV-R `gtokens (S p) er`: prec > p — both are exactly the `eb_top_prec`
  bounds `eb_operand` threads).  On `inner`: the left gives prec ≥ p, `op_token o` prec p (the new min,
  rightmost so far), the right prec > p — so the scan lands on `op_token o`'s position; `op_token_inj`
  recovers `o`, an `app`-length split gives `el`/`er`, IH recurses.  ⛔ NOT derived from the parser:
  `parse (gtokens e) = e` (`gtokens_parse`; the string-level analogue is `parse_print_roundtrip`) + equal
  token lists would give uniqueness in two lines — the exact parser-as-foundation inversion the charter
  forbids; the scan REPROVES the precedence-climb structurally.
  TYPE-SKIP (LANDED): a type-led operand is skipped WHOLE by the pure `skip_gty : list Token -> option
  (list Token)` — NOT the parser `parse_gty_b` (that would make `gtokens_inj` lean on the parser); a token
  UTILITY like `bd`/`fsep` that returns just the remainder (`Acc`-recursive on length; the `map[K]V`
  two-part skip is non-structural).  (`skip_gty` + `skip_gty_types` (exactness) + `skip_gty_lt` (progress) LANDED as slice 2i —
  the type-skip foundation.  `skip_gty_acc` now returns the STRICT sig `{ r | length r < length toks }`,
  so `skip_gty_lt` is a trivial projection.)

  ★EBn LOCATOR — `eb_find` LANDED (slice 2j): the split is found by
  `eb_find : list Token -> option (list Token * BinOp)` — a SUFFIX-returning `Acc`-recursive scan
  (`eb_find_acc toks d oc a`) that walks the unwrapped tokens tracking bracket-depth `d` + operand-complete
  `oc`, returning `Some (R, o)` for the RIGHTMOST depth-0 infix operator `o` of MINIMAL precedence (the top
  constructor by left-assoc) with `R` the suffix after it.  Returning the SUFFIX (not a position) means no
  index arithmetic: the chosen op's `R` just propagates up the recursion.  Overlap is resolved by `oc`: at
  `oc=false` `*`/`&`/`^` are unary prefixes and `-(` is `UNeg`; at `oc=true` they are the infix ops
  (`infix_op`).  Type-led operands are skipped WHOLE by `skip_gty_acc` (so a pointer-`TStar` inside a type
  is never read as `BMul`); its STRICT sig hands the length proof to the value-group recursion's `Acc`
  cert DIRECTLY — no convoy (the earlier `eq_refl` convoy made a proof unable to case-split the scrutinee;
  the strict sig was the fix).  Bracket interiors (`d>0`) are depth-tracked, operators ignored.
  Slice 2k = the rightmost-min CORRECTNESS on the
  UNWRAPPED inner — `eb_find (gtokens (prec o) l ++ op_token o :: gtokens (S (prec o)) r) =
  Some (gtokens (S (prec o)) r, o)` (NOT on `gtokens ctx (EBn o l r)`: for `prec o < ctx` that is
  paren-WRAPPED and `eb_find` returns `None`; `gtokens_inj` peels the wrapper before calling `eb_find`),
  broken into: 2k-a `eb_find_acc_pi` (LANDED, gated) — [Acc]-proof-irrelevance so the correctness proof can
  reason equationally across the [Acc_inv] certs `eb_find_acc`'s own recursion produces.
  ★The two depth-scan laws (worked out from the `gtokens` clauses) — TWO SEPARATE inductions on `e`
  (`GExpr_ind'`), BOTH LANDED (the depth law (ii) is self-contained, so it was proved first and stands
  alone; it is NOT one conjunction with (i)):
    (ii) DEPTH (d≥1) — LANDED as `eb_depth` (`eb_find_acc (gtokens c e ++ suffix) (S sd) oc =
        eb_find_acc suffix (S sd) oc` — a gtokens block is skipped whole inside brackets).  Proved by
        induction on `GExpr` (NOT the arbitrary-balanced-`g` `eb_bal_skip` route — that needs a fiddly
        min-depth split and was AVOIDED), chaining the depth-step toolkit + `eb_depth_ty`/`args`/`pairs`.
    (i) OPERAND (d=0) — LANDED (`eb_operand`): `eb_find_acc (gtokens c e ++ suffix) 0 false = eb_combine
        (eb_top c e) suffix (eb_find_acc suffix 0 true)` where `eb_top c (EBn o _ r) = if prec o <? c then
        None else Some (gtokens (S prec o) r, o)`, `eb_top c _ = None` (LANDED); and `eb_combine (Some
        (rr,o)) suffix rest = match rest with Some (r',o') => if prec o' <=? prec o then rest else Some
        (rr ++ suffix, o) | None => Some (rr ++ suffix, o) end`, `eb_combine None _ rest = rest` (LANDED) —
        note the 3-ARG form: when the node's op wins its right part gains the trailing `suffix` (the split's
        R runs to end-of-input).  Per-constructor facts from `gtokens`: the postfix base `e0` sits at
        `gtokens 0 e0` WRAPPED by `op_needs_paren` (an EBn base ⇒ wrapped ⇒ a paren group ⇒ `eb_top`=None);
        `EUn`'s operand is `gtokens 0` wrapped by `unop_paren`; delimiters (`TDot TId`, `TLB..TRB`,
        `TLP..TRP`, `.(T)`, composites — the type via `skip_gty_acc`) are consumed by the DEPTH-0 step
        toolkit (`eb0f_*`/`eb0t_*`, LANDED) + `eb_depth` for the bracket interiors.  The lone non-primary
        case `EBn` unwrapped unfolds to `gtokens (prec o) l ++ op_token o :: gtokens (S prec o) r`, applies
        (i) to `l` (suffix = `op_token o :: …`), handles `op_token o` via `eb0t_infix` (infix at oc=true)
        whose recursion on `r` gives ops of prec > prec o, so `eb_combine` keeps `o`.
  The `EBn`-unwrapped crux was isolated into pure combine ALGEBRA (all LANDED, gated): `eb_infix_combine`
  (the node op IS the rightmost-min split over the right operand's scan), `eb_combine_left_absorb`/
  `eb_combine_absorb` (a left operand's op, prec ≥ the node op, never displaces the always-`Some` split);
  the type-led operands use `eb_type_skip`/`eb_type_slice`/`eb_type_conv` (whole-type skip via
  `skip_gty_acc` + `skip_gty_types`, parser-free) and `eb_top_unbare` for the bare unary operand.
  2k-d (LANDED) = the top-level `eb_find` correctness, in its GENERAL form `eb_find_gtokens : eb_find
  (gtokens ctx e) = eb_top ctx e` (proved from (i)=`eb_operand` at the empty suffix ⇒ the combine collapses
  to `eb_top`; `Some (R,o)` for an unwrapped `EBn`, `None` otherwise).  `eb_find_inner` (the `EBn`-node
  instance, `R ++ nil = R`) is now its corollary.  The two operator-bearing DIAGONALS are LANDED, both
  FULL: `gtokens_inj_ebn` (the EBn diagonal — `gtokens_ebn_inner`'s unwrapped-inner recursion (`app`-split
  at `op_token o`, IH on `l`/`r`) promoted past the ctx-wrapper: `eb_find_gtokens` ⇒ `eb_top` equality ⇒
  wrapped-vs-unwrapped mismatch is `None=Some`, same-wrapping strips to equal inner lists) and
  `gtokens_eun_inner` (the EUn diagonal — no ctx-wrapper).  The first cross-discriminator `nonatom_len`
  (atom vs everything, by length) is LANDED too, as are ALL FIVE postfix diagonals `gtokens_inj_esel`/
  `gtokens_inj_eindex`/`gtokens_inj_eassert`/`gtokens_inj_eslice`/`gtokens_inj_ecall` AND the three
  type-led composites `gtokens_inj_econv`/`gtokens_inj_eslicelit`/`gtokens_inj_emaplit`.  NEXT =
  the FULL `gtokens_inj` ASSEMBLY — the remaining bulk: the four ATOM-row diagonals (trivial — one
  distinguishing token each),
  and the ~14×13 cross-constructor discrimination (the genuine crux; likely surfaces further discrimination
  sub-lemmas), NOT just the EBn case.

Then `canon_expr_unique` (+ `gtokens_inj`) join the printer Print Assumptions gate.
Phase 3c = reprove `gprint_inj` off `gtokens_inj` + `gtokens_lex` (making it a corollary of the
canonical layer, no longer of `parse_print_roundtrip`), retiring the parser as the
expression-injectivity authority.

## Landing rules

Golden byte-identical throughout (proof-only; no emission change).  No new axioms;
every new public claim inside the gated surface.  The relation mirrors `gtokens`
EXACTLY — any divergence is a bug in one of them, never a "tolerance".  No demo may
substitute for the uniqueness theorem.
