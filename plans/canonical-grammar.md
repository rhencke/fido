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
the `last0`/`bdip`/`fsep` split lemmas, `no_depth0_sep`, `gtokens_args_inj`).  STILL OPEN: the
complete-list `gtokens_inj` (⇒ `canon_expr_unique`).  Until it lands, `gprint_inj` still routes
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
gated.  NEXT = Phase 3b SLICE 2: the complete-list gtokens_inj (canon_expr_unique =
canon_expr_tokens + gtokens_inj), design pinned below.  Phase 3b SLICE 2a LANDED — the `last0`
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
`gtokens_args_nonnil`/`gtokens_args_single`/`gtokens_args_cons2`), gated.  STILL TO WRITE: the
paren/bare operand discrimination; `gtokens_pairs_inj` (the map-pair analogue: `k TColon v` pairs
comma-joined); ★the EBn OPERATOR-PRECEDENCE
disambiguation (rightmost-minimal-precedence depth-0 op + the ctx-wrapping invariant lemmas +
`op_token`/`prefix_token` injectivity) — the crux risk; and `gtokens_inj` itself.  (The
arbitrary-SUFFIX determinism lemma was found FALSE — see the design.)

## Phases (each: green, golden byte-identical, gated, reviewed)

1. **CanonTy + CanonExpr (the relations).**  Mutual inductives mirroring `gtokens`'
   arms as PRODUCTIONS — `CanonTy : GoTy -> list Token -> Prop`,
   `CanonConvTy : ConvTy -> list Token -> Prop`,
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
   arbitrary-suffix determinism lemma) in the "Phase 3b/3c" section below.  Slice 1 (the
   `bd` balance toolkit + `gtokens_balanced`) is LANDED.
4. **CanonStmt/CanonProgram** + the same trio over the statement printer (the
   statement layer's `lex_gprint_stmt` does not exist yet — build the statement
   `gtokens` analogue first).
5. **Re-base the parser as derived tooling**: `parse_sound : parse ts = Some (e, nil)
   -> CanonExpr 0 e ts`, `parse_complete` (its converse via canon_expr_tokens +
   gtokens_parse — legitimate HERE because the parser is the SUBJECT, not the
   foundation); rewrite GoPrint's header authority claims; the PROGRESS gate list
   gains the canonical surface (one manifest-gated `Print Assumptions`).

## Phase 3b/3c — the expression uniqueness proof (design, pinned before coding)

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
  `bdip`/`balanced_close_split`, `fsep`/`sep_split`, `no_depth0_sep`, and `gtokens_args_inj`
  LANDED + gated; `gtokens_pairs_inj` (map pairs) is TO WRITE.)

`gtokens_inj` by structural induction on `e1` (`GExpr_ind'`), `destruct e2`, per pair — on
COMPLETE lists (no suffix):
- Atoms (EId/EInt/EStr/EHex): single-token; the head token decides; cross-shape auto-discriminated
  by distinct closed token ctors.
- Fixed-tail postfix ESel: strip the 2-token tail `TDot :: TId f` (equal, since the whole lists
  are equal) ⇒ `f_a=f_b` and `gtparen e0_a = gtparen e0_b`; then the operand step.
- Delimited-group forms (EIndex/ESlice/ECall/EConv/EAssert/ESliceLit/EMapLit): end in a CLOSER;
  `last0` pins the operand/type prefix length, `app_eq_length` isolates the group, `OPEN` stripped
  + `balanced_close_split cl:=CLOSE` peels `body`, then the single sub-expr (EIndex) recurses
  directly / the multi-element `body` splits via `gtokens_args_inj`/`gtokens_pairs_inj` (EIndex has
  one index, ESlice one `lo:hi` colon, ECall/lits a comma list, EMapLit colon+comma pairs); recurse
  on each.  EConv/lits lead with a TYPE (`canon_ty_unique`); `[]`/`map` lead tokens discriminate.
- Operand step `gtparen e0_a = gtparen e0_b -> e0_a = e0_b` (COMPLETE): `destruct op_needs_paren`
  both sides — bare/bare and paren/paren strip to `gtokens 0 e0_a = gtokens 0 e0_b` ⇒ IH; the
  paren/bare MISMATCH needs a discrimination lemma (a complete bare `gtokens 0 e` cannot equal a
  single `TLP…TRP`-wrapped group) — via `bd`/leading-token.  ★the two OPEN sub-lemmas: the
  `last0` group split, and the paren/bare operand discrimination.
- EUn: leading `prefix_token o` (injective on unops) fixes `o`; `unop_paren` P/N by the `TLP`;
  then the operand step.  A prefix operator, so no infix issue.
- ★EBn is the HARDEST case — genuine OPERATOR-PRECEDENCE disambiguation, NOT a bracket scan.
  `inner = gtokens p el ++ op_token o :: gtokens (S p) er` (`p = binop_prec o`) can carry SEVERAL
  depth-0 operators (`a+b*c` ⇒ `[a;+;b;*;c]`), so "the op at top balance level" does NOT locate the
  split.  The top operator is the RIGHTMOST depth-0 operator of MINIMAL precedence, justified by the
  ctx-wrapping invariants: `el` at ctx `p` wraps prec `< p` ⇒ its depth-0 ops have prec ≥ p; `er` at
  ctx `S p` wraps prec `≤ p` ⇒ its depth-0 ops have prec `> p`; `op_token o` has prec `p` ⇒ the
  minimal depth-0 precedence is `p`, achieved rightmost by `op_token o` (left-associative).  This
  needs an operator-precedence scan + the wrapping-invariant lemmas + `op_token`/`prefix_token`
  injectivity — a self-contained sub-arc, the crux risk of Phase 3b.  `Nat.ltb (binop_prec o) ctx`
  P/N split by the leading `TLP` as usual.

Then `canon_expr_unique` (+ `gtokens_inj`) join the printer Print Assumptions gate.
Phase 3c = reprove `gprint_inj` off `parse_print_roundtrip` (now a corollary of `gtokens_inj` +
`gtokens_lex`), retiring the parser as the expression-injectivity authority.

## Landing rules

Golden byte-identical throughout (proof-only; no emission change).  No new axioms;
every new public claim inside the gated surface.  The relation mirrors `gtokens`
EXACTLY — any divergence is a bug in one of them, never a "tolerance".  No demo may
substitute for the uniqueness theorem.
