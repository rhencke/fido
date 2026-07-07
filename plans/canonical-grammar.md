# The canonical relational grammar — the syntax AUTHORITY (CLAUDE.md; boss checkpoint-49 order #5)

GOAL: the intended syntax authority is a RELATIONAL canonical grammar with parser-free
token injectivity — printer correctness proved against the GRAMMAR, the executable
parser demoted to derived tooling.  Target shapes (CLAUDE.md "Syntax authority"):
`CanonExpr : nat -> GExpr -> list Token -> Prop` (+ CanonStmt/CanonProgram),
`gprint_expr_canonical`, `canon_expr_unique`, `lex_gprint_expr` (likewise per layer).

WHAT EXISTS (GoPrint.v, 6199 lines): the token type + the fuel-free Acc lexer;
`gtokens ctx e` (the executable canonical token assignment); `gtokens_lex : lex (gprint
ctx e) = Some (gtokens ctx e)` (lexical faithfulness, expression layer); `gtokens_parse`
+ `parse_print_roundtrip` (the executable-parser round-trip); `print_stmt_inj`/
`print_program_inj` (statement-layer STRING injectivity).  The gap: no relational
grammar, and every injectivity fact routes through either the executable parser or
string equality — the parser is still the de-facto foundation.

## The architecture (the parser-free uniqueness discipline)

⛔ `canon_expr_unique` must be proved DIRECTLY on the relation (leading-token
discrimination + balanced-bracket framing + strong induction) — NEVER via
`gtokens_parse`: deriving uniqueness from the parser's functionality would reinstate
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
children).  NEXT = Phase 3b/3c, canon_expr_unique (parser-free) at the expression layer.

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
   e1 = e2`, parser-free.  Toolkit: per-production LEADING-TOKEN discrimination (each
   production's first token classifies its constructor within a precedence context);
   bracket-balance framing (args/pairs/index/slice bodies are delimited, so equal
   concatenations split identically — `tokens_balanced` + an append-cancellation
   lemma family); strong induction on token-list length for the nested lists.
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
- Two split lemmas, both proved by a first-/last-dip index argument (`firstdip` for closers;
  a right-scan `lastrise` mirror for the opener-led groups):
  - `balanced_close_split` (generalizes `balanced_rb_split` to any closer): balanced prefixes
    before an unmatched closer coincide — frames the fixed-tail suffixes.
  - `last_group_split` (rightmost balanced bracket framing): `a ++ (OP :: m ++ CL :: nil) =
    a' ++ (OP :: m' ++ CL :: nil)` with `a,a',m,m'` balanced ⇒ `a=a' /\ m=m'` — frames the
    variable-length `[...]`/`(...)`/`{...}` groups of EIndex/ESlice/ECall/EAssert/lits.

`gtokens_inj` by structural induction on `e1`, `destruct e2`, per pair:
- Atoms (EId/EInt/EStr/EHex): single-token lists; head-token injectivity (`tok0_str`-style),
  and the closed distinct token constructors auto-discriminate cross-shape.
- Fixed-tail postfix ESel/EAssert: strip the fixed 2- resp. 4-token tail (identical since the
  whole lists are equal), giving `t0a = t0b`, recurse.  The `op_needs_paren` boolean split is a
  premise equality (like the type layer's leaf discrimination), so P vs N pairs discharge by the
  paren token being present/absent.
- Variable-tail postfix EIndex/ESlice/ECall + EConv/ESliceLit/EMapLit: `last_group_split` (and
  for the inner arg/pair lists, an induction on list length with `balanced_close_split` on the
  comma-joined balanced elements).
- EUn: leading `prefix_token o` — the operator token discriminates from atoms/postfix (whose
  leading token comes from the operand and is never a bare prefix operator except via a nested
  EUn, handled by recursion); `unop_paren` P/N split by the `TLP` presence.
- EBn: the `Nat.ltb (binop_prec o) ctx` P/N split by the leading `TLP`; the infix `op_token o`
  at the top balance level is located by `bd` (the operator sits at depth 0 between two balanced
  operands) — the one genuinely infix case, framed by a depth-0 operator-scan lemma.
- Cross-shape pairs discharged by the leading token + first-group opener kind (EConv leads with a
  TYPE token, ESliceLit with `TLB TRB`, EMapLit with `TMap`), all closed-constructor distinct.

Then `canon_expr_unique` + `gtokens_inj` join the printer Print Assumptions gate.  Phase 3c =
reprove `gprint_inj` off `parse_print_roundtrip` (now a corollary of `gtokens_inj` + `gtokens_lex`),
retiring the parser as the expression-injectivity authority.

## Landing rules

Golden byte-identical throughout (proof-only; no emission change).  No new axioms;
every new public claim inside the gated surface.  The relation mirrors `gtokens`
EXACTLY — any divergence is a bug in one of them, never a "tolerance".  No demo may
substitute for the uniqueness theorem.
