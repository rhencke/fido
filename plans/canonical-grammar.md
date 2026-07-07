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

## Landing rules

Golden byte-identical throughout (proof-only; no emission change).  No new axioms;
every new public claim inside the gated surface.  The relation mirrors `gtokens`
EXACTLY — any divergence is a bug in one of them, never a "tolerance".  No demo may
substitute for the uniqueness theorem.
