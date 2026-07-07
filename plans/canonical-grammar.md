# The canonical relational grammar — the syntax AUTHORITY (CLAUDE.md "Syntax authority")

GOAL: the intended syntax authority is a RELATIONAL canonical grammar with parser-free
token injectivity — printer correctness proved against the GRAMMAR, the executable
parser demoted to derived tooling.  Target shapes (CLAUDE.md "Syntax authority"):
`CanonExpr : nat -> GExpr -> list Token -> Prop` (+ CanonStmt/CanonProgram),
`gprint_expr_canonical`, `canon_expr_unique`, `lex_gprint_expr` (likewise per layer).

WHAT EXISTS (in GoPrint.v): the token type + the fuel-free Acc lexer;
`gtokens ctx e` (the executable canonical token assignment); `gtokens_lex : lex (gprint
ctx e) = Some (gtokens ctx e)` (lexical faithfulness, expression layer); `gtokens_parse`
+ `parse_print_roundtrip` (the executable-parser round-trip); `print_stmt_inj`/
`print_program_inj` (statement-layer STRING injectivity).  The gap: no relational
grammar, and every injectivity fact routes through either the executable parser or
string equality — the parser is still the de-facto foundation.

## The architecture (the parser-free uniqueness discipline)

⛔ `canon_expr_unique` must be proved DIRECTLY on the token functions (the continuation-passing
`gtokens_det`, strong induction on expression size — full design in "Phase 3b/3c" below) —
NEVER via `gtokens_parse`: deriving uniqueness from the parser's functionality would reinstate
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
gated.  NEXT = Phase 3b SLICE 2: the continuation-passing gtokens_det (canon_expr_unique =
canon_expr_tokens + its s1=s2=nil instance), design pinned below.  bdip/balanced_close_split
(the fixed-tail/paren-peel tool) are written + verified-to-compile — to land WITH gtokens_det so
nothing unused is committed; last0/last_group_split were RULED OUT (see the design's dead-end note).

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
   e1 = e2`, parser-free — via `canon_expr_tokens` + the continuation-passing `gtokens_det`
   (strong induction on expression size).  Full design + the two ruled-out dead ends
   (balanced-prefix cancellation; `last0`) in the "Phase 3b/3c" section below.  Slice 1 (the
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
- Split machinery.  ⚠ TWO dead ends ruled out: (1) "balanced prefix cancels" is FALSE
  (`gtokens 0 (EId x) = [TId x]` is a balanced proper prefix of `gtokens 0 (EBn Add (EId x)
  (EId y))`); (2) a `last0` "last depth-0 position" argument is ALSO insufficient — `gtparen b`
  can carry an INTERNAL depth-0 opener (when `b` is itself `EIndex`/`ECall`: its own `[`/`(` sits
  at depth 0 after the balanced operand), so bracket depth alone cannot pin where the operand
  ends.  ★THE RIGHT STRUCTURE is a CONTINUATION-PASSING DETERMINISM lemma, strong induction on
  the SIZE of `e1` — the operand IH (on a strictly smaller expression) carries the continuation
  and resolves the extent WITHOUT any global bracket scan:

    `gtokens_det : forall e1 e2 ctx s1 s2, (gtokens ctx e1 ++ s1)%list = (gtokens ctx e2 ++ s2)%list
                   -> e1 = e2 /\ s1 = s2`

  `gtokens_inj` is the `s1=s2=nil` instance; `canon_expr_unique` = `canon_expr_tokens` + it.
- `bdip` (all-kinds first-dip) + `bdip_app_nodip` + `app_eq_length` give `balanced_close_split`
  (any closer `cl`): `ts1 ++ cl::r1 = ts2 ++ cl::r2`, `ts1`/`ts2` balanced ⇒ `ts1=ts2 /\ r1=r2`.
  Its ROLE in `gtokens_det`: strip the PAREN-DELIMITED operand case `gtparen e0 =
  TLP::(gtokens 0 e0 ++ TRP::nil)` — the matched `TRP` closes the leading `TLP`, so
  balanced_close_split (with `cl := TRP`, prefix `gtokens 0 e0` balanced by `gtokens_balanced`)
  peels it, exposing `gtokens 0 e0` for the operand IH. (bdip/balanced_close_split are written +
  verified-to-compile, to land WITH gtokens_det; `last0` is NOT needed and will not be written.)

`gtokens_det` by strong induction on `size e1`, `destruct e1`/`destruct e2`, per pair:
- Atoms (EId/EInt/EStr/EHex): single-token; the continuation makes the head token decide — equal
  heads ⇒ same atom + `s1=s2`; cross-shape auto-discriminated by distinct closed token ctors.
- Every operand-bearing form: peel the FIXED framing tokens into the continuation, `destruct
  op_needs_paren` (bare ⇒ operand IH directly; paren ⇒ `balanced_close_split TRP` then operand
  IH), then recurse on the remaining sub-expressions (index/args/pairs via list-length induction
  with `balanced_close_split` on the comma/colon-joined balanced elements) threading the
  continuation.  EConv/lits lead with a TYPE (`canon_ty_unique`/`gttokens_ty_inj`); the `[]`/`map`
  lead tokens discriminate them cross-shape.  EBn's infix `op_token` sits at top balance level.

Then `canon_expr_unique` (+ `gtokens_det`/`gtokens_inj`) join the printer Print Assumptions gate.
Phase 3c = reprove `gprint_inj` off `parse_print_roundtrip` (now a corollary of `gtokens_inj` +
`gtokens_lex`), retiring the parser as the expression-injectivity authority.

## Landing rules

Golden byte-identical throughout (proof-only; no emission change).  No new axioms;
every new public claim inside the gated surface.  The relation mirrors `gtokens`
EXACTLY — any divergence is a bug in one of them, never a "tolerance".  No demo may
substitute for the uniqueness theorem.
