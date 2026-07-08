# The canonical relational grammar — the syntax AUTHORITY (CLAUDE.md "Syntax authority")

GOAL: the intended syntax authority is a RELATIONAL canonical grammar with parser-free
token injectivity — printer correctness proved against the GRAMMAR, the executable
parser demoted to derived tooling.  Target shapes (CLAUDE.md "Syntax authority"):
`CanonExpr : nat -> GExpr -> list Token -> Prop` (+ CanonStmt/CanonProgram),
`gprint_expr_canonical`, `canon_expr_unique`, `lex_gprint_expr` (likewise per layer).

_This doc is DESIGN only. Live status — which phases/slices/diagonals have landed and what is next —
is **PROGRESS.md "NEXT"** alone; per-slice landed history is in the git log._

THE LAYERS (design context, in GoPrint.v): the token type + the fuel-free Acc lexer; `gtokens ctx e`
(the executable canonical token assignment); the RELATIONAL grammar `CanonTy`/`CanonExpr` +
`canon_ty_tokens`/`canon_expr_tokens` (token-functionality) + `gprint_expr_canonical` (printer
canonicity) + `lex_gprint_expr` (lexical faithfulness, `lex (gprint ctx e) = Some (gtokens ctx e)`
composed with the canonical derivation).  Type-level token uniqueness is `canon_ty_unique`, PARSER-FREE
via `gttokens_ty_inj`; expression uniqueness has the SAME shape via the complete-list `gtokens_inj` (⇒
`canon_expr_unique`), designed in the "Phase 3b/3c" section below.  ARCHITECTURE NOTE: the arc moves
`gprint_inj` OFF the executable parser — Phase 3c reproves `gprint_inj` off `gtokens_inj` (replacing the
`gtokens_parse` + `parse_print_roundtrip` route), the statement layer (`print_stmt_inj`/
`print_program_inj`, string injectivity) moves onto the canonical layer likewise, and the parser is
retired to derived tooling LAST (Phase 5).

## The architecture (the parser-free uniqueness discipline)

⛔ `canon_expr_unique` must be proved DIRECTLY on the token functions (the complete-list
`gtokens_inj`, structural induction on `e1` with a `last0` bracket split — full design in
"Phase 3b/3c" below) — NEVER via `gtokens_parse`: deriving uniqueness from the parser's would reinstate
the parser as the foundation, the exact inversion CLAUDE.md forbids.  The executable
parser is re-based LAST as derived tooling (`parse_sound`/`parse_complete` against the
relation).

## Printer precedence/associativity (parse-shape preservation, NOT full-parenthesization)

`GExpr` has NO paren constructor — parens are a PRINTING ARTIFACT emitted only where Go's binding rules
would otherwise reparse the tokens into a DIFFERENT AST.  The context `ctx : nat` is the parent
precedence: an `EBn o l r` prints `l` at ctx `binop_prec o` and `r` at ctx `S (binop_prec o)` (Go binops
are LEFT-associative), so a same-precedence LEFT child stays bare and a same-precedence RIGHT child is
parenthesized — `Add (Add a b) c` → `a + b + c`, `Add a (Add b c)` → `a + (b + c)`.  Omission is
PARSE-SHAPE preservation ONLY, NEVER semantic associativity: the printer never collapses `a + (b + c)` to
`a + b + c` (no AST normalization); `gtokens_inj` proves those distinct ASTs give distinct tokens.  The
`eb_find`/`eb_operand` scan is the parser-free proof that a block's tokens locate the rightmost-min top
operator (the left-assoc split), never `parse`.

EXPLICIT DEFERRED FRONTIERS (after the expression arc seals — do NOT expand mid-proof, per checkpoint-53):
- Named-type conversions `T(x)` (T a NAME) are EXCLUDED — token-shape-ambiguous with calls absent a
  compile env Γ.  `ConvTy` is slice/chan/map ONLY (the "Option B" subset): conversions are type-led
  through `[]`/`chan`/`map`, syntactically disjoint from calls — exactly what makes the `ECall`-vs-`EConv`
  discrimination parser-free.  Γ-indexed `CanonExpr` (Option A) is the long-term path.
- Directional channel TYPES `chan<-`/`<-chan` are NOT modeled (`GoTy` has only bidirectional `chan T`), so
  the leftmost-`chan` parenthesization rules (`chan (<-chan T)`, the `(<-chan T)(x)` conversion head) do
  not arise in the current subset.  Adding `ChanDir` + `needs_type_parens` is future type-grammar work.

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
   arbitrary-suffix determinism lemma) in the "Phase 3b/3c" section below.  `gtokens_inj` (the assembly
   over the per-constructor diagonals + the ~14×13 cross-constructor discrimination) is the crux;
   `canon_expr_unique` follows from it exactly as `canon_ty_unique` follows from `gttokens_ty_inj`.
4. **CanonStmt/CanonProgram** + the same trio over the statement printer (build the
   statement `gtokens` analogue + its `lex_gprint_stmt` first, then mirror the expression layer).
5. **Re-base the parser as derived tooling**: `parse_sound : parse ts = Some (e, nil)
   -> CanonExpr 0 e ts`, `parse_complete` (its converse via canon_expr_tokens +
   gtokens_parse — legitimate HERE because the parser is the SUBJECT, not the
   foundation); rewrite GoPrint's header authority claims; the PROGRESS gate list
   gains the canonical surface (one manifest-gated `Print Assumptions`).

## Phase 3b/3c — the expression uniqueness proof (design + per-slice/per-diagonal technique)

TARGET (mirrors the type layer exactly): `canon_expr_unique ctx e1 e2 ts` = `canon_expr_tokens`
on both sides + a PARSER-FREE `gtokens_inj : forall ctx e1 e2, gtokens ctx e1 = gtokens ctx e2
-> e1 = e2`.  (`canon_ty_unique` has this shape via `gttokens_ty_inj` — the type-layer template.)  Everything
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
  `last0_group : last0 (P ++ OPEN :: body ++ CLOSE :: nil) = length P`,
  via `nd`/`nd_add`/`bd_nd`/`bd_prefix_defined`/`last0_aux_inv`.  NOTE the closer
  hypothesis is unnecessary — the final token is at depth-before 1, so it never records a
  best; the split holds for any final token.  The `app_eq_length`-based split COROLLARY is trivial.)
- `bdip` (all-kinds first-dip) + `bdip_app_nodip` + `app_eq_length` give `balanced_close_split`
  (any closer `cl`): `ts1 ++ cl::r1 = ts2 ++ cl::r2`, `ts1`/`ts2` balanced ⇒ `ts1=ts2 /\ r1=r2`.
  ROLE: after `last0` isolates the group `OPEN :: body ++ CLOSE :: nil` and the `OPEN` is stripped,
  `balanced_close_split cl:=CLOSE` peels the `body` token list (balanced) off the final `CLOSE`.
- The comma/colon-joined ELEMENTS inside `body` (ECall args, ESliceLit elems, EMapLit pairs,
  ESlice's `lo:hi`) are NOT split by `balanced_close_split` (`TComma`/`TColon` are depth-neutral,
  not closers).  They need `gtokens_args_inj`/`gtokens_pairs_inj` — list injectivity by induction
  on the element list, splitting at the TOP-LEVEL (depth-0-within-the-group) `TComma`/`TColon`
  via a first-depth-0-separator lemma, resting on `no_depth0_sep`: no expression's `gtokens 0 e`
  contains a depth-0 `TComma`/`TColon` (they occur only inside nested groups, at depth ≥1), so the
  first top-level separator delimits the first element.  (`last0`/`last0_group`,
  `bdip`/`balanced_close_split`, `fsep`/`sep_split`, `no_depth0_sep`, `gtokens_args_inj`, and
  `gtokens_pairs_inj`.)

`gtokens_inj` by structural induction on `e1` (`GExpr_ind'`), `destruct e2`, per pair — on
COMPLETE lists (no suffix):
- Atoms (EId/EInt/EStr/EHex): single-token; the head token separates the four atoms; a longer form
  (even one sharing the head token, e.g. a bare-atom-based `ESel`) is ruled out by `nonatom_len` (length
  ≥ 2 for every non-atom).
- Fixed-tail postfix ESel (`gtokens_inj_esel`): strip the 2-token tail `TDot :: TId f` (equal, since the
  whole lists are equal) ⇒ `f_a=f_b` and `gtparen e0_a = gtparen e0_b`; then the operand step.
- Delimited-group forms (EIndex/ESlice/ECall/EConv/EAssert/ESliceLit/EMapLit — `gtokens_inj_eindex`/
  `_eslice`/`_ecall`/`_econv`/`_eassert`/`_eslicelit`/`_emaplit`): end in a CLOSER;
  `last0` pins the operand/type prefix length, `app_eq_length` isolates the group, `OPEN` stripped
  + `balanced_close_split cl:=CLOSE` peels `body`, then the single sub-expr (EIndex) recurses
  directly / the multi-element `body` splits via `gtokens_args_inj`/`gtokens_pairs_inj` (EIndex has
  one index, ESlice one `lo:hi` colon, ECall/lits a comma list, EMapLit colon+comma pairs); recurse
  on each.  EConv/lits lead with a TYPE (`gttokens_ty_inj`/`convty_ty_inj` recovers it); `[]`/`map`
  lead tokens discriminate.
- Operand step `gtparen e0_a = gtparen e0_b -> e0_a = e0_b` (COMPLETE, `bare_not_paren_group` +
  `gtparen_inj`): `destruct op_needs_paren` both sides — bare/bare and paren/paren strip to
  `gtokens 0 e0_a = gtokens 0 e0_b` ⇒ IH; the paren/bare MISMATCH is impossible (a complete bare
  `gtokens 0 e` cannot equal a single `TLP…TRP`-wrapped group) — `bare_not_paren_group` via `last0`.
- EUn (`gtokens_eun_inner`): leading `prefix_token o` (injective on unops) fixes `o`; `unop_paren` P/N
  by the `TLP`; then the operand step.  A prefix operator, so no infix issue.
- ★EBn is the HARDEST case — genuine OPERATOR-PRECEDENCE disambiguation, NOT a bracket scan.  The
  design: a scan `eb_find`/`eb_find_acc`, correct by the operand law `eb_operand` → `eb_find_gtokens`
  — this paragraph explains WHY the scan is correct; `gtokens_inj`'s EBn case (`gtokens_inj_ebn`)
  applies it.
  `inner = gtokens p el ++ op_token o :: gtokens (S p) er` (`p = binop_prec o`) can carry SEVERAL
  depth-0 operators (`a+b*c` ⇒ `[a;+;b;*;c]`), so "the op at top balance level" does NOT locate the
  split.  The top operator is the RIGHTMOST depth-0 operator of MINIMAL precedence, justified by the
  ctx-wrapping invariants: `el` at ctx `p` wraps prec `< p` ⇒ its depth-0 ops have prec ≥ p; `er` at
  ctx `S p` wraps prec `≤ p` ⇒ its depth-0 ops have prec `> p`; `op_token o` has prec `p` ⇒ the
  minimal depth-0 precedence is `p`, achieved rightmost by `op_token o` (left-associative).  This is
  done by the operator-precedence scan `eb_find` + the wrapping bounds (`eb_top_prec`) + `op_token`/
  `prefix_token` injectivity (`op_token_inj`/`prefix_token_inj`) — the scan
  `eb_find`/`eb_operand`/`eb_find_gtokens` realizes it.  ⚠ TOKEN OVERLAP: `op_token` and
  `prefix_token` SHARE `TMinus`/`TStar`/`TAmp`/`TCaret` (BSub/UNeg, BMul/UDeref, BAnd/UAddr, BXor/UXor),
  so "depth-0 operator" is ambiguous at the token level — the scan classifies by prefix/infix POSITION
  (an infix op follows a COMPLETE operand; a unary prefix leads an operand), the parser's job reproved
  structurally.  `Nat.ltb (binop_prec o) ctx` P/N split by the leading `TLP` as usual.
  THE SCAN (`eb_find_acc`): a left-to-right fold tracking (a) bracket depth `bd`, (b)
  an OPERAND-COMPLETE state — an operator token counts as INFIX only after a complete operand
  (atom/closer/finished postfix chain), so a leading `TMinus`/`TStar`/`TAmp`/`TCaret` reads unary, not
  binary — and (c) the RIGHTMOST depth-0 position of MINIMAL `infix_op` precedence.  ⚠ TYPE-CONTEXT
  HAZARD: `gttokens_ty` emits pointer types as `TStar :: …`, and type-led operands splice
  type tokens at EXPRESSION depth 0 — `ESliceLit`'s element type after `[]` (`a * []*int{}`) and
  `EMapLit`'s value type after `map[K]` — so a `TStar` INSIDE such a type is a POINTER star, not `BMul`.
  (`TMinus`/`TAmp`/`TCaret` never occur in types; only `TStar` does; `EAssert`'s type sits inside
  `TLP…TRP` at depth ≥ 1, safe.)  `eb_find_acc` therefore ALSO tracks TYPE-CONTEXT — a region entered
  ONLY by an expression-level type-LED form: `[]` (`ESliceLit`/`CTSlice`), `map` (`EMapLit`/`CTMap`),
  `chan` (`CTChan`) — and closed at the value delimiter `{` or `(`; a `TStar` counts as type syntax
  ONLY once inside such a scan.  ⚠ do NOT list a bare `*` as an opener: a depth-0 `TStar` at
  OPERAND-START is unary deref (`prefix_token UDeref`), not a type — cf. `*b * c` — and there is no
  bare-pointer conversion (`ConvTy` = slice/chan/map only, in `GoAst.v`) and no `[N]` arrays (`GoTy`
  has no array ctor).  With type-context tracked, the invariants hold — and these two invariants are
  captured by the operand law `eb_operand` (INV-L `gtokens p el`: its depth-0 non-type infix ops have prec
  ≥ p and it ends operand-complete; INV-R `gtokens (S p) er`: prec > p — both are exactly the `eb_top_prec`
  bounds `eb_operand` threads).  On `inner`: the left gives prec ≥ p, `op_token o` prec p (the new min,
  rightmost so far), the right prec > p — so the scan lands on `op_token o`'s position; `op_token_inj`
  recovers `o`, an `app`-length split gives `el`/`er`, IH recurses.  ⛔ NOT derived from the parser:
  `parse (gtokens e) = e` (`gtokens_parse`; the string-level analogue is `parse_print_roundtrip`) + equal
  token lists would give uniqueness in two lines — the exact parser-as-foundation inversion the charter
  forbids; the scan REPROVES the precedence-climb structurally.
  TYPE-SKIP: a type-led operand is skipped WHOLE by the pure `skip_gty : list Token -> option
  (list Token)` — NOT the parser `parse_gty_b` (that would make `gtokens_inj` lean on the parser); a token
  UTILITY like `bd`/`fsep` that returns just the remainder (`Acc`-recursive on length; the `map[K]V`
  two-part skip is non-structural).  (`skip_gty` + `skip_gty_types` (exactness) + `skip_gty_lt` (progress) —
  the type-skip foundation.  `skip_gty_acc` returns the STRICT sig `{ r | length r < length toks }`,
  so `skip_gty_lt` is a trivial projection.)

  ★EBn LOCATOR — `eb_find`: the split is found by
  `eb_find : list Token -> option (list Token * BinOp)` — a SUFFIX-returning `Acc`-recursive scan
  (`eb_find_acc toks d oc a`) that walks the unwrapped tokens tracking bracket-depth `d` + operand-complete
  `oc`, returning `Some (R, o)` for the RIGHTMOST depth-0 infix operator `o` of MINIMAL precedence (the top
  constructor by left-assoc) with `R` the suffix after it.  Returning the SUFFIX (not a position) means no
  index arithmetic: the chosen op's `R` just propagates up the recursion.  Overlap is disambiguated by `oc`: at
  `oc=false` `*`/`&`/`^` are unary prefixes and `-(` is `UNeg`; at `oc=true` they are the infix ops
  (`infix_op`).  Type-led operands are skipped WHOLE by `skip_gty_acc` (so a pointer-`TStar` inside a type
  is never read as `BMul`); its STRICT sig hands the length proof to the value-group recursion's `Acc`
  cert DIRECTLY — no convoy: the strict sig lets a proof case-split the scrutinee (an `eq_refl` convoy
  would block it).  Bracket interiors (`d>0`) are depth-tracked, operators ignored.
  The rightmost-min CORRECTNESS on the
  UNWRAPPED inner — `eb_find (gtokens (prec o) l ++ op_token o :: gtokens (S (prec o)) r) =
  Some (gtokens (S (prec o)) r, o)` (NOT on `gtokens ctx (EBn o l r)`: for `prec o < ctx` that is
  paren-WRAPPED and `eb_find` returns `None`; `gtokens_inj` peels the wrapper before calling `eb_find`),
  broken into: `eb_find_acc_pi` — [Acc]-proof-irrelevance so the correctness proof can
  reason equationally across the [Acc_inv] certs `eb_find_acc`'s own recursion produces.
  ★The two depth-scan laws (from the `gtokens` clauses) — TWO SEPARATE inductions on `e`
  (`GExpr_ind'`) (the depth law (ii) is self-contained — a separate induction, NOT one conjunction
  with (i)):
    (ii) DEPTH (d≥1) — `eb_depth` (`eb_find_acc (gtokens c e ++ suffix) (S sd) oc =
        eb_find_acc suffix (S sd) oc` — a gtokens block is skipped whole inside brackets).  By
        induction on `GExpr` (NOT the arbitrary-balanced-`g` `eb_bal_skip` route, which needs a fiddly
        min-depth split), chaining the depth-step toolkit + `eb_depth_ty`/`args`/`pairs`.
    (i) OPERAND (d=0) — `eb_operand`: `eb_find_acc (gtokens c e ++ suffix) 0 false = eb_combine
        (eb_top c e) suffix (eb_find_acc suffix 0 true)` where `eb_top c (EBn o _ r) = if prec o <? c then
        None else Some (gtokens (S prec o) r, o)`, `eb_top c _ = None`; and `eb_combine (Some
        (rr,o)) suffix rest = match rest with Some (r',o') => if prec o' <=? prec o then rest else Some
        (rr ++ suffix, o) | None => Some (rr ++ suffix, o) end`, `eb_combine None _ rest = rest` —
        note the 3-ARG form: when the node's op wins its right part gains the trailing `suffix` (the split's
        R runs to end-of-input).  Per-constructor facts from `gtokens`: the postfix base `e0` sits at
        `gtokens 0 e0` WRAPPED by `op_needs_paren` (an EBn base ⇒ wrapped ⇒ a paren group ⇒ `eb_top`=None);
        `EUn`'s operand is `gtokens 0` wrapped by `unop_paren`; delimiters (`TDot TId`, `TLB..TRB`,
        `TLP..TRP`, `.(T)`, composites — the type via `skip_gty_acc`) are consumed by the DEPTH-0 step
        toolkit (`eb0f_*`/`eb0t_*`) + `eb_depth` for the bracket interiors.  The lone non-primary
        case `EBn` unwrapped unfolds to `gtokens (prec o) l ++ op_token o :: gtokens (S prec o) r`, applies
        (i) to `l` (suffix = `op_token o :: …`), handles `op_token o` via `eb0t_infix` (infix at oc=true)
        whose recursion on `r` gives ops of prec > prec o, so `eb_combine` keeps `o`.
  The `EBn`-unwrapped crux factors into pure combine ALGEBRA: `eb_infix_combine`
  (the node op IS the rightmost-min split over the right operand's scan), `eb_combine_left_absorb`/
  `eb_combine_absorb` (a left operand's op, prec ≥ the node op, never displaces the always-`Some` split);
  the type-led operands use `eb_type_skip`/`eb_type_slice`/`eb_type_conv` (whole-type skip via
  `skip_gty_acc` + `skip_gty_types`, parser-free) and `eb_top_unbare` for the bare unary operand.
  The top-level `eb_find` correctness, in its GENERAL form `eb_find_gtokens : eb_find
  (gtokens ctx e) = eb_top ctx e` (from (i)=`eb_operand` at the empty suffix ⇒ the combine collapses
  to `eb_top`; `Some (R,o)` for an unwrapped `EBn`, `None` otherwise); `eb_find_inner` (the `EBn`-node
  instance, `R ++ nil = R`) is its corollary.  The same-constructor DIAGONALS then discriminate per pair:
  the two operator-bearing — `gtokens_inj_ebn` (the EBn diagonal — `gtokens_ebn_inner`'s unwrapped-inner
  recursion (`app`-split at `op_token o`, IH on `l`/`r`) promoted past the ctx-wrapper: `eb_find_gtokens`
  ⇒ `eb_top` equality ⇒ wrapped-vs-unwrapped mismatch is `None=Some`, same-wrapping strips to equal inner
  lists) and `gtokens_eun_inner` (the EUn diagonal — no ctx-wrapper); the length cross-discriminator
  `nonatom_len` (atom vs everything); the five postfix diagonals `gtokens_inj_esel`/`gtokens_inj_eindex`/
  `gtokens_inj_eassert`/`gtokens_inj_eslice`/`gtokens_inj_ecall`; and the three type-led composites
  `gtokens_inj_econv`/`gtokens_inj_eslicelit`/`gtokens_inj_emaplit` — the last eight share the split:
  base-or-type prefix peeled by `last0_group` + `app_eq_length`, then `app_inj_tail`/`sep_split`/
  `gtokens_args_inj`/`gtokens_pairs_inj`, the type recovered via `gttokens_ty_inj` + `convty_ty_inj`.  The
  full `gtokens_inj` assembles these diagonals with the four ATOM-row diagonals (single distinguishing
  token each) and the ~14×13 cross-constructor discrimination — the genuine crux (not just the EBn case;
  likely surfacing further discrimination sub-lemmas).

Then `canon_expr_unique` (+ `gtokens_inj`) join the printer Print Assumptions gate.
Phase 3c = reprove `gprint_inj` off `gtokens_inj` + `gtokens_lex` (making it a corollary of the
canonical layer, no longer of `parse_print_roundtrip`), retiring the parser as the
expression-injectivity authority.

## Landing rules

Golden byte-identical throughout (proof-only; no emission change).  No new axioms;
every new public claim inside the gated surface.  The relation mirrors `gtokens`
EXACTLY — any divergence is a bug in one of them, never a "tolerance".  No demo may
substitute for the uniqueness theorem.
