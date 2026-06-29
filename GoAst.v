(** ============================================================================
    GoAst.v — structured Go SYNTAX (the AST: "what can be written").
    Part of the AST-first certified-emission spine (see ARCHITECTURE.md): GoAst is
    syntax only — it may represent unsafe programs; safety lives in GoSafe, printing
    in GoPrint.  NO raw/opaque syntax strings (charter §8 Rule 1): every constructor
    takes validated/semantic payloads (validated [Ident]/[TyName], a [Z] literal),
    never a raw expr/stmt/type string.  Moved here verbatim from the pre-split printer seed; the
    printer / lexer / parser / round-trip theorems live in GoPrint.v.
    ============================================================================ *)
From Stdlib Require Import String List Ascii ZArith Lia Bool Eqdep_dec.
Import ListNotations.
Open Scope string_scope.

(** ---- IDENTIFIER VALIDITY (for nominal [GTNamed] types) ---- a Go identifier is [_A-Za-z][_A-Za-z0-9]*.
    These come BEFORE [GoTy] because [GTNamed] carries a VALIDATED identifier ([Ident], a [sig]): the
    validity is part of the TYPE, so an invalid nominal name (a keyword, or non-identifier text) is
    UNREPRESENTABLE — not merely excluded by a side-condition theorem.  The would-be cycle ([valid_ident]
    must reject type keywords, but the keyword→[GoTy] map [classify] needs [GoTy]) is broken by factoring
    out [is_type_keyword]: the keyword SET is just strings, independent of [GoTy]; [classify] (below
    [GoTy]) reuses that set to assign each keyword its type. *)
Definition is_idc (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (andb (Nat.leb 48 n) (Nat.leb n 57)) (andb (Nat.leb 65 n) (Nat.leb n 90)))
      (orb (andb (Nat.leb 97 n) (Nat.leb n 122)) (Nat.eqb n 95)).
Definition is_idstart (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (andb (Nat.leb 65 n) (Nat.leb n 90)) (andb (Nat.leb 97 n) (Nat.leb n 122))) (Nat.eqb n 95).
Fixpoint all_idc (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (is_idc c) (all_idc s') end.
(** Two [GoTy]-independent STRING keyword sets (so they gate the identifier predicates ahead of [GoTy]):
    [is_type_keyword] is the 14 builtin scalar type names + [chan]/[map] (used for parser invertibility);
    [go_keyword] is Go's 25 RESERVED WORDS — so an identifier is never a keyword ([func]/[return]/[var]/
    [type]/[struct]/[interface]/[select]/… are rejected, which the old [valid_ident] wrongly accepted). *)
Definition is_type_keyword (s : string) : bool :=
  existsb (String.eqb s)
    ["int64"; "int32"; "int16"; "int8"; "int"; "uint64"; "uint32"; "uint16"; "uint8"; "uint";
     "bool"; "string"; "float64"; "float32"; "chan"; "map"].
Definition go_keyword (s : string) : bool :=
  existsb (String.eqb s)
    ["break"; "case"; "chan"; "const"; "continue"; "default"; "defer"; "else"; "fallthrough"; "for";
     "func"; "go"; "goto"; "if"; "import"; "interface"; "map"; "package"; "range"; "return";
     "select"; "struct"; "switch"; "type"; "var"].
(** A Go IDENTIFIER (for an [AIdent] atom): non-empty, [_A-Za-z]-led, all identifier chars, and NOT a Go
    keyword.  A builtin type name like [int]/[string] IS a valid identifier (predeclared, shadowable —
    Go allows [var int = 5]), so [go_ident] ACCEPTS it; only [nominal_type_ident] rejects it. *)
Definition go_ident (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c _  => andb (andb (is_idstart c) (all_idc s)) (negb (go_keyword s))
  end.
(** A NOMINAL TYPE NAME (for a [GTNamed] tag): a [go_ident] that is additionally not a builtin type name
    (nor [chan]/[map] — those are keywords) — so it print-parses back as [GTNamed], never as a scalar /
    chan / map.  This is the parser-INVERTIBILITY refinement; [nominal_type_ident s -> go_ident s]. *)
Definition nominal_type_ident (s : string) : bool := andb (go_ident s) (negb (is_type_keyword s)).
(** The two validity-carrying sig types (validity IN THE TYPE — invalid names unrepresentable; both
    extract to a bare [string], the proof erased): [Ident] for expression identifiers ([AIdent]),
    [TyName] for nominal type names ([GTNamed]). *)
Definition Ident : Type := { s : string | go_ident s = true }.
Definition mkIdent (s : string) (H : go_ident s = true) : Ident := exist _ s H.
Definition TyName : Type := { s : string | nominal_type_ident s = true }.
Definition mkTyName (s : string) (H : nominal_type_ident s = true) : TyName := exist _ s H.

(** A Go type, as the plugin renders them.  Note [GTInt] (Go's platform [int], the [GoInt]/[TInt64]
    tag) is DISTINCT from [GTInt64] (the full-width [int64], the [GoI64]/[TI64] tag) — conflating them
    is exactly the kind of bug the verified printer rules out (it caught one in the first integration). *)
Inductive GoTy : Type :=
  | GTInt     : GoTy
  | GTInt64   : GoTy
  | GTBool    : GoTy
  | GTString  : GoTy
  | GTFloat64 : GoTy
  | GTFloat32 : GoTy
  | GTUint    : GoTy
  | GTU8      : GoTy
  | GTI8      : GoTy
  | GTU16     : GoTy
  | GTI16     : GoTy
  | GTU32     : GoTy
  | GTI32     : GoTy
  | GTU64     : GoTy
  | GTPtr     : GoTy -> GoTy
  | GTSlice   : GoTy -> GoTy
  | GTChan    : GoTy -> GoTy
  | GTMap     : GoTy -> GoTy -> GoTy
  | GTNamed   : TyName -> GoTy.

Inductive BinOp : Type :=
  (* Go precedence 5: *  /  %  <<  >>  &  &^ *)
  | BMul | BDiv | BRem | BShl | BShr | BAnd | BAndNot
  (* Go precedence 4: +  -  |  ^ *)
  | BAdd | BSub | BOr | BXor
  (* Go precedence 3: ==  !=  <  <=  >  >= *)
  | BEq | BNe | BLt | BLe | BGt | BGe
  (* Go precedence 2 / 1: &&  || *)
  | BLAnd | BLOr.

Inductive UnaryOp : Type := UNot | UXor | UDeref | UAddr | UNeg.

(** ---- CONVERSION type-form ([ConvTy]) — the bracket/keyword-led GoTy subset usable as a type-form
    conversion operand [T(x)] (printer/parser in GoPrint).  Excludes a pointer head [*T] ([*T(x)] is
    ambiguous with the deref [*(T(x))]).  Defined BEFORE [GExpr] because the [EConv] node carries one. *)
Inductive ConvTy : Type :=
  | CTSlice : GoTy -> ConvTy          (* []T     *)
  | CTChan  : GoTy -> ConvTy          (* chan T  *)
  | CTMap   : GoTy -> GoTy -> ConvTy. (* map[K]V *)
Definition convty_ty (c : ConvTy) : GoTy :=
  match c with CTSlice u => GTSlice u | CTChan u => GTChan u | CTMap k v => GTMap k v end.

(** ---- THE CLEAN AST ---- the Go expression grammar above, fully structured: every node is a typed form,
    with NO raw/opaque string constructor (by construction it cannot represent unstructured text).  CORE + the
    five postfix forms + the type-form conversion [EConv] (grows toward composite-literals / func-lits).
    Literals carry their value. *)
Inductive GExpr : Type :=
  | EId  : Ident -> GExpr
  | EInt : Z -> GExpr
  | EUn  : UnaryOp -> GExpr -> GExpr
  | EBn  : BinOp -> GExpr -> GExpr -> GExpr
  | ESel : GExpr -> Ident -> GExpr    (* postfix selector [e.field] — binds tighter than every operator *)
  | EIndex : GExpr -> GExpr -> GExpr  (* postfix index [e[i]] — also a tightest-binding postfix form *)
  | ESlice : GExpr -> GExpr -> GExpr -> GExpr  (* postfix two-index slice [e[lo:hi]] (both bounds present) *)
  | ECall : GExpr -> list GExpr -> GExpr  (* postfix call [e(a1, .., an)] — the arg list is a [list GExpr] *)
  | EAssert : GExpr -> GoTy -> GExpr   (* postfix type assertion [e.(T)] — the type child is a [GoTy] *)
  | EConv : ConvTy -> GExpr -> GExpr.  (* type-form conversion [[]T(x)] / [chan T(x)] / [map[K]V(x)] — PREFIX *)

(** Custom induction principle: the auto-generated [GExpr_ind] gives NO hypothesis for the elements of the
    [ECall] argument list (a nested [list GExpr]), so structural recursion into the args is impossible.  This
    recursor adds [Forall P args] for the [ECall] case (built by an inner list recursion), and mirrors the
    auto principle's binder order for the other seven constructors so existing [induction e as [...]] proofs
    keep working verbatim under [using GExpr_ind']. *)
Fixpoint GExpr_ind' (P : GExpr -> Prop)
  (fid  : forall i, P (EId i))
  (fint : forall z, P (EInt z))
  (fun_ : forall o e0, P e0 -> P (EUn o e0))
  (fbn  : forall o l, P l -> forall r, P r -> P (EBn o l r))
  (fsel : forall e0, P e0 -> forall f, P (ESel e0 f))
  (fidx : forall e0, P e0 -> forall i, P i -> P (EIndex e0 i))
  (fslc : forall e0, P e0 -> forall lo, P lo -> forall hi, P hi -> P (ESlice e0 lo hi))
  (fcall : forall e0, P e0 -> forall args, List.Forall P args -> P (ECall e0 args))
  (fassert : forall e0, P e0 -> forall T, P (EAssert e0 T))
  (fconv : forall c e0, P e0 -> P (EConv c e0))
  (e : GExpr) : P e :=
  match e with
  | EId i  => fid i
  | EInt z => fint z
  | EUn o e0 => fun_ o e0 (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv e0)
  | EBn o l r => fbn o l (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv l)
                       r (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv r)
  | ESel e0 f => fsel e0 (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv e0) f
  | EIndex e0 i => fidx e0 (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv e0)
                         i (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv i)
  | ESlice e0 lo hi => fslc e0 (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv e0)
                            lo (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv lo)
                            hi (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv hi)
  | ECall e0 args => fcall e0 (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv e0) args
      ((fix args_ind (l : list GExpr) : List.Forall P l :=
          match l with
          | nil => List.Forall_nil P
          | a :: r => List.Forall_cons a (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv a) (args_ind r)
          end) args)
  | EAssert e0 T => fassert e0 (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv e0) T
  | EConv c e0 => fconv c e0 (GExpr_ind' P fid fint fun_ fbn fsel fidx fslc fcall fassert fconv e0)
  end.

(** ---- GO STATEMENTS ---- the body of [func main].  PHASE-4 (ARCHITECTURE.md §11), grown form-by-form, each
    constructor reusing the verified expression layer: [GsExprStmt e] is an EXPRESSION STATEMENT (e.g. a call
    [f(args)]) — it reuses the machine-checked printer [gprint]; [GsReturn] is a bare [return] (no value),
    valid as the tail of a void func like [main]; [GsReturnVal e] is a value return [return e] (printed
    `return <e>`).  Like [GExpr] this is SYNTAX only: it can represent a non-call expr statement, OR a value
    return in a VOID function (both illegal Go) — that is GoSafe's concern, not the AST's (and [GsReturnVal]
    is currently REJECTED by [stmt_ok] precisely because the only function we emit, [main], is void).  Grows
    (assignment / var / if / for / …) further. *)
Inductive GoStmt : Type :=
  | GsExprStmt  : GExpr -> GoStmt   (* an expression used as a statement, e.g. a function call [f(a, b)] *)
  | GsReturn    : GoStmt            (* a bare [return] (no value) — valid as the tail of a void func like main *)
  | GsReturnVal : GExpr -> GoStmt.  (* a value return [return e] — valid only in a NON-void function (not main) *)

(** ---- A GO PROGRAM ---- the top-level unit GoEmit emits: a package name + the body of [func main()] (a
    list of [GoStmt]s).  No raw strings — the package is a validated [Ident] and the body is structured
    statements.  Still small (no imports / top-level decls yet) but no longer an empty shell: it carries a
    real func body, the printer renders it via [gprint], and GoEmit certifies+prints it.  Grows as the AST
    does. *)
Record Program : Type := mkProgram { prog_pkg : Ident ; prog_body : list GoStmt }.
