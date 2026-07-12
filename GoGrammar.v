(** ============================================================================
    GoGrammar — the admitted Go grammar for the checkpoint-66 slice, over the post-ASI
    token stream, INDEPENDENT of any renderer policy (no renderer or token-printing
    function appears here; GoRender later PROVES its canonical stream derives).

    HONEST SCOPE: these rules define the token shape of exactly the admitted subset —
    [package main], one [func main()], brace-delimited straight-line [println] call
    statements terminated by (inserted) semicolons, over primitive expressions.  That
    this shape is also accepted by the real Go parser is the pinned-toolchain
    INTEGRATION claim (the e2e), not a theorem here.
    ============================================================================ *)
From Stdlib Require Import String ZArith List.
From Fido Require Import CoreType TypedIR GoToken.
Import ListNotations.
Open Scope string_scope.

(** Primitive expressions.  [true]/[false] are the predeclared identifiers. *)
Inductive ExprG : list GoToken -> TypedPrimExpr -> Prop :=
| GTrue  : ExprG [TIdent "true"]  (TEBool true)
| GFalse : ExprG [TIdent "false"] (TEBool false)
| GStr   : forall s (H : str_ok s = true),     ExprG [TStrLit s] (TEStr s H)
| GInt   : forall n (H : int_lit_ok n = true), ExprG [TIntLit n] (TEIntLit n H)
| GNeg   : forall n (H : neg_lit_ok n = true), ExprG [TMinus; TIntLit n] (TENeg n H).

(** Nonempty comma-separated argument list. *)
Inductive Args1G : list GoToken -> list TypedPrimExpr -> Prop :=
| GArg1    : forall ts e, ExprG ts e -> Args1G ts [e]
| GArgCons : forall ts e rest es,
    ExprG ts e -> Args1G rest es -> Args1G (ts ++ TComma :: rest) (e :: es).

(** Possibly-empty argument list ([println()] is valid Go). *)
Inductive ArgsG : list GoToken -> list TypedPrimExpr -> Prop :=
| GArgs0 : ArgsG [] []
| GArgsN : forall ts es, Args1G ts es -> ArgsG ts es.

(** A statement: a [println] call terminated by its (inserted) semicolon. *)
Inductive StmtG : list GoToken -> TypedStmt -> Prop :=
| GPrintln : forall ats args,
    ArgsG ats args ->
    StmtG (TIdent "println" :: TLParen :: ats ++ [TRParen; TSemi]) (TPrintln args).

Inductive BodyG : list GoToken -> list TypedStmt -> Prop :=
| GBody0    : BodyG [] []
| GBodyCons : forall ts s rest ss,
    StmtG ts s -> BodyG rest ss -> BodyG (ts ++ rest) (s :: ss).

(** The whole program unit: [package main;] [func main() {] body [};] (post-ASI). *)
Inductive ProgG : list GoToken -> TypedProgram -> Prop :=
| GProg : forall bts body,
    BodyG bts body ->
    ProgG ([KwPackage; TIdent "main"; TSemi;
            KwFunc; TIdent "main"; TLParen; TRParen; TLBrace]
             ++ bts ++ [TRBrace; TSemi])
          (mkTypedProgram body).
