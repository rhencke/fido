(** ============================================================================
    Surface — RAW proposed syntax for the checkpoint-66 slice (pre-elaboration).

    This layer may contain INVALID candidates: unresolved call names, out-of-range or
    negative "literals", nested negation, calls in argument position, a wrong package
    name.  It carries NO semantic classification — [println] here is just a string that
    elaboration must resolve through the predeclared CompileEnv.  Everything invalid is
    REJECTED by Elaborate (returns [None] / no derivation), so no [.go] can ever exist
    for it.  There is deliberately NO import constructor, NO user function, NO control
    flow — those are unrepresentable in this slice, not merely rejected.
    ============================================================================ *)
From Stdlib Require Import String ZArith List.
Import ListNotations.

(* [SCall] nests [list]; the auto-generated induction principle is shallow there, which is
   fine — no proof recurses through surface args (elaboration recurses over the LIST, not
   the nested scheme).  Silence the register-all hint. *)
#[local] Set Warnings "-register-all".

Inductive SurfaceExpr : Type :=
| SBool   : bool -> SurfaceExpr
| SIntLit : Z -> SurfaceExpr                       (* a DECIMAL literal; lexically nonneg — a negative Z here is an invalid candidate, rejected at elaboration *)
| SStr    : string -> SurfaceExpr                  (* raw payload bytes; charset validated at elaboration *)
| SNeg    : SurfaceExpr -> SurfaceExpr             (* unary minus; admitted ONLY over a nonneg int literal *)
| SCall   : string -> list SurfaceExpr -> SurfaceExpr.  (* unresolved callee name + args *)

Inductive SurfaceStmt : Type :=
| SExprStmt : SurfaceExpr -> SurfaceStmt.          (* expression statement; elaboration admits only a resolved builtin call *)

Record SurfaceProgram : Type := mkSurfaceProgram {
  sp_package : string;                             (* must resolve to exactly "main" *)
  sp_body    : list SurfaceStmt                    (* the body of the one [func main()] *)
}.
