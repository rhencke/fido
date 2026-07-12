(** ============================================================================
    Elaborate — declarative resolution/typing for the checkpoint-66 slice, with an
    executable elaborator proved SOUND and COMPLETE against it.

    The declarative relations ([ElabExpr]/[ElabStmt]/[ElabProgram]) are the compile
    authority for this slice — NOT a boolean equality.  [elab_program] is the executable
    face; [elab_program_sound] and [elab_program_complete] pin the two exactly together
    over the whole admitted subset.  A rejected candidate has NO derivation and elaborates
    to [None] — it can never reach the typed IR, so no [.go] can ever exist for it (the
    REJECTIONS section pins representative classes by computation).
    ============================================================================ *)
From Stdlib Require Import String ZArith List Bool.
From Fido Require Import TargetConfig CoreType Surface TypedIR CompileEnv.
Import ListNotations.
Open Scope string_scope.

(** [check b] decides [b = true] and hands back the evidence.  [check_true] is what lets
    the executable elaborator reproduce EXACTLY the typed value any derivation names:
    [subst] rewrites the derivation's proof to [eq_refl] (proofs of a decidable equality
    are unique), so both sides coincide definitionally. *)
Definition check (b : bool) : option (b = true) :=
  match b as x return option (x = true) with
  | true  => Some eq_refl
  | false => None
  end.

Lemma check_true : forall b (H : b = true), check b = Some H.
Proof. intros b H. subst b. reflexivity. Qed.

(** ---- The declarative judgments ---- *)

Inductive ElabExpr : SurfaceExpr -> TypedPrimExpr -> Prop :=
| EEBool : forall b, ElabExpr (SBool b) (TEBool b)
| EEStr  : forall s (H : str_ok s = true), ElabExpr (SStr s) (TEStr s H)
| EEInt  : forall n (H : int_lit_ok n = true), ElabExpr (SIntLit n) (TEIntLit n H)
| EENeg  : forall n (H : neg_lit_ok n = true), ElabExpr (SNeg (SIntLit n)) (TENeg n H).

Inductive ElabStmt : SurfaceStmt -> TypedStmt -> Prop :=
| ESPrintln : forall name args targs,
    lookup_predeclared name = Some BPrintln ->
    Forall2 ElabExpr args targs ->
    ElabStmt (SExprStmt (SCall name args)) (TPrintln targs).

Inductive ElabProgram : SurfaceProgram -> TypedProgram -> Prop :=
| EProg : forall body tbody,
    Forall2 ElabStmt body tbody ->
    ElabProgram (mkSurfaceProgram "main" body) (mkTypedProgram tbody).

(** ---- The executable elaborator ---- *)

Definition elab_expr (e : SurfaceExpr) : option TypedPrimExpr :=
  match e with
  | SBool b   => Some (TEBool b)
  | SStr s    => match check (str_ok s)      with Some H => Some (TEStr s H)   | None => None end
  | SIntLit n => match check (int_lit_ok n)  with Some H => Some (TEIntLit n H) | None => None end
  | SNeg (SIntLit n) =>
                 match check (neg_lit_ok n)  with Some H => Some (TENeg n H)   | None => None end
  | SNeg _    => None      (* negation of anything but a nonneg int literal *)
  | SCall _ _ => None      (* a call has no value in this slice — never an argument *)
  end.

Fixpoint elab_args (es : list SurfaceExpr) : option (list TypedPrimExpr) :=
  match es with
  | [] => Some []
  | e :: es' =>
      match elab_expr e, elab_args es' with
      | Some te, Some tes => Some (te :: tes)
      | _, _ => None
      end
  end.

Definition elab_stmt (s : SurfaceStmt) : option TypedStmt :=
  match s with
  | SExprStmt (SCall name args) =>
      match lookup_predeclared name with
      | Some BPrintln =>
          match elab_args args with
          | Some targs => Some (TPrintln targs)
          | None => None
          end
      | None => None
      end
  | SExprStmt _ => None    (* a non-call expression statement ([1], ["x"]) is invalid Go: value not used *)
  end.

Fixpoint elab_body (ss : list SurfaceStmt) : option (list TypedStmt) :=
  match ss with
  | [] => Some []
  | s :: ss' =>
      match elab_stmt s, elab_body ss' with
      | Some ts, Some tss => Some (ts :: tss)
      | _, _ => None
      end
  end.

Definition elab_program (p : SurfaceProgram) : option TypedProgram :=
  if String.eqb (sp_package p) "main"
  then match elab_body (sp_body p) with
       | Some tb => Some (mkTypedProgram tb)
       | None => None
       end
  else None.

(** ---- Soundness: the elaborator only produces derivable results ---- *)

Lemma elab_expr_sound : forall e te, elab_expr e = Some te -> ElabExpr e te.
Proof.
  intros e te H.
  destruct e as [ b | n | s | e' | name args ]; simpl in H.
  - injection H as <-. constructor.
  - destruct (check (int_lit_ok n)) as [Hn|]; [ injection H as <- | discriminate ].
    constructor.
  - destruct (check (str_ok s)) as [Hs|]; [ injection H as <- | discriminate ].
    constructor.
  - destruct e' as [ | n | | | ]; try discriminate.
    destruct (check (neg_lit_ok n)) as [Hn|]; [ injection H as <- | discriminate ].
    constructor.
  - discriminate.
Qed.

Lemma elab_args_sound : forall es tes, elab_args es = Some tes -> Forall2 ElabExpr es tes.
Proof.
  induction es as [ | e es' IH ]; intros tes H; simpl in H.
  - injection H as <-. constructor.
  - destruct (elab_expr e) as [te|] eqn:He; [ | discriminate ].
    destruct (elab_args es') as [tes'|] eqn:Hes; [ | discriminate ].
    injection H as <-. constructor; [ exact (elab_expr_sound _ _ He) | exact (IH _ eq_refl) ].
Qed.

Lemma elab_stmt_sound : forall s ts, elab_stmt s = Some ts -> ElabStmt s ts.
Proof.
  intros [e] ts H. simpl in H.
  destruct e as [ | | | | name args ]; try discriminate.
  destruct (lookup_predeclared name) as [[]|] eqn:Hn; [ | discriminate ].
  destruct (elab_args args) as [targs|] eqn:Ha; [ | discriminate ].
  injection H as <-. econstructor; [ exact Hn | exact (elab_args_sound _ _ Ha) ].
Qed.

Lemma elab_body_sound : forall ss tss, elab_body ss = Some tss -> Forall2 ElabStmt ss tss.
Proof.
  induction ss as [ | s ss' IH ]; intros tss H; simpl in H.
  - injection H as <-. constructor.
  - destruct (elab_stmt s) as [ts|] eqn:Hs; [ | discriminate ].
    destruct (elab_body ss') as [tss'|] eqn:Hss; [ | discriminate ].
    injection H as <-. constructor; [ exact (elab_stmt_sound _ _ Hs) | exact (IH _ eq_refl) ].
Qed.

Theorem elab_program_sound : forall p tp, elab_program p = Some tp -> ElabProgram p tp.
Proof.
  intros [pkg body] tp H. unfold elab_program in H. simpl in H.
  destruct (String.eqb pkg "main") eqn:Hp; [ | discriminate ].
  apply String.eqb_eq in Hp. subst pkg.
  destruct (elab_body body) as [tb|] eqn:Hb; [ | discriminate ].
  injection H as <-. constructor. exact (elab_body_sound _ _ Hb).
Qed.

(** ---- Completeness: every derivation is reproduced exactly by the elaborator ---- *)

Lemma elab_expr_complete : forall e te, ElabExpr e te -> elab_expr e = Some te.
Proof.
  intros e te D. destruct D as [ b | s H | n H | n H ]; simpl.
  - reflexivity.
  - rewrite (check_true _ H). reflexivity.
  - rewrite (check_true _ H). reflexivity.
  - rewrite (check_true _ H). reflexivity.
Qed.

Lemma elab_args_complete : forall es tes, Forall2 ElabExpr es tes -> elab_args es = Some tes.
Proof.
  intros es tes D. induction D as [ | e te es' tes' De _ IH ]; simpl.
  - reflexivity.
  - rewrite (elab_expr_complete _ _ De), IH. reflexivity.
Qed.

Lemma elab_stmt_complete : forall s ts, ElabStmt s ts -> elab_stmt s = Some ts.
Proof.
  intros s ts D. destruct D as [ name args targs Hn Ha ]. simpl.
  rewrite Hn, (elab_args_complete _ _ Ha). reflexivity.
Qed.

Lemma elab_body_complete : forall ss tss, Forall2 ElabStmt ss tss -> elab_body ss = Some tss.
Proof.
  intros ss tss D. induction D as [ | s ts ss' tss' Ds _ IH ]; simpl.
  - reflexivity.
  - rewrite (elab_stmt_complete _ _ Ds), IH. reflexivity.
Qed.

Theorem elab_program_complete : forall p tp, ElabProgram p tp -> elab_program p = Some tp.
Proof.
  intros p tp D. destruct D as [ body tbody Hb ].
  unfold elab_program. simpl.
  rewrite (elab_body_complete _ _ Hb). reflexivity.
Qed.

(** ---- REJECTIONS (the B-corpus) — representative invalid classes elaborate to [None],
    each BY COMPUTATION, so no derivation exists ([elab_program_sound] contrapositive)
    and no [.go] can ever be produced for them. ---- *)

(* an unresolved callee: [printf] is not predeclared *)
Example reject_unresolved_callee :
  elab_program (mkSurfaceProgram "main" [SExprStmt (SCall "printf" [SStr "hi"])]) = None.
Proof. reflexivity. Qed.

(* a package-qualified name: imports do not exist in this slice *)
Example reject_qualified_callee :
  elab_program (mkSurfaceProgram "main" [SExprStmt (SCall "fmt.Println" [SStr "hi"])]) = None.
Proof. reflexivity. Qed.

(* a wrong package clause: the program unit must be exactly [package main] *)
Example reject_wrong_package :
  elab_program (mkSurfaceProgram "Main" []) = None.
Proof. reflexivity. Qed.

(* a bare value as a statement: [42] alone is invalid Go (value not used) *)
Example reject_value_statement :
  elab_program (mkSurfaceProgram "main" [SExprStmt (SIntLit 42)]) = None.
Proof. reflexivity. Qed.

(* a call in argument position: [println] has no value in this slice *)
Example reject_call_argument :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SCall "println" [SIntLit 1]])]) = None.
Proof. reflexivity. Qed.

(* nested negation [- -5]: negation is admitted only over a nonneg literal *)
Example reject_nested_negation :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SNeg (SNeg (SIntLit 5))])]) = None.
Proof. reflexivity. Qed.

(* negation of a non-integer *)
Example reject_negated_bool :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SNeg (SBool true)])]) = None.
Proof. reflexivity. Qed.

(* a literal node holding a negative number: no such Go literal exists *)
Example reject_negative_literal_node :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SIntLit (-1)])]) = None.
Proof. reflexivity. Qed.

(* constant overflow: [2^63] does not fit the pinned [int]; Go rejects it at compile
   time, so it must die HERE (no-expected-Go-failure rule) *)
Example reject_int_overflow :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SIntLit 9223372036854775808])]) = None.
Proof. vm_compute. reflexivity. Qed.

(* negated-constant overflow: [-(2^63 + 1)] underflows the pinned [int] *)
Example reject_neg_overflow :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SNeg (SIntLit 9223372036854775809)])]) = None.
Proof. vm_compute. reflexivity. Qed.

(* boundary ACCEPTANCE: [-(2^63)] is exactly int_min — valid Go, admitted *)
Example accept_min_int :
  exists tp, elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SNeg (SIntLit 9223372036854775808)])]) = Some tp.
Proof. eexists. vm_compute. reflexivity. Qed.

(* a control byte in a string payload (BEL): outside the admitted charset *)
Example reject_control_byte_string :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SStr (String (Ascii.ascii_of_nat 7) "")])]) = None.
Proof. vm_compute. reflexivity. Qed.

(* a byte >127 in a string payload: could break source UTF-8 validity — rejected *)
Example reject_high_byte_string :
  elab_program (mkSurfaceProgram "main"
    [SExprStmt (SCall "println" [SStr (String (Ascii.ascii_of_nat 255) "")])]) = None.
Proof. vm_compute. reflexivity. Qed.
