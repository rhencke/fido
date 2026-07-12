(** ============================================================================
    GoCompile — the static/compiler-admissibility authority for [GoAST], and the
    ELABORATOR that resolves a raw [GoFile] into a decorated [CompiledFile].

    This is the doc's §2 authority, not a boolean.  It owns:

      - [CompiledFile] / [CompiledStmt] / [CompiledExpr]: the SAME program tree with
        ambiguity replaced by CHECKED FACTS.  [EIdent] (any identifier) is resolved to
        a predeclared boolean [CBool]; the statement callee (any identifier) is resolved
        to the ONE admitted builtin ([CPrintln] — there is no unresolved-callee form);
        an integer magnitude carries INTRINSIC target-representability evidence, so an
        out-of-range constant is UNREPRESENTABLE in the compiled tree.  Package and
        function are the pinned constants ("main"), so a non-"main" program cannot be a
        [CompiledFile] at all.  There are no unresolved names left for GoSafe/GoRender.
      - [CompilesFile]: the DECLARATIVE relation raw ↦ compiled.
      - [go_compile]: the EXECUTABLE elaborator, proved SOUND and COMPLETE against the
        relation, DETERMINISTIC, and its output ERASES back to the raw tree.  It is never
        a bare [check = true]; a boolean is not the authority (doc PAINFUL_LESSONS #6).

    What GoCompile means, precisely: within the fragment [GoAST] can represent, a
    [CompiledFile] exists iff the program is package "main" / func "main" whose every
    statement is a [println] of admissible primitive operands, each in the pinned target
    [int] range.  Whether that admitted fragment's canonical rendering is in fact accepted
    by the pinned Go toolchain is a LAST-MILE integration fact (the e2e), NOT proved here —
    GoCompile formalizes the static rules; it does not contain a Go-compiler oracle.

    Target facts are consumed MECHANICALLY, not restated: the int range comes from
    [TargetConfig.int_min]/[int_max] (derived from [tc_int_bits]); the [println] rule
    requires [tc_println_builtin target = true].  So a target without the builtin, or with
    a different int width, changes what compiles — the dependency is real, not decorative.
    ============================================================================ *)
From Stdlib Require Import String NArith ZArith List Bool Eqdep_dec.
From Fido Require Import TargetConfig Literals GoIdent GoAST.
Import ListNotations.
Open Scope Z_scope.

(** A boolean, reflected as a decision that REMEMBERS the witnessing equation — the standard
    way to build an evidence-carrying constructor from a decidable check.  Self-contained so
    the theory depends on no incidental Stdlib module path. *)
Definition bool_sumbool (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** ---- The decorated / resolved tree (the "CompiledGoAST") ---- *)

Inductive CompiledExpr : Type :=
| CBool : bool -> CompiledExpr                                      (* [EIdent] resolved to a predeclared bool *)
| CInt  : forall n : N, (Z.of_N n <=? int_max) = true -> CompiledExpr   (* magnitude, representable by construction *)
| CNeg  : forall n : N, (Z.of_N n <=? - int_min) = true -> CompiledExpr (* -magnitude, representable by construction *)
| CStr  : forall s : string, str_ok s = true -> CompiledExpr.       (* admitted-charset string value *)

Inductive CompiledStmt : Type :=
| CPrintln : list CompiledExpr -> CompiledStmt.                     (* callee resolved to the [println] builtin *)

(** The compiled program.  Package and function are the pinned "main" constants — carried
    implicitly (the type cannot represent any other), reconstructed by [erase_file]. *)
Record CompiledFile : Type := mkCompiledFile { cf_body : list CompiledStmt }.

(** ---- The declarative judgment: raw [GoFile] ↦ decorated [CompiledFile] ---- *)

Inductive CompilesExpr : GoExpr -> CompiledExpr -> Prop :=
| CmpTrue  : forall i, ident_str i = "true"%string  -> CompilesExpr (EIdent i) (CBool true)
| CmpFalse : forall i, ident_str i = "false"%string -> CompilesExpr (EIdent i) (CBool false)
| CmpInt   : forall n (H : (Z.of_N n <=? int_max) = true),     CompilesExpr (EInt n) (CInt n H)
| CmpNeg   : forall n (H : (Z.of_N n <=? - int_min) = true),   CompilesExpr (ENeg n) (CNeg n H)
| CmpStr   : forall s H, CompilesExpr (EStr s H) (CStr s H).

Inductive CompilesStmt : GoStmt -> CompiledStmt -> Prop :=
| CmpCall : forall callee args cargs,
    ident_str callee = "println"%string ->       (* the callee resolves to the builtin name *)
    tc_println_builtin target = true ->           (* which the pinned target provides *)
    Forall2 CompilesExpr args cargs ->
    CompilesStmt (SCall callee args) (CPrintln cargs).

Inductive CompilesFile : GoFile -> CompiledFile -> Prop :=
| CmpFile : forall raw cbody,
    ident_str (file_pkg raw) = "main"%string ->
    ident_str (fn_name (file_func raw)) = "main"%string ->
    Forall2 CompilesStmt (fn_body (file_func raw)) cbody ->
    CompilesFile raw (mkCompiledFile cbody).

(** The public predicate: the program has a compilation. *)
Definition GoCompile (raw : GoFile) : Prop := exists c, CompilesFile raw c.

(** ---- The executable elaborator ---- *)
(* [option] rather than [result CompileError]: an informative error type has no consumer
   yet (the plugin's diagnostics would be its first), and an unused error enum is fat.
   Soundness/completeness do not depend on the error content — divergence from the doc's
   suggested [result] shape is deliberate and noted. *)

Definition compile_expr (e : GoExpr) : option CompiledExpr :=
  match e with
  | EIdent i =>
      if String.eqb (ident_str i) "true" then Some (CBool true)
      else if String.eqb (ident_str i) "false" then Some (CBool false)
      else None
  | EInt n =>
      match bool_sumbool (Z.of_N n <=? int_max) with
      | left H  => Some (CInt n H)
      | right _ => None
      end
  | ENeg n =>
      match bool_sumbool (Z.of_N n <=? - int_min) with
      | left H  => Some (CNeg n H)
      | right _ => None
      end
  | EStr s H => Some (CStr s H)
  end.

Fixpoint compile_exprs (es : list GoExpr) : option (list CompiledExpr) :=
  match es with
  | [] => Some []
  | e :: es' =>
      match compile_expr e, compile_exprs es' with
      | Some c, Some cs => Some (c :: cs)
      | _, _ => None
      end
  end.

Definition compile_stmt (s : GoStmt) : option CompiledStmt :=
  match s with
  | SCall callee args =>
      if String.eqb (ident_str callee) "println" && tc_println_builtin target
      then match compile_exprs args with
           | Some cs => Some (CPrintln cs)
           | None => None
           end
      else None
  end.

Fixpoint compile_stmts (ss : list GoStmt) : option (list CompiledStmt) :=
  match ss with
  | [] => Some []
  | s :: ss' =>
      match compile_stmt s, compile_stmts ss' with
      | Some c, Some cs => Some (c :: cs)
      | _, _ => None
      end
  end.

Definition go_compile (raw : GoFile) : option CompiledFile :=
  if String.eqb (ident_str (file_pkg raw)) "main"
     && String.eqb (ident_str (fn_name (file_func raw))) "main"
  then match compile_stmts (fn_body (file_func raw)) with
       | Some b => Some (mkCompiledFile b)
       | None => None
       end
  else None.

(** ---- Soundness: the elaborator only produces genuine compilations ---- *)

Lemma compile_expr_sound : forall e c, compile_expr e = Some c -> CompilesExpr e c.
Proof.
  intros e c H. destruct e as [ i | n | n | s Hs ]; cbn [compile_expr] in H.
  - destruct (String.eqb (ident_str i) "true") eqn:Et.
    + injection H as <-. apply CmpTrue. apply String.eqb_eq; exact Et.
    + destruct (String.eqb (ident_str i) "false") eqn:Ef.
      * injection H as <-. apply CmpFalse. apply String.eqb_eq; exact Ef.
      * discriminate.
  - destruct (bool_sumbool (Z.of_N n <=? int_max)) as [Hle|Hle].
    + injection H as <-. apply CmpInt.
    + discriminate.
  - destruct (bool_sumbool (Z.of_N n <=? - int_min)) as [Hle|Hle].
    + injection H as <-. apply CmpNeg.
    + discriminate.
  - injection H as <-. apply CmpStr.
Qed.

Lemma compile_exprs_sound : forall es cs, compile_exprs es = Some cs -> Forall2 CompilesExpr es cs.
Proof.
  induction es as [ | e es' IH ]; intros cs H; simpl in H.
  - injection H as <-. constructor.
  - destruct (compile_expr e) as [ce|] eqn:E1; [ | discriminate ].
    destruct (compile_exprs es') as [ces|] eqn:E2; [ | discriminate ].
    injection H as <-. constructor.
    + apply compile_expr_sound; exact E1.
    + apply IH; reflexivity.   (* [destruct ... eqn] rewrote [compile_exprs es'] inside IH to [Some ces] *)
Qed.

Lemma compile_stmt_sound : forall s c, compile_stmt s = Some c -> CompilesStmt s c.
Proof.
  intros [callee args] c H. simpl in H. rewrite andb_true_r in H.  (* target provides println *)
  destruct (String.eqb (ident_str callee) "println") eqn:Ec; [ | discriminate ].
  destruct (compile_exprs args) as [ces|] eqn:E; [ | discriminate ].
  injection H as <-.
  apply String.eqb_eq in Ec.
  apply CmpCall; [ exact Ec | apply println_supported | apply compile_exprs_sound; exact E ].
Qed.

Lemma compile_stmts_sound : forall ss cs, compile_stmts ss = Some cs -> Forall2 CompilesStmt ss cs.
Proof.
  induction ss as [ | s ss' IH ]; intros cs H; simpl in H.
  - injection H as <-. constructor.
  - destruct (compile_stmt s) as [ce|] eqn:E1; [ | discriminate ].
    destruct (compile_stmts ss') as [ces|] eqn:E2; [ | discriminate ].
    injection H as <-. constructor.
    + apply compile_stmt_sound; exact E1.
    + apply IH; reflexivity.   (* [destruct ... eqn] rewrote [compile_stmts ss'] inside IH to [Some ces] *)
Qed.

Theorem go_compile_sound : forall raw c, go_compile raw = Some c -> CompilesFile raw c.
Proof.
  intros raw c H. unfold go_compile in H.
  destruct (String.eqb (ident_str (file_pkg raw)) "main"
            && String.eqb (ident_str (fn_name (file_func raw))) "main") eqn:Eg;
    [ | discriminate ].
  destruct (compile_stmts (fn_body (file_func raw))) as [b|] eqn:E; [ | discriminate ].
  injection H as <-.
  apply andb_true_iff in Eg as [Hp Hf]. apply String.eqb_eq in Hp. apply String.eqb_eq in Hf.
  apply CmpFile; [ exact Hp | exact Hf | apply compile_stmts_sound; exact E ].
Qed.

(** ---- Completeness: every genuine compilation is found by the elaborator ---- *)

Lemma compile_expr_complete : forall e c, CompilesExpr e c -> compile_expr e = Some c.
Proof.
  intros e c H. destruct H; cbn [compile_expr].
  - rewrite H. reflexivity.                                     (* true  *)
  - rewrite H. reflexivity.                                     (* false: eqb "false" "true" = false, then = "false" *)
  - destruct (bool_sumbool (Z.of_N n <=? int_max)) as [H'|H'].
    + f_equal. f_equal. apply UIP_dec, Bool.bool_dec.
    + rewrite H in H'; discriminate.
  - destruct (bool_sumbool (Z.of_N n <=? - int_min)) as [H'|H'].
    + f_equal. f_equal. apply UIP_dec, Bool.bool_dec.
    + rewrite H in H'; discriminate.
  - reflexivity.
Qed.

Lemma compile_exprs_complete : forall es cs, Forall2 CompilesExpr es cs -> compile_exprs es = Some cs.
Proof.
  intros es cs H; induction H as [ | e c es' cs' Hec Hrest IH ]; simpl.
  - reflexivity.
  - rewrite (compile_expr_complete _ _ Hec), IH. reflexivity.
Qed.

Lemma compile_stmt_complete : forall s c, CompilesStmt s c -> compile_stmt s = Some c.
Proof.
  intros s c H. destruct H as [ callee args cargs Hc Hp HF ]. simpl. rewrite andb_true_r.
  rewrite (proj2 (String.eqb_eq _ _) Hc).
  rewrite (compile_exprs_complete _ _ HF). reflexivity.
Qed.

Lemma compile_stmts_complete : forall ss cs, Forall2 CompilesStmt ss cs -> compile_stmts ss = Some cs.
Proof.
  intros ss cs H; induction H as [ | s c ss' cs' Hsc Hrest IH ]; simpl.
  - reflexivity.
  - rewrite (compile_stmt_complete _ _ Hsc), IH. reflexivity.
Qed.

Theorem go_compile_complete : forall raw c, CompilesFile raw c -> go_compile raw = Some c.
Proof.
  intros raw c H. destruct H as [ raw0 cbody Hp Hf HF ]. unfold go_compile.
  rewrite (proj2 (String.eqb_eq _ _) Hp), (proj2 (String.eqb_eq _ _) Hf). simpl.
  rewrite (compile_stmts_complete _ _ HF). reflexivity.
Qed.

Corollary go_compile_iff : forall raw c, go_compile raw = Some c <-> CompilesFile raw c.
Proof. intros raw c. split; [ apply go_compile_sound | apply go_compile_complete ]. Qed.

(** ---- Determinism: a raw program has at most one compilation ---- *)

Lemma Forall2_det : forall (A B : Type) (R : A -> B -> Prop),
  (forall a b1 b2, R a b1 -> R a b2 -> b1 = b2) ->
  forall l l1 l2, Forall2 R l l1 -> Forall2 R l l2 -> l1 = l2.
Proof.
  intros A B R Hfun l l1 l2 H1; revert l2.
  induction H1 as [ | x y l0 l1' Hxy Hrest IH ]; intros l2 H2; inversion H2; subst.
  - reflexivity.
  - f_equal; [ eapply Hfun; eauto | eapply IH; eauto ].
Qed.

Lemma CompilesExpr_det : forall e c1 c2, CompilesExpr e c1 -> CompilesExpr e c2 -> c1 = c2.
Proof.
  intros e c1 c2 H1 H2. destruct e as [ i | n | n | s Hs ].
  - inversion H1; subst; inversion H2; subst; try reflexivity; exfalso; congruence.
  - inversion H1; subst; inversion H2; subst. f_equal. apply UIP_dec, Bool.bool_dec.
  - inversion H1; subst; inversion H2; subst. f_equal. apply UIP_dec, Bool.bool_dec.
  - inversion H1; subst; inversion H2; subst. f_equal. apply UIP_dec, Bool.bool_dec.
Qed.

Lemma CompilesStmt_det : forall s c1 c2, CompilesStmt s c1 -> CompilesStmt s c2 -> c1 = c2.
Proof.
  intros s c1 c2 H1 H2. inversion H1; subst; inversion H2; subst.
  f_equal. eapply Forall2_det; [ apply CompilesExpr_det | eassumption | eassumption ].
Qed.

Theorem CompilesFile_det : forall raw c1 c2, CompilesFile raw c1 -> CompilesFile raw c2 -> c1 = c2.
Proof.
  intros raw c1 c2 H1 H2. inversion H1; subst; inversion H2; subst.
  f_equal. eapply Forall2_det; [ apply CompilesStmt_det | eassumption | eassumption ].
Qed.

(** ---- Erasure: the decorated tree projects back to exactly the raw tree ---- *)

Lemma ok_true    : go_ident_ok "true"    = true. Proof. reflexivity. Qed.
Lemma ok_false   : go_ident_ok "false"   = true. Proof. reflexivity. Qed.
Lemma ok_println : go_ident_ok "println" = true. Proof. reflexivity. Qed.
Lemma ok_main    : go_ident_ok "main"    = true. Proof. reflexivity. Qed.

Definition true_ident    : GoIdent := mkGoIdent "true"    ok_true.
Definition false_ident   : GoIdent := mkGoIdent "false"   ok_false.
Definition println_ident : GoIdent := mkGoIdent "println" ok_println.
Definition main_ident    : GoIdent := mkGoIdent "main"    ok_main.

Definition erase_expr (c : CompiledExpr) : GoExpr :=
  match c with
  | CBool true  => EIdent true_ident
  | CBool false => EIdent false_ident
  | CInt n _ => EInt n
  | CNeg n _ => ENeg n
  | CStr s H => EStr s H
  end.

Definition erase_stmt (c : CompiledStmt) : GoStmt :=
  match c with
  | CPrintln cargs => SCall println_ident (map erase_expr cargs)
  end.

Definition erase_file (c : CompiledFile) : GoFile :=
  mkGoFile main_ident (mkGoFunc main_ident (map erase_stmt (cf_body c))).

Lemma erase_expr_faithful : forall e c, CompilesExpr e c -> erase_expr c = e.
Proof.
  intros e c H. destruct H; simpl.
  - f_equal. apply goident_payload_eq. rewrite H. reflexivity.
  - f_equal. apply goident_payload_eq. rewrite H. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma erase_exprs_faithful : forall es cs, Forall2 CompilesExpr es cs -> map erase_expr cs = es.
Proof.
  intros es cs H; induction H as [ | e c es' cs' Hec Hrest IH ]; simpl.
  - reflexivity.
  - rewrite (erase_expr_faithful _ _ Hec), IH. reflexivity.
Qed.

Lemma erase_stmt_faithful : forall s c, CompilesStmt s c -> erase_stmt c = s.
Proof.
  intros s c H. destruct H as [ callee args cargs Hc Hp HF ]. simpl.
  f_equal.
  - apply goident_payload_eq. rewrite Hc. reflexivity.
  - apply erase_exprs_faithful; exact HF.
Qed.

Lemma erase_stmts_faithful : forall ss cs, Forall2 CompilesStmt ss cs -> map erase_stmt cs = ss.
Proof.
  intros ss cs H; induction H as [ | s c ss' cs' Hsc Hrest IH ]; simpl.
  - reflexivity.
  - rewrite (erase_stmt_faithful _ _ Hsc), IH. reflexivity.
Qed.

Theorem compiled_erases_to_raw : forall raw c, CompilesFile raw c -> erase_file c = raw.
Proof.
  intros raw c H. destruct H as [ raw0 cbody Hp Hf HF ].
  destruct raw0 as [ pkg [ fn body ] ]. simpl in Hp, Hf, HF.
  unfold erase_file. simpl. f_equal.
  - apply goident_payload_eq. rewrite Hp. reflexivity.
  - f_equal.
    + apply goident_payload_eq. rewrite Hf. reflexivity.
    + apply erase_stmts_faithful; exact HF.
Qed.

(** GoCompile is decidable — the elaborator decides it. *)
Corollary GoCompile_dec : forall raw, {GoCompile raw} + {~ GoCompile raw}.
Proof.
  intro raw. destruct (go_compile raw) as [c|] eqn:E.
  - left. exists c. apply go_compile_sound; exact E.
  - right. intros [c Hc]. apply go_compile_complete in Hc. rewrite Hc in E; discriminate.
Qed.
