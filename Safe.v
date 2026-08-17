From Fido Require Import Syntax Compilable.

(* Trivially True today: the fragment has no unsafe operation, and this is the permanent safety extension point. *)
Definition Property {p} {c : Compilable.Compilation p} (_ : Compilable.Prog.Program c) : Prop := True.

(* Primitive projections so reading a certificate's source never co-normalizes the retained heavy phases. *)
#[projections(primitive)]
Record Program : Type := certify {
  safe_src  : Syntax.Program ;
  safe_comp : Compilable.Compilation safe_src ;
  safe_prog : Compilable.Prog.Program safe_comp ;
  safe_ok   : Property safe_prog
}.

(* The certified source: [Emit] reaches it via this projection, then [Render] traverses that raw [Syntax]. *)
Definition source (sp : Program) : Syntax.Program := safe_src sp.

(* Retention: the stored compilation and capability are exactly those supplied, recovered by projection. *)
Theorem safe_retains_program :
  forall src comp prog ok,
    safe_comp (certify src comp prog ok) = comp /\ safe_prog (certify src comp prog ok) = prog.
Proof. intros; split; reflexivity. Qed.
