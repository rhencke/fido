From Fido Require Import Syntax Compilable.

(* Trivially True today: the fragment has no unsafe operation, and this is the permanent safety extension point. *)
Definition Property {p} {c : Compilable.Compilation p} (_ : Compilable.Prog.Program c) : Prop := True.

(* Primitive projections so reading a certificate's source never co-normalizes the retained heavy phases. *)
#[projections(primitive)]
Record Program : Type := certify {
  safe_src     : Syntax.Program ;
  safe_dec     : Compilable.Decision safe_src ;
  safe_comp    : Compilable.Compilation safe_src ;
  safe_payload : Compilable.CompiledPayload safe_dec safe_comp ;
  safe_ok      : Property (Compilable.Prog.compiled_prog safe_payload)
}.

(* The certified source: [Emit] reaches it via this projection, then [Render] traverses that raw [Syntax]. *)
Definition source (sp : Program) : Syntax.Program := safe_src sp.

(* Retention: the stored decision, compilation, and compiled payload are exactly those supplied, by projection. *)
Theorem safe_retains_program :
  forall src dec comp cp ok,
    safe_dec (certify src dec comp cp ok) = dec
    /\ safe_comp (certify src dec comp cp ok) = comp
    /\ safe_payload (certify src dec comp cp ok) = cp.
Proof. intros; repeat split; reflexivity. Qed.
