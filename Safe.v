From Fido Require Import Syntax Compilable.

(* Trivial today, because the fragment has no unsafe operation; this is the permanent extension point. *)
Definition Property (cp : Compilable.Program) : Prop := True.

(* The representation and its constructor stay inside, so [certify] is the only way a program exists. *)
Module Type CERTIFICATE.
  Parameter Program : Type.
  Parameter compiled : Program -> Compilable.Program.
  Parameter certify : forall cp : Compilable.Program, Property cp -> Program.
  Parameter certify_retains : forall cp (H : Property cp), compiled (certify cp H) = cp.
End CERTIFICATE.

Module Certificate : CERTIFICATE.
  Record ProgramRepresentation : Type := Make {
    compiled : Compilable.Program;
    proof     : Property compiled
  }.
  Definition Program : Type := ProgramRepresentation.
  (* certify is proof-taking: a certificate carries the exact compiled program AND the proof of its safety property *)
  Definition certify (cp : Compilable.Program) (H : Property cp) : Program := Make cp H.
  Lemma certify_retains : forall cp (H : Property cp), compiled (certify cp H) = cp.
  Proof. reflexivity. Qed.
End Certificate.
Include Certificate.

(* The certified source: [Emit] reaches it via this projection, then [Render] traverses that raw [Syntax] directly. *)
Definition source (sp : Program) : Syntax.Program := Compilable.source (compiled sp).

(* Safety wraps the capability, so a certified program retains the exact core that justified it. *)
Definition core (sp : Program) : Compilable.Core (source sp) := Compilable.core (compiled sp).

(* The certified program's source is the capability's, propositionally since [certify] is opaque. *)
Theorem certify_source : forall cp (H : Property cp), source (certify cp H) = Compilable.source cp.
Proof. intros cp H. unfold source. rewrite certify_retains. reflexivity. Qed.

Theorem certify_retains_capability : forall cp (H : Property cp), compiled (certify cp H) = cp.
Proof. exact certify_retains. Qed.

(* Retention over any certificate, not only a freshly certified one, and so strictly stronger. *)
Theorem certify_retains_core : forall sp, core sp = Compilable.core (compiled sp).
Proof. reflexivity. Qed.
