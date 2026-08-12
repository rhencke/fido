(* Compilable — the static semantic phase and the permanent three-way Compiled/Rejected/OutsideScope decision. *)

From Stdlib Require Import List Bool String Ascii ZArith NArith Lia.
From Fido Require Import Collections FilePath ModulePath Version Names Integer Float Complex Syntax Index Compilable.TypeResolution Compilable.Bindings Compilable.Report Compilable.Facts.
Import ListNotations.

(* The core and the three verdict payloads are sealed behind CAPABILITY; the only way to one is compile. *)
Definition Admissible (p : Syntax.Program) : Prop := all_diags p = [] /\ all_boundaries p = [].

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

Module Type CAPABILITY.
  Parameter Core : Syntax.Program -> Type.
  Parameter core_diagnostics : forall {p}, Core p -> list RootCause.
  Parameter core_boundaries  : forall {p}, Core p -> list Boundary.

  Parameter Program : Type.
  Parameter source   : Program -> Syntax.Program.
  Parameter core     : forall cp : Program, Core (source cp).
  Parameter accepted : forall cp : Program, core_diagnostics (core cp) = [].
  Parameter in_scope : forall cp : Program, core_boundaries (core cp) = [].
  (* positive exact-object identity: the retained core IS the exact source elaboration, no rerun, no factory *)
  Parameter core_source_exact : forall cp : Program,
    core_diagnostics (core cp) = all_diags (source cp) /\ core_boundaries (core cp) = all_boundaries (source cp).

  Parameter Failure : Syntax.Program -> Type.
  Parameter failure_core : forall {p}, Failure p -> Core p.
  Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> [].
  Parameter failure_core_exact : forall p (f : Failure p),
    core_diagnostics (failure_core f) = all_diags p /\ core_boundaries (failure_core f) = all_boundaries p.

  Parameter Outside_ : Syntax.Program -> Type.
  Parameter outside_core    : forall {p}, Outside_ p -> Core p.
  Parameter outside_clean   : forall {p} (o : Outside_ p), core_diagnostics (outside_core o) = [].
  Parameter outside_blocked : forall {p} (o : Outside_ p), core_boundaries (outside_core o) <> [].
  Parameter outside_core_exact : forall p (o : Outside_ p),
    core_diagnostics (outside_core o) = all_diags p /\ core_boundaries (outside_core o) = all_boundaries p.

  Inductive Outcome (p : Syntax.Program) : Type :=
  | Compiled (cp : Program) (Hcp : source cp = p)
  | Rejected (f : Failure p)
  | OutsideScope (o : Outside_ p).

  Parameter compile : forall p : Syntax.Program, Outcome p.
  (* branch bridges: a client reads compile's verdict from the transparent reports, never the sealed capability *)
  Parameter compiled_diagnostics : forall p cp H, compile p = Compiled p cp H -> all_diags p = [].
  Parameter compiled_boundaries  : forall p cp H, compile p = Compiled p cp H -> all_boundaries p = [].
  Parameter rejected_diagnostics : forall p f, compile p = Rejected p f -> all_diags p <> [].
  Parameter outside_diagnostics  : forall p o, compile p = OutsideScope p o -> all_diags p = [].
  Parameter outside_boundaries   : forall p o, compile p = OutsideScope p o -> all_boundaries p <> [].
End CAPABILITY.

Module Capability : CAPABILITY.
  (* the retained elaborated object: one static pass's diagnostics and boundaries; every verdict reads it, no rerun *)
  Record CoreRep (p : Syntax.Program) : Type := MkCore {
    core_diagnostics : list RootCause;
    core_boundaries  : list Boundary
  }.
  Arguments core_diagnostics {p}. Arguments core_boundaries {p}.
  Definition Core := CoreRep.
  Definition elaborate (p : Syntax.Program) : Core p :=
    MkCore p (all_diags p) (all_boundaries p).
  Lemma elaborate_diagnostics : forall p, core_diagnostics (elaborate p) = all_diags p. Proof. reflexivity. Qed.
  Lemma elaborate_boundaries  : forall p, core_boundaries (elaborate p) = all_boundaries p. Proof. reflexivity. Qed.

  (* each verdict keeps the source and its proofs; core is the projection [elaborate source], no stored peer Core *)
  Record ProgramRep : Type := MkProg {
    prog_source   : Syntax.Program;
    prog_accepted : all_diags prog_source = [];
    prog_in_scope : all_boundaries prog_source = []
  }.
  Definition Program := ProgramRep.
  Definition source (cp : Program) : Syntax.Program := prog_source cp.
  Definition core (cp : Program) : Core (source cp) := elaborate (source cp).
  Definition accepted (cp : Program) : core_diagnostics (core cp) = [] := prog_accepted cp.
  Definition in_scope (cp : Program) : core_boundaries (core cp) = [] := prog_in_scope cp.
  Lemma core_source_exact : forall cp : Program,
    core_diagnostics (core cp) = all_diags (source cp) /\ core_boundaries (core cp) = all_boundaries (source cp).
  Proof. intro cp. split; reflexivity. Qed.

  Record FailureRep (p : Syntax.Program) : Type := MkFail {
    fail_rejected : all_diags p <> []
  }.
  Arguments fail_rejected {p}.
  Definition Failure := FailureRep.
  Definition failure_core {p} (f : Failure p) : Core p := elaborate p.
  Definition rejected {p} (f : Failure p) : core_diagnostics (failure_core f) <> [] := fail_rejected f.
  Lemma failure_core_exact : forall p (f : Failure p),
    core_diagnostics (failure_core f) = all_diags p /\ core_boundaries (failure_core f) = all_boundaries p.
  Proof. intros p f. split; reflexivity. Qed.

  Record OutsideRep (p : Syntax.Program) : Type := MkOut {
    out_clean   : all_diags p = [];
    out_blocked : all_boundaries p <> []
  }.
  Arguments out_clean {p}. Arguments out_blocked {p}.
  Definition Outside_ := OutsideRep.
  Definition outside_core {p} (o : Outside_ p) : Core p := elaborate p.
  Definition outside_clean {p} (o : Outside_ p) : core_diagnostics (outside_core o) = [] := out_clean o.
  Definition outside_blocked {p} (o : Outside_ p) : core_boundaries (outside_core o) <> [] := out_blocked o.
  Lemma outside_core_exact : forall p (o : Outside_ p),
    core_diagnostics (outside_core o) = all_diags p /\ core_boundaries (outside_core o) = all_boundaries p.
  Proof. intros p o. split; reflexivity. Qed.

  Inductive Outcome (p : Syntax.Program) : Type :=
  | Compiled (cp : Program) (Hcp : source cp = p)
  | Rejected (f : Failure p)
  | OutsideScope (o : Outside_ p).

  (* one elaboration decides the branch from its own reports; verdicts keep the source, the core is a projection *)
  Definition compile (p : Syntax.Program) : Outcome p :=
    let c := elaborate p in
    match nil_dec (core_diagnostics c) with
    | left Hd =>
        match nil_dec (core_boundaries c) with
        | left Hb  => Compiled p (MkProg p Hd Hb) eq_refl
        | right Hb => OutsideScope p (MkOut p Hd Hb)
        end
    | right Hd => Rejected p (MkFail p Hd)
    end.

  Lemma compiled_diagnostics : forall p cp H, compile p = Compiled p cp H -> all_diags p = [].
  Proof.
    intros p cp H Hc. unfold compile in Hc. cbv zeta in Hc.
    destruct (nil_dec (core_diagnostics (elaborate p))) as [Hd|Hd];
      [rewrite <- elaborate_diagnostics; exact Hd | discriminate Hc].
  Qed.
  Lemma compiled_boundaries : forall p cp H, compile p = Compiled p cp H -> all_boundaries p = [].
  Proof.
    intros p cp H Hc. unfold compile in Hc. cbv zeta in Hc.
    destruct (nil_dec (core_diagnostics (elaborate p))) as [Hd|Hd]; [|discriminate Hc].
    destruct (nil_dec (core_boundaries (elaborate p))) as [Hb|Hb];
      [rewrite <- elaborate_boundaries; exact Hb | discriminate Hc].
  Qed.
  Lemma rejected_diagnostics : forall p f, compile p = Rejected p f -> all_diags p <> [].
  Proof.
    intros p f Hc. unfold compile in Hc. cbv zeta in Hc.
    destruct (nil_dec (core_diagnostics (elaborate p))) as [Hd|Hd];
      [destruct (nil_dec (core_boundaries (elaborate p))); discriminate Hc
      | rewrite <- elaborate_diagnostics; exact Hd].
  Qed.
  Lemma outside_diagnostics : forall p o, compile p = OutsideScope p o -> all_diags p = [].
  Proof.
    intros p o Hc. unfold compile in Hc. cbv zeta in Hc.
    destruct (nil_dec (core_diagnostics (elaborate p))) as [Hd|Hd];
      [rewrite <- elaborate_diagnostics; exact Hd | discriminate Hc].
  Qed.
  Lemma outside_boundaries : forall p o, compile p = OutsideScope p o -> all_boundaries p <> [].
  Proof.
    intros p o Hc. unfold compile in Hc. cbv zeta in Hc.
    destruct (nil_dec (core_diagnostics (elaborate p))) as [Hd|Hd]; [|discriminate Hc].
    destruct (nil_dec (core_boundaries (elaborate p))) as [Hb|Hb];
      [discriminate Hc | rewrite <- elaborate_boundaries; exact Hb].
  Qed.
End Capability.
Include Capability.
Arguments Compiled {p} _ _. Arguments Rejected {p} _. Arguments OutsideScope {p} _.

(* extract the exact compiled program and its source identity from admissibility — through compile, no 2nd mint *)
Definition compiled_of (p : Syntax.Program) (H : Admissible p) : { cp : Program | source cp = p } :=
  match compile p as o return (compile p = o -> { cp : Program | source cp = p }) with
  | Compiled cp Hcp => fun _  => exist _ cp Hcp
  | Rejected f      => fun Hc => False_rect _ (rejected_diagnostics p f Hc (proj1 H))
  | OutsideScope o  => fun Hc => False_rect _ (outside_boundaries p o Hc (proj2 H))
  end eq_refl.
Definition program_of (p : Syntax.Program) (H : Admissible p) : Program := proj1_sig (compiled_of p H).
Definition program_of_source (p : Syntax.Program) (H : Admissible p) : source (program_of p H) = p :=
  proj2_sig (compiled_of p H).

(* the two exact verdict predicates a control asserts, decided through compile from the transparent reports *)
Definition compiles (p : Syntax.Program) : Prop := exists cp H, compile p = Compiled cp H.
Definition rejects  (p : Syntax.Program) : Prop := exists f, compile p = Rejected f.

Definition compiles_of_admissible (p : Syntax.Program) (H : Admissible p) : compiles p :=
  match compile p as o return (compile p = o -> compiles p) with
  | Compiled cp Hcp => fun Hc => ex_intro _ cp (ex_intro _ Hcp Hc)
  | Rejected f      => fun Hc => False_rect _ (rejected_diagnostics p f Hc (proj1 H))
  | OutsideScope o  => fun Hc => False_rect _ (outside_boundaries p o Hc (proj2 H))
  end eq_refl.
Definition rejects_of_diags (p : Syntax.Program) (Hd : all_diags p <> []) : rejects p :=
  match compile p as o return (compile p = o -> rejects p) with
  | Compiled cp Hcp => fun Hc => False_rect _ (Hd (compiled_diagnostics p cp Hcp Hc))
  | Rejected f      => fun Hc => ex_intro _ f Hc
  | OutsideScope o  => fun Hc => False_rect _ (Hd (outside_diagnostics p o Hc))
  end eq_refl.
