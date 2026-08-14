(* Compilable — the static semantic phase and the permanent three-way Compiled/Rejected/OutsideScope decision. *)

From Stdlib Require Import List Bool String Ascii ZArith NArith Lia.
From Fido Require Import Collections FilePath ModulePath Version Names Integer Float Complex Syntax Index Compilable.TypeResolution Compilable.Bindings Compilable.Report Compilable.Facts.
Import ListNotations.

(* compile returns one Decision: the exact decided core, then a verdict that is a fact about that same core. *)
Definition Admissible (p : Syntax.Program) : Prop := all_diags p = [] /\ all_boundaries p = [].

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

Module Type CAPABILITY.
  Parameter Core : Syntax.Program -> Type.
  Parameter core_diagnostics : forall {p}, Core p -> list RootCause.
  Parameter core_boundaries  : forall {p}, Core p -> list Boundary.

  (* each branch payload is indexed by the exact program p and the exact decided core c, and states a fact about c *)
  Parameter CompiledAt : forall (p : Syntax.Program), Core p -> Type.
  Parameter c_accepted : forall {p} {c : Core p}, CompiledAt p c -> core_diagnostics c = [].
  Parameter c_in_scope : forall {p} {c : Core p}, CompiledAt p c -> core_boundaries c = [].
  Parameter RejectedAt : forall (p : Syntax.Program), Core p -> Type.
  Parameter r_rejected : forall {p} {c : Core p}, RejectedAt p c -> core_diagnostics c <> [].
  Parameter OutsideAt : forall (p : Syntax.Program), Core p -> Type.
  Parameter o_clean   : forall {p} {c : Core p}, OutsideAt p c -> core_diagnostics c = [].
  Parameter o_blocked : forall {p} {c : Core p}, OutsideAt p c -> core_boundaries c <> [].

  Inductive Verdict (p : Syntax.Program) (c : Core p) : Type :=
  | Compiled     (payload : CompiledAt p c)
  | Rejected     (payload : RejectedAt p c)
  | OutsideScope (payload : OutsideAt p c).

  (* the public decision object: one decided core, and a verdict a client reads over that very core *)
  Parameter Decision : Syntax.Program -> Type.
  Parameter decided_core : forall {p}, Decision p -> Core p.
  Parameter verdict : forall {p} (d : Decision p), Verdict p (decided_core d).

  Parameter compile : forall p : Syntax.Program, Decision p.

  (* adequacy: the retained decided core's reports ARE the source-level reports, read off the same object *)
  Parameter decided_diagnostics : forall p, core_diagnostics (decided_core (compile p)) = all_diags p.
  Parameter decided_boundaries  : forall p, core_boundaries (decided_core (compile p)) = all_boundaries p.
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
    let ph := elaborate_phase p in MkCore p (fst ph) (snd ph).
  Lemma elaborate_diagnostics : forall p, core_diagnostics (elaborate p) = all_diags p. Proof. reflexivity. Qed.
  Lemma elaborate_boundaries  : forall p, core_boundaries (elaborate p) = all_boundaries p. Proof. reflexivity. Qed.

  Record CompiledRep (p : Syntax.Program) (c : Core p) : Type := MkCompiled {
    c_accepted : core_diagnostics c = [];
    c_in_scope : core_boundaries c = []
  }.
  Arguments c_accepted {p c}. Arguments c_in_scope {p c}.
  Definition CompiledAt := CompiledRep.
  Record RejectedRep (p : Syntax.Program) (c : Core p) : Type := MkRejected {
    r_rejected : core_diagnostics c <> []
  }.
  Arguments r_rejected {p c}.
  Definition RejectedAt := RejectedRep.
  Record OutsideRep (p : Syntax.Program) (c : Core p) : Type := MkOutside {
    o_clean   : core_diagnostics c = [];
    o_blocked : core_boundaries c <> []
  }.
  Arguments o_clean {p c}. Arguments o_blocked {p c}.
  Definition OutsideAt := OutsideRep.

  Inductive Verdict (p : Syntax.Program) (c : Core p) : Type :=
  | Compiled     (payload : CompiledAt p c)
  | Rejected     (payload : RejectedAt p c)
  | OutsideScope (payload : OutsideAt p c).

  Record DecisionRep (p : Syntax.Program) : Type := MkDecision {
    decided_core : Core p;
    verdict : Verdict p decided_core
  }.
  Arguments decided_core {p}. Arguments verdict {p}.
  Definition Decision := DecisionRep.

  (* one elaboration, retained as [c]; the verdict is chosen from [c]'s own reports and indexed by that same [c] *)
  Definition compile (p : Syntax.Program) : Decision p :=
    let c := elaborate p in
    MkDecision p c
      match nil_dec (core_diagnostics c) with
      | left Hd =>
          match nil_dec (core_boundaries c) with
          | left Hb  => Compiled p c (MkCompiled p c Hd Hb)
          | right Hb => OutsideScope p c (MkOutside p c Hd Hb)
          end
      | right Hd => Rejected p c (MkRejected p c Hd)
      end.

  Lemma decided_diagnostics : forall p, core_diagnostics (decided_core (compile p)) = all_diags p.
  Proof. reflexivity. Qed.
  Lemma decided_boundaries  : forall p, core_boundaries (decided_core (compile p)) = all_boundaries p.
  Proof. reflexivity. Qed.

End Capability.
Include Capability.
Arguments Compiled {p c} _. Arguments Rejected {p c} _. Arguments OutsideScope {p c} _.

(* the accepted program: a transparent carrier of the exact retained source, decided core and compiled evidence *)
Record Program : Type := MkProgram {
  prog_src  : Syntax.Program;
  prog_core : Core prog_src;
  prog_ok   : CompiledAt prog_src prog_core
}.
Definition source (pr : Program) : Syntax.Program := prog_src pr.
Definition core (pr : Program) : Core (source pr) := prog_core pr.
Definition accepted (pr : Program) : core_diagnostics (core pr) = [] := c_accepted (prog_ok pr).
Definition in_scope (pr : Program) : core_boundaries (core pr) = [] := c_in_scope (prog_ok pr).

(* the two exact verdict predicates a control asserts, read from the decision's verdict branch. *)
Definition compiles (p : Syntax.Program) : Prop :=
  match verdict (compile p) with Compiled _ => True | _ => False end.
Definition rejects (p : Syntax.Program) : Prop :=
  match verdict (compile p) with Rejected _ => True | _ => False end.
Definition outsides (p : Syntax.Program) : Prop :=
  match verdict (compile p) with OutsideScope _ => True | _ => False end.

(* the payload of the Compiled branch, retained as the accepted program's compiled evidence *)
Definition compiled_payload (p : Syntax.Program) (H : compiles p) : CompiledAt p (decided_core (compile p)) :=
  match verdict (compile p) as v
    return (match v with Compiled _ => True | _ => False end) -> CompiledAt p (decided_core (compile p)) with
  | Compiled payload => fun _ => payload
  | Rejected _ => fun H0 => False_rect _ H0
  | OutsideScope _ => fun H0 => False_rect _ H0
  end H.

(* the compiled decision mints its accepted program with prog_src set directly, so source computes past the seal *)
Definition program_of_compiled (p : Syntax.Program) (H : compiles p) : Program :=
  MkProgram p (decided_core (compile p)) (compiled_payload p H).

Definition compiles_of_admissible (p : Syntax.Program) (H : Admissible p) : compiles p :=
  match verdict (compile p) as v return (match v with Compiled _ => True | _ => False end) with
  | Compiled _ => I
  | Rejected payload => r_rejected payload (eq_trans (decided_diagnostics p) (proj1 H))
  | OutsideScope payload => o_blocked payload (eq_trans (decided_boundaries p) (proj2 H))
  end.
Definition rejects_of_diags (p : Syntax.Program) (Hd : all_diags p <> []) : rejects p :=
  match verdict (compile p) as v return (match v with Rejected _ => True | _ => False end) with
  | Compiled payload => False_rect _ (Hd (eq_trans (eq_sym (decided_diagnostics p)) (c_accepted payload)))
  | Rejected _ => I
  | OutsideScope payload => False_rect _ (Hd (eq_trans (eq_sym (decided_diagnostics p)) (o_clean payload)))
  end.
Definition outsides_of_boundaries (p : Syntax.Program) (Hd : all_diags p = []) (Hb : all_boundaries p <> []) : outsides p :=
  match verdict (compile p) as v return (match v with OutsideScope _ => True | _ => False end) with
  | Compiled payload => False_rect _ (Hb (eq_trans (eq_sym (decided_boundaries p)) (c_in_scope payload)))
  | Rejected payload => False_rect _ (r_rejected payload (eq_trans (decided_diagnostics p) Hd))
  | OutsideScope _ => I
  end.

(* compiled soundness: a program that compiles has empty source-level diagnostics and boundaries *)
Definition admissible_of_compiles (p : Syntax.Program) (H : compiles p) : Admissible p :=
  match verdict (compile p) as v
    return (match v with Compiled _ => True | _ => False end) -> Admissible p with
  | Compiled payload => fun _ =>
      conj (eq_trans (eq_sym (decided_diagnostics p)) (c_accepted payload))
           (eq_trans (eq_sym (decided_boundaries p)) (c_in_scope payload))
  | Rejected _ => fun H0 => False_rect _ H0
  | OutsideScope _ => fun H0 => False_rect _ H0
  end H.
(* soundness and completeness together: a program compiles exactly when it is admissible *)
Definition accepted_iff_admissible (p : Syntax.Program) : compiles p <-> Admissible p :=
  conj (admissible_of_compiles p) (compiles_of_admissible p).

(* exact rejected characterization: a program is Rejected exactly when it has a diagnostic *)
Definition diags_of_rejects (p : Syntax.Program) (H : rejects p) : all_diags p <> [] :=
  match verdict (compile p) as v
    return (match v with Rejected _ => True | _ => False end) -> all_diags p <> [] with
  | Rejected payload => fun _ Hb => r_rejected payload (eq_trans (decided_diagnostics p) Hb)
  | Compiled _ => fun H0 => False_rect _ H0
  | OutsideScope _ => fun H0 => False_rect _ H0
  end H.
Definition rejects_iff_diags (p : Syntax.Program) : rejects p <-> all_diags p <> [] :=
  conj (diags_of_rejects p) (rejects_of_diags p).

(* exact outside characterization: Outside exactly when clean of diagnostics but blocked by a boundary *)
Definition outside_char_of_outsides (p : Syntax.Program) (H : outsides p)
  : all_diags p = [] /\ all_boundaries p <> [] :=
  match verdict (compile p) as v
    return (match v with OutsideScope _ => True | _ => False end) -> (all_diags p = [] /\ all_boundaries p <> []) with
  | OutsideScope payload => fun _ =>
      conj (eq_trans (eq_sym (decided_diagnostics p)) (o_clean payload))
           (fun Hb => o_blocked payload (eq_trans (decided_boundaries p) Hb))
  | Compiled _ => fun H0 => False_rect _ H0
  | Rejected _ => fun H0 => False_rect _ H0
  end H.
Definition outsides_iff (p : Syntax.Program)
  : outsides p <-> (all_diags p = [] /\ all_boundaries p <> []) :=
  conj (outside_char_of_outsides p)
       (fun H => outsides_of_boundaries p (proj1 H) (proj2 H)).

(* branch exhaustiveness: every program is compiled, rejected, or outside scope *)
Definition decision_total (p : Syntax.Program) : compiles p \/ rejects p \/ outsides p :=
  match verdict (compile p) as v
    return (match v with Compiled _ => True | _ => False end)
        \/ (match v with Rejected _ => True | _ => False end)
        \/ (match v with OutsideScope _ => True | _ => False end) with
  | Compiled _ => or_introl I
  | Rejected _ => or_intror (or_introl I)
  | OutsideScope _ => or_intror (or_intror I)
  end.

(* branch exclusivity: the three verdicts are pairwise incompatible *)
Definition compiles_not_rejects (p : Syntax.Program) (Hc : compiles p) : ~ rejects p :=
  match verdict (compile p) as v
    return (match v with Compiled _ => True | _ => False end) -> (match v with Rejected _ => True | _ => False end) -> False with
  | Compiled _ => fun _ Hx => Hx | Rejected _ => fun Hx _ => Hx | OutsideScope _ => fun Hx _ => Hx
  end Hc.
Definition compiles_not_outsides (p : Syntax.Program) (Hc : compiles p) : ~ outsides p :=
  match verdict (compile p) as v
    return (match v with Compiled _ => True | _ => False end) -> (match v with OutsideScope _ => True | _ => False end) -> False with
  | Compiled _ => fun _ Hx => Hx | Rejected _ => fun Hx _ => Hx | OutsideScope _ => fun Hx _ => Hx
  end Hc.
Definition rejects_not_outsides (p : Syntax.Program) (Hr : rejects p) : ~ outsides p :=
  match verdict (compile p) as v
    return (match v with Rejected _ => True | _ => False end) -> (match v with OutsideScope _ => True | _ => False end) -> False with
  | Compiled _ => fun Hx _ => Hx | Rejected _ => fun _ Hx => Hx | OutsideScope _ => fun Hx _ => Hx
  end Hr.

(* exact program identity: the minted program's source and retained core ARE the decision's, by computation *)
Definition program_source (p : Syntax.Program) (H : compiles p) : source (program_of_compiled p H) = p := eq_refl.
Definition program_core (p : Syntax.Program) (H : compiles p) : core (program_of_compiled p H) = decided_core (compile p) := eq_refl.
