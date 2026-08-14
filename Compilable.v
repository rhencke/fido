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

  (* the accepted-program payload Safe retains: the exact source, its decided core, and the compiled evidence *)
  Parameter Program : Type.
  Parameter source   : Program -> Syntax.Program.
  Parameter core     : forall pr : Program, Core (source pr).
  Parameter accepted : forall pr : Program, core_diagnostics (core pr) = [].
  Parameter in_scope : forall pr : Program, core_boundaries (core pr) = [].

  (* adequacy: the retained decided core's reports ARE the source-level reports, read off the same object *)
  Parameter decided_diagnostics : forall p, core_diagnostics (decided_core (compile p)) = all_diags p.
  Parameter decided_boundaries  : forall p, core_boundaries (decided_core (compile p)) = all_boundaries p.

  (* an admissible program yields its accepted payload by eliminating the real decision, retaining its core *)
  Parameter program_of : forall (p : Syntax.Program), Admissible p -> Program.
  Parameter program_of_source : forall (p : Syntax.Program) (H : Admissible p), source (program_of p H) = p.
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

  Record ProgramRep : Type := MkProgram {
    prog_src  : Syntax.Program;
    prog_core : Core prog_src;
    prog_ok   : CompiledAt prog_src prog_core
  }.
  Definition Program := ProgramRep.
  Definition source (pr : Program) : Syntax.Program := prog_src pr.
  Definition core (pr : Program) : Core (source pr) := prog_core pr.
  Definition accepted (pr : Program) : core_diagnostics (core pr) = [] := c_accepted (prog_ok pr).
  Definition in_scope (pr : Program) : core_boundaries (core pr) = [] := c_in_scope (prog_ok pr).

  (* eliminate the real decision: an admissible program's verdict is Compiled, so retain its exact core+payload *)
  Definition compiled_of (p : Syntax.Program) (H : Admissible p) : { pr : Program | source pr = p } :=
    match verdict (compile p) with
    | Compiled _ _ payload =>
        exist _ (MkProgram p (decided_core (compile p)) payload) eq_refl
    | Rejected _ _ payload =>
        False_rect _ (r_rejected payload (eq_trans (decided_diagnostics p) (proj1 H)))
    | OutsideScope _ _ payload =>
        False_rect _ (o_blocked payload (eq_trans (decided_boundaries p) (proj2 H)))
    end.
  Definition program_of (p : Syntax.Program) (H : Admissible p) : Program := proj1_sig (compiled_of p H).
  Definition program_of_source (p : Syntax.Program) (H : Admissible p) : source (program_of p H) = p :=
    proj2_sig (compiled_of p H).
End Capability.
Include Capability.
Arguments Compiled {p c} _. Arguments Rejected {p c} _. Arguments OutsideScope {p c} _.

(* the two exact verdict predicates a control asserts, read from the decision's verdict branch. *)
Definition compiles (p : Syntax.Program) : Prop :=
  match verdict (compile p) with Compiled _ => True | _ => False end.
Definition rejects (p : Syntax.Program) : Prop :=
  match verdict (compile p) with Rejected _ => True | _ => False end.

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
