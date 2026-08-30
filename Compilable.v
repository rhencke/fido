(* Compilable — the C4 root: compile mints Program/Rejection/Outside, each retaining one sealed Compilation *)

From Stdlib Require Import List Bool.
From Fido Require Import Syntax Compilable.Analysis Compilable.Report.
Import ListNotations.

Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

Inductive Disposition := Compiled | Rejected | OutsideScope.

(* observations computed from the exact SUPPLIED Result, never by opening a certificate or rerunning analyze *)
Definition diagnostics_data {p} (r : AN.Result p) := RP.result_diagnostics r.
Definition boundaries_data {p} (r : AN.Result p) := RP.result_boundaries r.
Definition AdmissibleData {p} (r : AN.Result p) : Prop := diagnostics_data r = [] /\ boundaries_data r = [].

(* the sole branch decision reads emptiness from ONE shared ResultData d, never rebuilding the exact ref lists *)
Definition disposition_from_data {p} (d : AN.ResultData p) : Disposition :=
  if AN.data_diagnostics_empty d
  then (if AN.data_boundaries_empty d then Compiled else OutsideScope)
  else Rejected.
Definition disposition_of {p} (r : AN.Result p) : Disposition := disposition_from_data (AN.data_of_result r).
Definition disposition (p : Syntax.Program) : Disposition := disposition_of (AN.analyze p).

(* the public computation bridge: disposition p is the disposition of the canonical data via the sole mint law *)
Lemma disposition_observe_data (p : Syntax.Program) :
  disposition p = disposition_from_data (AN.result_data p).
Proof. unfold disposition, disposition_of. rewrite AN.analyze_observe_data. reflexivity. Qed.

(* disposition inversion: invert disposition_of over the exact supplied data; assumption-free *)
Lemma disposition_compiled {p} (r : AN.Result p) : disposition_of r = Compiled -> AdmissibleData r.
Proof.
  unfold disposition_of, disposition_from_data, AdmissibleData.
  destruct (AN.data_diagnostics_empty (AN.data_of_result r)) eqn:Hd; [ | discriminate ].
  destruct (AN.data_boundaries_empty (AN.data_of_result r)) eqn:Hb; [ | discriminate ].
  intros _. split.
  - exact (proj1 (AN.data_diagnostics_empty_correct r) Hd).
  - exact (proj1 (AN.data_boundaries_empty_correct r) Hb).
Qed.
Lemma disposition_rejected {p} (r : AN.Result p) : disposition_of r = Rejected -> diagnostics_data r <> [].
Proof.
  unfold disposition_of, disposition_from_data; intro H.
  destruct (AN.data_diagnostics_empty (AN.data_of_result r)) eqn:Hd.
  - exfalso; destruct (AN.data_boundaries_empty (AN.data_of_result r)); discriminate H.
  - intro Hnil. rewrite (proj2 (AN.data_diagnostics_empty_correct r) Hnil) in Hd. discriminate Hd.
Qed.
Lemma disposition_outside {p} (r : AN.Result p) :
  disposition_of r = OutsideScope -> diagnostics_data r = [] /\ boundaries_data r <> [].
Proof.
  unfold disposition_of, disposition_from_data; intro H.
  destruct (AN.data_diagnostics_empty (AN.data_of_result r)) eqn:Hd; [ | discriminate H ].
  destruct (AN.data_boundaries_empty (AN.data_of_result r)) eqn:Hb; [ discriminate H | ].
  split.
  - exact (proj1 (AN.data_diagnostics_empty_correct r) Hd).
  - intro Hnil. rewrite (proj2 (AN.data_boundaries_empty_correct r) Hnil) in Hb. discriminate Hb.
Qed.

(* the sealed one-parameter ownership graph: Compilation retains one Result, each branch one Compilation *)
Module Type C4_PUBLIC.
  Parameter Compilation : Syntax.Program -> Type.
  Parameter Program   : Syntax.Program -> Type.
  Parameter Rejection : Syntax.Program -> Type.
  Parameter Outside   : Syntax.Program -> Type.

  (* primitive stored-field projections — the only abstract readers *)
  Parameter compilation_result   : forall {p}, Compilation p -> AN.Result p.
  Parameter program_compilation   : forall {p}, Program p -> Compilation p.
  Parameter rejection_compilation : forall {p}, Rejection p -> Compilation p.
  Parameter outside_compilation   : forall {p}, Outside p -> Compilation p.

  (* composed readers — manifest structural compositions, never abstract *)
  Definition program_result {p} (cp : Program p) : AN.Result p :=
    compilation_result (program_compilation cp).
  Definition rejection_result {p} (rj : Rejection p) : AN.Result p :=
    compilation_result (rejection_compilation rj).
  Definition outside_result {p} (ou : Outside p) : AN.Result p :=
    compilation_result (outside_compilation ou).

  Definition OutcomeAt (p : Syntax.Program) (k : Disposition) : Type :=
    match k with Compiled => Program p | Rejected => Rejection p | OutsideScope => Outside p end.

  Definition outcome_compilation {p k} (o : OutcomeAt p k) : Compilation p :=
    match k return OutcomeAt p k -> Compilation p with
    | Compiled     => fun o => program_compilation o
    | Rejected     => fun o => rejection_compilation o
    | OutsideScope => fun o => outside_compilation o
    end o.

  Definition outcome_result {p k} (o : OutcomeAt p k) : AN.Result p :=
    compilation_result (outcome_compilation o).

  (* the sole public branch-object acquisition path *)
  Parameter compile : forall p, OutcomeAt p (disposition p).

  (* branch evidence over the structurally observed supplied result *)
  Parameter program_admissible        : forall {p} (cp : Program p), AdmissibleData (program_result cp).
  Parameter rejection_has_diagnostics : forall {p} (rj : Rejection p), diagnostics_data (rejection_result rj) <> [].
  Parameter outside_reports           : forall {p} (ou : Outside p),
      diagnostics_data (outside_result ou) = [] /\ boundaries_data (outside_result ou) <> [].
  Parameter program_forces_compiled   : forall {p} (cp : Program p), disposition p = Compiled.

  (* the SOLE cross-seal computation law over the exact compile outcome; a computation interface, not provenance *)
  Parameter compile_observe_data : forall p,
    AN.data_of_result (outcome_result (compile p)) = AN.result_data p.
End C4_PUBLIC.

Module Sealed : C4_PUBLIC.
  Record CompilationR (p : Syntax.Program) : Type := mkComp { retained_result : AN.Result p }.
  Arguments mkComp {p} _.
  Arguments retained_result {p} _.

  Record ProgramR (p : Syntax.Program) : Type := mkProg {
    pr_comp        : CompilationR p ;
    pr_adm         : AdmissibleData (retained_result pr_comp) ;
    pr_source_disp : disposition p = Compiled
  }.
  Arguments mkProg {p} _ _ _.
  Arguments pr_comp {p} _. Arguments pr_adm {p} _. Arguments pr_source_disp {p} _.

  Record RejectionR (p : Syntax.Program) : Type := mkRej {
    rj_comp : CompilationR p ;
    rj_diag : diagnostics_data (retained_result rj_comp) <> []
  }.
  Arguments mkRej {p} _ _.
  Arguments rj_comp {p} _. Arguments rj_diag {p} _.

  Record OutsideR (p : Syntax.Program) : Type := mkOut {
    ou_comp : CompilationR p ;
    ou_diag : diagnostics_data (retained_result ou_comp) = [] ;
    ou_bnd  : boundaries_data (retained_result ou_comp) <> []
  }.
  Arguments mkOut {p} _ _ _.
  Arguments ou_comp {p} _. Arguments ou_diag {p} _. Arguments ou_bnd {p} _.

  Definition Compilation (p : Syntax.Program) : Type := CompilationR p.
  Definition Program   (p : Syntax.Program) : Type := ProgramR p.
  Definition Rejection (p : Syntax.Program) : Type := RejectionR p.
  Definition Outside   (p : Syntax.Program) : Type := OutsideR p.

  Definition compilation_result   {p} (c : Compilation p) : AN.Result p := retained_result c.
  Definition program_compilation   {p} (cp : Program p)   : Compilation p := pr_comp cp.
  Definition rejection_compilation {p} (rj : Rejection p) : Compilation p := rj_comp rj.
  Definition outside_compilation   {p} (ou : Outside p)   : Compilation p := ou_comp ou.

  Definition program_result {p} (cp : Program p) : AN.Result p :=
    compilation_result (program_compilation cp).
  Definition rejection_result {p} (rj : Rejection p) : AN.Result p :=
    compilation_result (rejection_compilation rj).
  Definition outside_result {p} (ou : Outside p) : AN.Result p :=
    compilation_result (outside_compilation ou).

  Definition OutcomeAt (p : Syntax.Program) (k : Disposition) : Type :=
    match k with Compiled => Program p | Rejected => Rejection p | OutsideScope => Outside p end.

  Definition outcome_compilation {p k} (o : OutcomeAt p k) : Compilation p :=
    match k return OutcomeAt p k -> Compilation p with
    | Compiled     => fun o => program_compilation o
    | Rejected     => fun o => rejection_compilation o
    | OutsideScope => fun o => outside_compilation o
    end o.

  Definition outcome_result {p k} (o : OutcomeAt p k) : AN.Result p :=
    compilation_result (outcome_compilation o).

  (* compile: bind r := analyze p once, put one c := mkComp r in every branch with its exact disposition proof *)
  Definition compile (p : Syntax.Program) : OutcomeAt p (disposition p) :=
    let r := AN.analyze p in
    let c := mkComp r in
    match disposition p as k return disposition p = k -> OutcomeAt p k with
    | Compiled     => fun H => mkProg c (disposition_compiled r H) H
    | Rejected     => fun H => mkRej  c (disposition_rejected r H)
    | OutsideScope => fun H => mkOut  c (proj1 (disposition_outside r H)) (proj2 (disposition_outside r H))
    end eq_refl.

  Definition program_admissible {p} (cp : Program p) : AdmissibleData (program_result cp) := pr_adm cp.
  Definition rejection_has_diagnostics {p} (rj : Rejection p) : diagnostics_data (rejection_result rj) <> [] := rj_diag rj.
  Definition outside_reports {p} (ou : Outside p) :
      diagnostics_data (outside_result ou) = [] /\ boundaries_data (outside_result ou) <> [] :=
    conj (ou_diag ou) (ou_bnd ou).
  Definition program_forces_compiled {p} (cp : Program p) : disposition p = Compiled := pr_source_disp cp.

  (* private checks: each branch payload observation equals the direct observation of the retained r, by refl *)
  Local Lemma compilation_projection_observes_input {p} (r : AN.Result p) :
    AN.data_of_result (compilation_result (mkComp r)) = AN.data_of_result r.
  Proof. reflexivity. Qed.
  Local Lemma program_projection_observes_input {p} (c : CompilationR p)
      (adm : AdmissibleData (retained_result c)) (Hd : disposition p = Compiled) :
    AN.data_of_result (program_result (mkProg c adm Hd)) = AN.data_of_result (retained_result c).
  Proof. reflexivity. Qed.
  Local Lemma rejection_projection_observes_input {p} (c : CompilationR p)
      (Hne : diagnostics_data (retained_result c) <> []) :
    AN.data_of_result (rejection_result (mkRej c Hne)) = AN.data_of_result (retained_result c).
  Proof. reflexivity. Qed.
  Local Lemma outside_projection_observes_input {p} (c : CompilationR p)
      (Hd : diagnostics_data (retained_result c) = []) (Hb : boundaries_data (retained_result c) <> []) :
    AN.data_of_result (outside_result (mkOut c Hd Hb)) = AN.data_of_result (retained_result c).
  Proof. reflexivity. Qed.

  (* proof device: abstract the branch construction over the decided disposition value k so cases split on k *)
  Local Lemma compile_obs_aux (p : Syntax.Program) (c : CompilationR p) (k : Disposition) (E : disposition p = k)
      (adm : disposition p = Compiled -> AdmissibleData (retained_result c))
      (rej : disposition p = Rejected -> diagnostics_data (retained_result c) <> [])
      (out : disposition p = OutsideScope ->
             diagnostics_data (retained_result c) = [] /\ boundaries_data (retained_result c) <> []) :
    AN.data_of_result (outcome_result (
      match k as k0 return disposition p = k0 -> OutcomeAt p k0 with
      | Compiled     => fun H => mkProg c (adm H) H
      | Rejected     => fun H => mkRej  c (rej H)
      | OutsideScope => fun H => mkOut  c (proj1 (out H)) (proj2 (out H))
      end E)) = AN.data_of_result (retained_result c).
  Proof. destruct k; reflexivity. Qed.

  (* the sole cross-seal law: the compile outcome observes the retained analyze data via the stored Compilation *)
  Theorem compile_observe_data (p : Syntax.Program) :
    AN.data_of_result (outcome_result (compile p)) = AN.result_data p.
  Proof.
    transitivity (AN.data_of_result (retained_result (mkComp (AN.analyze p)))).
    - exact (compile_obs_aux p (mkComp (AN.analyze p)) (disposition p) eq_refl
               (disposition_compiled (AN.analyze p)) (disposition_rejected (AN.analyze p))
               (disposition_outside (AN.analyze p))).
    - exact (AN.analyze_observe_data p).
  Qed.
End Sealed.

(* outer public surface: abstract carriers and structural readers re-exported from the seal *)
Definition Compilation (p : Syntax.Program) : Type := Sealed.Compilation p.
Definition Program   (p : Syntax.Program) : Type := Sealed.Program p.
Definition Rejection (p : Syntax.Program) : Type := Sealed.Rejection p.
Definition Outside   (p : Syntax.Program) : Type := Sealed.Outside p.

Definition compilation_result   {p} (c : Compilation p) : AN.Result p := Sealed.compilation_result c.
Definition program_compilation   {p} (cp : Program p)   : Compilation p := Sealed.program_compilation cp.
Definition rejection_compilation {p} (rj : Rejection p) : Compilation p := Sealed.rejection_compilation rj.
Definition outside_compilation   {p} (ou : Outside p)   : Compilation p := Sealed.outside_compilation ou.

(* the source of a Compilation is exactly its type index; not a reader of the stored object *)
Definition comp_source {p} (_ : Compilation p) : Syntax.Program := p.

Definition OutcomeAt (p : Syntax.Program) (k : Disposition) : Type := Sealed.OutcomeAt p k.
Definition outcome_compilation {p k} (o : OutcomeAt p k) : Compilation p := Sealed.outcome_compilation o.
Definition compile (p : Syntax.Program) : OutcomeAt p (disposition p) := Sealed.compile p.

(* composed readers: each structurally follows the stored Compilation to the stored Result *)
Definition program_result   {p} (cp : Program p)  : AN.Result p := compilation_result (program_compilation cp).
Definition rejection_result {p} (rj : Rejection p) : AN.Result p := compilation_result (rejection_compilation rj).
Definition outside_result   {p} (ou : Outside p)   : AN.Result p := compilation_result (outside_compilation ou).
Definition outcome_result   {p k} (o : OutcomeAt p k) : AN.Result p := compilation_result (outcome_compilation o).

(* report observations follow compilation_result from the SUPPLIED Compilation, never reacquire from p *)
Definition Diagnostic {p} (c : Compilation p) : Type := RP.Diagnostic (compilation_result c).
Definition Boundary   {p} (c : Compilation p) : Type := RP.Boundary (compilation_result c).
Definition diagnostics {p} (c : Compilation p) := diagnostics_data (compilation_result c).
Definition boundaries  {p} (c : Compilation p) := boundaries_data (compilation_result c).
Definition Admissible  {p} (c : Compilation p) : Prop := AdmissibleData (compilation_result c).
Lemma admissible_iff_reports {p} (c : Compilation p) : Admissible c <-> diagnostics c = [] /\ boundaries c = [].
Proof. unfold Admissible, AdmissibleData, diagnostics, boundaries; split; intro H; exact H. Qed.

Definition program_admissible {p} (cp : Program p) : Admissible (program_compilation cp) :=
  Sealed.program_admissible cp.
Definition rejection_has_diagnostics {p} (rj : Rejection p) : diagnostics (rejection_compilation rj) <> [] :=
  Sealed.rejection_has_diagnostics rj.
Definition outside_reports {p} (ou : Outside p) :
    diagnostics (outside_compilation ou) = [] /\ boundaries (outside_compilation ou) <> [] :=
  Sealed.outside_reports ou.
Definition program_forces_compiled {p} (cp : Program p) : disposition p = Compiled :=
  Sealed.program_forces_compiled cp.

(* the sanctioned whole-payload computation laws over the exact compile outcome and its compiled transport *)
Definition compile_observe_data (p : Syntax.Program) :
  AN.data_of_result (outcome_result (compile p)) = AN.result_data p := Sealed.compile_observe_data p.

(* the sanctioned compiled capability: compile (the sole source) transported by a disposition=Compiled proof *)
Definition compiled_program (p : Syntax.Program) (H : disposition p = Compiled) : Program p :=
  eq_rect (disposition p) (fun k => OutcomeAt p k) (compile p) Compiled H.

(* the payload observed through the exact compile outcome is invariant under disposition transport *)
Local Lemma outcome_data_eq_rect (p : Syntax.Program) (k : Disposition) (H : disposition p = k) :
  AN.data_of_result (outcome_result (eq_rect (disposition p) (fun k0 => OutcomeAt p k0) (compile p) k H))
  = AN.data_of_result (outcome_result (compile p)).
Proof. destruct H. reflexivity. Qed.

Lemma compiled_program_preserves_data (p : Syntax.Program) (H : disposition p = Compiled) :
  AN.data_of_result (program_result (compiled_program p H)) =
  AN.data_of_result (outcome_result (compile p)).
Proof. unfold compiled_program. exact (outcome_data_eq_rect p Compiled H). Qed.

(* the three branch predicates over the transparent disposition; each proven by the sanctioned rewrite *)
Definition compiles (p : Syntax.Program) : Prop := disposition p = Compiled.
Definition rejects  (p : Syntax.Program) : Prop := disposition p = Rejected.
Definition outsides (p : Syntax.Program) : Prop := disposition p = OutsideScope.
