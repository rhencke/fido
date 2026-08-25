(* Compilable — the C4 root: compile mints Program/Rejection/Outside as opaque certificates indexed by the Result *)

From Stdlib Require Import List Bool.
From Fido Require Import Syntax Compilable.Analysis Compilable.Report.
Import ListNotations.

Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

(* the ONE canonical analysis data for p: the sole Result computation used by disposition, compile, and readers *)
Definition compilation_data (p : Syntax.Program) : AN.Result p := AN.analyze p.

Inductive Disposition := Compiled | Rejected | OutsideScope.

(* observations computed from the exact data index, never by opening a certificate *)
Definition diagnostics_data {p} (r : AN.Result p) := RP.diagnostics (AN.res_facts r) (AN.res_pkg r).
Definition boundaries_data {p} (r : AN.Result p) := RP.boundaries (AN.res_facts r).
Definition AdmissibleData {p} (r : AN.Result p) : Prop := diagnostics_data r = [] /\ boundaries_data r = [].

(* the sole branch decision, over exact data; the program tag is that decision on the canonical data — one decider *)
Definition disposition_of {p} (r : AN.Result p) : Disposition :=
  match nil_dec (diagnostics_data r) with
  | left _ => match nil_dec (boundaries_data r) with left _ => Compiled | right _ => OutsideScope end
  | right _ => Rejected
  end.
Definition disposition (p : Syntax.Program) : Disposition := disposition_of (compilation_data p).

(* disposition inversion: the OPAQUE branch witnesses invert disposition_of over the exact data; assumption-free *)
Lemma disposition_compiled {p} (r : AN.Result p) : disposition_of r = Compiled -> AdmissibleData r.
Proof.
  unfold disposition_of, AdmissibleData; intro H.
  destruct (nil_dec (diagnostics_data r)) as [Hd|Hd]; [ | discriminate H ].
  destruct (nil_dec (boundaries_data r)) as [Hb|Hb]; [ split; assumption | discriminate H ].
Qed.
Lemma disposition_rejected {p} (r : AN.Result p) : disposition_of r = Rejected -> diagnostics_data r <> [].
Proof.
  unfold disposition_of; intro H. destruct (nil_dec (diagnostics_data r)) as [Hd|Hd].
  - exfalso; destruct (nil_dec (boundaries_data r)) as [Hb|Hb]; discriminate H.
  - exact Hd.
Qed.
Lemma disposition_outside {p} (r : AN.Result p) :
  disposition_of r = OutsideScope -> diagnostics_data r = [] /\ boundaries_data r <> [].
Proof.
  unfold disposition_of; intro H. destruct (nil_dec (diagnostics_data r)) as [Hd|Hd]; [ | discriminate H ].
  destruct (nil_dec (boundaries_data r)) as [Hb|Hb]; [ discriminate H | split; [exact Hd | exact Hb] ].
Qed.
(* the converse for capability provenance: admissible canonical data forces the Compiled disposition *)
Lemma admissible_forces_compiled {p} (r : AN.Result p) (Hr : r = compilation_data p)
  (Had : AdmissibleData r) : disposition p = Compiled.
Proof.
  unfold disposition. subst r. destruct Had as [Hd Hb]. unfold disposition_of.
  destruct (nil_dec (diagnostics_data (compilation_data p))) as [_|Hd']; [ | exfalso; exact (Hd' Hd) ].
  destruct (nil_dec (boundaries_data (compilation_data p))) as [_|Hb']; [ reflexivity | exfalso; exact (Hb' Hb) ].
Qed.

Module Type C4_PUBLIC.
  Parameter Compilation : forall (p : Syntax.Program), AN.Result p -> Type.
  Parameter Program   : forall (p : Syntax.Program), AN.Result p -> Type.
  Parameter Rejection : forall (p : Syntax.Program), AN.Result p -> Type.
  Parameter Outside   : forall (p : Syntax.Program), AN.Result p -> Type.

  Definition OutcomeAt (p : Syntax.Program) (r : AN.Result p) (k : Disposition) : Type :=
    match k with Compiled => Program p r | Rejected => Rejection p r | OutsideScope => Outside p r end.

  (* sole branch-object acquisition: for concrete p the data and tag reduce and compile p IS the branch type *)
  Parameter compile : forall p, OutcomeAt p (compilation_data p) (disposition_of (compilation_data p)).

  Parameter program_certificate   : forall {p r}, Program p r -> Compilation p r.
  Parameter rejection_certificate : forall {p r}, Rejection p r -> Compilation p r.
  Parameter outside_certificate   : forall {p r}, Outside p r -> Compilation p r.

  (* provenance: a certificate certifies its exact data index is the sole canonical analyze data; not a reader *)
  Parameter compilation_canonical : forall {p r}, Compilation p r -> r = compilation_data p.

  Parameter program_admissible        : forall {p r}, Program p r -> AdmissibleData r.
  Parameter rejection_has_diagnostics : forall {p r}, Rejection p r -> diagnostics_data r <> [].
  Parameter outside_reports           : forall {p r}, Outside p r -> diagnostics_data r = [] /\ boundaries_data r <> [].

  (* substitution-resistance: a capability exists only for the Compiled disposition of p's own analyze data *)
  Parameter program_forces_compiled  : forall {p r}, Program p r -> disposition p = Compiled.
End C4_PUBLIC.

Module Sealed : C4_PUBLIC.
  (* the certificate carries only OPAQUE logical evidence over the exact data index; NO Result field is stored *)
  Record CompilationR (p : Syntax.Program) (r : AN.Result p) : Type := mkComp { c_prov : r = compilation_data p }.
  Record ProgramR   (p : Syntax.Program) (r : AN.Result p) : Type := mkProg { pr_comp : CompilationR p r ; pr_adm : AdmissibleData r }.
  Record RejectionR (p : Syntax.Program) (r : AN.Result p) : Type := mkRej { rj_comp : CompilationR p r ; rj_diag : diagnostics_data r <> [] }.
  Record OutsideR   (p : Syntax.Program) (r : AN.Result p) : Type := mkOut { ou_comp : CompilationR p r ; ou_diag : diagnostics_data r = [] ; ou_bnd : boundaries_data r <> [] }.
  Arguments mkComp {p r} _. Arguments c_prov {p r} _.
  Arguments mkProg {p r} _ _. Arguments pr_comp {p r} _. Arguments pr_adm {p r} _.
  Arguments mkRej {p r} _ _. Arguments rj_comp {p r} _. Arguments rj_diag {p r} _.
  Arguments mkOut {p r} _ _ _. Arguments ou_comp {p r} _. Arguments ou_diag {p r} _. Arguments ou_bnd {p r} _.
  Definition Compilation := CompilationR. Definition Program := ProgramR. Definition Rejection := RejectionR. Definition Outside := OutsideR.

  Definition OutcomeAt (p : Syntax.Program) (r : AN.Result p) (k : Disposition) : Type :=
    match k with Compiled => Program p r | Rejected => Rejection p r | OutsideScope => Outside p r end.

  (* the sole composer, private: one proof-only compilation certificate over the canonical data *)
  Definition elaborate (p : Syntax.Program) : Compilation p (compilation_data p) := mkComp eq_refl.

  (* compile selects the branch by disposition_of and fills the certificate with OPAQUE witnesses; no Result stored *)
  Definition compile (p : Syntax.Program) : OutcomeAt p (compilation_data p) (disposition_of (compilation_data p)) :=
    match disposition_of (compilation_data p) as k
      return disposition_of (compilation_data p) = k -> OutcomeAt p (compilation_data p) k with
    | Compiled     => fun H => mkProg (elaborate p) (disposition_compiled (compilation_data p) H)
    | Rejected     => fun H => mkRej  (elaborate p) (disposition_rejected (compilation_data p) H)
    | OutsideScope => fun H => mkOut  (elaborate p) (proj1 (disposition_outside (compilation_data p) H))
                                                    (proj2 (disposition_outside (compilation_data p) H))
    end eq_refl.

  Definition program_certificate   {p r} (cp : Program p r) : Compilation p r := pr_comp cp.
  Definition rejection_certificate {p r} (rj : Rejection p r) : Compilation p r := rj_comp rj.
  Definition outside_certificate   {p r} (ou : Outside p r) : Compilation p r := ou_comp ou.
  Lemma compilation_canonical {p r} (c : Compilation p r) : r = compilation_data p.
  Proof. exact (c_prov c). Qed.
  Lemma program_admissible {p r} (cp : Program p r) : AdmissibleData r.
  Proof. exact (pr_adm cp). Qed.
  Lemma rejection_has_diagnostics {p r} (rj : Rejection p r) : diagnostics_data r <> [].
  Proof. exact (rj_diag rj). Qed.
  Lemma outside_reports {p r} (ou : Outside p r) : diagnostics_data r = [] /\ boundaries_data r <> [].
  Proof. exact (conj (ou_diag ou) (ou_bnd ou)). Qed.
  Lemma program_forces_compiled {p r} (cp : Program p r) : disposition p = Compiled.
  Proof. exact (admissible_forces_compiled r (compilation_canonical (program_certificate cp)) (pr_adm cp)). Qed.
End Sealed.

(* the transparent Result reader (§H): the exact type INDEX of the certificate, never opening or matching it *)
Definition outcome_result {p} {r : AN.Result p} {k : Disposition} (_ : Sealed.OutcomeAt p r k) : AN.Result p := r.

(* the public one-parameter API: certificates fixed at the canonical data index, so consumers stay source-compatible *)
Definition Compilation (p : Syntax.Program) : Type := Sealed.Compilation p (compilation_data p).
Definition Program (p : Syntax.Program) : Type := Sealed.Program p (compilation_data p).
Definition Rejection (p : Syntax.Program) : Type := Sealed.Rejection p (compilation_data p).
Definition Outside (p : Syntax.Program) : Type := Sealed.Outside p (compilation_data p).
Definition OutcomeAt (p : Syntax.Program) (k : Disposition) : Type := Sealed.OutcomeAt p (compilation_data p) k.
Definition compile (p : Syntax.Program) : OutcomeAt p (disposition p) := Sealed.compile p.

(* the certified source of a compiled program: Emit reaches it via this projection, then Render traverses it *)
Definition comp_source {p} (_ : Compilation p) : Syntax.Program := p.

Definition program_compilation {p} (cp : Program p) : Compilation p := Sealed.program_certificate cp.
Definition rejection_compilation {p} (rj : Rejection p) : Compilation p := Sealed.rejection_certificate rj.
Definition outside_compilation {p} (ou : Outside p) : Compilation p := Sealed.outside_certificate ou.

(* data-index convenience observations, read from the exact canonical index; no certificate opened *)
Definition Diagnostic {p} (_ : Compilation p) : Type := RP.Diagnostic (AN.res_facts (compilation_data p)).
Definition Boundary {p} (_ : Compilation p) : Type := RP.Boundary (AN.res_facts (compilation_data p)).
Definition diagnostics {p} (_ : Compilation p) := diagnostics_data (compilation_data p).
Definition boundaries {p} (_ : Compilation p) := boundaries_data (compilation_data p).
Definition Admissible {p} (_ : Compilation p) : Prop := AdmissibleData (compilation_data p).
Lemma admissible_iff_reports {p} (c : Compilation p) : Admissible c <-> diagnostics c = [] /\ boundaries c = [].
Proof. unfold Admissible, AdmissibleData, diagnostics, boundaries; split; intro H; exact H. Qed.

Definition program_admissible {p} (cp : Program p) : Admissible (program_compilation cp) := Sealed.program_admissible cp.
Definition rejection_has_diagnostics {p} (rj : Rejection p) : diagnostics (rejection_compilation rj) <> [] := Sealed.rejection_has_diagnostics rj.
Definition outside_reports {p} (ou : Outside p) : diagnostics (outside_compilation ou) = [] /\ boundaries (outside_compilation ou) <> [] := Sealed.outside_reports ou.
Definition program_forces_compiled {p} (cp : Program p) : disposition p = Compiled := Sealed.program_forces_compiled cp.

(* read-only result readers for evidence layers: each branch object's exact retained result IS its exact type index *)
Definition program_result   {p} (_ : Program p)  : AN.Result p := compilation_data p.
Definition rejection_result {p} (_ : Rejection p) : AN.Result p := compilation_data p.
Definition outside_result   {p} (_ : Outside p)   : AN.Result p := compilation_data p.

(* each branch reader IS p's one analyze data, definitionally — no rebuilt peer, no opaque certificate projection *)
Lemma program_result_canonical  {p} (cp : Program p)   : program_result cp = AN.analyze p.
Proof. reflexivity. Qed.
Lemma rejection_result_canonical {p} (rj : Rejection p) : rejection_result rj = AN.analyze p.
Proof. reflexivity. Qed.
Lemma outside_result_canonical   {p} (ou : Outside p)   : outside_result ou = AN.analyze p.
Proof. reflexivity. Qed.

(* the sanctioned compiled capability: compile (the sole source) coerced by a decidable disposition=Compiled proof *)
Definition compiled_program (p : Syntax.Program) (H : disposition p = Compiled) : Program p :=
  eq_rect (disposition p) (fun k => OutcomeAt p k) (compile p) Compiled H.

(* the three branch predicates over the transparent disposition; each proven by computation on a concrete program *)
Definition compiles (p : Syntax.Program) : Prop := disposition p = Compiled.
Definition rejects  (p : Syntax.Program) : Prop := disposition p = Rejected.
Definition outsides (p : Syntax.Program) : Prop := disposition p = OutsideScope.
