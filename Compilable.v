(* Compilable — the C4 root: compile is the sole source of the abstract Program/Rejection/Outside branch objects *)

From Stdlib Require Import List Bool.
From Fido Require Import Syntax Index Compilable.TypeResolution Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

(* the one canonical analysis chain for p, each builder named exactly once; every projection derives from it *)
Local Definition c_i (p : Syntax.Program) : Index.ProgramIndex p := Index.index_program p.
Local Definition c_s (p : Syntax.Program) : PI.PackageSurface (c_i p) := PI.package_surface (c_i p).
Local Definition c_b (p : Syntax.Program) : BN.BindingPhase (c_s p) := BN.bindings (c_s p).
Local Definition c_pf (p : Syntax.Program) : AN.PackageFacts (c_b p) := AN.package_facts (c_b p).
Local Definition c_fp (p : Syntax.Program) : AN.FactPhase (c_b p) := AN.facts (c_b p).

(* the public program branch tag: a direct 3-way projection of the one canonical issue table over p's chain *)
Inductive Disposition := Compiled | Rejected | OutsideScope.

Definition disposition (p : Syntax.Program) : Disposition :=
  match nil_dec (RP.diagnostics (c_fp p) (c_pf p)) with
  | left _ => match nil_dec (RP.boundaries (c_fp p) (c_pf p)) with left _ => Compiled | right _ => OutsideScope end
  | right _ => Rejected
  end.

Module Type C4_PUBLIC.
  Parameter Compilation : Syntax.Program -> Type.
  Parameter Program   : Syntax.Program -> Type.
  Parameter Rejection : Syntax.Program -> Type.
  Parameter Outside   : Syntax.Program -> Type.

  Definition OutcomeAt (p : Syntax.Program) (k : Disposition) : Type :=
    match k with Compiled => Program p | Rejected => Rejection p | OutsideScope => Outside p end.

  (* sole branch-object acquisition: for concrete p the tag reduces and compile p IS the branch type directly *)
  Parameter compile : forall p, OutcomeAt p (disposition p).

  Parameter program_compilation   : forall {p}, Program p -> Compilation p.
  Parameter rejection_compilation : forall {p}, Rejection p -> Compilation p.
  Parameter outside_compilation   : forall {p}, Outside p -> Compilation p.

  Parameter Diagnostic : forall {p}, Compilation p -> Type.
  Parameter Boundary   : forall {p}, Compilation p -> Type.
  Parameter diagnostics : forall {p} (c : Compilation p), list (Diagnostic c).
  Parameter boundaries  : forall {p} (c : Compilation p), list (Boundary c).

  Parameter Admissible : forall {p}, Compilation p -> Prop.
  Parameter admissible_iff_reports :
    forall {p} (c : Compilation p), Admissible c <-> diagnostics c = [] /\ boundaries c = [].

  Parameter program_admissible       : forall {p} (cp : Program p),   Admissible (program_compilation cp).
  Parameter rejection_has_diagnostics : forall {p} (r : Rejection p), diagnostics (rejection_compilation r) <> [].
  Parameter outside_reports :
    forall {p} (o : Outside p), diagnostics (outside_compilation o) = [] /\ boundaries (outside_compilation o) <> [].
End C4_PUBLIC.

Module Sealed : C4_PUBLIC.
  (* one retained compilation: the exact index-surface-bindings-package-facts chain, built once, kept as fields *)
  Record CompilationR (p : Syntax.Program) : Type := mkComp {
    k_i  : Index.ProgramIndex p ;
    k_s  : PI.PackageSurface k_i ;
    k_b  : BN.BindingPhase k_s ;
    k_pf : AN.PackageFacts k_b ;
    k_fp : AN.FactPhase k_b
  }.
  Arguments mkComp {p} _ _ _ _ _.
  Arguments k_pf {p} _.
  Arguments k_fp {p} _.
  Definition Compilation := CompilationR.

  Definition Diagnostic {p} (c : Compilation p) : Type := RP.Diagnostic (k_fp c) (k_pf c).
  Definition Boundary {p} (c : Compilation p) : Type := RP.Boundary (k_fp c) (k_pf c).
  Definition diagnostics {p} (c : Compilation p) : list (Diagnostic c) := RP.diagnostics (k_fp c) (k_pf c).
  Definition boundaries {p} (c : Compilation p) : list (Boundary c) := RP.boundaries (k_fp c) (k_pf c).

  Definition Admissible {p} (c : Compilation p) : Prop := diagnostics c = [] /\ boundaries c = [].
  Lemma admissible_iff_reports {p} (c : Compilation p) : Admissible c <-> diagnostics c = [] /\ boundaries c = [].
  Proof. unfold Admissible; split; intro H; exact H. Qed.

  (* the sole composer, private: it consumes the one shared chain, so no downstream module rebuilds the index *)
  Definition elaborate (p : Syntax.Program) : Compilation p := mkComp (c_i p) (c_s p) (c_b p) (c_pf p) (c_fp p).

  Record ProgramR   (p : Syntax.Program) : Type := mkProg { pr_comp : Compilation p ; pr_adm  : Admissible pr_comp }.
  Record RejectionR (p : Syntax.Program) : Type := mkRej  { rj_comp : Compilation p ; rj_diag : diagnostics rj_comp <> [] }.
  Record OutsideR   (p : Syntax.Program) : Type := mkOut  { ou_comp : Compilation p ; ou_diag : diagnostics ou_comp = [] ; ou_bnd : boundaries ou_comp <> [] }.
  Arguments mkProg {p} _ _. Arguments pr_comp {p} _. Arguments pr_adm {p} _.
  Arguments mkRej {p} _ _.  Arguments rj_comp {p} _. Arguments rj_diag {p} _.
  Arguments mkOut {p} _ _ _. Arguments ou_comp {p} _. Arguments ou_diag {p} _. Arguments ou_bnd {p} _.
  Definition Program := ProgramR. Definition Rejection := RejectionR. Definition Outside := OutsideR.

  Definition OutcomeAt (p : Syntax.Program) (k : Disposition) : Type :=
    match k with Compiled => Program p | Rejected => Rejection p | OutsideScope => Outside p end.

  (* compile builds the branch object whose tag the transparent disposition already names, from the same reports *)
  Definition compile (p : Syntax.Program) : OutcomeAt p (disposition p).
  Proof.
    unfold OutcomeAt, disposition.
    destruct (nil_dec (RP.diagnostics (c_fp p) (c_pf p))) as [Hd|Hd].
    - destruct (nil_dec (RP.boundaries (c_fp p) (c_pf p))) as [Hb|Hb].
      + exact (mkProg (elaborate p) (conj Hd Hb)).
      + exact (mkOut (elaborate p) Hd Hb).
    - exact (mkRej (elaborate p) Hd).
  Defined.

  Definition program_compilation {p} (cp : Program p) : Compilation p := pr_comp cp.
  Definition rejection_compilation {p} (r : Rejection p) : Compilation p := rj_comp r.
  Definition outside_compilation {p} (o : Outside p) : Compilation p := ou_comp o.

  Lemma program_admissible {p} (cp : Program p) : Admissible (program_compilation cp).
  Proof. exact (pr_adm cp). Qed.
  Lemma rejection_has_diagnostics {p} (r : Rejection p) : diagnostics (rejection_compilation r) <> [].
  Proof. exact (rj_diag r). Qed.
  Lemma outside_reports {p} (o : Outside p) : diagnostics (outside_compilation o) = [] /\ boundaries (outside_compilation o) <> [].
  Proof. exact (conj (ou_diag o) (ou_bnd o)). Qed.
End Sealed.

(* the certified source of a compiled program: Emit reaches it via this projection, then Render traverses it *)
Definition comp_source {p} (_ : Sealed.Compilation p) : Syntax.Program := p.

(* the public C4 API, named at Compilable: abstract root objects + the sole compile + exact projections *)
Definition Compilation := Sealed.Compilation.
Definition Program := Sealed.Program.
Definition Rejection := Sealed.Rejection.
Definition Outside := Sealed.Outside.
Definition OutcomeAt := Sealed.OutcomeAt.
Definition compile := Sealed.compile.
Definition program_compilation {p} := @Sealed.program_compilation p.
Definition rejection_compilation {p} := @Sealed.rejection_compilation p.
Definition outside_compilation {p} := @Sealed.outside_compilation p.
Definition Diagnostic {p} := @Sealed.Diagnostic p.
Definition Boundary {p} := @Sealed.Boundary p.
Definition diagnostics {p} := @Sealed.diagnostics p.
Definition boundaries {p} := @Sealed.boundaries p.
Definition Admissible {p} := @Sealed.Admissible p.
Definition admissible_iff_reports {p} := @Sealed.admissible_iff_reports p.
Definition program_admissible {p} := @Sealed.program_admissible p.
Definition rejection_has_diagnostics {p} := @Sealed.rejection_has_diagnostics p.
Definition outside_reports {p} := @Sealed.outside_reports p.

(* the sanctioned compiled capability: compile (the sole source) coerced by a decidable disposition=Compiled proof *)
Definition compiled_program (p : Syntax.Program) (H : disposition p = Compiled) : Program p :=
  eq_rect (disposition p) (fun k => OutcomeAt p k) (compile p) Compiled H.

(* the three branch predicates over the transparent disposition; each proven by computation on a concrete program *)
Definition compiles (p : Syntax.Program) : Prop := disposition p = Compiled.
Definition rejects  (p : Syntax.Program) : Prop := disposition p = Rejected.
Definition outsides (p : Syntax.Program) : Prop := disposition p = OutsideScope.
