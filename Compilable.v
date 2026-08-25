(* Compilable — the C4 root: compile alone mints Program/Rejection/Outside over one Analysis.Result. *)

From Stdlib Require Import List Bool.
From Fido Require Import Syntax Compilable.Analysis Compilable.Report.
Import ListNotations.

Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

(* the one canonical analysis result for p; every projection and branch object derives from this single object *)
Local Definition c_result (p : Syntax.Program) : AN.Result p := AN.analyze p.

(* the public program branch tag: a direct 3-way projection of the one canonical result's issue lists *)
Inductive Disposition := Compiled | Rejected | OutsideScope.

Definition disposition (p : Syntax.Program) : Disposition :=
  let c := c_result p in
  match nil_dec (RP.diagnostics (AN.res_facts c) (AN.res_pkg c)) with
  | left _ => match nil_dec (RP.boundaries (AN.res_facts c)) with left _ => Compiled | right _ => OutsideScope end
  | right _ => Rejected
  end.

(* empty reports of p's canonical analyze result force the Compiled disposition; the transport bridge *)
Lemma disposition_of_admissible {p} (r : AN.Result p) (Hr : r = AN.analyze p)
  (Hd : RP.diagnostics (AN.res_facts r) (AN.res_pkg r) = [])
  (Hb : RP.boundaries (AN.res_facts r) = []) : disposition p = Compiled.
Proof.
  subst r. unfold disposition; cbv zeta.
  change (c_result p) with (AN.analyze p).
  destruct (nil_dec (RP.diagnostics (AN.res_facts (AN.analyze p)) (AN.res_pkg (AN.analyze p)))) as [_|Hd'];
    [ | exfalso; exact (Hd' Hd) ].
  destruct (nil_dec (RP.boundaries (AN.res_facts (AN.analyze p)))) as [_|Hb'];
    [ reflexivity | exfalso; exact (Hb' Hb) ].
Qed.

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

  (* the exact retained analysis result projected read-only from each compilation; it mints no capability *)
  Parameter compilation_result : forall {p}, Compilation p -> AN.Result p.
  (* provenance: the retained result is exactly the sole analyze object, never an independently rebuilt peer *)
  Parameter compilation_result_canonical : forall {p} (c : Compilation p), compilation_result c = AN.analyze p.

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

  (* substitution-resistance: a capability exists only for the Compiled disposition of p's own analyze result *)
  Parameter program_forces_compiled : forall {p} (cp : Program p), disposition p = Compiled.
End C4_PUBLIC.

Module Sealed : C4_PUBLIC.
  (* one retained result, with a provenance proof pinning it to the sole analyze builder; kept whole *)
  Record CompilationR (p : Syntax.Program) : Type := mkComp { c_res : AN.Result p ; c_prov : c_res = AN.analyze p }.
  Arguments mkComp {p} _ _.
  Arguments c_res {p} _.
  Arguments c_prov {p} _.
  Definition Compilation := CompilationR.

  Definition Diagnostic {p} (c : Compilation p) : Type := RP.Diagnostic (AN.res_facts (c_res c)).
  Definition Boundary {p} (c : Compilation p) : Type := RP.Boundary (AN.res_facts (c_res c)).
  Definition diagnostics {p} (c : Compilation p) : list (Diagnostic c) := RP.diagnostics (AN.res_facts (c_res c)) (AN.res_pkg (c_res c)).
  Definition boundaries {p} (c : Compilation p) : list (Boundary c) := RP.boundaries (AN.res_facts (c_res c)).

  Definition Admissible {p} (c : Compilation p) : Prop := diagnostics c = [] /\ boundaries c = [].
  Lemma admissible_iff_reports {p} (c : Compilation p) : Admissible c <-> diagnostics c = [] /\ boundaries c = [].
  Proof. unfold Admissible; split; intro H; exact H. Qed.

  (* the sole composer, private: it binds one exact result and keeps it whole; no downstream module rebuilds it *)
  Definition elaborate (p : Syntax.Program) : Compilation p := mkComp (AN.analyze p) eq_refl.
  Definition compilation_result {p} (c : Compilation p) : AN.Result p := c_res c.
  Lemma compilation_result_canonical {p} (c : Compilation p) : compilation_result c = AN.analyze p.
  Proof. exact (c_prov c). Qed.

  Record ProgramR   (p : Syntax.Program) : Type := mkProg { pr_comp : Compilation p ; pr_adm  : Admissible pr_comp }.
  Record RejectionR (p : Syntax.Program) : Type := mkRej  { rj_comp : Compilation p ; rj_diag : diagnostics rj_comp <> [] }.
  Record OutsideR   (p : Syntax.Program) : Type := mkOut  { ou_comp : Compilation p ; ou_diag : diagnostics ou_comp = [] ; ou_bnd : boundaries ou_comp <> [] }.
  Arguments mkProg {p} _ _. Arguments pr_comp {p} _. Arguments pr_adm {p} _.
  Arguments mkRej {p} _ _.  Arguments rj_comp {p} _. Arguments rj_diag {p} _.
  Arguments mkOut {p} _ _ _. Arguments ou_comp {p} _. Arguments ou_diag {p} _. Arguments ou_bnd {p} _.
  Definition Program := ProgramR. Definition Rejection := RejectionR. Definition Outside := OutsideR.

  Definition OutcomeAt (p : Syntax.Program) (k : Disposition) : Type :=
    match k with Compiled => Program p | Rejected => Rejection p | OutsideScope => Outside p end.

  (* compile builds the branch object whose tag the transparent disposition already names, from the same result *)
  Definition compile (p : Syntax.Program) : OutcomeAt p (disposition p).
  Proof.
    unfold OutcomeAt, disposition. cbv zeta. set (c := c_result p).
    destruct (nil_dec (RP.diagnostics (AN.res_facts c) (AN.res_pkg c))) as [Hd|Hd].
    - destruct (nil_dec (RP.boundaries (AN.res_facts c))) as [Hb|Hb].
      + exact (mkProg (mkComp c eq_refl) (conj Hd Hb)).
      + exact (mkOut (mkComp c eq_refl) Hd Hb).
    - exact (mkRej (mkComp c eq_refl) Hd).
  Defined.

  (* provenance: possessing a Program forces the Compiled disposition; no rebuilt result manufactures a capability *)
  Lemma program_forces_compiled {p} (cp : ProgramR p) : disposition p = Compiled.
  Proof.
    pose proof (pr_adm cp) as Hadm.
    unfold Admissible, diagnostics, boundaries in Hadm.
    destruct Hadm as [Hd Hb].
    exact (disposition_of_admissible (c_res (pr_comp cp)) (c_prov (pr_comp cp)) Hd Hb).
  Qed.

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
Definition compilation_result {p} := @Sealed.compilation_result p.
Definition compilation_result_canonical {p} := @Sealed.compilation_result_canonical p.
Definition program_forces_compiled {p} := @Sealed.program_forces_compiled p.
Definition Diagnostic {p} := @Sealed.Diagnostic p.
Definition Boundary {p} := @Sealed.Boundary p.
Definition diagnostics {p} := @Sealed.diagnostics p.
Definition boundaries {p} := @Sealed.boundaries p.
Definition Admissible {p} := @Sealed.Admissible p.
Definition admissible_iff_reports {p} := @Sealed.admissible_iff_reports p.
Definition program_admissible {p} := @Sealed.program_admissible p.
Definition rejection_has_diagnostics {p} := @Sealed.rejection_has_diagnostics p.
Definition outside_reports {p} := @Sealed.outside_reports p.

(* read-only result projections for future evidence layers: each branch object exposes its exact retained result *)
Definition program_result   {p} (cp : Program p)  : AN.Result p := compilation_result (program_compilation cp).
Definition rejection_result {p} (r  : Rejection p) : AN.Result p := compilation_result (rejection_compilation r).
Definition outside_result   {p} (o  : Outside p)   : AN.Result p := compilation_result (outside_compilation o).

(* each branch object projects exactly p's one analyze result, so no reader consults a rebuilt peer chain *)
Lemma program_result_canonical  {p} (cp : Program p)   : program_result cp = AN.analyze p.
Proof. apply compilation_result_canonical. Qed.
Lemma rejection_result_canonical {p} (r : Rejection p) : rejection_result r = AN.analyze p.
Proof. apply compilation_result_canonical. Qed.
Lemma outside_result_canonical   {p} (o : Outside p)   : outside_result o = AN.analyze p.
Proof. apply compilation_result_canonical. Qed.

(* the sanctioned compiled capability: compile (the sole source) coerced by a decidable disposition=Compiled proof *)
Definition compiled_program (p : Syntax.Program) (H : disposition p = Compiled) : Program p :=
  eq_rect (disposition p) (fun k => OutcomeAt p k) (compile p) Compiled H.

(* the three branch predicates over the transparent disposition; each proven by computation on a concrete program *)
Definition compiles (p : Syntax.Program) : Prop := disposition p = Compiled.
Definition rejects  (p : Syntax.Program) : Prop := disposition p = Rejected.
Definition outsides (p : Syntax.Program) : Prop := disposition p = OutsideScope.
