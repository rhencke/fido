(* Compilable — the sole production composer: one transparent retained compilation, an abstract compiled
   capability, and the permanent three-way Compiled/Rejected/OutsideScope decision. *)

From Stdlib Require Import List Bool.
From Fido Require Import Syntax Index Compilable.TypeResolution Compilable.PackageIdentity Compilable.Bindings Compilable.Packages Compilable.Facts Compilable.Report.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module PK := Compilable.Packages.
Module FA := Compilable.Facts.
Module RP := Compilable.Report.

(* one transparent retained compilation: every phase built once and kept as a field *)
Record Compilation (p : Syntax.Program) : Type := mk_compilation {
  comp_index   : Index.ProgramIndex p ;
  comp_surface : PI.PackageSurface comp_index ;
  comp_binds   : BN.BindingPhase comp_surface ;
  comp_pkgs    : PK.PackageFacts comp_binds ;
  comp_facts   : FA.FactPhase comp_binds
}.
Arguments mk_compilation {p} _ _ _ _ _.
Arguments comp_index {p} _.
Arguments comp_surface {p} _.
Arguments comp_binds {p} _.
Arguments comp_pkgs {p} _.
Arguments comp_facts {p} _.

Definition elaborate (p : Syntax.Program) : Compilation p :=
  let idx := Index.index_program p in
  let surface := PI.package_surface idx in
  let binds := BN.bindings surface in
  mk_compilation idx surface binds (PK.package_facts binds) (FA.facts binds).

Definition diagnostics {p} (c : Compilation p) := RP.diagnostics (comp_facts c) (comp_pkgs c).
Definition boundaries {p} (c : Compilation p) := RP.boundaries (comp_facts c) (comp_pkgs c).
Definition comp_source {p} (_ : Compilation p) : Syntax.Program := p.

Definition Admissible {p} (c : Compilation p) : Prop := diagnostics c = [] /\ boundaries c = [].

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

(* the compiled capability: an abstract indexed type whose only maker requires admissibility *)
Module Type PROGRAM_SIG.
  Parameter Program : forall {p}, Compilation p -> Type.
  Parameter issue : forall {p} (c : Compilation p), Admissible c -> Program c.
  Definition program_compilation {p} {c : Compilation p} (_ : Program c) : Compilation p := c.
  Definition program_source {p} {c : Compilation p} (_ : Program c) : Syntax.Program := p.
End PROGRAM_SIG.

Module Prog : PROGRAM_SIG.
  Definition Program {p} (_ : Compilation p) : Type := unit.
  Definition issue {p} (c : Compilation p) (_ : Admissible c) : Program c := tt.
  Definition program_compilation {p} {c : Compilation p} (_ : Program c) : Compilation p := c.
  Definition program_source {p} {c : Compilation p} (_ : Program c) : Syntax.Program := p.
End Prog.

(* the permanent three-way decision; each branch carries the exact compilation built once *)
Inductive Decision (p : Syntax.Program) : Type :=
| Compiled : forall c : Compilation p, Prog.Program c -> Decision p
| Rejected : forall c : Compilation p, diagnostics c <> [] -> Decision p
| OutsideScope : forall c : Compilation p, diagnostics c = [] -> boundaries c <> [] -> Decision p.
Arguments Compiled {p} _ _.
Arguments Rejected {p} _ _.
Arguments OutsideScope {p} _ _ _.

Definition compile (p : Syntax.Program) : Decision p :=
  let c := elaborate p in
  match nil_dec (diagnostics c) with
  | left Hd =>
      match nil_dec (boundaries c) with
      | left Hb => Compiled c (Prog.issue c (conj Hd Hb))
      | right Hb => OutsideScope c Hd Hb
      end
  | right Hd => Rejected c Hd
  end.

Definition compiles (p : Syntax.Program) : Prop :=
  match compile p with Compiled _ _ => True | _ => False end.
Definition rejects (p : Syntax.Program) : Prop :=
  match compile p with Rejected _ _ => True | _ => False end.
Definition outsides (p : Syntax.Program) : Prop :=
  match compile p with OutsideScope _ _ _ => True | _ => False end.

(* ---- narrow decision-partition theorems (these characterize the checker against its own projections) ---- *)

Lemma decision_total : forall p, compiles p \/ rejects p \/ outsides p.
Proof. intro p; unfold compiles, rejects, outsides; destruct (compile p); auto. Qed.

Lemma compiles_not_rejects : forall p, compiles p -> ~ rejects p.
Proof. intro p; unfold compiles, rejects; destruct (compile p); cbn; tauto. Qed.
Lemma compiles_not_outsides : forall p, compiles p -> ~ outsides p.
Proof. intro p; unfold compiles, outsides; destruct (compile p); cbn; tauto. Qed.
Lemma rejects_not_outsides : forall p, rejects p -> ~ outsides p.
Proof. intro p; unfold rejects, outsides; destruct (compile p); cbn; tauto. Qed.

Lemma accepted_iff_admissible : forall p, compiles p <-> Admissible (elaborate p).
Proof.
  intro p; unfold compiles, compile, Admissible.
  destruct (nil_dec (diagnostics (elaborate p))) as [Hd|Hd];
    destruct (nil_dec (boundaries (elaborate p))) as [Hb|Hb]; cbn; split; intro K;
    solve [ exact I
          | split; assumption
          | destruct K
          | destruct K as [K1 K2]; contradiction ].
Qed.

Lemma rejects_iff_diags : forall p, rejects p <-> diagnostics (elaborate p) <> [].
Proof.
  intro p; unfold rejects, compile.
  destruct (nil_dec (diagnostics (elaborate p))) as [Hd|Hd].
  - destruct (nil_dec (boundaries (elaborate p))) as [Hb|Hb]; cbn; split; intro K; contradiction.
  - cbn; split; [ intros _; exact Hd | intros _; exact I ].
Qed.

Lemma outsides_iff : forall p,
  outsides p <-> (diagnostics (elaborate p) = [] /\ boundaries (elaborate p) <> []).
Proof.
  intro p; unfold outsides, compile.
  destruct (nil_dec (diagnostics (elaborate p))) as [Hd|Hd].
  - destruct (nil_dec (boundaries (elaborate p))) as [Hb|Hb]; cbn; split.
    + tauto.
    + intros [_ Hb']; contradiction.
    + intros _; split; assumption.
    + intros _; exact I.
  - cbn; split; [ tauto | intros [Hd' _]; contradiction ].
Qed.
