(* Compilable — the sealed public surface: compile is the sole Decision source, inspect its sole eliminator. *)

From Stdlib Require Import List Bool.
From Fido Require Import Syntax Index Compilable.TypeResolution Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

(* one retained compilation: every phase built once and kept as a field; the composer is private *)
Record Compilation (p : Syntax.Program) : Type := mk_compilation {
  comp_index   : Index.ProgramIndex p ;
  comp_surface : PI.PackageSurface comp_index ;
  comp_binds   : BN.BindingPhase comp_surface ;
  comp_pkgs    : AN.PackageFacts comp_binds ;
  comp_facts   : AN.FactPhase comp_binds
}.
Arguments mk_compilation {p} _ _ _ _ _.
Arguments comp_index {p} _.
Arguments comp_surface {p} _.
Arguments comp_binds {p} _.
Arguments comp_pkgs {p} _.
Arguments comp_facts {p} _.

(* the sole composer, private: a client cannot rebuild a compilation, only receive one from compile via inspect *)
Local Definition elaborate (p : Syntax.Program) : Compilation p :=
  let idx := Index.index_program p in
  let surface := PI.package_surface idx in
  let binds := BN.bindings surface in
  mk_compilation idx surface binds (AN.package_facts binds) (AN.facts binds).

Definition Diagnostic {p} (c : Compilation p) : Type := RP.Diagnostic (comp_facts c) (comp_pkgs c).
Definition Boundary {p} (c : Compilation p) : Type := RP.Boundary (comp_facts c) (comp_pkgs c).
Definition diagnostics {p} (c : Compilation p) : list (Diagnostic c) := RP.diagnostics (comp_facts c) (comp_pkgs c).
Definition boundaries {p} (c : Compilation p) : list (Boundary c) := RP.boundaries (comp_facts c) (comp_pkgs c).

Definition Admissible {p} (c : Compilation p) : Prop := diagnostics c = [] /\ boundaries c = [].

Lemma admissible_iff_reports {p} (c : Compilation p) :
  Admissible c <-> diagnostics c = [] /\ boundaries c = [].
Proof. unfold Admissible; split; intro H; exact H. Qed.

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

(* Generic proof support: a bool observation of a list's outer constructor, not used in any production definition. *)
Definition list_is_nilb {A : Type} (xs : list A) : bool :=
  match xs with [] => true | _ :: _ => false end.
Lemma list_is_nilb_true {A : Type} (xs : list A) : list_is_nilb xs = true -> xs = [].
Proof. destruct xs as [|x xs]; cbn; [ intros _; reflexivity | intros H; discriminate H ]. Qed.
Lemma list_is_nilb_false {A : Type} (xs : list A) : list_is_nilb xs = false -> xs <> [].
Proof. destruct xs as [|x xs]; cbn; [ intros H; discriminate H | intros _ H; discriminate H ]. Qed.

(* the permanent three-way decision; each branch carries the exact compilation built once, with its exact proof *)
Inductive Decision (p : Syntax.Program) : Type :=
| DCompiled : forall c : Compilation p, Admissible c -> Decision p
| DRejected : forall c : Compilation p, diagnostics c <> [] -> Decision p
| DOutside  : forall c : Compilation p, diagnostics c = [] -> boundaries c <> [] -> Decision p.
Arguments DCompiled {p} _ _.
Arguments DRejected {p} _ _.
Arguments DOutside {p} _ _ _.

Definition compile (p : Syntax.Program) : Decision p :=
  let c := elaborate p in
  match nil_dec (diagnostics c) with
  | left Hd =>
      match nil_dec (boundaries c) with
      | left Hb => DCompiled c (conj Hd Hb)
      | right Hb => DOutside c Hd Hb
      end
  | right Hd => DRejected c Hd
  end.

(* branch payloads: obtainable only by eliminating a supplied Decision; each names its exact revealed compilation *)
Definition CompiledPayload {p} (d : Decision p) (c : Compilation p) : Type :=
  match d with DCompiled c' _ => c' = c | _ => False end.
Definition RejectedPayload {p} (d : Decision p) (c : Compilation p) : Type :=
  match d with DRejected c' _ => c' = c | _ => False end.
Definition OutsidePayload {p} (d : Decision p) (c : Compilation p) : Type :=
  match d with DOutside c' _ _ => c' = c | _ => False end.

Definition rejected_diagnostics {p} {d : Decision p} {c : Compilation p} (_ : RejectedPayload d c) : list (Diagnostic c) :=
  diagnostics c.
Definition rejected_boundaries {p} {d : Decision p} {c : Compilation p} (_ : RejectedPayload d c) : list (Boundary c) :=
  boundaries c.
Definition outside_boundaries {p} {d : Decision p} {c : Compilation p} (_ : OutsidePayload d c) : list (Boundary c) :=
  boundaries c.

(* the compiled capability: an abstract type whose only public maker projects it from a supplied compiled payload *)
Module Type PROGRAM_SIG.
  Parameter Program : forall {p}, Compilation p -> Type.
  Parameter compiled_prog : forall {p} {d : Decision p} {c : Compilation p}, CompiledPayload d c -> Program c.
End PROGRAM_SIG.

Module Prog : PROGRAM_SIG.
  Definition Program {p} (_ : Compilation p) : Type := unit.
  (* private: the sole admissibility-gated mint, reachable only through compiled_prog on a real compiled payload *)
  Definition issue {p} (c : Compilation p) (_ : Admissible c) : Program c := tt.
  Definition compiled_prog {p} {d : Decision p} {c : Compilation p} (cp : CompiledPayload d c) : Program c :=
    (match d as d0 return CompiledPayload d0 c -> Program c with
     | DCompiled c' Hadm => fun Heq => issue c (eq_rect c' (fun x => Admissible x) Hadm c Heq)
     | DRejected _ _ => fun f => match f return Program c with end
     | DOutside _ _ _ => fun f => match f return Program c with end
     end) cp.
End Prog.

(* inspect's result: a supplied Decision revealed as exactly one branch with its abstract payload *)
Inductive Case {p} (d : Decision p) : Type :=
| IsCompiled : forall c : Compilation p, CompiledPayload d c -> Case d
| IsRejected : forall c : Compilation p, RejectedPayload d c -> Case d
| IsOutside  : forall c : Compilation p, OutsidePayload d c -> Case d.
Arguments IsCompiled {p d} _ _.
Arguments IsRejected {p d} _ _.
Arguments IsOutside {p d} _ _.

Definition inspect {p} (d : Decision p) : Case d :=
  match d as d0 return Case d0 with
  | DCompiled c Hadm => IsCompiled c (eq_refl : CompiledPayload (DCompiled c Hadm) c)
  | DRejected c Hd => IsRejected c (eq_refl : RejectedPayload (DRejected c Hd) c)
  | DOutside c Hd Hb => IsOutside c (eq_refl : OutsidePayload (DOutside c Hd Hb) c)
  end.

(* branch facts: each payload characterizes the exact revealed compilation's reports; none mints a capability *)
Lemma compiled_admissible {p} {d : Decision p} {c : Compilation p} (cp : CompiledPayload d c) :
  diagnostics c = [] /\ boundaries c = [].
Proof.
  destruct d as [c' Hadm | c' Hd | c' Hd Hb]; cbn in cp; [ destruct cp; exact Hadm | destruct cp | destruct cp ].
Qed.

Lemma rejected_has_diagnostics {p} {d : Decision p} {c : Compilation p} (rp : RejectedPayload d c) :
  diagnostics c <> [].
Proof.
  destruct d as [c' Hadm | c' Hd | c' Hd Hb]; cbn in rp; [ destruct rp | destruct rp; exact Hd | destruct rp ].
Qed.

Lemma outside_reports {p} {d : Decision p} {c : Compilation p} (op : OutsidePayload d c) :
  diagnostics c = [] /\ boundaries c <> [].
Proof.
  destruct d as [c' Hadm | c' Hd | c' Hd Hb]; cbn in op; [ destruct op | destruct op | destruct op; split; assumption ].
Qed.

(* the compiled capability retains the admissibility of exactly the revealed compilation *)
Lemma compiled_prog_admissible {p} {d : Decision p} {c : Compilation p} (cp : CompiledPayload d c) :
  Admissible c.
Proof. apply admissible_iff_reports; exact (compiled_admissible cp). Qed.

(* payload disjointness: for one supplied decision, at most one branch payload is inhabited *)
Lemma compiled_not_rejected {p} {d : Decision p} {c c' : Compilation p} :
  CompiledPayload d c -> RejectedPayload d c' -> False.
Proof. destruct d; cbn; intros H1 H2; solve [ destruct H1 | destruct H2 ]. Qed.
Lemma compiled_not_outside {p} {d : Decision p} {c c' : Compilation p} :
  CompiledPayload d c -> OutsidePayload d c' -> False.
Proof. destruct d; cbn; intros H1 H2; solve [ destruct H1 | destruct H2 ]. Qed.
Lemma rejected_not_outside {p} {d : Decision p} {c c' : Compilation p} :
  RejectedPayload d c -> OutsidePayload d c' -> False.
Proof. destruct d; cbn; intros H1 H2; solve [ destruct H1 | destruct H2 ]. Qed.

(* shallow branch recovery: a client selects the compile branch by nilb observers, not a deep normal form *)
Definition diag_nilb (p : Syntax.Program) : bool := list_is_nilb (diagnostics (elaborate p)).
Definition bound_nilb (p : Syntax.Program) : bool := list_is_nilb (boundaries (elaborate p)).

Definition compiled_of_nilb (p : Syntax.Program) :
  diag_nilb p = true -> bound_nilb p = true -> { c : Compilation p & CompiledPayload (compile p) c }.
Proof.
  intros Hd Hb. apply list_is_nilb_true in Hd. apply list_is_nilb_true in Hb.
  unfold compile.
  destruct (nil_dec (diagnostics (elaborate p))) as [Hd'|Hd'].
  - destruct (nil_dec (boundaries (elaborate p))) as [Hb'|Hb'].
    + exists (elaborate p); reflexivity.
    + exfalso; exact (Hb' Hb).
  - exfalso; exact (Hd' Hd).
Defined.

Definition rejected_of_nilb (p : Syntax.Program) :
  diag_nilb p = false -> { c : Compilation p & RejectedPayload (compile p) c }.
Proof.
  intro Hd. apply list_is_nilb_false in Hd. unfold compile.
  destruct (nil_dec (diagnostics (elaborate p))) as [Hd'|Hd'].
  - exfalso; exact (Hd Hd').
  - exists (elaborate p); reflexivity.
Defined.

Definition outside_of_nilb (p : Syntax.Program) :
  diag_nilb p = true -> bound_nilb p = false -> { c : Compilation p & OutsidePayload (compile p) c }.
Proof.
  intros Hd Hb. apply list_is_nilb_true in Hd. apply list_is_nilb_false in Hb.
  unfold compile.
  destruct (nil_dec (diagnostics (elaborate p))) as [Hd'|Hd'].
  - destruct (nil_dec (boundaries (elaborate p))) as [Hb'|Hb'].
    + exfalso; exact (Hb Hb').
    + exists (elaborate p); reflexivity.
  - exfalso; exact (Hd' Hd).
Defined.

(* the supplied program of a revealed compilation, by projection *)
Definition comp_source {p} (_ : Compilation p) : Syntax.Program := p.

(* compile's branch is decided exactly by the report lists of the one compilation it builds *)
Theorem inspect_compile {p} :
  match inspect (compile p) with
  | IsCompiled c _ => diagnostics c = [] /\ boundaries c = []
  | IsRejected c _ => diagnostics c <> []
  | IsOutside c _  => diagnostics c = [] /\ boundaries c <> []
  end.
Proof.
  unfold compile.
  destruct (nil_dec (diagnostics (elaborate p))) as [Hd|Hd].
  - destruct (nil_dec (boundaries (elaborate p))) as [Hb|Hb]; cbn.
    + split; assumption.
    + split; assumption.
  - cbn; exact Hd.
Qed.

(* convenience branch predicates over the production authority; each recovered from shallow nilb observers *)
Definition compiles (p : Syntax.Program) : Prop :=
  match compile p with DCompiled _ _ => True | _ => False end.
Definition rejects (p : Syntax.Program) : Prop :=
  match compile p with DRejected _ _ => True | _ => False end.
Definition outsides (p : Syntax.Program) : Prop :=
  match compile p with DOutside _ _ _ => True | _ => False end.

Lemma compiles_via_nilb (p : Syntax.Program) : diag_nilb p = true -> bound_nilb p = true -> compiles p.
Proof.
  intros Hd Hb. destruct (compiled_of_nilb p Hd Hb) as [c cp]. unfold compiles.
  destruct (compile p) as [c' Hadm | c' Hd' | c' Hd' Hb']; cbn in cp; [ exact I | destruct cp | destruct cp ].
Qed.
Lemma rejects_via_nilb (p : Syntax.Program) : diag_nilb p = false -> rejects p.
Proof.
  intro Hd. destruct (rejected_of_nilb p Hd) as [c rp]. unfold rejects.
  destruct (compile p) as [c' Hadm | c' Hd' | c' Hd' Hb']; cbn in rp; [ destruct rp | exact I | destruct rp ].
Qed.
Lemma outsides_via_nilb (p : Syntax.Program) : diag_nilb p = true -> bound_nilb p = false -> outsides p.
Proof.
  intros Hd Hb. destruct (outside_of_nilb p Hd Hb) as [c op]. unfold outsides.
  destruct (compile p) as [c' Hadm | c' Hd' | c' Hd' Hb']; cbn in op; [ destruct op | destruct op | exact I ].
Qed.
