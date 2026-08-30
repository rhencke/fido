(* The evidence DAG exercised end to end over one compiled root: A, B, their aggregate, and a derived object. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Render Emit.
Import ListNotations.

(* one exact compiled root: a minimal valid module with no source files *)
Definition ev_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition ev_prog : Syntax.Program := empty_program ev_module.
Definition ev_cp : Compilable.Program ev_prog :=
  Compilable.compiled_program ev_prog (ltac:(rewrite Compilable.disposition_observe_data; vm_compute; reflexivity)).

(* EvidenceA / EvidenceB: exact proofs, indexed by the SAME cp, that its diagnostics resp. boundaries are empty *)
Definition EvidenceA {p} (cp : Compilable.Program p) : Prop :=
  Compilable.diagnostics (Compilable.program_compilation cp) = [].
Definition EvidenceB {p} (cp : Compilable.Program p) : Prop :=
  Compilable.boundaries (Compilable.program_compilation cp) = [].
(* Admissible is sealed (opaque); admissible_iff_reports is the exact bridge to the concrete empty-report facts *)
Definition adm_reports {p} (cp : Compilable.Program p) : EvidenceA cp /\ EvidenceB cp :=
  proj1 (Compilable.admissible_iff_reports (Compilable.program_compilation cp)) (Compilable.program_admissible cp).
Definition evA {p} (cp : Compilable.Program p) : EvidenceA cp := proj1 (adm_reports cp).
Definition evB {p} (cp : Compilable.Program p) : EvidenceB cp := proj2 (adm_reports cp).

(* AggregateAB: mandatory exact fields A and B over the SAME cp; the type forbids combining two roots *)
Record AggregateAB {p} (cp : Compilable.Program p) : Type := mk_agg { agg_a : EvidenceA cp ; agg_b : EvidenceB cp }.
Arguments mk_agg {p cp} _ _. Arguments agg_a {p cp} _. Arguments agg_b {p cp} _.
Definition evAgg {p} (cp : Compilable.Program p) : AggregateAB cp := mk_agg (evA cp) (evB cp).

(* DerivedAB: retains the exact aggregate and adds one new theorem (Admissible) derived from its exact fields *)
Record DerivedAB {p} (cp : Compilable.Program p) : Type :=
  mk_der { der_agg : AggregateAB cp ; der_adm : Compilable.Admissible (Compilable.program_compilation cp) }.
Arguments mk_der {p cp} _ _. Arguments der_agg {p cp} _. Arguments der_adm {p cp} _.
Definition evDer {p} (cp : Compilable.Program p) : DerivedAB cp :=
  mk_der (evAgg cp)
         (proj2 (Compilable.admissible_iff_reports (Compilable.program_compilation cp))
                (conj (agg_a (evAgg cp)) (agg_b (evAgg cp)))).

(* the five images over the exact same ev_cp, each carrying its evidence by construction of the type *)
Definition img_base : Emit.Image ev_cp Emit.CompiledOnly tt := Emit.of_compiled ev_cp.
Definition img_A    : Emit.Image ev_cp EvidenceA (evA ev_cp) := Emit.of_evidence.
Definition img_B    : Emit.Image ev_cp EvidenceB (evB ev_cp) := Emit.of_evidence.
Definition img_agg  : Emit.Image ev_cp AggregateAB (evAgg ev_cp) := Emit.of_evidence.
Definition img_der  : Emit.Image ev_cp DerivedAB (evDer ev_cp) := Emit.of_evidence.

(* projection theorems: the aggregate recovers exact A and B; the derived recovers the exact aggregate *)
Lemma agg_recovers_A : agg_a (evAgg ev_cp) = evA ev_cp. Proof. reflexivity. Qed.
Lemma agg_recovers_B : agg_b (evAgg ev_cp) = evB ev_cp. Proof. reflexivity. Qed.
Lemma der_recovers_agg : der_agg (evDer ev_cp) = evAgg ev_cp. Proof. reflexivity. Qed.

(* transport equality: every evidence image transports to exactly the base transport (evidence-independent) *)
Lemma transport_A_eq_base   : Emit.transport img_A   = Emit.transport img_base. Proof. reflexivity. Qed.
Lemma transport_B_eq_base   : Emit.transport img_B   = Emit.transport img_base. Proof. reflexivity. Qed.
Lemma transport_agg_eq_base : Emit.transport img_agg = Emit.transport img_base. Proof. reflexivity. Qed.
Lemma transport_der_eq_base : Emit.transport img_der = Emit.transport img_base. Proof. reflexivity. Qed.

Declare ML Module "fido.emit".
Fido Materialize img_base To "/workspace/ev-base".
Fido Materialize img_A    To "/workspace/ev-a".
Fido Materialize img_B    To "/workspace/ev-b".
Fido Materialize img_agg  To "/workspace/ev-agg".
Fido Materialize img_der  To "/workspace/ev-der".
(* the five images all materialize identically; the emit stage byte-compares the five pristine trees *)
