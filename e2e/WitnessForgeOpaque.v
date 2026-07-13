(** Negative fixture for the PROVENANCE closure check — the OPAQUE-Qed case.  The provenance proof is a
    lemma CLOSED WITH Qed (so its proof body is opaque), and that body depends on axioms.  `Print
    Assumptions` machinery descends opaque proof bodies via the indirect accessor; this fixture proves the
    emit-time check does the same — it finds the axioms behind the Qed and rejects the image before any
    filesystem effect.  (The genuine witness in Witness.v also carries a Qed/opaque lemma — [demo_valid] —
    that is axiom-free, and IS accepted, so this is exactly the descent discriminating good from bad.) *)
From Stdlib Require Import List String.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition forged_map : fmap FilePath string :=
  fm_singleton (mkFP "main.go" eq_refl) "forged uncertified bytes"%string.

Axiom hidden_sp : SafeProgram.
Axiom hidden_eq : forged_map = render_map hidden_sp.
Lemma opaque_prov : exists sp, forged_map = render_map sp.
Proof. exists hidden_sp. exact hidden_eq. Qed.   (* Qed ⇒ opaque body; it references the two axioms *)

Declare ML Module "fido.emit".
Fido Emit (mkImage forged_map opaque_prov) To "/workspace/e2e-forge-opaque".
