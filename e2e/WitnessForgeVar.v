(** Negative fixture for the PROVENANCE closure check — the DIRECT section-variable case.  The provenance
    proof is a section [Variable] appearing DIRECTLY in the submitted term, so its [VarRef] is caught by
    the emit command's up-front direct-variable check (before the [Assumptions] pass).  This exercises
    that up-front check; WitnessForgeVarIndirect.v covers the transitive [Printer.Variable] arm.  Rejected
    before any filesystem effect; the target is never created. *)
From Stdlib Require Import List String.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition forged_map : fmap FilePath string :=
  fm_singleton (mkFP "main.go" eq_refl) "forged uncertified bytes"%string.

Declare ML Module "fido.emit".

Section Forge.
  Variable v_prov : exists sp, forged_map = render_map sp.
  (* v_prov appears DIRECTLY in the emitted term -> caught by the up-front direct-variable check. *)
  Fido Emit (mkImage forged_map v_prov) To "/workspace/e2e-forge-var".
End Forge.
