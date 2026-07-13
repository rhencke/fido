(** Negative fixture for the PROVENANCE closure check — the SECTION-VARIABLE case.  The provenance proof
    is a section [Variable] (a local assumption), so the image is well-typed inside the section but its
    assumption closure contains a section variable.  The emit-time check rejects it — this exercises the
    [Printer.Variable] arm of the guard, independently of the [Axiom] arm — before any filesystem effect. *)
From Stdlib Require Import List String.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition forged_map : fmap FilePath string :=
  fm_singleton (mkFP "main.go" eq_refl) "forged uncertified bytes"%string.

Declare ML Module "fido.emit".

Section Forge.
  Variable v_prov : exists sp, forged_map = render_map sp.
  (* well-typed image (v_prov discharges di_prov), but its closure is a section variable: rejected. *)
  Fido Emit (mkImage forged_map v_prov) To "/workspace/e2e-forge-var".
End Forge.
