(** Negative fixture for the PROVENANCE closure check — the TRANSITIVE section-variable case.  The
    provenance proof is a section [Variable] reached INDIRECTLY through a section-local definition, so the
    submitted term (the bare name [forged_indirect]) contains NO direct [VarRef]; the up-front direct-
    variable check does not fire.  The variable is discovered only by [Assumptions.assumptions] descending
    [forged_indirect]'s body, and rejected via the [Printer.Variable] arm — before any filesystem effect.
    (WitnessForgeVar.v covers the direct case.) *)
From Stdlib Require Import List String.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition forged_map : fmap FilePath string :=
  fm_singleton (mkFP "main.go" eq_refl) "forged uncertified bytes"%string.

Declare ML Module "fido.emit".

Section Forge.
  Variable v_prov : exists sp, forged_map = render_map sp.
  Definition forged_indirect : DirectoryImage := mkImage forged_map v_prov.
  (* the submitted term is the NAME forged_indirect (no direct VarRef); assumptions must descend its body
     to find the section variable and reject via the Printer.Variable arm. *)
  Fido Emit forged_indirect To "/workspace/e2e-forge-var-indirect".
End Forge.
