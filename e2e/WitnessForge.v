(** Negative fixture for the PROVENANCE closure check.  A forged image: an arbitrary map paired with an
    AXIOMATIC provenance proof.  It typechecks as a DirectoryImage ([di_prov] is discharged by the
    axiom), so the type boundary alone would accept it — but `Fido Emit` inspects the term's assumption
    closure and refuses to emit anything that depends on an axiom/assumption.  So this forged, otherwise-
    reducible image is rejected BEFORE any filesystem effect, and its target is never created. *)
From Stdlib Require Import List String.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition forged_map : fmap FilePath string :=
  fm_singleton (mkFP "main.go" eq_refl) "forged uncertified bytes"%string.
Axiom forged_prov : exists sp, forged_map = render_map sp.
Definition forged : DirectoryImage := mkImage forged_map forged_prov.

Declare ML Module "fido.emit".
(* NO [Fail] wrapper: we WANT `rocq c` to error here so the emit stage can verify the rejection REASON
   (the assumption-closure check) from the printed message and confirm the target was never created.
   Rocq's [Fail] absorbs the error message silently in batch mode, which would leave the reason unchecked. *)
Fido Emit forged To "/workspace/e2e-forge".
