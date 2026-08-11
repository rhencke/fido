(* The byte and rune alias differential: the accepted conversions, rendered in their source spellings. *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import FilePath ModulePath Version Names Syntax Compilable Safe Render Emit.
Import ListNotations.

Local Notation PL args := (Syntax.ExprStmt (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PPrintln)) args)).
Local Notation CONV t e := (Syntax.Application (Syntax.Name (Names.predeclared_ordinary t)) [e]).
Local Notation ILIT n := (Syntax.LiteralExpr (Syntax.IntegerLiteral n)).
Local Notation NEG e := (Syntax.Unary Syntax.UnaryMinus e).

Definition alias_file : list Syntax.TopLevelDecl :=
  [ Syntax.Main (Syntax.MakeBlock
    [ PL [ CONV Names.PByte  (ILIT 0)
         ; CONV Names.PByte  (ILIT 255)
         ; CONV Names.PUint8 (ILIT 255)
         ; CONV Names.PRune  (NEG (ILIT 2147483648))
         ; CONV Names.PRune  (ILIT 2147483647)
         ; CONV Names.PInt32 (NEG (ILIT 2147483648))
         ; CONV Names.PInt32 (ILIT 2147483647) ] ]) ].
Definition alias_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition alias_program : Syntax.Program := singleton_program alias_module (FilePath.Make "main.go" eq_refl) alias_file.

Definition alias_valid : Compilable.Admissible alias_program.
Proof. split; vm_compute; reflexivity. Qed.

Definition alias_compiled : Compilable.Program :=
  Compilable.program_of alias_program alias_valid.
Definition alias_safe : Safe.Program := certify alias_compiled I.
Definition alias_image : Emit.Image :=
  Emit.of_safe_at alias_safe alias_program
    (eq_trans (Safe.certify_source alias_compiled I) (Compilable.program_of_source alias_program alias_valid)).

Declare ML Module "fido.emit".
Fido Materialize alias_image To "/workspace/generated-alias".
(* the witness materializes only, and this tree is never the canonical published image *)
