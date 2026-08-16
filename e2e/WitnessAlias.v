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

Definition alias_valid : Compilable.Admissible (Compilable.elaborate alias_program).
Proof. split; apply Compilable.list_is_nilb_true; vm_compute; reflexivity. Qed.

(* carry the exact compilation and its capability into the certified image *)
Definition alias_cap : Compilable.Prog.Program (Compilable.elaborate alias_program) :=
  Compilable.Prog.issue (Compilable.elaborate alias_program) alias_valid.
Definition alias_safe : Safe.Program := Safe.certify alias_program (Compilable.elaborate alias_program) alias_cap I.
Definition alias_image : Emit.Image := Emit.of_safe alias_safe.

Declare ML Module "fido.emit".
Fido Materialize alias_image To "/workspace/generated-alias".
(* the witness materializes only, and this tree is never the canonical published image *)
