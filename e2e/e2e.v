(** Minimal END-TO-END SMOKE TEST (NOT a certified-emission or compiler-soundness claim).  Builds one known
    Go program AST, prints it with the surviving [print_program], and extracts those closed bytes; the build
    then confirms the pinned Go toolchain accepts them (gofmt-clean + go build + go vet).  It exercises the
    printer end to end (Rocq -> extraction -> OCaml -> .go -> Go toolchain) for THIS one program only. *)
From Fido Require Import GoAst GoPrint.
From Stdlib Require Import String ZArith List Extraction ExtrOcamlNativeString.
Import ListNotations. Open Scope string_scope.
Definition e2e_main    : Ident := mkIdent "main" eq_refl.
Definition e2e_println : Ident := mkIdent "println" eq_refl.
Definition e2e_program : Program :=
  mkProgram e2e_main [GsExprStmt (ECall (EId e2e_println) [EInt 1]); GsReturn].
Definition e2e_bytes : string := print_program e2e_program.
(* the exact printed bytes are Rocq-checked here (reflexivity), so extraction cannot silently diverge *)
Example e2e_bytes_val : e2e_bytes = "package main" ++ String (Ascii.ascii_of_nat 10) "" ++ String (Ascii.ascii_of_nat 10) "" ++ "func main() {" ++ String (Ascii.ascii_of_nat 10) "" ++ String (Ascii.ascii_of_nat 9) "" ++ "println(1)" ++ String (Ascii.ascii_of_nat 10) "" ++ String (Ascii.ascii_of_nat 9) "" ++ "return" ++ String (Ascii.ascii_of_nat 10) "" ++ "}" ++ String (Ascii.ascii_of_nat 10) "".
Proof. reflexivity. Qed.
Extraction Language OCaml.
Set Extraction Output Directory "e2e".
Extraction "e2e.ml" e2e_bytes.
