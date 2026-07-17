(** The empty-program witness (contract §24): a valid [ModuleSpec] with an EMPTY source-file map is a
    valid program — a generated Go module containing only `go.mod` and no packages.  Kernel facts: the
    empty program builds, is [ProgValid], compiles ([go_compile] accepts), certifies to a [SafeProgram],
    and renders to an image whose go.mod is present and whose `.go` file map is EMPTY.  Emitted by the
    GENERAL Fido Emit transport; the e2e then runs `go build ./...` over the module (zero packages is
    accepted). *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath FMap ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition empty_module : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated" eq_refl) Go1_23.
Definition empty_prog : GoProgram := empty_program empty_module.

Lemma empty_valid : ProgValid empty_prog.
Proof. apply prog_ok_iff. reflexivity. Qed.

Definition empty_compiled : CompilableProgram :=
  mkCompilable empty_prog empty_valid.
Definition empty_safe : SafeProgram := certify empty_compiled.

(* the empty source map builds, compiles, and renders NO .go files *)
Example empty_builds : exists p, build_program empty_module [] = Some p.
Proof. eexists; reflexivity. Qed.
Example empty_compiles : exists cp, go_compile empty_prog = Ok cp.
Proof. eexists; reflexivity. Qed.
Example empty_no_go_files : di_go_file_entries (render_program empty_safe) = [].
Proof. reflexivity. Qed.

Declare ML Module "fido.emit".
Fido Emit (render_program empty_safe) To "/workspace/e2e-empty".
