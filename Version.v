(** Version — the module-declared Go LANGUAGE version, an intrinsic SEMANTIC program fact (the `go`
    directive of the generated `go.mod`), NOT environment configuration and NOT a raw string.  It is
    deliberately a SINGLETON today: exactly [Go1_23], rendered `1.23`.

    Adding any later constructor (e.g. `Go1_24`) is itself a reviewed SEMANTIC milestone: it requires
    formal treatment of every relevant language/compiler difference for the represented AST, rendering
    support, and differential fixtures under the matching pinned toolchain — never silent reuse of the
    Go1_23 semantics if behaviour changed.  The exact compiler binary / toolchain pin is operational and
    lives OUTSIDE this type (Dockerfile/Makefile), not threaded through the theorems. *)
From Stdlib Require Import String.
Open Scope string_scope.

Inductive Version : Type :=
| Go1_23.

(** The canonical `go` directive value (no leading `v`, no patch component). *)
Definition render (v : Version) : string :=
  match v with Go1_23 => "1.23" end.

(** The exact rendered spelling, kernel-pinned. *)
Lemma render_go1_23 : render Go1_23 = "1.23".
Proof. reflexivity. Qed.

Definition equalb (a b : Version) : bool :=
  match a, b with Go1_23, Go1_23 => true end.

Lemma equalb_spec : forall a b, equalb a b = true <-> a = b.
Proof. intros [] []; simpl; split; reflexivity. Qed.
