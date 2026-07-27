(** The Go language version a module declares: a program fact, not environment configuration. *)
From Stdlib Require Import String.
Open Scope string_scope.

Inductive Version : Type :=
| Go1_23.

(** The `go` directive value: no leading `v`, no patch component. *)
Definition render (v : Version) : string :=
  match v with Go1_23 => "1.23" end.

(** The exact rendered spelling, kernel-pinned. *)
Lemma render_go1_23 : render Go1_23 = "1.23".
Proof. reflexivity. Qed.

Definition equalb (a b : Version) : bool :=
  match a, b with Go1_23, Go1_23 => true end.

Lemma equalb_spec : forall a b, equalb a b = true <-> a = b.
Proof. intros [] []; simpl; split; reflexivity. Qed.
