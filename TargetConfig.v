(** ============================================================================
    TargetConfig — the ONE authority for pinned target facts (checkpoint-66 root 1).

    Every target-dependent fact the slice uses (int width, target identity, whether the
    bootstrapping builtin [println] exists) is a field HERE and is consumed by derivation —
    never restated in the printer, the elaborator, or a test.  The Go toolchain IMAGE
    (digest) is a build pin and lives in the Makefile; [tc_go_version]/[tc_goos]/[tc_goarch]
    name the language/target the integration goldens are facts ABOUT.

    [println] is Go's BOOTSTRAPPING builtin: the spec does not guarantee it stays in the
    language and its exact output formatting is implementation-specific.  [tc_println_builtin]
    records that the pinned target provides it; no portable text-formatting theorem is ever
    claimed (the runtime golden is pinned-toolchain integration evidence only).
    ============================================================================ *)
From Stdlib Require Import String ZArith.
Open Scope Z_scope.

Record TargetConfig : Type := mkTargetConfig {
  tc_go_version     : string;  (* language version the pinned toolchain implements *)
  tc_goos           : string;
  tc_goarch         : string;
  tc_int_bits       : Z;       (* width of Go [int] on this target *)
  tc_println_builtin : bool    (* the bootstrapping builtin [println] exists on this target *)
}.

(** The one pinned target instance. *)
Definition target : TargetConfig := {|
  tc_go_version      := "go1.23"%string;
  tc_goos            := "linux"%string;
  tc_goarch          := "amd64"%string;
  tc_int_bits        := 64;
  tc_println_builtin := true
|}.

(** Exact bounds of Go [int] on the pinned target, DERIVED from the one width field. *)
Definition int_min : Z := - 2 ^ (tc_int_bits target - 1).
Definition int_max : Z := 2 ^ (tc_int_bits target - 1) - 1.

Lemma int_min_val : int_min = -9223372036854775808. Proof. reflexivity. Qed.
Lemma int_max_val : int_max =  9223372036854775807. Proof. reflexivity. Qed.
Lemma println_supported : tc_println_builtin target = true. Proof. reflexivity. Qed.
