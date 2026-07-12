(** ============================================================================
    Ints — the ONE integer-width authority.  Project scope is the Go 1 language surface on modern
    64-bit targets: signed [int] is 64-bit.  There is NO TargetConfig and no parameterization by Go
    point release, GOOS, GOARCH, or word size — that abstraction tax is not paid until 32-bit support
    is deliberately chosen in a future reviewed milestone.  The external integration build still pins
    an actual Go toolchain operationally (Dockerfile/Makefile); that pin is not threaded through the
    theorems.  Only the constants an admitted construct actually uses live here (the AST has only signed
    int literals today — a [uint] bound is not declared until a [uint] construct exists).  No file may
    silently use a different int width — use these constants.
    ============================================================================ *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition int_min : Z := - 2 ^ 63.
Definition int_max : Z := 2 ^ 63 - 1.

Lemma int_min_val : int_min = -9223372036854775808. Proof. reflexivity. Qed.
Lemma int_max_val : int_max =  9223372036854775807. Proof. reflexivity. Qed.
