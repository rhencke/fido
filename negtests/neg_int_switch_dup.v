(* EXPECT: DUPLICATE case *)
(* An expression switch with two IDENTICAL case values (5, 5) — Go rejects "duplicate case
   in switch".  Extraction MUST abort (reject_dup_cases): emitting
   `switch x { case 5:… case 5:… }` is invalid Go, a fail-OPEN caught only at `go build`.
   The guard compares the ACTUAL emitted case strings, so it needs no assumption about how a
   value renders.  A regression that drops the guard reopens the switch fail-open. *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
From Fido Require Import GoEffects.
From Fido Require Import GoSwitch.
Require Import Coq.Lists.List.
Import ListNotations.
Definition neg_dup : IO unit :=
  int_switch2 (7)%i64
    (5)%i64 (println [any (1)%i64])
    (5)%i64 (println [any (2)%i64])
    (println [any (9)%i64]).
Go Main Extraction neg_out "neg_dup".
