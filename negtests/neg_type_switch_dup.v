(* EXPECT: DUPLICATE case *)
(* A type switch with two IDENTICAL case types (bool, bool) — Go rejects "duplicate case
   in type switch".  Extraction MUST abort (reject_dup_cases): the guard compares the ACTUAL
   emitted case type strings (via go_type_of_tag), so it catches the collision directly —
   with NO assumption that the trusted tag→Go-type bridge is injective.  A regression that
   drops the guard reopens the type-switch fail-open. *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
From Fido Require Import GoEffects.
From Fido Require Import GoSwitch.
Require Import Coq.Lists.List.
Import ListNotations.
Definition neg_dup : IO unit :=
  type_switch2 (any true)
    TBool (fun b => println [any b; any (1)%i64])
    TBool (fun b => println [any b; any (2)%i64])
    (println [any (9)%i64]).
Go Main Extraction neg_out "neg_dup".
