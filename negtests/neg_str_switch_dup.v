(* EXPECT: DUPLICATE case *)
(* A STRING expression switch with two IDENTICAL case values ("a", "a") — Go rejects
   "duplicate case in switch".  This pins the VALUE-based key: the guard decodes each string
   case to its exact byte list (decode_go_string) and compares bytes, so a string-value
   collision is caught independent of how the literal is rendered/escaped.  A regression to a
   rendered-text comparison would risk missing value-equal-but-differently-escaped cases. *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
From Fido Require Import GoEffects.
From Fido Require Import GoString.
From Fido Require Import GoSwitch.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Definition neg_dup : IO unit :=
  str_switch2 "x"%string
    "a"%string (println [any (1)%i64])
    "a"%string (println [any (2)%i64])
    (println [any (9)%i64]).
Go Main Extraction neg_out "neg_dup".
