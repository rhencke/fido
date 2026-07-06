(* EXPECT: model/printer-only decimal authority *)
(* The shared [Fido.digits] module is suppressed from Go emission (its decls exist for the
   model's exact panic payloads and the verified printer's extraction).  A LIVE reference
   in emitted code would print an UNDEFINED Go identifier — the plugin must abort. *)
From Fido Require Import preamble digits.
From Fido Require Import GoRuntimeTypes.
From Stdlib Require Import ZArith String.
Definition neg_bad : GoString := print_Z 5%Z.
Go Main Extraction neg_out "neg_bad".
