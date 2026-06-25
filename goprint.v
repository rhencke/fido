(** ============================================================================
    THE VERIFIED PRINTER — slice 1 (the gap #10 / review #12 path).

    The trusted/unverified part of Fido is the hand-written OCaml in [plugin/go.ml]: no theorem relates
    the Go string it emits to the source term.  The agreed fix (no more raw OCaml): the PRINTER moves
    INTO Rocq — a Go AST + a pretty-printer defined here as Rocq functions — is EXTRACTED to OCaml (so
    the plugin runs the SAME function Rocq reasons about, not a hand-written re-implementation), and
    CORRECTNESS theorems are layered atop it.  This file is the foundation; later slices grow the AST to
    cover the emitted fragment, rewire [go.ml] to call the extracted printer, and delete the raw OCaml.

    Slice 1: the Go TYPE sub-language.  [print_ty] renders a [GoTy] to Go source; [print_ty_inj] proves
    it is INJECTIVE on the structural fragment — distinct Go types render to distinct strings, so the
    printer can NEVER conflate two types (the property every [v.(T)] cast / tag rendering depends on).
    [Extraction "printer.ml"] emits the OCaml the plugin will call. *)

From Stdlib Require Import String List Ascii.
Import ListNotations.
Open Scope string_scope.

(** A Go type, as the plugin renders them: the four no-import scalars, pointers, slices, and a nominal
    (named) type [GTNamed "Cell"]. *)
Inductive GoTy : Type :=
  | GTInt64   : GoTy
  | GTBool    : GoTy
  | GTString  : GoTy
  | GTFloat64 : GoTy
  | GTPtr     : GoTy -> GoTy
  | GTSlice   : GoTy -> GoTy
  | GTNamed   : string -> GoTy.

(** The pretty-printer: a Go type to its source text. *)
Fixpoint print_ty (t : GoTy) : string :=
  match t with
  | GTInt64   => "int64"
  | GTBool    => "bool"
  | GTString  => "string"
  | GTFloat64 => "float64"
  | GTPtr u   => "*"  ++ print_ty u
  | GTSlice u => "[]" ++ print_ty u
  | GTNamed n => n
  end.

(** STRUCTURAL = no nominal [GTNamed] anywhere (a named type can legally shadow a built-in's rendering
    — Go forbids it too — so injectivity is stated on the shadow-free fragment). *)
Fixpoint structural (t : GoTy) : bool :=
  match t with
  | GTNamed _ => false
  | GTPtr u   => structural u
  | GTSlice u => structural u
  | _         => true
  end.

(** FAITHFULNESS — the type printer is INJECTIVE on the structural fragment: two structural Go types
    that print to the same string ARE the same type.  So the emitted type text never conflates [int64]
    with [bool], [*int64] with [[]int64], etc. — the first verified property of the verified printer. *)
Theorem print_ty_inj : forall t1 t2,
  structural t1 = true -> structural t2 = true -> print_ty t1 = print_ty t2 -> t1 = t2.
Proof.
  induction t1 as [ | | | | u IHu | u IHu | n ];
    intros [ | | | | v | v | m ] H1 H2 He; cbn in *;
    try reflexivity; try discriminate.
  - (* GTPtr u vs GTPtr v *) injection He as He'. f_equal. apply IHu; assumption.
  - (* GTSlice u vs GTSlice v *) injection He as He'. f_equal. apply IHu; assumption.
Qed.

(** Extract the Rocq printer to the OCaml the plugin will call (slice 2 wires [go.ml] to it). *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty.
