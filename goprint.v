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

From Stdlib Require Import String List Ascii ZArith Lia.
Import ListNotations.
Open Scope string_scope.

(** A Go type, as the plugin renders them.  Note [GTInt] (Go's platform [int], the [GoInt]/[TInt64]
    tag) is DISTINCT from [GTInt64] (the full-width [int64], the [GoI64]/[TI64] tag) — conflating them
    is exactly the kind of bug the verified printer rules out (it caught one in the first integration). *)
Inductive GoTy : Type :=
  | GTInt     : GoTy
  | GTInt64   : GoTy
  | GTBool    : GoTy
  | GTString  : GoTy
  | GTFloat64 : GoTy
  | GTFloat32 : GoTy
  | GTUint    : GoTy
  | GTU8      : GoTy
  | GTI8      : GoTy
  | GTU16     : GoTy
  | GTI16     : GoTy
  | GTU32     : GoTy
  | GTI32     : GoTy
  | GTU64     : GoTy
  | GTPtr     : GoTy -> GoTy
  | GTSlice   : GoTy -> GoTy
  | GTChan    : GoTy -> GoTy
  | GTMap     : GoTy -> GoTy -> GoTy
  | GTNamed   : string -> GoTy.

(** The pretty-printer: a Go type to its source text. *)
Fixpoint print_ty (t : GoTy) : string :=
  match t with
  | GTInt     => "int"
  | GTInt64   => "int64"
  | GTBool    => "bool"
  | GTString  => "string"
  | GTFloat64 => "float64"
  | GTFloat32 => "float32"
  | GTUint    => "uint"
  | GTU8      => "uint8"
  | GTI8      => "int8"
  | GTU16     => "uint16"
  | GTI16     => "int16"
  | GTU32     => "uint32"
  | GTI32     => "int32"
  | GTU64     => "uint64"
  | GTPtr u   => "*"  ++ print_ty u
  | GTSlice u => "[]" ++ print_ty u
  | GTChan u  => "chan " ++ print_ty u
  | GTMap k v => "map[" ++ print_ty k ++ "]" ++ print_ty v
  | GTNamed n => n
  end.

(** STRUCTURAL = no nominal [GTNamed] anywhere (a named type can legally shadow a built-in's rendering
    — Go forbids it too — so injectivity is stated on the shadow-free fragment). *)
Fixpoint structural (t : GoTy) : bool :=
  match t with
  | GTNamed _  => false
  | GTMap _ _  => false   (* maps are EXCLUDED from the injectivity fragment for now: the "]" between
                             key and value clashes with "[]" slices, so unambiguity needs balanced-
                             bracket reasoning — a later proof slice (the RENDERING is already verified). *)
  | GTPtr u    => structural u
  | GTSlice u  => structural u
  | GTChan u   => structural u
  | _          => true
  end.

(** FAITHFULNESS — the type printer is INJECTIVE on the structural fragment: two structural Go types
    that print to the same string ARE the same type.  So the emitted type text never conflates [int64]
    with [bool], [*int64] with [[]int64], etc. — the first verified property of the verified printer. *)
Theorem print_ty_inj : forall t1 t2,
  structural t1 = true -> structural t2 = true -> print_ty t1 = print_ty t2 -> t1 = t2.
Proof.
  induction t1 as [ | | | | | | | | | | | | | | u IHu | u IHu | u IHu | k IHk v IHv | n ];
    intros t2 H1 H2 He; destruct t2; cbn in *;
    try reflexivity; try discriminate.
  (* the three composite cases (ptr/slice/chan) — peel the constant prefix, recurse via the IH;
     maps are killed by [structural _ = false] in H1/H2 (discriminate above) *)
  all: repeat (injection He as He); f_equal; apply IHu; assumption.
Qed.

(** PRINT-PARSE ROUND-TRIP — the deeper faithfulness: a PARSER recovers the type from its printed
    text.  So the type printer is not just injective but UNAMBIGUOUSLY DECODABLE — the emitted text
    denotes exactly the source type, no information lost or aliased (the verified-printer milestone,
    here for the type sub-language; maps/named are out of the structural fragment as for injectivity). *)
Fixpoint strip (p s : string) : option string :=
  match p with
  | EmptyString  => Some s
  | String pc p' => match s with
                    | String sc s' => if Ascii.eqb pc sc then strip p' s' else None
                    | EmptyString  => None
                    end
  end.

(** Keyword scalars — LONGEST first (so [int8] is read before [int], etc.). *)
Definition kw_match (s : string) : option (GoTy * string) :=
  match strip "int64" s   with Some r => Some (GTInt64, r)   | None =>
  match strip "int32" s   with Some r => Some (GTI32, r)     | None =>
  match strip "int16" s   with Some r => Some (GTI16, r)     | None =>
  match strip "int8" s    with Some r => Some (GTI8, r)      | None =>
  match strip "int" s     with Some r => Some (GTInt, r)     | None =>
  match strip "uint64" s  with Some r => Some (GTU64, r)     | None =>
  match strip "uint32" s  with Some r => Some (GTU32, r)     | None =>
  match strip "uint16" s  with Some r => Some (GTU16, r)     | None =>
  match strip "uint8" s   with Some r => Some (GTU8, r)      | None =>
  match strip "uint" s    with Some r => Some (GTUint, r)    | None =>
  match strip "bool" s    with Some r => Some (GTBool, r)    | None =>
  match strip "string" s  with Some r => Some (GTString, r)  | None =>
  match strip "float64" s with Some r => Some (GTFloat64, r) | None =>
  match strip "float32" s with Some r => Some (GTFloat32, r) | None =>
  None end end end end end end end end end end end end end end.

Fixpoint parse_ty (fuel : nat) (s : string) : option (GoTy * string) :=
  match fuel with
  | O   => None
  | S f =>
    match strip "*" s with
    | Some r => match parse_ty f r with Some (u, r') => Some (GTPtr u, r') | None => None end
    | None =>
    match strip "[]" s with
    | Some r => match parse_ty f r with Some (u, r') => Some (GTSlice u, r') | None => None end
    | None =>
    match strip "chan " s with
    | Some r => match parse_ty f r with Some (u, r') => Some (GTChan u, r') | None => None end
    | None => kw_match s
    end end end
  end.

Fixpoint ty_depth (t : GoTy) : nat :=
  match t with
  | GTPtr u | GTSlice u | GTChan u => S (ty_depth u)
  | GTMap a b => S (Nat.max (ty_depth a) (ty_depth b))
  | _ => O
  end.

Theorem parse_print_ty : forall t f,
  structural t = true -> ty_depth t < f -> parse_ty f (print_ty t) = Some (t, ""%string).
Proof.
  induction t as [ | | | | | | | | | | | | | | u IH | u IH | u IH | a IHa b IHb | n ];
    intros f Hs Hf; try (cbn in Hs; discriminate Hs);
    destruct f as [ | f ]; cbn in Hf; try lia;
    try reflexivity.
  - (* GTPtr u *)  cbn in *. rewrite (IH f Hs ltac:(lia)). reflexivity.
  - (* GTSlice u *) cbn in *. rewrite (IH f Hs ltac:(lia)). reflexivity.
  - (* GTChan u *) cbn in *. rewrite (IH f Hs ltac:(lia)). reflexivity.
Qed.

(** ---- INTEGER LITERALS ---- the decimal rendering of a [Z] value (replacing go.ml's raw
    [Printf.sprintf "%Ld"/"%Lu"]).  Magnitude is carried by [Z], so this is faithful for the FULL
    int64 AND uint64 ranges (the unsigned [2^63,2^64) values that wrap as a negative [Int64.t] are
    just large [Zpos] here — no special-casing). *)
Definition dec_digit (n : nat) : ascii := ascii_of_nat (48 + n).
Fixpoint z_digits (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O    => acc
  | S f  => let d := dec_digit (Z.to_nat (z mod 10)) in
            if (z / 10 =? 0)%Z then String d acc
            else z_digits f (z / 10)%Z (String d acc)
  end.
Definition print_Z (z : Z) : string :=
  if (z =? 0)%Z then "0"
  else if (z <? 0)%Z then ("-" ++ z_digits 64 (- z) "")%string
  else z_digits 64 z "".

(** Computational checks: the decimal printer is correct on samples spanning the int64/uint64 range
    (incl. the unsigned value [2^63] that an [Int64.t]-based printer renders only via [%Lu]). *)
Example print_Z_0    : print_Z 0 = "0".                                       Proof. reflexivity. Qed.
Example print_Z_42   : print_Z 42 = "42".                                     Proof. reflexivity. Qed.
Example print_Z_neg  : print_Z (-7) = "-7".                                   Proof. reflexivity. Qed.
Example print_Z_imax : print_Z 9223372036854775807 = "9223372036854775807".  Proof. reflexivity. Qed.
Example print_Z_u63  : print_Z 9223372036854775808 = "9223372036854775808".  Proof. reflexivity. Qed.

(** ---- STRING LITERALS ---- escape a Go double-quoted string literal (replacing go.ml's raw
    [go_string_lit]): wrap in dquotes, escape dquote/backslash/newline/tab/CR, pass printable ASCII
    through, and emit a hex escape (backslash-x, lowercase, 2 digits) for everything else.  ASCII
    codes: 34 dquote, 92 backslash, 10 newline, 9 tab, 13 CR, 110 n, 116 t, 114 r, 120 x. *)
Definition ch (n : nat) : ascii := ascii_of_nat n.
Definition hexdig (n : nat) : ascii := ascii_of_nat (if Nat.ltb n 10 then 48 + n else 87 + n).
Definition esc_byte (b : nat) (acc : string) : string :=
  if Nat.eqb b 34 then String (ch 92) (String (ch 34) acc)
  else if Nat.eqb b 92 then String (ch 92) (String (ch 92) acc)
  else if Nat.eqb b 10 then String (ch 92) (String (ch 110) acc)
  else if Nat.eqb b 9  then String (ch 92) (String (ch 116) acc)
  else if Nat.eqb b 13 then String (ch 92) (String (ch 114) acc)
  else if andb (Nat.leb 32 b) (Nat.ltb b 127) then String (ch b) acc
  else String (ch 92) (String (ch 120)
         (String (hexdig (Nat.div b 16)) (String (hexdig (Nat.modulo b 16)) acc))).
Fixpoint esc_string (s : string) : string :=
  match s with
  | EmptyString   => EmptyString
  | String c rest => esc_byte (nat_of_ascii c) (esc_string rest)
  end.
Definition print_string_lit (s : string) : string :=
  String (ch 34) (esc_string s ++ String (ch 34) EmptyString).

Example psl_empty : print_string_lit "" = String (ch 34) (String (ch 34) ""). Proof. reflexivity. Qed.
Example psl_fido  : print_string_lit "fido" = String (ch 34) ("fido" ++ String (ch 34) ""). Proof. reflexivity. Qed.

(** ---- HEX LITERALS ---- [0x]-prefixed lowercase hex (replacing go.ml's [Printf.sprintf "0x%x"] for
    fixed-width bit masks / sign bits). *)
Fixpoint hex_digits (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O   => acc
  | S f => let d := hexdig (Z.to_nat (z mod 16)) in
           if (z / 16 =? 0)%Z then String d acc else hex_digits f (z / 16)%Z (String d acc)
  end.
Definition print_hex (z : Z) : string :=
  ("0x" ++ (if (z =? 0)%Z then "0" else hex_digits 64 z ""))%string.
Example ph_ff : print_hex 255 = "0xff". Proof. reflexivity. Qed.
Example ph_0  : print_hex 0   = "0x0".  Proof. reflexivity. Qed.
Example ph_80 : print_hex 128 = "0x80". Proof. reflexivity. Qed.

(** ---- PROOFS ATOP THE PRINTERS ---- WELL-FORMEDNESS: every printer yields a NON-EMPTY string, so no
    emitted token is ever blank (which would be malformed Go).  [print_ty] on the structural fragment,
    and the literal printers unconditionally.  (Injectivity / print-parse round-trip are the deeper
    follow-ups; [print_ty_inj] already covers type injectivity on the structural fragment.) *)
Lemma print_ty_nonempty : forall t, structural t = true -> print_ty t <> ""%string.
Proof. induction t; intro H; cbn in *; try discriminate; intro Hc; discriminate Hc. Qed.
Lemma print_string_lit_nonempty : forall s, print_string_lit s <> ""%string.
Proof. intros s Hc. unfold print_string_lit in Hc. discriminate Hc. Qed.
Lemma print_hex_nonempty : forall z, print_hex z <> ""%string.
Proof. intros z Hc. unfold print_hex in Hc. discriminate Hc. Qed.

(** [z_digits] with a non-empty accumulator stays non-empty; hence [print_Z] is never blank. *)
Lemma z_digits_acc_nonempty : forall fuel z c rest, z_digits fuel z (String c rest) <> ""%string.
Proof.
  induction fuel as [ | f IH ]; intros z c rest; cbn [z_digits]; [ discriminate | ].
  destruct (z / 10 =? 0)%Z; [ discriminate | apply IH ].
Qed.
(* one unfold step, with the fuel kept ABSTRACT (so cbn does not expand all 64 nested levels) *)
Lemma z_digits_first_nonempty : forall f z, z_digits (S f) z ""%string <> ""%string.
Proof.
  intros f z. cbn [z_digits].
  destruct (z / 10 =? 0)%Z; [ discriminate | apply z_digits_acc_nonempty ].
Qed.
Lemma print_Z_nonempty : forall z, print_Z z <> ""%string.
Proof.
  intro z. unfold print_Z.
  destruct (z =? 0)%Z. { discriminate. }
  destruct (z <? 0)%Z.
  - intro Hc. discriminate Hc.            (* "-" ++ … reduces (whnf) to String "-" … *)
  - apply z_digits_first_nonempty.        (* z_digits 64 z "" = z_digits (S 63) z "" *)
Qed.

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex.
