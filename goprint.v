(** ============================================================================
    THE VERIFIED PRINTER — slice 1 (the gap #10 / review #12 path).

    The trusted/unverified part of Fido is the hand-written OCaml in [plugin/go.ml]: no theorem relates
    the Go string it emits to the source term.  The agreed fix (no more raw OCaml): the PRINTER moves
    INTO Rocq — a Go AST + a pretty-printer defined here as Rocq functions — is EXTRACTED to OCaml (so
    the plugin runs the SAME function Rocq reasons about, not a hand-written re-implementation), and
    CORRECTNESS theorems are layered atop it.  This file is the foundation; later slices grow the AST to
    cover the emitted fragment, rewire [go.ml] to call the extracted printer, and delete the raw OCaml.

    Slice 1: the Go TYPE sub-language.  [print_ty] renders a [GoTy] to Go source; [print_ty_inj] proves
    it is INJECTIVE over ALL of [GoTy] unconditionally (nominal names carry a validated [Ident], so an
    invalid name is unrepresentable) — distinct Go types render to distinct strings, so the printer can
    NEVER conflate two types (the property every [v.(T)] cast / tag rendering depends on).
    [Extraction "printer.ml"] emits the OCaml the plugin will call. *)

From Stdlib Require Import String List Ascii ZArith Lia Bool Eqdep_dec.
Import ListNotations.
Open Scope string_scope.

(** ---- IDENTIFIER VALIDITY (for nominal [GTNamed] types) ---- a Go identifier is [_A-Za-z][_A-Za-z0-9]*.
    These come BEFORE [GoTy] because [GTNamed] carries a VALIDATED identifier ([Ident], a [sig]): the
    validity is part of the TYPE, so an invalid nominal name (a keyword, or non-identifier text) is
    UNREPRESENTABLE — not merely excluded by a side-condition theorem.  The would-be cycle ([valid_ident]
    must reject type keywords, but the keyword→[GoTy] map [classify] needs [GoTy]) is broken by factoring
    out [is_type_keyword]: the keyword SET is just strings, independent of [GoTy]; [classify] (below
    [GoTy]) reuses that set to assign each keyword its type. *)
Definition is_idc (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (andb (Nat.leb 48 n) (Nat.leb n 57)) (andb (Nat.leb 65 n) (Nat.leb n 90)))
      (orb (andb (Nat.leb 97 n) (Nat.leb n 122)) (Nat.eqb n 95)).
Definition is_idstart (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (andb (Nat.leb 65 n) (Nat.leb n 90)) (andb (Nat.leb 97 n) (Nat.leb n 122))) (Nat.eqb n 95).
Fixpoint all_idc (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (is_idc c) (all_idc s') end.
(** Two [GoTy]-independent STRING keyword sets (so they gate the identifier predicates ahead of [GoTy]):
    [is_type_keyword] is the 14 builtin scalar type names + [chan]/[map] (used for parser invertibility);
    [go_keyword] is Go's 25 RESERVED WORDS — so an identifier is never a keyword ([func]/[return]/[var]/
    [type]/[struct]/[interface]/[select]/… are rejected, which the old [valid_ident] wrongly accepted). *)
Definition is_type_keyword (s : string) : bool :=
  existsb (String.eqb s)
    ["int64"; "int32"; "int16"; "int8"; "int"; "uint64"; "uint32"; "uint16"; "uint8"; "uint";
     "bool"; "string"; "float64"; "float32"; "chan"; "map"].
Definition go_keyword (s : string) : bool :=
  existsb (String.eqb s)
    ["break"; "case"; "chan"; "const"; "continue"; "default"; "defer"; "else"; "fallthrough"; "for";
     "func"; "go"; "goto"; "if"; "import"; "interface"; "map"; "package"; "range"; "return";
     "select"; "struct"; "switch"; "type"; "var"].
(** A Go IDENTIFIER (for an [AIdent] atom): non-empty, [_A-Za-z]-led, all identifier chars, and NOT a Go
    keyword.  A builtin type name like [int]/[string] IS a valid identifier (predeclared, shadowable —
    Go allows [var int = 5]), so [go_ident] ACCEPTS it; only [nominal_type_ident] rejects it. *)
Definition go_ident (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c _  => andb (andb (is_idstart c) (all_idc s)) (negb (go_keyword s))
  end.
(** A NOMINAL TYPE NAME (for a [GTNamed] tag): a [go_ident] that is additionally not a builtin type name
    (nor [chan]/[map] — those are keywords) — so it print-parses back as [GTNamed], never as a scalar /
    chan / map.  This is the parser-INVERTIBILITY refinement; [nominal_type_ident s -> go_ident s]. *)
Definition nominal_type_ident (s : string) : bool := andb (go_ident s) (negb (is_type_keyword s)).
(** The two validity-carrying sig types (validity IN THE TYPE — invalid names unrepresentable; both
    extract to a bare [string], the proof erased): [Ident] for expression identifiers ([AIdent]),
    [TyName] for nominal type names ([GTNamed]). *)
Definition Ident : Type := { s : string | go_ident s = true }.
Definition mkIdent (s : string) (H : go_ident s = true) : Ident := exist _ s H.
Definition TyName : Type := { s : string | nominal_type_ident s = true }.
Definition mkTyName (s : string) (H : nominal_type_ident s = true) : TyName := exist _ s H.

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
  | GTNamed   : TyName -> GoTy.

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
  | GTNamed n => proj1_sig n
  end.

(** FAITHFULNESS — the type printer is INJECTIVE and print-parse-INVERTIBLE over the WHOLE [GoTy], with NO
    side-condition: a nominal [GTNamed] carries an [Ident] (a name validated IN THE TYPE), so an invalid
    name is unrepresentable and the old [valid_ty] hypothesis disappears.  So the emitted type text never
    conflates [int64] with [bool], [*int64] with [[]int64], [map[int]int] with [map[int8]int], or two
    distinct named types — and a named type with a keyword prefix ([int8x]) is never confused with the
    keyword ([int8]), nor can a keyword ([int]) ever appear AS a nominal name.  Both are DERIVED from the
    print-parse round-trip [parse_print_ty] / [print_ty_inj] (now unconditional). *)

(** PRINT-PARSE ROUND-TRIP — the deeper faithfulness: a PARSER recovers the type from its printed
    text.  So the type printer is not just injective but UNAMBIGUOUSLY DECODABLE — the emitted text
    denotes exactly the source type, no information lost or aliased.  Stated in the PREFIX form
    ([parse_ty] consumes exactly [print_ty t], leaving any trailing [rest]) so the cases compose —
    crucially the map case, where the key type is followed by "]" and the value type. *)
Fixpoint strip (p s : string) : option string :=
  match p with
  | EmptyString  => Some s
  | String pc p' => match s with
                    | String sc s' => if Ascii.eqb pc sc then strip p' s' else None
                    | EmptyString  => None
                    end
  end.

(** [scan_id] consumes the maximal run of identifier characters (so it stops at "]", a space, or
    end-of-string — exactly the boundaries [print_ty] places after a type), and [classify] maps a complete
    token to its scalar type (or [None] for a nominal name).  Token-FIRST parsing (scan the run, then
    classify) gives maximal munch for free: "int8x" scans whole and classifies as nominal, never as
    [int8] + "x".  ([is_idc]/[is_idstart]/[all_idc]/[is_type_keyword]/[valid_ident]/[Ident] are defined
    above [GoTy], since [GTNamed] carries an [Ident].) *)
Fixpoint scan_id (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c s' => if is_idc c then let (tok, rest) := scan_id s' in (String c tok, rest)
                   else (EmptyString, s)
  end.
Definition classify (s : string) : option GoTy :=
       if String.eqb s "int64"   then Some GTInt64
  else if String.eqb s "int32"   then Some GTI32
  else if String.eqb s "int16"   then Some GTI16
  else if String.eqb s "int8"    then Some GTI8
  else if String.eqb s "int"     then Some GTInt
  else if String.eqb s "uint64"  then Some GTU64
  else if String.eqb s "uint32"  then Some GTU32
  else if String.eqb s "uint16"  then Some GTU16
  else if String.eqb s "uint8"   then Some GTU8
  else if String.eqb s "uint"    then Some GTUint
  else if String.eqb s "bool"    then Some GTBool
  else if String.eqb s "string"  then Some GTString
  else if String.eqb s "float64" then Some GTFloat64
  else if String.eqb s "float32" then Some GTFloat32
  else None.

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
    match scan_id s with
    | (EmptyString, _) => None
    | (tok, rest) =>
        match classify tok with
        | Some t => Some (t, rest)
        | None =>
            if String.eqb tok "chan" then
              match strip " " rest with
              | Some r => match parse_ty f r with Some (u, r') => Some (GTChan u, r') | None => None end
              | None => None end
            else if String.eqb tok "map" then
              match strip "[" rest with
              | Some r => match parse_ty f r with
                          | Some (k, r1) =>
                              match strip "]" r1 with
                              | Some r2 => match parse_ty f r2 with
                                           | Some (v, r3) => Some (GTMap k v, r3)
                                           | None => None end
                              | None => None end
                          | None => None end
              | None => None end
            else match bool_dec (nominal_type_ident tok) true with
                 | left H  => Some (GTNamed (mkTyName tok H), rest)
                 | right _ => None
                 end
        end
    end end end
  end.

Fixpoint ty_depth (t : GoTy) : nat :=
  match t with
  | GTPtr u | GTSlice u | GTChan u => S (ty_depth u)
  | GTMap a b => S (Nat.max (ty_depth a) (ty_depth b))
  | _ => O
  end.

(** Append is associative and right-unital on strings, and a literal prefix strips off cleanly. *)
Lemma sapp_assoc : forall a b c, ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. induction a as [ | x a IH ]; intros b c; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.
Lemma sapp_nil_r : forall s, (s ++ "")%string = s.
Proof. induction s as [ | x s IH ]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.
(** A type is only ever followed (within [print_ty]) by end-of-string or a "]" (the map key→value
    boundary).  [rbound] captures that: such a [rest] cannot extend the just-parsed token (the only
    keyword extensions are digits, and "]" is not one), so the parse is unambiguous. *)
Definition rbound (rest : string) : Prop := rest = ""%string \/ exists r, rest = ("]" ++ r)%string.

(** [scan_id] consumes a maximal identifier run exactly: an all-identifier-char string [n] followed by a
    non-identifier char (or end) scans back to [(n, rest)]. *)
Lemma scan_id_all : forall n rest, all_idc n = true ->
  match rest with EmptyString => True | String c _ => is_idc c = false end ->
  scan_id (n ++ rest)%string = (n, rest).
Proof.
  induction n as [ | c n' IH ]; intros rest Hall Hr.
  - cbn [append]. destruct rest as [ | rc rs ]; cbn [scan_id]; [ reflexivity | rewrite Hr; reflexivity ].
  - cbn [all_idc] in Hall. apply andb_true_iff in Hall. destruct Hall as [ Hc Hn' ].
    cbn [append scan_id]. rewrite Hc, (IH rest Hn' Hr). reflexivity.
Qed.

(** An [rbound] remainder ("" or "]"-led) starts with a non-identifier char — the seam a [scan_id] stops
    at. *)
Lemma rbound_not_idc : forall rest, rbound rest ->
  match rest with EmptyString => True | String c _ => is_idc c = false end.
Proof. intros rest [ -> | [r -> ] ]; [ exact I | cbn; reflexivity ]. Qed.

(** One-step unfolders for the composite leaves: "chan " scans to the [chan] token then strips the
    space; "map[" scans to [map] then strips "[".  ([scan_id] consumes only the keyword run — it stops at
    the space / "[" — so these hold by computation.) *)
Lemma parse_ty_chan : forall f s, parse_ty (S f) ("chan " ++ s)%string =
  match parse_ty f s with Some (t, r') => Some (GTChan t, r') | None => None end.
Proof. reflexivity. Qed.
Lemma parse_ty_map : forall f s, parse_ty (S f) ("map[" ++ s)%string =
  match parse_ty f s with
  | Some (k, r1) => match strip "]" r1 with
                    | Some r2 => match parse_ty f r2 with Some (v, r3) => Some (GTMap k v, r3) | None => None end
                    | None => None end
  | None => None end.
Proof. reflexivity. Qed.

(** A non-keyword name classifies as nominal and is neither the [chan] nor [map] keyword.  Bridges the
    [GoTy]-independent [is_type_keyword] (which gates [Ident]) to [classify] (which assigns the [GoTy]):
    if [s] is none of the 16 keyword strings, then [classify s = None] and [s] is not [chan]/[map]. *)
Lemma kw_false_classify : forall s, is_type_keyword s = false ->
  classify s = None /\ String.eqb s "chan" = false /\ String.eqb s "map" = false.
Proof.
  intros s H. unfold is_type_keyword in H. cbn [existsb] in H.
  apply orb_false_iff in H; destruct H as [ Hi64 H ].
  apply orb_false_iff in H; destruct H as [ Hi32 H ].
  apply orb_false_iff in H; destruct H as [ Hi16 H ].
  apply orb_false_iff in H; destruct H as [ Hi8  H ].
  apply orb_false_iff in H; destruct H as [ Hint H ].
  apply orb_false_iff in H; destruct H as [ Hu64 H ].
  apply orb_false_iff in H; destruct H as [ Hu32 H ].
  apply orb_false_iff in H; destruct H as [ Hu16 H ].
  apply orb_false_iff in H; destruct H as [ Hu8  H ].
  apply orb_false_iff in H; destruct H as [ Hu   H ].
  apply orb_false_iff in H; destruct H as [ Hbool   H ].
  apply orb_false_iff in H; destruct H as [ Hstr    H ].
  apply orb_false_iff in H; destruct H as [ Hf64    H ].
  apply orb_false_iff in H; destruct H as [ Hf32    H ].
  apply orb_false_iff in H; destruct H as [ Hchan   H ].
  apply orb_false_iff in H; destruct H as [ Hmap    _ ].
  unfold classify.
  rewrite Hi64, Hi32, Hi16, Hi8, Hint, Hu64, Hu32, Hu16, Hu8, Hu, Hbool, Hstr, Hf64, Hf32.
  split; [ reflexivity | split; [ exact Hchan | exact Hmap ] ].
Qed.

(** PRINT-PARSE ROUND-TRIP (prefix form): [parse_ty] consumes EXACTLY [print_ty t], leaving [rest], for
    EVERY [t] — UNCONDITIONALLY, with no [valid_ty] hypothesis.  A nominal name now carries its validity
    in the [Ident] type, so the side-condition the old statement threaded is discharged BY CONSTRUCTION
    (and a colliding name like [GTNamed "int"] is unrepresentable).  The map case needs the prefix
    generality (after the key comes "]" then the value); the [rbound] discipline keeps the maximal-munch
    leaf parse correct (a token never bleeds into the trailing "]" or end). *)
Theorem parse_print_ty : forall t f rest,
  ty_depth t < f -> rbound rest ->
  parse_ty f (print_ty t ++ rest) = Some (t, rest).
Proof.
  induction t as [ | | | | | | | | | | | | | | u IH | u IH | u IH | a IHa b IHb | i ];
    intros f rest Hf Hrb;
    destruct f as [ | f ]; cbn [ty_depth] in Hf; try lia.
  (* 14 scalar leaves: [print_ty] is a complete keyword; with [rest] empty or "]"-led the scan + classify
     is concrete, so cbn + reflexivity closes it *)
  all: try (destruct Hrb as [-> | [r ->]]; cbn; reflexivity).
  - (* GTPtr u *)  cbn. rewrite (IH f rest ltac:(lia) Hrb). reflexivity.
  - (* GTSlice u *) cbn. rewrite (IH f rest ltac:(lia) Hrb). reflexivity.
  - (* GTChan u *)  cbn [print_ty]. rewrite sapp_assoc, parse_ty_chan.
    rewrite (IH f rest ltac:(lia) Hrb). reflexivity.
  - (* GTMap a b *)
    assert (Hk : parse_ty f (print_ty a ++ ("]" ++ (print_ty b ++ rest)))%string
               = Some (a, ("]" ++ (print_ty b ++ rest))%string))
      by (apply IHa; [ lia | right; eexists; reflexivity ]).
    assert (Hv : parse_ty f (print_ty b ++ rest)%string = Some (b, rest))
      by (apply IHb; [ lia | exact Hrb ]).
    cbn [print_ty]. rewrite !sapp_assoc, parse_ty_map, Hk.
    cbn. rewrite Hv. reflexivity.
  - (* GTNamed i : nominal — validity carried by [i] *)
    destruct i as [ s Hs ]. cbn [print_ty proj1_sig].
    pose proof Hs as Hni.
    destruct s as [ | c n' ]; [ cbn in Hni; discriminate | ].
    unfold nominal_type_ident in Hni. apply andb_true_iff in Hni. destruct Hni as [ Hgi Hkw ].
    unfold go_ident in Hgi. apply andb_true_iff in Hgi. destruct Hgi as [ Hsa _ ].
    apply andb_true_iff in Hsa. destruct Hsa as [ Hstart Hall ].
    apply negb_true_iff in Hkw.
    assert (Hstar : Ascii.eqb "*"%char c = false).
    { destruct (Ascii.eqb "*"%char c) eqn:E; [ apply Ascii.eqb_eq in E; subst c; cbn in Hstart; discriminate | reflexivity ]. }
    assert (Hbrack : Ascii.eqb "["%char c = false).
    { destruct (Ascii.eqb "["%char c) eqn:E; [ apply Ascii.eqb_eq in E; subst c; cbn in Hstart; discriminate | reflexivity ]. }
    assert (Hss : strip "*" (String c (n' ++ rest))%string = None) by (cbn [strip]; rewrite Hstar; reflexivity).
    assert (Hsb : strip "[]" (String c (n' ++ rest))%string = None) by (cbn [strip]; rewrite Hbrack; reflexivity).
    assert (Hscan : scan_id (String c (n' ++ rest))%string = (String c n', rest)).
    { change (String c (n' ++ rest))%string with ((String c n') ++ rest)%string.
      apply scan_id_all; [ exact Hall | apply rbound_not_idc; exact Hrb ]. }
    destruct (kw_false_classify _ Hkw) as [ Hcl [ Hchanf Hmapf ] ].
    cbn [parse_ty append].
    rewrite Hss, Hsb, Hscan, Hcl, Hchanf, Hmapf.
    destruct (bool_dec (nominal_type_ident (String c n')) true) as [ Hd | Hd ].
    + (* the parser's freshly-built [TyName] equals [i]: same name, proofs equal by UIP-on-[bool] *)
      assert (E : Hd = Hs) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
    + exfalso. apply Hd. exact Hs.
Qed.

(** FAITHFULNESS COROLLARY — INJECTIVITY, now UNCONDITIONAL (over ALL [GoTy], no [valid_ty] side-
    condition): two types that print alike parse to the same tree, hence are equal.  So the emitted type
    text never conflates ANY two distinct Go types — and because an invalid nominal name is
    unrepresentable, there is no escape hatch (e.g. no [GTNamed "int"] aliasing [GTInt]). *)
Corollary print_ty_inj : forall t1 t2, print_ty t1 = print_ty t2 -> t1 = t2.
Proof.
  intros t1 t2 He.
  set (f := S (Nat.max (ty_depth t1) (ty_depth t2))).
  assert (R1 : parse_ty f (print_ty t1) = Some (t1, "")).
  { rewrite <- (sapp_nil_r (print_ty t1)).
    apply parse_print_ty; [ unfold f; lia | left; reflexivity ]. }
  assert (R2 : parse_ty f (print_ty t2) = Some (t2, "")).
  { rewrite <- (sapp_nil_r (print_ty t2)).
    apply parse_print_ty; [ unfold f; lia | left; reflexivity ]. }
  rewrite He in R1. rewrite R1 in R2. injection R2 as Ht. exact Ht.
Qed.

(** Concrete nominal round-trips — a validated name parses back as [GTNamed], even with a keyword PREFIX
    ([int8x] is ONE token via maximal munch, never [int8] + "x"), and composes under the constructors.
    The names are wrapped in [mkIdent _ eq_refl]: validity is now in the type, so [eq_refl] DISCHARGES it
    by computation (and a keyword like [GTNamed "int"] would not typecheck — the proof would fail). *)
Example rt_ty_named : parse_ty 2 (print_ty (GTNamed (mkTyName "Foo" eq_refl)))
                    = Some (GTNamed (mkTyName "Foo" eq_refl), "").
Proof. reflexivity. Qed.
Example rt_ty_named_kwprefix : parse_ty 2 (print_ty (GTNamed (mkTyName "int8x" eq_refl)))
                             = Some (GTNamed (mkTyName "int8x" eq_refl), "").
Proof. reflexivity. Qed.
Example rt_ty_named_slice : parse_ty 3 (print_ty (GTSlice (GTNamed (mkTyName "Foo" eq_refl))))
                          = Some (GTSlice (GTNamed (mkTyName "Foo" eq_refl)), "").
Proof. reflexivity. Qed.
Example rt_ty_named_chan : parse_ty 3 (print_ty (GTChan (GTNamed (mkTyName "T" eq_refl))))
                         = Some (GTChan (GTNamed (mkTyName "T" eq_refl)), "").
Proof. reflexivity. Qed.
Example rt_ty_named_map : parse_ty 5 (print_ty (GTMap (GTNamed (mkTyName "Key" eq_refl)) GTInt))
                        = Some (GTMap (GTNamed (mkTyName "Key" eq_refl)) GTInt, "").
Proof. reflexivity. Qed.

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
(** Adaptive fuel — at least as many steps as [z] has decimal digits, so [z_digits] NEVER truncates a
    large input (the old fixed [64] silently dropped digits for |z| >= 10^64 — accepted arbitrary [Z] but
    was correct only under a bound).  [Z.log2 z + 1] is the BIT width, which exceeds the decimal-digit
    count (since 10 > 2), so it is always enough; and it is cheap (no astronomically large [nat]).  Only
    ever applied to [z > 0] ([print_Z] special-cases 0 and negates negatives). *)
Definition digit_fuel (z : Z) : nat := S (Z.to_nat (Z.log2 z)).
Definition print_Z (z : Z) : string :=
  if (z =? 0)%Z then "0"
  else if (z <? 0)%Z then ("-" ++ z_digits (digit_fuel (- z)) (- z) "")%string
  else z_digits (digit_fuel z) z "".

(** Computational checks: the decimal printer is correct on samples spanning the int64/uint64 range
    (incl. the unsigned value [2^63] that an [Int64.t]-based printer renders only via [%Lu]). *)
Example print_Z_0    : print_Z 0 = "0".                                       Proof. reflexivity. Qed.
Example print_Z_42   : print_Z 42 = "42".                                     Proof. reflexivity. Qed.
Example print_Z_neg  : print_Z (-7) = "-7".                                   Proof. reflexivity. Qed.
Example print_Z_imax : print_Z 9223372036854775807 = "9223372036854775807".  Proof. reflexivity. Qed.
Example print_Z_u63  : print_Z 9223372036854775808 = "9223372036854775808".  Proof. reflexivity. Qed.

(** ---- INTEGER FAITHFULNESS (round-trip) ---- a decimal PARSER recovers the [Z] from [print_Z]'s
    output, so the emitted integer literal denotes EXACTLY the source value over the whole modelled
    range (|z| < 10^64 — far beyond the int64/uint64 values [print_Z] is ever called with).  The
    analog of [parse_print_ty] / [esc_string_roundtrip] for integer literals — the most-emitted leaf. *)
Definition dval (c : ascii) : Z := Z.of_nat (nat_of_ascii c - 48).
Fixpoint parseZ_pos (acc : Z) (s : string) : Z :=
  match s with EmptyString => acc | String c s' => parseZ_pos (acc * 10 + dval c)%Z s' end.
Definition parse_Z (s : string) : Z :=
  match s with
  | EmptyString  => 0%Z
  | String c s'  => if Ascii.eqb c (ascii_of_nat 45) then (- parseZ_pos 0 s')%Z else parseZ_pos 0 s
  end.

(** [dval] inverts [dec_digit] on a single decimal digit. *)
Lemma dval_dec_digit : forall n, (n < 10)%nat -> dval (dec_digit n) = Z.of_nat n.
Proof.
  intros n H. unfold dval, dec_digit. rewrite Ascii.nat_ascii_embedding by lia. f_equal. lia.
Qed.

(** KEY LEMMA — parsing [z_digits]' output from accumulator 0 recovers [z] into the running fold: the
    digit-count shift would be [a * 10^k] but [a = 0] kills it, so NO power arithmetic is needed. *)
Lemma parseZ_pos_z_digits : forall fuel z acc,
  (0 <= z)%Z -> (z < 10 ^ Z.of_nat fuel)%Z -> parseZ_pos 0 (z_digits fuel z acc) = parseZ_pos z acc.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hz Hb.
  - cbn [z_digits]. assert (z = 0%Z) by (cbn in Hb; lia). subst z. reflexivity.
  - cbn [z_digits].
    pose proof (Z.mod_pos_bound z 10 ltac:(lia)) as Hmod.
    assert (Hk : (Z.to_nat (z mod 10) < 10)%nat) by lia.
    destruct (Z.eqb (z / 10) 0) eqn:E.
    + apply Z.eqb_eq in E.
      cbn [parseZ_pos]. rewrite dval_dec_digit by exact Hk. rewrite Z2Nat.id by lia.
      replace (0 * 10 + z mod 10)%Z with z by (pose proof (Z.div_mod z 10 ltac:(lia)); lia).
      reflexivity.
    + apply Z.eqb_neq in E.
      assert (Hdpos : (0 <= z / 10)%Z) by (apply Z.div_pos; lia).
      assert (Hdlt : (z / 10 < 10 ^ Z.of_nat f)%Z).
      { apply Z.div_lt_upper_bound; [ lia | ].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hb by lia. lia. }
      rewrite (IH (z / 10)%Z (String (dec_digit (Z.to_nat (z mod 10))) acc) Hdpos Hdlt).
      cbn [parseZ_pos]. rewrite dval_dec_digit by exact Hk. rewrite Z2Nat.id by lia.
      replace (z / 10 * 10 + z mod 10)%Z with z by (pose proof (Z.div_mod z 10 ltac:(lia)); lia).
      reflexivity.
Qed.

(** The first character [z_digits] emits is a decimal digit (so, for a POSITIVE [z], it is never the
    leading "-" — which lets [parse_Z] take the unsigned branch). *)
Lemma z_digits_head : forall f z acc, (0 < f)%nat ->
  exists k r, (k < 10)%nat /\ z_digits f z acc = String (dec_digit k) r.
Proof.
  induction f as [ | f IH ]; intros z acc Hf; [ lia | ].
  cbn [z_digits]. pose proof (Z.mod_pos_bound z 10 ltac:(lia)) as Hmod.
  assert (Hk : (Z.to_nat (z mod 10) < 10)%nat) by lia.
  destruct (Z.eqb (z / 10) 0) eqn:E.
  - exists (Z.to_nat (z mod 10)), acc; split; [ exact Hk | reflexivity ].
  - destruct f as [ | f' ].
    + exists (Z.to_nat (z mod 10)), acc; split; [ exact Hk | reflexivity ].
    + destruct (IH (z / 10)%Z (String (dec_digit (Z.to_nat (z mod 10))) acc) ltac:(lia))
        as [k [r [Hk2 Hr]]].
      exists k, r; split; [ exact Hk2 | exact Hr ].
Qed.

Lemma dec_digit_ne_minus : forall k, (k < 10)%nat -> Ascii.eqb (dec_digit k) (ascii_of_nat 45) = false.
Proof.
  intros k Hk. apply Bool.not_true_iff_false. intro H. apply Ascii.eqb_eq in H.
  unfold dec_digit in H. apply (f_equal nat_of_ascii) in H.
  rewrite !Ascii.nat_ascii_embedding in H by lia. lia.
Qed.

Lemma parse_Z_neg : forall X, parse_Z (String (ascii_of_nat 45) X) = (- parseZ_pos 0 X)%Z.
Proof. intro X. cbn [parse_Z]. rewrite Ascii.eqb_refl. reflexivity. Qed.
Lemma parse_Z_nonminus : forall c X, Ascii.eqb c (ascii_of_nat 45) = false ->
  parse_Z (String c X) = parseZ_pos 0 (String c X).
Proof. intros c X H. cbn [parse_Z]. rewrite H. reflexivity. Qed.

(** The adaptive fuel is always enough for ANY base [b >= 2]: [z < b ^ digit_fuel z] for [z > 0].
    [digit_fuel z] is the bit width [Z.log2 z + 1]; [z < 2^(log2 z + 1)] and [2^k <= b^k], so
    [z < b^(log2 z + 1)].  (Instantiated at b=10 for [print_Z], b=16 for [print_hex].) *)
Lemma z_lt_pow_digit_fuel : forall b z, (2 <= b)%Z -> (0 < z)%Z -> (z < b ^ Z.of_nat (digit_fuel z))%Z.
Proof.
  intros b z Hb Hz. unfold digit_fuel.
  rewrite Nat2Z.inj_succ, Z2Nat.id by apply Z.log2_nonneg.
  apply Z.lt_le_trans with (2 ^ Z.succ (Z.log2 z))%Z.
  - apply (proj2 (Z.log2_spec z Hz)).
  - apply Z.pow_le_mono_l; lia.
Qed.

(** FAITHFULNESS, now UNCONDITIONAL — with the adaptive fuel [print_Z] never truncates, so the round-trip
    holds for EVERY [z] (no |z| < 10^64 side condition). *)
Theorem print_parse_Z : forall z, parse_Z (print_Z z) = z.
Proof.
  intro z. unfold print_Z.
  destruct (Z.eqb z 0) eqn:E0; [ apply Z.eqb_eq in E0; subst z; reflexivity | ].
  apply Z.eqb_neq in E0. destruct (Z.ltb z 0) eqn:Eneg.
  - (* z < 0 *) apply Z.ltb_lt in Eneg.
    replace (("-" ++ z_digits (digit_fuel (- z)) (- z) "")%string)
       with (String (ascii_of_nat 45) (z_digits (digit_fuel (- z)) (- z) "")) by reflexivity.
    rewrite parse_Z_neg.
    rewrite parseZ_pos_z_digits by (try (apply (z_lt_pow_digit_fuel 10)); lia).
    cbn [parseZ_pos]. lia.
  - (* z > 0 *) apply Z.ltb_ge in Eneg. assert (Hz : (0 < z)%Z) by lia.
    destruct (z_digits_head (digit_fuel z) z "" ltac:(unfold digit_fuel; lia)) as [k [r [Hk Hr]]].
    rewrite Hr, (parse_Z_nonminus _ _ (dec_digit_ne_minus k Hk)), <- Hr.
    rewrite parseZ_pos_z_digits by (try (apply (z_lt_pow_digit_fuel 10)); lia).
    cbn [parseZ_pos]. reflexivity.
Qed.

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

(** ---- STRING-LITERAL FAITHFULNESS (round-trip) ---- the escaping is LOSSLESS: a decoder [unescape]
    recovers the exact original bytes from [esc_string], so [print_string_lit] denotes precisely its
    argument — no byte dropped, merged, or corrupted by an escape.  This is the data-faithfulness
    property for string literals (the analog of [parse_print_ty] for the type sub-language). *)
Lemma nat_of_ascii_lt_256 : forall c, nat_of_ascii c < 256.
Proof. intro c. destruct c. repeat match goal with b : bool |- _ => destruct b end; cbn; lia. Qed.
Lemma nat_of_ch : forall n, n < 256 -> nat_of_ascii (ch n) = n.
Proof. intros n H. unfold ch. apply Ascii.nat_ascii_embedding. exact H. Qed.
Lemma ch_nat : forall c, ch (nat_of_ascii c) = c.
Proof. intro c. unfold ch. apply Ascii.ascii_nat_embedding. Qed.

(** Inverse of [hexdig] on a single hex nibble. *)
Definition unhex (c : ascii) : nat :=
  let v := nat_of_ascii c in if Nat.leb v 57 then v - 48 else v - 87.
Lemma unhex_hexdig : forall k, k < 16 -> unhex (hexdig k) = k.
Proof.
  intros k H. unfold unhex, hexdig. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite Ascii.nat_ascii_embedding by lia.
    destruct (Nat.leb (48 + k) 57) eqn:E2; [ lia | apply Nat.leb_gt in E2; lia ].
  - apply Nat.ltb_ge in E. rewrite Ascii.nat_ascii_embedding by lia.
    destruct (Nat.leb (87 + k) 57) eqn:E2; [ apply Nat.leb_le in E2; lia | lia ].
Qed.

(** The decoder: reverse [esc_byte].  A backslash (92) introduces an escape — the next byte selects
    the special char or, for "x" (120), the two hex nibbles; any other byte is itself.  Structural on
    sub-terms of [s] (so no fuel needed). *)
Fixpoint unescape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 rest =>
      if Nat.eqb (nat_of_ascii c1) 92 then
        match rest with
        | EmptyString => EmptyString
        | String c2 rest2 =>
            let d := nat_of_ascii c2 in
            if Nat.eqb d 34 then String (ch 34) (unescape rest2)
            else if Nat.eqb d 92 then String (ch 92) (unescape rest2)
            else if Nat.eqb d 110 then String (ch 10) (unescape rest2)
            else if Nat.eqb d 116 then String (ch 9) (unescape rest2)
            else if Nat.eqb d 114 then String (ch 13) (unescape rest2)
            else if Nat.eqb d 120 then
              match rest2 with
              | String h1 (String h2 rest3) => String (ch (16 * unhex h1 + unhex h2)) (unescape rest3)
              | _ => EmptyString
              end
            else EmptyString
        end
      else String c1 (unescape rest)
  end.

(* Keep [ch]/[nat_of_ascii]/[unhex]/[hexdig] opaque so [cbn] reduces only the [Nat.eqb] dispatch and
   the matches, leaving [ch <v>] / [nat_of_ascii (ch _)] / [unhex (hexdig _)] symbolic for the rewrites. *)
Local Opaque ch nat_of_ascii unhex hexdig Nat.div Nat.modulo.
Lemma unescape_esc_byte : forall c X, unescape (esc_byte (nat_of_ascii c) X) = String c (unescape X).
Proof.
  intros c X. assert (Hc : nat_of_ascii c < 256) by apply nat_of_ascii_lt_256.
  unfold esc_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34.
  { apply Nat.eqb_eq in E34.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 34) by lia. cbn.
    rewrite <- E34, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92.
  { apply Nat.eqb_eq in E92.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn.
    rewrite <- E92, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10.
  { apply Nat.eqb_eq in E10.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 110) by lia. cbn.
    rewrite <- E10, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 9) eqn:E9.
  { apply Nat.eqb_eq in E9.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 116) by lia. cbn.
    rewrite <- E9, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13.
  { apply Nat.eqb_eq in E13.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 114) by lia. cbn.
    rewrite <- E13, ch_nat. reflexivity. }
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.ltb (nat_of_ascii c) 127)) eqn:Eprint.
  { (* printable byte: emitted as-is, decoded as-is (not a backslash since c <> 92 by E92) *)
    cbn [unescape]. rewrite (nat_of_ch (nat_of_ascii c)) by exact Hc.
    rewrite E92. cbn. rewrite ch_nat. reflexivity. }
  { (* hex escape: \xHL with H = b/16, L = b mod 16; 16*H + L = b *)
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 120) by lia. cbn. f_equal.
    rewrite (unhex_hexdig (Nat.div (nat_of_ascii c) 16)) by (apply Nat.Div0.div_lt_upper_bound; lia).
    rewrite (unhex_hexdig (Nat.modulo (nat_of_ascii c) 16)) by (apply Nat.mod_upper_bound; lia).
    transitivity (ch (nat_of_ascii c));
      [ f_equal; pose proof (Nat.div_mod_eq (nat_of_ascii c) 16); lia | apply ch_nat ]. }
Qed.
Local Transparent ch nat_of_ascii unhex hexdig Nat.div Nat.modulo.

Theorem esc_string_roundtrip : forall s, unescape (esc_string s) = s.
Proof.
  induction s as [ | c rest IH ]; [ reflexivity | ].
  cbn [esc_string]. rewrite unescape_esc_byte, IH. reflexivity.
Qed.

(** ---- HEX LITERALS ---- [0x]-prefixed lowercase hex (replacing go.ml's [Printf.sprintf "0x%x"] for
    fixed-width bit masks / sign bits). *)
Fixpoint hex_digits (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O   => acc
  | S f => let d := hexdig (Z.to_nat (z mod 16)) in
           if (z / 16 =? 0)%Z then String d acc else hex_digits f (z / 16)%Z (String d acc)
  end.
Definition print_hex (z : Z) : string :=
  ("0x" ++ (if (z =? 0)%Z then "0" else hex_digits (digit_fuel z) z ""))%string.
Example ph_ff : print_hex 255 = "0xff". Proof. reflexivity. Qed.
Example ph_0  : print_hex 0   = "0x0".  Proof. reflexivity. Qed.
Example ph_80 : print_hex 128 = "0x80". Proof. reflexivity. Qed.

(** ---- HEX FAITHFULNESS (round-trip) ---- the analog of [print_parse_Z] for the [0x]-hex printer
    ([hex_digits] is structurally [z_digits] in base 16; [unhex]/[unhex_hexdig] from the string section
    already invert [hexdig]).  [print_hex] is only ever called on NON-NEGATIVE values (bit masks), so the
    statement is for [0 <= z < 16^64] — again far beyond any fixed-width mask. *)
Fixpoint parseHex_pos (acc : Z) (s : string) : Z :=
  match s with EmptyString => acc | String c s' => parseHex_pos (acc * 16 + Z.of_nat (unhex c))%Z s' end.
Definition parse_hex (s : string) : Z :=
  match s with String _ (String _ rest) => parseHex_pos 0 rest | _ => 0%Z end.

Lemma parse_hex_0x : forall X, parse_hex ("0x" ++ X)%string = parseHex_pos 0 X.
Proof. intro X. reflexivity. Qed.
Lemma print_hex_pos : forall z, (z <> 0)%Z -> print_hex z = ("0x" ++ hex_digits (digit_fuel z) z "")%string.
Proof. intros z H. apply Z.eqb_neq in H. unfold print_hex. rewrite H. reflexivity. Qed.

Lemma parseHex_pos_hex_digits : forall fuel z acc,
  (0 <= z)%Z -> (z < 16 ^ Z.of_nat fuel)%Z -> parseHex_pos 0 (hex_digits fuel z acc) = parseHex_pos z acc.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hz Hb.
  - cbn [hex_digits]. assert (z = 0%Z) by (cbn in Hb; lia). subst z. reflexivity.
  - cbn [hex_digits].
    pose proof (Z.mod_pos_bound z 16 ltac:(lia)) as Hmod.
    assert (Hk : (Z.to_nat (z mod 16) < 16)%nat) by lia.
    destruct (Z.eqb (z / 16) 0) eqn:E.
    + apply Z.eqb_eq in E.
      cbn [parseHex_pos]. rewrite unhex_hexdig by exact Hk. rewrite Z2Nat.id by lia.
      replace (0 * 16 + z mod 16)%Z with z by (pose proof (Z.div_mod z 16 ltac:(lia)); lia).
      reflexivity.
    + apply Z.eqb_neq in E.
      assert (Hdpos : (0 <= z / 16)%Z) by (apply Z.div_pos; lia).
      assert (Hdlt : (z / 16 < 16 ^ Z.of_nat f)%Z).
      { apply Z.div_lt_upper_bound; [ lia | ].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hb by lia. lia. }
      rewrite (IH (z / 16)%Z (String (hexdig (Z.to_nat (z mod 16))) acc) Hdpos Hdlt).
      cbn [parseHex_pos]. rewrite unhex_hexdig by exact Hk. rewrite Z2Nat.id by lia.
      replace (z / 16 * 16 + z mod 16)%Z with z by (pose proof (Z.div_mod z 16 ltac:(lia)); lia).
      reflexivity.
Qed.

(** UNCONDITIONAL for every non-negative [z] (the adaptive fuel never truncates). *)
Theorem print_parse_hex : forall z, (0 <= z)%Z -> parse_hex (print_hex z) = z.
Proof.
  intros z Hlo. destruct (Z.eqb z 0) eqn:E0.
  - apply Z.eqb_eq in E0; subst z. reflexivity.
  - apply Z.eqb_neq in E0. rewrite print_hex_pos by exact E0. rewrite parse_hex_0x.
    rewrite parseHex_pos_hex_digits by (try (apply (z_lt_pow_digit_fuel 16)); lia).
    cbn [parseHex_pos]. reflexivity.
Qed.

(** ---- FLOAT-HEX LITERAL ---- the IEEE [spec_float] finite value ±m·2^e emits as Go's hex float
    [±0x<m>p<e>].  Slice 15 verified the mantissa/exponent PIECES (print_hex / print_Z); this moves the
    ASSEMBLY into Rocq too (the last leaf whose glue was raw OCaml [^]).  [sign] = sign, [mant] =
    mantissa (rendered hex), [exp] = exponent (signed decimal). *)
Definition print_float_hex (sign : bool) (mant exp : Z) : string :=
  ((if sign then "-" else "") ++ print_hex mant ++ "p" ++ print_Z exp)%string.

Example pfh_pos : print_float_hex false 24 (-52) = "0x18p-52". Proof. reflexivity. Qed.
Example pfh_neg : print_float_hex true 18 51   = "-0x12p51". Proof. reflexivity. Qed.

(** FAITHFULNESS — the float literal round-trips: a parser recovers [(sign, mant, exp)] EXACTLY.  The
    "p" delimiter is unambiguous because the mantissa render [print_hex] contains no "p" (hex digits are
    0-9a-f); [split_p] cuts there, then [parse_hex] / [parse_Z] recover the parts (slices 20/21). *)
Definition is_p (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 112).  (* 'p' = 112 *)
Fixpoint no_p (s : string) : Prop :=
  match s with EmptyString => True | String c s' => is_p c = false /\ no_p s' end.
Lemma no_p_app : forall a b, no_p a -> no_p b -> no_p (a ++ b).
Proof.
  induction a as [ | c a IH ]; intros b Ha Hb; [ exact Hb | ].
  cbn [no_p append] in *. destruct Ha as [Hc Ha]. split; [ exact Hc | apply IH; assumption ].
Qed.

Lemma is_p_hexdig : forall k, (k < 16)%nat -> is_p (hexdig k) = false.
Proof.
  intros k Hk. unfold is_p, hexdig.
  destruct (Nat.ltb k 10) eqn:E; cbv iota;
    [ apply Nat.ltb_lt in E | apply Nat.ltb_ge in E ];
    apply Bool.not_true_iff_false; intro H; apply Ascii.eqb_eq in H;
    apply (f_equal nat_of_ascii) in H; rewrite !Ascii.nat_ascii_embedding in H by lia; lia.
Qed.

Lemma hex_digits_no_p : forall fuel z acc, no_p acc -> no_p (hex_digits fuel z acc).
Proof.
  induction fuel as [ | f IH ]; intros z acc Hacc; [ exact Hacc | ].
  cbn [hex_digits]. pose proof (Z.mod_pos_bound z 16 ltac:(lia)) as Hmod.
  assert (Hk : (Z.to_nat (z mod 16) < 16)%nat) by lia.
  destruct (Z.eqb (z / 16) 0).
  - cbn [no_p]. split; [ apply is_p_hexdig; exact Hk | exact Hacc ].
  - apply IH. cbn [no_p]. split; [ apply is_p_hexdig; exact Hk | exact Hacc ].
Qed.

Lemma no_p_print_hex : forall z, no_p (print_hex z).
Proof.
  intro z. unfold print_hex. apply no_p_app.
  - cbn [no_p]. repeat split; (reflexivity || exact I).
  - destruct (Z.eqb z 0); [ cbn [no_p]; repeat split; (reflexivity || exact I)
                          | apply hex_digits_no_p; exact I ].
Qed.

Fixpoint split_p (s : string) : string * string :=
  match s with
  | EmptyString  => (""%string, ""%string)
  | String c s'  => if is_p c then (""%string, s') else let (a, b) := split_p s' in (String c a, b)
  end.
Lemma split_p_app : forall pre suf, no_p pre ->
  split_p (pre ++ String (ascii_of_nat 112) suf) = (pre, suf).
Proof.
  induction pre as [ | c pre IH ]; intros suf Hnp.
  - cbn. reflexivity.
  - cbn [no_p] in Hnp. destruct Hnp as [Hc Hnp].
    cbn [split_p append]. rewrite Hc, (IH suf Hnp). reflexivity.
Qed.

(** [print_hex mant ++ "p" ++ print_Z exp] (optionally prefixed by a "p"-free [pre]) splits at the
    delimiter into the mantissa render and the exponent render. *)
Lemma split_p_float : forall pre mant exp, no_p pre ->
  split_p (pre ++ print_hex mant ++ "p" ++ print_Z exp)%string
    = ((pre ++ print_hex mant)%string, print_Z exp).
Proof.
  intros pre mant exp Hpre.
  assert (Heq : (pre ++ print_hex mant ++ "p" ++ print_Z exp)%string
              = ((pre ++ print_hex mant) ++ String (ascii_of_nat 112) (print_Z exp))%string)
    by (rewrite !sapp_assoc; reflexivity).
  rewrite Heq. apply split_p_app. apply no_p_app; [ exact Hpre | apply no_p_print_hex ].
Qed.

(** [print_hex] always begins with the digit "0" (of its "0x" prefix), so a positive float's mantissa
    part never looks like the leading "-". *)
Lemma print_hex_head : forall z, exists rest, print_hex z = String (ascii_of_nat 48) rest.
Proof. intro z. unfold print_hex. eexists. reflexivity. Qed.

Definition parse_float_hex (s : string) : bool * Z * Z :=
  let (mpart, epart) := split_p s in
  let e := parse_Z epart in
  match mpart with
  | String c rest => if Ascii.eqb c (ascii_of_nat 45) then (true, parse_hex rest, e)
                     else (false, parse_hex mpart, e)
  | EmptyString => (false, 0%Z, e)
  end.
Lemma parse_float_hex_eq : forall s mpart epart, split_p s = (mpart, epart) ->
  parse_float_hex s =
    (match mpart with
     | String c rest => if Ascii.eqb c (ascii_of_nat 45) then (true, parse_hex rest, parse_Z epart)
                        else (false, parse_hex mpart, parse_Z epart)
     | EmptyString => (false, 0%Z, parse_Z epart)
     end).
Proof. intros s mpart epart H. unfold parse_float_hex. rewrite H. reflexivity. Qed.

Local Opaque print_hex print_Z parse_hex parse_Z.
(** UNCONDITIONAL but for the mantissa's non-negativity (hex is unsigned); [exp] is any [Z]. *)
Theorem print_parse_float_hex : forall sign mant exp,
  (0 <= mant)%Z ->
  parse_float_hex (print_float_hex sign mant exp) = (sign, mant, exp).
Proof.
  intros sign mant exp Hm.
  assert (Hmrt : parse_hex (print_hex mant) = mant) by (apply print_parse_hex; lia).
  assert (Hert : parse_Z (print_Z exp) = exp) by (apply print_parse_Z).
  unfold print_float_hex. destruct sign; cbv iota.
  - (* sign = true: prefix "-" *)
    rewrite (parse_float_hex_eq _ _ _
              (split_p_float "-" mant exp ltac:(cbn [no_p]; repeat split; (reflexivity || exact I)))).
    cbn. rewrite Hmrt, Hert. reflexivity.
  - (* sign = false: empty prefix *)
    destruct (print_hex_head mant) as [rest Hph].
    rewrite (parse_float_hex_eq _ _ _ (split_p_float "" mant exp ltac:(exact I))).
    cbn [append]. rewrite Hph at 1. cbn. rewrite Hmrt, Hert. reflexivity.
Qed.
Local Transparent print_hex print_Z parse_hex parse_Z.

(** ---- PROOFS ATOP THE PRINTERS ---- WELL-FORMEDNESS: every printer yields a NON-EMPTY string, so no
    emitted token is ever blank (which would be malformed Go).  [print_ty] UNCONDITIONALLY now (a nominal
    name is a validated [Ident], hence non-empty), and the literal printers too.  (Injectivity AND the
    print-parse round-trip are likewise unconditional — [print_ty_inj] / [parse_print_ty].) *)
Lemma print_ty_nonempty : forall t, print_ty t <> ""%string.
Proof.
  induction t as [ | | | | | | | | | | | | | | | | | | i ]; cbn [print_ty];
    try (intro Hc; discriminate Hc).
  (* GTNamed i : the [Ident] proof forces the name non-empty *)
  destruct i as [ s Hs ]. cbn [proj1_sig].
  destruct s as [ | c n' ]; [ cbn in Hs; discriminate Hs | intro Hc; discriminate Hc ].
Qed.
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

(** ============================================================================
    ---- EXPRESSIONS: OPERATOR PRECEDENCE ---- the first STRUCTURAL (recursive) piece of the printer to
    move into Rocq.  [go.ml]'s [pp_prec] renders a binary-operator tree, inserting parentheses ONLY
    where an operand's operator binds LOOSER than its context — get this wrong and [(a+b)*c] misprints
    as [a+b*c], silently changing the program's meaning.  This is the hardest correctness property of the
    structural printer, so it is the right first target.

    [GoExpr] models the binary-operator tree the plugin assembles.  CRUCIALLY the operator text and its
    precedence are NOT supplied by the caller — they are DERIVED from a [BinOp] constructor, so a caller
    cannot mis-state them.  (The old [GEBin (p:nat) (op:string) …] let a caller pass " * " at precedence 5
    with a looser raw operand — e.g. [GEBin 5 " * " (GERaw "a + b") (GERaw "c")] — which printed
    [a + b * c] for what should be [(a + b) * c]: the balance theorem held yet the parse was wrong.)
    [EAtom s] is a pre-rendered ATOM — an operand that binds tightest (literal / variable / call / field /
    index); [EBin o l r] is a LEFT-ASSOCIATIVE binary operator [o].  [print_expr ctx e] renders [e] where
    the context demands precedence >= [ctx]: an [EBin] of precedence [binop_prec o] is parenthesized
    exactly when that [< ctx]; operands recurse at [p] (left) and [S p] (right, one tighter — left
    associativity), MIRRORING the plugin's [pp_prec] byte-for-byte. *)
Inductive BinOp : Type :=
  (* Go precedence 5: *  /  %  <<  >>  &  &^ *)
  | BMul | BDiv | BRem | BShl | BShr | BAnd | BAndNot
  (* Go precedence 4: +  -  |  ^ *)
  | BAdd | BSub | BOr | BXor
  (* Go precedence 3: ==  !=  <  <=  >  >= *)
  | BEq | BNe | BLt | BLe | BGt | BGe
  (* Go precedence 2 / 1: &&  || *)
  | BLAnd | BLOr.

(** Operator precedence and surface text DERIVED from the constructor — the single source of truth. *)
Definition binop_prec (o : BinOp) : nat :=
  match o with
  | BMul | BDiv | BRem | BShl | BShr | BAnd | BAndNot => 5
  | BAdd | BSub | BOr | BXor => 4
  | BEq | BNe | BLt | BLe | BGt | BGe => 3
  | BLAnd => 2
  | BLOr => 1
  end.
Definition binop_text (o : BinOp) : string :=
  match o with
  | BMul => " * "  | BDiv => " / "  | BRem => " % "  | BShl => " << " | BShr => " >> "
  | BAnd => " & "  | BAndNot => " &^ "
  | BAdd => " + "  | BSub => " - "  | BOr  => " | "  | BXor => " ^ "
  | BEq  => " == " | BNe  => " != " | BLt  => " < "  | BLe  => " <= " | BGt => " > " | BGe => " >= "
  | BLAnd => " && " | BLOr => " || "
  end.


(* ---- ATOM LEXER (moved ABOVE GoExpr: [GoAtom] below carries an [atomic] proof) ---- *)
(** The operator-recognition table: every [BinOp], longest-text-first so a shorter operator can never
    pre-empt a longer one (in fact no [binop_text] is a prefix of another — the trailing space
    disambiguates — so the order is immaterial; we keep the longest-first order for clarity).  The
    surface text is taken from [binop_text] (the single source of truth), never duplicated here. *)
Definition op_order : list BinOp :=
  [ BShl; BShr; BAndNot; BLAnd; BLOr; BEq; BNe; BLe; BGe;
    BMul; BDiv; BRem; BAnd; BAdd; BSub; BOr; BXor; BLt; BGt ].
Fixpoint op_match_in (tbl : list BinOp) (s : string) : option (BinOp * string) :=
  match tbl with
  | [] => None
  | o :: tl => match strip (binop_text o) s with Some r => Some (o, r) | None => op_match_in tl s end
  end.
(** The [BinOp] whose surface text is a prefix of [s] (at most one — see above), paired with the
    remainder after it. *)
Definition op_match (s : string) : option (BinOp * string) := op_match_in op_order s.

(** [op_match] recovers exactly the printed operator and its remainder. *)
Lemma op_match_binop : forall o rest, op_match (binop_text o ++ rest)%string = Some (o, rest).
Proof. intros o rest. destruct o; reflexivity. Qed.

Example op_match_ident : op_match "foo" = None. Proof. reflexivity. Qed.
Example op_match_plus  : op_match (" + " ++ "x") = Some (BAdd, "x"). Proof. reflexivity. Qed.

(** [strip] only succeeds when [s]'s head matches the pattern's head — so a successful strip pins down
    [s]'s first character. *)
Lemma strip_head : forall pc p' s r, strip (String pc p') s = Some r ->
  exists s', s = String pc s'.
Proof.
  intros pc p' s r H. destruct s as [ | c s' ]; cbn in H; [ discriminate | ].
  destruct (Ascii.eqb pc c) eqn:E; [ | discriminate ].
  apply Ascii.eqb_eq in E; subst c. exists s'. reflexivity.
Qed.

Definition is_space (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 32).  (* ' ' *)

(** Every operator text begins with a space (ascii 32) — so [op_match] can fire ONLY on a string whose
    first character is a space.  Contrapositive: a non-space-led string never matches an operator.  This
    is the operator-seam guarantee — at any depth-0, non-space position inside an atom, no operator can
    begin (whatever follows), so [scan_atom] cannot split the atom early. *)
Lemma binop_text_head_space : forall o, exists t, binop_text o = String (ascii_of_nat 32) t.
Proof. intro o. destruct o; eexists; reflexivity. Qed.
Lemma op_match_not_space : forall c s, is_space c = false -> op_match (String c s) = None.
Proof.
  intros c s Hns. unfold op_match.
  assert (forall tbl, op_match_in tbl (String c s) = None) as Hgen.
  { induction tbl as [ | o tl IH ]; cbn; [ reflexivity | ].
    destruct (strip (binop_text o) (String c s)) as [ r | ] eqn:E; [ | exact IH ].
    exfalso. destruct (binop_text_head_space o) as [ t Ht ]. rewrite Ht in E.
    destruct (strip_head _ _ _ _ E) as [ s' Hs ]. inversion Hs; subst c.
    unfold is_space in Hns. rewrite Ascii.eqb_refl in Hns. discriminate. }
  apply Hgen.
Qed.

(** An ASCII char that appears as the SECOND character of some operator text, i.e. an operator's leading
    op-char ([* / % < > & ^ + - | = !]).  Every operator text is `" " ++ op-char ++ ...`, so a space
    followed by a NON-op-char can never begin an operator — the seam guarantee that lets [scan_atom]
    consume an atom containing interior depth-0 spaces (e.g. a function-literal's `) T {`). *)
Definition is_op_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (orb (Nat.eqb n 42) (Nat.eqb n 47)) (orb (Nat.eqb n 37) (Nat.eqb n 60)))
      (orb (orb (orb (Nat.eqb n 62) (Nat.eqb n 38)) (orb (Nat.eqb n 94) (Nat.eqb n 43)))
           (orb (orb (Nat.eqb n 45) (Nat.eqb n 124)) (orb (Nat.eqb n 61) (Nat.eqb n 33)))).
Lemma binop_text_second_opchar : forall o, exists opc t,
  binop_text o = String (ascii_of_nat 32) (String opc t) /\ is_op_char opc = true.
Proof. intro o. destruct o; do 2 eexists; split; reflexivity. Qed.
(** A successful strip of a two-char-or-longer pattern pins down [s]'s first two characters. *)
Lemma strip_two : forall a b p s r, strip (String a (String b p)) s = Some r ->
  exists s', s = String a (String b s').
Proof.
  intros a b p s r H. destruct s as [ | sa s1 ]; cbn in H; [ discriminate | ].
  destruct (Ascii.eqb a sa) eqn:Ea; [ | discriminate H ]. apply Ascii.eqb_eq in Ea; subst sa.
  destruct s1 as [ | sb s2 ]; cbn in H; [ discriminate | ].
  destruct (Ascii.eqb b sb) eqn:Eb; [ | discriminate H ]. apply Ascii.eqb_eq in Eb; subst sb.
  exists s2. reflexivity.
Qed.
Lemma op_match_second_nonop : forall c1 c2 s, is_op_char c2 = false ->
  op_match (String c1 (String c2 s)) = None.
Proof.
  intros c1 c2 s Hns. unfold op_match.
  assert (forall tbl, op_match_in tbl (String c1 (String c2 s)) = None) as Hgen.
  { induction tbl as [ | o tl IH ]; cbn [op_match_in]; [ reflexivity | ].
    destruct (strip (binop_text o) (String c1 (String c2 s))) as [ r | ] eqn:E; [ | exact IH ].
    exfalso. destruct (binop_text_second_opchar o) as [ opc [ t [ Ht Hopc ] ] ]. rewrite Ht in E.
    destruct (strip_two _ _ _ _ _ E) as [ s' Hs' ]. injection Hs' as _ Hc2 _. subst c2.
    rewrite Hopc in Hns. discriminate Hns. }
  apply Hgen.
Qed.

(** Bracket depth tracks ALL of ( [ { vs ) ] } — so an operator inside a function-literal's `{ … }` body
    (or a slice/composite literal) sits at depth >0 and does not end the atom.  [is_open]/[is_close] stay
    "(" / ")" — they are the EXPRESSION-level precedence-paren that [parse_primary] and the climb use. *)
Definition is_bopen (c : ascii) : bool :=
  orb (orb (Ascii.eqb c (ascii_of_nat 40)) (Ascii.eqb c (ascii_of_nat 91))) (Ascii.eqb c (ascii_of_nat 123)).
Definition is_bclose (c : ascii) : bool :=
  orb (orb (Ascii.eqb c (ascii_of_nat 41)) (Ascii.eqb c (ascii_of_nat 93))) (Ascii.eqb c (ascii_of_nat 125)).
Definition is_open  (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 40).  (* '(' *)
Definition is_close (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 41).  (* ')' *)
Definition opens (s : string) : bool := match op_match s with Some _ => true | None => false end.

(** Read a primary's ATOM: from BRACKET-depth [d], stop at a depth-0 operator or a depth-0 ")" or end;
    otherwise consume the char, tracking ALL bracket depths ( [ { vs ) ] }.  An [atomic] operand has no
    depth-0 operator and is bracket-balanced — and any operator inside its own brackets is at depth >0 —
    so this consumes EXACTLY the atom, INCLUDING a function-literal `func(…) T { return x - y }(a, b)`
    whose `-` lives in the `{ }` body and whose `) T {` spaces sit between non-operator characters. *)
Fixpoint scan_atom (d : nat) (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c s' =>
      if andb (Nat.eqb d 0) (orb (opens (String c s')) (is_close c))
      then (EmptyString, String c s')
      else let d' := if is_bopen c then S d else if is_bclose c then Nat.pred d else d in
           let (a, rest) := scan_atom d' s' in (String c a, rest)
  end.

(** A depth-0 space is only dangerous when an OP-CHAR follows it (it could begin an operator straddling
    into the remainder); a space followed by a non-op char (or end) is harmless. *)
Definition op_after (s : string) : bool :=
  match s with EmptyString => false | String c _ => is_op_char c end.

(** [atomic s] — a legal primary atom: non-empty, not "("-led (else a parenthesised group), BRACKET-
    balanced, with NO depth-0 operator AND no depth-0 space IMMEDIATELY FOLLOWED BY AN OP-CHAR (the seam
    condition; interior spaces — a function-literal's return type, a struct literal's fields — are fine).
    The plugin's operands satisfy this: their operators sit inside their own brackets, and their depth-0
    spaces are followed by non-op characters (a type name, "{", ")", …). *)
Fixpoint atomic_from (d : nat) (s : string) : bool :=
  match s with
  | EmptyString => Nat.eqb d 0
  | String c s' =>
      if andb (Nat.eqb d 0) (orb (orb (opens (String c s')) (is_bclose c)) (andb (is_space c) (op_after s')))
      then false
      else atomic_from (if is_bopen c then S d else if is_bclose c then Nat.pred d else d) s'
  end.
Definition atomic (s : string) : bool :=
  match s with EmptyString => false | String c _ => andb (negb (is_open c)) (atomic_from 0 s) end.

(** SAFETY — [print_prec] emits WELL-BRACKETED Go: scanning the output left to right, the parenthesis
    depth never goes negative and ends at zero (so no dangling/unmatched paren — always syntactically
    valid bracketing), PROVIDED every atom and operator string is itself well-bracketed (Go operands and
    operators are — calls like [f(a, b)] balance their own parens).  This certifies the parenthesization
    DISCIPLINE: the only parens [print_prec] adds are matched pairs around a balanced inner string. *)
Definition pv (c : ascii) : Z :=
  if Ascii.eqb c (ascii_of_nat 40) then 1%Z         (* '(' *)
  else if Ascii.eqb c (ascii_of_nat 41) then (-1)%Z (* ')' *)
  else 0%Z.
Fixpoint depth (d : Z) (s : string) : Z :=
  match s with EmptyString => d | String c s' => depth (d + pv c)%Z s' end.
Fixpoint nneg (d : Z) (s : string) : Prop :=
  match s with EmptyString => True | String c s' => (0 <= d + pv c)%Z /\ nneg (d + pv c)%Z s' end.
Definition balanced (s : string) : Prop := depth 0 s = 0%Z /\ nneg 0 s.

(** A BOOLEAN paren-balance, sound w.r.t. [balanced], so the [Atom] predicate (below) can carry it. *)
Fixpoint nneg_b (d : Z) (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (0 <=? d + pv c)%Z (nneg_b (d + pv c)%Z s') end.
Definition balanced_b (s : string) : bool := andb (depth 0 s =? 0)%Z (nneg_b 0 s).
Lemma nneg_b_sound : forall s d, nneg_b d s = true -> nneg d s.
Proof.
  induction s as [ | c s' IH ]; intros d H.
  - exact I.
  - cbn [nneg_b] in H. cbn [nneg]. apply andb_true_iff in H. destruct H as [ Hle Hrest ].
    split; [ apply Z.leb_le; exact Hle | apply IH; exact Hrest ].
Qed.
Lemma balanced_b_sound : forall s, balanced_b s = true -> balanced s.
Proof.
  intros s H. unfold balanced_b in H. apply andb_true_iff in H. destruct H as [ Hd Hn ].
  unfold balanced. split; [ apply Z.eqb_eq; exact Hd | apply nneg_b_sound; exact Hn ].
Qed.

(** The ATOM well-formedness, carried IN THE TYPE below: ATOMIC (a primary binding tighter than any
    operator — no depth-0 operator, not "("-led) AND paren-BALANCED.  [atomic] alone does NOT imply
    [balanced] (atomic_from tracks COMBINED bracket depth, so e.g. "[)" is atomic but unbalanced), so
    BOTH are required; the plugin's build_goexpr guard checks exactly [atom_ok]. *)
Definition atom_ok (s : string) : bool := andb (atomic s) (balanced_b s).
Lemma atom_ok_atomic : forall s, atom_ok s = true -> atomic s = true.
Proof. intros s H. apply andb_true_iff in H. destruct H as [ Ha _ ]. exact Ha. Qed.
Lemma atom_ok_balanced : forall s, atom_ok s = true -> balanced s.
Proof. intros s H. apply andb_true_iff in H. destruct H as [ _ Hb ]. apply balanced_b_sound; exact Hb. Qed.

(** ---- IDENTIFIERS ARE ATOMS ---- an identifier char is never a space, bracket, or paren, so an
    all-identifier string is [atomic] (no depth-0 operator — operators are space-led — / close / bracket)
    and paren-BALANCED (no parens).  Hence [valid_ident s -> atom_ok s]: an identifier structures as a
    well-formed atom — letting a future [GoAtom]'s [AIdent] case carry only a [valid_ident] proof. *)
Lemma is_idc_eqb_false : forall c k, is_idc c = true -> is_idc (ascii_of_nat k) = false ->
  Ascii.eqb c (ascii_of_nat k) = false.
Proof.
  intros c k Hc Hk. destruct (Ascii.eqb c (ascii_of_nat k)) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E. subst c. rewrite Hk in Hc. discriminate.
Qed.
Lemma is_idc_not_space : forall c, is_idc c = true -> is_space c = false.
Proof. intros c H. unfold is_space. apply is_idc_eqb_false; [ exact H | reflexivity ]. Qed.
Lemma is_idc_not_open : forall c, is_idc c = true -> is_open c = false.
Proof. intros c H. unfold is_open. apply is_idc_eqb_false; [ exact H | reflexivity ]. Qed.
Lemma is_idc_not_bopen : forall c, is_idc c = true -> is_bopen c = false.
Proof.
  intros c H. unfold is_bopen.
  rewrite (is_idc_eqb_false c 40 H eq_refl), (is_idc_eqb_false c 91 H eq_refl),
          (is_idc_eqb_false c 123 H eq_refl). reflexivity.
Qed.
Lemma is_idc_not_bclose : forall c, is_idc c = true -> is_bclose c = false.
Proof.
  intros c H. unfold is_bclose.
  rewrite (is_idc_eqb_false c 41 H eq_refl), (is_idc_eqb_false c 93 H eq_refl),
          (is_idc_eqb_false c 125 H eq_refl). reflexivity.
Qed.
Lemma is_idc_pv0 : forall c, is_idc c = true -> pv c = 0%Z.
Proof.
  intros c H. unfold pv.
  rewrite (is_idc_eqb_false c 40 H eq_refl), (is_idc_eqb_false c 41 H eq_refl). reflexivity.
Qed.
Lemma is_idstart_is_idc : forall c, is_idstart c = true -> is_idc c = true.
Proof.
  intros c H. unfold is_idstart in H. unfold is_idc.
  apply orb_true_iff in H. destruct H as [ H | H ].
  - apply orb_true_iff in H. destruct H as [ Hu | Hl ].
    + apply orb_true_iff. left. apply orb_true_iff. right. exact Hu.
    + apply orb_true_iff. right. apply orb_true_iff. left. exact Hl.
  - apply orb_true_iff. right. apply orb_true_iff. right. exact H.
Qed.
Lemma all_idc_depth : forall s d, all_idc s = true -> depth d s = d.
Proof.
  induction s as [ | c s' IH ]; intros d H; cbn [depth]; [ reflexivity | ].
  cbn [all_idc] in H. apply andb_true_iff in H. destruct H as [ Hc Hs' ].
  rewrite (is_idc_pv0 c Hc), Z.add_0_r. apply IH; exact Hs'.
Qed.
Lemma all_idc_nneg_b : forall s d, (0 <= d)%Z -> all_idc s = true -> nneg_b d s = true.
Proof.
  induction s as [ | c s' IH ]; intros d Hd H; cbn [nneg_b]; [ reflexivity | ].
  cbn [all_idc] in H. apply andb_true_iff in H. destruct H as [ Hc Hs' ].
  rewrite (is_idc_pv0 c Hc), Z.add_0_r, (proj2 (Z.leb_le 0 d) Hd). cbn [andb].
  apply IH; [ exact Hd | exact Hs' ].
Qed.
Lemma all_idc_atomic_from : forall s, all_idc s = true -> atomic_from 0 s = true.
Proof.
  induction s as [ | c s' IH ]; intro H; [ reflexivity | ].
  cbn [all_idc] in H. apply andb_true_iff in H. destruct H as [ Hc Hs' ].
  cbn [atomic_from].
  assert (Hopens : opens (String c s') = false).
  { unfold opens. rewrite (op_match_not_space c s' (is_idc_not_space c Hc)). reflexivity. }
  rewrite Hopens, (is_idc_not_bclose c Hc), (is_idc_not_space c Hc), (is_idc_not_bopen c Hc).
  cbn [orb andb Nat.eqb]. apply IH; exact Hs'.
Qed.
Lemma go_ident_atom_ok : forall s, go_ident s = true -> atom_ok s = true.
Proof.
  intros s H. unfold go_ident in H. destruct s as [ | c s' ]; [ discriminate | ].
  apply andb_true_iff in H. destruct H as [ H _ ]. apply andb_true_iff in H. destruct H as [ Hstart Hall ].
  pose proof (is_idstart_is_idc c Hstart) as Hc.
  unfold atom_ok. apply andb_true_iff. split.
  - unfold atomic. apply andb_true_iff. split.
    + apply negb_true_iff. apply is_idc_not_open; exact Hc.
    + apply all_idc_atomic_from; exact Hall.
  - unfold balanced_b. apply andb_true_iff. split.
    + rewrite (all_idc_depth (String c s') 0 Hall). reflexivity.
    + apply all_idc_nneg_b; [ apply Z.le_refl | exact Hall ].
Qed.

(** [raw_ok s] — a NON-identifier well-formed atom: [atom_ok] AND not a [valid_ident] (so identifiers
    structure SEPARATELY, as [AIdent]).  The split lets the round-trip DISAMBIGUATE: a [valid_ident]
    re-parses to [AIdent], anything else to [ARaw]. *)
Definition raw_ok (s : string) : bool := andb (atom_ok s) (negb (go_ident s)).
Lemma raw_ok_atom_ok : forall s, raw_ok s = true -> atom_ok s = true.
Proof. intros s H. apply andb_true_iff in H. destruct H as [ Ha _ ]. exact Ha. Qed.
Lemma raw_ok_not_ident : forall s, raw_ok s = true -> go_ident s = false.
Proof. intros s H. apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn. Qed.

(** A structured Go ATOM, validity carried IN THE TYPE (malformed atom text UNREPRESENTABLE): a validated
    IDENTIFIER ([AIdent], the first richer constructor), or a "raw" atom ([ARaw] — [atom_ok] but not an
    identifier: a call, cast, literal, …).  [GoAtom] extracts to a 2-constructor type over bare strings
    (proofs erased); [atom_str] is the underlying text, always [atom_ok]. *)
Inductive GoAtom : Type :=
  | AIdent : Ident -> GoAtom
  | ARaw   : { s : string | raw_ok s = true } -> GoAtom.
Definition atom_str (a : GoAtom) : string :=
  match a with AIdent i => proj1_sig i | ARaw r => proj1_sig r end.
Lemma atom_str_atom_ok : forall a, atom_ok (atom_str a) = true.
Proof.
  intros [ i | r ]; cbn [atom_str].
  - apply go_ident_atom_ok, (proj2_sig i).
  - apply raw_ok_atom_ok, (proj2_sig r).
Qed.

Inductive GoExpr : Type :=
  | EAtom : GoAtom -> GoExpr
  | EBin  : BinOp -> GoExpr -> GoExpr -> GoExpr.

Fixpoint print_expr (ctx : nat) (e : GoExpr) : string :=
  match e with
  | EAtom a => atom_str a
  | EBin o l r =>
      let p := binop_prec o in
      let inner := (print_expr p l ++ binop_text o ++ print_expr (S p) r)%string in
      if Nat.ltb p ctx then ("(" ++ inner ++ ")")%string else inner
  end.

(** CHARACTERIZATION — exact behaviour and the byte-identical basis vs [pp_prec]: an atom prints
    verbatim; a binop wraps iff [binop_prec o < ctx]. *)
Lemma print_expr_atom : forall ctx (a : GoAtom), print_expr ctx (EAtom a) = atom_str a.
Proof. reflexivity. Qed.
Lemma print_expr_unwrapped : forall o l r ctx, Nat.ltb (binop_prec o) ctx = false ->
  print_expr ctx (EBin o l r)
    = (print_expr (binop_prec o) l ++ binop_text o ++ print_expr (S (binop_prec o)) r)%string.
Proof. intros o l r ctx H. cbn [print_expr]. rewrite H. reflexivity. Qed.
Lemma print_expr_wrapped : forall o l r ctx, Nat.ltb (binop_prec o) ctx = true ->
  print_expr ctx (EBin o l r)
    = ("(" ++ (print_expr (binop_prec o) l ++ binop_text o ++ print_expr (S (binop_prec o)) r) ++ ")")%string.
Proof. intros o l r ctx H. cbn [print_expr]. rewrite H. reflexivity. Qed.


(** [depth]/[nneg] are homomorphic over append, and tolerant of a raised starting floor. *)
Lemma depth_app : forall a b d, depth d (a ++ b) = depth (depth d a) b.
Proof. induction a as [ | c a IH ]; intros b d; [ reflexivity | cbn; apply IH ]. Qed.
Lemma depth_shift : forall s d, depth d s = (d + depth 0 s)%Z.
Proof.
  induction s as [ | c s IH ]; intro d; cbn [depth].
  - lia.
  - rewrite (IH (d + pv c)%Z), (IH (0 + pv c)%Z). lia.
Qed.
Lemma nneg_app : forall a b d, nneg d (a ++ b) <-> nneg d a /\ nneg (depth d a) b.
Proof.
  induction a as [ | c a IH ]; intros b d; cbn.
  - intuition.
  - rewrite IH. intuition.
Qed.
Lemma nneg_raise : forall s d d', (d <= d')%Z -> nneg d s -> nneg d' s.
Proof.
  induction s as [ | c s IH ]; intros d d' Hle Hn; cbn in *; [ exact I | ].
  destruct Hn as [Hpos Hrest]. split.
  - lia.
  - apply (IH (d + pv c)%Z); [ lia | exact Hrest ].
Qed.

(** Every operator render is paren-free, hence balanced — so [wf] need only constrain the ATOMS. *)
Lemma binop_text_balanced : forall o, balanced (binop_text o).
Proof. intro o. destruct o; unfold balanced; cbn; repeat split; (lia || exact I). Qed.

(** A well-bracketed-atoms predicate over the tree: every [EAtom] string is balanced (operators are
    derived and provably balanced, so they need no hypothesis). *)
Fixpoint wf (e : GoExpr) : Prop :=
  match e with
  | EAtom a => balanced (atom_str a)
  | EBin _ l r => wf l /\ wf r
  end.

(** The single ascii of "(" / ")" scans as depth +1 / -1, and the matching non-negativity facts. *)
Lemma depth_lparen : forall d, depth d "(" = (d + 1)%Z.
Proof. intro d. reflexivity. Qed.
Lemma depth_rparen : forall d, depth d ")" = (d - 1)%Z.
Proof. intro d. cbn. lia. Qed.
Lemma nneg_lparen : forall d, (0 <= d)%Z -> nneg d "(".
Proof. intros d Hd. cbn. split; [ lia | exact I ]. Qed.
Lemma nneg_rparen : forall d, (1 <= d)%Z -> nneg d ")".
Proof. intros d Hd. cbn. split; [ lia | exact I ]. Qed.

(** Wrapping a string in a matched paren pair leaves its net depth-change unchanged, and preserves
    non-negativity when the inner string is itself net-zero and balanced ([s] abstract → the inner
    appends stay opaque, so these don't decompose the operand). *)
Lemma depth_wrap : forall d s, depth d ("(" ++ s ++ ")") = depth d s.
Proof.
  intros d s. rewrite !depth_app, depth_lparen, depth_rparen,
                      (depth_shift s (d + 1)%Z), (depth_shift s d). lia.
Qed.
Lemma nneg_wrap : forall d s, (0 <= d)%Z -> depth 0 s = 0%Z -> nneg d s -> nneg d ("(" ++ s ++ ")").
Proof.
  intros d s Hd Hs Hn. rewrite nneg_app. split; [ apply nneg_lparen; lia | ].
  rewrite depth_lparen, nneg_app. split.
  - apply (nneg_raise s d (d + 1)%Z); [ lia | exact Hn ].
  - rewrite (depth_shift s (d + 1)%Z), Hs. apply nneg_rparen. lia.
Qed.

(** Core: from any non-negative starting depth, printing a well-formed expr returns to that exact depth
    and never dips below it.  Generalized over [ctx] and [d] so the recursive sub-calls (at [p], [S p],
    and inside the wrap) are covered by the IH.  Uses the [print_prec_wrapped]/[_unwrapped]
    characterization to expose the printed string without fighting [cbn]. *)
Lemma print_expr_depth_nneg : forall e ctx d, (0 <= d)%Z -> wf e ->
  depth d (print_expr ctx e) = d /\ nneg d (print_expr ctx e).
Proof.
  induction e as [ s | o l IHl r IHr ]; intros ctx d Hd Hwf.
  - (* EAtom a *) cbn [print_expr wf] in *. destruct Hwf as [Hz Hn]. split.
    + rewrite depth_shift, Hz. lia.
    + apply (nneg_raise (atom_str s) 0 d); [ lia | exact Hn ].
  - (* EBin o l r *)
    cbn [wf] in Hwf. destruct Hwf as [Hwl Hwr].
    destruct (binop_text_balanced o) as [Hopz Hopn].
    destruct (IHl (binop_prec o) d Hd Hwl) as [Hld Hln].
    destruct (IHr (S (binop_prec o)) d Hd Hwr) as [Hrd Hrn].
    (* the inner string [l ++ binop_text o ++ r] returns to [d] and never dips below it *)
    assert (Hinner_d : depth d (print_expr (binop_prec o) l ++ binop_text o
                                ++ print_expr (S (binop_prec o)) r) = d).
    { rewrite !depth_app, Hld, (depth_shift (binop_text o) d), Hopz, Z.add_0_r, Hrd. reflexivity. }
    assert (Hinner0 : depth 0 (print_expr (binop_prec o) l ++ binop_text o
                               ++ print_expr (S (binop_prec o)) r) = 0%Z)
      by (rewrite depth_shift in Hinner_d; lia).
    assert (Hinner_n : nneg d (print_expr (binop_prec o) l ++ binop_text o
                               ++ print_expr (S (binop_prec o)) r)).
    { rewrite !nneg_app. split; [ exact Hln | ]. rewrite Hld. split.
      - apply (nneg_raise (binop_text o) 0 d); [ lia | exact Hopn ].
      - rewrite (depth_shift (binop_text o) d), Hopz, Z.add_0_r. exact Hrn. }
    destruct (Nat.ltb (binop_prec o) ctx) eqn:E.
    + (* wrapped: "(" ++ inner ++ ")" *)
      rewrite (print_expr_wrapped o l r ctx E). split.
      * rewrite depth_wrap. exact Hinner_d.
      * apply nneg_wrap; [ lia | exact Hinner0 | exact Hinner_n ].
    + (* not wrapped *)
      rewrite (print_expr_unwrapped o l r ctx E).
      split; [ exact Hinner_d | exact Hinner_n ].
Qed.

Theorem print_expr_balanced : forall e ctx, wf e -> balanced (print_expr ctx e).
Proof.
  intros e ctx Hwf. unfold balanced.
  destruct (print_expr_depth_nneg e ctx 0 (Z.le_refl 0) Hwf) as [Hd Hn].
  split; assumption.
Qed.

(** ============================================================================
    ---- EXPRESSION PRINTER/PARSER SELF-CONSISTENCY (the Rocq expression grammar) ---- the balance theorem
    above proves the output is WELL-BRACKETED, but not that the parenthesisation is PRECEDENCE-correct.
    This section defines a precedence-climbing PARSER for a Rocq MODEL of Go's binary-operator grammar
    (the same 5 levels, left-associative) and proves [parse_expr 0 (print_expr 0 e) = Some (e, "")] — so
    [print_expr] and this parser are mutually inverse: the parenthesisation [print_expr] emits is exactly
    what the parser re-reads to [e].  HONEST SCOPE: this is printer/parser SELF-CONSISTENCY for the Rocq
    grammar — NOT yet a theorem that Go's own parser accepts the text with the intended structure (that
    needs a Go-subset grammar / a recognition theorem; gap to close).  It is strictly stronger than
    bracket balance and rules out the precedence counterexamples the balance theorem could not. *)


(** One-step unfolders — expose [scan_atom]/[atomic_from] on a cons without [cbn] over-reducing the
    [opens]/[op_match] guards (which we instead rewrite via the seam lemmas). *)
Lemma scan_atom_cons : forall d c s',
  scan_atom d (String c s') =
    if andb (Nat.eqb d 0) (orb (opens (String c s')) (is_close c))
    then (EmptyString, String c s')
    else let (a, rest) := scan_atom (if is_bopen c then S d else if is_bclose c then Nat.pred d else d) s'
         in (String c a, rest).
Proof. reflexivity. Qed.
Lemma atomic_from_cons : forall d c s',
  atomic_from d (String c s') =
    if andb (Nat.eqb d 0) (orb (orb (opens (String c s')) (is_bclose c)) (andb (is_space c) (op_after s')))
    then false
    else atomic_from (if is_bopen c then S d else if is_bclose c then Nat.pred d else d) s'.
Proof. reflexivity. Qed.

(** A [rest] at which [scan_atom] stops cleanly: empty, or its head is ")" or begins an operator. *)
Definition good_seam (rest : string) : bool :=
  match rest with EmptyString => true | String c _ => orb (opens rest) (is_close c) end.

Lemma is_close_of_bclose : forall c, is_bclose c = false -> is_close c = false.
Proof.
  intros c H. unfold is_bclose in H. unfold is_close.
  apply orb_false_iff in H. destruct H as [ H _ ]. apply orb_false_iff in H. destruct H as [ H _ ]. exact H.
Qed.
Lemma op_match_space_nil : op_match (String (ascii_of_nat 32) "") = None.
Proof. reflexivity. Qed.

(** A [good_seam] remainder begins with a non-op character (a space — operator-led — or ")") or is empty;
    so a depth-0 trailing space in the atom cannot straddle into it. *)
Lemma good_seam_first_nonop : forall rest, good_seam rest = true ->
  match rest with EmptyString => True | String c2 _ => is_op_char c2 = false end.
Proof.
  intros rest H. destruct rest as [ | c2 rs ]; [ exact I | ].
  unfold good_seam in H. apply orb_true_iff in H. destruct H as [ Hop | Hcl ].
  - unfold opens in Hop. destruct (op_match (String c2 rs)) eqn:Eop; [ | discriminate Hop ].
    destruct (is_space c2) eqn:Esp.
    + unfold is_space in Esp. apply Ascii.eqb_eq in Esp; subst c2. reflexivity.
    + rewrite (op_match_not_space c2 rs Esp) in Eop. discriminate Eop.
  - unfold is_close in Hcl. apply Ascii.eqb_eq in Hcl; subst c2. reflexivity.
Qed.

(** SCAN CORRECTNESS — an [atomic_from d] string [a] followed by a [good_seam] remainder is consumed
    EXACTLY.  At a depth-0, non-space position [op_match_not_space] kills [opens]; at a depth-0 space, the
    next character (in [a] or, for a trailing space, in [rest] via [good_seam_first_nonop]) is a non-op
    char, so [op_match_second_nonop] kills [opens] — the seam cannot be straddled. *)
Lemma scan_atom_gen : forall a d rest, atomic_from d a = true -> good_seam rest = true ->
  scan_atom d (a ++ rest) = (a, rest).
Proof.
  induction a as [ | c a' IH ]; intros d rest Hat Hseam.
  - cbn in Hat. apply Nat.eqb_eq in Hat; subst d. cbn [append].
    destruct rest as [ | rc rs ]; [ reflexivity | ].
    rewrite scan_atom_cons. unfold good_seam in Hseam. rewrite Hseam. reflexivity.
  - rewrite atomic_from_cons in Hat.
    destruct (andb (Nat.eqb d 0)
               (orb (orb (opens (String c a')) (is_bclose c)) (andb (is_space c) (op_after a')))) eqn:Estop;
      [ discriminate Hat | ].
    cbn [append]. rewrite scan_atom_cons.
    assert (Estop2 : andb (Nat.eqb d 0) (orb (opens (String c (a' ++ rest))) (is_close c)) = false).
    { destruct (Nat.eqb d 0) eqn:Ed; cbn [andb] in Estop |- *; [ | reflexivity ].
      apply orb_false_iff in Estop. destruct Estop as [ Hocb Hsp ].
      apply orb_false_iff in Hocb. destruct Hocb as [ Hop Hbcl ].
      rewrite (is_close_of_bclose c Hbcl), orb_false_r. unfold opens.
      destruct (is_space c) eqn:Esc.
      - cbn [andb] in Hsp.
        destruct a' as [ | c2 a'' ]; cbn [append].
        + destruct rest as [ | rc rs ].
          * unfold is_space in Esc. apply Ascii.eqb_eq in Esc; subst c. rewrite op_match_space_nil. reflexivity.
          * pose proof (good_seam_first_nonop (String rc rs) Hseam) as Hrc.
            rewrite (op_match_second_nonop c rc rs Hrc). reflexivity.
        + cbn [op_after] in Hsp. rewrite (op_match_second_nonop c c2 (a'' ++ rest) Hsp). reflexivity.
      - rewrite (op_match_not_space c (a' ++ rest) Esc). reflexivity. }
    rewrite Estop2.
    rewrite (IH (if is_bopen c then S d else if is_bclose c then Nat.pred d else d) rest Hat Hseam).
    reflexivity.
Qed.

Lemma scan_atom_correct : forall a rest, atomic a = true -> good_seam rest = true ->
  scan_atom 0 (a ++ rest) = (a, rest).
Proof.
  intros a rest Hat Hseam. unfold atomic in Hat.
  destruct a as [ | c a' ]; [ discriminate | ].
  apply andb_true_iff in Hat. destruct Hat as [_ Hfrom].
  apply scan_atom_gen; assumption.
Qed.

(** [build_atom a] — the atom DISAMBIGUATION: a [valid_ident] string structures as [AIdent], any other
    [atom_ok] string as [ARaw]; a malformed string is rejected ([None]).  Factored out so the round-trip
    proof uses [build_atom_str] UNIFORMLY (no per-constructor case split in the climbing proof). *)
Definition build_atom (a : string) : option GoExpr :=
  match bool_dec (go_ident a) true with
  | left Hi => Some (EAtom (AIdent (exist _ a Hi)))
  | right _ => match bool_dec (raw_ok a) true with
               | left Hr => Some (EAtom (ARaw (exist _ a Hr)))
               | right _ => None
               end
  end.
Lemma build_atom_str : forall g, build_atom (atom_str g) = Some (EAtom g).
Proof.
  intros [ i | r ]; cbn [atom_str]; unfold build_atom.
  - destruct i as [ s Hvi ]; cbn [proj1_sig].
    destruct (bool_dec (go_ident s) true) as [ Hd | Hd ].
    + do 3 f_equal. assert (E : Hd = Hvi) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
    + exfalso. apply Hd. exact Hvi.
  - destruct r as [ s Hr ]; cbn [proj1_sig].
    pose proof (raw_ok_not_ident _ Hr) as Hni.
    destruct (bool_dec (go_ident s) true) as [ Hd | Hd ]; [ exfalso; congruence | ].
    destruct (bool_dec (raw_ok s) true) as [ Hd2 | Hd2 ].
    + do 3 f_equal. assert (E : Hd2 = Hr) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
    + exfalso. apply Hd2. exact Hr.
Qed.

(** The precedence-climbing parser (Go's binary-operator grammar): [parse_expr k] reads the maximal
    expression whose operators all bind at precedence [>= k]; [parse_primary] reads an atom (via
    [build_atom]) or a "("-delimited sub-expression; [parse_climb] left-folds operators of precedence
    [>= k].  Fuel bounds the recursion (every call strictly decreases it). *)
Fixpoint parse_expr (fuel k : nat) (s : string) : option (GoExpr * string) :=
  match fuel with
  | O => None
  | S f => match parse_primary f s with Some (l, s1) => parse_climb f k l s1 | None => None end
  end
with parse_primary (fuel : nat) (s : string) : option (GoExpr * string) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => None
    | String c s' =>
        if is_open c then
          match parse_expr f 0 s' with
          | Some (e, s1) => match s1 with
                            | String c1 s2 => if is_close c1 then Some (e, s2) else None
                            | EmptyString => None end
          | None => None end
        else match scan_atom 0 s with
             | (EmptyString, _) => None
             | (a, rest) => match build_atom a with Some e => Some (e, rest) | None => None end
             end
    end
  end
with parse_climb (fuel k : nat) (l : GoExpr) (s : string) : option (GoExpr * string) :=
  match fuel with
  | O => None
  | S f =>
    match op_match s with
    | Some (o, s1) =>
        if Nat.leb k (binop_prec o)
        then match parse_expr f (S (binop_prec o)) s1 with
             | Some (r, s2) => parse_climb f k (EBin o l r) s2
             | None => None end
        else Some (l, s)
    | None => Some (l, s)
    end
  end.

(** One-step unfolders for the three fuelled parsers (so proofs expose the body without [cbn]
    over-reducing [op_match]/[scan_atom]). *)
Lemma parse_expr_S : forall f k s, parse_expr (S f) k s =
  match parse_primary f s with Some (l, s1) => parse_climb f k l s1 | None => None end.
Proof. reflexivity. Qed.
Lemma parse_primary_S : forall f s, parse_primary (S f) s =
  match s with
  | EmptyString => None
  | String c s' =>
      if is_open c then
        match parse_expr f 0 s' with
        | Some (e, s1) => match s1 with String c1 s2 => if is_close c1 then Some (e, s2) else None
                          | EmptyString => None end
        | None => None end
      else match scan_atom 0 s with
           | (EmptyString, _) => None
           | (a, rest) => match build_atom a with Some e => Some (e, rest) | None => None end
           end
  end.
Proof. reflexivity. Qed.
Lemma parse_climb_S : forall f k l s, parse_climb (S f) k l s =
  match op_match s with
  | Some (o, s1) =>
      if Nat.leb k (binop_prec o)
      then match parse_expr f (S (binop_prec o)) s1 with
           | Some (r, s2) => parse_climb f k (EBin o l r) s2 | None => None end
      else Some (l, s)
  | None => Some (l, s)
  end.
Proof. reflexivity. Qed.

(** FUEL MONOTONICITY — more fuel never changes a [Some] answer.  Proven as a single S-step over the
    three mutually-recursive parsers, then lifted to any [f <= f'].  This lets the round-trip proof use a
    canonical fuel and bridge the off-by-one fuel mismatches the climb recursion introduces. *)
Lemma parse_mono_S : forall f,
  (forall k s r, parse_expr f k s = Some r -> parse_expr (S f) k s = Some r) /\
  (forall s r, parse_primary f s = Some r -> parse_primary (S f) s = Some r) /\
  (forall k l s r, parse_climb f k l s = Some r -> parse_climb (S f) k l s = Some r).
Proof.
  induction f as [ | f IH ].
  - repeat split; intros; discriminate.
  - destruct IH as [ IHe [ IHp IHc ] ]. repeat split.
    + intros k s r H. rewrite parse_expr_S in H. rewrite parse_expr_S.
      destruct (parse_primary f s) as [ [l0 s1] | ] eqn:Ep; [ | discriminate H ].
      rewrite (IHp _ _ Ep). apply IHc. exact H.
    + intros s r H. destruct s as [ | c s' ]; [ discriminate H | ].
      rewrite parse_primary_S in H. rewrite parse_primary_S.
      destruct (is_open c).
      * destruct (parse_expr f 0 s') as [ [e s1] | ] eqn:Epe; [ | discriminate H ].
        rewrite (IHe _ _ _ Epe). exact H.
      * exact H.
    + intros k l s r H. rewrite parse_climb_S in H. rewrite parse_climb_S.
      destruct (op_match s) as [ [o s1] | ]; [ | exact H ].
      destruct (Nat.leb k (binop_prec o)); [ | exact H ].
      destruct (parse_expr f (S (binop_prec o)) s1) as [ [r0 s2] | ] eqn:Epe; [ | discriminate H ].
      rewrite (IHe _ _ _ Epe). apply IHc. exact H.
Qed.

Lemma parse_mono : forall f' f, f <= f' ->
  (forall k s r, parse_expr f k s = Some r -> parse_expr f' k s = Some r) /\
  (forall s r, parse_primary f s = Some r -> parse_primary f' s = Some r) /\
  (forall k l s r, parse_climb f k l s = Some r -> parse_climb f' k l s = Some r).
Proof.
  induction f' as [ | f' IH ]; intros f Hle.
  - inversion Hle; subst. repeat split; intros; assumption.
  - destruct (Nat.eq_dec f (S f')) as [ -> | Hne ].
    + repeat split; intros; assumption.
    + assert (Hle' : f <= f') by lia. destruct (IH f Hle') as [ He [ Hp Hc ] ].
      destruct (parse_mono_S f') as [ Se [ Sp Sc ] ].
      repeat split; intros.
      * apply Se, He; assumption.
      * apply Sp, Hp; assumption.
      * apply Sc, Hc; assumption.
Qed.

(** Concrete atoms: [EA] is an IDENTIFIER atom, [EAr] a "raw" (non-identifier) atom.  The [valid_ident] /
    [raw_ok] proof is discharged by [eq_refl] (it computes), so a malformed atom string — or an identifier
    written as [EAr] / a non-identifier as [EA] — fails to typecheck: atoms are unrepresentable-when-
    malformed, AND the ident/raw split is enforced at the type. *)
Notation EA s := (EAtom (AIdent (exist _ s eq_refl))).
Notation EAr s := (EAtom (ARaw (exist _ s eq_refl))).

(** Concrete round-trips — including the precedence cases the balance theorem could NOT distinguish:
    [a + b * c] keeps [b * c] grouped, [(a + b) * c] keeps the parens. *)
Example rt_atom : parse_expr 9 0 (print_expr 0 (EA "a")) = Some (EA "a", "").
Proof. reflexivity. Qed.
Example rt_add : parse_expr 9 0 (print_expr 0 (EBin BAdd (EA "a") (EA "b")))
              = Some (EBin BAdd (EA "a") (EA "b"), "").
Proof. reflexivity. Qed.
Example rt_prec : parse_expr 9 0 (print_expr 0 (EBin BAdd (EA "a") (EBin BMul (EA "b") (EA "c"))))
               = Some (EBin BAdd (EA "a") (EBin BMul (EA "b") (EA "c")), "").
Proof. reflexivity. Qed.
Example rt_wrap : parse_expr 9 0 (print_expr 0 (EBin BMul (EBin BAdd (EA "a") (EA "b")) (EA "c")))
               = Some (EBin BMul (EBin BAdd (EA "a") (EA "b")) (EA "c"), "").
Proof. reflexivity. Qed.
Example rt_leftassoc : parse_expr 9 0 (print_expr 0 (EBin BSub (EBin BSub (EA "a") (EA "b")) (EA "c")))
                     = Some (EBin BSub (EBin BSub (EA "a") (EA "b")) (EA "c"), "").
Proof. reflexivity. Qed.
(** Across ALL five precedence levels and both wrap directions — the parenthesisation is recovered
    exactly (these are the cases bracket-balance alone could not tell apart). *)
Example rt_or_and : parse_expr 9 0 (print_expr 0 (EBin BLOr (EA "a") (EBin BLAnd (EA "b") (EA "c"))))
                  = Some (EBin BLOr (EA "a") (EBin BLAnd (EA "b") (EA "c")), "").  (* a || b && c *)
Proof. reflexivity. Qed.
Example rt_and_or_wrap : parse_expr 9 0 (print_expr 0 (EBin BLAnd (EBin BLOr (EA "a") (EA "b")) (EA "c")))
                       = Some (EBin BLAnd (EBin BLOr (EA "a") (EA "b")) (EA "c"), "").  (* (a || b) && c *)
Proof. reflexivity. Qed.
Example rt_cmp_arith : parse_expr 9 0 (print_expr 0 (EBin BEq (EBin BAdd (EA "a") (EA "b")) (EA "c")))
                     = Some (EBin BEq (EBin BAdd (EA "a") (EA "b")) (EA "c"), "").  (* a + b == c *)
Proof. reflexivity. Qed.
Example rt_shift_or : parse_expr 9 0 (print_expr 0 (EBin BOr (EBin BShl (EA "a") (EA "b")) (EA "c")))
                    = Some (EBin BOr (EBin BShl (EA "a") (EA "b")) (EA "c"), "").  (* a << b | c *)
Proof. reflexivity. Qed.
Example rt_rightassoc_wrap : parse_expr 9 0 (print_expr 0 (EBin BSub (EA "a") (EBin BSub (EA "b") (EA "c"))))
                           = Some (EBin BSub (EA "a") (EBin BSub (EA "b") (EA "c")), "").  (* a - (b - c) *)
Proof. reflexivity. Qed.
Example rt_sumofprods : parse_expr 12 0 (print_expr 0
                          (EBin BAdd (EBin BMul (EA "a") (EA "b")) (EBin BMul (EA "c") (EA "d"))))
                      = Some (EBin BAdd (EBin BMul (EA "a") (EA "b")) (EBin BMul (EA "c") (EA "d")), "").
Proof. reflexivity. Qed.  (* a * b + c * d *)
Example rt_prodofsums : parse_expr 12 0 (print_expr 0
                          (EBin BMul (EBin BAdd (EA "a") (EA "b")) (EBin BAdd (EA "c") (EA "d"))))
                      = Some (EBin BMul (EBin BAdd (EA "a") (EA "b")) (EBin BAdd (EA "c") (EA "d")), "").
Proof. reflexivity. Qed.  (* (a + b) * (c + d) *)
(** Atoms with their OWN parens/spaces (a call) — the operator inside is at paren-depth > 0, so the
    scanner reads the whole call as one atom and the top-level " + " still splits correctly. *)
Example rt_call_atom : parse_expr 9 0 (print_expr 0 (EBin BAdd (EAr "f(a, b)") (EA "c")))
                     = Some (EBin BAdd (EAr "f(a, b)") (EA "c"), "").  (* f(a, b) + c *)
Proof. reflexivity. Qed.
(** A FUNCTION-LITERAL atom — exactly the plugin's arith-force typed-IIFE (e.g. main.go line 322) — is
    now [atomic] (its `-` is inside `{ }`, its `) T {` spaces precede non-op chars) and round-trips even
    as a binary-operator operand.  This is the coverage hole that the depth-0-space ban used to leave
    open: such an atom was NOT atomic, so the round-trip silently did not cover IIFE-containing exprs. *)
Example atomic_funclit :
  atomic "func(x int64, y int64) int64 { return x - y }(0, 7)" = true.
Proof. reflexivity. Qed.
Example rt_funclit :
  parse_expr 9 0 (print_expr 0 (EBin BAdd (EAr "func(x int64, y int64) int64 { return x - y }(0, 7)")
                                          (EA "z")))
  = Some (EBin BAdd (EAr "func(x int64, y int64) int64 { return x - y }(0, 7)") (EA "z"), "").
Proof. reflexivity. Qed.

(** ============================================================================
    ---- THE UNIVERSAL EXPRESSION ROUND-TRIP ---- the EXAMPLES above fix the precedence-critical cases
    by reflexivity; this is the theorem for EVERY tree — UNCONDITIONALLY (no [wf]/[atomic_tree]
    hypothesis), because [EAtom] now carries an [Atom] (its [atom_ok] proof in the type), so a malformed
    atom is unrepresentable.  So the parenthesisation [print_expr] emits is precedence-CORRECT (not merely
    balanced): the Rocq parser re-reads the text to the SAME tree [e] — printer/parser SELF-CONSISTENCY
    (see the section header; this is NOT yet a claim about Go's own parser — the remaining gap).  The
    internal lemmas below still THREAD [wf]/[atomic_tree] (the headline discharges them via
    [wf_always]/[atomic_tree_always]).  Proven by a combined strong induction on tree size of
    two facts — [P e]
    (round-trip with a stopping tail) and [Left e] (the spine equation: parsing the print of [e] as a
    left operand reduces to [parse_climb] with [e] as the accumulator).  Climb-recursion fuel mismatches
    are bridged by [parse_mono]. *)

Fixpoint esize (e : GoExpr) : nat :=
  match e with EAtom _ => 1 | EBin _ l r => S (esize l + esize r) end.

Fixpoint atomic_tree (e : GoExpr) : Prop :=
  match e with EAtom a => atomic (atom_str a) = true | EBin _ l r => atomic_tree l /\ atomic_tree r end.

(** Now that [EAtom] carries an [Atom] (its [atom_ok] proof IN THE TYPE), both round-trip side-conditions
    hold for EVERY tree — discharged structurally, no hypothesis needed. *)
Lemma atomic_tree_always : forall e, atomic_tree e.
Proof.
  induction e as [ a | o l IHl r IHr ]; [ cbn; apply atom_ok_atomic, atom_str_atom_ok | cbn; split; assumption ].
Qed.
Lemma wf_always : forall e, wf e.
Proof.
  induction e as [ a | o l IHl r IHr ]; [ cbn; apply atom_ok_balanced, atom_str_atom_ok | cbn; split; assumption ].
Qed.

(** A [rest] at which BOTH [parse_climb k] and [scan_atom] stop cleanly: empty, ")"-led, or led by an
    operator binding LOOSER than [k] (precedence [< k]). *)
Definition tail_ok (k : nat) (rest : string) : Prop :=
  rest = EmptyString
  \/ (exists c rs, rest = String c rs /\ is_close c = true)
  \/ (exists o s1, op_match rest = Some (o, s1) /\ binop_prec o < k).

Lemma is_close_not_space : forall c, is_close c = true -> is_space c = false.
Proof. intros c H. unfold is_close in H. apply Ascii.eqb_eq in H. subst c. reflexivity. Qed.

Lemma leb_false_of_lt : forall a b, a < b -> Nat.leb b a = false.
Proof. intros a b H. destruct (Nat.leb b a) eqn:E; [ apply Nat.leb_le in E; lia | reflexivity ]. Qed.

Lemma tail_ok_mono : forall k k' rest, tail_ok k rest -> k <= k' -> tail_ok k' rest.
Proof.
  intros k k' rest H Hle. destruct H as [ He | [ Hc | [ o [ s1 [ Hop Hp ] ] ] ] ].
  - left; exact He.
  - right; left; exact Hc.
  - right; right. exists o, s1. split; [ exact Hop | lia ].
Qed.

Lemma tail_ok_good_seam : forall k rest, tail_ok k rest -> good_seam rest = true.
Proof.
  intros k rest H. destruct H as [ He | [ Hc | [ o [ s1 [ Hop Hp ] ] ] ] ].
  - subst rest; reflexivity.
  - destruct Hc as [ c [ rs [ Hr Hcl ] ] ]. subst rest. unfold good_seam. rewrite Hcl, orb_true_r. reflexivity.
  - destruct rest as [ | c rs ]; [ discriminate Hop | ]. unfold good_seam, opens. rewrite Hop. reflexivity.
Qed.

Lemma tail_ok_climb_stop : forall k rest F l, tail_ok k rest -> parse_climb (S F) k l rest = Some (l, rest).
Proof.
  intros k rest F l H. rewrite parse_climb_S.
  destruct H as [ He | [ Hc | [ o [ s1 [ Hop Hp ] ] ] ] ].
  - subst rest; reflexivity.
  - destruct Hc as [ c [ rs [ Hr Hcl ] ] ]. subst rest.
    rewrite (op_match_not_space c rs (is_close_not_space c Hcl)). reflexivity.
  - rewrite Hop, (leb_false_of_lt _ _ Hp). reflexivity.
Qed.

(** The per-tree round-trip property, abbreviated so it can be carried as a hypothesis for sub-trees
    (operands) inside the spine-fold lemma below. *)
(** Fuel budget [3*esize e + 2 < F]: the [+2] is the slack a WRAPPED [e] needs (its "(" + inner parse
    cost 2 fuel over the unwrapped parse it reduces to); the [3*] covers the left spine, whose length plus
    operand sizes together make up [esize e] — see [lspine_fuel3]. *)
Definition Pexpr (e : GoExpr) : Prop :=
  forall k ctx rest F, k <= ctx -> tail_ok k rest -> 3 * esize e + 2 < F ->
    parse_expr F k (print_expr ctx e ++ rest) = Some (e, rest).

(** A LEFT-LEANING spine, as a base operand and a list of (operator, right-operand) pairs printed in
    sequence; [fold_pairs] rebuilds the (left-associative) tree, [print_pairs] the surface text. *)
Fixpoint print_pairs (ps : list (BinOp * GoExpr)) : string :=
  match ps with
  | [] => ""
  | (o, r) :: ps' => (binop_text o ++ print_expr (S (binop_prec o)) r ++ print_pairs ps')%string
  end.
Fixpoint fold_pairs (base : GoExpr) (ps : list (BinOp * GoExpr)) : GoExpr :=
  match ps with [] => base | (o, r) :: ps' => fold_pairs (EBin o base r) ps' end.
Fixpoint pairs_fuel (ps : list (BinOp * GoExpr)) : nat :=
  match ps with [] => 1 | (_, r) :: ps' => S (3 * esize r + 2 + pairs_fuel ps') end.
(** Climb-readiness: every operator binds at precedence [>= k], consecutive operators are NON-increasing
    (left-associativity — so each right operand's parse stops before the next operator), and every right
    operand already round-trips ([Pexpr]). *)
Fixpoint spine_ok (k : nat) (ps : list (BinOp * GoExpr)) : Prop :=
  match ps with
  | [] => True
  | (o, r) :: ps' => k <= binop_prec o /\ Pexpr r
      /\ (match ps' with [] => True | (o2, _) :: _ => binop_prec o2 <= binop_prec o end)
      /\ spine_ok k ps'
  end.

Lemma pairs_fuel_pos : forall ps, 1 <= pairs_fuel ps.
Proof. intro ps. destruct ps as [ | [o r] ps' ]; cbn; lia. Qed.

(** SPINE FOLD — [parse_climb] consumes a printed left-leaning spine EXACTLY, left-folding it back to
    [fold_pairs base ps] and stopping at the [good] tail.  Induction on the pair list; each step recovers
    one operator ([op_match_binop]), parses the right operand ([Pexpr]), folds, and recurses. *)
Lemma parse_climb_pairs : forall ps k base rest F,
  spine_ok k ps -> tail_ok k rest -> pairs_fuel ps <= F ->
  parse_climb F k base (print_pairs ps ++ rest) = Some (fold_pairs base ps, rest).
Proof.
  induction ps as [ | [o r] ps' IH ]; intros k base rest F Hsp Htl HF.
  - cbn [print_pairs fold_pairs] in *. destruct F as [ | f ]; [ cbn in HF; lia | ].
    apply tail_ok_climb_stop; exact Htl.
  - cbn [pairs_fuel] in HF. destruct F as [ | f ]; [ lia | ].
    destruct Hsp as [ Hk [ Hpr [ Hnext Hsp' ] ] ].
    cbn [print_pairs fold_pairs]. rewrite parse_climb_S.
    (* expose the leading operator *)
    rewrite sapp_assoc, op_match_binop.
    assert (Hleb : Nat.leb k (binop_prec o) = true) by (apply Nat.leb_le; exact Hk).
    rewrite Hleb.
    (* parse the right operand at level S(prec o), tail = print_pairs ps' ++ rest *)
    assert (Htl2 : tail_ok (S (binop_prec o)) (print_pairs ps' ++ rest)).
    { destruct ps' as [ | [o2 r2] ps'' ].
      - cbn [print_pairs]. apply (tail_ok_mono k); [ exact Htl | lia ].
      - right; right. cbn [print_pairs]. rewrite sapp_assoc, op_match_binop.
        eexists; eexists; split; [ reflexivity | lia ]. }
    pose proof (pairs_fuel_pos ps') as Hpos.
    rewrite sapp_assoc.
    rewrite (Hpr (S (binop_prec o)) (S (binop_prec o)) (print_pairs ps' ++ rest) f
                 (le_n _) Htl2 ltac:(lia)).
    apply IH; [ exact Hsp' | exact Htl | lia ].
Qed.

(** ---- LEFT-SPINE DECOMPOSITION ---- [lspine fl e] peels [e]'s left children as long as they print
    UNWRAPPED at the running floor (operator precedence [>= floor]), yielding the leftmost PRIMARY
    [base] (an atom, or a subtree that prints parenthesised), the floor [bfl] it sits at, and the spine
    of [(operator, right-operand)] pairs above it.  [print_expr fl e = print_expr bfl base ++ print_pairs
    ps] and [fold_pairs base ps = e]: the decomposition is print- and structure-faithful. *)
Fixpoint lspine (fl : nat) (e : GoExpr) : nat * GoExpr * list (BinOp * GoExpr) :=
  match e with
  | EAtom s => (fl, EAtom s, [])
  | EBin o l r =>
      if Nat.leb fl (binop_prec o)
      then let '(bfl, base, ps) := lspine (binop_prec o) l in (bfl, base, (ps ++ [(o, r)])%list)
      else (fl, EBin o l r, [])
  end.

Lemma ltb_false_of_leb : forall fl p, Nat.leb fl p = true -> Nat.ltb p fl = false.
Proof.
  intros fl p H. destruct (Nat.ltb p fl) eqn:E; [ | reflexivity ].
  apply Nat.ltb_lt in E. apply Nat.leb_le in H. lia.
Qed.

Lemma print_pairs_app : forall a b, print_pairs (a ++ b)%list = (print_pairs a ++ print_pairs b)%string.
Proof.
  induction a as [ | [o r] a IH ]; intro b; cbn [print_pairs app]; [ reflexivity | ].
  rewrite IH, !sapp_assoc. reflexivity.
Qed.

Lemma fold_pairs_app : forall a b base, fold_pairs base (a ++ b)%list = fold_pairs (fold_pairs base a) b.
Proof.
  induction a as [ | [o r] a IH ]; intros b base; cbn [fold_pairs app]; [ reflexivity | apply IH ].
Qed.

Lemma lspine_print : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> print_expr fl e = (print_expr bfl base ++ print_pairs ps)%string.
Proof.
  induction e as [ s | o l IHl r IHr ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [print_pairs]. rewrite sapp_nil_r. reflexivity.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H.
      rewrite (print_expr_unwrapped o l r fl (ltb_false_of_leb _ _ Eleb)), (IHl _ _ _ _ El),
              print_pairs_app. cbn [print_pairs]. rewrite sapp_nil_r, !sapp_assoc. reflexivity.
    + inversion H; subst. cbn [print_pairs]. rewrite sapp_nil_r. reflexivity.
Qed.

Lemma lspine_fold : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> fold_pairs base ps = e.
Proof.
  induction e as [ s | o l IHl r IHr ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H.
      rewrite fold_pairs_app. cbn [fold_pairs]. rewrite (IHl _ _ _ _ El). reflexivity.
    + inversion H; subst. reflexivity.
Qed.

(** [spine_ok] tolerates a LOWER climb level (more operators qualify), and accepts an operator [o]
    appended at the spine end when the existing spine already binds at [>= prec o] (the junction is
    non-increasing because every spine operator is [>= prec o]). *)
Lemma spine_ok_weaken : forall ps k k', spine_ok k ps -> k' <= k -> spine_ok k' ps.
Proof.
  induction ps as [ | [o r] ps' IH ]; intros k k' H Hle; cbn in *; [ exact I | ].
  destruct H as [ Hk [ Hpr [ Hnext Hsp' ] ] ].
  split; [ lia | split; [ exact Hpr | split; [ exact Hnext | apply (IH k); assumption ] ] ].
Qed.

Lemma spine_ok_snoc : forall ps o r, spine_ok (binop_prec o) ps -> Pexpr r ->
  spine_ok (binop_prec o) (ps ++ [(o, r)])%list.
Proof.
  induction ps as [ | [o1 r1] ps' IH ]; intros o r Hsp Hpr.
  - cbn. split; [ lia | split; [ exact Hpr | split; exact I ] ].
  - cbn [app spine_ok] in *. destruct Hsp as [ Hk1 [ Hpr1 [ Hnext1 Hsp1 ] ] ].
    split; [ exact Hk1 | split; [ exact Hpr1 | split ] ].
    + destruct ps' as [ | [o2 r2] ps'' ]; cbn [app]; [ exact Hk1 | exact Hnext1 ].
    + apply IH; [ exact Hsp1 | exact Hpr ].
Qed.

(** [spine_ok] of the decomposed spine: every operator binds at [>= fl], consecutive operators are
    non-increasing, and every right operand round-trips (the last via the strong IH, the rest via the
    structural IH on [l]).  This is where the per-operand [Pexpr] obligations are discharged. *)
Lemma lspine_spine_ok : forall e fl bfl base ps,
  (forall e', esize e' < esize e -> wf e' -> atomic_tree e' -> Pexpr e') ->
  wf e -> atomic_tree e -> lspine fl e = (bfl, base, ps) -> spine_ok fl ps.
Proof.
  induction e as [ s | o l IHl r IHr ]; intros fl bfl base ps Hsih Hwf Hat H.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. cbn [wf atomic_tree] in Hwf, Hat. destruct Hwf as [ Hwl Hwr ]. destruct Hat as [ Hal Har ].
    destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst.
      apply (spine_ok_weaken _ (binop_prec o)); [ | apply Nat.leb_le; exact Eleb ].
      apply spine_ok_snoc.
      * eapply IHl; [ | exact Hwl | exact Hal | exact El ].
        intros e' He' We Ae. apply Hsih; [ cbn; lia | exact We | exact Ae ].
      * apply Hsih; [ cbn; lia | exact Hwr | exact Har ].
    + inversion H; subst. exact I.
Qed.

(** Appending one [(o,r)] to a spine adds exactly [S (esize r)] fuel; hence base size and spine fuel
    partition [S (esize e)] — so [esize e < F] alone bounds BOTH the base parse and the spine fold. *)
Lemma pairs_fuel_snoc : forall ps o r, pairs_fuel (ps ++ [(o, r)])%list = pairs_fuel ps + (3 * esize r + 3).
Proof.
  induction ps as [ | [o1 r1] ps' IH ]; intros o r; cbn [app pairs_fuel]; [ lia | rewrite IH; lia ].
Qed.

Lemma esize_pos : forall e, 1 <= esize e.
Proof. induction e as [ | o l IHl r IHr ]; cbn [esize]; lia. Qed.

(** The crucial fuel accounting: base size and spine fuel partition exactly [S (3*esize e)].  Each spine
    pair [(o, r)] contributes [3*esize r + 3] (operand budget [3*esize r] + 2 wrap slack + 1 climb step),
    and [esize base + sum(esize r) + length = esize e] — so [3*esize base + pairs_fuel ps = 3*esize e + 1].
    Hence [pairs_fuel ps <= 3*esize e - 2] (base parse) and [3*esize base <= 3*esize e - 6] (spine fold)
    both sit under the [3*esize e] budget. *)
Lemma lspine_fuel3 : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> 3 * esize base + pairs_fuel ps = S (3 * esize e).
Proof.
  induction e as [ s | o l IHl r IHr ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H. rewrite pairs_fuel_snoc.
      pose proof (IHl _ _ _ _ El) as IH. cbn [esize]. lia.
    + inversion H; subst. cbn [esize pairs_fuel]. lia.
Qed.

(** The base prints as a PRIMARY at its floor [bfl] (an atom, or an [EBin] wrapped because [bfl] exceeds
    its operator precedence) and is well-formed / atomic — so [parse_primary] reads it. *)
Lemma lspine_base : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> wf e -> atomic_tree e ->
  wf base /\ atomic_tree base /\
  match base with EAtom _ => True | EBin o' _ _ => binop_prec o' < bfl end.
Proof.
  induction e as [ s | o l IHl r IHr ]; intros fl bfl base ps H Hwf Hat.
  - cbn in H. inversion H; subst. cbn [wf atomic_tree] in *.
    split; [ exact Hwf | split; [ exact Hat | exact I ] ].
  - cbn in H. cbn [wf atomic_tree] in Hwf, Hat. destruct Hwf as [ Hwl Hwr ]. destruct Hat as [ Hal Har ].
    destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H. apply (IHl _ _ _ _ El Hwl Hal).
    + inversion H; subst. cbn [wf atomic_tree].
      repeat split; [ exact Hwl | exact Hwr | exact Hal | exact Har | ].
      apply Nat.leb_gt in Eleb. exact Eleb.
Qed.

Lemma lspine_base_le : forall e fl bfl base ps, lspine fl e = (bfl, base, ps) -> esize base <= esize e.
Proof.
  induction e as [ s | o l IHl r IHr ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. pose proof (IHl _ _ _ _ El). cbn [esize]. lia.
    + inversion H; subst. cbn [esize]. lia.
Qed.

(** [parse_primary] on a "(" reads the parenthesised sub-expression (parses it at level 0, demands the
    closing ")"). *)
Lemma parse_primary_paren : forall f X, parse_primary (S f) ("(" ++ X)%string =
  match parse_expr f 0 X with
  | Some (e, s1) => match s1 with String c1 s2 => if is_close c1 then Some (e, s2) else None
                    | EmptyString => None end
  | None => None end.
Proof. intros f X. rewrite parse_primary_S. cbn [append]. reflexivity. Qed.

(** A string at which [op_match] fires is a good seam (it is non-empty and operator-led). *)
Lemma good_seam_opens : forall s, opens s = true -> good_seam s = true.
Proof.
  intros s H. destruct s as [ | c s' ]; [ unfold opens in H; cbn in H; discriminate | ].
  unfold good_seam. rewrite H. reflexivity.
Qed.

(** A printed non-empty spine, followed by anything, is operator-led — hence a good seam for the base
    scan that precedes it. *)
Lemma good_seam_pairs : forall ps rest, ps <> [] -> good_seam (print_pairs ps ++ rest) = true.
Proof.
  intros ps rest H. destruct ps as [ | [o r] ps' ]; [ contradiction | ].
  apply good_seam_opens. unfold opens. cbn [print_pairs]. rewrite !sapp_assoc, op_match_binop. reflexivity.
Qed.

(** [parse_primary] reads the decomposed base EXACTLY: an atom via [scan_atom], a wrapped sub-tree via
    the paren rule and its own round-trip ([Pexpr]).  [S (2*esize base) < F] gives the one extra unit the
    "(" consumes before the inner parse. *)
Lemma parse_primary_base : forall base bfl TAIL F,
  wf base -> atomic_tree base -> Pexpr base ->
  match base with EAtom _ => True | EBin o' _ _ => binop_prec o' < bfl end ->
  good_seam TAIL = true -> 3 * esize base + 3 < F ->
  parse_primary F (print_expr bfl base ++ TAIL)%string = Some (base, TAIL).
Proof.
  intros base bfl TAIL F Hwf Hat Hpr Hprim Hgs HF.
  destruct base as [ s | o' l' r' ].
  - (* EAtom s — [s : GoAtom]; [build_atom_str] recovers the structured atom uniformly *)
    cbn [print_expr].
    pose proof (atom_ok_atomic _ (atom_str_atom_ok s)) as Hatm.
    destruct F as [ | f ]; [ cbn in HF; lia | ].
    destruct (atom_str s) as [ | c s' ] eqn:Estr; [ cbn in Hatm; discriminate | ].
    rewrite parse_primary_S.
    assert (Hopen : is_open c = false).
    { unfold atomic in Hatm. apply andb_true_iff in Hatm. destruct Hatm as [ Hno _ ].
      apply negb_true_iff in Hno. exact Hno. }
    cbn [append]. rewrite Hopen.
    assert (Hscan : scan_atom 0 ((String c s') ++ TAIL)%string = (String c s', TAIL))
      by (apply scan_atom_correct; [ exact Hatm | exact Hgs ]).
    change ((String c s') ++ TAIL)%string with (String c (s' ++ TAIL))%string in Hscan.
    rewrite Hscan, <- Estr, build_atom_str. reflexivity.
  - (* EBin o' l' r' : wrapped at bfl since binop_prec o' < bfl *)
    assert (Hwrap : Nat.ltb (binop_prec o') bfl = true) by (apply Nat.ltb_lt; exact Hprim).
    rewrite (print_expr_wrapped o' l' r' bfl Hwrap).
    destruct F as [ | f ]; [ cbn in HF; lia | ].
    rewrite sapp_assoc, parse_primary_paren, sapp_assoc.
    assert (Hpo : Nat.ltb (binop_prec o') (binop_prec o') = false) by (apply Nat.ltb_ge; lia).
    rewrite <- (print_expr_unwrapped o' l' r' (binop_prec o') Hpo).
    assert (Htl0 : tail_ok 0 (")" ++ TAIL)%string).
    { right; left. exists ")"%char, TAIL. split; [ cbn [append]; reflexivity | reflexivity ]. }
    rewrite (Hpr 0 (binop_prec o') (")" ++ TAIL)%string f (Nat.le_0_l _) Htl0 ltac:(cbn [esize] in HF |- *; lia)).
    cbn [append]. reflexivity.
Qed.

(** THE UNIVERSAL ROUND-TRIP — by strong induction on tree size.  [Hunwr] proves the cases where [e]
    prints UNWRAPPED at [ctx] (an atom, or an [EBin] with [ctx <= prec]); the dispatch below sends an
    atom and the unwrapped [EBin] straight to it, and a WRAPPED [EBin] (prec < ctx) — whose text is
    "(" ++ (e printed unwrapped at prec) ++ ")" — through the paren rule to [Hunwr] at the SAME [e].  No
    circularity: [Hunwr] recurses only into strictly smaller sub-trees (operands and base) via the IH. *)
Lemma print_parse_expr_n : forall n e, esize e <= n -> wf e -> atomic_tree e -> Pexpr e.
Proof.
  induction n as [ | n IH ]; intros e Hsz Hwf Hat; [ destruct e; cbn [esize] in Hsz; lia | ].
  assert (Hunwr : forall k ctx rest F, k <= ctx -> tail_ok k rest -> 3 * esize e < F ->
            match e with EAtom _ => True | EBin o _ _ => ctx <= binop_prec o end ->
            parse_expr F k (print_expr ctx e ++ rest) = Some (e, rest)).
  { intros k ctx rest F Hk Htl HF Hctx. destruct e as [ s | o l r ].
    - (* EAtom s — [s : GoAtom]; [build_atom_str] recovers it uniformly *)
      cbn [print_expr].
      pose proof (atom_ok_atomic _ (atom_str_atom_ok s)) as Hatm.
      destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
      destruct (atom_str s) as [ | c s' ] eqn:Estr; [ cbn in Hatm; discriminate | ].
      destruct f0 as [ | f1 ]; [ cbn [esize] in HF; lia | ].
      rewrite parse_expr_S.
      assert (Hopen : is_open c = false).
      { unfold atomic in Hatm. apply andb_true_iff in Hatm. destruct Hatm as [ Hno _ ].
        apply negb_true_iff in Hno. exact Hno. }
      assert (Hgs : good_seam rest = true) by (apply (tail_ok_good_seam k); exact Htl).
      assert (Hpp : parse_primary (S f1) ((String c s') ++ rest)%string = Some (EAtom s, rest)).
      { rewrite parse_primary_S. cbn [append]. rewrite Hopen.
        assert (Hscan : scan_atom 0 ((String c s') ++ rest)%string = (String c s', rest))
          by (apply scan_atom_correct; [ exact Hatm | exact Hgs ]).
        change ((String c s') ++ rest)%string with (String c (s' ++ rest))%string in Hscan.
        rewrite Hscan, <- Estr, build_atom_str. reflexivity. }
      rewrite Hpp. apply tail_ok_climb_stop. exact Htl.
    - (* EBin o l r, unwrapped: Hctx : ctx <= binop_prec o *)
      assert (Hleb : Nat.leb ctx (binop_prec o) = true) by (apply Nat.leb_le; exact Hctx).
      destruct (lspine (binop_prec o) l) as [ [ bfl base ] ps0 ] eqn:El.
      assert (Els : lspine ctx (EBin o l r) = (bfl, base, (ps0 ++ [(o, r)])%list))
        by (cbn [lspine]; rewrite Hleb, El; reflexivity).
      pose proof (lspine_fold _ _ _ _ _ Els) as Hfold.
      destruct (lspine_base _ _ _ _ _ Els Hwf Hat) as [ Hwb [ Hab Hprim ] ].
      pose proof (lspine_fuel3 _ _ _ _ _ Els) as Hf3.
      pose proof (lspine_base_le _ _ _ _ _ El) as Hble.
      pose proof (pairs_fuel_snoc ps0 o r) as Hpfs.
      pose proof (pairs_fuel_pos ps0) as Hpp0. pose proof (esize_pos r) as Her.
      pose proof (esize_pos base) as Heb.
      assert (HPbase : Pexpr base) by (apply (IH base); [ cbn [esize] in Hsz; lia | exact Hwb | exact Hab ]).
      assert (Hspine : spine_ok k (ps0 ++ [(o, r)])%list).
      { apply (spine_ok_weaken _ ctx); [ | exact Hk ].
        eapply lspine_spine_ok; [ | exact Hwf | exact Hat | exact Els ].
        intros e' He' We Ae. apply (IH e'); [ lia | exact We | exact Ae ]. }
      rewrite (lspine_print _ _ _ _ _ Els), sapp_assoc.
      destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
      assert (Hpp : parse_primary f0 (print_expr bfl base ++ (print_pairs (ps0 ++ [(o, r)]) ++ rest))%string
                  = Some (base, print_pairs (ps0 ++ [(o, r)]) ++ rest)).
      { apply parse_primary_base;
          [ exact Hwb | exact Hab | exact HPbase | exact Hprim
          | apply good_seam_pairs; destruct ps0; discriminate
          | cbn [esize] in HF, Hf3; rewrite Hpfs in Hf3; lia ]. }
      rewrite parse_expr_S, Hpp.
      change (parse_climb f0 k base (print_pairs (ps0 ++ [(o, r)]) ++ rest) = Some (EBin o l r, rest)).
      rewrite (parse_climb_pairs (ps0 ++ [(o, r)]) k base rest f0 Hspine Htl
                 ltac:(cbn [esize] in HF, Hf3; rewrite Hpfs in Hf3; lia)).
      rewrite Hfold. reflexivity. }
  unfold Pexpr. intros k ctx rest F Hk Htl HF.
  destruct e as [ s | o l r ].
  - apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
  - destruct (Nat.ltb (binop_prec o) ctx) eqn:Ewrap.
    + (* wrapped *)
      rewrite (print_expr_wrapped o l r ctx Ewrap).
      destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
      destruct f0 as [ | f1 ]; [ cbn [esize] in HF; lia | ].
      assert (Hpo : Nat.ltb (binop_prec o) (binop_prec o) = false) by (apply Nat.ltb_ge; lia).
      assert (Htl0 : tail_ok 0 (")" ++ rest)%string)
        by (right; left; exists ")"%char, rest; split; [ cbn [append]; reflexivity | reflexivity ]).
      assert (Hpp_w : parse_primary (S f1)
                (("(" ++ (print_expr (binop_prec o) l ++ binop_text o ++ print_expr (S (binop_prec o)) r) ++ ")") ++ rest)%string
              = Some (EBin o l r, rest)).
      { rewrite sapp_assoc, parse_primary_paren, sapp_assoc.
        rewrite <- (print_expr_unwrapped o l r (binop_prec o) Hpo).
        rewrite (Hunwr 0 (binop_prec o) (")" ++ rest)%string f1 (Nat.le_0_l _) Htl0
                   ltac:(cbn [esize] in HF |- *; lia) (Nat.le_refl _)).
        cbn [append]. reflexivity. }
      rewrite parse_expr_S, Hpp_w.
      change (parse_climb (S f1) k (EBin o l r) rest = Some (EBin o l r, rest)).
      apply tail_ok_climb_stop. exact Htl.
    + (* unwrapped *)
      apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia
                   | apply Nat.ltb_ge in Ewrap; exact Ewrap ].
Qed.

(** The headline — UNCONDITIONAL now.  [EAtom] carries an [Atom] (its [atom_ok = atomic && balanced_b]
    proof IN THE TYPE), so [wf e] and [atomic_tree e] hold for EVERY [e] by construction (discharged via
    [wf_always]/[atomic_tree_always]) — a malformed atom is unrepresentable, so there is no side-condition
    to assume.  [print_expr] emits text the Rocq [parse_expr] re-reads to the SAME tree (precedence-correct,
    not merely balanced).  HONEST SCOPE: this remains printer/parser SELF-CONSISTENCY for the Rocq grammar —
    NOT yet a theorem about Go's OWN parser (a Go-subset recognition theorem is the remaining gap, #10). *)
Theorem print_parse_expr : forall e,
  parse_expr (3 * esize e + 3) 0 (print_expr 0 e) = Some (e, "").
Proof.
  intros e.
  rewrite <- (sapp_nil_r (print_expr 0 e)).
  apply (print_parse_expr_n (esize e) e (le_n _) (wf_always e) (atomic_tree_always e));
    [ lia | left; reflexivity | lia ].
Qed.

(** FAITHFULNESS COROLLARY — INJECTIVITY of the expression printer (the analog of [print_ty_inj], now for
    [GoExpr]): two expressions that print alike re-parse to the same tree, hence are equal.  So the emitted
    expression text NEVER conflates two distinct expressions — derived directly from the (unconditional)
    round-trip, lifting both parses to a common fuel via [parse_mono]. *)
Corollary print_expr_inj : forall e1 e2, print_expr 0 e1 = print_expr 0 e2 -> e1 = e2.
Proof.
  intros e1 e2 He.
  set (F := 3 * esize e1 + 3 + (3 * esize e2 + 3)).
  assert (HF1 : 3 * esize e1 + 3 <= F) by (unfold F; lia).
  assert (HF2 : 3 * esize e2 + 3 <= F) by (unfold F; lia).
  assert (R1 : parse_expr F 0 (print_expr 0 e1) = Some (e1, "")).
  { apply (proj1 (parse_mono F _ HF1)). apply print_parse_expr. }
  assert (R2 : parse_expr F 0 (print_expr 0 e2) = Some (e2, "")).
  { apply (proj1 (parse_mono F _ HF2)). apply print_parse_expr. }
  rewrite He in R1. rewrite R1 in R2. injection R2 as Ht. exact Ht.
Qed.

(** ============================================================================
    ---- SEPARATED LISTS ---- the OTHER pervasive structural primitive: a comma-joined sequence
    (function arguments, composite-literal elements, type-argument lists, multi-return values, struct
    fields).  [go.ml] rendered these with Coq's [prlist_with_sep]; [print_sep] is the verified
    replacement — it joins the already-rendered pieces with [sep], NO leading or trailing separator
    (the off-by-one a hand-rolled join gets wrong).  The empty list prints empty, a singleton prints
    itself, and only INTERIOR gaps get a separator. *)
Fixpoint print_sep (sep : string) (xs : list string) : string :=
  match xs with
  | []        => ""
  | x :: xs'  => match xs' with
                 | []     => x
                 | _ :: _ => (x ++ sep ++ print_sep sep xs')%string
                 end
  end.

Example print_sep_empty  : print_sep ", " [] = "".              Proof. reflexivity. Qed.
Example print_sep_single : print_sep ", " ["a"] = "a".          Proof. reflexivity. Qed.
Example print_sep_three  : print_sep ", " ["a"; "b"; "c"] = "a, b, c". Proof. reflexivity. Qed.

(** Concatenation of two balanced strings is balanced (depth/nneg are homomorphic over append). *)
Lemma balanced_app : forall a b, balanced a -> balanced b -> balanced (a ++ b).
Proof.
  intros a b [Ha Hna] [Hb Hnb]. unfold balanced. split.
  - rewrite depth_app, Ha. exact Hb.
  - rewrite nneg_app, Ha. split; assumption.
Qed.

(** SAFETY — a separated list of well-bracketed pieces (and a well-bracketed separator) is itself
    well-bracketed: [print_sep] never introduces an unmatched paren. *)
Theorem print_sep_balanced : forall xs sep,
  balanced sep -> (forall x, In x xs -> balanced x) -> balanced (print_sep sep xs).
Proof.
  induction xs as [ | x xs IH ]; intros sep Hsep Hall.
  - (* [] *) unfold balanced; cbn [print_sep depth nneg]. split; [ reflexivity | exact I ].
  - (* x :: xs *) destruct xs as [ | y xs' ].
    + (* singleton *) cbn [print_sep]. apply Hall. left. reflexivity.
    + (* x :: y :: xs' *) cbn [print_sep].
      apply balanced_app; [ apply Hall; left; reflexivity | ].
      apply balanced_app; [ exact Hsep | ].
      apply IH; [ exact Hsep | ]. intros z Hz. apply Hall. right. exact Hz.
Qed.

(** GATE — goprint.v is part of the trust base: the EXTRACTED printer is governed by these theorems, so
    they MUST be axiom-free.  The build (Dockerfile prover stage) compiles goprint.v standalone and FAILS
    if any of these rests on an unproved assumption (a non-empty Axioms section in its Print Assumptions).
    Keep this list in sync with the headline results below. *)
Print Assumptions parse_print_ty.
Print Assumptions print_ty_inj.
Print Assumptions esc_string_roundtrip.
Print Assumptions print_parse_Z.
Print Assumptions print_parse_hex.
Print Assumptions print_parse_float_hex.
Print Assumptions print_expr_balanced.
Print Assumptions print_parse_expr.
Print Assumptions print_expr_inj.
Print Assumptions print_sep_balanced.

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_expr print_sep print_float_hex atomic atom_ok go_ident nominal_type_ident.
