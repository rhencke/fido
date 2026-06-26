(** ============================================================================
    THE VERIFIED PRINTER — slice 1 (the gap #10 / review #12 path).

    The trusted/unverified part of Fido is the hand-written OCaml in [plugin/go.ml]: no theorem relates
    the Go string it emits to the source term.  The agreed fix (no more raw OCaml): the PRINTER moves
    INTO Rocq — a Go AST + a pretty-printer defined here as Rocq functions — is EXTRACTED to OCaml (so
    the plugin runs the SAME function Rocq reasons about, not a hand-written re-implementation), and
    CORRECTNESS theorems are layered atop it.  This file is the foundation; later slices grow the AST to
    cover the emitted fragment, rewire [go.ml] to call the extracted printer, and delete the raw OCaml.

    ⚠️ HONEST SCOPE OF "VERIFIED" (review #7 item 3) — "verified printer" here means: the printer is
    verified AGAINST THE Rocq PARSER in this file (a printer/parser round-trip + injectivity for THIS
    Rocq grammar), NOT against Go's own parser.  There is NO theorem yet that Go's compiler reads the
    emitted text as the same AST — that Go-subset RECOGNITION theorem (emitted grammar ⊆ Go grammar) is
    the remaining gap (#10).  So [print_parse_expr] / [print_ty_inj] are ROCQ-GRAMMAR self-consistency
    results, and must not be read as "Go printer correctness."  (The plugin → emitted-bytes path also has
    a trusted [gofmt] post-step — see the Makefile — so even the byte-exact final text is not yet in-proof.)

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

(** ---- QUOTE-AWARE STRING-LITERAL SCANNER (external review #5 item 1) ---- [scan_strlit_body s] reads
    the BODY of a string literal — the bytes AFTER the opening quote — in STRING/ESCAPE mode: a backslash
    takes the NEXT byte verbatim (so [\] then a quote is body, NOT the close), every other byte is body,
    and the first UNescaped quote ends the body.  Returns [(body, rest-after-the-closing-quote)], or
    [None] if unterminated.  This is the lexical core that lets a quoted literal be parsed as its OWN
    primary — NOT scanned as generic Go source — so a valid Go string whose CONTENTS would confuse the
    expression atom scanner (a space-then-operator like "a + b", or an unmatched bracket like "[") is
    handled correctly, instead of being rejected by [atom_ok]'s seam / bracket-stack checks. *)
Fixpoint scan_strlit_body (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c rest =>
      if Ascii.eqb c (ch 34) then Some (EmptyString, rest)               (* unescaped quote ends the body *)
      else if Ascii.eqb c (ch 92) then                                   (* backslash: next byte is verbatim *)
        match rest with
        | EmptyString      => None
        | String c2 rest2  =>
            match scan_strlit_body rest2 with
            | Some (body, r) => Some (String c (String c2 body), r)
            | None           => None
            end
        end
      else
        match scan_strlit_body rest with
        | Some (body, r) => Some (String c body, r)
        | None           => None
        end
  end.
(** The flagged cases — contents that the generic atom scanner mishandles — scan correctly here. *)
Example scan_plus_space : scan_strlit_body (esc_string "a + b" ++ String (ch 34) "X") = Some (esc_string "a + b", "X").
Proof. reflexivity. Qed.
Example scan_unmatched_bracket : scan_strlit_body (esc_string "[" ++ String (ch 34) "X") = Some (esc_string "[", "X").
Proof. reflexivity. Qed.
Example scan_escaped_quote : scan_strlit_body (esc_string "a""b" ++ String (ch 34) "X") = Some (esc_string "a""b", "X").
Proof. reflexivity. Qed.

(** [scan_strlit_body] INVERTS [esc_string]: scanning a printed body up to the closing quote recovers
    EXACTLY that body (no early stop on an escaped quote, no over-run).  This is the round-trip key for
    the string-literal primary.  Helpers + an [esc_byte]-case lemma (mirroring [unescape_esc_byte]). *)
Lemma eqb_ch_false : forall c k, k < 256 -> nat_of_ascii c <> k -> Ascii.eqb c (ch k) = false.
Proof.
  intros c k Hk Hne. destruct (Ascii.eqb c (ch k)) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E. exfalso. apply Hne. rewrite E. apply nat_of_ch. exact Hk.
Qed.
Lemma ch_ch_eqb : forall a b, a < 256 -> b < 256 -> Ascii.eqb (ch a) (ch b) = Nat.eqb a b.
Proof.
  intros a b Ha Hb. destruct (Nat.eqb a b) eqn:E.
  - apply Nat.eqb_eq in E. subst. apply Ascii.eqb_refl.
  - apply Nat.eqb_neq in E. apply eqb_ch_false; [ exact Hb | ]. rewrite nat_of_ch by exact Ha. exact E.
Qed.
Lemma esc_byte_app : forall b acc X, (esc_byte b acc ++ X)%string = esc_byte b (acc ++ X)%string.
Proof.
  intros b acc X. unfold esc_byte.
  destruct (Nat.eqb b 34); [ reflexivity | ].
  destruct (Nat.eqb b 92); [ reflexivity | ].
  destruct (Nat.eqb b 10); [ reflexivity | ].
  destruct (Nat.eqb b 9);  [ reflexivity | ].
  destruct (Nat.eqb b 13); [ reflexivity | ].
  destruct (andb (Nat.leb 32 b) (Nat.ltb b 127)); reflexivity.
Qed.
Lemma hexdig_ne_q : forall k, k < 16 -> Ascii.eqb (hexdig k) (ch 34) = false.
Proof.
  intros k Hk. apply eqb_ch_false; [ lia | ]. unfold hexdig.
  rewrite Ascii.nat_ascii_embedding by (destruct (Nat.ltb k 10); lia).
  destruct (Nat.ltb k 10) eqn:Eh; [ apply Nat.ltb_lt in Eh | apply Nat.ltb_ge in Eh ]; lia.
Qed.
Lemma hexdig_ne_bs : forall k, k < 16 -> Ascii.eqb (hexdig k) (ch 92) = false.
Proof.
  intros k Hk. apply eqb_ch_false; [ lia | ]. unfold hexdig.
  rewrite Ascii.nat_ascii_embedding by (destruct (Nat.ltb k 10); lia).
  destruct (Nat.ltb k 10) eqn:Eh; [ apply Nat.ltb_lt in Eh | apply Nat.ltb_ge in Eh ]; lia.
Qed.
Local Opaque ch.
Lemma scan_strlit_body_esc_byte : forall c Y,
  scan_strlit_body (esc_byte (nat_of_ascii c) Y) =
    match scan_strlit_body Y with Some (b, r) => Some (esc_byte (nat_of_ascii c) b, r) | None => None end.
Proof.
  intros c Y. assert (Hc : nat_of_ascii c < 256) by apply nat_of_ascii_lt_256.
  unfold esc_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34.
  { cbn [scan_strlit_body]. rewrite (ch_ch_eqb 92 34) by lia. rewrite (ch_ch_eqb 92 92) by lia.
    destruct (scan_strlit_body Y) as [ [b r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92.
  { cbn [scan_strlit_body]. rewrite (ch_ch_eqb 92 34) by lia. rewrite (ch_ch_eqb 92 92) by lia.
    destruct (scan_strlit_body Y) as [ [b r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10.
  { cbn [scan_strlit_body]. rewrite (ch_ch_eqb 92 34) by lia. rewrite (ch_ch_eqb 92 92) by lia.
    destruct (scan_strlit_body Y) as [ [b r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 9) eqn:E9.
  { cbn [scan_strlit_body]. rewrite (ch_ch_eqb 92 34) by lia. rewrite (ch_ch_eqb 92 92) by lia.
    destruct (scan_strlit_body Y) as [ [b r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13.
  { cbn [scan_strlit_body]. rewrite (ch_ch_eqb 92 34) by lia. rewrite (ch_ch_eqb 92 92) by lia.
    destruct (scan_strlit_body Y) as [ [b r] | ]; reflexivity. }
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.ltb (nat_of_ascii c) 127)) eqn:Eprint.
  { cbn [scan_strlit_body].
    rewrite (ch_ch_eqb (nat_of_ascii c) 34) by lia. rewrite E34.
    rewrite (ch_ch_eqb (nat_of_ascii c) 92) by lia. rewrite E92.
    destruct (scan_strlit_body Y) as [ [b r] | ]; reflexivity. }
  { assert (Hhi : Nat.div (nat_of_ascii c) 16 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hlo : Nat.modulo (nat_of_ascii c) 16 < 16) by (apply Nat.mod_upper_bound; lia).
    cbn [scan_strlit_body]. rewrite (ch_ch_eqb 92 34) by lia. rewrite (ch_ch_eqb 92 92) by lia.
    cbn [scan_strlit_body]. rewrite (hexdig_ne_q _ Hhi), (hexdig_ne_bs _ Hhi).
    cbn [scan_strlit_body]. rewrite (hexdig_ne_q _ Hlo), (hexdig_ne_bs _ Hlo).
    destruct (scan_strlit_body Y) as [ [b r] | ]; reflexivity. }
Qed.
Local Transparent ch.
Lemma scan_strlit_body_esc : forall s rest,
  scan_strlit_body (esc_string s ++ String (ch 34) rest) = Some (esc_string s, rest).
Proof.
  induction s as [ | c s' IH ]; intro rest.
  - cbn [esc_string String.append scan_strlit_body]. rewrite (ch_ch_eqb 34 34) by lia. reflexivity.
  - cbn [esc_string]. rewrite esc_byte_app, scan_strlit_body_esc_byte, IH. reflexivity.
Qed.

(** ---- STRING-LITERAL ATOM RECOGNITION ---- [is_strlit a] decides whether [a] is a CANONICAL Go
    string literal — i.e. [a = print_string_lit s] for the [s] it decodes to.  It strips the opening
    and closing quote chars ([but_last] drops the trailing one), [unescape]s the body, and RE-PRINTS:
    the re-print equality IS the validator (it rejects a missing close, an internal UNescaped quote, or
    any non-canonical escaping — all of which re-escape to something not equal to [a]).  This lets
    [GoAtom]'s [AStringLit] structure a string literal SEPARATELY from a generic [ARaw] atom, so the
    printer surface is Go-shaped, not string-shaped. *)
Fixpoint but_last (s : string) : string :=
  match s with
  | EmptyString  => EmptyString
  | String c rest => match rest with EmptyString => EmptyString | String _ _ => String c (but_last rest) end
  end.
Definition is_strlit (a : string) : bool :=
  match a with
  | EmptyString  => false
  | String c rest =>
      andb (Ascii.eqb c (ch 34))
           (match rest with
            | EmptyString => false   (* a lone opening quote is not a literal *)
            | String _ _  => String.eqb (print_string_lit (unescape (but_last rest))) a
            end)
  end.
Lemma is_strlit_cons : forall a, is_strlit a = true -> exists rest, a = String (ch 34) rest.
Proof.
  intros a H. unfold is_strlit in H. destruct a as [ | c rest ]; [ discriminate | ].
  apply andb_true_iff in H. destruct H as [ Hq _ ]. apply Ascii.eqb_eq in Hq. subst c.
  exists rest. reflexivity.
Qed.
Example is_strlit_hello : is_strlit (print_string_lit "hello") = true. Proof. reflexivity. Qed.
Example is_strlit_empty : is_strlit (print_string_lit "") = true.      Proof. reflexivity. Qed.
Example is_strlit_lone_quote : is_strlit (String (ch 34) "") = false.  Proof. reflexivity. Qed.
(** [is_strlit] EXACTLY characterises a printed literal — both directions, for the string-literal primary:
    EVERY [print_string_lit val] is [is_strlit] (so [AStringLit] needs no [atom_ok]), and every [is_strlit]
    string IS some [print_string_lit val] (so the parser recovers the value).  [but_last_snoc] drops the
    appended closing quote. *)
Lemma but_last_snoc : forall X c, but_last (X ++ String c "")%string = X.
Proof.
  induction X as [ | a X' IH ]; intro c; [ reflexivity | ].
  cbn [String.append but_last]. destruct (X' ++ String c "")%string eqn:E.
  - destruct X'; cbn in E; discriminate.
  - rewrite <- E, IH. reflexivity.
Qed.
Lemma is_strlit_print_string_lit : forall val, is_strlit (print_string_lit val) = true.
Proof.
  intro val. unfold print_string_lit, is_strlit. rewrite Ascii.eqb_refl. cbn [andb].
  destruct (esc_string val ++ String (ch 34) "")%string eqn:E.
  - exfalso. destruct (esc_string val); cbn in E; discriminate.
  - rewrite <- E, but_last_snoc, esc_string_roundtrip. apply String.eqb_refl.
Qed.
Lemma is_strlit_print : forall lit, is_strlit lit = true -> exists val, lit = print_string_lit val.
Proof.
  intros lit H. unfold is_strlit in H. destruct lit as [ | c rest ]; [ discriminate | ].
  apply andb_true_iff in H. destruct H as [ _ Hrest ].
  destruct rest as [ | c2 rest2 ]; [ discriminate | ].
  exists (unescape (but_last (String c2 rest2))). apply String.eqb_eq in Hrest. symmetry. exact Hrest.
Qed.

(** [strlit_value lit] recovers the SEMANTIC VALUE from a printed literal [lit = "<esc body>"]: drop the
    opening quote, [but_last] drops the closing quote, [unescape] decodes the body.  The exact inverse of
    [print_string_lit] ([strlit_value_print_string_lit]) — used by the plugin's [mk_atom] to build
    [AStringLit value] from the literal text it already holds (review #7 item 4). *)
Definition strlit_value (lit : string) : string :=
  match lit with EmptyString => EmptyString | String _ body => unescape (but_last body) end.
Lemma strlit_value_print_string_lit : forall v, strlit_value (print_string_lit v) = v.
Proof.
  intro v. unfold strlit_value, print_string_lit. rewrite but_last_snoc, esc_string_roundtrip. reflexivity.
Qed.

(** ---- SELECTOR SPLITTING ---- [split_last_dot s] splits [s] at its LAST '.' into [(operand, field)]
    with [operand ++ "." ++ field = s] (or [None] if no '.').  Used to recover a selector atom [x.f]:
    a selector's field is an IDENTIFIER (dot-free), so the LAST '.' is the outermost selector's '.'.
    NO bracket-depth tracking is needed — a '.' inside brackets (e.g. [f(a.b)]) leaves a non-identifier
    suffix that the [go_ident field] check in [build_atom] rejects, so only a genuine selector '.' ever
    splits.  ([split_last_dot_snoc] is the round-trip key: re-splitting a printed [operand."."field]
    recovers exactly [(operand, field)] when the field is dot-free.) *)
Fixpoint split_last_dot (s : string) : option (string * string) :=
  match s with
  | EmptyString  => None
  | String c rest =>
      match split_last_dot rest with
      | Some (op, fld) => Some (String c op, fld)
      | None => if Ascii.eqb c (ch 46) then Some (EmptyString, rest) else None
      end
  end.
Fixpoint dot_free (s : string) : bool :=
  match s with EmptyString => true | String c rest => andb (negb (Ascii.eqb c (ch 46))) (dot_free rest) end.
Lemma dot_free_no_split : forall s, dot_free s = true -> split_last_dot s = None.
Proof.
  induction s as [ | c rest IH ]; intro H; [ reflexivity | ].
  cbn [dot_free] in H. apply andb_true_iff in H. destruct H as [ Hc Hr ].
  cbn [split_last_dot]. rewrite (IH Hr). apply negb_true_iff in Hc. rewrite Hc. reflexivity.
Qed.
Lemma split_last_dot_snoc : forall op fld, dot_free fld = true ->
  split_last_dot (op ++ String (ch 46) fld) = Some (op, fld).
Proof.
  induction op as [ | c op' IH ]; intros fld Hdf.
  - cbn [String.append split_last_dot]. rewrite (dot_free_no_split fld Hdf), Ascii.eqb_refl. reflexivity.
  - cbn [String.append split_last_dot]. rewrite (IH fld Hdf). reflexivity.
Qed.
Example split_xf   : split_last_dot "x.f"   = Some ("x", "f").    Proof. reflexivity. Qed.
Example split_abc  : split_last_dot "a.b.c" = Some ("a.b", "c").  Proof. reflexivity. Qed.
Example split_none : split_last_dot "xyz"   = None.               Proof. reflexivity. Qed.

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

(** UNARY operators (review #6 — [EUnary], the prefix node that shrinks [SRaw]): negate / not / bitwise-
    complement / dereference / address-of.  UNSPACED single-char prefixes (Go: [-x] [!b] [^x] [*p] [&x]),
    binding TIGHTER than every binary operator.  ([+] unary is omitted — the plugin never emits it; channel
    receive [<-] is a separate comma-ok form.)  [unop_char_of] gives the leading char the parser dispatches
    on; a [-] FOLLOWED BY A DIGIT is a negative literal ([is_dec] -> [SIntLit]), NOT [UNeg]. *)
(** NB: unary [-] is DELIBERATELY OMITTED.  [-5] is a negative LITERAL ([SIntLit]); were [-] a unary op,
    [EUnary UNeg (lit 5)] would also print [-5] and the round-trip could not disambiguate.  So [EUnary]
    carries only the four UNAMBIGUOUS prefixes [!]/[^]/[*]/[&] (and [-x] of a non-literal stays [SRaw]). *)
Inductive UnaryOp : Type := UNot | UXor | UDeref | UAddr.
Definition unop_text (o : UnaryOp) : string :=
  match o with UNot => "!" | UXor => "^" | UDeref => "*" | UAddr => "&" end.
Definition is_unop_char (c : ascii) : bool :=
  orb (orb (Ascii.eqb c (ch 33)) (Ascii.eqb c (ch 94))) (orb (Ascii.eqb c (ch 42)) (Ascii.eqb c (ch 38))).
Definition unop_char_of (c : ascii) : option UnaryOp :=
  if Ascii.eqb c (ch 33) then Some UNot
  else if Ascii.eqb c (ch 94) then Some UXor
  else if Ascii.eqb c (ch 42) then Some UDeref
  else if Ascii.eqb c (ch 38) then Some UAddr
  else None.
Lemma unop_text_char_of : forall o, exists c s,
  unop_text o = String c s /\ s = EmptyString /\ unop_char_of c = Some o /\ is_unop_char c = true.
Proof. intro o; destruct o; cbn; eauto 10. Qed.


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
(** ---- INDEX SPLITTING ---- [split_last_idx s] splits an index atom [operand[index]] at the '[' matching
    its FINAL ']' (the LAST top-level '['), returning [(operand, index)].  QUOTE-AWARE: brackets inside a
    string literal are opaque (so [m["["]] splits as [(m, "[")], not at the inner '['), tracking in-string
    ([instr]) and escape ([esc]) state.  [split_idx_aux] keeps the LAST depth-0 '[' by preferring a split
    found later in the string; the foundation for [SIndex], analogous to [split_last_dot] for [SSelector]. *)
Fixpoint split_idx_aux (instr esc : bool) (d : nat) (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c s' =>
      let '(instr', esc', d', is_split) :=
        if esc then (instr, false, d, false)
        else if instr then
          (if Ascii.eqb c (ch 92) then (true, true, d, false)
           else if Ascii.eqb c (ch 34) then (false, false, d, false)
           else (true, false, d, false))
        else
          (if Ascii.eqb c (ch 34) then (true, false, d, false)
           else if is_bopen c then (false, false, S d, andb (Nat.eqb d 0) (Ascii.eqb c (ch 91)))
           else if is_bclose c then (false, false, Nat.pred d, false)
           else (false, false, d, false))
      in
      match split_idx_aux instr' esc' d' s' with
      | Some (op', idx') => Some (String c op', idx')
      | None => if is_split then Some (EmptyString, s') else None
      end
  end.
Fixpoint last_char (s : string) : option ascii :=
  match s with EmptyString => None | String c EmptyString => Some c | String _ s' => last_char s' end.
Definition split_last_idx (s : string) : option (string * string) :=
  match split_idx_aux false false 0 s with
  | Some (op, idxb) =>
      match last_char idxb with
      | Some lc => if Ascii.eqb lc (ch 93) then Some (op, but_last idxb) else None
      | None => None
      end
  | None => None
  end.
Example split_idx_ai   : split_last_idx "a[i]"    = Some ("a", "i").       Proof. reflexivity. Qed.
Example split_idx_aij  : split_last_idx "a[i][j]" = Some ("a[i]", "j").    Proof. reflexivity. Qed.
Example split_idx_call : split_last_idx "f(x)[k]" = Some ("f(x)", "k").    Proof. reflexivity. Qed.
Example split_idx_none : split_last_idx "xyz"     = None.                  Proof. reflexivity. Qed.
(* QUOTE-AWARE: the '[' INSIDE the string-literal index "[" is opaque — the split is the operand's '['. *)
Example split_idx_strkey : split_last_idx "m[""[""]" = Some ("m", """[""").  Proof. reflexivity. Qed.
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
      if Ascii.eqb c (ch 34) then
        (* QUOTE-AWARE: the string literal is part of the atom — reconstruct dquote ++ body ++ dquote and continue
           scanning AT THE SAME DEPTH after the close quote (no bracket/seam inside the literal). *)
        let (a, rest) :=
          (fix skip (t : string) : string * string :=
             match t with
             | EmptyString => (EmptyString, EmptyString)                 (* unterminated *)
             | String e t' =>
                 if Ascii.eqb e (ch 34) then
                   let (a2, r2) := scan_atom d t' in (String e a2, r2)   (* close quote, then resume *)
                 else if Ascii.eqb e (ch 92) then
                   match t' with
                   | EmptyString => (String e EmptyString, EmptyString)
                   | String f t'' => let (a2, r2) := skip t'' in (String e (String f a2), r2)
                   end
                 else let (a2, r2) := skip t' in (String e a2, r2)
             end) s'
        in (String c a, rest)
      else if andb (Nat.eqb d 0) (orb (opens (String c s')) (is_close c))
      then (EmptyString, String c s')
      else let d' := if is_bopen c then S d else if is_bclose c then Nat.pred d else d in
           let (a, rest) := scan_atom d' s' in (String c a, rest)
  end.
(** [scan_skip d t] — the in-string reconstruction of [scan_atom] (named, mirrors [bstack_skip]). *)
Fixpoint scan_skip (d : nat) (t : string) : string * string :=
  match t with
  | EmptyString => (EmptyString, EmptyString)
  | String e t' =>
      if Ascii.eqb e (ch 34) then let (a2, r2) := scan_atom d t' in (String e a2, r2)
      else if Ascii.eqb e (ch 92) then
        match t' with
        | EmptyString => (String e EmptyString, EmptyString)
        | String f t'' => let (a2, r2) := scan_skip d t'' in (String e (String f a2), r2)
        end
      else let (a2, r2) := scan_skip d t' in (String e a2, r2)
  end.
Lemma scan_atom_quote : forall d s',
  scan_atom d (String (ch 34) s') = (let (a, rest) := scan_skip d s' in (String (ch 34) a, rest)).
Proof.
  intros d s'. cbn [scan_atom]. rewrite Ascii.eqb_refl.
  assert (Hskip : (fix skip (t : string) : string * string :=
             match t with
             | EmptyString => (EmptyString, EmptyString)
             | String e t' =>
                 if Ascii.eqb e (ch 34) then let (a2, r2) := scan_atom d t' in (String e a2, r2)
                 else if Ascii.eqb e (ch 92) then
                   match t' with EmptyString => (String e EmptyString, EmptyString)
                   | String f t'' => let (a2, r2) := skip t'' in (String e (String f a2), r2) end
                 else let (a2, r2) := skip t' in (String e a2, r2)
             end) s' = scan_skip d s').
  { generalize s'. fix IH 1. intro t. destruct t as [ | e t' ]; [ reflexivity | ].
    cbn [scan_skip]. destruct (Ascii.eqb e (ch 34)); [ reflexivity | ].
    destruct (Ascii.eqb e (ch 92)); [ destruct t' as [ | f t'' ]; [ reflexivity | rewrite IH; reflexivity ]
                                    | rewrite IH; reflexivity ]. }
  rewrite Hskip. reflexivity.
Qed.

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
      if Ascii.eqb c (ch 34) then
        (fix skip (t : string) : bool :=                          (* QUOTE-AWARE — skip the opaque literal *)
           match t with
           | EmptyString => false
           | String e t' =>
               if Ascii.eqb e (ch 34) then atomic_from d t'
               else if Ascii.eqb e (ch 92) then
                 match t' with EmptyString => false | String _ t'' => skip t'' end
               else skip t'
           end) s'
      else if andb (Nat.eqb d 0) (orb (orb (opens (String c s')) (is_bclose c)) (andb (is_space c) (op_after s')))
      then false
      else atomic_from (if is_bopen c then S d else if is_bclose c then Nat.pred d else d) s'
  end.
(** [atomic_skip d t] — the string-literal skip of [atomic_from], named (mirrors [bstack_skip]). *)
Fixpoint atomic_skip (d : nat) (t : string) : bool :=
  match t with
  | EmptyString => false
  | String e t' =>
      if Ascii.eqb e (ch 34) then atomic_from d t'
      else if Ascii.eqb e (ch 92) then
        match t' with EmptyString => false | String _ t'' => atomic_skip d t'' end
      else atomic_skip d t'
  end.
Lemma atomic_from_quote : forall d s', atomic_from d (String (ch 34) s') = atomic_skip d s'.
Proof.
  intros d s'. cbn [atomic_from]. rewrite Ascii.eqb_refl.
  generalize s'. fix IH 1. intro t. destruct t as [ | e t' ]; [ reflexivity | ].
  cbn [atomic_skip]. destruct (Ascii.eqb e (ch 34)); [ reflexivity | ].
  destruct (Ascii.eqb e (ch 92)); [ destruct t' as [ | f t'' ]; [ reflexivity | apply IH ] | apply IH ].
Qed.
(** STRICT bracket validation — a real bracket STACK.  The looser [atomic_from] above tracks only
    COMBINED depth (one counter), so [ [} ] / [ {] ] / [ f([}) ] slip through (combined depth returns to
    0).  [close_of] maps an open bracket to its required close; [bstack_ok st] PUSHES that close on an
    open and POPS-IF-MATCHING on a close (a mismatched close, or a close on an empty stack, FAILS) — so
    [(] closes only with [)], [[] with []], [{] with [}].  Same depth-0 SEAM guard as [atomic_from] (at
    the top — empty stack — no operator and no space-then-op).  [atomic] uses THIS for its bracket check;
    [atomic_from] is retained only as the parser scan's depth helper, linked by [bstack_ok_atomic_from]. *)
Definition close_of (c : ascii) : ascii :=
  if Ascii.eqb c (ascii_of_nat 40) then ascii_of_nat 41
  else if Ascii.eqb c (ascii_of_nat 91) then ascii_of_nat 93
  else ascii_of_nat 125.
Fixpoint bstack_ok (st : list ascii) (s : string) : bool :=
  match s with
  | EmptyString => match st with nil => true | _ => false end
  | String c s' =>
      if Ascii.eqb c (ch 34) then
        (* QUOTE-AWARE: a string literal is OPAQUE — skip its body (backslash takes the next byte; the
           first UNescaped quote ends it, mirroring [scan_strlit_body]) so a bracket/operator char inside
           a literal is not counted by the stack/seam.  Continue [bstack_ok st] after the close quote. *)
        (fix skip (t : string) : bool :=
           match t with
           | EmptyString => false                                   (* unterminated literal *)
           | String d t' =>
               if Ascii.eqb d (ch 34) then bstack_ok st t'          (* close quote: resume after it *)
               else if Ascii.eqb d (ch 92) then
                 match t' with EmptyString => false | String _ t'' => skip t'' end   (* backslash: skip next byte *)
               else skip t'
           end) s'
      else if andb (match st with nil => true | _ => false end)
              (orb (opens (String c s')) (andb (is_space c) (op_after s')))
      then false
      else if is_bopen c then bstack_ok (cons (close_of c) st) s'
      else if is_bclose c then
        match st with nil => false | cons top st' => if Ascii.eqb c top then bstack_ok st' s' else false end
      else bstack_ok st s'
  end.
Lemma bstack_ok_cons : forall st c s',
  bstack_ok st (String c s') =
    if Ascii.eqb c (ch 34) then
      (fix skip (t : string) : bool :=
         match t with
         | EmptyString => false
         | String d t' =>
             if Ascii.eqb d (ch 34) then bstack_ok st t'
             else if Ascii.eqb d (ch 92) then
               match t' with EmptyString => false | String _ t'' => skip t'' end
             else skip t'
         end) s'
    else if andb (match st with nil => true | _ => false end)
            (orb (opens (String c s')) (andb (is_space c) (op_after s')))
    then false
    else if is_bopen c then bstack_ok (cons (close_of c) st) s'
    else if is_bclose c then
      match st with nil => false | cons top st' => if Ascii.eqb c top then bstack_ok st' s' else false end
    else bstack_ok st s'.
Proof. reflexivity. Qed.
(** [bstack_skip st t] — the string-literal SKIP as a standalone fixpoint (the same body inlined in
    [bstack_ok]'s quote branch), so the quote case of downstream proofs can name it.  [bstack_ok_quote]
    rewrites the quote branch to it. *)
Fixpoint bstack_skip (st : list ascii) (t : string) : bool :=
  match t with
  | EmptyString => false
  | String d t' =>
      if Ascii.eqb d (ch 34) then bstack_ok st t'
      else if Ascii.eqb d (ch 92) then
        match t' with EmptyString => false | String _ t'' => bstack_skip st t'' end
      else bstack_skip st t'
  end.
Lemma bstack_ok_quote : forall st s', bstack_ok st (String (ch 34) s') = bstack_skip st s'.
Proof.
  intros st s'. rewrite bstack_ok_cons, Ascii.eqb_refl.
  generalize s'. fix IH 1. intro t. destruct t as [ | d t' ]; [ reflexivity | ].
  cbn [bstack_skip]. destruct (Ascii.eqb d (ch 34)); [ reflexivity | ].
  destruct (Ascii.eqb d (ch 92)); [ destruct t' as [ | e t'' ]; [ reflexivity | apply IH ] | apply IH ].
Qed.
(** Bracket chars are not spaces, an open is not a close, and a bracket never begins an operator. *)
Lemma bopen_not_bclose : forall c, is_bopen c = true -> is_bclose c = false.
Proof.
  intros c H. unfold is_bopen in H. unfold is_bclose.
  apply orb_true_iff in H. destruct H as [ H | H ];
    [ apply orb_true_iff in H; destruct H as [ H | H ] | ]; apply Ascii.eqb_eq in H; subst c; reflexivity.
Qed.
Lemma bopen_not_space : forall c, is_bopen c = true -> is_space c = false.
Proof.
  intros c H. unfold is_bopen in H. unfold is_space.
  apply orb_true_iff in H. destruct H as [ H | H ];
    [ apply orb_true_iff in H; destruct H as [ H | H ] | ]; apply Ascii.eqb_eq in H; subst c; reflexivity.
Qed.
Lemma bclose_not_space : forall c, is_bclose c = true -> is_space c = false.
Proof.
  intros c H. unfold is_bclose in H. unfold is_space.
  apply orb_true_iff in H. destruct H as [ H | H ];
    [ apply orb_true_iff in H; destruct H as [ H | H ] | ]; apply Ascii.eqb_eq in H; subst c; reflexivity.
Qed.
Lemma bopen_not_opens : forall c s', is_bopen c = true -> opens (String c s') = false.
Proof. intros c s' H. unfold opens. rewrite (op_match_not_space c s' (bopen_not_space c H)). reflexivity. Qed.
Lemma bclose_not_opens : forall c s', is_bclose c = true -> opens (String c s') = false.
Proof. intros c s' H. unfold opens. rewrite (op_match_not_space c s' (bclose_not_space c H)). reflexivity. Qed.
Definition atomic (s : string) : bool :=
  match s with EmptyString => false | String c _ => andb (negb (is_open c)) (bstack_ok nil s) end.

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
(** An identifier char is never the dquote (ch 34) — dispatches the QUOTE-AWARE scanner's quote branch to
    [false] for ident / decimal chars (stated with [ch 34] so it rewrites the scanner [if] directly). *)
Lemma is_idc_not_quote : forall c, is_idc c = true -> Ascii.eqb c (ch 34) = false.
Proof. intros c Hc. apply (is_idc_eqb_false c 34 Hc); reflexivity. Qed.
(** An identifier char is never a unary-operator char (so an ident/decimal-led atom is never [unary_op_led]
    — dispatches [parse_primary] past the unary branch to [scan_atom]). *)
Lemma is_idc_not_unop : forall c, is_idc c = true -> is_unop_char c = false.
Proof.
  intros c Hc. unfold is_unop_char, ch.
  rewrite (is_idc_eqb_false c 33 Hc eq_refl), (is_idc_eqb_false c 94 Hc eq_refl),
          (is_idc_eqb_false c 42 Hc eq_refl), (is_idc_eqb_false c 38 Hc eq_refl). reflexivity.
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
Lemma all_idc_bstack_ok : forall s, all_idc s = true -> bstack_ok nil s = true.
Proof.
  induction s as [ | c s' IH ]; intro H; [ reflexivity | ].
  cbn [all_idc] in H. apply andb_true_iff in H. destruct H as [ Hc Hs' ].
  rewrite bstack_ok_cons, (is_idc_not_quote c Hc).
  assert (Hopens : opens (String c s') = false).
  { unfold opens. rewrite (op_match_not_space c s' (is_idc_not_space c Hc)). reflexivity. }
  rewrite Hopens, (is_idc_not_space c Hc), (is_idc_not_bopen c Hc), (is_idc_not_bclose c Hc).
  cbn [orb andb]. apply IH; exact Hs'.
Qed.
(** The CORE "[identifier char] + [identifier tail] is an atom", factored so BOTH [go_ident] atoms and
    decimal-literal atoms reuse it (DRY): a leading [is_idc] char + [all_idc] tail is [atomic] (not
    "("-led, no depth-0 bracket / operator — operators are space-led) and paren-BALANCED (no parens). *)
Lemma all_idc_cons_atom_ok : forall c s, is_idc c = true -> all_idc s = true -> atom_ok (String c s) = true.
Proof.
  intros c s Hc Hs.
  assert (Hcs : all_idc (String c s) = true)
    by (cbn [all_idc]; apply andb_true_iff; split; [ exact Hc | exact Hs ]).
  unfold atom_ok. apply andb_true_iff. split.
  - unfold atomic. apply andb_true_iff. split.
    + apply negb_true_iff, is_idc_not_open; exact Hc.
    + apply all_idc_bstack_ok; exact Hcs.
  - unfold balanced_b. apply andb_true_iff. split.
    + rewrite (all_idc_depth (String c s) 0 Hcs); reflexivity.
    + apply all_idc_nneg_b; [ apply Z.le_refl | exact Hcs ].
Qed.
Lemma go_ident_atom_ok : forall s, go_ident s = true -> atom_ok s = true.
Proof.
  intros s H. unfold go_ident in H. destruct s as [ | c s' ]; [ discriminate | ].
  apply andb_true_iff in H. destruct H as [ H _ ]. apply andb_true_iff in H. destruct H as [ _ Hall ].
  cbn [all_idc] in Hall. apply andb_true_iff in Hall. destruct Hall as [ Hc Hs' ].
  apply all_idc_cons_atom_ok; [ exact Hc | exact Hs' ].
Qed.

(** ---- DECIMAL INTEGER LITERALS ARE ATOMS ---- a decimal digit (or a single leading '-') is never a
    space, bracket, or paren, so an optional-'-'-then-digits string is [atomic] (no depth-0 operator —
    operators are space-led) and paren-balanced; hence [is_dec s -> atom_ok s].  This lets [GoAtom]'s
    [AIntLit] carry only the [Z] (its text is [print_Z]), and — since a decimal is never [is_idstart]-led
    — [is_dec s -> go_ident s = false], so the round-trip DISAMBIGUATES a decimal from an identifier. *)
Definition is_dec_char (c : ascii) : bool :=
  andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57).
Fixpoint all_dec (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (is_dec_char c) (all_dec s') end.
Definition is_dec (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
      if Ascii.eqb c (ascii_of_nat 45)        (* leading '-' — the only non-digit a decimal literal admits *)
      then match rest with EmptyString => false | String _ _ => all_dec rest end
      else andb (is_dec_char c) (all_dec rest)
  end.
Lemma is_dec_char_is_idc : forall c, is_dec_char c = true -> is_idc c = true.
Proof.
  intros c H. unfold is_dec_char in H. unfold is_idc.
  apply orb_true_iff; left. apply orb_true_iff; left. exact H.
Qed.
Lemma all_dec_all_idc : forall s, all_dec s = true -> all_idc s = true.
Proof.
  induction s as [ | c s' IH ]; intro H; [ reflexivity | ].
  cbn [all_dec] in H. apply andb_true_iff in H. destruct H as [ Hc Hs ].
  cbn [all_idc]. apply andb_true_iff. split; [ apply is_dec_char_is_idc; exact Hc | apply IH; exact Hs ].
Qed.
Lemma is_dec_char_not_idstart : forall c, is_dec_char c = true -> is_idstart c = false.
Proof.
  intros c H. unfold is_dec_char in H. apply andb_true_iff in H. destruct H as [ Hlo Hhi ].
  apply Nat.leb_le in Hlo, Hhi. unfold is_idstart.
  apply orb_false_iff. split.
  - apply orb_false_iff. split; apply andb_false_iff; left; apply Nat.leb_gt; lia.
  - apply Nat.eqb_neq. lia.
Qed.
(** A non-space, non-bracket char prepended to a [bstack_ok nil] string stays [bstack_ok nil] (it neither
    opens an operator — operators are space-led — nor pushes/pops the bracket stack).  The leading '-' of
    a negative literal is exactly such a char; so is every identifier/decimal char. *)
Lemma bstack_ok_nil_plain : forall c s,
  Ascii.eqb c (ch 34) = false ->
  is_space c = false -> is_bopen c = false -> is_bclose c = false ->
  bstack_ok nil s = true -> bstack_ok nil (String c s) = true.
Proof.
  intros c s Hq Hsp Hbo Hbc Hs. rewrite bstack_ok_cons, Hq.
  assert (Ho : opens (String c s) = false)
    by (unfold opens; rewrite (op_match_not_space c s Hsp); reflexivity).
  rewrite Ho, Hsp, Hbo, Hbc. cbn [andb orb]. exact Hs.
Qed.
(** Appending a SELECTOR suffix ["." ++ <identifier chars>] to a [bstack_ok] string keeps it valid: the
    suffix adds no bracket, and — its leading '.' being a NON-operator char — cannot create or straddle a
    depth-0 operator seam (the "seam cannot be straddled" argument of [scan_atom_gen], via
    [op_match_second_nonop]).  Generalized over the stack for the induction.  Foundation for [ASelector]. *)
(** Combined with the string-literal SKIP state, by STRONG induction on a length bound (the backslash case
    of [bstack_skip] consumes TWO chars, so structural induction on [base] is too weak).  Proves BOTH that
    [bstack_ok] and [bstack_skip] are preserved by the [".f"] append; the quote / close-quote cases bridge
    between the two via [bstack_ok_quote]. *)
Lemma bstack_app_dotid : forall fld n base st, all_idc fld = true -> String.length base <= n ->
  (bstack_ok st base = true -> bstack_ok st (base ++ String (ch 46) fld)%string = true) /\
  (bstack_skip st base = true -> bstack_skip st (base ++ String (ch 46) fld)%string = true).
Proof.
  intros fld n. induction n as [ | n IH ]; intros base st Hf Hlen.
  - destruct base as [ | c base' ]; [ | cbn [String.length] in Hlen; lia ].
    split; [ | intro Hb; cbn [bstack_skip] in Hb; discriminate Hb ].
    intro Hb. cbn [bstack_ok] in Hb. destruct st as [ | t st0 ]; [ | discriminate Hb ].
    cbn [append]. rewrite bstack_ok_cons. assert (Hq : Ascii.eqb (ch 46) (ch 34) = false) by reflexivity.
    rewrite Hq. assert (Ho : opens (String (ch 46) fld) = false)
      by (unfold opens; rewrite (op_match_not_space (ch 46) fld eq_refl); reflexivity).
    rewrite Ho. cbn [is_space is_bopen is_bclose andb orb]. apply all_idc_bstack_ok; exact Hf.
  - destruct base as [ | c base' ].
    + split; [ | intro Hb; cbn [bstack_skip] in Hb; discriminate Hb ].
      intro Hb. cbn [bstack_ok] in Hb. destruct st as [ | t st0 ]; [ | discriminate Hb ].
      cbn [append]. rewrite bstack_ok_cons. assert (Hq : Ascii.eqb (ch 46) (ch 34) = false) by reflexivity.
      rewrite Hq. assert (Ho : opens (String (ch 46) fld) = false)
        by (unfold opens; rewrite (op_match_not_space (ch 46) fld eq_refl); reflexivity).
      rewrite Ho. cbn [is_space is_bopen is_bclose andb orb]. apply all_idc_bstack_ok; exact Hf.
    + cbn [String.length] in Hlen. assert (Hl' : String.length base' <= n) by lia.
      split.
      * intro Hb. cbn [append]. destruct (Ascii.eqb c (ch 34)) eqn:Eq.
        -- apply Ascii.eqb_eq in Eq. subst c. rewrite bstack_ok_quote in Hb |- *.
           apply (proj2 (IH base' st Hf Hl')); exact Hb.
        -- rewrite bstack_ok_cons in Hb. rewrite Eq in Hb. rewrite bstack_ok_cons. rewrite Eq.
           destruct (andb (match st with nil => true | _ => false end)
                          (orb (opens (String c base')) (andb (is_space c) (op_after base')))) eqn:Eseam;
             [ discriminate Hb | ].
           assert (Eseam2 : andb (match st with nil => true | _ => false end)
                     (orb (opens (String c (base' ++ String (ch 46) fld)))
                          (andb (is_space c) (op_after (base' ++ String (ch 46) fld)))) = false).
           { destruct st as [ | t st0 ]; cbn [andb] in Eseam |- *; [ | reflexivity ].
             apply orb_false_iff in Eseam. destruct Eseam as [ Hop Hsp ].
             apply orb_false_iff. split.
             - destruct (is_space c) eqn:Esc.
               + destruct base' as [ | c2 base'' ]; cbn [append].
                 * unfold opens. rewrite (op_match_second_nonop c (ch 46) fld eq_refl). reflexivity.
                 * cbn [andb op_after] in Hsp.
                   unfold opens. rewrite (op_match_second_nonop c c2 (base'' ++ String (ch 46) fld) Hsp). reflexivity.
               + unfold opens. rewrite (op_match_not_space c (base' ++ String (ch 46) fld) Esc). reflexivity.
             - destruct base' as [ | c2 base'' ]; cbn [append op_after].
               + assert (Hdot : is_op_char (ch 46) = false) by reflexivity. rewrite Hdot. apply andb_false_r.
               + cbn [op_after] in Hsp. exact Hsp. }
           rewrite Eseam2. destruct (is_bopen c) eqn:Ebo.
           ++ apply (proj1 (IH base' (close_of c :: st) Hf Hl')); exact Hb.
           ++ destruct (is_bclose c) eqn:Ebc.
              ** destruct st as [ | t st0 ]; [ discriminate Hb | ].
                 destruct (Ascii.eqb c t) eqn:Et;
                   [ apply (proj1 (IH base' st0 Hf Hl')); exact Hb | discriminate Hb ].
              ** apply (proj1 (IH base' st Hf Hl')); exact Hb.
      * intro Hb. cbn [append]. cbn [bstack_skip] in Hb |- *. destruct (Ascii.eqb c (ch 34)) eqn:Eq1.
        -- apply (proj1 (IH base' st Hf Hl')); exact Hb.
        -- destruct (Ascii.eqb c (ch 92)) eqn:Eq2.
           ++ destruct base' as [ | d base'' ]; [ cbn [bstack_skip] in Hb; discriminate Hb | ].
              cbn [append]. assert (Hl'' : String.length base'' <= n) by (cbn [String.length] in Hl'; lia).
              apply (proj2 (IH base'' st Hf Hl'')); exact Hb.
           ++ apply (proj2 (IH base' st Hf Hl')); exact Hb.
Qed.
Lemma bstack_ok_app_dotid : forall fld base st, all_idc fld = true ->
  bstack_ok st base = true -> bstack_ok st (base ++ String (ch 46) fld)%string = true.
Proof.
  intros fld base st Hf Hb.
  exact (proj1 (bstack_app_dotid fld (String.length base) base st Hf (le_n _)) Hb).
Qed.
Lemma is_dec_atom_ok : forall s, is_dec s = true -> atom_ok s = true.
Proof.
  intros s H. unfold is_dec in H. destruct s as [ | c rest ]; [ discriminate | ].
  destruct (Ascii.eqb c (ascii_of_nat 45)) eqn:Em.
  - (* leading '-': the digit tail is an atom, and prepending '-' preserves atomic + balanced *)
    apply Ascii.eqb_eq in Em. subst c.
    destruct rest as [ | c2 r2 ]; [ discriminate | ].
    pose proof (all_dec_all_idc _ H) as Hidc.
    unfold atom_ok. apply andb_true_iff. split.
    + unfold atomic. apply andb_true_iff. split.
      * apply negb_true_iff. reflexivity.
      * apply bstack_ok_nil_plain;
          [ reflexivity | reflexivity | reflexivity | reflexivity | apply all_idc_bstack_ok; exact Hidc ].
    + unfold balanced_b. apply andb_true_iff. split.
      * assert (Hd : depth 0 (String (ascii_of_nat 45) (String c2 r2)) = depth 0 (String c2 r2)) by reflexivity.
        rewrite Hd, (all_idc_depth (String c2 r2) 0 Hidc). reflexivity.
      * assert (Hn : nneg_b 0 (String (ascii_of_nat 45) (String c2 r2)) = nneg_b 0 (String c2 r2)) by reflexivity.
        rewrite Hn. apply all_idc_nneg_b; [ apply Z.le_refl | exact Hidc ].
  - (* leading digit: the whole string is all-idc, so reuse the identifier-atom core *)
    apply andb_true_iff in H. destruct H as [ Hc Hrest ].
    apply all_idc_cons_atom_ok; [ apply is_dec_char_is_idc; exact Hc | apply all_dec_all_idc; exact Hrest ].
Qed.
Lemma is_dec_not_go_ident : forall s, is_dec s = true -> go_ident s = false.
Proof.
  intros s H. unfold is_dec in H. destruct s as [ | c rest ]; [ discriminate | ].
  unfold go_ident. destruct (Ascii.eqb c (ascii_of_nat 45)) eqn:Em.
  - apply Ascii.eqb_eq in Em. subst c. reflexivity.
  - apply andb_true_iff in H. destruct H as [ Hc _ ].
    rewrite (is_dec_char_not_idstart c Hc). reflexivity.
Qed.

(** [print_Z] STRUCTURE: its output is always [is_dec] — "0", a run of decimal digits, or '-' then digits.
    [z_digits] emits only decimal digits ([all_dec_z_digits]); its first char is one ([z_digits_head]), so
    a positive number is digit-led and a negative is '-'-led.  Hence [is_dec (print_Z z) = true] for EVERY
    [z] — the witness that [AIntLit z]'s printed text is a well-formed atom (via [is_dec_atom_ok]). *)
Lemma is_dec_char_dec_digit : forall k, (k < 10)%nat -> is_dec_char (dec_digit k) = true.
Proof.
  intros k Hk. unfold is_dec_char, dec_digit. rewrite Ascii.nat_ascii_embedding by lia.
  apply andb_true_iff. split; apply Nat.leb_le; lia.
Qed.
Lemma all_dec_z_digits : forall fuel z acc, all_dec acc = true -> all_dec (z_digits fuel z acc) = true.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hacc; cbn [z_digits]; [ exact Hacc | ].
  pose proof (Z.mod_pos_bound z 10 ltac:(lia)) as Hmod.
  assert (Hk : (Z.to_nat (z mod 10) < 10)%nat) by lia.
  destruct (z / 10 =? 0)%Z eqn:E.
  - cbn [all_dec]. apply andb_true_iff. split; [ apply is_dec_char_dec_digit; exact Hk | exact Hacc ].
  - apply IH. cbn [all_dec]. apply andb_true_iff. split; [ apply is_dec_char_dec_digit; exact Hk | exact Hacc ].
Qed.
Lemma is_dec_String_dec_digit : forall k r, (k < 10)%nat -> all_dec r = true -> is_dec (String (dec_digit k) r) = true.
Proof.
  intros k r Hk Hr. unfold is_dec. rewrite (dec_digit_ne_minus k Hk).
  change (andb (is_dec_char (dec_digit k)) (all_dec r) = true).
  apply andb_true_iff. split; [ apply is_dec_char_dec_digit; exact Hk | exact Hr ].
Qed.
Lemma is_dec_String_minus : forall k r, (k < 10)%nat -> all_dec r = true ->
  is_dec (String (ascii_of_nat 45) (String (dec_digit k) r)) = true.
Proof.
  intros k r Hk Hr. unfold is_dec. rewrite Ascii.eqb_refl.
  change (all_dec (String (dec_digit k) r) = true).
  cbn [all_dec]. apply andb_true_iff. split; [ apply is_dec_char_dec_digit; exact Hk | exact Hr ].
Qed.
Lemma is_dec_print_Z : forall z, is_dec (print_Z z) = true.
Proof.
  intro z. unfold print_Z. destruct (z =? 0)%Z eqn:E0; [ reflexivity | ].
  destruct (z <? 0)%Z eqn:Eneg.
  - destruct (z_digits_head (digit_fuel (- z)) (- z) ""%string ltac:(unfold digit_fuel; lia))
      as [ k [ r [ Hk Hz ] ] ].
    rewrite Hz. change (is_dec (String (ascii_of_nat 45) (String (dec_digit k) r)) = true).
    apply is_dec_String_minus; [ exact Hk | ].
    pose proof (all_dec_z_digits (digit_fuel (- z)) (- z) ""%string eq_refl) as HD.
    rewrite Hz in HD. cbn [all_dec] in HD. apply andb_true_iff in HD. apply HD.
  - destruct (z_digits_head (digit_fuel z) z ""%string ltac:(unfold digit_fuel; lia))
      as [ k [ r [ Hk Hz ] ] ].
    rewrite Hz. apply is_dec_String_dec_digit; [ exact Hk | ].
    pose proof (all_dec_z_digits (digit_fuel z) z ""%string eq_refl) as HD.
    rewrite Hz in HD. cbn [all_dec] in HD. apply andb_true_iff in HD. apply HD.
Qed.

(** A STRING-LITERAL atom: just a CANONICAL [is_strlit] (a printed [print_string_lit]).  Review #5 item 1:
    it NEEDS NO [atom_ok] — a string literal is parsed by its OWN primary ([parse_strlit_prim], in quote /
    escape mode), NOT scanned as generic Go source — so a valid Go string whose CONTENTS would confuse the
    atom scanner (a space-then-operator like "a + b", or an unmatched bracket like "[") is still
    representable.  Quote-led, so DISJOINT from [go_ident] (identifier-led) and [is_dec] (digit/'-'-led)
    — the round-trip DISAMBIGUATES it from [AIdent] / [AIntLit]. *)
Definition strlit_ok (s : string) : bool := is_strlit s.
Lemma strlit_ok_is_strlit : forall s, strlit_ok s = true -> is_strlit s = true.
Proof. intros s H. exact H. Qed.
Lemma strlit_ok_not_go_ident : forall s, strlit_ok s = true -> go_ident s = false.
Proof. intros s H. destruct (is_strlit_cons s H) as [ rest -> ]. reflexivity. Qed.
Lemma strlit_ok_not_is_dec : forall s, strlit_ok s = true -> is_dec s = false.
Proof. intros s H. destruct (is_strlit_cons s H) as [ rest -> ]. reflexivity. Qed.

(** [raw_ok s] / [ARaw] — ⚠️ NOT a "simple Go atom".  BRUTALLY HONEST MEANING (external review #5 item 3):
    [ARaw] is an OPAQUE-TIGHT-EXPRESSION escape hatch — a checked string the plugin promises represents a
    Go expression that BINDS TIGHTER THAN ALL BINARY OPERATORS (so [print_expr] may treat it as a primary
    for precedence).  It is a TRANSITION strategy, NOT a faithful grammar node: a function-literal call or
    a cast is a COMPLEX expression we are choosing to render opaquely, not a real atom.  The name [ARaw] is
    deliberately treated as suspect — KEEP MOVING CASES OUT of it (selector / call / index / conversion /
    composite-literal / func-literal-call), and KEEP TIGHTENING [raw_ok] so it cannot smuggle in grammar
    nonsense.  [raw_ok s] = [atom_ok] AND none of the structured forms ([go_ident] / [is_dec] / [is_strlit])
    AND not a Go KEYWORD ([go_keyword] — review #5 item 2: [return]/[func]/[type] are not [go_ident] but
    the simple scanner would otherwise pass them) AND not [unary_op_led] / [is_selector_shaped] / a
    depth-0 break ([has_d0_break]).  review #7 — the unspaced-[a+b] hole is CLOSED: [atom_ok]'s [op_match]
    only sees SPACED operators, but [has_d0_break] now rejects ANY depth-0 binary-operator char (the
    hex-float exponent sign excepted, exactly), so [raw_ok "a+b" = false] is machine-checked — no longer
    a documented smell.  The split lets the round-trip DISAMBIGUATE uniquely.  The
    string-literal exclusion is by [quote_led] (ANY dquote-led string), not [is_strlit]: a dquote-led
    string is the string-literal PRIMARY's domain (canonical -> [AStringLit], non-canonical -> rejected),
    so [ARaw] must never be dquote-led — else [parse_primary] would intercept it as a literal. *)
Definition quote_led (s : string) : bool := match s with String c _ => Ascii.eqb c (ch 34) | _ => false end.
(** [go_ident] / [all_idc] / [dot_free] bridges for the SELECTOR layer: a [go_ident] field is all
    identifier-chars (hence [atom_ok_app_dotid] applies) and DOT-FREE (hence [split_last_dot_snoc] re-splits
    a printed selector at exactly its outermost '.'). *)
Lemma go_ident_all_idc : forall s, go_ident s = true -> all_idc s = true.
Proof.
  intros s H. unfold go_ident in H. destruct s as [ | c s' ]; [ discriminate | ].
  apply andb_true_iff in H. destruct H as [ H _ ]. apply andb_true_iff in H. destruct H as [ _ Ha ]. exact Ha.
Qed.
Lemma all_idc_dot_free : forall s, all_idc s = true -> dot_free s = true.
Proof.
  induction s as [ | c s' IH ]; intro H; [ reflexivity | ].
  cbn [all_idc] in H. apply andb_true_iff in H. destruct H as [ Hc Hs ].
  cbn [dot_free]. rewrite (IH Hs), andb_true_r. apply negb_true_iff.
  apply (is_idc_eqb_false c 46 Hc). reflexivity.
Qed.
(** [is_selector_shaped s] — [s] ends in ["." ++ <identifier>] (its last '.' is followed by a [go_ident]).
    [build_satom] reads such a string as an [SSelector]; so [raw_ok] EXCLUDES it (a raw atom is never
    selector-shaped) — making the raw vs selector split UNIQUE, which the round-trip needs.  Defined from
    [split_last_dot] + [go_ident] only (NOT [build_satom]) — so there is no circular definition. *)
Definition is_selector_shaped (s : string) : bool :=
  match split_last_dot s with Some (_, fld) => go_ident fld | None => false end.
(** [unary_op_led s] — [s] starts with an unspaced unary-operator prefix ([!]/[^]/[*]/[&], or [-] NOT
    followed by a digit) — EXACTLY [parse_primary]'s unary-dispatch condition (review #6 [EUnary]).
    [raw_ok] excludes it: a string [parse_primary] reads as an [EUnary] must NOT also be a representable
    [SRaw] (else the round-trip is not unique — [build_satom_str (SRaw "*p")] would fail).  [-]+digit is a
    negative LITERAL ([SIntLit]), not unary, so it is NOT excluded. *)
Definition unary_op_led (s : string) : bool :=
  match s with String c _ => is_unop_char c | _ => false end.
(** RAW HARDENING (review #6 item 1; review #7 — the unspaced-binop hole CLOSED) — the bracket+quote
    scanner alone is too permissive for atom shapes.  [has_d0_break s]: a depth-0 char that BREAKS the
    string into more than one token — a separator ',' (ch 44) / ';' (ch 59), OR a binary-OPERATOR char
    ([is_op_char]: + - * / % < > & ^ | = !) — tracked quote/bracket-aware like [split_idx_aux].  These
    NEVER occur at depth 0 in a single PRIMARY atom (commas/operators live INSIDE brackets; a depth-0
    operator means a binary expression).  This is what makes the unspaced [a+b] FAIL [raw_ok] (review #7:
    a known-accepted invalid shape is a bug, not an allowance) — the [-5] negative literal is NOT affected
    (it is [SIntLit] via [is_dec], built BEFORE [raw_ok]); a depth-0 leading unary [!]/[^]/[*]/[&] is
    separately rejected by [unary_op_led] (it is an [EUnary], not an atom).  [leading_is_keyword s]: the
    leading identifier RUN is a Go keyword — so [return()] / [if()] (keyword-LED, not whole-keyword) are
    rejected, which the whole-string [go_keyword] check misses. *)
(** A HEX-led atom ([0x]/[0X]…) — the only context where a depth-0 '+'/'-' can be a (hex-float) EXPONENT
    sign rather than a binary operator.  Go hex-float literals are [0x<mantissa>p<sign><exp>]; the [p]/[P]
    immediately precedes the exponent sign.  (Decimal floats would use [e]/[E], but the plugin emits floats
    as HEX via [print_float_hex], so only the hex case occurs — checked against the golden.) *)
Definition is_hex_led (s : string) : bool :=
  match s with
  | String c0 (String c1 _) =>
      andb (Ascii.eqb c0 (ch 48)) (orb (Ascii.eqb c1 (ch 120)) (Ascii.eqb c1 (ch 88)))
  | _ => false
  end.
(** [prevp] = the previous depth-0 char was [p]/[P] (a hex-float exponent marker).  A '+'/'-' right after
    it, in a [hexf] atom, is the exponent SIGN (part of the literal) — NOT a break.  Every OTHER depth-0
    operator char, and any other '+'/'-', breaks the atom (it is a binary expression, not a primary). *)
Fixpoint d0_break_aux (hexf prevp instr esc : bool) (d : nat) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      let '(instr', esc', d', found) :=
        if esc then (instr, false, d, false)
        else if instr then
          (if Ascii.eqb c (ch 92) then (true, true, d, false)
           else if Ascii.eqb c (ch 34) then (false, false, d, false)
           else (true, false, d, false))
        else
          (if Ascii.eqb c (ch 34) then (true, false, d, false)
           else if is_bopen c then (false, false, S d, false)
           else if is_bclose c then (false, false, Nat.pred d, false)
           else (false, false, d,
                 andb (Nat.eqb d 0)
                   (orb (orb (Ascii.eqb c (ch 44)) (Ascii.eqb c (ch 59)))
                        (andb (is_op_char c)
                              (negb (andb (andb hexf prevp)
                                          (orb (Ascii.eqb c (ch 43)) (Ascii.eqb c (ch 45)))))))))
      in
      let prevp' := andb (negb instr) (orb (Ascii.eqb c (ch 112)) (Ascii.eqb c (ch 80))) in
      if found then true else d0_break_aux hexf prevp' instr' esc' d' s'
  end.
Definition has_d0_break (s : string) : bool := d0_break_aux (is_hex_led s) false false false 0 s.
Fixpoint leading_ident (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if is_idc c then String c (leading_ident s') else EmptyString
  end.
(** Keywords that legitimately LEAD an operand atom (a func-literal / composite-literal type / channel
    type) are EXCLUDED from the rejection — so [func(x int64) int64 {...}(0)] and [map[K]V{...}] are kept
    while [return()] / [if()] / [for()] are rejected.  Distinguishing a valid [func]-lit from [func()]
    nonsense needs the parser, so the operand-leading keywords are conservatively ALLOWED here (the plugin
    only emits well-formed ones; they are caught downstream if malformed). *)
Definition operand_lead_kw (s : string) : bool :=
  existsb (String.eqb s) ["func"; "map"; "chan"; "struct"; "interface"].
Definition leading_is_keyword (s : string) : bool :=
  andb (go_keyword (leading_ident s)) (negb (operand_lead_kw (leading_ident s))).
Definition raw_ok (s : string) : bool :=
  andb (andb (andb (andb (andb (andb (atom_ok s) (negb (go_ident s))) (negb (is_dec s)))
                   (negb (quote_led s))) (negb (go_keyword s))) (negb (is_selector_shaped s)))
       (andb (andb (negb (has_d0_break s)) (negb (leading_is_keyword s))) (negb (unary_op_led s))).
Lemma raw_ok_atom_ok : forall s, raw_ok s = true -> atom_ok s = true.
Proof.
  intros s H. unfold raw_ok in H.
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ Ha _ ]. exact Ha.
Qed.
Lemma raw_ok_not_ident : forall s, raw_ok s = true -> go_ident s = false.
Proof.
  intros s H. unfold raw_ok in H.
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_dec : forall s, raw_ok s = true -> is_dec s = false.
Proof.
  intros s H. unfold raw_ok in H.
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_quote_led : forall s, raw_ok s = true -> quote_led s = false.
Proof.
  intros s H. unfold raw_ok in H.
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_keyword : forall s, raw_ok s = true -> go_keyword s = false.
Proof.
  intros s H. unfold raw_ok in H.
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_selector : forall s, raw_ok s = true -> is_selector_shaped s = false.
Proof.
  intros s H. unfold raw_ok in H.
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_unary : forall s, raw_ok s = true -> unary_op_led s = false.
Proof.
  intros s H. unfold raw_ok in H.
  apply andb_true_iff in H. destruct H as [ _ H ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
(** DESIRED-FAILURE regressions (review #6 item 1): the hardened [raw_ok] makes these non-atom shapes
    UNREPRESENTABLE as [SRaw] — each [Fail] asserts the proof-carrying construction does NOT type-check
    (depth-0 comma/semicolon, statement-keyword-led).  A [func]-literal-call ([func]-led but valid) is NOT
    rejected — see [raw_ok_funclit_call_kept]. *)
Fail Definition raw_d0_comma  : { s : string | raw_ok s = true } := exist _ "a,b" eq_refl.
Fail Definition raw_d0_semi   : { s : string | raw_ok s = true } := exist _ "a;b" eq_refl.
Fail Definition raw_kw_return : { s : string | raw_ok s = true } := exist _ "return()" eq_refl.
Fail Definition raw_kw_if     : { s : string | raw_ok s = true } := exist _ "if(x)" eq_refl.
Example raw_d0_comma_rejected  : raw_ok "a,b"      = false. Proof. reflexivity. Qed.
Example raw_d0_semi_rejected   : raw_ok "a;b"      = false. Proof. reflexivity. Qed.
Example raw_kw_return_rejected : raw_ok "return()" = false. Proof. reflexivity. Qed.
Example raw_ok_funclit_call_kept :
  raw_ok "func(x int64, y int64) int64 { return x - y }(0, 7)" = true. Proof. reflexivity. Qed.
(** review #7 — the unspaced-binop hole is CLOSED: a depth-0 operator char makes [raw_ok] FALSE, so an
    unspaced binary [a+b] is REJECTED as an atom (it is not a primary).  The [-5] negative literal is
    unaffected (built as [SIntLit] before [raw_ok]); [*p]/[&x]/[!b] are [EUnary], rejected by
    [unary_op_led].  These were the cases the old "known allowance" hand-waved — now machine-checked dead. *)
Example raw_unspaced_binop_rejected : raw_ok "a+b" = false. Proof. reflexivity. Qed.
Example raw_unspaced_mul_rejected   : raw_ok "a*b" = false. Proof. reflexivity. Qed.
Example raw_unspaced_or_rejected    : raw_ok "x|y" = false. Proof. reflexivity. Qed.
Example raw_unspaced_sub_rejected   : raw_ok "a-b" = false. Proof. reflexivity. Qed.
Example raw_neg_dec_still_intlit    : is_dec "-5" = true.   Proof. reflexivity. Qed.
(* the hex-float EXPONENT sign [p-51] is part of the literal, NOT a binary op — still a valid raw atom *)
Example raw_hex_float_exp_kept      : raw_ok "0x14000000000000p-51" = true. Proof. reflexivity. Qed.
Example raw_hex_float_pos_exp_kept  : raw_ok "0x18000000000000p+3"  = true. Proof. reflexivity. Qed.
(* but a hex-INT followed by a binary '-' ([0x1E-5] = [0x1E - 5]) is NOT exempt (E is a hex digit, not p) *)
Example raw_hexint_minus_rejected   : raw_ok "0x1E-5" = false. Proof. reflexivity. Qed.

(** A structured Go ATOM.  Validity is carried IN THE TYPE (malformed atom text UNREPRESENTABLE), and a
    SELECTOR is RECURSIVE ([x.f.g] = nested [SSelector]).  Two layers, because a selector's operand must be
    structurally a SCANNED atom (never a string literal — ["s".f] would not round-trip), and a constraint
    like [{a | atom_scanned a}] is CIRCULAR (the operand type would mention a function OF the atom type):
      - [SAtom] — the SCANNED atoms, whose text is always [atom_ok]: an IDENTIFIER ([SIdent]), a DECIMAL
        INTEGER LITERAL ([SIntLit], carrying the [Z]; its text is the canonical [print_Z], no proof needed),
        a "raw" atom ([SRaw] — the QUARANTINED escape hatch: [atom_ok], not [go_ident]/[is_dec]/selector-
        shaped, e.g. a call / cast / composite literal), or a SELECTOR ([SSelector operand field], plain
        recursion — the operand is itself an [SAtom], so it is STRUCTURALLY never a string literal).
      - [GoAtom] — a scanned atom ([AScanned]) or a STRING LITERAL ([AStringLit] — a [strlit_ok] atom,
        recovered by its own quote-aware primary, NOT by the generic scanner).
    Both extract to bare strings / [Z] / nested constructors (proofs erased); [atom_str] is the text. *)
(** [SAtom]/[GoAtom]/[GoExpr] are ONE MUTUAL block — atoms can contain expressions (a future [SIndex]
    [a[i]] / [SCall] [f(args)] carries [GoExpr] children) and expressions contain atoms ([EAtom]), so the
    three families are mutually recursive.  TODAY no atom constructor references [GoExpr] yet (the cycle is
    latent), so the auto-generated per-type induction principles are exactly the non-mutual ones and every
    existing proof is unchanged; grouping them now is the structural prerequisite for the recursive
    expression-carrying atoms. *)
Inductive SAtom : Type :=
  | SIdent    : Ident -> SAtom
  | SIntLit   : Z -> SAtom
  | SRaw      : { s : string | raw_ok s = true } -> SAtom
  | SSelector : SAtom -> Ident -> SAtom
with GoAtom : Type :=
  | AScanned   : SAtom -> GoAtom
  | AStringLit : string -> GoAtom   (* the SEMANTIC string VALUE (review #7 item 4: AST-first, not the
                                       printed lexeme).  ANY value is printable, so no proof is needed —
                                       an invalid literal SOURCE is unrepresentable by construction. *)
with GoExpr : Type :=
  | EAtom  : GoAtom -> GoExpr
  | EBin   : BinOp -> GoExpr -> GoExpr -> GoExpr
  | EUnary : UnaryOp -> GoExpr -> GoExpr.
Fixpoint satom_str (a : SAtom) : string :=
  match a with
  | SIdent i      => proj1_sig i
  | SIntLit z     => print_Z z
  | SRaw r        => proj1_sig r
  | SSelector a f => (satom_str a ++ String (ch 46) (proj1_sig f))%string
  end.
Definition atom_str (a : GoAtom) : string :=
  match a with AScanned s => satom_str s | AStringLit v => print_string_lit v end.
(** [atom_scanned a] — the atom is recovered by the GENERIC atom scanner ([scan_atom] + [build_atom]):
    [AScanned], but not [AStringLit] (recovered by its own quote-aware primary).  Only a scanned atom's
    text is [atom_ok] (a string literal's text need not be — review #5 item 1). *)
Definition atom_scanned (a : GoAtom) : bool := match a with AStringLit _ => false | _ => true end.
(** [satom_ok] / [satom_not_quote_led] and their [GoAtom] wrappers [atom_str_atom_ok] /
    [atom_scanned_not_quote_led] are proved BELOW [atom_ok_app_dotid] (the [SSelector] case needs it).
    ([GoExpr] is defined ABOVE, in the mutual [SAtom]/[GoAtom]/[GoExpr] block.) *)

Fixpoint print_expr (ctx : nat) (e : GoExpr) : string :=
  match e with
  | EAtom a => atom_str a
  | EBin o l r =>
      let p := binop_prec o in
      let inner := (print_expr p l ++ binop_text o ++ print_expr (S p) r)%string in
      if Nat.ltb p ctx then ("(" ++ inner ++ ")")%string else inner
  | EUnary o e =>
      (* unary binds TIGHTER than every binop (prec 5 max), so [EUnary] is a PRIMARY — it never wraps for
         [ctx], and its operand prints at prec 6 so an [EBin] operand parenthesises ([-(a + b)]). *)
      (unop_text o ++ print_expr 6 e)%string
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
Lemma nneg_b_app : forall a b d, nneg_b d (a ++ b)%string = andb (nneg_b d a) (nneg_b (depth d a) b).
Proof.
  induction a as [ | c a' IH ]; intros b d; cbn [String.append nneg_b depth].
  - reflexivity.
  - rewrite IH, andb_assoc. reflexivity.
Qed.
(** [atom_ok] is preserved by appending a SELECTOR suffix ["." ++ <identifier chars>]: ATOMIC via
    [bstack_ok_app_dotid] (same first char, no new bracket / seam), and BALANCED since the suffix carries
    no parens ([depth]/[nneg] are unchanged by it).  The [atom_ok] foundation for [ASelector]. *)
Lemma atom_ok_app_dotid : forall base f, atom_ok base = true -> all_idc f = true ->
  atom_ok (base ++ String (ch 46) f)%string = true.
Proof.
  intros base f Hb Hf. pose proof (atom_ok_atomic _ Hb) as Hatm.
  unfold atom_ok in Hb. apply andb_true_iff in Hb. destruct Hb as [ _ Hbal ].
  unfold balanced_b in Hbal. apply andb_true_iff in Hbal. destruct Hbal as [ Hd0 Hn0 ].
  apply Z.eqb_eq in Hd0.
  assert (Hpv : pv (ch 46) = 0%Z) by reflexivity.
  unfold atom_ok. apply andb_true_iff. split.
  - destruct base as [ | c base' ]; [ cbn in Hatm; discriminate Hatm | ].
    cbn [String.append]. unfold atomic in Hatm |- *.
    apply andb_true_iff in Hatm. destruct Hatm as [ Hno Hbs ].
    apply andb_true_iff. split; [ exact Hno | ].
    change (String c (base' ++ String (ch 46) f)%string) with ((String c base') ++ String (ch 46) f)%string.
    apply bstack_ok_app_dotid; [ exact Hf | exact Hbs ].
  - unfold balanced_b. apply andb_true_iff. split.
    + rewrite depth_app, Hd0. cbn [depth]. rewrite Hpv, Z.add_0_r, (all_idc_depth f 0 Hf). reflexivity.
    + rewrite nneg_b_app, Hn0, andb_true_l, Hd0. cbn [nneg_b].
      rewrite Hpv, Z.add_0_r. apply (all_idc_nneg_b f 0 (Z.le_refl 0) Hf).
Qed.
(** Every SCANNED atom's text is [atom_ok] — by induction on [SAtom]; the [SSelector] case is exactly
    [atom_ok_app_dotid] (operand [atom_ok] by IH, field all-identifier-chars by [go_ident_all_idc]). *)
Lemma satom_ok : forall a : SAtom, atom_ok (satom_str a) = true.
Proof.
  induction a as [ i | z | r | a IH f ]; cbn [satom_str].
  - apply go_ident_atom_ok, (proj2_sig i).
  - apply is_dec_atom_ok, is_dec_print_Z.
  - apply raw_ok_atom_ok, (proj2_sig r).
  - apply atom_ok_app_dotid; [ exact IH | apply go_ident_all_idc, (proj2_sig f) ].
Qed.
Lemma atom_str_atom_ok : forall a, atom_scanned a = true -> atom_ok (atom_str a) = true.
Proof.
  intros [ s | r ] H; cbn [atom_str atom_scanned] in *; [ apply satom_ok | discriminate H ].
Qed.
(** A scanned atom is never dquote-led (so [parse_primary] sends it to [scan_atom], not the literal prim):
    an identifier is [is_idstart]-led, a decimal is digit/'-'-led, a raw atom is [not quote_led], and a
    SELECTOR begins with its operand (non-dquote by IH; its text is [atom_ok], hence nonempty). *)
Lemma satom_not_quote_led : forall a : SAtom, quote_led (satom_str a) = false.
Proof.
  induction a as [ i | z | r | a IH f ]; cbn [satom_str].
  - destruct i as [ s Hs ]; cbn [proj1_sig]. unfold go_ident in Hs.
    destruct s as [ | c s' ]; [ discriminate | ].
    apply andb_true_iff in Hs. destruct Hs as [ Hs _ ]. apply andb_true_iff in Hs. destruct Hs as [ Hstart _ ].
    unfold quote_led. apply (is_idc_eqb_false c 34); [ apply is_idstart_is_idc; exact Hstart | reflexivity ].
  - pose proof (is_dec_print_Z z) as Hd. unfold is_dec in Hd.
    destruct (print_Z z) as [ | c rest ] eqn:EP; [ discriminate Hd | ].
    unfold quote_led.
    destruct (Ascii.eqb c (ascii_of_nat 45)) eqn:Em.
    + apply Ascii.eqb_eq in Em. subst c. reflexivity.
    + apply andb_true_iff in Hd. destruct Hd as [ Hc _ ].
      apply (is_idc_eqb_false c 34); [ apply is_dec_char_is_idc; exact Hc | reflexivity ].
  - destruct r as [ s Hr ]; cbn [proj1_sig]. apply raw_ok_not_quote_led; exact Hr.
  - destruct (satom_str a) as [ | c rest ] eqn:Ea.
    + exfalso. pose proof (satom_ok a) as Hok. rewrite Ea in Hok. discriminate Hok.
    + cbn [String.append]. unfold quote_led in IH |- *. exact IH.
Qed.
Lemma atom_scanned_not_quote_led : forall a, atom_scanned a = true -> quote_led (atom_str a) = false.
Proof.
  intros [ s | r ] H; cbn [atom_str atom_scanned] in *; [ apply satom_not_quote_led | discriminate H ].
Qed.
(** A scanned atom is never [unary_op_led] (so [parse_primary] dispatches it past the unary branch to
    [scan_atom]): an identifier is [is_idstart]-led, a decimal is digit-or-'-'-led (the '-' is a negative
    LITERAL — its second char is a digit, so the unary condition is false), a raw atom is [raw_ok] (which
    EXCLUDES [unary_op_led]), and a selector begins with its operand (non-unary by IH, second char
    invariant under the appended ".f"). *)
Lemma satom_unary_op_led_false : forall a : SAtom, unary_op_led (satom_str a) = false.
Proof.
  induction a as [ i | z | r | a IH f ]; cbn [satom_str].
  - destruct i as [ s Hs ]; cbn [proj1_sig]. unfold go_ident in Hs.
    destruct s as [ | c s' ]; [ discriminate | ].
    apply andb_true_iff in Hs. destruct Hs as [ Hs _ ]. apply andb_true_iff in Hs. destruct Hs as [ Hstart _ ].
    cbn [unary_op_led]. apply (is_idc_not_unop c (is_idstart_is_idc c Hstart)).
  - pose proof (is_dec_print_Z z) as Hd. unfold is_dec in Hd.
    destruct (print_Z z) as [ | c rest ] eqn:EP; [ discriminate Hd | ].
    cbn [unary_op_led]. destruct (Ascii.eqb c (ascii_of_nat 45)) eqn:Em.
    + apply Ascii.eqb_eq in Em. subst c. reflexivity.
    + apply andb_true_iff in Hd. destruct Hd as [ Hcd _ ].
      apply (is_idc_not_unop c (is_dec_char_is_idc c Hcd)).
  - destruct r as [ s Hr ]; cbn [proj1_sig]. apply raw_ok_not_unary; exact Hr.
  - destruct (satom_str a) as [ | c rest ] eqn:Ea.
    + exfalso. pose proof (satom_ok a) as Hok. rewrite Ea in Hok. discriminate Hok.
    + cbn [String.append]. cbn [unary_op_led] in IH |- *. exact IH.
Qed.
Lemma atom_scanned_unary_op_led_false : forall a, atom_scanned a = true -> unary_op_led (atom_str a) = false.
Proof.
  intros [ s | r ] H; cbn [atom_str atom_scanned] in *; [ apply satom_unary_op_led_false | discriminate H ].
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
  | EAtom (AStringLit _) => True   (* a string literal is parsed by its own primary, not by paren-balance *)
  | EAtom a => balanced (atom_str a)
  | EBin _ l r => wf l /\ wf r
  | EUnary _ e => wf e
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

(** RETIRED (external review #5 item 1): the old [print_expr_balanced] proved [print_expr ctx e] is
    bracket-[balanced] (raw paren-[depth] returns to 0).  Once a string literal ([AStringLit]) may carry
    ARBITRARY bracket content (a lone open paren, a lone open bracket), raw bracket balance NO LONGER holds
    verbatim — the paren INSIDE the quotes counts in [depth] though it is not a real paren.  This is NOT a
    regression: the round-trip below ([print_parse_expr]) is STRICTLY STRONGER — it proves the parser
    re-reads [print_expr e] back to EXACTLY [e] (so the brackets the parser actually pairs are correct),
    AND it covers [AStringLit] via the quote-aware [parse_strlit_prim].  So bracket-balance is subsumed by
    the stronger, string-literal-correct round-trip, and [print_expr_depth_nneg] / [print_expr_balanced]
    are removed in its favour (a weaker proxy that cannot hold for arbitrary string content). *)

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
    if Ascii.eqb c (ch 34) then (let (a, rest) := scan_skip d s' in (String c a, rest))
    else if andb (Nat.eqb d 0) (orb (opens (String c s')) (is_close c))
    then (EmptyString, String c s')
    else let (a, rest) := scan_atom (if is_bopen c then S d else if is_bclose c then Nat.pred d else d) s'
         in (String c a, rest).
Proof.
  intros d c s'. destruct (Ascii.eqb c (ch 34)) eqn:Eq.
  - apply Ascii.eqb_eq in Eq. subst c. apply scan_atom_quote.
  - cbn [scan_atom]. rewrite Eq. reflexivity.
Qed.
Lemma atomic_from_cons : forall d c s',
  atomic_from d (String c s') =
    if Ascii.eqb c (ch 34) then atomic_skip d s'
    else if andb (Nat.eqb d 0) (orb (orb (opens (String c s')) (is_bclose c)) (andb (is_space c) (op_after s')))
    then false
    else atomic_from (if is_bopen c then S d else if is_bclose c then Nat.pred d else d) s'.
Proof.
  intros d c s'. destruct (Ascii.eqb c (ch 34)) eqn:Eq.
  - apply Ascii.eqb_eq in Eq. subst c. apply atomic_from_quote.
  - cbn [atomic_from]. rewrite Eq. reflexivity.
Qed.

(** BRIDGE — the strict bracket STACK implies the loose combined-depth COUNT (matched brackets are
    balanced), the count being the stack's LENGTH.  This lets [atomic] (now stack-validated) still feed
    [scan_atom_correct] (stated over the count [atomic_from]) — the scan works unchanged while [atom_ok]
    now rejects mismatched brackets. *)
(** Combined with the skip state, by STRONG induction on length (the backslash case consumes two chars). *)
Lemma bstack_atomic_from : forall n s st, String.length s <= n ->
  (bstack_ok st s = true -> atomic_from (length st) s = true) /\
  (bstack_skip st s = true -> atomic_skip (length st) s = true).
Proof.
  intros n. induction n as [ | n IH ]; intros s st Hlen.
  - destruct s as [ | c s' ]; [ | cbn [String.length] in Hlen; lia ].
    split; [ intro H | intro H; cbn [bstack_skip] in H; discriminate H ].
    cbn [bstack_ok] in H. destruct st as [ | top st' ]; [ reflexivity | discriminate H ].
  - destruct s as [ | c s' ].
    + split; [ intro H | intro H; cbn [bstack_skip] in H; discriminate H ].
      cbn [bstack_ok] in H. destruct st as [ | top st' ]; [ reflexivity | discriminate H ].
    + cbn [String.length] in Hlen. assert (Hl' : String.length s' <= n) by lia. split.
      * intro H. destruct (Ascii.eqb c (ch 34)) eqn:Eq.
        -- apply Ascii.eqb_eq in Eq. subst c. rewrite bstack_ok_quote in H. rewrite atomic_from_quote.
           apply (proj2 (IH s' st Hl')); exact H.
        -- rewrite bstack_ok_cons in H. rewrite Eq in H. rewrite atomic_from_cons. rewrite Eq.
           destruct st as [ | top st' ].
           ++ cbn [andb] in H.
              destruct (orb (opens (String c s')) (andb (is_space c) (op_after s'))) eqn:Eos; [ discriminate H | ].
              apply orb_false_iff in Eos. destruct Eos as [ Hop Hsp ]. cbn [length].
              destruct (is_bopen c) eqn:Ebo.
              ** rewrite Hop, (bopen_not_bclose c Ebo), Hsp. cbn [orb andb Nat.eqb].
                 change (S 0) with (length (cons (close_of c) nil)). apply (proj1 (IH s' _ Hl')); exact H.
              ** destruct (is_bclose c) eqn:Ebc; [ discriminate H | ].
                 rewrite Hop, Hsp. cbn [orb andb Nat.eqb].
                 change 0 with (length (@nil ascii)). apply (proj1 (IH s' _ Hl')); exact H.
           ++ cbn [andb] in H. cbn [length].
              assert (Hne : Nat.eqb (S (length st')) 0 = false) by reflexivity. rewrite Hne. cbn [andb].
              destruct (is_bopen c) eqn:Ebo.
              ** change (S (S (length st'))) with (length (cons (close_of c) (cons top st'))).
                 apply (proj1 (IH s' _ Hl')); exact H.
              ** destruct (is_bclose c) eqn:Ebc.
                 --- destruct (Ascii.eqb c top) eqn:Em; [ | discriminate H ].
                     cbn [Nat.pred]. apply (proj1 (IH s' _ Hl')); exact H.
                 --- change (S (length st')) with (length (cons top st')). apply (proj1 (IH s' _ Hl')); exact H.
      * intro H. cbn [bstack_skip] in H. cbn [atomic_skip]. destruct (Ascii.eqb c (ch 34)) eqn:Eq1.
        -- apply (proj1 (IH s' st Hl')); exact H.
        -- destruct (Ascii.eqb c (ch 92)) eqn:Eq2.
           ++ destruct s' as [ | d s'' ]; [ discriminate H | ].
              assert (Hl'' : String.length s'' <= n) by (cbn [String.length] in Hl'; lia).
              apply (proj2 (IH s'' st Hl'')); exact H.
           ++ apply (proj2 (IH s' st Hl')); exact H.
Qed.
Lemma bstack_ok_atomic_from : forall s st, bstack_ok st s = true -> atomic_from (length st) s = true.
Proof. intros s st H. exact (proj1 (bstack_atomic_from (String.length s) s st (le_n _)) H). Qed.

(** A [rest] at which [scan_atom] stops cleanly: empty, or its head is ")" or begins an operator. *)
Definition good_seam (rest : string) : bool :=
  match rest with EmptyString => true | String c _ => orb (opens rest) (is_close c) end.
(** A seam char is never a dquote: an operator is space-led ([opens] needs [op_match], which fails on a
    non-space head) and ')' is not a dquote.  So the QUOTE-AWARE [scan_atom] does NOT mistake a [good_seam]
    remainder for a nested string literal. *)
Lemma good_seam_not_quote : forall c rs, good_seam (String c rs) = true -> Ascii.eqb c (ch 34) = false.
Proof.
  intros c rs H. destruct (Ascii.eqb c (ch 34)) eqn:Eq; [ | reflexivity ].
  apply Ascii.eqb_eq in Eq. subst c. exfalso. unfold good_seam in H. unfold opens in H.
  rewrite (op_match_not_space (ch 34) rs eq_refl) in H. cbn in H. discriminate H.
Qed.

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
(** Combined with the in-string reconstruction [scan_skip], by STRONG induction on length (backslash
    consumes two chars).  The [atomic_from]/[scan_atom] conjunct is the ORIGINAL seam proof (the quote
    branch dispatched to [scan_skip] via [scan_atom_quote]); the [atomic_skip]/[scan_skip] conjunct
    reconstructs the literal char-by-char, bridging back at the close quote. *)
Lemma scan_atom_gen_skip : forall n a d rest, String.length a <= n -> good_seam rest = true ->
  (atomic_from d a = true -> scan_atom d (a ++ rest) = (a, rest)) /\
  (atomic_skip d a = true -> scan_skip d (a ++ rest) = (a, rest)).
Proof.
  intros n. induction n as [ | n IH ]; intros a d rest Hlen Hseam.
  - destruct a as [ | c a' ]; [ | cbn [String.length] in Hlen; lia ].
    split; [ | intro Hat; cbn [atomic_skip] in Hat; discriminate Hat ].
    intro Hat. cbn [atomic_from] in Hat. apply Nat.eqb_eq in Hat; subst d. cbn [append].
    destruct rest as [ | rc rs ]; [ reflexivity | ].
    rewrite scan_atom_cons, (good_seam_not_quote rc rs Hseam).
    unfold good_seam in Hseam. rewrite Hseam. reflexivity.
  - destruct a as [ | c a' ].
    + split; [ | intro Hat; cbn [atomic_skip] in Hat; discriminate Hat ].
      intro Hat. cbn [atomic_from] in Hat. apply Nat.eqb_eq in Hat; subst d. cbn [append].
      destruct rest as [ | rc rs ]; [ reflexivity | ].
      rewrite scan_atom_cons, (good_seam_not_quote rc rs Hseam).
      unfold good_seam in Hseam. rewrite Hseam. reflexivity.
    + cbn [String.length] in Hlen. assert (Hl' : String.length a' <= n) by lia. split.
      * intro Hat. cbn [append]. destruct (Ascii.eqb c (ch 34)) eqn:Eq.
        -- apply Ascii.eqb_eq in Eq. subst c. rewrite atomic_from_quote in Hat. rewrite scan_atom_quote.
           rewrite (proj2 (IH a' d rest Hl' Hseam) Hat). reflexivity.
        -- rewrite atomic_from_cons in Hat. rewrite Eq in Hat. rewrite scan_atom_cons. rewrite Eq.
           destruct (andb (Nat.eqb d 0)
                      (orb (orb (opens (String c a')) (is_bclose c)) (andb (is_space c) (op_after a')))) eqn:Estop;
             [ discriminate Hat | ].
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
           rewrite (proj1 (IH a' (if is_bopen c then S d else if is_bclose c then Nat.pred d else d)
                             rest Hl' Hseam) Hat). reflexivity.
      * intro Hat. cbn [append]. cbn [scan_skip]. cbn [atomic_skip] in Hat.
        destruct (Ascii.eqb c (ch 34)) eqn:Eq1.
        -- rewrite (proj1 (IH a' d rest Hl' Hseam) Hat). reflexivity.
        -- destruct (Ascii.eqb c (ch 92)) eqn:Eq2.
           ++ destruct a' as [ | f a'' ]; [ discriminate Hat | ].
              cbn [append]. assert (Hl'' : String.length a'' <= n) by (cbn [String.length] in Hl'; lia).
              rewrite (proj2 (IH a'' d rest Hl'' Hseam) Hat). reflexivity.
           ++ rewrite (proj2 (IH a' d rest Hl' Hseam) Hat). reflexivity.
Qed.
Lemma scan_atom_gen : forall a d rest, atomic_from d a = true -> good_seam rest = true ->
  scan_atom d (a ++ rest) = (a, rest).
Proof.
  intros a d rest Hat Hseam.
  exact (proj1 (scan_atom_gen_skip (String.length a) a d rest (le_n _) Hseam) Hat).
Qed.

Lemma scan_atom_correct : forall a rest, atomic a = true -> good_seam rest = true ->
  scan_atom 0 (a ++ rest) = (a, rest).
Proof.
  intros a rest Hat Hseam. unfold atomic in Hat.
  destruct a as [ | c a' ]; [ discriminate | ].
  apply andb_true_iff in Hat. destruct Hat as [_ Hstk].
  apply scan_atom_gen; [ exact (bstack_ok_atomic_from _ nil Hstk) | exact Hseam ].
Qed.

(** ============================================================================
    POSTFIX PrimaryExpr grammar — the OPERAND scanner (review #7 item 2; validated in scratchpad
    scanbase2.v).  [scan_base s] splits an atom into [(operand, rest)]: [operand] is the leftmost Go
    Operand (an ident / number / opaque func-lit / composite literal) and [rest] is the trailing postfix
    ops ([.f] / [\[e\]] / [(args)]) + remainder.  The KEY corrections over a naive maximal-ident scan:
    (1) read until a DEPTH-0 POSTFIX char ('.'/'['/'(' — [is_postfix_start]), NOT an ident boundary, so a
    hex float [0x..p-51] reads WHOLE (the '-' exponent is not a break); (2) QUOTE-AWARE (a string literal
    body is opaque, via [scan_strlit_body]) so a bracket inside a literal does not miscount depth;
    (3) a leading "func" is the one special case — its own [(params){body}] are part of the operand, so
    consume them ([scan_bal] the params, [scan_to_brace] the body) BEFORE [scan_rest].  ('{' is NOT a
    postfix start — it opens a composite literal whose [{...}] joins the operand.)  DORMANT until the
    parser is rewired; the faithful-split + round-trip lemmas + the [SIndex]/[SSlice]/[SCall] postfix
    constructors land in the following slices. *)
Definition is_postfix_start (c : ascii) : bool :=
  orb (orb (Ascii.eqb c (ch 46)) (Ascii.eqb c (ch 91))) (Ascii.eqb c (ch 40)).   (* . [ ( *)
(** [scan_bal f d s] consumes a BALANCED bracket span (already inside [d] open brackets), quote-aware;
    returns [(span-incl-the-close-returning-to-d-1, rest)]. *)
Fixpoint scan_bal (fuel d : nat) (s : string) : option (string * string) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => None
    | String c s' =>
        if Ascii.eqb c (ch 34) then
          match scan_strlit_body s' with
          | Some (body, rest) =>
              match scan_bal f d rest with
              | Some (a, r) => Some (String c (body ++ String (ch 34) a), r) | None => None end
          | None => None end
        else if is_bopen c then
          match scan_bal f (S d) s' with Some (a, r) => Some (String c a, r) | None => None end
        else if is_bclose c then
          (match d with
           | S O => Some (String c EmptyString, s')
           | S d' => match scan_bal f d' s' with Some (a, r) => Some (String c a, r) | None => None end
           | O => None end)
        else match scan_bal f d s' with Some (a, r) => Some (String c a, r) | None => None end
    end
  end.
(** [scan_to_brace f s] consumes up to and INCLUDING the next balanced "{...}" (the func-lit's return
    type + body span — everything from here to the matching close of the FIRST '{'). *)
Fixpoint scan_to_brace (fuel : nat) (s : string) : option (string * string) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => None
    | String c s' =>
        if Ascii.eqb c (ch 123) then
          match scan_bal f 1 s' with Some (a, r) => Some (String c a, r) | None => None end
        else match scan_to_brace f s' with Some (a, r) => Some (String c a, r) | None => None end
    end
  end.
(** [scan_rest f d s] reads operand bytes until a DEPTH-0 [is_postfix_start] char, quote-aware. *)
Fixpoint scan_rest (fuel d : nat) (s : string) : string * string :=
  match fuel with
  | O => (EmptyString, s)
  | S f =>
    match s with
    | EmptyString => (EmptyString, EmptyString)
    | String c s' =>
        if Ascii.eqb c (ch 34) then
          match scan_strlit_body s' with
          | Some (body, rest) =>
              let (a, r) := scan_rest f d rest in (String c (body ++ String (ch 34) a), r)
          | None => (EmptyString, s) end
        else if andb (Nat.eqb d 0) (is_postfix_start c) then (EmptyString, s)
        else if is_bopen c then let (a, r) := scan_rest f (S d) s' in (String c a, r)
        else if is_bclose c then
          (match d with S d' => let (a, r) := scan_rest f d' s' in (String c a, r) | O => (EmptyString, s) end)
        else let (a, r) := scan_rest f d s' in (String c a, r)
    end
  end.
(** [scan_base s] — the leading operand.  [leading_ident s = "func"] ⇒ a func-lit (consume its
    [(params){body}], then any trailing postfix is found by [scan_rest]); else [scan_rest] from depth 0. *)
Definition scan_base (s : string) : string * string :=
  if String.eqb (leading_ident s) "func" then
    match s with
    | String _ (String _ (String _ (String _ afterfunc))) =>
        match afterfunc with
        | String c r1 =>
            if Ascii.eqb c (ch 40) then
              match scan_bal (String.length afterfunc) 1 r1 with
              | Some (params, r2) =>
                  match scan_to_brace (String.length r2) r2 with
                  | Some (body, r3) =>
                      let funclit := ("func" ++ String (ch 40) params ++ body)%string in
                      let (more, rest) := scan_rest (String.length r3) 0 r3 in
                      ((funclit ++ more)%string, rest)
                  | None => scan_rest (String.length s) 0 s end
              | None => scan_rest (String.length s) 0 s end
            else scan_rest (String.length s) 0 s
        | EmptyString => ("func", EmptyString) end
    | _ => scan_rest (String.length s) 0 s end
  else scan_rest (String.length s) 0 s.
(** Sanity (computational): the operand splits validated in scanbase2.v hold over goprint's helpers too. *)
Example scan_base_sel  : scan_base ("foo" ++ String (ch 46) "bar") = ("foo", String (ch 46) "bar").
Proof. reflexivity. Qed.
Example scan_base_hexf : scan_base "0x14000000000000p-51" = ("0x14000000000000p-51", ""). Proof. reflexivity. Qed.

(** FAITHFUL SPLIT — every operand scanner loses no bytes: the consumed span ++ the returned rest
    reconstructs the input.  A necessary component of the round-trip (the operand recovered IS a prefix
    of the printed atom).  [scan_strlit_body] first (the quote case of the others reduces to it). *)
Lemma scan_strlit_body_split_n : forall n s body rest, String.length s <= n ->
  scan_strlit_body s = Some (body, rest) -> s = (body ++ String (ch 34) rest)%string.
Proof.
  induction n as [ | n IH ]; intros s body rest Hlen H.
  - destruct s; [ cbn in H; discriminate | cbn in Hlen; lia ].
  - destruct s as [ | c s' ]; cbn [scan_strlit_body] in H; [ discriminate | ].
    destruct (Ascii.eqb c (ch 34)) eqn:Eq.
    + apply Ascii.eqb_eq in Eq. subst c. injection H as <- <-. reflexivity.
    + destruct (Ascii.eqb c (ch 92)) eqn:Eb.
      * destruct s' as [ | c2 s'' ]; [ discriminate | ].
        destruct (scan_strlit_body s'') as [ [b r] | ] eqn:Er; [ | discriminate ].
        injection H as <- <-. cbn [append]. do 2 f_equal.
        apply (IH s'' b r); [ cbn [String.length] in Hlen; lia | exact Er ].
      * destruct (scan_strlit_body s') as [ [b r] | ] eqn:Er; [ | discriminate ].
        injection H as <- <-. cbn [append]. f_equal.
        apply (IH s' b r); [ cbn [String.length] in Hlen; lia | exact Er ].
Qed.
Lemma scan_strlit_body_split : forall s body rest,
  scan_strlit_body s = Some (body, rest) -> s = (body ++ String (ch 34) rest)%string.
Proof. intros s body rest H. exact (scan_strlit_body_split_n (String.length s) s body rest (le_n _) H). Qed.
Lemma scan_rest_split : forall f d s,
  (fst (scan_rest f d s) ++ snd (scan_rest f d s))%string = s.
Proof.
  induction f as [ | f IH ]; intros d s; [ destruct s; reflexivity | ].
  cbn [scan_rest]. destruct s as [ | c s' ]; [ reflexivity | ].
  destruct (Ascii.eqb c (ch 34)) eqn:Eq.
  - apply Ascii.eqb_eq in Eq. subst c. destruct (scan_strlit_body s') as [ [body rest] | ] eqn:Er.
    + pose proof (scan_strlit_body_split s' body rest Er) as Hs'.
      destruct (scan_rest f d rest) as [a r] eqn:Erest. cbn [fst snd].
      pose proof (IH d rest) as Hih. rewrite Erest in Hih. cbn [fst snd] in Hih.
      cbn [append]. f_equal. rewrite sapp_assoc. cbn [append]. rewrite Hih. symmetry; exact Hs'.
    + cbn [fst snd]. reflexivity.
  - destruct (andb (Nat.eqb d 0) (is_postfix_start c)) eqn:Ep; [ cbn [fst snd]; reflexivity | ].
    destruct (is_bopen c) eqn:Eo.
    + destruct (scan_rest f (S d) s') as [a r] eqn:Erest. cbn [fst snd].
      pose proof (IH (S d) s') as Hih. rewrite Erest in Hih. cbn [fst snd] in Hih.
      cbn [append]. f_equal. exact Hih.
    + destruct (is_bclose c) eqn:Ec.
      * destruct d as [ | d' ]; [ cbn [fst snd]; reflexivity | ].
        destruct (scan_rest f d' s') as [a r] eqn:Erest. cbn [fst snd].
        pose proof (IH d' s') as Hih. rewrite Erest in Hih. cbn [fst snd] in Hih.
        cbn [append]. f_equal. exact Hih.
      * destruct (scan_rest f d s') as [a r] eqn:Erest. cbn [fst snd].
        pose proof (IH d s') as Hih. rewrite Erest in Hih. cbn [fst snd] in Hih.
        cbn [append]. f_equal. exact Hih.
Qed.

(** ---- THE RECURSIVE ATOM PARSER ---- [build_satom] is [build_atom]'s engine: it DISAMBIGUATES an
    [atom_ok] string into the [SAtom] tree.  [go_ident] -> [SIdent]; [is_dec] -> [SIntLit] (its [Z] via
    [parse_Z]); else if the string is SELECTOR-SHAPED (last '.' followed by a [go_ident] field) peel that
    '.' and RECURSE on the operand -> [SSelector]; else any [raw_ok] string -> [SRaw]; else reject.  The
    selector arm precedes [raw_ok] and [raw_ok] EXCLUDES selector-shaped strings ([raw_ok_not_selector]),
    so each [atom_ok] string takes exactly one arm — the round-trip ([build_satom_str_fuel]) is then UNIQUE.
    Fuel bounds the selector recursion (each '.' strips >= 2 chars; [satom_len_depth] shows the string is
    long enough). *)
Fixpoint satom_depth (a : SAtom) : nat :=
  match a with SSelector a' _ => S (satom_depth a') | _ => 0 end.
Lemma slen_app : forall a b, String.length (a ++ b) = String.length a + String.length b.
Proof. induction a as [ | c a IH ]; intro b; cbn [String.append String.length];
       [ reflexivity | rewrite IH; reflexivity ]. Qed.
(** A string containing '.' is neither an identifier nor a decimal (their char-classes exclude '.'), so a
    selector string falls through the [go_ident]/[is_dec] arms to the selector arm. *)
Lemma all_idc_app_dot_false : forall x y, all_idc (x ++ String (ch 46) y) = false.
Proof.
  induction x as [ | c x' IH ]; intro y;
    [ reflexivity | cbn [String.append all_idc]; rewrite IH; apply andb_false_r ].
Qed.
Lemma all_dec_app_dot_false : forall x y, all_dec (x ++ String (ch 46) y) = false.
Proof.
  induction x as [ | c x' IH ]; intro y;
    [ reflexivity | cbn [String.append all_dec]; rewrite IH; apply andb_false_r ].
Qed.
Lemma go_ident_app_dot_false : forall x y, go_ident (x ++ String (ch 46) y) = false.
Proof.
  intros x y. destruct (go_ident (x ++ String (ch 46) y)) eqn:E; [ | reflexivity ].
  apply go_ident_all_idc in E. rewrite all_idc_app_dot_false in E. discriminate.
Qed.
Lemma is_dec_app_dot_false : forall x y, is_dec (x ++ String (ch 46) y) = false.
Proof.
  intros x y. destruct x as [ | c x' ]; [ reflexivity | ].
  cbn [String.append is_dec]. destruct (Ascii.eqb c (ascii_of_nat 45)) eqn:Ec.
  - pose proof (all_dec_app_dot_false x' y) as Hf.
    destruct (x' ++ String (ch 46) y) as [ | c2 r2 ] eqn:Erest; [ reflexivity | ].
    exact Hf.
  - rewrite (all_dec_app_dot_false x' y). apply andb_false_r.
Qed.
Lemma satom_len_depth : forall s, S (satom_depth s) <= String.length (satom_str s).
Proof.
  induction s as [ i | z | r | a IH fld ]; cbn [satom_depth satom_str].
  - destruct i as [ s Hs ]; cbn [proj1_sig].
    destruct s as [ | c s' ]; [ unfold go_ident in Hs; discriminate Hs | cbn [String.length]; lia ].
  - pose proof (is_dec_print_Z z) as Hd.
    destruct (print_Z z) as [ | c r ] eqn:EP; [ discriminate Hd | cbn [String.length]; lia ].
  - destruct r as [ s Hr ]; cbn [proj1_sig]. pose proof (raw_ok_atom_ok _ Hr) as Hok.
    destruct s as [ | c s' ]; [ discriminate Hok | cbn [String.length]; lia ].
  - rewrite slen_app; cbn [String.length]; lia.
Qed.
Fixpoint build_satom (fuel : nat) (a : string) : option SAtom :=
  match fuel with
  | O => None
  | S f =>
    match bool_dec (go_ident a) true with
    | left Hi => Some (SIdent (exist _ a Hi))
    | right _ =>
      match bool_dec (is_dec a) true with
      | left _ => Some (SIntLit (parse_Z a))
      | right _ =>
        match split_last_dot a with
        | Some (op, fld) =>
            match bool_dec (go_ident fld) true with
            | left Hf =>
                match build_satom f op with
                | Some sa => Some (SSelector sa (exist _ fld Hf))
                | None => None
                end
            | right _ =>
                match bool_dec (raw_ok a) true with
                | left Hr => Some (SRaw (exist _ a Hr)) | right _ => None end
            end
        | None =>
            match bool_dec (raw_ok a) true with
            | left Hr => Some (SRaw (exist _ a Hr)) | right _ => None end
        end
      end
    end
  end.
Definition build_atom (a : string) : option GoExpr :=
  match build_satom (String.length a) a with
  | Some sa => Some (EAtom (AScanned sa))
  | None => None
  end.
(** The atom ROUND-TRIP, with enough fuel: [build_satom] re-reads [satom_str s] to exactly [s].  By
    induction on [s] (the [<= f] form folds the recursion AND fuel-monotonicity into one statement): leaves
    are immediate ([go_ident]/[is_dec]/[raw_ok] + UIP-on-bool for the erased sig proof); the SELECTOR
    re-splits at its outermost '.' ([split_last_dot_snoc]; its field is [dot_free] via [go_ident_all_idc] +
    [all_idc_dot_free]) and recurses (the operand's fuel-bound [<= g] holds — its [satom_depth] is one less). *)
Lemma build_satom_str_fuel : forall s f, S (satom_depth s) <= f -> build_satom f (satom_str s) = Some s.
Proof.
  intros s. induction s as [ i | z | r | a IH fld ]; intros f Hf; cbn [satom_depth satom_str] in *.
  - destruct f as [ | g ]; [ lia | ]. destruct i as [ s Hs ]; cbn [proj1_sig].
    cbn [build_satom]. destruct (bool_dec (go_ident s) true) as [ Hd | Hd ]; [ | exfalso; apply Hd; exact Hs ].
    assert (E : Hd = Hs) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
  - destruct f as [ | g ]; [ lia | ]. cbn [build_satom].
    pose proof (is_dec_print_Z z) as Hdec. pose proof (is_dec_not_go_ident _ Hdec) as Hni.
    destruct (bool_dec (go_ident (print_Z z)) true) as [ Hd | Hd ]; [ exfalso; congruence | ].
    destruct (bool_dec (is_dec (print_Z z)) true) as [ Hd2 | Hd2 ]; [ | exfalso; apply Hd2; exact Hdec ].
    rewrite print_parse_Z. reflexivity.
  - destruct f as [ | g ]; [ lia | ]. destruct r as [ s Hr ]; cbn [proj1_sig]. cbn [build_satom].
    pose proof (raw_ok_not_ident _ Hr) as Hni. pose proof (raw_ok_not_dec _ Hr) as Hnd.
    pose proof (raw_ok_not_selector _ Hr) as Hns. unfold is_selector_shaped in Hns.
    destruct (bool_dec (go_ident s) true) as [ Hd | _ ]; [ exfalso; congruence | ].
    destruct (bool_dec (is_dec s) true) as [ Hd2 | _ ]; [ exfalso; congruence | ].
    destruct (split_last_dot s) as [ [ op fld ] | ] eqn:Esp.
    + cbn in Hns.
      destruct (bool_dec (go_ident fld) true) as [ Hf3 | _ ]; [ exfalso; congruence | ].
      destruct (bool_dec (raw_ok s) true) as [ Hr2 | Hr2 ]; [ | exfalso; apply Hr2; exact Hr ].
      assert (E : Hr2 = Hr) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
    + destruct (bool_dec (raw_ok s) true) as [ Hr2 | Hr2 ]; [ | exfalso; apply Hr2; exact Hr ].
      assert (E : Hr2 = Hr) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
  - destruct f as [ | g ]; [ lia | ]. destruct fld as [ fs Hfs ]; cbn [proj1_sig] in *.
    assert (Hdf : dot_free fs = true) by (apply all_idc_dot_free, go_ident_all_idc; exact Hfs).
    pose proof (go_ident_app_dot_false (satom_str a) fs) as Hgo.
    pose proof (is_dec_app_dot_false (satom_str a) fs) as Hid.
    cbn [build_satom].
    destruct (bool_dec (go_ident (satom_str a ++ String (ch 46) fs)) true) as [ Hbad | _ ];
      [ exfalso; congruence | ].
    destruct (bool_dec (is_dec (satom_str a ++ String (ch 46) fs)) true) as [ Hbad | _ ];
      [ exfalso; congruence | ].
    destruct (split_last_dot (satom_str a ++ String (ch 46) fs)) as [ [ op fld2 ] | ] eqn:Esp;
      [ | exfalso; rewrite (split_last_dot_snoc (satom_str a) fs Hdf) in Esp; discriminate Esp ].
    rewrite (split_last_dot_snoc (satom_str a) fs Hdf) in Esp. injection Esp as Eop Efld. subst op fld2.
    destruct (bool_dec (go_ident fs) true) as [ Hf3 | Hf3 ]; [ | exfalso; apply Hf3; exact Hfs ].
    destruct (build_satom g (satom_str a)) as [ sa | ] eqn:Eb.
    + pose proof (IH g ltac:(lia)) as IHa. rewrite Eb in IHa. injection IHa as Ea. subst sa.
      assert (E : Hf3 = Hfs) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
    + pose proof (IH g ltac:(lia)) as IHa. rewrite Eb in IHa. discriminate IHa.
Qed.
(** [build_atom] recovers a SCANNED atom (review #5 item 1: [AStringLit] is NOT scanned — it is recovered
    by [parse_strlit_prim], so it is excluded here by the [atom_scanned] hypothesis). *)
Lemma build_atom_str : forall g, atom_scanned g = true -> build_atom (atom_str g) = Some (EAtom g).
Proof.
  intros [ s | r ] Hsc; cbn [atom_str atom_scanned] in *; [ | discriminate Hsc ].
  unfold build_atom. rewrite (build_satom_str_fuel s (String.length (satom_str s)) (satom_len_depth s)).
  reflexivity.
Qed.

(** The precedence-climbing parser (Go's binary-operator grammar): [parse_expr k] reads the maximal
    expression whose operators all bind at precedence [>= k]; [parse_primary] reads an atom (via
    [build_atom]) or a "("-delimited sub-expression; [parse_climb] left-folds operators of precedence
    [>= k].  Fuel bounds the recursion (every call strictly decreases it). *)
(** The STRING-LITERAL PRIMARY (review #5 item 1): a quoted literal is parsed HERE, in quote/escape mode
    via [scan_strlit_body] — NOT by [scan_atom], which would mis-read its CONTENTS as Go source.  It reads
    the body to the closing quote and [unescape]s it to the SEMANTIC VALUE, returning [AStringLit value]
    (review #7 item 4: AST-first).  So a valid Go string like "a + b" / "[" parses correctly.  No
    canonicality re-check / UIP is needed — [print_string_lit (unescape (esc_string v)) = print_string_lit v]
    holds by [esc_string_roundtrip].  No fuel: [scan_strlit_body] is structural. *)
Definition parse_strlit_prim (s : string) : option (GoExpr * string) :=
  match s with
  | String c s' =>
      if Ascii.eqb c (ch 34) then
        match scan_strlit_body s' with
        | Some (body, rest) => Some (EAtom (AStringLit (unescape body)), rest)
        | None => None
        end
      else None
  | EmptyString => None
  end.
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
        else if Ascii.eqb c (ch 34) then parse_strlit_prim s
        else if is_unop_char c then
          (* UNARY PREFIX (review #6): an unspaced unary op ([!]/[^]/[*]/[&]).  The operand is a recursive
             primary.  ('-' is NOT a unop char — a '-'-led string is a negative literal via [scan_atom]). *)
          match unop_char_of c with
          | Some op => match parse_primary f s' with Some (e, s1) => Some (EUnary op e, s1) | None => None end
          | None => None
          end
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
      else if Ascii.eqb c (ch 34) then parse_strlit_prim s
      else if is_unop_char c then
        match unop_char_of c with
        | Some op => match parse_primary f s' with Some (e, s1) => Some (EUnary op e, s1) | None => None end
        | None => None
        end
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
      * destruct (Ascii.eqb c (ch 34)); [ exact H | ].
        destruct (is_unop_char c).
        -- destruct (unop_char_of c) as [ op | ]; [ | exact H ].
           destruct (parse_primary f s') as [ [e s1] | ] eqn:Epp; [ | discriminate H ].
           rewrite (IHp _ _ Epp). exact H.
        -- exact H.
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
Notation EA s := (EAtom (AScanned (SIdent (exist _ s eq_refl)))).
Notation EAr s := (EAtom (AScanned (SRaw (exist _ s eq_refl)))).
Notation EAi z := (EAtom (AScanned (SIntLit z))).  (* a decimal integer-literal atom — carries the [Z], no proof *)
Notation EAsel a f := (EAtom (AScanned (SSelector a (exist _ f eq_refl)))).  (* a selector [operand.field] *)
Notation EAs v := (EAtom (AStringLit v)).  (* a string literal of value [v] *)

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
(** SELECTOR atoms ([SSelector] — the first RECURSIVE atom constructor, structurally shrinking [SRaw]):
    [x.f], the nested [a.b.c] (= [SSelector (SSelector a b) c]), a selector whose operand is a CALL
    ([f(a).g], operand stays [SRaw]), and a selector AS A BINOP OPERAND.  [build_satom] re-splits at each
    '.' ([split_last_dot]) and recovers the nested structure; the round-trip is exact. *)
Example rt_sel_xf : parse_expr 9 0 (print_expr 0 (EAsel (SIdent (exist _ "x" eq_refl)) "f"))
                  = Some (EAsel (SIdent (exist _ "x" eq_refl)) "f", "").  (* x.f *)
Proof. reflexivity. Qed.
Example rt_sel_abc :
  parse_expr 9 0 (print_expr 0 (EAsel (SSelector (SIdent (exist _ "a" eq_refl)) (exist _ "b" eq_refl)) "c"))
  = Some (EAsel (SSelector (SIdent (exist _ "a" eq_refl)) (exist _ "b" eq_refl)) "c", "").  (* a.b.c *)
Proof. reflexivity. Qed.
Example rt_sel_call : parse_expr 9 0 (print_expr 0 (EAsel (SRaw (exist _ "f(a)" eq_refl)) "g"))
                    = Some (EAsel (SRaw (exist _ "f(a)" eq_refl)) "g", "").  (* f(a).g *)
Proof. reflexivity. Qed.
Example rt_sel_bin :
  parse_expr 11 0 (print_expr 0 (EBin BAdd (EAsel (SIdent (exist _ "p" eq_refl)) "x") (EA "c")))
  = Some (EBin BAdd (EAsel (SIdent (exist _ "p" eq_refl)) "x") (EA "c"), "").  (* p.x + c *)
Proof. reflexivity. Qed.
(** A FUNCTION-LITERAL atom — exactly the plugin's arith-force typed-IIFE (e.g. main.go line 322) — is
    now [atomic] (its `-` is inside `{ }`, its `) T {` spaces precede non-op chars) and round-trips even
    as a binary-operator operand.  This is the coverage hole that the depth-0-space ban used to leave
    open: such an atom was NOT atomic, so the round-trip silently did not cover IIFE-containing exprs. *)
Example atomic_funclit :
  atomic "func(x int64, y int64) int64 { return x - y }(0, 7)" = true.
Proof. reflexivity. Qed.
(** The bracket STACK rejects mismatched / cross-nested brackets that the old combined-DEPTH counter
    accepted (combined depth returned to 0 but the kinds don't match). *)
Example bstack_rejects_mismatch :
  atomic "[}" = false /\ atomic "{]" = false /\ atomic "f([})" = false /\ atomic "([)]" = false.
Proof. repeat split; reflexivity. Qed.
(** QUOTE-AWARE scanning (review #5 item 1, the NESTED-literal half): a bracket / operator-seam char INSIDE
    a string literal nested in an atom is now OPAQUE — so [m["["]] (a map index whose key is the string
    "[") and [f("a + b")] (a call whose arg is the string "a + b") are [atomic] / [atom_ok], where the
    quote-UNAWARE scanner miscounted the inner '[' (or tripped the ' + ' seam) and REJECTED them.  The
    inner [""] are escaped dquotes in Coq string syntax. *)
Example atomic_index_bracket_string : atomic "m[""[""]" = true.
Proof. reflexivity. Qed.
Example atomic_call_seam_string : atomic "f(""a + b"")" = true.
Proof. reflexivity. Qed.
Example scan_index_bracket_string :
  scan_atom 0 ("m[""[""]" ++ " + x") = ("m[""[""]", " + x").
Proof. reflexivity. Qed.
(** DECIMAL INTEGER-LITERAL atoms ([AIntLit], carrying the [Z] — its text is the canonical [print_Z]):
    [build_atom] DISAMBIGUATES a digit-led (or '-'-led) atom into [AIntLit], an identifier into [AIdent],
    and the round-trip recovers the EXACT [Z] — across the full int64/uint64 range, negatives included. *)
Example build_atom_dec   : build_atom "42"  = Some (EAi 42).        Proof. reflexivity. Qed.
Example build_atom_neg   : build_atom "-7"  = Some (EAi (-7)).      Proof. reflexivity. Qed.
Example build_atom_ident : build_atom "x42" = Some (EA "x42").      Proof. reflexivity. Qed.
Example rt_intlit : parse_expr 9 0 (print_expr 0 (EBin BAdd (EAi 42) (EAi 7)))
                  = Some (EBin BAdd (EAi 42) (EAi 7), "").  (* 42 + 7 *)
Proof. reflexivity. Qed.
Example rt_intlit_u63 : parse_expr 9 0 (print_expr 0 (EAi 9223372036854775808))
                      = Some (EAi 9223372036854775808, "").  (* the unsigned 2^63 — exact, no truncation *)
Proof. reflexivity. Qed.
(** STRING-LITERAL atoms ([AStringLit]) are now parsed by their OWN quote/escape-mode primary
    ([parse_strlit_prim]), NOT the generic atom scanner — so a literal whose CONTENTS would confuse the
    scanner (a space-then-operator, an unmatched bracket) is REPRESENTABLE and round-trips (review #5
    item 1).  [build_atom] (the generic scanner) does NOT build them: it returns [None] on a dquote-led
    string.  The first two examples are exactly the cases the review flagged as previously rejected. *)
Example strlit_ok_plus_space : strlit_ok (print_string_lit "a + b") = true.   Proof. reflexivity. Qed.
Example strlit_ok_bracket    : strlit_ok (print_string_lit "[") = true.       Proof. reflexivity. Qed.
Example parse_strlit_hi      : parse_strlit_prim (print_string_lit "hi") = Some (EAs "hi", "").  Proof. reflexivity. Qed.
Example build_atom_not_strlit : build_atom (print_string_lit "hi") = None.    Proof. reflexivity. Qed.
Example rt_strlit : parse_expr 12 0 (print_expr 0 (EBin BAdd (EAs "a") (EAs "b")))
                  = Some (EBin BAdd (EAs "a") (EAs "b"), "").
Proof. reflexivity. Qed.
Example rt_strlit_space : parse_expr 12 0 (print_expr 0 (EBin BAdd (EAs "hello world") (EA "z")))
                        = Some (EBin BAdd (EAs "hello world") (EA "z"), "").
Proof. reflexivity. Qed.
Example rt_strlit_seam : parse_expr 12 0 (print_expr 0 (EBin BAdd (EAs "a + b") (EA "z")))
                       = Some (EBin BAdd (EAs "a + b") (EA "z"), "").  (* contents look like an operator seam *)
Proof. reflexivity. Qed.
Example rt_strlit_bracket : parse_expr 12 0 (print_expr 0 (EBin BAdd (EAs "[") (EA "z")))
                          = Some (EBin BAdd (EAs "[") (EA "z"), "").  (* contents are an unmatched bracket *)
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
  match e with
  | EAtom _ => 1 | EBin _ l r => S (esize l + esize r)
  | EUnary _ e => S (S (esize e))   (* +2: the unary op consumes a [parse_primary] step + leaves fuel budget *)
  end.

Fixpoint atomic_tree (e : GoExpr) : Prop :=
  match e with
  | EAtom (AStringLit _) => True   (* the string literal is parsed by its own primary, not [scan_atom] *)
  | EAtom a => atomic (atom_str a) = true
  | EBin _ l r => atomic_tree l /\ atomic_tree r
  | EUnary _ e => atomic_tree e
  end.

(** Both round-trip side-conditions hold for EVERY tree — a SCANNED atom via its [atom_ok] proof in the
    type, an [AStringLit] trivially (it is parsed by [parse_strlit_prim], so needs neither). *)
Lemma atomic_tree_always : forall e, atomic_tree e.
Proof.
  induction e as [ a | o l IHl r IHr | o e IHe ].
  - cbn. destruct a as [ s | r ].
    + apply atom_ok_atomic, (atom_str_atom_ok (AScanned s) eq_refl).
    + exact I.
  - cbn; split; assumption.
  - cbn; exact IHe.
Qed.
Lemma wf_always : forall e, wf e.
Proof.
  induction e as [ a | o l IHl r IHr | o e IHe ].
  - cbn. destruct a as [ s | r ].
    + apply atom_ok_balanced, (atom_str_atom_ok (AScanned s) eq_refl).
    + exact I.
  - cbn; split; assumption.
  - cbn; exact IHe.
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
  | EUnary o e => (fl, EUnary o e, [])   (* a unary expr is a PRIMARY base — no binary left-spine *)
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
  induction e as [ s | o l IHl r IHr | o e0 IHe ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [print_pairs]. rewrite sapp_nil_r. reflexivity.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H.
      rewrite (print_expr_unwrapped o l r fl (ltb_false_of_leb _ _ Eleb)), (IHl _ _ _ _ El),
              print_pairs_app. cbn [print_pairs]. rewrite sapp_nil_r, !sapp_assoc. reflexivity.
    + inversion H; subst. cbn [print_pairs]. rewrite sapp_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [print_pairs]. rewrite sapp_nil_r. reflexivity.
Qed.

Lemma lspine_fold : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> fold_pairs base ps = e.
Proof.
  induction e as [ s | o l IHl r IHr | o e0 IHe ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H.
      rewrite fold_pairs_app. cbn [fold_pairs]. rewrite (IHl _ _ _ _ El). reflexivity.
    + inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
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
  induction e as [ s | o l IHl r IHr | o e0 IHe ]; intros fl bfl base ps Hsih Hwf Hat H.
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
  - cbn in H. inversion H; subst. exact I.
Qed.

(** Appending one [(o,r)] to a spine adds exactly [S (esize r)] fuel; hence base size and spine fuel
    partition [S (esize e)] — so [esize e < F] alone bounds BOTH the base parse and the spine fold. *)
Lemma pairs_fuel_snoc : forall ps o r, pairs_fuel (ps ++ [(o, r)])%list = pairs_fuel ps + (3 * esize r + 3).
Proof.
  induction ps as [ | [o1 r1] ps' IH ]; intros o r; cbn [app pairs_fuel]; [ lia | rewrite IH; lia ].
Qed.

Lemma esize_pos : forall e, 1 <= esize e.
Proof. induction e as [ | o l IHl r IHr | o e0 IHe ]; cbn [esize]; lia. Qed.

(** The crucial fuel accounting: base size and spine fuel partition exactly [S (3*esize e)].  Each spine
    pair [(o, r)] contributes [3*esize r + 3] (operand budget [3*esize r] + 2 wrap slack + 1 climb step),
    and [esize base + sum(esize r) + length = esize e] — so [3*esize base + pairs_fuel ps = 3*esize e + 1].
    Hence [pairs_fuel ps <= 3*esize e - 2] (base parse) and [3*esize base <= 3*esize e - 6] (spine fold)
    both sit under the [3*esize e] budget. *)
Lemma lspine_fuel3 : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> 3 * esize base + pairs_fuel ps = S (3 * esize e).
Proof.
  induction e as [ s | o l IHl r IHr | o e0 IHe ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H. rewrite pairs_fuel_snoc.
      pose proof (IHl _ _ _ _ El) as IH. cbn [esize]. lia.
    + inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
Qed.

(** The base prints as a PRIMARY at its floor [bfl] (an atom, or an [EBin] wrapped because [bfl] exceeds
    its operator precedence) and is well-formed / atomic — so [parse_primary] reads it. *)
Lemma lspine_base : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> wf e -> atomic_tree e ->
  wf base /\ atomic_tree base /\
  match base with EAtom _ => True | EUnary _ _ => True | EBin o' _ _ => binop_prec o' < bfl end.
Proof.
  induction e as [ s | o l IHl r IHr | o e0 IHe ]; intros fl bfl base ps H Hwf Hat.
  - cbn in H. inversion H; subst. cbn [wf atomic_tree] in *.
    split; [ exact Hwf | split; [ exact Hat | exact I ] ].
  - cbn in H. cbn [wf atomic_tree] in Hwf, Hat. destruct Hwf as [ Hwl Hwr ]. destruct Hat as [ Hal Har ].
    destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H. apply (IHl _ _ _ _ El Hwl Hal).
    + inversion H; subst. cbn [wf atomic_tree].
      repeat split; [ exact Hwl | exact Hwr | exact Hal | exact Har | ].
      apply Nat.leb_gt in Eleb. exact Eleb.
  - cbn in H. inversion H; subst. cbn [wf atomic_tree] in *.
    split; [ exact Hwf | split; [ exact Hat | exact I ] ].
Qed.

Lemma lspine_base_le : forall e fl bfl base ps, lspine fl e = (bfl, base, ps) -> esize base <= esize e.
Proof.
  induction e as [ s | o l IHl r IHr | o e0 IHe ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. pose proof (IHl _ _ _ _ El). cbn [esize]. lia.
    + inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
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
(** A SCANNED atom is recovered by [scan_atom] + [build_atom] (the EAtom round-trip case for every atom
    except [AStringLit]).  The first char is not [is_open] (from [atomic]) nor a dquote (from
    [atom_scanned_not_quote_led]), so [parse_primary] takes the generic-atom branch. *)
Lemma parse_primary_scanned : forall s TAIL f, atom_scanned s = true -> good_seam TAIL = true ->
  parse_primary (S f) (atom_str s ++ TAIL)%string = Some (EAtom s, TAIL).
Proof.
  intros s TAIL f Hsc Hgs.
  pose proof (atom_ok_atomic _ (atom_str_atom_ok s Hsc)) as Hatm.
  pose proof (atom_scanned_not_quote_led s Hsc) as Hqnq.
  destruct (atom_str s) as [ | c s' ] eqn:Estr; [ cbn in Hatm; discriminate | ].
  rewrite parse_primary_S.
  assert (Hopen : is_open c = false).
  { unfold atomic in Hatm. apply andb_true_iff in Hatm. destruct Hatm as [ Hno _ ].
    apply negb_true_iff in Hno. exact Hno. }
  assert (Hq : Ascii.eqb c (ch 34) = false) by exact Hqnq.
  cbn [append]. rewrite Hopen, Hq.
  assert (Huol : is_unop_char c = false).
  { change (unary_op_led (String c s') = false). rewrite <- Estr.
    apply atom_scanned_unary_op_led_false; exact Hsc. }
  rewrite Huol.
  assert (Hscan : scan_atom 0 ((String c s') ++ TAIL)%string = (String c s', TAIL))
    by (apply scan_atom_correct; [ exact Hatm | exact Hgs ]).
  change ((String c s') ++ TAIL)%string with (String c (s' ++ TAIL))%string in Hscan.
  rewrite Hscan, <- Estr, (build_atom_str s Hsc). reflexivity.
Qed.
(** [parse_strlit_prim] recovers an [AStringLit] from its printed text (the EAtom round-trip case for a
    STRING LITERAL — quote/escape mode, NOT generic atom scanning). *)
Lemma parse_strlit_prim_correct : forall val TAIL,
  parse_strlit_prim (print_string_lit val ++ TAIL)%string
    = Some (EAtom (AStringLit val), TAIL).
Proof.
  intros val TAIL.
  assert (Hin : (print_string_lit val ++ TAIL)%string
              = String (ch 34) (esc_string val ++ String (ch 34) TAIL)%string).
  { unfold print_string_lit. cbn [String.append]. rewrite sapp_assoc. cbn [String.append]. reflexivity. }
  rewrite Hin. cbn [parse_strlit_prim]. rewrite Ascii.eqb_refl, scan_strlit_body_esc.
  rewrite esc_string_roundtrip. reflexivity.
Qed.
Lemma parse_primary_strlit : forall (val : string) TAIL f,
  parse_primary (S f) (atom_str (AStringLit val) ++ TAIL)%string = Some (EAtom (AStringLit val), TAIL).
Proof.
  intros val TAIL f. cbn [atom_str].
  rewrite parse_primary_S.
  assert (Hin : (print_string_lit val ++ TAIL)%string
              = String (ch 34) (esc_string val ++ String (ch 34) TAIL)%string).
  { unfold print_string_lit. cbn [String.append]. rewrite sapp_assoc. cbn [String.append]. reflexivity. }
  rewrite Hin.
  assert (Ho : is_open (ch 34) = false) by reflexivity.
  assert (Hq : Ascii.eqb (ch 34) (ch 34) = true) by apply Ascii.eqb_refl.
  cbn [String.append]. rewrite Ho, Hq.
  rewrite <- Hin. apply (parse_strlit_prim_correct val TAIL).
Qed.
Lemma binop_prec_lt6 : forall o, binop_prec o < 6.
Proof. intro o; destruct o; cbn [binop_prec]; lia. Qed.
Lemma is_unop_not_open : forall c, is_unop_char c = true -> is_open c = false.
Proof.
  intros c H. unfold is_open. destruct (Ascii.eqb c (ascii_of_nat 40)) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E. subst c. cbn in H. discriminate H.
Qed.
Lemma is_unop_not_quote : forall c, is_unop_char c = true -> Ascii.eqb c (ch 34) = false.
Proof.
  intros c H. destruct (Ascii.eqb c (ch 34)) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E. subst c. cbn in H. discriminate H.
Qed.
(** A PRIMARY base (atom, [EUnary], or an [EBin] wrapped because [binop_prec o' < bfl]) is read by
    [parse_primary].  STRONG induction on [esize base] (the new [EUnary] case recurses on its operand,
    whose round-trip [Pexpr] is supplied by [print_parse_expr_n]'s size-IH [Hsih]). *)
Lemma parse_primary_base : forall n base bfl TAIL F, esize base <= n ->
  (forall e', esize e' < esize base -> wf e' -> atomic_tree e' -> Pexpr e') ->
  wf base -> atomic_tree base -> Pexpr base ->
  match base with EAtom _ => True | EUnary _ _ => True | EBin o' _ _ => binop_prec o' < bfl end ->
  good_seam TAIL = true -> 3 * esize base + 3 < F ->
  parse_primary F (print_expr bfl base ++ TAIL)%string = Some (base, TAIL).
Proof.
  induction n as [ | n IHn ]; intros base bfl TAIL F Hn Hsih Hwf Hat Hpr Hprim Hgs HF.
  - destruct base; cbn [esize] in Hn; lia.
  - destruct base as [ s | o' l' r' | op e ].
    + cbn [print_expr]. destruct F as [ | f ]; [ cbn in HF; lia | ].
      destruct s as [ sc | rs ].
      * apply (parse_primary_scanned (AScanned sc) TAIL f eq_refl Hgs).
      * apply (parse_primary_strlit rs TAIL f).
    + assert (Hwrap : Nat.ltb (binop_prec o') bfl = true) by (apply Nat.ltb_lt; exact Hprim).
      rewrite (print_expr_wrapped o' l' r' bfl Hwrap).
      destruct F as [ | f ]; [ cbn in HF; lia | ].
      rewrite sapp_assoc, parse_primary_paren, sapp_assoc.
      assert (Hpo : Nat.ltb (binop_prec o') (binop_prec o') = false) by (apply Nat.ltb_ge; lia).
      rewrite <- (print_expr_unwrapped o' l' r' (binop_prec o') Hpo).
      assert (Htl0 : tail_ok 0 (")" ++ TAIL)%string).
      { right; left. exists ")"%char, TAIL. split; [ cbn [append]; reflexivity | reflexivity ]. }
      rewrite (Hpr 0 (binop_prec o') (")" ++ TAIL)%string f (Nat.le_0_l _) Htl0 ltac:(cbn [esize] in HF |- *; lia)).
      cbn [append]. reflexivity.
    + (* EUnary op e : [unop_text op ++ print_expr 6 e], a recursive primary *)
      cbn [print_expr]. destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
      destruct (unop_text_char_of op) as [ uc [ us [ Hut [ Hus [ Huc Hisu ] ] ] ] ].
      rewrite Hut, Hus. cbn [append]. rewrite parse_primary_S. cbn [append].
      rewrite (is_unop_not_open uc Hisu), (is_unop_not_quote uc Hisu), Hisu, Huc.
      cbn [wf atomic_tree] in Hwf, Hat.
      rewrite (IHn e 6 TAIL f
                 ltac:(cbn [esize] in Hn; lia)
                 ltac:(intros e' He' We Ae; apply Hsih; [ cbn [esize]; lia | exact We | exact Ae ])
                 Hwf Hat
                 ltac:(apply Hsih; [ cbn [esize]; lia | exact Hwf | exact Hat ])
                 ltac:(destruct e as [ ? | o'' ? ? | ? ? ]; [ exact I | apply binop_prec_lt6 | exact I ])
                 Hgs
                 ltac:(cbn [esize] in HF; lia)).
      reflexivity.
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
            match e with EAtom _ => True | EUnary _ _ => True | EBin o _ _ => ctx <= binop_prec o end ->
            parse_expr F k (print_expr ctx e ++ rest) = Some (e, rest)).
  { intros k ctx rest F Hk Htl HF Hctx. destruct e as [ s | o l r | op e0 ].
    - (* EAtom s — split: a STRING LITERAL via [parse_primary_strlit], any other atom via [_scanned] *)
      cbn [print_expr].
      destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
      destruct f0 as [ | f1 ]; [ cbn [esize] in HF; lia | ].
      assert (Hgs : good_seam rest = true) by (apply (tail_ok_good_seam k); exact Htl).
      assert (Hpp : parse_primary (S f1) (atom_str s ++ rest)%string = Some (EAtom s, rest)).
      { destruct s as [ sc | rs ].
        + apply (parse_primary_scanned (AScanned sc) rest f1 eq_refl Hgs).
        + apply (parse_primary_strlit rs rest f1). }
      rewrite parse_expr_S, Hpp. apply tail_ok_climb_stop. exact Htl.
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
      { apply (parse_primary_base (esize base) base bfl _ f0 (le_n _));
          [ intros e' He' We Ae; apply (IH e'); [ cbn [esize] in Hsz; lia | exact We | exact Ae ]
          | exact Hwb | exact Hab | exact HPbase | exact Hprim
          | apply good_seam_pairs; destruct ps0; discriminate
          | cbn [esize] in HF, Hf3; rewrite Hpfs in Hf3; lia ]. }
      rewrite parse_expr_S, Hpp.
      change (parse_climb f0 k base (print_pairs (ps0 ++ [(o, r)]) ++ rest) = Some (EBin o l r, rest)).
      rewrite (parse_climb_pairs (ps0 ++ [(o, r)]) k base rest f0 Hspine Htl
                 ltac:(cbn [esize] in HF, Hf3; rewrite Hpfs in Hf3; lia)).
      rewrite Hfold. reflexivity.
    - (* EUnary op e0 — a PRIMARY: [unop_text op ++ print_expr 6 e0], NOT ctx-wrapped.
         The leading unary char dispatches [parse_primary] to its unop branch, then [parse_primary_base]
         re-parses the operand [e0] (Pexpr e0 supplied by the OUTER strong IH, not circular). *)
      cbn [print_expr]. rewrite sapp_assoc.
      destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
      destruct f0 as [ | f1 ]; [ cbn [esize] in HF; lia | ].
      assert (Hgs : good_seam rest = true) by (apply (tail_ok_good_seam k); exact Htl).
      destruct (unop_text_char_of op) as [ uc [ us [ Hut [ Hus [ Huc Hisu ] ] ] ] ].
      assert (Hpp : parse_primary (S f1) (unop_text op ++ (print_expr 6 e0 ++ rest))%string
                  = Some (EUnary op e0, rest)).
      { rewrite Hut, Hus. cbn [append]. rewrite parse_primary_S. cbn [append].
        rewrite (is_unop_not_open uc Hisu), (is_unop_not_quote uc Hisu), Hisu, Huc.
        cbn [wf atomic_tree] in Hwf, Hat.
        rewrite (parse_primary_base (esize e0) e0 6 rest f1 (le_n _)
                   ltac:(intros e' He' We Ae; apply (IH e'); [ cbn [esize] in Hsz; lia | exact We | exact Ae ])
                   Hwf Hat
                   ltac:(apply (IH e0); [ cbn [esize] in Hsz; lia | exact Hwf | exact Hat ])
                   ltac:(destruct e0 as [ ? | o'' ? ? | ? ? ]; [ exact I | apply binop_prec_lt6 | exact I ])
                   Hgs ltac:(cbn [esize] in HF; lia)).
        reflexivity. }
      rewrite parse_expr_S, Hpp. apply tail_ok_climb_stop. exact Htl. }
  unfold Pexpr. intros k ctx rest F Hk Htl HF.
  destruct e as [ s | o l r | op e0 ].
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
  - (* EUnary op e0 — never ctx-wrapped (a primary), so [Hunwr] applies directly. *)
    apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
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
Print Assumptions print_parse_expr.
Print Assumptions print_expr_inj.
Print Assumptions print_sep_balanced.

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_expr print_sep print_float_hex atomic atom_ok go_ident nominal_type_ident is_dec raw_ok parse_Z strlit_ok strlit_value build_atom.
