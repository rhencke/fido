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
(** [scan_strlit_body] DISTRIBUTES over a trailing append: the close quote it finds is unchanged, so the
    remainder simply gains [rest].  Strong induction on length (the backslash case consumes 2 chars). *)
Lemma scan_strlit_body_app : forall n s body r rest, String.length s <= n ->
  scan_strlit_body s = Some (body, r) ->
  scan_strlit_body (s ++ rest)%string = Some (body, (r ++ rest)%string).
Proof.
  induction n as [ | n IH ]; intros s body r rest Hlen Hsc.
  - destruct s; [ cbn in Hsc; discriminate | cbn [String.length] in Hlen; lia ].
  - destruct s as [ | c s' ]; [ cbn in Hsc; discriminate | ].
    cbn [String.append] in *. cbn [scan_strlit_body] in Hsc |- *.
    destruct (Ascii.eqb c (ch 34)).
    + injection Hsc as <- <-. reflexivity.
    + destruct (Ascii.eqb c (ch 92)).
      * destruct s' as [ | c2 s'' ]; [ discriminate Hsc | ].
        cbn [String.length] in Hlen. cbn [String.append].
        destruct (scan_strlit_body s'') as [ [b2 r2] | ] eqn:E2; [ | discriminate Hsc ].
        injection Hsc as <- <-. rewrite (IH s'' b2 r2 rest ltac:(lia) E2). reflexivity.
      * cbn [String.length] in Hlen.
        destruct (scan_strlit_body s') as [ [b2 r2] | ] eqn:E2; [ | discriminate Hsc ].
        injection Hsc as <- <-. rewrite (IH s' b2 r2 rest ltac:(lia) E2). reflexivity.
Qed.
(** [scan_strlit_body] consumes at least the closing quote, so its remainder is strictly shorter. *)
Lemma scan_strlit_body_len : forall n s body r, String.length s <= n ->
  scan_strlit_body s = Some (body, r) -> String.length r < String.length s.
Proof.
  induction n as [ | n IH ]; intros s body r Hlen Hsc.
  - destruct s; [ cbn in Hsc; discriminate | cbn [String.length] in Hlen; lia ].
  - destruct s as [ | c s' ]; [ cbn in Hsc; discriminate | ].
    cbn [scan_strlit_body] in Hsc. cbn [String.length].
    destruct (Ascii.eqb c (ch 34)).
    + injection Hsc as <- <-. lia.
    + destruct (Ascii.eqb c (ch 92)).
      * destruct s' as [ | c2 s'' ]; [ discriminate Hsc | ].
        destruct (scan_strlit_body s'') as [ [b2 r2] | ] eqn:E2; [ | discriminate Hsc ].
        injection Hsc as <- <-. cbn [String.length] in Hlen.
        pose proof (IH s'' b2 r2 ltac:(lia) E2). cbn [String.length]. lia.
      * destruct (scan_strlit_body s') as [ [b2 r2] | ] eqn:E2; [ | discriminate Hsc ].
        injection Hsc as <- <-. cbn [String.length] in Hlen.
        pose proof (IH s' b2 r2 ltac:(lia) E2). lia.
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
(** [UNeg] (unary [-]) IS carried — but it prints AMBIGUOUSLY against a negative LITERAL: a bare [-x]
    collides with [-5] ([SIntLit]).  So [UNeg] alone among the unary ops prints PARENTHESISED — [-(x)] —
    and the parser dispatches the unambiguous two-char prefix [-(] to it (see [print_expr]/[parse_primary]).
    The other four ([!]/[^]/[*]/[&]) are single-char-unambiguous and print bare ([unop_char_of] gives the
    dispatch char; [-] is NOT a [unop_char] — it never single-char-dispatches, only via the [-(] prefix). *)
Inductive UnaryOp : Type := UNot | UXor | UDeref | UAddr | UNeg.
Definition unop_text (o : UnaryOp) : string :=
  match o with UNot => "!" | UXor => "^" | UDeref => "*" | UAddr => "&" | UNeg => "-" end.
Definition is_unop_char (c : ascii) : bool :=
  orb (orb (Ascii.eqb c (ch 33)) (Ascii.eqb c (ch 94))) (orb (Ascii.eqb c (ch 42)) (Ascii.eqb c (ch 38))).
Definition unop_char_of (c : ascii) : option UnaryOp :=
  if Ascii.eqb c (ch 33) then Some UNot
  else if Ascii.eqb c (ch 94) then Some UXor
  else if Ascii.eqb c (ch 42) then Some UDeref
  else if Ascii.eqb c (ch 38) then Some UAddr
  else None.
(** The single-char dispatch characterization — for the four bare-printing ops ([UNeg] excluded: it prints
    [-(x)], parsed by the dedicated [-(] prefix branch, not the [is_unop_char] single-char dispatch). *)
Lemma unop_text_char_of : forall o, o <> UNeg -> exists c s,
  unop_text o = String c s /\ s = EmptyString /\ unop_char_of c = Some o /\ is_unop_char c = true.
Proof. intro o; destruct o; intro Hne; cbn; try (eauto 10). exfalso; apply Hne; reflexivity. Qed.


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
      else if andb (Nat.eqb d 0) (orb (orb (orb (opens (String c s')) (is_bclose c)) (Ascii.eqb c (ch 58))) (Ascii.eqb c (ch 44)))
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
      else if andb (Nat.eqb d 0)
                (orb (orb (orb (orb (opens (String c s')) (is_bclose c)) (Ascii.eqb c (ch 58)))
                          (andb (is_space c) (op_after s')))
                     (Ascii.eqb c (ch 44)))
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
              (orb (orb (orb (opens (String c s')) (Ascii.eqb c (ch 58))) (andb (is_space c) (op_after s')))
                   (Ascii.eqb c (ch 44)))
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
            (orb (orb (orb (opens (String c s')) (Ascii.eqb c (ch 58))) (andb (is_space c) (op_after s')))
                 (Ascii.eqb c (ch 44)))
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
(** An identifier char is never a COMMA (ch 44) — discharges the comma-delimiter guard the scanner/validators
    now carry (review #8 P0-1b: a depth-0 comma is a lexical separator, so an ident-led atom is never broken
    by it).  Used wherever a proof reduces [scan_atom]/[bstack_ok]/[atomic_from] past an [is_idc] head. *)
Lemma is_idc_not_comma : forall c, is_idc c = true -> Ascii.eqb c (ch 44) = false.
Proof. intros c Hc. apply (is_idc_eqb_false c 44 Hc); reflexivity. Qed.
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
  assert (Hcolon : Ascii.eqb c (ch 58) = false) by (apply (is_idc_eqb_false c 58 Hc eq_refl)).
  rewrite Hopens, (is_idc_not_space c Hc), (is_idc_not_bopen c Hc), (is_idc_not_bclose c Hc), Hcolon,
          (is_idc_not_comma c Hc).
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

(** ---- HEX LITERALS ARE ATOMS (review #9 A2) ---- every char of [print_hex z] is [is_idc] ('0','x', and
    the hex digits 0-9/a-f), so a hex literal is a plain [atom_ok] atom — exactly like a decimal. *)
Lemma hexdig_is_idc : forall n, (n < 16)%nat -> is_idc (hexdig n) = true.
Proof. intros n H. do 16 (destruct n as [ | n ]; [ vm_compute; reflexivity | ]); lia. Qed.
Lemma zmod16_lt16 : forall z, (Z.to_nat (z mod 16) < 16)%nat.
Proof.
  intro z. assert (Hb : (0 <= z mod 16 < 16)%Z) by (apply Z.mod_pos_bound; lia).
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma hex_digits_all_idc : forall fuel z acc, all_idc acc = true -> all_idc (hex_digits fuel z acc) = true.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hacc; cbn [hex_digits]; [ exact Hacc | ].
  assert (Hd : is_idc (hexdig (Z.to_nat (z mod 16))) = true) by (apply hexdig_is_idc, zmod16_lt16).
  destruct (z / 16 =? 0)%Z.
  - cbn [all_idc]. apply andb_true_iff. split; [ exact Hd | exact Hacc ].
  - apply IH. cbn [all_idc]. apply andb_true_iff. split; [ exact Hd | exact Hacc ].
Qed.
Lemma print_hex_all_idc : forall z, all_idc (print_hex z) = true.
Proof.
  intro z. unfold print_hex. destruct (z =? 0)%Z; [ reflexivity | ].
  cbn [String.append all_idc]. apply andb_true_iff; split; [ reflexivity | ].
  apply andb_true_iff; split; [ reflexivity | ].
  apply (hex_digits_all_idc (digit_fuel z) z "" eq_refl).
Qed.
Lemma print_hex_atom_ok : forall z, atom_ok (print_hex z) = true.
Proof.
  intro z. pose proof (print_hex_all_idc z) as Hall.
  destruct (print_hex_head z) as [ rest Hr ]. rewrite Hr in Hall |- *.
  cbn [all_idc] in Hall. apply andb_true_iff in Hall. destruct Hall as [ Hc Hrest ].
  apply all_idc_cons_atom_ok; [ exact Hc | exact Hrest ].
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
  Ascii.eqb c (ch 34) = false -> Ascii.eqb c (ch 58) = false -> Ascii.eqb c (ch 44) = false ->
  is_space c = false -> is_bopen c = false -> is_bclose c = false ->
  bstack_ok nil s = true -> bstack_ok nil (String c s) = true.
Proof.
  intros c s Hq Hcolon Hcomma Hsp Hbo Hbc Hs. rewrite bstack_ok_cons, Hq.
  assert (Ho : opens (String c s) = false)
    by (unfold opens; rewrite (op_match_not_space c s Hsp); reflexivity).
  rewrite Ho, Hcolon, Hsp, Hbo, Hbc, Hcomma. cbn [andb orb]. exact Hs.
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
                          (orb (orb (orb (opens (String c base')) (Ascii.eqb c (ch 58)))
                                    (andb (is_space c) (op_after base')))
                               (Ascii.eqb c (ch 44)))) eqn:Eseam;
             [ discriminate Hb | ].
           assert (Eseam2 : andb (match st with nil => true | _ => false end)
                     (orb (orb (orb (opens (String c (base' ++ String (ch 46) fld))) (Ascii.eqb c (ch 58)))
                               (andb (is_space c) (op_after (base' ++ String (ch 46) fld))))
                          (Ascii.eqb c (ch 44))) = false).
           { destruct st as [ | t st0 ]; cbn [andb] in Eseam |- *; [ | reflexivity ].
             apply orb_false_iff in Eseam. destruct Eseam as [ Eseam0 Hcomma ].
             apply orb_false_iff in Eseam0. destruct Eseam0 as [ Hoc Hsp ].
             apply orb_false_iff in Hoc. destruct Hoc as [ Hop Hcolon ].
             apply orb_false_iff. split; [ | exact Hcomma ].
             apply orb_false_iff. split.
             - apply orb_false_iff. split; [ | exact Hcolon ].
               destruct (is_space c) eqn:Esc.
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
          [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply all_idc_bstack_ok; exact Hidc ].
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
(** Keywords that legitimately LEAD an operand ATOM-VALUE: only [func]-literals ([func(..){..}(..)]) and
    [map] composite literals ([map[K]V{..}]) — these carry interior depth-0 whitespace / braces and are the
    real primary forms.  [chan]/[struct]/[interface] are TYPE expressions, not atom values, so they are NOT
    exempted (review #8 P0-1: [chan int64] is rejected by [leading_is_keyword]).  A bare [func()] with no
    body is rejected by [raw_wellshaped]'s [has_char "{"] rule — no "the plugin won't emit it" hand-wave. *)
Definition operand_lead_kw (s : string) : bool :=
  existsb (String.eqb s) ["func"; "map"].
Definition leading_is_keyword (s : string) : bool :=
  andb (go_keyword (leading_ident s)) (negb (operand_lead_kw (leading_ident s))).
Definition is_postfix_start (c : ascii) : bool :=
  orb (orb (Ascii.eqb c (ch 46)) (Ascii.eqb c (ch 91))) (Ascii.eqb c (ch 40)).   (* . [ ( — selector / index /
    slice / CALL (review #8 P0-1b STEP 3: '(' splits the call spine off the operand, [scan_base] → operand +
    "(args)" → [SApply]).  A leading "func" is the composite exception ([scan_base]'s [scan_bal]/[scan_to_brace]
    consume its own [(params){body}] BEFORE the postfix split — so a func-lit-CALL is [SApply (SRaw funclit) args]). *)
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

(** [scan_composite_base s] — a LEADING-'[' (array/slice composite [ [N]T{...} / []T{...} ]) or a "map"-led
    (map composite [ map[K]V{...} ]) operand is read WHOLESALE: [scan_to_brace] consumes the dims+element-type
    up to and including the balanced [{body}], then [scan_rest] picks up any trailing postfix.  Falls back to
    [scan_rest] if there is no '{' (not a composite literal). *)
Definition scan_composite_base (s : string) : string * string :=
  match scan_to_brace (String.length s) s with
  | Some (comp, r) => let (more, rest) := scan_rest (String.length r) 0 r in ((comp ++ more)%string, rest)
  | None => scan_rest (String.length s) 0 s
  end.
(** [scan_func_base s] — a "func"-led operand is read WHOLE: [scan_to_brace] consumes the func-lit
    [(params){body}] (so the PARAM '(' is part of the operand, never a call split), then a TRAILING call
    [(args)] (an IIFE) is consumed by [scan_bal] (so [func(){}(args)] is one opaque [SRaw] func-lit-call —
    func-lit bodies hold STATEMENTS, irreducibly opaque until the statement-AST layer).  No [scan_rest], so
    [is_postfix_start]'s '(' never mis-splits a func-lit. *)
Definition scan_func_base (s : string) : string * string :=
  match scan_to_brace (String.length s) s with
  | Some (body, r) =>
      match r with
      | String c _ =>
          if Ascii.eqb c (ch 40)
          then match scan_bal (String.length r) 0 r with
               | Some (call, r2) => ((body ++ call)%string, r2)
               | None => (body, r)
               end
          else (body, r)
      | EmptyString => (body, EmptyString)
      end
  | None => (s, EmptyString)
  end.
(** [scan_base s] — the leading operand.  A LEADING '[' or a "map"-led head is read WHOLE by
    [scan_composite_base]; a "func"-led head by [scan_func_base] (the func-lit + its IIFE call, whole);
    everything else is [scan_rest] (stops at a depth-0 '.'/'['/'(' — an operand-led index/selector/CALL
    spine — [is_postfix_start]).  review #8 P0-1b STEP 3: an IDENTIFIER call [f(a, b)] splits at the '(' →
    [SApply]; a func-lit-call stays a whole opaque [SRaw] (its body is statements — Phase B [GoFuncLit]). *)
Definition scan_base (s : string) : string * string :=
  if String.eqb (leading_ident s) "func" then scan_func_base s
  else if String.eqb (leading_ident s) "map" then scan_composite_base s
  else match s with
       | String c _ => if Ascii.eqb c (ch 91) then scan_composite_base s
                       else scan_rest (String.length s) 0 s
       | EmptyString => (EmptyString, EmptyString)
       end.
(** [whole_base s] — [s] is a COMPLETE opaque base: [scan_base] reads ALL of it (no postfix spine split).
    This is the SRaw INVARIANT (replaces the char-level depth-0-'['/'.' rejection that could not tell a
    composite's leading '[' from an index's operand-led '['): a composite/call/conversion is whole (TRUE),
    an index- or selector-shaped string SPLITS (FALSE).  Exactly the round-trip's need —
    [parse(print(SRaw r)) = SRaw r] requires [scan_base r = (r, "")]. *)
Definition whole_base (s : string) : bool :=
  let (b, r) := scan_base s in andb (String.eqb b s) (String.eqb r "").
(** [is_comp_lead s] — [s] heads a COMPOSITE base ([scan_base] routes it to [scan_composite_base]): a "map"-led
    map literal or a '['-led array/slice literal.  A composite base carries NO postfix spine (the printer never
    indexes/selects a composite LITERAL — [ []int{1,2,3}[0] ] is valid Go but unemitted); [atomic_tree] encodes
    this grammar well-formedness so the round-trip's [scan_base] split stays exact (review #8, rule-2 bounded). *)
Definition is_comp_lead (s : string) : bool :=
  orb (orb (String.eqb (leading_ident s) "map") (String.eqb (leading_ident s) "func"))
      (match s with String c _ => Ascii.eqb c (ch 91) | EmptyString => false end).

(** ── REVIEW #8 P0-1: [raw_ok] now MECHANICALLY enforces the Go PRIMARY-atom LEXICAL invariants, so it
    REJECTS non-atoms (interior spaces, malformed numbers/hex, bare keyword forms) instead of trusting
    "the plugin only emits well-formed ones".  Each conjunct of [raw_wellshaped] is a real Go lexer rule —
    a primary atom is ONE token-run — not an ever-growing ad-hoc scanner. *)
Definition is_ws (c : ascii) : bool :=
  orb (Ascii.eqb c (ch 32)) (orb (Ascii.eqb c (ch 9)) (Ascii.eqb c (ch 10))).
(* quote/bracket-aware DEPTH-0 whitespace: a space/tab/newline outside every bracket and string literal
   splits the atom into >1 token.  (A func-literal's interior ") T {" spaces ARE at depth 0, so func/map
   operand-lead forms are EXEMPTED below — they are the primary forms with legit interior depth-0 space.) *)
Fixpoint has_d0_ws_aux (instr esc : bool) (d : nat) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      if esc then has_d0_ws_aux instr false d s'
      else if instr then (if Ascii.eqb c (ch 92) then has_d0_ws_aux true true d s'
                          else if Ascii.eqb c (ch 34) then has_d0_ws_aux false false d s'
                          else has_d0_ws_aux true false d s')
      else if Ascii.eqb c (ch 34) then has_d0_ws_aux true false d s'
      else if is_bopen c then has_d0_ws_aux false false (S d) s'
      else if is_bclose c then has_d0_ws_aux false false (Nat.pred d) s'
      else if andb (Nat.eqb d 0) (is_ws c) then true
      else has_d0_ws_aux false false d s'
  end.
Definition has_d0_ws (s : string) : bool := has_d0_ws_aux false false 0 s.
Definition is_hex_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (andb (Nat.leb 48 n) (Nat.leb n 57))
      (orb (andb (Nat.leb 97 n) (Nat.leb n 102)) (andb (Nat.leb 65 n) (Nat.leb n 70))).
(* the chars a Go hex literal admits after "0x": hex digits, '.', 'p'/'P' exponent, '+'/'-' sign *)
Definition is_hexlit_char (c : ascii) : bool :=
  orb (is_hex_digit c)
      (orb (Ascii.eqb c (ch 46)) (orb (Ascii.eqb c (ch 112)) (orb (Ascii.eqb c (ch 80))
           (orb (Ascii.eqb c (ch 43)) (Ascii.eqb c (ch 45)))))).
Fixpoint all_hexlit (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (is_hexlit_char c) (all_hexlit s') end.
Definition hex_body_ok (s : string) : bool :=
  match s with String _ (String _ body) => all_hexlit body | _ => true end.
(** [is_hexint s] — [s] is a hex INTEGER literal "0x" + (>=1) hex DIGITS only (no '.'/'p'/exponent — those
    are hex FLOATS, which stay [SRaw]).  Review #9 A2: such a string is the structured [SHexLit], so [raw_ok]
    must REJECT it (else an [SRaw] holding it would collide with [SHexLit] and break the universal round-trip). *)
Fixpoint all_hex_digit (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (is_hex_digit c) (all_hex_digit s') end.
Definition is_hexint (s : string) : bool :=
  match s with
  | String c0 (String c1 body) =>
      andb (andb (Ascii.eqb c0 (ch 48)) (Ascii.eqb c1 (ch 120)))   (* "0x"-led *)
           (all_hex_digit body)                                    (* body is hex DIGITS only (no exponent) *)
  | _ => false
  end.
Fixpoint has_char (target : ascii) (s : string) : bool :=
  match s with EmptyString => false | String c s' => orb (Ascii.eqb c target) (has_char target s') end.
Definition is_digit_led (s : string) : bool :=
  match s with String c _ => is_dec_char c | _ => false end.
Definition func_led (s : string) : bool := String.eqb (leading_ident s) "func".
(** Whole-atom lexical well-shapedness — EACH conjunct a real Go lexer rule. *)
Definition raw_wellshaped (s : string) : bool :=
  andb (andb (andb (orb (operand_lead_kw (leading_ident s)) (negb (has_d0_ws s)))  (* depth-0 ws only in func/map forms *)
                   (orb (negb (is_hex_led s)) (hex_body_ok s)))                    (* a 0x-literal has only hex chars *)
             (andb (orb (negb (is_digit_led s)) (orb (is_dec s) (is_hex_led s)))   (* digit-led ⟹ a decimal or hex *)
                   (orb (negb (func_led s)) (has_char (ch 123) s))))               (* a func-lit carries a "{" body *)
       (negb (is_hexint s)).  (* review #9 A2: a hex INTEGER is the structured [SHexLit], never raw *)

Definition raw_ok (s : string) : bool :=
  andb (raw_wellshaped s)
  (andb
   (andb (andb (andb (andb (andb (andb (atom_ok s) (negb (go_ident s))) (negb (is_dec s)))
                   (negb (quote_led s))) (negb (go_keyword s))) (negb (is_selector_shaped s)))
       (andb (andb (negb (has_d0_break s)) (negb (leading_is_keyword s))) (negb (unary_op_led s))))
   (whole_base s)).

(** REVIEW #8 P0-1 REGRESSION TESTS.  An earlier [vm_compute] confirmed [raw_ok] ACCEPTED all six of these
    non-atoms (silent fail-open).  They are now mechanically REJECTED.  Review #8 P0-1b STEP 3: an IDENTIFIER
    CALL is no longer an opaque raw atom — '(' is a postfix split ([is_postfix_start]), so [f(a, b)] is now a
    structured [SApply], NOT [raw_ok].
    ★QUARANTINE (review #9): a func-lit and its IIFE-call ([func(x int64) int64 { return x }(7)]) are STILL
    whole [raw_ok] — they are the bounded OPAQUE hatch ([scan_func_base] reads them whole), because a func-lit
    BODY is Go STATEMENT syntax, irreducibly opaque until the Phase-B statement AST ([GoFuncLit]/[SFuncLitCall])
    lands.  These are explicitly NON-CORE / not "verified syntax" — they round-trip only as an opaque string;
    do not count them as structured.  A hex mask also still PASSes. *)
Example raw_space_rejected      : raw_ok "foo bar"     = false. Proof. reflexivity. Qed.
Example raw_space2_rejected     : raw_ok "x y"         = false. Proof. reflexivity. Qed.
Example raw_bad_digit_rejected  : raw_ok "123abc"      = false. Proof. reflexivity. Qed.
Example raw_bad_hex_rejected    : raw_ok "0xzz"        = false. Proof. reflexivity. Qed.
Example raw_bad_func_rejected   : raw_ok "func()"      = false. Proof. reflexivity. Qed.
Example raw_chan_type_rejected  : raw_ok "chan int64"  = false. Proof. reflexivity. Qed.
Example raw_call_rejected : raw_ok "f(a, b)" = false. Proof. reflexivity. Qed.  (* a CALL is [SApply], never raw *)
Example raw_hexint_rejected : raw_ok "0xff" = false. Proof. reflexivity. Qed.  (* review #9 A2: a hex INT is [SHexLit] *)
(* a hex FLOAT ([0x..p..]) is NOT a hex INTEGER ([is_hexint] rejects the 'p'/exponent) — it stays a raw atom *)
Example raw_hexfloat_kept : raw_ok "0x14000000000000p-51" = true. Proof. reflexivity. Qed.
(* QUARANTINED non-core: func-lit + IIFE stay whole-opaque until Phase-B [GoFuncLit] — NOT verified syntax. *)
Example raw_funclit_body_quarantined : raw_ok "func(x int64) int64 { return x }" = true. Proof. reflexivity. Qed.
Example raw_funclit_call_quarantined : raw_ok "func(x int64) int64 { return x }(7)" = true. Proof. reflexivity. Qed.

Lemma raw_ok_atom_ok : forall s, raw_ok s = true -> atom_ok s = true.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ Ha _ ]. exact Ha.
Qed.
Lemma raw_ok_not_ident : forall s, raw_ok s = true -> go_ident s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_dec : forall s, raw_ok s = true -> is_dec s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_quote_led : forall s, raw_ok s = true -> quote_led s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_keyword : forall s, raw_ok s = true -> go_keyword s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_selector : forall s, raw_ok s = true -> is_selector_shaped s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
  apply andb_true_iff in H. destruct H as [ H _ ].
  apply andb_true_iff in H. destruct H as [ _ Hn ]. apply negb_true_iff in Hn. exact Hn.
Qed.
Lemma raw_ok_not_unary : forall s, raw_ok s = true -> unary_op_led s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
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
(* review #9 QUARANTINE: a func-lit IIFE-call stays a WHOLE opaque [raw_ok] atom ([scan_func_base] reads the
   body + trailing call whole) — non-core, opaque until Phase-B [GoFuncLit]; a func-lit body holds statements. *)
Example raw_ok_funclit_call_quarantined :
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
    [a[i]] / [SApply] [f(args)] carries [GoExpr] children) and expressions contain atoms ([EAtom]), so the
    three families are mutually recursive.  TODAY no atom constructor references [GoExpr] yet (the cycle is
    latent), so the auto-generated per-type induction principles are exactly the non-mutual ones and every
    existing proof is unchanged; grouping them now is the structural prerequisite for the recursive
    expression-carrying atoms. *)
Inductive SAtom : Type :=
  | SIdent    : Ident -> SAtom
  | SIntLit   : Z -> SAtom
  | SHexLit   : N -> SAtom                          (* 0x… hex literal (review #9 A2): a STRUCTURED leaf
                                                       (prints via [print_hex (Z.of_N n)]), replacing the
                                                       hex-mask [SRaw].  The value is [N] — a Go hex literal
                                                       is NON-NEGATIVE, so a negative is UNREPRESENTABLE by
                                                       type and the round-trip ([print_parse_hex] needs 0<=z)
                                                       is total.  A leaf like [SIntLit], base-16 surface. *)
  | SRaw      : { s : string | raw_ok s = true } -> SAtom
  | SSelector : SAtom -> Ident -> SAtom
  | SIndex    : SAtom -> GoExpr -> SAtom            (* a[i]    — postfix index (review #8: the postfix
                                                       PrimaryExpr grammar replacing SRaw for indexes) *)
  | SSlice    : SAtom -> GoExpr -> GoExpr -> SAtom  (* a[lo:hi] — postfix slice *)
  | SApply     : SAtom -> ArgList -> SAtom           (* operand(args) — APPLICATION syntax (review #9): a Go
                                                       function CALL [f(a, b)] AND an identifier-led CONVERSION
                                                       [int64(x)] / [MyType(x)] are the SAME syntactic node —
                                                       indistinguishable at the token level (call vs conversion
                                                       depends on whether the operand denotes a type, which
                                                       needs a type namespace).  The semantic distinction is
                                                       carried by the GENERATOR, not faked in the parser;
                                                       [SConvert] (Phase A3) is reserved for TYPE-FORM-led
                                                       conversions ([[]T(x)]/[*T(x)]/[map[K]V(x)]) that ARE
                                                       syntactically unambiguous.  args = a MUTUAL [ArgList]
                                                       (so [GoTree_mutind] yields a per-arg IH). *)
with GoAtom : Type :=
  | AScanned   : SAtom -> GoAtom
  | AStringLit : string -> GoAtom   (* the SEMANTIC string VALUE (review #7 item 4: AST-first, not the
                                       printed lexeme).  ANY value is printable, so no proof is needed —
                                       an invalid literal SOURCE is unrepresentable by construction. *)
with GoExpr : Type :=
  | EAtom  : GoAtom -> GoExpr
  | EBin   : BinOp -> GoExpr -> GoExpr -> GoExpr
  | EUnary : UnaryOp -> GoExpr -> GoExpr
with ArgList : Type :=
  | ANil  : ArgList
  | ACons : GoExpr -> ArgList -> ArgList.
(** [satom_str]/[print_expr]/[atom_str] are ONE mutual [Fixpoint]: [SIndex]/[SSlice] carry [GoExpr]
    children ([a[i]] / [a[lo:hi]]), so the atom printer recurses through the expression printer. *)
Fixpoint satom_str (a : SAtom) : string :=
  match a with
  | SIdent i      => proj1_sig i
  | SIntLit z     => print_Z z
  | SHexLit z     => print_hex (Z.of_N z)
  | SRaw r        => proj1_sig r
  | SSelector a f => (satom_str a ++ String (ch 46) (proj1_sig f))%string
  | SIndex a i    => (satom_str a ++ String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString))%string
  | SSlice a lo hi => (satom_str a ++ String (ch 91)
                        (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString)))%string
  | SApply a args => (satom_str a ++ String (ch 40) (argl_str args ++ String (ch 41) EmptyString))%string
  end
with print_expr (ctx : nat) (e : GoExpr) : string :=
  match e with
  | EAtom a => atom_str a
  | EBin o l r =>
      let p := binop_prec o in
      let inner := (print_expr p l ++ binop_text o ++ print_expr (S p) r)%string in
      if Nat.ltb p ctx then ("(" ++ inner ++ ")")%string else inner
  | EUnary o e =>
      (* unary binds TIGHTER than every binop (prec 5 max), so [EUnary] is a PRIMARY — it never wraps for
         [ctx].  [UNeg] prints PARENTHESISED ([-(e)], operand at prec 0 — the parens make it unambiguous
         vs a [-5] literal and the [-(] prefix is the parser's dispatch); the other four print bare, operand
         at prec 6 so an [EBin] operand parenthesises ([!(a == b)]). *)
      match o with
      | UNeg => ("-(" ++ print_expr 0 e ++ ")")%string
      | _ => (unop_text o ++ print_expr 6 e)%string
      end
  end
with atom_str (a : GoAtom) : string :=
  match a with AScanned s => satom_str s | AStringLit v => print_string_lit v end
with argl_str (l : ArgList) : string :=
  match l with
  | ANil          => EmptyString
  | ACons e ANil  => print_expr 0 e
  | ACons e rest  => (print_expr 0 e ++ String (ch 44) (String (ch 32) (argl_str rest)))%string
  end.
(** [atom_scanned a] — the atom is recovered by the GENERIC atom scanner ([scan_atom] + [build_atom]):
    [AScanned], but not [AStringLit] (recovered by its own quote-aware primary).  Only a scanned atom's
    text is [atom_ok] (a string literal's text need not be — review #5 item 1). *)
Definition atom_scanned (a : GoAtom) : bool := match a with AStringLit _ => false | _ => true end.
(** [satom_ok] / [satom_not_quote_led] and their [GoAtom] wrappers [atom_str_atom_ok] /
    [atom_scanned_not_quote_led] are proved BELOW [atom_ok_app_dotid] (the [SSelector] case needs it).
    ([GoExpr]/[print_expr] are defined ABOVE, in the mutual [SAtom]/[GoAtom]/[GoExpr]/[satom_str] block —
    [SIndex]/[SSlice] carry [GoExpr] children, so the printers are mutual.) *)

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
Lemma print_expr_unary : forall op e ctx, op <> UNeg ->
  print_expr ctx (EUnary op e) = (unop_text op ++ print_expr 6 e)%string.
Proof. intros op e ctx Hne. destruct op; cbn [print_expr]; try reflexivity. exfalso; apply Hne; reflexivity. Qed.
Lemma print_expr_uneg : forall e ctx,
  print_expr ctx (EUnary UNeg e) = ("-(" ++ print_expr 0 e ++ ")")%string.
Proof. reflexivity. Qed.


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
(** [satom_ok] (whole-atom [atom_ok]) is RETIRED by the postfix grammar (review #8): a postfix atom
    [a[i]] is NOT scanned as one [atom_ok] blob — it is [scan_base] (operand) + [parse_postfix] (the
    [GoExpr] children), and [atom_ok (satom_str (SIndex a i))] need not even hold (a string-literal index
    [a["("]] unbalances the non-quote-aware bracket check).  What the first-char dispatch lemmas need is
    only NONEMPTINESS of the operand, captured here. *)
Lemma satom_nonempty : forall a : SAtom, satom_str a <> EmptyString.
Proof.
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [satom_str].
  - destruct i as [ s Hs ]; cbn [proj1_sig].
    destruct s as [ | c s' ]; [ unfold go_ident in Hs; discriminate Hs | discriminate ].
  - pose proof (is_dec_print_Z z) as Hd. destruct (print_Z z) as [ | c rest ]; [ discriminate Hd | discriminate ].
  - exact (print_hex_nonempty (Z.of_N hz)).
  - destruct r as [ s Hr ]; cbn [proj1_sig].
    destruct s as [ | c s' ]; [ apply raw_ok_atom_ok in Hr; discriminate Hr | discriminate ].
  - destruct (satom_str a) as [ | c rest ]; discriminate.
  - destruct (satom_str a) as [ | c rest ]; discriminate.
  - destruct (satom_str a) as [ | c rest ]; discriminate.
  - destruct (satom_str a) as [ | c rest ]; discriminate.
Qed.
(** A scanned atom is never dquote-led (so [parse_primary] sends it to [scan_atom], not the literal prim):
    an identifier is [is_idstart]-led, a decimal is digit/'-'-led, a raw atom is [not quote_led], and a
    SELECTOR begins with its operand (non-dquote by IH; its text is [atom_ok], hence nonempty). *)
Lemma satom_not_quote_led : forall a : SAtom, quote_led (satom_str a) = false.
Proof.
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [satom_str].
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
  - destruct (print_hex_head (Z.of_N hz)) as [ rest Hr ]. rewrite Hr. reflexivity.
  - destruct r as [ s Hr ]; cbn [proj1_sig]. apply raw_ok_not_quote_led; exact Hr.
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; unfold quote_led in IH |- *; exact IH ].
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; unfold quote_led in IH |- *; exact IH ].
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; unfold quote_led in IH |- *; exact IH ].
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; unfold quote_led in IH |- *; exact IH ].
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
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [satom_str].
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
  - destruct (print_hex_head (Z.of_N hz)) as [ rest Hr ]. rewrite Hr. reflexivity.
  - destruct r as [ s Hr ]; cbn [proj1_sig]. apply raw_ok_not_unary; exact Hr.
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; cbn [unary_op_led] in IH |- *; exact IH ].
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; cbn [unary_op_led] in IH |- *; exact IH ].
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; cbn [unary_op_led] in IH |- *; exact IH ].
  - destruct (satom_str a) as [ | c rest ] eqn:Ea;
      [ exfalso; apply (satom_nonempty a); exact Ea
      | cbn [String.append]; cbn [unary_op_led] in IH |- *; exact IH ].
Qed.
Lemma atom_scanned_unary_op_led_false : forall a, atom_scanned a = true -> unary_op_led (atom_str a) = false.
Proof.
  intros [ s | r ] H; cbn [atom_str atom_scanned] in *; [ apply satom_unary_op_led_false | discriminate H ].
Qed.

(** [neg_paren_led s] — [s] heads the unambiguous [UNeg] prefix [-(] (a depth-0 '-' immediately followed by
    '(').  This is EXACTLY [parse_primary]'s [UNeg]-dispatch guard.  No SCANNED atom prints to such a string
    (a negative literal is '-'+DIGIT, never '-'+'('; a raw atom is never '-'-led — a depth-0 '-' is a
    [has_d0_break]), so [parse_primary] dispatches every atom PAST the [UNeg] branch to [scan_atom]. *)
Definition neg_paren_led (s : string) : bool :=
  match s with
  | String c s' => andb (Ascii.eqb c (ch 45)) (match s' with String c1 _ => is_open c1 | _ => false end)
  | EmptyString => false
  end.
(** A leading '-' is itself a depth-0 break (an [is_op_char] outside any bracket/hex-exponent), so it can
    never begin a [raw_ok] atom. *)
Lemma has_d0_break_minus : forall s', has_d0_break (String (ch 45) s') = true.
Proof. intro s'. unfold has_d0_break. destruct (is_hex_led (String (ch 45) s')); reflexivity. Qed.
Lemma is_idc_not_minus : forall c, is_idc c = true -> Ascii.eqb c (ch 45) = false.
Proof. intros c H. exact (is_idc_eqb_false c 45 H eq_refl). Qed.
(** No (scanned) atom's text — even followed by anything — heads the [-(] prefix: by structural induction,
    the leaf base is an identifier ('-'-free), a decimal ('-'+digit, second char not '('), or a raw atom
    ('-'-free via [has_d0_break]); the postfix spine appends AFTER the base, preserving its first two chars. *)
Lemma satom_not_neg_paren_app : forall (a : SAtom) (tail : string),
  neg_paren_led (satom_str a ++ tail) = false.
Proof.
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; intro tail; cbn [satom_str].
  - (* SIdent — go_ident-led, first char is_idstart, never '-' *)
    destruct i as [ s Hs ]; cbn [proj1_sig]. unfold go_ident in Hs.
    destruct s as [ | c s' ]; [ discriminate Hs | ].
    apply andb_true_iff in Hs. destruct Hs as [ Hs _ ]. apply andb_true_iff in Hs. destruct Hs as [ Hstart _ ].
    cbn [append neg_paren_led]. rewrite (is_idc_not_minus c (is_idstart_is_idc c Hstart)). reflexivity.
  - (* SIntLit — print_Z: digit-led, or '-' then a digit (is_open false) *)
    pose proof (is_dec_print_Z z) as Hd. unfold is_dec in Hd.
    destruct (print_Z z) as [ | c rest ] eqn:EP; [ discriminate Hd | ].
    cbn [append neg_paren_led]. destruct (Ascii.eqb c (ch 45)) eqn:Em; [ | reflexivity ].
    unfold ch in Em. rewrite Em in Hd.
    destruct rest as [ | d t ]; [ discriminate Hd | ].
    cbn [all_dec] in Hd. apply andb_true_iff in Hd. destruct Hd as [ Hdc _ ].
    cbn [andb append]. rewrite (is_idc_not_open d (is_dec_char_is_idc d Hdc)). reflexivity.
  - (* SHexLit — print_hex is '0'-led, never '-' *)
    destruct (print_hex_head (Z.of_N hz)) as [ rest Hr ]. rewrite Hr. cbn [append neg_paren_led]. reflexivity.
  - (* SRaw — raw_ok excludes a depth-0 '-' (has_d0_break) *)
    destruct r as [ s Hr ]; cbn [proj1_sig].
    destruct s as [ | c s' ]; [ apply raw_ok_atom_ok in Hr; cbn in Hr; discriminate Hr | ].
    cbn [append neg_paren_led]. destruct (Ascii.eqb c (ch 45)) eqn:Em; [ | reflexivity ].
    exfalso. apply Ascii.eqb_eq in Em. subst c.
    unfold raw_ok in Hr. apply andb_true_iff in Hr. destruct Hr as [ _ Hr ].
    apply andb_true_iff in Hr. destruct Hr as [ Hr _ ].
    apply andb_true_iff in Hr. destruct Hr as [ _ Hr ].
    apply andb_true_iff in Hr. destruct Hr as [ Hr _ ].
    apply andb_true_iff in Hr. destruct Hr as [ Hnb _ ].
    apply negb_true_iff in Hnb. rewrite has_d0_break_minus in Hnb. discriminate Hnb.
  - (* SSelector — the spine appends after the base, first two chars from [a] *)
    rewrite sapp_assoc. exact (IH (String (ch 46) (proj1_sig f) ++ tail)).
  - (* SIndex *)
    rewrite sapp_assoc.
    exact (IH (String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString) ++ tail)).
  - (* SSlice *)
    rewrite sapp_assoc.
    exact (IH (String (ch 91) (print_expr 0 lo ++ String (ch 58)
                 (print_expr 0 hi ++ String (ch 93) EmptyString)) ++ tail)).
  - (* SApply — the spine appends "(" args ")" after the base, first two chars from [a] *)
    rewrite sapp_assoc.
    exact (IH (String (ch 40) (argl_str args ++ String (ch 41) EmptyString) ++ tail)).
Qed.
Lemma satom_not_neg_paren : forall a : SAtom, neg_paren_led (satom_str a) = false.
Proof. intro a. rewrite <- (sapp_nil_r (satom_str a)). apply satom_not_neg_paren_app. Qed.
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

(** [wf] is now VACUOUS (review #8 postfix grammar): the old per-[EAtom] [balanced] (raw, NON-quote-aware
    paren depth) is FALSE for a postfix atom carrying a string-literal child ([a["("]] — the paren inside the
    quotes counts though it is not real), AND it is NOT needed: the round-trip below rests ONLY on the
    quote-aware [atomic_tree] (the brackets the parser actually pairs).  Kept as a trivially-true predicate so
    the threaded lemma signatures are unchanged; [wf_always] discharges it for free. *)
Fixpoint wf (e : GoExpr) : Prop :=
  match e with
  | EBin _ l r => wf l /\ wf r
  | EUnary _ e => wf e
  | EAtom _ => True
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
    else if andb (Nat.eqb d 0) (orb (orb (orb (opens (String c s')) (is_bclose c)) (Ascii.eqb c (ch 58))) (Ascii.eqb c (ch 44)))
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
    else if andb (Nat.eqb d 0)
              (orb (orb (orb (orb (opens (String c s')) (is_bclose c)) (Ascii.eqb c (ch 58)))
                        (andb (is_space c) (op_after s')))
                   (Ascii.eqb c (ch 44)))
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
              destruct (orb (orb (orb (opens (String c s')) (Ascii.eqb c (ch 58)))
                                  (andb (is_space c) (op_after s')))
                            (Ascii.eqb c (ch 44))) eqn:Eos; [ discriminate H | ].
              apply orb_false_iff in Eos. destruct Eos as [ Eos0 Hcomma ].
              apply orb_false_iff in Eos0. destruct Eos0 as [ Hoc Hsp ].
              apply orb_false_iff in Hoc. destruct Hoc as [ Hop Hcolon ]. cbn [length].
              destruct (is_bopen c) eqn:Ebo.
              ** rewrite Hop, (bopen_not_bclose c Ebo), Hcolon, Hsp, Hcomma. cbn [orb andb Nat.eqb].
                 change (S 0) with (length (cons (close_of c) nil)). apply (proj1 (IH s' _ Hl')); exact H.
              ** destruct (is_bclose c) eqn:Ebc; [ discriminate H | ].
                 rewrite Hop, Hcolon, Hsp, Hcomma. cbn [orb andb Nat.eqb].
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

(** REVIEW #8 P0-1b REGRESSION — the lexer now treats a DEPTH-0 COMMA as a delimiter token (classic
    lexer/parser design, USER directive: "no string splits").  [scan_atom] STOPS at it (it no longer scans
    [a, b] as one blob), and [atomic] REJECTS a depth-0-comma string (more than one atom).  Depth-tracked: a
    comma INSIDE brackets (a call's args) is NOT a delimiter — [f(a, b)] still scans whole, so the change is
    golden BYTE-IDENTICAL (no current SRaw atom has a depth-0 comma).  Foundation for the verified [SApply]
    arg-list — the parser's [expr (',' expr)*] rule will now see the comma as the next token. *)
Example scan_atom_stops_at_comma     : scan_atom 0 "a, b"    = ("a", ", b")%string.   Proof. reflexivity. Qed.
Example scan_atom_keeps_nested_comma : scan_atom 0 "f(a, b)" = ("f(a, b)", "")%string. Proof. reflexivity. Qed.
Example atomic_rejects_depth0_comma  : atomic "a,b" = false.                            Proof. reflexivity. Qed.
Example atomic_keeps_nested_comma    : atomic "f(a,b)" = true.                           Proof. reflexivity. Qed.

(** A [rest] at which [scan_atom] stops cleanly: empty, a depth-0 close bracket (")" / "]" / "}"), or it
    begins an operator.  ([is_bclose], not just ")": the postfix grammar's index/slice children close on
    "]" within the chunk.) *)
Definition good_seam (rest : string) : bool :=
  match rest with EmptyString => true
  | String c _ => orb (orb (orb (opens rest) (is_bclose c)) (Ascii.eqb c (ch 58))) (Ascii.eqb c (ch 44)) end.
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
  unfold good_seam in H. apply orb_true_iff in H. destruct H as [ Hoc | Hcomma ].
  - apply orb_true_iff in Hoc. destruct Hoc as [ Hoc2 | Hcolon ].
    + apply orb_true_iff in Hoc2. destruct Hoc2 as [ Hop | Hcl ].
      * unfold opens in Hop. destruct (op_match (String c2 rs)) eqn:Eop; [ | discriminate Hop ].
        destruct (is_space c2) eqn:Esp.
        -- unfold is_space in Esp. apply Ascii.eqb_eq in Esp; subst c2. reflexivity.
        -- rewrite (op_match_not_space c2 rs Esp) in Eop. discriminate Eop.
      * unfold is_bclose in Hcl. apply orb_true_iff in Hcl. destruct Hcl as [ Hcl | Hcl ];
          [ apply orb_true_iff in Hcl; destruct Hcl as [ Hcl | Hcl ] | ];
          apply Ascii.eqb_eq in Hcl; subst c2; reflexivity.
    + apply Ascii.eqb_eq in Hcolon; subst c2. reflexivity.
  - apply Ascii.eqb_eq in Hcomma; subst c2. reflexivity.
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
                      (orb (orb (orb (orb (opens (String c a')) (is_bclose c)) (Ascii.eqb c (ch 58)))
                                (andb (is_space c) (op_after a')))
                           (Ascii.eqb c (ch 44)))) eqn:Estop;
             [ discriminate Hat | ].
           assert (Estop2 : andb (Nat.eqb d 0)
                     (orb (orb (orb (opens (String c (a' ++ rest))) (is_bclose c)) (Ascii.eqb c (ch 58)))
                          (Ascii.eqb c (ch 44))) = false).
           { destruct (Nat.eqb d 0) eqn:Ed; cbn [andb] in Estop |- *; [ | reflexivity ].
             apply orb_false_iff in Estop. destruct Estop as [ Estop0 Hcomma ].
             apply orb_false_iff in Estop0. destruct Estop0 as [ Hocb Hsp ].
             apply orb_false_iff in Hocb. destruct Hocb as [ Hocb2 Hcolon ].
             apply orb_false_iff in Hocb2. destruct Hocb2 as [ Hop Hbcl ].
             apply orb_false_iff. split; [ | exact Hcomma ].
             apply orb_false_iff. split; [ | exact Hcolon ].
             apply orb_false_iff. split; [ | exact Hbcl ]. unfold opens.
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
    parser is rewired; the faithful-split + round-trip lemmas + the [SIndex]/[SSlice]/[SApply] postfix
    constructors land in the following slices. *)
(* [is_postfix_start]/[scan_bal]/[scan_to_brace]/[scan_rest]/[scan_base]/[whole_base] RELOCATED above [raw_ok] (so [raw_ok] can use [whole_base]). *)
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
Lemma scan_bal_split : forall f d s a r, scan_bal f d s = Some (a, r) -> (a ++ r)%string = s.
Proof.
  induction f as [ | f IH ]; intros d s a r H; cbn [scan_bal] in H; [ discriminate | ].
  destruct s as [ | c s' ]; [ discriminate | ].
  destruct (Ascii.eqb c (ch 34)) eqn:Eq.
  - apply Ascii.eqb_eq in Eq. subst c.
    destruct (scan_strlit_body s') as [ [body rest] | ] eqn:Eb; [ | discriminate ].
    destruct (scan_bal f d rest) as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    injection H as <- <-.
    pose proof (scan_strlit_body_split s' body rest Eb) as Hs'.
    pose proof (IH d rest a2 r2 E2) as Hih.
    cbn [append]. f_equal. rewrite sapp_assoc. cbn [append]. rewrite Hih. symmetry; exact Hs'.
  - destruct (is_bopen c) eqn:Eo.
    + destruct (scan_bal f (S d) s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
      injection H as <- <-. cbn [append]. f_equal. apply (IH (S d) s' a2 r2 E2).
    + destruct (is_bclose c) eqn:Ec.
      * destruct d as [ | d0 ]; [ discriminate | ]. destruct d0 as [ | d1 ].
        -- injection H as <- <-. cbn [append]. reflexivity.
        -- destruct (scan_bal f (S d1) s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
           injection H as <- <-. cbn [append]. f_equal. apply (IH (S d1) s' a2 r2 E2).
      * destruct (scan_bal f d s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
        injection H as <- <-. cbn [append]. f_equal. apply (IH d s' a2 r2 E2).
Qed.
Lemma scan_to_brace_split : forall f s a r, scan_to_brace f s = Some (a, r) -> (a ++ r)%string = s.
Proof.
  induction f as [ | f IH ]; intros s a r H; cbn [scan_to_brace] in H; [ discriminate | ].
  destruct s as [ | c s' ]; [ discriminate | ].
  destruct (Ascii.eqb c (ch 123)) eqn:Eq.
  - apply Ascii.eqb_eq in Eq. subst c. destruct (scan_bal f 1 s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    injection H as <- <-. cbn [append]. f_equal. apply (scan_bal_split f 1 s' a2 r2 E2).
  - destruct (scan_to_brace f s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    injection H as <- <-. cbn [append]. f_equal. apply (IH s' a2 r2 E2).
Qed.

(** PREFIX-STABILITY: a balanced span [scan_bal] reads WHOLE ([r = ""]) is read the SAME when a postfix
    suffix is appended — [scan_bal] stops at the matching close (within [s]), leaving [pops] untouched.  The
    composite-base analog of [scan_rest_clean]; used by [scan_composite_base_correct] for an indexed/selected
    composite literal ([ [3]int{}[i] ]). *)
Lemma scan_bal_prefix : forall f d s a pops, scan_bal f d s = Some (a, EmptyString) ->
  scan_bal f d (s ++ pops)%string = Some (a, pops).
Proof.
  induction f as [ | f IH ]; intros d s a pops H; cbn [scan_bal] in H; [ discriminate | ].
  destruct s as [ | c s' ]; [ discriminate | ]. cbn [String.append]. cbn [scan_bal].
  destruct (Ascii.eqb c (ch 34)) eqn:Eq.
  - destruct (scan_strlit_body s') as [ [body rest] | ] eqn:Eb; [ | discriminate ].
    rewrite (scan_strlit_body_app (String.length s') s' body rest pops (le_n _) Eb).
    destruct (scan_bal f d rest) as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    injection H as Ea Er; subst. rewrite (IH d rest a2 pops E2). reflexivity.
  - destruct (is_bopen c) eqn:Eo.
    + destruct (scan_bal f (S d) s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
      injection H as Ea Er; subst. rewrite (IH (S d) s' a2 pops E2). reflexivity.
    + destruct (is_bclose c) eqn:Ec.
      * destruct d as [ | d0 ]; [ discriminate | ]. destruct d0 as [ | d1 ].
        -- injection H as Ea Er; subst. reflexivity.
        -- destruct (scan_bal f (S d1) s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
           injection H as Ea Er; subst. rewrite (IH (S d1) s' a2 pops E2). reflexivity.
      * destruct (scan_bal f d s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
        injection H as Ea Er; subst. rewrite (IH d s' a2 pops E2). reflexivity.
Qed.
Lemma scan_to_brace_prefix : forall f s a pops, scan_to_brace f s = Some (a, EmptyString) ->
  scan_to_brace f (s ++ pops)%string = Some (a, pops).
Proof.
  induction f as [ | f IH ]; intros s a pops H; cbn [scan_to_brace] in H; [ discriminate | ].
  destruct s as [ | c s' ]; [ discriminate | ]. cbn [String.append]. cbn [scan_to_brace].
  destruct (Ascii.eqb c (ch 123)) eqn:Eq.
  - destruct (scan_bal f 1 s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    injection H as Ea Er; subst. rewrite (scan_bal_prefix f 1 s' a2 pops E2). reflexivity.
  - destruct (scan_to_brace f s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    injection H as Ea Er; subst. rewrite (IH s' a2 pops E2). reflexivity.
Qed.
(** GENERALISED prefix lemmas (arbitrary remainder [r] → [r ++ pops], + the fuel can GROW by any [n] — both
    needed because [scan_composite_base] picks fuel = the input length, which grows under [++ pops]).  Review
    #8 P0-1b STEP 3: the func-lit operand reads via [scan_to_brace] so a TRAILING call splits off. *)
Lemma scan_bal_app : forall f n d s a r pops, scan_bal f d s = Some (a, r) ->
  scan_bal (f + n) d (s ++ pops)%string = Some (a, (r ++ pops)%string).
Proof.
  induction f as [ | f IH ]; intros n d s a r pops H; cbn [scan_bal] in H; [ discriminate | ].
  destruct s as [ | c s' ]; [ discriminate | ]. cbn [Nat.add String.append scan_bal].
  destruct (Ascii.eqb c (ch 34)) eqn:Eq.
  - destruct (scan_strlit_body s') as [ [body rest] | ] eqn:Eb; [ | discriminate ].
    rewrite (scan_strlit_body_app (String.length s') s' body rest pops (le_n _) Eb).
    destruct (scan_bal f d rest) as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    rewrite (IH n d rest a2 r2 pops E2). injection H as Ea Er; subst a r; reflexivity.
  - destruct (is_bopen c) eqn:Eo.
    + destruct (scan_bal f (S d) s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
      rewrite (IH n (S d) s' a2 r2 pops E2). injection H as Ea Er; subst a r; reflexivity.
    + destruct (is_bclose c) eqn:Ec.
      * destruct d as [ | d0 ]; [ discriminate | ]. destruct d0 as [ | d1 ].
        -- injection H as Ea Er; subst a r; reflexivity.
        -- destruct (scan_bal f (S d1) s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
           rewrite (IH n (S d1) s' a2 r2 pops E2). injection H as Ea Er; subst a r; reflexivity.
      * destruct (scan_bal f d s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
        rewrite (IH n d s' a2 r2 pops E2). injection H as Ea Er; subst a r; reflexivity.
Qed.
Lemma scan_to_brace_app : forall f n s a r pops, scan_to_brace f s = Some (a, r) ->
  scan_to_brace (f + n) (s ++ pops)%string = Some (a, (r ++ pops)%string).
Proof.
  induction f as [ | f IH ]; intros n s a r pops H; cbn [scan_to_brace] in H; [ discriminate | ].
  destruct s as [ | c s' ]; [ discriminate | ]. cbn [Nat.add String.append scan_to_brace].
  destruct (Ascii.eqb c (ch 123)) eqn:Eq.
  - destruct (scan_bal f 1 s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    rewrite (scan_bal_app f n 1 s' a2 r2 pops E2). injection H as Ea Er; subst a r; reflexivity.
  - destruct (scan_to_brace f s') as [ [a2 r2] | ] eqn:E2; [ | discriminate ].
    rewrite (IH n s' a2 r2 pops E2). injection H as Ea Er; subst a r; reflexivity.
Qed.

(** ---- THE RECURSIVE ATOM PARSER ---- [build_satom] is [build_atom]'s engine: it DISAMBIGUATES an
    [atom_ok] string into the [SAtom] tree.  [go_ident] -> [SIdent]; [is_dec] -> [SIntLit] (its [Z] via
    [parse_Z]); else if the string is SELECTOR-SHAPED (last '.' followed by a [go_ident] field) peel that
    '.' and RECURSE on the operand -> [SSelector]; else any [raw_ok] string -> [SRaw]; else reject.  The
    selector arm precedes [raw_ok] and [raw_ok] EXCLUDES selector-shaped strings ([raw_ok_not_selector]),
    so each [atom_ok] string takes exactly one arm — the round-trip ([build_satom_str_fuel]) is then UNIQUE.
    Fuel bounds the selector recursion (each '.' strips >= 2 chars; [satom_len_depth] shows the string is
    long enough). *)
(** [satom_depth]/[satom_len_depth] (the [build_satom] selector-recursion fuel bound) are RETIRED with
    [build_satom] — the postfix parser's fuel comes from the [parse_expr] block, not the atom string length. *)
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
(** [build_base] (review #8 — the postfix grammar) — classify a BARE OPERAND string ([scan_base]'s
    result) into its base [SAtom].  NO selector/[split_last_dot] recursion: selectors are now POSTFIX ops
    parsed structurally by [parse_postfix], NOT re-split out of a whole-atom blob.  [go_ident] -> [SIdent];
    [is_dec] -> [SIntLit] (its [Z] via [parse_Z]); any [raw_ok] operand -> [SRaw] (an OPAQUE func-lit /
    composite-literal base); else reject.  Each [atom_ok] operand takes exactly one arm. *)
Definition build_base (a : string) : option SAtom :=
  match bool_dec (go_ident a) true with
  | left Hi => Some (SIdent (exist _ a Hi))
  | right _ =>
    match bool_dec (is_dec a) true with
    | left _ => Some (SIntLit (parse_Z a))
    | right _ =>
      (* review #9 A2: a hex INTEGER literal is the structured [SHexLit] (its [N] via [parse_hex]),
         checked BEFORE [raw_ok] (which now REJECTS hex ints) — disjoint, so the round-trip is unique. *)
      match bool_dec (is_hexint a) true with
      | left _ => Some (SHexLit (Z.to_N (parse_hex a)))
      | right _ =>
        match bool_dec (raw_ok a) true with
        | left Hr => Some (SRaw (exist _ a Hr)) | right _ => None end
      end
    end
  end.
(** The old [build_satom]/[build_atom] whole-atom round-trip ([build_satom_str_fuel]/[build_atom_str]) is
    RETIRED (review #8 — the postfix grammar): a scanned atom is recovered structurally by [scan_base]
    (operand) + [parse_postfix] (the spine), proved by [parse_primary_atom] (below the [parse_expr] block),
    NOT by re-reading the whole printed atom with [split_last_dot] surgery. *)

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
(** [scan_field s] — the maximal leading identifier-char run + the remainder (the SELECTOR field after a
    '.', recovered by [parse_postfix]).  Stops at '.', '[', '(' (not [is_idc]). *)
Fixpoint scan_field (s : string) : string * string :=
  match s with
  | String c s' => if is_idc c then let (i, r) := scan_field s' in (String c i, r) else (EmptyString, s)
  | EmptyString => (EmptyString, EmptyString)
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
        else if andb (Ascii.eqb c (ch 45)) (match s' with String c1 _ => is_open c1 | _ => false end) then
          (* UNARY NEGATION (review #7): the unambiguous two-char prefix [-(].  A bare [-x] would collide with
             a [-5] literal, so [UNeg] alone prints/parses PARENTHESISED — its operand is the recursive
             paren-primary [parse_primary f s'] ([s'] is "("-led here, so the paren rule fires).  ([-]+digit
             does NOT match this guard ([(] vs a digit) and falls through to the atom path — a negative
             literal via [scan_atom], NOT [UNeg]. *)
          match parse_primary f s' with Some (e, s1) => Some (EUnary UNeg e, s1) | None => None end
        else
          (* ATOM (review #8 — the postfix PrimaryExpr grammar): [scan_atom] isolates the atomic CHUNK
             (depth-0 operator seams + negative literals + quotes — already proven); [scan_base] splits the
             chunk into OPERAND + postfix; [build_base] classifies the operand; [parse_postfix] structures
             the spine (.f / [e] / [lo:hi], children via [parse_expr]).  The postfix must fully consume the
             chunk's tail (leftover [""]). *)
          let (chunk, rest) := scan_atom 0 s in
          match chunk with
          | EmptyString => None
          | String _ _ =>
              let (base, post) := scan_base chunk in
              match build_base base with
              | Some a0 =>
                  match parse_postfix f a0 post with
                  | Some (e, EmptyString) => Some (e, rest)
                  | _ => None
                  end
              | None => None
              end
          end
    end
  end
with parse_postfix (fuel : nat) (a : SAtom) (s : string) : option (GoExpr * string) :=
  (* the POSTFIX SPINE: selector (.f) / index ([e]) / slice ([lo:hi]).  Index/slice children are full
     expressions read by [parse_expr] (the 3-way fuel cycle).  Stops (returns the atom) at any non-postfix
     char.  Fuel exhausted = FAILURE (None), distinct from the data-driven stop in the [S f] branch. *)
  match fuel with
  | O => None
  | S f =>
    match s with
    | String c s' =>
        if Ascii.eqb c (ch 46) then
          let (fld, rest) := scan_field s' in
          match bool_dec (go_ident fld) true with
          | left Hf => parse_postfix f (SSelector a (exist _ fld Hf)) rest
          | right _ => None
          end
        else if Ascii.eqb c (ch 91) then
          match parse_expr f 0 s' with
          | Some (lo, s1) =>
              match s1 with
              | String c2 s2 =>
                  if Ascii.eqb c2 (ch 93) then parse_postfix f (SIndex a lo) s2
                  else if Ascii.eqb c2 (ch 58) then
                    match parse_expr f 0 s2 with
                    | Some (hi, s3) =>
                        match s3 with
                        | String c3 s4 => if Ascii.eqb c3 (ch 93) then parse_postfix f (SSlice a lo hi) s4 else None
                        | EmptyString => None
                        end
                    | None => None
                    end
                  else None
              | EmptyString => None
              end
          | None => None
          end
        else if Ascii.eqb c (ch 40) then
          (* CALL (review #8 P0-1b): "(" args ")".  [parse_args] reads the WHOLE argument list (it returns
             [ANil] on an immediate ")" — the empty "()" — else the comma-separated expressions), then ")"
             closes and the spine CONTINUES ([parse_postfix f] — so [g(x)(y)] / [f(x).y] chain). *)
          match parse_args f s' with
          | Some (args, r1) =>
              match r1 with
              | String c2 s3 => if Ascii.eqb c2 (ch 41) then parse_postfix f (SApply a args) s3 else None
              | EmptyString => None
              end
          | None => None
          end
        else Some (EAtom (AScanned a), s)
    | EmptyString => Some (EAtom (AScanned a), EmptyString)
    end
  end
with parse_args (fuel : nat) (s : string) : option (ArgList * string) :=
  (* the ARGUMENT LIST: an immediate ")" is the EMPTY list ([ANil]); otherwise one-or-more expressions
     separated by a depth-0 ", " (the lexer halts each at the comma — review #8 P0-1b STEP 1).  Each arg is
     a full [parse_expr] (the comma is a clean stopping seam, [tail_ok]'s 4th disjunct). *)
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => None
    | String c0 _ =>
        if Ascii.eqb c0 (ch 41) then Some (ANil, s)
        else match parse_expr f 0 s with
             | None => None
             | Some (e, rest) =>
                 match rest with
                 | String c1 (String c2 r2) =>
                     if andb (Ascii.eqb c1 (ch 44)) (Ascii.eqb c2 (ch 32))
                     then match parse_args f r2 with
                          | Some (es, r3) => Some (ACons e es, r3)
                          | None => None
                          end
                     else Some (ACons e ANil, rest)
                 | _ => Some (ACons e ANil, rest)
                 end
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
      else if andb (Ascii.eqb c (ch 45)) (match s' with String c1 _ => is_open c1 | _ => false end) then
        match parse_primary f s' with Some (e, s1) => Some (EUnary UNeg e, s1) | None => None end
      else
        let (chunk, rest) := scan_atom 0 s in
        match chunk with
        | EmptyString => None
        | String _ _ =>
            let (base, post) := scan_base chunk in
            match build_base base with
            | Some a0 => match parse_postfix f a0 post with Some (e, EmptyString) => Some (e, rest) | _ => None end
            | None => None
            end
        end
  end.
Proof. reflexivity. Qed.
Lemma parse_postfix_S : forall f a s, parse_postfix (S f) a s =
  match s with
  | String c s' =>
      if Ascii.eqb c (ch 46) then
        let (fld, rest) := scan_field s' in
        match bool_dec (go_ident fld) true with
        | left Hf => parse_postfix f (SSelector a (exist _ fld Hf)) rest
        | right _ => None
        end
      else if Ascii.eqb c (ch 91) then
        match parse_expr f 0 s' with
        | Some (lo, s1) =>
            match s1 with
            | String c2 s2 =>
                if Ascii.eqb c2 (ch 93) then parse_postfix f (SIndex a lo) s2
                else if Ascii.eqb c2 (ch 58) then
                  match parse_expr f 0 s2 with
                  | Some (hi, s3) =>
                      match s3 with
                      | String c3 s4 => if Ascii.eqb c3 (ch 93) then parse_postfix f (SSlice a lo hi) s4 else None
                      | EmptyString => None
                      end
                  | None => None
                  end
                else None
            | EmptyString => None
            end
        | None => None
        end
      else if Ascii.eqb c (ch 40) then
        match parse_args f s' with
        | Some (args, r1) =>
            match r1 with
            | String c2 s3 => if Ascii.eqb c2 (ch 41) then parse_postfix f (SApply a args) s3 else None
            | EmptyString => None
            end
        | None => None
        end
      else Some (EAtom (AScanned a), s)
  | EmptyString => Some (EAtom (AScanned a), EmptyString)
  end.
Proof. reflexivity. Qed.
Lemma parse_args_S : forall f s, parse_args (S f) s =
  match s with
  | EmptyString => None
  | String c0 _ =>
      if Ascii.eqb c0 (ch 41) then Some (ANil, s)
      else match parse_expr f 0 s with
           | None => None
           | Some (e, rest) =>
               match rest with
               | String c1 (String c2 r2) =>
                   if andb (Ascii.eqb c1 (ch 44)) (Ascii.eqb c2 (ch 32))
                   then match parse_args f r2 with Some (es, r3) => Some (ACons e es, r3) | None => None end
                   else Some (ACons e ANil, rest)
               | _ => Some (ACons e ANil, rest)
               end
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
  (forall a s r, parse_postfix f a s = Some r -> parse_postfix (S f) a s = Some r) /\
  (forall k l s r, parse_climb f k l s = Some r -> parse_climb (S f) k l s = Some r) /\
  (forall s r, parse_args f s = Some r -> parse_args (S f) s = Some r).
Proof.
  induction f as [ | f IH ].
  - repeat split; intros; discriminate.
  - destruct IH as [ IHe [ IHp [ IHpf [ IHc IHargs ] ] ] ]. repeat split.
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
        -- destruct (andb (Ascii.eqb c (ch 45))
                          (match s' with EmptyString => false | String c1 _ => is_open c1 end)).
           ++ destruct (parse_primary f s') as [ [e s1] | ] eqn:Epp; [ | discriminate H ].
              rewrite (IHp _ _ Epp). exact H.
           ++ destruct (scan_atom 0 (String c s')) as [ chunk rest ].
              destruct chunk as [ | cc cr ]; [ exact H | ].
              destruct (scan_base (String cc cr)) as [ base post ].
              destruct (build_base base) as [ a0 | ]; [ | exact H ].
              destruct (parse_postfix f a0 post) as [ [e leftover] | ] eqn:Epp; [ | discriminate H ].
              rewrite (IHpf _ _ _ Epp). exact H.
    + intros a s r H. rewrite parse_postfix_S in H. rewrite parse_postfix_S.
      destruct s as [ | c s' ]; [ exact H | ].
      destruct (Ascii.eqb c (ch 46)).
      * destruct (scan_field s') as [ fld rest ].
        destruct (bool_dec (go_ident fld) true) as [ Hf | _ ]; [ | exact H ].
        apply IHpf. exact H.
      * destruct (Ascii.eqb c (ch 91)).
        -- destruct (parse_expr f 0 s') as [ [lo s1] | ] eqn:Elo; [ | discriminate H ].
           rewrite (IHe _ _ _ Elo).
           destruct s1 as [ | c2 s2 ]; [ discriminate H | ].
           destruct (Ascii.eqb c2 (ch 93)).
           ++ apply IHpf. exact H.
           ++ destruct (Ascii.eqb c2 (ch 58)); [ | discriminate H ].
              destruct (parse_expr f 0 s2) as [ [hi s3] | ] eqn:Ehi; [ | discriminate H ].
              rewrite (IHe _ _ _ Ehi).
              destruct s3 as [ | c3 s4 ]; [ discriminate H | ].
              destruct (Ascii.eqb c3 (ch 93)); [ | discriminate H ].
              apply IHpf. exact H.
        -- destruct (Ascii.eqb c (ch 40)).
           ++ (* CALL: "(" args ")" *)
              destruct (parse_args f s') as [ [args r1] | ] eqn:Epa; [ | discriminate H ].
              rewrite (IHargs _ _ Epa).
              destruct r1 as [ | c2 s3 ]; [ discriminate H | ].
              destruct (Ascii.eqb c2 (ch 41)); [ | discriminate H ].
              apply IHpf. exact H.
           ++ exact H.
    + intros k l s r H. rewrite parse_climb_S in H. rewrite parse_climb_S.
      destruct (op_match s) as [ [o s1] | ]; [ | exact H ].
      destruct (Nat.leb k (binop_prec o)); [ | exact H ].
      destruct (parse_expr f (S (binop_prec o)) s1) as [ [r0 s2] | ] eqn:Epe; [ | discriminate H ].
      rewrite (IHe _ _ _ Epe). apply IHc. exact H.
    + (* parse_args: more fuel preserves the parse *)
      intros s r H. rewrite parse_args_S in H. rewrite parse_args_S.
      destruct s as [ | c0 s' ]; [ exact H | ].
      destruct (Ascii.eqb c0 (ch 41)); [ exact H | ].
      destruct (parse_expr f 0 (String c0 s')) as [ [e rest] | ] eqn:Epe; [ | discriminate H ].
      rewrite (IHe _ _ _ Epe).
      destruct rest as [ | c1 [ | c2 r2 ] ]; [ exact H | exact H | ].
      destruct (andb (Ascii.eqb c1 (ch 44)) (Ascii.eqb c2 (ch 32))); [ | exact H ].
      destruct (parse_args f r2) as [ [es r3] | ] eqn:Epa; [ | discriminate H ].
      rewrite (IHargs _ _ Epa). exact H.
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
Notation EAh n := (EAtom (AScanned (SHexLit n))).  (* a hex integer-literal atom [0x…] — carries the [N], no proof (review #9 A2) *)
Notation EAsel a f := (EAtom (AScanned (SSelector a (exist _ f eq_refl)))).  (* a selector [operand.field] *)
Notation EAs v := (EAtom (AStringLit v)).  (* a string literal of value [v] *)
Notation EApply hd args := (EAtom (AScanned (SApply hd args))).  (* a call [hd(args)] — review #8 SApply *)
Notation EAid s := (SIdent (exist _ s eq_refl)).  (* a bare-identifier SAtom (for an SApply/SSelector head) *)

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
(** ★review #8 P0-1b STEP 3: a CALL is now the STRUCTURED [SApply] node (operand + arg list), no longer an
    opaque [SRaw] — [f(a, b)] parses to [SApply (SIdent "f") [a; b]], and as a binop operand the top-level
    " + " still splits correctly (the call's own parens are at depth > 0). *)
Example rt_call_atom : parse_expr 12 0 (print_expr 0
    (EBin BAdd (EApply (EAid "f") (ACons (EA "a") (ACons (EA "b") ANil))) (EA "c")))
  = Some (EBin BAdd (EApply (EAid "f") (ACons (EA "a") (ACons (EA "b") ANil))) (EA "c"), "").  (* f(a, b) + c *)
Proof. reflexivity. Qed.
Example rt_call_empty : parse_expr 9 0 (print_expr 0 (EApply (EAid "f") ANil))
                      = Some (EApply (EAid "f") ANil, "").  (* f() — empty arg list *)
Proof. reflexivity. Qed.
Example rt_call_nested : parse_expr 12 0 (print_expr 0 (EApply (EAid "g") (ACons (EApply (EAid "f") (ACons (EA "x") ANil)) ANil)))
                       = Some (EApply (EAid "g") (ACons (EApply (EAid "f") (ACons (EA "x") ANil)) ANil), "").  (* g(f(x)) *)
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
Example rt_sel_call : parse_expr 12 0 (print_expr 0 (EAsel (SApply (EAid "f") (ACons (EA "a") ANil)) "g"))
                    = Some (EAsel (SApply (EAid "f") (ACons (EA "a") ANil)) "g", "").  (* f(a).g — now SApply operand *)
Proof. reflexivity. Qed.
Example rt_sel_bin :
  parse_expr 11 0 (print_expr 0 (EBin BAdd (EAsel (SIdent (exist _ "p" eq_refl)) "x") (EA "c")))
  = Some (EBin BAdd (EAsel (SIdent (exist _ "p" eq_refl)) "x") (EA "c"), "").  (* p.x + c *)
Proof. reflexivity. Qed.
(** UNARY NEGATION [UNeg] (review #7 — closes the latent [-x] regression: the plugin's float/f32/complex/
    i64/u64 negations emit Go [-x], which as a binop OPERAND was an [SRaw] "-x" atom [raw_ok] now REJECTS —
    so they MUST become [EUnary UNeg] or [build_atom] aborts).  Unlike the four single-char prefixes, [UNeg]
    prints PARENTHESISED [-(e)] (a bare [-x] would collide with the [-5] literal) and the parser dispatches
    the unambiguous [-(] prefix; a negative LITERAL stays [SIntLit] (the [-(] guard fails on [-]+digit). *)
Example print_uneg : print_expr 0 (EUnary UNeg (EA "x")) = "-(x)". Proof. reflexivity. Qed.
Example rt_uneg_x : parse_expr 30 0 (print_expr 0 (EUnary UNeg (EA "x")))
                  = Some (EUnary UNeg (EA "x"), "").  (* -(x) *)
Proof. reflexivity. Qed.
Example rt_uneg_lit : parse_expr 30 0 (print_expr 0 (EUnary UNeg (EAi 5)))
                    = Some (EUnary UNeg (EAi 5), "").  (* -(5) — UNeg of a literal, distinct from -5 *)
Proof. reflexivity. Qed.
Example rt_neg_lit_stays : parse_expr 30 0 (print_expr 0 (EAi (-5)))
                         = Some (EAi (-5), "").  (* -5 stays a literal, NOT [EUnary UNeg] *)
Proof. reflexivity. Qed.
Example rt_uneg_left : parse_expr 30 0 (print_expr 0 (EBin BAdd (EUnary UNeg (EA "x")) (EA "y")))
                     = Some (EBin BAdd (EUnary UNeg (EA "x")) (EA "y"), "").  (* -(x) + y *)
Proof. reflexivity. Qed.
Example rt_uneg_right : parse_expr 30 0 (print_expr 0 (EBin BAdd (EA "a") (EUnary UNeg (EA "b"))))
                      = Some (EBin BAdd (EA "a") (EUnary UNeg (EA "b")), "").  (* a + -(b) *)
Proof. reflexivity. Qed.
Example rt_uneg_compound : parse_expr 30 0 (print_expr 0 (EUnary UNeg (EBin BAdd (EA "a") (EA "b"))))
                         = Some (EUnary UNeg (EBin BAdd (EA "a") (EA "b")), "").  (* -(a + b) *)
Proof. reflexivity. Qed.
Example rt_uneg_deref : parse_expr 30 0 (print_expr 0 (EUnary UNeg (EUnary UDeref (EA "p"))))
                      = Some (EUnary UNeg (EUnary UDeref (EA "p")), "").  (* negate a pointer deref *)
Proof. reflexivity. Qed.
(** UNeg x POSTFIX-GRAMMAR interaction — the new [UNeg] node as an index/slice CHILD, and the negation OF
    an indexed atom.  The round-trip THEOREM ([print_parse_expr]) already covers these by [atomic_tree];
    these are the explicit WITNESSES of the [UNeg]x[SIndex]/[SSlice] combination (no un-demoed corner). *)
Example rt_idx_uneg :  (* a[-(i)] — UNeg as an index child (parsed at ctx 0 inside [ ]) *)
  parse_expr 30 0 (print_expr 0 (EAtom (AScanned (SIndex (SIdent (exist _ "a" eq_refl)) (EUnary UNeg (EA "i"))))))
  = Some (EAtom (AScanned (SIndex (SIdent (exist _ "a" eq_refl)) (EUnary UNeg (EA "i")))), "").
Proof. reflexivity. Qed.
Example rt_slice_uneg :  (* a[-(i):n] — UNeg as a slice low bound *)
  parse_expr 40 0 (print_expr 0 (EAtom (AScanned
     (SSlice (SIdent (exist _ "a" eq_refl)) (EUnary UNeg (EA "i")) (EA "n")))))
  = Some (EAtom (AScanned (SSlice (SIdent (exist _ "a" eq_refl)) (EUnary UNeg (EA "i")) (EA "n"))), "").
Proof. reflexivity. Qed.
Example rt_uneg_idx :  (* -(a[i]) — negation OF an indexed atom *)
  parse_expr 30 0 (print_expr 0 (EUnary UNeg (EAtom (AScanned (SIndex (SIdent (exist _ "a" eq_refl)) (EA "i"))))))
  = Some (EUnary UNeg (EAtom (AScanned (SIndex (SIdent (exist _ "a" eq_refl)) (EA "i")))), "").
Proof. reflexivity. Qed.
Example rt_uneg_idx_binop :  (* -(a[i]) + b — the negated index as a binop operand *)
  parse_expr 40 0 (print_expr 0 (EBin BAdd
     (EUnary UNeg (EAtom (AScanned (SIndex (SIdent (exist _ "a" eq_refl)) (EA "i"))))) (EA "b")))
  = Some (EBin BAdd (EUnary UNeg (EAtom (AScanned (SIndex (SIdent (exist _ "a" eq_refl)) (EA "i"))))) (EA "b"), "").
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
Example build_base_dec   : build_base "42"  = Some (SIntLit 42).      Proof. reflexivity. Qed.
Example build_base_neg   : build_base "-7"  = Some (SIntLit (-7)).    Proof. reflexivity. Qed.
Example build_base_ident : build_base "x42" = Some (SIdent (exist _ "x42" eq_refl)). Proof. reflexivity. Qed.
(* review #9 A2: a hex INT literal is a VERIFIED [SHexLit] node, NOT an opaque [SRaw] — [build_base]
   recognises [0x…] (the [is_hexint] arm, before [raw_ok]) and round-trips through [print_hex]. *)
Example build_base_hex   : build_base "0xff" = Some (SHexLit 255).  Proof. reflexivity. Qed.
Example build_base_hex0  : build_base "0x0"  = Some (SHexLit 0).    Proof. reflexivity. Qed.
Example rt_hexlit : parse_expr 9 0 (print_expr 0 (EBin BAdd (EAh 255) (EAh 16)))
                  = Some (EBin BAdd (EAh 255) (EAh 16), "").  (* 0xff + 0x10 *)
Proof. reflexivity. Qed.
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
Example build_base_not_strlit : build_base (print_string_lit "hi") = None.    Proof. reflexivity. Qed.
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
(** ★review #9 QUARANTINE: a func-lit CALL (IIFE) is a WHOLE opaque [SRaw] atom — the func-lit body is Go
    STATEMENT syntax, irreducibly opaque until the Phase-B statement AST ([GoFuncLit]).  [scan_func_base]
    reads the body + trailing call whole, so it round-trips as one string.  NON-CORE (not verified syntax);
    it survives only as the bounded opaque hatch, exactly like the review's intent for func-lits. *)
Example rt_funclit :
  parse_expr 12 0 (print_expr 0 (EBin BAdd
    (EAr "func(x int64, y int64) int64 { return x - y }(0, 7)") (EA "z")))
  = Some (EBin BAdd (EAr "func(x int64, y int64) int64 { return x - y }(0, 7)") (EA "z"), "").
Proof. reflexivity. Qed.

(** ============================================================================
    ---- THE UNIVERSAL EXPRESSION ROUND-TRIP ---- the EXAMPLES above fix the precedence-critical cases
    by reflexivity.  [wf] is discharged UNCONDITIONALLY ([wf_always]: [EAtom] carries an [Atom] with its
    [atom_ok] proof in the type, so a malformed atom is unrepresentable).  [atomic_tree] is NOT universal —
    it carries the rule-2 composite-no-spine restriction ([ []int{1,2,3}[0] ] is excluded) — so the headline
    [print_parse_expr] KEEPS it as a premise; it is ENFORCED (not assumed) at the plugin's recovery boundary
    by [build_atom]'s [atomic_tree_b] guard ([build_atom_atomic_tree]/[build_atom_roundtrip]).  The
    parenthesisation [print_expr] emits is precedence-CORRECT (not merely balanced): the Rocq parser re-reads
    the text to the SAME tree [e] — printer/parser SELF-CONSISTENCY (see the section header; this is NOT yet a
    claim about Go's own parser — the remaining gap).  The internal lemmas below THREAD [wf]/[atomic_tree].
    Proven by a combined strong induction on tree size of
    two facts — [P e]
    (round-trip with a stopping tail) and [Left e] (the spine equation: parsing the print of [e] as a
    left operand reduces to [parse_climb] with [e] as the accumulator).  Climb-recursion fuel mismatches
    are bridged by [parse_mono]. *)

(** [esize] now RECURSES INTO an atom's expr children ([SIndex]/[SSlice] carry [GoExpr]s) so the round-trip
    FUEL scales with them — but LEAF-preserving: [asize] of every base/leaf is 1, so [esize (EAtom leaf) = 1]
    exactly as before (the binop machinery's arithmetic is unchanged on leaves; only postfix atoms grow). *)
Fixpoint esize (e : GoExpr) : nat :=
  match e with
  | EAtom a => gsize a
  | EBin _ l r => S (esize l + esize r)
  | EUnary _ e => S (S (esize e))   (* +2: the unary op consumes a [parse_primary] step + leaves fuel budget *)
  end
with gsize (a : GoAtom) : nat :=
  match a with AScanned sa => asize sa | AStringLit _ => 1 end
with asize (a : SAtom) : nat :=
  match a with
  | SIdent _ => 1 | SIntLit _ => 1 | SHexLit _ => 1 | SRaw _ => 1
  | SSelector a _ => S (asize a)
  | SIndex a i => S (asize a + esize i)
  | SSlice a lo hi => S (asize a + esize lo + esize hi)
  | SApply a args => S (S (asize a + argl_size args))   (* +2 slack: the [parse_args] fuel ([opsz OApply]) needs it *)
  end
with argl_size (l : ArgList) : nat :=
  match l with
  | ANil => 0
  | ACons e rest => S (esize e + argl_size rest)
  end.
Lemma asize_pos : forall a, 1 <= asize a.
Proof. destruct a; cbn [asize]; lia. Qed.
Lemma gsize_pos : forall a, 1 <= gsize a.
Proof. destruct a as [ sa | v ]; cbn [gsize]; [ apply asize_pos | lia ]. Qed.
Lemma esize_pos : forall e, 1 <= esize e.
Proof. destruct e as [ a | | ]; cbn [esize]; [ apply gsize_pos | lia | lia ]. Qed.

(** [binop_text]/[unop_text] are BSTACK-NO-OPS inside brackets ([st <> nil]): only spaces + a single
    operator char, none of which is a bracket/quote, and the depth-0 seam check is OFF when [st <> nil]. *)
Lemma bstack_no_bracket_app : forall s st rest,
  (forall c, In c (list_ascii_of_string s) -> Ascii.eqb c (ch 34) = false /\ is_bopen c = false /\ is_bclose c = false) ->
  st <> nil -> bstack_ok st (s ++ rest)%string = bstack_ok st rest.
Proof.
  induction s as [ | c s IH ]; intros st rest Hc Hne; cbn [String.append]; [ reflexivity | ].
  destruct (Hc c (or_introl eq_refl)) as [ Hq [ Hbo Hbc ] ].
  rewrite bstack_ok_cons, Hq.
  destruct st as [ | t st0 ]; [ exfalso; apply Hne; reflexivity | ].
  cbn [andb]. rewrite Hbo, Hbc.
  apply IH; [ intros c' Hin'; apply Hc; right; exact Hin' | exact Hne ].
Qed.

(** An identifier char is never a quote or bracket (its [is_idc] nat-range excludes 34/40/41/91/93/123/125). *)
Lemma is_idc_not_special : forall c, is_idc c = true ->
  Ascii.eqb c (ch 34) = false /\ is_bopen c = false /\ is_bclose c = false.
Proof.
  intros c H. unfold is_bopen, is_bclose. repeat split.
  - apply (is_idc_eqb_false c 34 H eq_refl).
  - rewrite (is_idc_eqb_false c 40 H eq_refl), (is_idc_eqb_false c 91 H eq_refl),
            (is_idc_eqb_false c 123 H eq_refl). reflexivity.
  - rewrite (is_idc_eqb_false c 41 H eq_refl), (is_idc_eqb_false c 93 H eq_refl),
            (is_idc_eqb_false c 125 H eq_refl). reflexivity.
Qed.
(** An all-identifier-char string is bstack-NEUTRAL inside brackets (no bracket/quote chars; seam off). *)
Lemma all_idc_neutral : forall s st rest, all_idc s = true -> st <> nil ->
  bstack_ok st (s ++ rest)%string = bstack_ok st rest.
Proof.
  induction s as [ | c s IH ]; intros st rest Hidc Hne; cbn [String.append]; [ reflexivity | ].
  cbn [all_idc] in Hidc. apply andb_true_iff in Hidc. destruct Hidc as [ Hc Hs ].
  destruct (is_idc_not_special c Hc) as [ Hq [ Hbo Hbc ] ].
  rewrite bstack_ok_cons, Hq.
  destruct st as [ | t st0 ]; [ exfalso; apply Hne; reflexivity | ].
  cbn [andb]. rewrite Hbo, Hbc. apply IH; [ exact Hs | exact Hne ].
Qed.

(** [bstack_skip] runs the SAME string-literal skip as [scan_strlit_body], then resumes [bstack_ok] on the
    remainder — so it equals running [scan_strlit_body] and [bstack_ok]-ing its rest.  Strong induction on
    length (the backslash case consumes 2 chars). *)
Lemma bstack_skip_scan : forall n t st, String.length t <= n ->
  bstack_skip st t = match scan_strlit_body t with Some (_, r) => bstack_ok st r | None => false end.
Proof.
  induction n as [ | n IH ]; intros t st Hlen.
  - destruct t; [ reflexivity | cbn [String.length] in Hlen; lia ].
  - destruct t as [ | c t' ]; [ reflexivity | ].
    cbn [bstack_skip scan_strlit_body].
    destruct (Ascii.eqb c (ch 34)); [ reflexivity | ].
    destruct (Ascii.eqb c (ch 92)).
    + destruct t' as [ | c2 t'' ]; [ reflexivity | ].
      cbn [String.length] in Hlen. rewrite (IH t'' st ltac:(lia)).
      destruct (scan_strlit_body t'') as [ [b r] | ]; reflexivity.
    + cbn [String.length] in Hlen. rewrite (IH t' st ltac:(lia)).
      destruct (scan_strlit_body t') as [ [b r] | ]; reflexivity.
Qed.
(** A printed STRING LITERAL is bstack-NEUTRAL (its body is skipped opaquely; the close quote resumes). *)
Lemma strlit_neutral : forall v st rest, bstack_ok st (print_string_lit v ++ rest)%string = bstack_ok st rest.
Proof.
  intros v st rest.
  assert (Hin : (print_string_lit v ++ rest)%string
              = String (ch 34) (esc_string v ++ String (ch 34) rest)%string)
    by (unfold print_string_lit; cbn [String.append]; rewrite sapp_assoc; cbn [String.append]; reflexivity).
  rewrite Hin, bstack_ok_quote,
          (bstack_skip_scan (String.length (esc_string v ++ String (ch 34) rest)) _ st (le_n _)),
          scan_strlit_body_esc.
  reflexivity.
Qed.

(** [bstack_ok] on a non-quote cons, unfolded (the seam test exposed). *)
Lemma bstack_ok_cons_nq : forall c s' st, Ascii.eqb c (ch 34) = false ->
  bstack_ok st (String c s') =
    if andb (match st with nil => true | _ => false end)
            (orb (orb (orb (opens (String c s')) (Ascii.eqb c (ch 58))) (andb (is_space c) (op_after s')))
                 (Ascii.eqb c (ch 44))) then false
    else if is_bopen c then bstack_ok (cons (close_of c) st) s'
    else if is_bclose c then
      match st with nil => false | cons top st' => if Ascii.eqb c top then bstack_ok st' s' else false end
    else bstack_ok st s'.
Proof. intros c s' st Hq. rewrite bstack_ok_cons, Hq. reflexivity. Qed.
(** ...and on a NON-EMPTY stack with a NON-quote head, the seam is off (stack never empty), so it
    reduces to pure bracket tracking.  Requiring [c <> quote] iota-drops the quote branch — avoiding a
    [bstack_skip] fold/unfold that [reflexivity] chokes on. *)
Lemma bstack_ok_cons_nonnil_nq : forall c s' st, st <> nil -> Ascii.eqb c (ch 34) = false ->
  bstack_ok st (String c s') =
    if is_bopen c then bstack_ok (cons (close_of c) st) s'
    else if is_bclose c then
      match st with nil => false | cons top st' => if Ascii.eqb c top then bstack_ok st' s' else false end
    else bstack_ok st s'.
Proof.
  intros c s' st Hne Hq. destruct st as [ | t st0 ]; [ exfalso; apply Hne; reflexivity | ].
  rewrite bstack_ok_cons, Hq. reflexivity.
Qed.

(** STACK-LIFT: a string [bstack_ok] from [sstack] (which it closes to empty) processes the same way above
    any [st <> nil] suffix — brackets balance back to [st], quotes skip, and the depth-0 seam check is off
    (the stack is never empty above [st]).  Strong induction on length (quote jumps past the literal). *)
Lemma bstack_lift_gen : forall n s sstack st rest, String.length s <= n -> st <> nil ->
  bstack_ok sstack s = true -> bstack_ok (sstack ++ st)%list (s ++ rest)%string = bstack_ok st rest.
Proof.
  induction n as [ | n IH ]; intros s sstack st rest Hlen Hne Hok.
  - destruct s; [ | cbn [String.length] in Hlen; lia ].
    cbn [bstack_ok] in Hok. destruct sstack; [ | discriminate Hok ]. reflexivity.
  - destruct s as [ | c s' ].
    + cbn [bstack_ok] in Hok. destruct sstack; [ | discriminate Hok ]. reflexivity.
    + cbn [String.length] in Hlen. cbn [String.append].
      destruct (Ascii.eqb c (ch 34)) eqn:Eq.
      * (* string literal: fold both sides to [bstack_skip], skip it, recurse on the shorter remainder *)
        apply Ascii.eqb_eq in Eq; subst c.
        rewrite bstack_ok_quote in Hok. rewrite bstack_ok_quote.
        rewrite (bstack_skip_scan (String.length s') s' sstack (le_n _)) in Hok.
        destruct (scan_strlit_body s') as [ [body r2] | ] eqn:Esc; [ | discriminate Hok ].
        rewrite (bstack_skip_scan (String.length (s' ++ rest)) (s' ++ rest) (sstack ++ st) (le_n _)),
                (scan_strlit_body_app (String.length s') s' body r2 rest (le_n _) Esc).
        pose proof (scan_strlit_body_len (String.length s') s' body r2 (le_n _) Esc) as Hlr.
        apply (IH r2 sstack st rest ltac:(lia) Hne Hok).
      * (* NOT a quote: bopen pushes, bclose pops, else is a no-op; the seam is off (goal stack non-nil;
           [Hok = true] forbids it).  Recurse via [IH] on the lifted stack. *)
        rewrite (bstack_ok_cons_nq c s' sstack Eq) in Hok.
        assert (Hgn : (sstack ++ st)%list <> nil)
          by (destruct sstack; cbn [List.app]; [ exact Hne | discriminate ]).
        rewrite (bstack_ok_cons_nonnil_nq c (s' ++ rest) (sstack ++ st) Hgn Eq).
        destruct (andb (match sstack with nil => true | _ => false end)
                       (orb (orb (orb (opens (String c s')) (Ascii.eqb c (ch 58)))
                                 (andb (is_space c) (op_after s')))
                            (Ascii.eqb c (ch 44)))) eqn:Eseam;
          [ discriminate Hok | ].
        destruct (is_bopen c) eqn:Ebo.
        -- exact (IH s' (cons (close_of c) sstack) st rest ltac:(lia) Hne Hok).
        -- destruct (is_bclose c) eqn:Ebc.
           ++ destruct sstack as [ | top st0 ]; [ discriminate Hok | ].
              cbn [List.app]. destruct (Ascii.eqb c top) eqn:Etop; [ | discriminate Hok ].
              exact (IH s' st0 st rest ltac:(lia) Hne Hok).
           ++ exact (IH s' sstack st rest ltac:(lia) Hne Hok).
Qed.

(** Any [atom_ok] text is bstack-NEUTRAL inside brackets: [atomic] gives [bstack_ok nil r], which
    [bstack_lift_gen] carries over any [st <> nil].  Covers identifiers / integers / raw atoms (each is
    [atom_ok] via [go_ident_atom_ok] / [is_dec_atom_ok] / [raw_ok_atom_ok]). *)
Lemma atom_ok_neutral : forall r st rest, atom_ok r = true -> st <> nil ->
  bstack_ok st (r ++ rest)%string = bstack_ok st rest.
Proof.
  intros r st rest Hao Hne.
  unfold atom_ok in Hao. apply andb_true_iff in Hao. destruct Hao as [ Hatm _ ].
  unfold atomic in Hatm.
  destruct r as [ | c0 r0 ]; [ discriminate Hatm | ].
  apply andb_true_iff in Hatm. destruct Hatm as [ _ Hbs ].
  exact (bstack_lift_gen (String.length (String c0 r0)) (String c0 r0) nil st rest (le_n _) Hne Hbs).
Qed.

(** [binop_text]/[unop_text] are bstack-NEUTRAL inside brackets (spaces + a single operator char — no
    bracket/quote — and the seam check is off when [st <> nil]). *)
Lemma binop_neutral : forall o st rest, st <> nil ->
  bstack_ok st (binop_text o ++ rest)%string = bstack_ok st rest.
Proof.
  intros o st rest Hne. apply bstack_no_bracket_app; [ | exact Hne ].
  intros c Hin. destruct o; cbn [binop_text list_ascii_of_string In] in Hin;
    intuition (subst c; repeat split; reflexivity).
Qed.
Lemma unop_neutral : forall o st rest, st <> nil ->
  bstack_ok st (unop_text o ++ rest)%string = bstack_ok st rest.
Proof.
  intros o st rest Hne. apply bstack_no_bracket_app; [ | exact Hne ].
  intros c Hin. destruct o; cbn [unop_text list_ascii_of_string In] in Hin;
    intuition (subst c; repeat split; reflexivity).
Qed.

Scheme GoExpr_mut := Induction for GoExpr Sort Prop
  with GoAtom_mut := Induction for GoAtom Sort Prop
  with SAtom_mut := Induction for SAtom Sort Prop
  with ArgList_mut := Induction for ArgList Sort Prop.
Combined Scheme GoTree_mutind from GoExpr_mut, GoAtom_mut, SAtom_mut, ArgList_mut.

(** A NON-special char (not a quote / open / close) is a bstack NO-OP inside brackets ([st <> nil]):
    no quote-skip, no push, no pop, no depth-0 seam.  Used for the selector "." and the slice ":". *)
Lemma nonspecial_cons : forall c s' st, st <> nil -> Ascii.eqb c (ch 34) = false ->
  is_bopen c = false -> is_bclose c = false -> bstack_ok st (String c s') = bstack_ok st s'.
Proof.
  intros c s' st Hne Hq Hbo Hbc.
  rewrite (bstack_ok_cons_nonnil_nq c s' st Hne Hq), Hbo, Hbc. reflexivity.
Qed.

(** [print_expr]/[atom_str]/[satom_str] are BSTACK-TRANSPARENT inside brackets: processed from a NON-EMPTY
    stack they leave it unchanged (own brackets balance; quotes skip; depth-0 operator seams not checked
    when [st <> nil]).  STRUCTURAL mutual induction (subterms give the IH directly). *)
Lemma print_bstack :
  (forall e c st rest, st <> nil -> bstack_ok st (print_expr c e ++ rest)%string = bstack_ok st rest) /\
  (forall a st rest, st <> nil -> bstack_ok st (atom_str a ++ rest)%string = bstack_ok st rest) /\
  (forall sa st rest, st <> nil -> bstack_ok st (satom_str sa ++ rest)%string = bstack_ok st rest) /\
  (forall args st rest, st <> nil -> bstack_ok st (argl_str args ++ rest)%string = bstack_ok st rest).
Proof.
  apply GoTree_mutind.
  - (* EAtom a *)
    intros a IHa c st rest Hne. rewrite (print_expr_atom c a). exact (IHa st rest Hne).
  - (* EBin o l r *)
    intros o l IHl r IHr c st rest Hne.
    destruct (Nat.ltb (binop_prec o) c) eqn:E.
    + rewrite (print_expr_wrapped o l r c E), !sapp_assoc. cbn [String.append].
      rewrite (bstack_ok_cons_nonnil_nq (ch 40) _ st Hne eq_refl).
      rewrite (IHl (binop_prec o) (cons (close_of (ch 40)) st) _ ltac:(discriminate)).
      rewrite (binop_neutral o (cons (close_of (ch 40)) st) _ ltac:(discriminate)).
      rewrite (IHr (S (binop_prec o)) (cons (close_of (ch 40)) st) _ ltac:(discriminate)).
      cbn [String.append]. reflexivity.
    + rewrite (print_expr_unwrapped o l r c E), !sapp_assoc.
      rewrite (IHl (binop_prec o) st _ Hne).
      rewrite (binop_neutral o st _ Hne).
      rewrite (IHr (S (binop_prec o)) st rest Hne). reflexivity.
  - (* EUnary op e *)
    intros op e IHe c st rest Hne.
    assert (Hnu : forall oo, oo <> UNeg ->
              bstack_ok st (print_expr c (EUnary oo e) ++ rest)%string = bstack_ok st rest).
    { intros oo Hoo. rewrite (print_expr_unary oo e c Hoo), !sapp_assoc,
        (unop_neutral oo st _ Hne), (IHe 6 st rest Hne). reflexivity. }
    destruct op; try (apply Hnu; discriminate).
    (* UNeg: "-(" ++ print 0 e ++ ")" — leading '-' is nonspecial, then push '(' / IHe / pop ')'. *)
    rewrite print_expr_uneg, !sapp_assoc. cbn [String.append].
    rewrite (nonspecial_cons (ch 45) _ st Hne ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)).
    rewrite (bstack_ok_cons_nonnil_nq (ch 40) _ st Hne eq_refl).
    rewrite (IHe 0 (cons (close_of (ch 40)) st) _ ltac:(discriminate)).
    cbn [String.append]. reflexivity.
  - (* AScanned s *)
    intros s IHs st rest Hne. change (atom_str (AScanned s)) with (satom_str s). exact (IHs st rest Hne).
  - (* AStringLit v *)
    intros v st rest Hne. change (atom_str (AStringLit v)) with (print_string_lit v).
    exact (strlit_neutral v st rest).
  - (* SIdent i *)
    intros i st rest Hne. change (satom_str (SIdent i)) with (proj1_sig i).
    apply all_idc_neutral; [ apply go_ident_all_idc; exact (proj2_sig i) | exact Hne ].
  - (* SIntLit z *)
    intros z st rest Hne. change (satom_str (SIntLit z)) with (print_Z z).
    apply atom_ok_neutral; [ apply is_dec_atom_ok, is_dec_print_Z | exact Hne ].
  - (* SHexLit z *)
    intros z st rest Hne. change (satom_str (SHexLit z)) with (print_hex (Z.of_N z)).
    apply atom_ok_neutral; [ apply (print_hex_atom_ok (Z.of_N z)) | exact Hne ].
  - (* SRaw r *)
    intros r st rest Hne. change (satom_str (SRaw r)) with (proj1_sig r).
    apply atom_ok_neutral; [ apply raw_ok_atom_ok; exact (proj2_sig r) | exact Hne ].
  - (* SSelector a f *)
    intros a IHa f st rest Hne.
    change (satom_str (SSelector a f)) with (satom_str a ++ String (ch 46) (proj1_sig f))%string.
    rewrite sapp_assoc, (IHa st _ Hne). cbn [String.append].
    rewrite (nonspecial_cons (ch 46) (proj1_sig f ++ rest) st Hne eq_refl eq_refl eq_refl).
    apply all_idc_neutral; [ apply go_ident_all_idc; exact (proj2_sig f) | exact Hne ].
  - (* SIndex a i *)
    intros a IHa i IHi st rest Hne.
    change (satom_str (SIndex a i))
      with (satom_str a ++ String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString))%string.
    rewrite sapp_assoc, (IHa st _ Hne). cbn [String.append].
    rewrite (bstack_ok_cons_nonnil_nq (ch 91) _ st Hne eq_refl), !sapp_assoc.
    rewrite (IHi 0 (cons (close_of (ch 91)) st) _ ltac:(discriminate)). cbn [String.append]. reflexivity.
  - (* SSlice a lo hi *)
    intros a IHa lo IHlo hi IHhi st rest Hne.
    change (satom_str (SSlice a lo hi))
      with (satom_str a ++ String (ch 91)
              (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString)))%string.
    rewrite sapp_assoc, (IHa st _ Hne). cbn [String.append].
    rewrite (bstack_ok_cons_nonnil_nq (ch 91) _ st Hne eq_refl), !sapp_assoc.
    rewrite (IHlo 0 (cons (close_of (ch 91)) st) _ ltac:(discriminate)). cbn [String.append].
    rewrite (nonspecial_cons (ch 58) _ (cons (close_of (ch 91)) st) ltac:(discriminate) eq_refl eq_refl eq_refl).
    rewrite sapp_assoc, (IHhi 0 (cons (close_of (ch 91)) st) _ ltac:(discriminate)).
    cbn [String.append]. reflexivity.
  - (* SApply a args — push '(' / args neutral / pop ')' *)
    intros a IHa args IHargs st rest Hne.
    change (satom_str (SApply a args))
      with (satom_str a ++ String (ch 40) (argl_str args ++ String (ch 41) EmptyString))%string.
    rewrite sapp_assoc, (IHa st _ Hne). cbn [String.append].
    rewrite (bstack_ok_cons_nonnil_nq (ch 40) _ st Hne eq_refl), !sapp_assoc.
    rewrite (IHargs (cons (close_of (ch 40)) st) _ ltac:(discriminate)). cbn [String.append]. reflexivity.
  - (* ANil — argl_str ANil = "" *)
    intros st rest Hne. cbn [argl_str String.append]. reflexivity.
  - (* ACons e l — first arg, then (", " + tail) when the tail is non-empty *)
    intros e IHe l IHl st rest Hne. destruct l as [ | e' l' ].
    + cbn [argl_str]. exact (IHe 0 st rest Hne).
    + change (argl_str (ACons e (ACons e' l')))
        with (print_expr 0 e ++ String (ch 44) (String (ch 32) (argl_str (ACons e' l'))))%string.
      rewrite sapp_assoc, (IHe 0 st _ Hne). cbn [String.append].
      rewrite (nonspecial_cons (ch 44) _ st Hne eq_refl eq_refl eq_refl).
      rewrite (nonspecial_cons (ch 32) _ st Hne eq_refl eq_refl eq_refl).
      exact (IHl st rest Hne).
Qed.

(** GENERALIZES [bstack_app_dotid] (review #8 postfix grammar): appending a SUFFIX [String sc suf'] to a
    [base] preserves [bstack_ok st base] when (1) the suffix's first char [sc] is a NON-operator char (so it
    cannot create or straddle a depth-0 operator seam — via [op_match_second_nonop]) and (2) the suffix is
    itself balanced from the empty stack ([bstack_ok nil (String sc suf')]).  The selector ".fld", the index
    "[i]" and the slice "[lo:hi]" are all such suffixes.  Strong induction on [base] length, generalized over
    the stack; proves BOTH the [bstack_ok] and [bstack_skip] (in-string) preservations together. *)
Lemma bstack_app_suffix : forall sc suf' n base st,
  is_op_char sc = false -> bstack_ok nil (String sc suf')%string = true -> String.length base <= n ->
  (bstack_ok st base = true -> bstack_ok st (base ++ String sc suf')%string = true) /\
  (bstack_skip st base = true -> bstack_skip st (base ++ String sc suf')%string = true).
Proof.
  intros sc suf' n. induction n as [ | n IH ]; intros base st Hsc Hbal Hlen.
  - destruct base as [ | c base' ]; [ | cbn [String.length] in Hlen; lia ].
    split; [ | intro Hb; cbn [bstack_skip] in Hb; discriminate Hb ].
    intro Hb. cbn [bstack_ok] in Hb. destruct st as [ | t st0 ]; [ | discriminate Hb ].
    cbn [append]. exact Hbal.
  - destruct base as [ | c base' ].
    + split; [ | intro Hb; cbn [bstack_skip] in Hb; discriminate Hb ].
      intro Hb. cbn [bstack_ok] in Hb. destruct st as [ | t st0 ]; [ | discriminate Hb ].
      cbn [append]. exact Hbal.
    + cbn [String.length] in Hlen. assert (Hl' : String.length base' <= n) by lia.
      split.
      * intro Hb. cbn [append]. destruct (Ascii.eqb c (ch 34)) eqn:Eq.
        -- apply Ascii.eqb_eq in Eq. subst c. rewrite bstack_ok_quote in Hb |- *.
           apply (proj2 (IH base' st Hsc Hbal Hl')); exact Hb.
        -- rewrite bstack_ok_cons in Hb. rewrite Eq in Hb. rewrite bstack_ok_cons. rewrite Eq.
           destruct (andb (match st with nil => true | _ => false end)
                          (orb (orb (orb (opens (String c base')) (Ascii.eqb c (ch 58)))
                                    (andb (is_space c) (op_after base')))
                               (Ascii.eqb c (ch 44)))) eqn:Eseam;
             [ discriminate Hb | ].
           assert (Eseam2 : andb (match st with nil => true | _ => false end)
                     (orb (orb (orb (opens (String c (base' ++ String sc suf'))) (Ascii.eqb c (ch 58)))
                               (andb (is_space c) (op_after (base' ++ String sc suf'))))
                          (Ascii.eqb c (ch 44))) = false).
           { destruct st as [ | t st0 ]; cbn [andb] in Eseam |- *; [ | reflexivity ].
             apply orb_false_iff in Eseam. destruct Eseam as [ Eseam0 Hcomma ].
             apply orb_false_iff in Eseam0. destruct Eseam0 as [ Hoc Hsp ].
             apply orb_false_iff in Hoc. destruct Hoc as [ Hop Hcolon ].
             apply orb_false_iff. split; [ | exact Hcomma ].
             apply orb_false_iff. split.
             - apply orb_false_iff. split; [ | exact Hcolon ].
               destruct (is_space c) eqn:Esc.
               + destruct base' as [ | c2 base'' ]; cbn [append].
                 * unfold opens. rewrite (op_match_second_nonop c sc suf' Hsc). reflexivity.
                 * cbn [andb op_after] in Hsp.
                   unfold opens. rewrite (op_match_second_nonop c c2 (base'' ++ String sc suf') Hsp). reflexivity.
               + unfold opens. rewrite (op_match_not_space c (base' ++ String sc suf') Esc). reflexivity.
             - destruct base' as [ | c2 base'' ]; cbn [append op_after].
               + rewrite Hsc. apply andb_false_r.
               + cbn [op_after] in Hsp. exact Hsp. }
           rewrite Eseam2. destruct (is_bopen c) eqn:Ebo.
           ++ apply (proj1 (IH base' (close_of c :: st) Hsc Hbal Hl')); exact Hb.
           ++ destruct (is_bclose c) eqn:Ebc.
              ** destruct st as [ | t st0 ]; [ discriminate Hb | ].
                 destruct (Ascii.eqb c t) eqn:Et;
                   [ apply (proj1 (IH base' st0 Hsc Hbal Hl')); exact Hb | discriminate Hb ].
              ** apply (proj1 (IH base' st Hsc Hbal Hl')); exact Hb.
      * intro Hb. cbn [append]. cbn [bstack_skip] in Hb |- *. destruct (Ascii.eqb c (ch 34)) eqn:Eq1.
        -- apply (proj1 (IH base' st Hsc Hbal Hl')); exact Hb.
        -- destruct (Ascii.eqb c (ch 92)) eqn:Eq2.
           ++ destruct base' as [ | d base'' ]; [ cbn [bstack_skip] in Hb; discriminate Hb | ].
              cbn [append]. assert (Hl'' : String.length base'' <= n) by (cbn [String.length] in Hl'; lia).
              apply (proj2 (IH base'' st Hsc Hbal Hl'')); exact Hb.
           ++ apply (proj2 (IH base' st Hsc Hbal Hl')); exact Hb.
Qed.

(** Pushing a "[" onto ANY stack (incl. nil): the depth-0 seam is off because "[" is not an operator
    ([opens] is false), so it just pushes its matching "]".  ([ascii_of_nat] literals don't reduce under
    [cbn], so the concrete bracket facts are discharged by [reflexivity] asserts.) *)
Lemma bstack_push_bracket : forall X st, opens (String (ch 91) X) = false ->
  bstack_ok st (String (ch 91) X) = bstack_ok (cons (ch 93) st) X.
Proof.
  intros X st Ho. rewrite bstack_ok_cons.
  assert (Hq : Ascii.eqb (ch 91) (ch 34) = false) by reflexivity. rewrite Hq.
  assert (Hseam : andb (match st with nil => true | _ => false end)
            (orb (orb (orb (opens (String (ch 91) X)) (Ascii.eqb (ch 91) (ch 58)))
                      (andb (is_space (ch 91)) (op_after X)))
                 (Ascii.eqb (ch 91) (ch 44))) = false)
    by (rewrite Ho; apply andb_false_r).
  rewrite Hseam.
  assert (Hbo : is_bopen (ch 91) = true) by reflexivity.
  assert (Hcl : close_of (ch 91) = ch 93) by reflexivity. rewrite Hbo, Hcl. reflexivity.
Qed.

(** A printed bracket block is balanced from the EMPTY stack: "[" pushes, the [GoExpr] child is
    bstack-transparent inside ([print_bstack]), "]" pops back. *)
Lemma index_balanced_nil : forall i,
  bstack_ok nil (String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString))%string = true.
Proof.
  intro i.
  assert (Ho : opens (String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString)) = false)
    by (unfold opens; rewrite (op_match_not_space (ch 91) _ eq_refl); reflexivity).
  rewrite (bstack_push_bracket _ nil Ho).
  rewrite (proj1 print_bstack i 0 (cons (ch 93) nil) (String (ch 93) EmptyString) ltac:(discriminate)).
  reflexivity.
Qed.
Lemma slice_balanced_nil : forall lo hi,
  bstack_ok nil (String (ch 91)
    (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString)))%string = true.
Proof.
  intros lo hi.
  assert (Ho : opens (String (ch 91)
      (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString))) = false)
    by (unfold opens; rewrite (op_match_not_space (ch 91) _ eq_refl); reflexivity).
  rewrite (bstack_push_bracket _ nil Ho).
  rewrite (proj1 print_bstack lo 0 (cons (ch 93) nil) _ ltac:(discriminate)).
  rewrite (nonspecial_cons (ch 58) _ (cons (ch 93) nil) ltac:(discriminate) eq_refl eq_refl eq_refl).
  rewrite (proj1 print_bstack hi 0 (cons (ch 93) nil) (String (ch 93) EmptyString) ltac:(discriminate)).
  reflexivity.
Qed.
(** '(' pushes its matching ')' — the paren analogue of [bstack_push_bracket]. *)
Lemma bstack_push_paren : forall X st, opens (String (ch 40) X) = false ->
  bstack_ok st (String (ch 40) X) = bstack_ok (cons (ch 41) st) X.
Proof.
  intros X st Ho. rewrite bstack_ok_cons.
  assert (Hq : Ascii.eqb (ch 40) (ch 34) = false) by reflexivity. rewrite Hq.
  assert (Hseam : andb (match st with nil => true | _ => false end)
            (orb (orb (orb (opens (String (ch 40) X)) (Ascii.eqb (ch 40) (ch 58)))
                      (andb (is_space (ch 40)) (op_after X)))
                 (Ascii.eqb (ch 40) (ch 44))) = false)
    by (rewrite Ho; apply andb_false_r).
  rewrite Hseam.
  assert (Hbo : is_bopen (ch 40) = true) by reflexivity.
  assert (Hcl : close_of (ch 40) = ch 41) by reflexivity. rewrite Hbo, Hcl. reflexivity.
Qed.
(** A printed call suffix "(args)" is balanced from the EMPTY stack: "(" pushes, the arg list is
    bstack-transparent inside ([print_bstack]'s [ArgList] component), ")" pops back. *)
Lemma call_balanced_nil : forall args,
  bstack_ok nil (String (ch 40) (argl_str args ++ String (ch 41) EmptyString))%string = true.
Proof.
  intro args.
  assert (Ho : opens (String (ch 40) (argl_str args ++ String (ch 41) EmptyString)) = false)
    by (unfold opens; rewrite (op_match_not_space (ch 40) _ eq_refl); reflexivity).
  rewrite (bstack_push_paren _ nil Ho).
  rewrite (proj2 (proj2 (proj2 print_bstack)) args (cons (ch 41) nil) (String (ch 41) EmptyString) ltac:(discriminate)).
  reflexivity.
Qed.

(** [atomic] decomposition / introduction (the predicate is [first-char-not-"(" AND bstack-balanced]). *)
Lemma atomic_inv : forall r, atomic r = true ->
  exists c r', r = String c r' /\ is_open c = false /\ bstack_ok nil r = true.
Proof.
  intros r H. destruct r as [ | c r' ]; [ discriminate H | ].
  cbn [atomic] in H. apply andb_true_iff in H. destruct H as [ Hno Hbs ].
  apply negb_true_iff in Hno. exists c, r'. split; [ reflexivity | split; assumption ].
Qed.
Lemma atomic_intro : forall c r', is_open c = false -> bstack_ok nil (String c r')%string = true ->
  atomic (String c r')%string = true.
Proof. intros c r' Ho Hb. cbn [atomic]. rewrite Ho, Hb. reflexivity. Qed.

(** Every SAtom's printed text is [atomic] (review #8): leaves via [atom_ok], a selector via
    [bstack_ok_app_dotid], and the POSTFIX index/slice via [bstack_app_suffix] (operand [bstack_ok] from the
    IH, the bracket block balanced by [index_balanced_nil]/[slice_balanced_nil]).  Note: NOT [atom_ok] — a
    postfix atom carrying a string-literal child unbalances the non-quote-aware [balanced], but [atomic] is
    quote-aware, so the quote-aware bracket balance the parser actually relies on holds. *)
Lemma satom_atomic : forall s : SAtom, atomic (satom_str s) = true.
Proof.
  induction s as [ i | z | hz | r | a IHa f | a IHa i | a IHa lo hi | a IHa args ].
  - change (satom_str (SIdent i)) with (proj1_sig i).
    apply atom_ok_atomic, go_ident_atom_ok, (proj2_sig i).
  - change (satom_str (SIntLit z)) with (print_Z z).
    apply atom_ok_atomic, is_dec_atom_ok, is_dec_print_Z.
  - change (satom_str (SHexLit hz)) with (print_hex (Z.of_N hz)).
    apply atom_ok_atomic, (print_hex_atom_ok (Z.of_N hz)).
  - change (satom_str (SRaw r)) with (proj1_sig r).
    apply atom_ok_atomic, raw_ok_atom_ok, (proj2_sig r).
  - change (satom_str (SSelector a f)) with (satom_str a ++ String (ch 46) (proj1_sig f))%string.
    destruct (atomic_inv _ IHa) as [ c0 [ r0 [ Heq [ Hopen Hbnil ] ] ] ].
    rewrite Heq in Hbnil |- *. cbn [String.append].
    apply atomic_intro; [ exact Hopen | ].
    change (String c0 (r0 ++ String (ch 46) (proj1_sig f)))
      with ((String c0 r0) ++ String (ch 46) (proj1_sig f))%string.
    apply bstack_ok_app_dotid; [ apply go_ident_all_idc, (proj2_sig f) | exact Hbnil ].
  - change (satom_str (SIndex a i))
      with (satom_str a ++ String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString))%string.
    destruct (atomic_inv _ IHa) as [ c0 [ r0 [ Heq [ Hopen Hbnil ] ] ] ].
    rewrite Heq in Hbnil |- *. cbn [String.append].
    apply atomic_intro; [ exact Hopen | ].
    change (String c0 (r0 ++ String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString)))
      with ((String c0 r0) ++ String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString))%string.
    exact (proj1 (bstack_app_suffix (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString)
                   (String.length (String c0 r0)) (String c0 r0) nil
                   eq_refl (index_balanced_nil i) (le_n _)) Hbnil).
  - change (satom_str (SSlice a lo hi))
      with (satom_str a ++ String (ch 91)
              (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString)))%string.
    destruct (atomic_inv _ IHa) as [ c0 [ r0 [ Heq [ Hopen Hbnil ] ] ] ].
    rewrite Heq in Hbnil |- *. cbn [String.append].
    apply atomic_intro; [ exact Hopen | ].
    change (String c0 (r0 ++ String (ch 91)
              (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString))))
      with ((String c0 r0) ++ String (ch 91)
              (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString)))%string.
    exact (proj1 (bstack_app_suffix (ch 91)
                   (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString))
                   (String.length (String c0 r0)) (String c0 r0) nil
                   eq_refl (slice_balanced_nil lo hi) (le_n _)) Hbnil).
  - change (satom_str (SApply a args))
      with (satom_str a ++ String (ch 40) (argl_str args ++ String (ch 41) EmptyString))%string.
    destruct (atomic_inv _ IHa) as [ c0 [ r0 [ Heq [ Hopen Hbnil ] ] ] ].
    rewrite Heq in Hbnil |- *. cbn [String.append].
    apply atomic_intro; [ exact Hopen | ].
    change (String c0 (r0 ++ String (ch 40) (argl_str args ++ String (ch 41) EmptyString)))
      with ((String c0 r0) ++ String (ch 40) (argl_str args ++ String (ch 41) EmptyString))%string.
    exact (proj1 (bstack_app_suffix (ch 40) (argl_str args ++ String (ch 41) EmptyString)
                   (String.length (String c0 r0)) (String c0 r0) nil
                   eq_refl (call_balanced_nil args) (le_n _)) Hbnil).
Qed.

(** [sa_leaf_comp sa] — is the DEEPEST (leftmost) base of [sa] composite-led? (= [is_comp_lead] of
    [fst (spine sa)], spine-free so it can precede [atomic_tree]).  [sa_has_ops] — does [sa] carry a postfix
    spine (= [snd (spine sa) <> nil])? *)
Fixpoint sa_leaf_comp (sa : SAtom) : bool :=
  match sa with
  | SIdent _ | SIntLit _ | SHexLit _ | SRaw _ => is_comp_lead (satom_str sa)
  | SSelector a _ | SIndex a _ | SSlice a _ _ | SApply a _ => sa_leaf_comp a
  end.
Definition sa_has_ops (sa : SAtom) : bool :=
  match sa with SIdent _ | SIntLit _ | SHexLit _ | SRaw _ => false | _ => true end.
(** [atomic_tree] — the round-trip's structural well-formedness, MUTUAL over [GoExpr]/[GoAtom]/[SAtom]:
    every scanned atom's text is [atomic] AND its base is non-composite-OR-spineless (the rule-2 bounded
    exclusion of a composite LITERAL carrying a postfix index/selector — [ []int{1,2,3}[0] ] is valid Go but
    unemitted), RECURSIVELY for the atom's index/slice CHILDREN (so the size-IH recovers each child's round-trip). *)
Fixpoint atomic_tree (e : GoExpr) : Prop :=
  match e with
  | EAtom a => atomic_atom a
  | EBin _ l r => atomic_tree l /\ atomic_tree r
  | EUnary _ e => atomic_tree e
  end
with atomic_atom (a : GoAtom) : Prop :=
  match a with
  | AStringLit _ => True   (* parsed by its own primary, not [scan_atom] *)
  | AScanned sa =>
      atomic (satom_str sa) = true /\
      (sa_leaf_comp sa = false \/ sa_has_ops sa = false) /\
      atomic_satom sa
  end
with atomic_satom (sa : SAtom) : Prop :=
  match sa with
  | SIdent _ => True | SIntLit _ => True | SHexLit _ => True | SRaw _ => True
  | SSelector a _ => atomic_satom a
  | SIndex a i => atomic_satom a /\ atomic_tree i
  | SSlice a lo hi => atomic_satom a /\ atomic_tree lo /\ atomic_tree hi
  | SApply a args => atomic_satom a /\ atomic_arglist args
  end
with atomic_arglist (l : ArgList) : Prop :=
  match l with
  | ANil => True
  | ACons e rest => atomic_tree e /\ atomic_arglist rest
  end.

(** [atomic_tree_b] — the DECIDABLE (boolean) mirror of [atomic_tree] (review #8 P0-3).  [build_atom] checks
    it, so a non-[atomic_tree] atom (e.g. a composite literal carrying a postfix spine, [ []int{1,2,3}[0] ])
    is MECHANICALLY REJECTED at the boundary — the [atomic_tree] premise of [print_parse_expr] is ENFORCED on
    everything the plugin recovers, not assumed.  Reflection [atomic_tree_b_refl] ties it to [atomic_tree]. *)
Fixpoint atomic_tree_b (e : GoExpr) : bool :=
  match e with
  | EAtom a => atomic_atom_b a
  | EBin _ l r => andb (atomic_tree_b l) (atomic_tree_b r)
  | EUnary _ e => atomic_tree_b e
  end
with atomic_atom_b (a : GoAtom) : bool :=
  match a with
  | AStringLit _ => true
  | AScanned sa => andb (andb (atomic (satom_str sa))
                              (orb (negb (sa_leaf_comp sa)) (negb (sa_has_ops sa))))
                        (atomic_satom_b sa)
  end
with atomic_satom_b (sa : SAtom) : bool :=
  match sa with
  | SIdent _ => true | SIntLit _ => true | SHexLit _ => true | SRaw _ => true
  | SSelector a _ => atomic_satom_b a
  | SIndex a i => andb (atomic_satom_b a) (atomic_tree_b i)
  | SSlice a lo hi => andb (andb (atomic_satom_b a) (atomic_tree_b lo)) (atomic_tree_b hi)
  | SApply a args => andb (atomic_satom_b a) (atomic_arglist_b args)
  end
with atomic_arglist_b (l : ArgList) : bool :=
  match l with
  | ANil => true
  | ACons e rest => andb (atomic_tree_b e) (atomic_arglist_b rest)
  end.
Lemma atomic_tree_b_refl :
  (forall e, atomic_tree_b e = true <-> atomic_tree e) /\
  (forall a, atomic_atom_b a = true <-> atomic_atom a) /\
  (forall sa, atomic_satom_b sa = true <-> atomic_satom sa) /\
  (forall args, atomic_arglist_b args = true <-> atomic_arglist args).
Proof.
  apply GoTree_mutind.
  - intros a IHa. cbn [atomic_tree_b atomic_tree]. exact IHa.
  - intros o l IHl r IHr. cbn [atomic_tree_b atomic_tree].
    rewrite Bool.andb_true_iff, IHl, IHr. reflexivity.
  - intros o e IHe. cbn [atomic_tree_b atomic_tree]. exact IHe.
  - intros sa IHsa. cbn [atomic_atom_b atomic_atom].
    rewrite !Bool.andb_true_iff, Bool.orb_true_iff, !Bool.negb_true_iff, IHsa. tauto.
  - intros v. cbn [atomic_atom_b atomic_atom]. split; [ reflexivity | reflexivity ].
  - intros i. cbn [atomic_satom_b atomic_satom]. split; [ intros _; exact I | reflexivity ].
  - intros z. cbn [atomic_satom_b atomic_satom]. split; [ intros _; exact I | reflexivity ].
  - intros hz. cbn [atomic_satom_b atomic_satom]. split; [ intros _; exact I | reflexivity ].
  - intros r. cbn [atomic_satom_b atomic_satom]. split; [ intros _; exact I | reflexivity ].
  - intros a IHa f. cbn [atomic_satom_b atomic_satom]. exact IHa.
  - intros a IHa i IHi. cbn [atomic_satom_b atomic_satom].
    rewrite Bool.andb_true_iff, IHa, IHi. reflexivity.
  - intros a IHa lo IHlo hi IHhi. cbn [atomic_satom_b atomic_satom].
    rewrite !Bool.andb_true_iff, IHa, IHlo, IHhi. tauto.
  - intros a IHa args IHargs. cbn [atomic_satom_b atomic_satom].
    rewrite Bool.andb_true_iff, IHa, IHargs. reflexivity.
  - cbn [atomic_arglist_b atomic_arglist]. split; [ intros _; exact I | reflexivity ].
  - intros e IHe l IHl. cbn [atomic_arglist_b atomic_arglist].
    rewrite Bool.andb_true_iff, IHe, IHl. reflexivity.
Qed.

(** [atomic_tree] carries the rule-2 composite-no-spine restriction.  The round-trip theorem
    [print_parse_expr] takes it as a premise — but [build_atom] (below) DECIDES it via [atomic_tree_b] and
    rejects any atom failing it, so the premise is ENFORCED at the recovery boundary, not assumed of go.ml. *)
(** [wf] is vacuous (the round-trip uses only [atomic_tree]); discharged trivially. *)
Lemma wf_always : forall e, wf e.
Proof. induction e as [ a | o l IHl r IHr | o e IHe ]; cbn; [ exact I | split; assumption | exact IHe ]. Qed.
(** A SCANNED atom's text is [atomic] (quote-aware) — the round-trip's only [EAtom] side-condition. *)
Lemma atom_scanned_atomic : forall s, atom_scanned s = true -> atomic (atom_str s) = true.
Proof. intros [ sa | v ] H; [ apply satom_atomic | discriminate H ]. Qed.

(** A [rest] at which BOTH [parse_climb k] and [scan_atom] stop cleanly: empty, ")"-led, or led by an
    operator binding LOOSER than [k] (precedence [< k]). *)
Definition tail_ok (k : nat) (rest : string) : Prop :=
  rest = EmptyString
  \/ (exists c rs, rest = String c rs /\ orb (is_bclose c) (Ascii.eqb c (ch 58)) = true)
  \/ (exists o s1, op_match rest = Some (o, s1) /\ binop_prec o < k)
  \/ (exists rs, rest = String (ch 44) rs).   (* a depth-0 COMMA stops the parse — the arg-list separator
                                                  (review #8 P0-1b: the lexer now halts at it, so an arg's
                                                  comma tail is a clean stopping seam, like ")"). *)

Lemma is_close_not_space : forall c, is_close c = true -> is_space c = false.
Proof. intros c H. unfold is_close in H. apply Ascii.eqb_eq in H. subst c. reflexivity. Qed.

Lemma leb_false_of_lt : forall a b, a < b -> Nat.leb b a = false.
Proof. intros a b H. destruct (Nat.leb b a) eqn:E; [ apply Nat.leb_le in E; lia | reflexivity ]. Qed.

Lemma tail_ok_mono : forall k k' rest, tail_ok k rest -> k <= k' -> tail_ok k' rest.
Proof.
  intros k k' rest H Hle. destruct H as [ He | [ Hc | [ [ o [ s1 [ Hop Hp ] ] ] | Hcomma ] ] ].
  - left; exact He.
  - right; left; exact Hc.
  - right; right; left. exists o, s1. split; [ exact Hop | lia ].
  - right; right; right. exact Hcomma.
Qed.

Lemma tail_ok_good_seam : forall k rest, tail_ok k rest -> good_seam rest = true.
Proof.
  intros k rest H. destruct H as [ He | [ Hc | [ [ o [ s1 [ Hop Hp ] ] ] | Hcomma ] ] ].
  - subst rest; reflexivity.
  - destruct Hc as [ c [ rs [ Hr Hcl ] ] ]. subst rest. unfold good_seam.
    apply orb_true_iff in Hcl. apply orb_true_iff. left. apply orb_true_iff. destruct Hcl as [ Hbc | Hco ];
      [ left; apply orb_true_iff; right; exact Hbc | right; exact Hco ].
  - destruct rest as [ | c rs ]; [ discriminate Hop | ]. unfold good_seam, opens. rewrite Hop. reflexivity.
  - destruct Hcomma as [ rs Hr ]. subst rest. unfold good_seam. apply orb_true_iff. right. reflexivity.
Qed.

Lemma tail_ok_climb_stop : forall k rest F l, tail_ok k rest -> parse_climb (S F) k l rest = Some (l, rest).
Proof.
  intros k rest F l H. rewrite parse_climb_S.
  destruct H as [ He | [ Hc | [ [ o [ s1 [ Hop Hp ] ] ] | Hcomma ] ] ].
  - subst rest; reflexivity.
  - destruct Hc as [ c [ rs [ Hr Hcl ] ] ]. subst rest.
    assert (Hns : is_space c = false).
    { apply orb_true_iff in Hcl. destruct Hcl as [ Hbc | Hco ];
        [ apply bclose_not_space; exact Hbc | apply Ascii.eqb_eq in Hco; subst c; reflexivity ]. }
    rewrite (op_match_not_space c rs Hns). reflexivity.
  - rewrite Hop, (leb_false_of_lt _ _ Hp). reflexivity.
  - destruct Hcomma as [ rs Hr ]. subst rest. rewrite (op_match_not_space (ch 44) rs eq_refl). reflexivity.
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
      - right; right; left. cbn [print_pairs]. rewrite sapp_assoc, op_match_binop.
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
(** The [UNeg] dispatch: a [-(]-led string fires the negation branch (the leading '-' is not open/quote/unop,
    and the following '(' makes the guard true), peeling to the recursive paren-primary on the operand. *)
Lemma parse_primary_negparen : forall f X, parse_primary (S f) ("-(" ++ X)%string =
  match parse_primary f ("(" ++ X)%string with
  | Some (e, s1) => Some (EUnary UNeg e, s1)
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
(** ============================================================================
    POSTFIX SPINE DECOMPOSITION (review #8) — transplant of the proven blueprint
    (scratchpad primary.v).  A scanned atom = a LEAF base operand ([SIdent] /
    [SIntLit] / [SRaw]) + a left-to-right list of postfix ops (selector / index /
    slice); [satom_str] = base ++ concat(pop ops); [parse_postfix] recovers the op
    list by its loop.  Index/slice children print at ctx 0 and round-trip via the
    main [parse_expr] (the 3-way fuel cycle), supplied per-op from the size-IH.
    ============================================================================ *)
Inductive POp : Type :=
  | OSel : Ident -> POp
  | OIdx : GoExpr -> POp
  | OSlc : GoExpr -> GoExpr -> POp
  | OApply : ArgList -> POp.

Fixpoint spine (a : SAtom) : SAtom * list POp :=
  match a with
  | SSelector a f  => let (b, ops) := spine a in (b, (ops ++ [OSel f])%list)
  | SIndex a i     => let (b, ops) := spine a in (b, (ops ++ [OIdx i])%list)
  | SSlice a lo hi => let (b, ops) := spine a in (b, (ops ++ [OSlc lo hi])%list)
  | SApply a args   => let (b, ops) := spine a in (b, (ops ++ [OApply args])%list)
  | b => (b, [])
  end.
Fixpoint applyops (a : SAtom) (ops : list POp) : SAtom :=
  match ops with
  | [] => a
  | OSel f :: r => applyops (SSelector a f) r
  | OIdx i :: r => applyops (SIndex a i) r
  | OSlc lo hi :: r => applyops (SSlice a lo hi) r
  | OApply args :: r => applyops (SApply a args) r
  end.
Definition pop (o : POp) : string :=
  match o with
  | OSel f => String (ch 46) (proj1_sig f)
  | OIdx i => String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString)
  | OSlc lo hi => String (ch 91)
      (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString))
  | OApply args => String (ch 40) (argl_str args ++ String (ch 41) EmptyString)
  end.
Fixpoint pops (ops : list POp) : string :=
  match ops with [] => EmptyString | o :: r => (pop o ++ pops r)%string end.

Lemma applyops_app : forall ops1 ops2 a, applyops a (ops1 ++ ops2)%list = applyops (applyops a ops1) ops2.
Proof.
  induction ops1 as [ | o ops1 IH ]; intros ops2 a; cbn [applyops List.app]; [ reflexivity | ].
  destruct o; rewrite IH; reflexivity.
Qed.
Lemma pops_app : forall ops1 ops2, pops (ops1 ++ ops2)%list = (pops ops1 ++ pops ops2)%string.
Proof.
  induction ops1 as [ | o ops1 IH ]; intros ops2; cbn [pops List.app]; [ reflexivity | ].
  rewrite IH, sapp_assoc. reflexivity.
Qed.
Lemma spine_correct : forall a, applyops (fst (spine a)) (snd (spine a)) = a.
Proof.
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [spine]; try reflexivity;
    (destruct (spine a) as [ b ops ] eqn:Es; cbn [fst snd] in *;
     rewrite applyops_app; cbn [applyops]; rewrite IH; reflexivity).
Qed.
Lemma print_spine : forall a, satom_str a = (satom_str (fst (spine a)) ++ pops (snd (spine a)))%string.
Proof.
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [spine].
  - cbn [fst snd pops]. rewrite sapp_nil_r; reflexivity.
  - cbn [fst snd pops]. rewrite sapp_nil_r; reflexivity.
  - cbn [fst snd pops]. rewrite sapp_nil_r; reflexivity.
  - cbn [fst snd pops]. rewrite sapp_nil_r; reflexivity.
  - change (satom_str (SSelector a f)) with (satom_str a ++ String (ch 46) (proj1_sig f))%string.
    destruct (spine a) as [ b ops ] eqn:Es; cbn [fst snd] in *.
    rewrite pops_app; cbn [pops pop]; rewrite sapp_nil_r, IH, sapp_assoc; reflexivity.
  - change (satom_str (SIndex a i))
      with (satom_str a ++ String (ch 91) (print_expr 0 i ++ String (ch 93) EmptyString))%string.
    destruct (spine a) as [ b ops ] eqn:Es; cbn [fst snd] in *.
    rewrite pops_app; cbn [pops pop]; rewrite sapp_nil_r, IH, sapp_assoc; reflexivity.
  - change (satom_str (SSlice a lo hi))
      with (satom_str a ++ String (ch 91)
              (print_expr 0 lo ++ String (ch 58) (print_expr 0 hi ++ String (ch 93) EmptyString)))%string.
    destruct (spine a) as [ b ops ] eqn:Es; cbn [fst snd] in *.
    rewrite pops_app; cbn [pops pop]; rewrite sapp_nil_r, IH, sapp_assoc; reflexivity.
  - change (satom_str (SApply a args))
      with (satom_str a ++ String (ch 40) (argl_str args ++ String (ch 41) EmptyString))%string.
    destruct (spine a) as [ b ops ] eqn:Es; cbn [fst snd] in *.
    rewrite pops_app; cbn [pops pop]; rewrite sapp_nil_r, IH, sapp_assoc; reflexivity.
Qed.

(** [opsz] — the [parse_postfix] fuel an op list needs: 1 per op + [3*esize] per expr child. *)
Fixpoint opsz (ops : list POp) : nat :=
  match ops with
  | [] => 0
  | OSel _ :: r => S (opsz r)
  | OIdx i :: r => S (S (S (3 * esize i + opsz r)))         (* +3: [Pexpr] child needs [3*esize+2 < fuel] *)
  | OSlc lo hi :: r => S (S (S (3 * esize lo + 3 * esize hi + opsz r)))
  | OApply args :: r => S (S (S (S (3 * argl_size args + opsz r))))   (* +4: [parse_args] needs [3*argl_size+4] fuel *)
  end.
Lemma opsz_app : forall a b, opsz (a ++ b)%list = opsz a + opsz b.
Proof.
  induction a as [ | x a IH ]; intro b; cbn [List.app opsz]; [ reflexivity | ].
  destruct x; cbn [opsz]; rewrite IH; lia.
Qed.
Lemma spine_fuel_a : forall a, opsz (snd (spine a)) + 3 <= 3 * asize a.
Proof.
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [spine asize].
  - cbn [snd opsz]. lia.
  - cbn [snd opsz]. lia.
  - cbn [snd opsz]. lia.
  - cbn [snd opsz]. lia.
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. rewrite opsz_app. cbn [opsz]. lia.
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. rewrite opsz_app. cbn [opsz]. lia.
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. rewrite opsz_app. cbn [opsz]. lia.
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. rewrite opsz_app. cbn [opsz]. lia.
Qed.

(** [scan_field] recovers a maximal all-[is_idc] run: a [go_ident]-derived field followed by a non-[is_idc]
    char (a '.' / '[' postfix-start or a delimiter) is read back exactly.  Selector-field analog of the
    blueprint's [scan_ident_app]. *)
Lemma scan_field_app : forall s rest, all_idc s = true ->
  (rest = EmptyString \/ exists c r, rest = String c r /\ is_idc c = false) ->
  scan_field (s ++ rest)%string = (s, rest).
Proof.
  induction s as [ | c s IH ]; intros rest Hall Hrest; cbn [String.append].
  - destruct Hrest as [ -> | [ rc [ r [ -> Hc ] ] ] ]; cbn [scan_field]; [ reflexivity | rewrite Hc; reflexivity ].
  - cbn [all_idc] in Hall. apply andb_true_iff in Hall. destruct Hall as [ Hc Hall ].
    cbn [scan_field]. rewrite Hc, (IH rest Hall Hrest). reflexivity.
Qed.
(** [Ident] proof-irrelevance: the parser rebuilds [exist _ s Hf] from the scanned field; it equals the
    original [Ident] because [go_ident s = true] has a UNIQUE proof (UIP on a decidable bool equality). *)
Lemma Ident_pi : forall (s : string) (H1 H2 : go_ident s = true),
  exist (fun s => go_ident s = true) s H1 = exist _ s H2.
Proof. intros s H1 H2. f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec). Qed.

(** Every argument of a call round-trips ([Pexpr]) — the per-arg obligation [parse_args] discharges. *)
Fixpoint argl_wf (l : ArgList) : Prop :=
  match l with ANil => True | ACons e r => Pexpr e /\ argl_wf r end.
(** The per-op round-trip obligation: an index/slice child round-trips as an expression ([Pexpr], supplied
    from the size-IH); a call's arguments each round-trip ([argl_wf]); a selector field needs nothing extra
    (its [go_ident] proof rides in the [Ident]). *)
Definition opwf (o : POp) : Prop :=
  match o with
  | OSel _ => True | OIdx i => Pexpr i | OSlc lo hi => Pexpr lo /\ Pexpr hi
  | OApply args => argl_wf args
  end.
(** The tail after the whole postfix spine: empty, or led by a char that is NOT [is_idc] (so a trailing
    selector field's [scan_field] stops) and NOT '.'/'['/'(' (so [parse_postfix] stops — incl. the call
    postfix, review #8 P0-1b: a '(' after the spine would otherwise be read as a continuation). *)
Definition post_tail (rest : string) : Prop :=
  forall c t, rest = String c t ->
    is_idc c = false /\ Ascii.eqb c (ch 46) = false /\ Ascii.eqb c (ch 91) = false /\ Ascii.eqb c (ch 40) = false.

(** The head of [pops ops ++ rest] is empty or non-[is_idc] — a pop-start '.'/'[' (non-idc) or a [post_tail]
    char — so a selector field's [scan_field] stops at it. *)
Lemma pops_rest_nonidc : forall ops rest, post_tail rest ->
  (pops ops ++ rest)%string = EmptyString \/
  exists c r, (pops ops ++ rest)%string = String c r /\ is_idc c = false.
Proof.
  intros ops rest Hr. destruct ops as [ | o ops' ].
  - cbn [pops]. cbn [String.append]. destruct rest as [ | c t ]; [ now left | right ].
    exists c, t. split; [ reflexivity | exact (proj1 (Hr c t eq_refl)) ].
  - right. cbn [pops]. destruct o as [ f | i | lo hi | args ]; cbn [pop String.append];
      eexists _, _; split; reflexivity.
Qed.

(** A ')'-led string is never bracket-balanced from the empty stack (')' pops nothing). *)
Lemma bstack_close_nil_false : forall r', bstack_ok nil (String (ch 41) r')%string = false.
Proof.
  intro r'. rewrite bstack_ok_cons. unfold opens.
  rewrite (op_match_not_space (ch 41) r' eq_refl). reflexivity.
Qed.
(** Hence an [atomic] string is never ')'-led. *)
Lemma atomic_not_close_led : forall c r', atomic (String c r')%string = true -> Ascii.eqb c (ch 41) = false.
Proof.
  intros c r' H. destruct (Ascii.eqb c (ch 41)) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E. subst c.
  destruct (atomic_inv _ H) as [ c0 [ r0 [ _ [ _ Hb ] ] ] ].
  rewrite bstack_close_nil_false in Hb. discriminate Hb.
Qed.
(** No printed expression is ')'-led: its first char is an atom lead (never ')' — [atomic]), a "(" wrap, or
    a unary op — checked by structural induction (the binop left spine recurses, atoms via [satom_atomic]). *)
Lemma print_expr_first : forall e ctx,
  exists c r, print_expr ctx e = String c r /\ Ascii.eqb c (ch 41) = false.
Proof.
  induction e as [ a | o l IHl r IHr | op e IHe ]; intro ctx.
  - rewrite print_expr_atom. destruct a as [ sa | v ].
    + change (atom_str (AScanned sa)) with (satom_str sa).
      pose proof (satom_atomic sa) as Hat.
      destruct (satom_str sa) as [ | c r ] eqn:E; [ exfalso; apply (satom_nonempty sa); exact E | ].
      exists c, r. split; [ reflexivity | apply (atomic_not_close_led c r); exact Hat ].
    + change (atom_str (AStringLit v)) with (print_string_lit v).
      unfold print_string_lit. eexists _, _; split; reflexivity.
  - destruct (Nat.ltb (binop_prec o) ctx) eqn:Ew.
    + rewrite (print_expr_wrapped o l r ctx Ew). eexists _, _; split; reflexivity.
    + rewrite (print_expr_unwrapped o l r ctx Ew).
      destruct (IHl (binop_prec o)) as [ c [ rr [ Hl Hc ] ] ]. rewrite Hl. cbn [String.append].
      eexists _, _; split; [ reflexivity | exact Hc ].
  - destruct op;
      [ rewrite (print_expr_unary UNot e ctx ltac:(discriminate))
      | rewrite (print_expr_unary UXor e ctx ltac:(discriminate))
      | rewrite (print_expr_unary UDeref e ctx ltac:(discriminate))
      | rewrite (print_expr_unary UAddr e ctx ltac:(discriminate))
      | rewrite (print_expr_uneg e ctx) ];
      cbn [unop_text String.append]; eexists _, _; split; reflexivity.
Qed.
(** A non-empty arg list is never ')'-led — it begins with its first argument's print ([print_expr_first]). *)
Lemma argl_str_first : forall args, args <> ANil ->
  exists c r, argl_str args = String c r /\ Ascii.eqb c (ch 41) = false.
Proof.
  intros [ | e rest ] Hne; [ exfalso; apply Hne; reflexivity | ].
  destruct (print_expr_first e 0) as [ c [ r [ He Hc ] ] ].
  destruct rest as [ | e2 rest' ].
  - cbn [argl_str]. rewrite He. exists c, r. split; [ reflexivity | exact Hc ].
  - change (argl_str (ACons e (ACons e2 rest')))
      with (print_expr 0 e ++ String (ch 44) (String (ch 32) (argl_str (ACons e2 rest'))))%string.
    rewrite He. cbn [String.append]. eexists _, _; split; [ reflexivity | exact Hc ].
Qed.

(** ★THE ARG-LIST ROUND-TRIP (review #8 P0-1b): the MUTUAL [parse_args] (in the [parse_expr] fuel cycle)
    recovers the EXACT [ArgList] from [argl_str args] followed by the closing ")".  Each arg round-trips by
    [Pexpr] (carried in [argl_wf]); its tail is a clean stopping seam — ", " (the [tail_ok] COMMA disjunct)
    for a non-last arg, ")" (a [bclose]) for the last.  Fuel [3*argl_size args + 4] feeds each
    [parse_expr f 0] the [3*esize e + 3] it needs.  Caller handles the empty "()" (no [parse_args] call). *)
Lemma parse_args_roundtrip_mut : forall args tail fuel,
  argl_wf args -> 3 * argl_size args + 4 <= fuel ->
  parse_args fuel (argl_str args ++ String (ch 41) tail)%string
    = Some (args, String (ch 41) tail).
Proof.
  induction args as [ | e rest IH ]; intros tail fuel Hwf Hsz.
  - (* ANil: "" ++ ")"tail = ")"tail — the leading ')' check fires, returns [ANil] *)
    destruct fuel as [ | f ]; [ cbn in Hsz; lia | ].
    rewrite parse_args_S. cbn [argl_str String.append]. rewrite Ascii.eqb_refl. reflexivity.
  - destruct Hwf as [ HPe Hwfr ].
    destruct fuel as [ | f ]; [ cbn in Hsz; lia | ].
    rewrite parse_args_S.
    (* the printed arg list is NOT ')'-led — expose its first char in the SCRUTINEE only ([at 1]), so the
       [parse_expr] argument keeps its [argl_str] head (no [cbn] merge), ready for [HPe]. *)
    destruct (argl_str_first (ACons e rest) ltac:(discriminate)) as [ c0 [ r0 [ Hf0 Hc0 ] ] ].
    rewrite Hf0 at 1. cbn [String.append]. rewrite Hc0.
    destruct rest as [ | e2 rest' ].
    + (* single arg: [argl_str (ACons e ANil) = print_expr 0 e]; tail ")" is a bclose seam *)
      cbn [argl_str]. cbn [argl_size] in Hsz.
      rewrite (HPe 0 0 (String (ch 41) tail) f (le_n 0)
                 ltac:(right; left; exists (ch 41), tail; split; reflexivity)
                 ltac:(lia)).
      destruct tail as [ | tc tt ]; reflexivity.
    + (* multi: first arg's tail is ", " — a comma seam — then recurse on the rest *)
      change (argl_str (ACons e (ACons e2 rest')))
        with (print_expr 0 e ++ String (ch 44) (String (ch 32) (argl_str (ACons e2 rest'))))%string.
      rewrite sapp_assoc. cbn [argl_size] in Hsz.
      rewrite (HPe 0 0 (String (ch 44) (String (ch 32) (argl_str (ACons e2 rest'))) ++ String (ch 41) tail)%string
                 f (le_n 0)
                 ltac:(right; right; right; eexists; reflexivity)
                 ltac:(lia)).
      cbn [String.append andb Ascii.eqb].
      rewrite (IH tail f Hwfr ltac:(cbn [argl_size]; lia)). reflexivity.
Qed.

(** THE POSTFIX SPINE ROUND-TRIP (transplant of blueprint [ppost_ops]): [parse_postfix] recovers the op
    list left-to-right — selector via [scan_field_app] + [Ident_pi], index/slice children via [Pexpr] (the
    3-way fuel cycle), call args via [parse_args_roundtrip_mut], stopping at the [post_tail]. *)
Lemma ppost_ops : forall ops base rest fuel,
  Forall opwf ops -> opsz ops < fuel -> post_tail rest ->
  parse_postfix fuel base (pops ops ++ rest)%string
    = Some (EAtom (AScanned (applyops base ops)), rest).
Proof.
  induction ops as [ | o ops IH ]; intros base rest fuel HF Hsz Hr.
  - cbn [pops]. cbn [String.append]. destruct fuel as [ | f ]; [ cbn in Hsz; lia | ].
    rewrite parse_postfix_S. destruct rest as [ | c t ]; [ reflexivity | ].
    destruct (Hr c t eq_refl) as [ _ [ Hdot [ Hlb Hlp ] ] ]. rewrite Hdot, Hlb, Hlp. reflexivity.
  - inversion HF as [ | o0 ops0 Ho HFr ]; subst.
    destruct fuel as [ | f ]; [ cbn in Hsz; lia | ].
    cbn [pops]. rewrite sapp_assoc. rewrite parse_postfix_S.
    destruct o as [ g | i | lo hi | args ]; cbn [pop opsz] in *.
    + (* OSel g : ".field" *)
      cbn [String.append]. rewrite Ascii.eqb_refl.
      rewrite (scan_field_app (proj1_sig g) (pops ops ++ rest)
                 (go_ident_all_idc _ (proj2_sig g)) (pops_rest_nonidc ops rest Hr)).
      destruct (bool_dec (go_ident (proj1_sig g)) true) as [ Hf | Hcontra ];
        [ | exfalso; apply Hcontra; exact (proj2_sig g) ].
      assert (Hg : exist (fun s => go_ident s = true) (proj1_sig g) Hf = g)
        by (destruct g as [ gs gH ]; cbn [proj1_sig]; apply Ident_pi).
      rewrite Hg. apply (IH (SSelector base g) rest f HFr); [ lia | exact Hr ].
    + (* OIdx i : "[print i]" *)
      cbn [String.append]. rewrite sapp_assoc. cbn [String.append].
      assert (Hlb_dot : Ascii.eqb (ch 91) (ch 46) = false) by reflexivity.
      rewrite Hlb_dot, Ascii.eqb_refl.
      rewrite (Ho 0 0 (String (ch 93) (pops ops ++ rest)) f (le_n 0)
                 ltac:(right; left; exists (ch 93), (pops ops ++ rest); split; reflexivity)
                 ltac:(lia)).
      rewrite Ascii.eqb_refl. apply (IH (SIndex base i) rest f HFr); [ lia | exact Hr ].
    + (* OSlc lo hi : "[print lo : print hi]" *)
      destruct Ho as [ Hlo Hhi ].
      cbn [String.append]. rewrite sapp_assoc. cbn [String.append]. rewrite sapp_assoc. cbn [String.append].
      assert (Hlb_dot : Ascii.eqb (ch 91) (ch 46) = false) by reflexivity.
      rewrite Hlb_dot, Ascii.eqb_refl.
      rewrite (Hlo 0 0 (String (ch 58) (print_expr 0 hi ++ String (ch 93) (pops ops ++ rest))) f (le_n 0)
                 ltac:(right; left; eexists _, _; split; reflexivity)
                 ltac:(lia)).
      assert (Hcln_rb : Ascii.eqb (ch 58) (ch 93) = false) by reflexivity.
      rewrite Hcln_rb, Ascii.eqb_refl.
      rewrite (Hhi 0 0 (String (ch 93) (pops ops ++ rest)) f (le_n 0)
                 ltac:(right; left; exists (ch 93), (pops ops ++ rest); split; reflexivity)
                 ltac:(lia)).
      rewrite Ascii.eqb_refl. apply (IH (SSlice base lo hi) rest f HFr); [ lia | exact Hr ].
    + (* OApply args : "(" args ")" — [parse_args_roundtrip_mut] recovers the whole list, then the spine continues *)
      cbn [String.append].
      assert (Hd1 : Ascii.eqb (ch 40) (ch 46) = false) by reflexivity.
      assert (Hd2 : Ascii.eqb (ch 40) (ch 91) = false) by reflexivity.
      rewrite Hd1, Hd2, Ascii.eqb_refl.
      rewrite sapp_assoc. cbn [String.append].
      rewrite (parse_args_roundtrip_mut args (pops ops ++ rest) f Ho ltac:(lia)).
      apply (IH (SApply base args) rest f HFr); [ lia | exact Hr ].
Qed.

(** [exist] proof-irrelevance over any decidable-bool predicate (UIP on a [bool] equality). *)
Lemma sig_pi : forall (P : string -> bool) (s : string) (H1 H2 : P s = true),
  exist (fun s => P s = true) s H1 = exist _ s H2.
Proof. intros P s H1 H2. f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec). Qed.
Lemma sig_eta_pi : forall (P : string -> bool) (i : { s | P s = true }) (H : P (proj1_sig i) = true),
  exist (fun s => P s = true) (proj1_sig i) H = i.
Proof. intros P [ s Hs ] H; cbn [proj1_sig]. apply sig_pi. Qed.
(** ---- HEX-INT RECOGNITION (review #9 A2) ---- [print_hex] is "0x"+hex-DIGITS, so it is [is_hexint] and is
    NOT [go_ident]/[is_dec]; and the value round-trips via [parse_hex] (0<=z). *)
Lemma hexdig_is_hex_digit : forall n, (n < 16)%nat -> is_hex_digit (hexdig n) = true.
Proof. intros n H. do 16 (destruct n as [ | n ]; [ vm_compute; reflexivity | ]); lia. Qed.
Lemma hex_digits_all_hex_digit : forall fuel z acc,
  all_hex_digit acc = true -> all_hex_digit (hex_digits fuel z acc) = true.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hacc; cbn [hex_digits]; [ exact Hacc | ].
  assert (Hd : is_hex_digit (hexdig (Z.to_nat (z mod 16))) = true) by (apply hexdig_is_hex_digit, zmod16_lt16).
  destruct (z / 16 =? 0)%Z.
  - cbn [all_hex_digit]. apply andb_true_iff. split; [ exact Hd | exact Hacc ].
  - apply IH. cbn [all_hex_digit]. apply andb_true_iff. split; [ exact Hd | exact Hacc ].
Qed.
Lemma print_hex_is_hexint : forall z, is_hexint (print_hex z) = true.
Proof.
  intro z. unfold print_hex. destruct (z =? 0)%Z; [ reflexivity | ].
  cbn [String.append is_hexint]. apply andb_true_iff; split; [ reflexivity | ].
  apply (hex_digits_all_hex_digit (digit_fuel z) z "" eq_refl).
Qed.
Lemma print_hex_not_is_dec : forall z, is_dec (print_hex z) = false.
Proof. intro z. unfold print_hex. destruct (z =? 0)%Z; reflexivity. Qed.
Lemma print_hex_not_go_ident : forall z, go_ident (print_hex z) = false.
Proof. intro z. unfold print_hex. destruct (z =? 0)%Z; reflexivity. Qed.
Lemma print_hex_to_N : forall n, Z.to_N (parse_hex (print_hex (Z.of_N n))) = n.
Proof. intro n. rewrite (print_parse_hex (Z.of_N n) (N2Z.is_nonneg n)). apply N2Z.id. Qed.
Lemma raw_ok_not_hexint : forall s, raw_ok s = true -> is_hexint s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H. destruct H as [ Hw _ ].
  unfold raw_wellshaped in Hw. apply andb_true_iff in Hw. destruct Hw as [ _ Hh ].
  apply negb_true_iff in Hh. exact Hh.
Qed.

(** [build_base] inverts a LEAF operand's printed text: [go_ident]→[SIdent], [is_dec]→[SIntLit] (via
    [print_parse_Z]), [is_hexint]→[SHexLit] (via [parse_hex]), else [SRaw] — the categories are disjoint. *)
Lemma build_base_correct : forall sa,
  match sa with SIdent _ => True | SIntLit _ => True | SHexLit _ => True | SRaw _ => True | _ => False end ->
  build_base (satom_str sa) = Some sa.
Proof.
  intros sa Hleaf. destruct sa as [ i | z | hz | r | a f | a i | a lo hi | a args ]; try contradiction; cbn [satom_str].
  - unfold build_base.
    destruct (bool_dec (go_ident (proj1_sig i)) true) as [ Hi | Hn ];
      [ | exfalso; apply Hn; exact (proj2_sig i) ].
    rewrite (sig_eta_pi go_ident i Hi). reflexivity.
  - unfold build_base.
    destruct (bool_dec (go_ident (print_Z z)) true) as [ Hi | Hn ];
      [ exfalso; pose proof (is_dec_not_go_ident _ (is_dec_print_Z z)) as Hng; rewrite Hng in Hi; discriminate | ].
    destruct (bool_dec (is_dec (print_Z z)) true) as [ Hd | Hnd ];
      [ | exfalso; apply Hnd; apply is_dec_print_Z ].
    rewrite (print_parse_Z z). reflexivity.
  - (* SHexLit hz : print_hex (Z.of_N hz) → is_hexint → SHexLit (Z.to_N (parse_hex …)) = SHexLit hz *)
    unfold build_base.
    destruct (bool_dec (go_ident (print_hex (Z.of_N hz))) true) as [ Hi | _ ];
      [ exfalso; rewrite print_hex_not_go_ident in Hi; discriminate | ].
    destruct (bool_dec (is_dec (print_hex (Z.of_N hz))) true) as [ Hd | _ ];
      [ exfalso; rewrite print_hex_not_is_dec in Hd; discriminate | ].
    destruct (bool_dec (is_hexint (print_hex (Z.of_N hz))) true) as [ _ | Hx ];
      [ | exfalso; apply Hx; apply print_hex_is_hexint ].
    rewrite print_hex_to_N. reflexivity.
  - unfold build_base.
    destruct (bool_dec (go_ident (proj1_sig r)) true) as [ Hi | Hn ];
      [ exfalso; pose proof (raw_ok_not_ident _ (proj2_sig r)) as Hng; rewrite Hng in Hi; discriminate | ].
    destruct (bool_dec (is_dec (proj1_sig r)) true) as [ Hd | Hnd ];
      [ exfalso; pose proof (raw_ok_not_dec _ (proj2_sig r)) as Hng; rewrite Hng in Hd; discriminate | ].
    destruct (bool_dec (is_hexint (proj1_sig r)) true) as [ Hx | Hnx ];
      [ exfalso; pose proof (raw_ok_not_hexint _ (proj2_sig r)) as Hng; rewrite Hng in Hx; discriminate | ].
    destruct (bool_dec (raw_ok (proj1_sig r)) true) as [ Hr | Hnr ];
      [ | exfalso; apply Hnr; exact (proj2_sig r) ].
    rewrite (sig_eta_pi raw_ok r Hr). reflexivity.
Qed.

(** The base of every atom's spine is a LEAF operand ([SIdent]/[SIntLit]/[SRaw]) — [build_base]'s domain. *)
Lemma spine_base_leaf : forall a,
  match fst (spine a) with SIdent _ => True | SIntLit _ => True | SHexLit _ => True | SRaw _ => True | _ => False end.
Proof.
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [spine].
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct (spine a) as [ b ops ]; cbn [fst] in *; exact IH.
  - destruct (spine a) as [ b ops ]; cbn [fst] in *; exact IH.
  - destruct (spine a) as [ b ops ]; cbn [fst] in *; exact IH.
  - destruct (spine a) as [ b ops ]; cbn [fst] in *; exact IH.
Qed.

(** [op_clean fuel d s] — [s] scans (from bracket depth [d]) to depth 0 with NO depth-0 postfix-start
    ('.'/'['), quote-aware, matching [scan_rest]'s tracking EXACTLY (a depth-0 close bracket STOPS [scan_rest],
    so [op_clean] rejects it).  Characterizes a LEAF operand that [scan_rest] reads exactly. *)
Fixpoint op_clean (fuel d : nat) (s : string) : bool :=
  match s with
  | EmptyString => Nat.eqb d 0
  | String c s' =>
    match fuel with
    | O => false
    | S f =>
        if Ascii.eqb c (ch 34) then
          match scan_strlit_body s' with Some (_, rest) => op_clean f d rest | None => false end
        else if andb (Nat.eqb d 0) (is_postfix_start c) then false
        else if is_bopen c then op_clean f (S d) s'
        else if is_bclose c then (match d with S d' => op_clean f d' s' | O => false end)
        else op_clean f d s'
    end
  end.
Lemma scan_rest_S : forall f d s, scan_rest (S f) d s =
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c s' =>
      if Ascii.eqb c (ch 34) then
        match scan_strlit_body s' with
        | Some (body, rest) => let (a, r) := scan_rest f d rest in (String c (body ++ String (ch 34) a), r)
        | None => (EmptyString, s) end
      else if andb (Nat.eqb d 0) (is_postfix_start c) then (EmptyString, s)
      else if is_bopen c then let (a, r) := scan_rest f (S d) s' in (String c a, r)
      else if is_bclose c then
        (match d with S d' => let (a, r) := scan_rest f d' s' in (String c a, r) | O => (EmptyString, s) end)
      else let (a, r) := scan_rest f d s' in (String c a, r)
  end.
Proof. reflexivity. Qed.

(** A postfix-start char is never a dquote (it is '.' / '[' / '('). *)
Lemma postfix_start_not_quote : forall c, is_postfix_start c = true -> Ascii.eqb c (ch 34) = false.
Proof.
  intros c H. unfold is_postfix_start in H. apply orb_true_iff in H.
  destruct H as [ H | H ]; [ apply orb_true_iff in H; destruct H as [ H | H ] | ];
    apply Ascii.eqb_eq in H; subst c; reflexivity.
Qed.

(** [scan_rest] reads an [op_clean] operand EXACTLY, stopping at the [is_postfix_start]-led (or empty) tail
    — the operand-recovery analog of [scan_atom_gen].  Induction on [fuel]; the quote case bridges via
    [scan_strlit_body_app]/[scan_strlit_body_split_n]. *)
Lemma scan_rest_stop : forall sf rest,
  (rest = EmptyString \/ exists c t, rest = String c t /\ is_postfix_start c = true) ->
  String.length rest <= sf -> scan_rest sf 0 rest = (EmptyString, rest).
Proof.
  intros sf rest Hrest Hlen. destruct Hrest as [ -> | [ rc [ rt [ -> Hps ] ] ] ].
  - destruct sf; reflexivity.
  - cbn [String.length] in Hlen. destruct sf as [ | f ]; [ lia | ].
    rewrite scan_rest_S, (postfix_start_not_quote rc Hps). cbn [Nat.eqb]. rewrite Hps. cbn [andb]. reflexivity.
Qed.
Lemma scan_rest_clean : forall fuel s d rest, op_clean fuel d s = true ->
  (rest = EmptyString \/ exists c t, rest = String c t /\ is_postfix_start c = true) ->
  scan_rest (fuel + String.length rest) d (s ++ rest)%string = (s, rest).
Proof.
  induction fuel as [ | f IH ]; intros s d rest Hc Hrest; destruct s as [ | c s' ].
  - cbn [op_clean] in Hc. apply Nat.eqb_eq in Hc; subst d.
    cbn [String.append Nat.add]. apply scan_rest_stop; [ exact Hrest | lia ].
  - discriminate Hc.
  - cbn [op_clean] in Hc. apply Nat.eqb_eq in Hc; subst d.
    cbn [String.append]. apply scan_rest_stop; [ exact Hrest | cbn [Nat.add String.length]; lia ].
  - cbn [op_clean] in Hc. cbn [String.append Nat.add]. rewrite scan_rest_S.
    destruct (Ascii.eqb c (ch 34)) eqn:Eq.
    + destruct (scan_strlit_body s') as [ [ body rlit ] | ] eqn:Esc; [ | discriminate Hc ].
      rewrite (scan_strlit_body_app (String.length s') s' body rlit rest (le_n _) Esc).
      rewrite (IH rlit d rest Hc Hrest).
      pose proof (scan_strlit_body_split_n (String.length s') s' body rlit (le_n _) Esc) as Hsp.
      rewrite <- Hsp. reflexivity.
    + destruct (andb (Nat.eqb d 0) (is_postfix_start c)) eqn:Eps; [ discriminate Hc | ].
      destruct (is_bopen c) eqn:Ebo.
      * rewrite (IH s' (S d) rest Hc Hrest). reflexivity.
      * destruct (is_bclose c) eqn:Ebc.
        -- destruct d as [ | d' ]; [ discriminate Hc | ]. rewrite (IH s' d' rest Hc Hrest). reflexivity.
        -- rewrite (IH s' d rest Hc Hrest). reflexivity.
Qed.

Lemma op_clean_S : forall f d c s', op_clean (S f) d (String c s') =
  (if Ascii.eqb c (ch 34)
   then match scan_strlit_body s' with Some (_, rest) => op_clean f d rest | None => false end
   else if andb (Nat.eqb d 0) (is_postfix_start c) then false
   else if is_bopen c then op_clean f (S d) s'
   else if is_bclose c then (match d with S d' => op_clean f d' s' | O => false end)
   else op_clean f d s').
Proof. reflexivity. Qed.

(** A "plain" operand char — not a quote / bracket / postfix-start — is read char-by-char by [scan_rest]
    (no depth change, no stop).  [SIdent] ([all_idc]) and [SIntLit] ([is_dec]) operands are all-plain. *)
Definition op_plain_char (c : ascii) : bool :=
  andb (negb (Ascii.eqb c (ch 34)))
       (andb (negb (is_bopen c)) (andb (negb (is_bclose c)) (negb (is_postfix_start c)))).
Fixpoint all_op_plain (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (op_plain_char c) (all_op_plain s') end.
Lemma all_op_plain_cons : forall c s,
  op_plain_char c = true -> all_op_plain s = true -> all_op_plain (String c s) = true.
Proof. intros c s Hc Hs. cbn [all_op_plain]. rewrite Hc, Hs. reflexivity. Qed.
Lemma op_plain_op_clean : forall s, all_op_plain s = true -> op_clean (String.length s) 0 s = true.
Proof.
  induction s as [ | c s IH ]; intro H; [ reflexivity | ].
  cbn [all_op_plain] in H. apply andb_true_iff in H. destruct H as [ Hc Hs ].
  unfold op_plain_char in Hc. apply andb_true_iff in Hc. destruct Hc as [ Hq Hc ].
  apply andb_true_iff in Hc. destruct Hc as [ Hbo Hc ]. apply andb_true_iff in Hc. destruct Hc as [ Hbc Hps ].
  apply negb_true_iff in Hq, Hbo, Hbc, Hps.
  cbn [String.length]. rewrite op_clean_S, Hq, Hps. cbn [andb Nat.eqb]. rewrite Hbo, Hbc. exact (IH Hs).
Qed.
Lemma all_idc_op_plain : forall s, all_idc s = true -> all_op_plain s = true.
Proof.
  induction s as [ | c s IH ]; intro H; [ reflexivity | ].
  cbn [all_idc] in H. apply andb_true_iff in H. destruct H as [ Hc Hs ].
  cbn [all_op_plain]. apply andb_true_iff. split; [ | apply IH; exact Hs ].
  unfold op_plain_char. destruct (is_idc_not_special c Hc) as [ Hq [ Hbo Hbc ] ]. rewrite Hq, Hbo, Hbc.
  assert (Hd46 : Ascii.eqb c (ch 46) = false) by apply (is_idc_eqb_false c 46 Hc eq_refl).
  assert (Hd91 : Ascii.eqb c (ch 91) = false) by apply (is_idc_eqb_false c 91 Hc eq_refl).
  assert (Hd40 : Ascii.eqb c (ch 40) = false) by apply (is_idc_eqb_false c 40 Hc eq_refl).
  assert (Hps : is_postfix_start c = false) by (unfold is_postfix_start; rewrite Hd46, Hd91, Hd40; reflexivity).
  rewrite Hps. reflexivity.
Qed.
Lemma is_dec_op_plain : forall s, is_dec s = true -> all_op_plain s = true.
Proof.
  intros s H. unfold is_dec in H. destruct s as [ | c rest ]; [ discriminate | ].
  destruct (Ascii.eqb c (ascii_of_nat 45)) eqn:Em.
  - destruct rest as [ | rc rr ]; [ discriminate | ]. apply Ascii.eqb_eq in Em; subst c.
    apply all_op_plain_cons; [ reflexivity | apply all_idc_op_plain; apply all_dec_all_idc; exact H ].
  - apply all_idc_op_plain; apply all_dec_all_idc; cbn [all_dec]; exact H.
Qed.

Lemma d0_break_aux_cons : forall hexf prevp instr esc d c s',
  d0_break_aux hexf prevp instr esc d (String c s') =
  (let '(instr', esc', d', found) :=
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
                           (negb (andb (andb hexf prevp) (orb (Ascii.eqb c (ch 43)) (Ascii.eqb c (ch 45)))))))))
   in let prevp' := andb (negb instr) (orb (Ascii.eqb c (ch 112)) (Ascii.eqb c (ch 80))) in
   if found then true else d0_break_aux hexf prevp' instr' esc' d' s').
Proof. reflexivity. Qed.

(** [d0_break_aux]'s in-string skip (instr=true, [esc] tracking backslash) matches [scan_strlit_body] — the
    literal is skipped (no break inside it, [instr=true]) and processing resumes at the literal's [rest]. *)
Lemma d0_break_instr_skip : forall n s' body rest hexf d, String.length s' <= n ->
  scan_strlit_body s' = Some (body, rest) ->
  d0_break_aux hexf false true false d s' = d0_break_aux hexf false false false d rest.
Proof.
  induction n as [ | n IH ]; intros s' body rest hexf d Hlen Hsc.
  - destruct s'; [ discriminate Hsc | cbn [String.length] in Hlen; lia ].
  - destruct s' as [ | c s'' ]; [ discriminate Hsc | ]. cbn [scan_strlit_body] in Hsc.
    destruct (Ascii.eqb c (ch 34)) eqn:Eq.
    + apply Ascii.eqb_eq in Eq; subst c. cbn in Hsc. injection Hsc as _ <-.
      rewrite d0_break_aux_cons. reflexivity.
    + destruct (Ascii.eqb c (ch 92)) eqn:Eb.
      * apply Ascii.eqb_eq in Eb; subst c. cbn in Hsc.
        destruct s'' as [ | c2 s3 ]; [ discriminate Hsc | ].
        destruct (scan_strlit_body s3) as [ [ b3 r3 ] | ] eqn:Es3; [ | discriminate Hsc ].
        injection Hsc as _ <-. cbn [String.length] in Hlen.
        rewrite d0_break_aux_cons. cbn -[d0_break_aux].
        rewrite d0_break_aux_cons. cbn -[d0_break_aux].
        apply (IH s3 b3 r3 hexf d ltac:(lia) Es3).
      * destruct (scan_strlit_body s'') as [ [ b2 r2 ] | ] eqn:Es2; [ | discriminate Hsc ].
        injection Hsc as _ <-. cbn [String.length] in Hlen.
        rewrite d0_break_aux_cons, Eq, Eb. cbn -[d0_break_aux]. apply (IH s'' b2 r2 hexf d ltac:(lia) Es2).
Qed.

(** [op_clean] from a [bstack_ok]-balanced, [has_d0_break]-free string: the bracket depth (count =
    [length st]) and quotes ([bstack_ok_quote]/[bstack_skip_scan] vs [op_clean]'s [scan_strlit_body], both
    skip the literal — [d0_break_instr_skip] bridges the [d0_break] side) track in lockstep, and a depth-0
    '.'/'[' (or operator) is PRECLUDED ([d0_break_aux] flags it).  The count-based core of [raw_ok→op_clean]. *)
(** [op_clean] from a BSTACK-balanced string that [scan_rest] reads WHOLE (snd = "").  The
    [snd(scan_rest)=""] hypothesis directly PRECLUDES a depth-0 postfix-start (where [scan_rest] would STOP,
    leaving a non-empty remainder) — replacing the old [d0_break]-flag argument, which no longer flags '.'/'['
    ([whole_base] now owns that disambiguation).  [bstack_ok] supplies the balance ([op_clean]'s final-depth-0
    + no bclose-underflow). *)
Lemma op_clean_of_bstack : forall fuel s st,
  String.length s <= fuel -> bstack_ok st s = true ->
  snd (scan_rest fuel (length st) s) = EmptyString ->
  op_clean fuel (length st) s = true.
Proof.
  induction fuel as [ | f IH ]; intros s st Hlen Hb Hsnd.
  - destruct s as [ | c s' ]; [ | cbn [String.length] in Hlen; lia ].
    cbn [op_clean bstack_ok] in *. destruct st; [ reflexivity | discriminate Hb ].
  - destruct s as [ | c s' ].
    + cbn [op_clean bstack_ok] in *. destruct st; [ reflexivity | discriminate Hb ].
    + cbn [String.length] in Hlen. rewrite scan_rest_S in Hsnd. rewrite op_clean_S.
      destruct (Ascii.eqb c (ch 34)) eqn:Eq.
      * apply Ascii.eqb_eq in Eq; subst c.
        rewrite bstack_ok_quote, (bstack_skip_scan (String.length s') s' st (le_n _)) in Hb.
        destruct (scan_strlit_body s') as [ [ body r ] | ] eqn:Esc; [ | discriminate Hb ].
        destruct (scan_rest f (length st) r) as [ a rr ] eqn:Esr. cbn [snd] in Hsnd.
        pose proof (scan_strlit_body_len (String.length s') s' body r (le_n _) Esc) as Hrlen.
        apply (IH r st ltac:(lia) Hb). rewrite Esr; cbn [snd]; exact Hsnd.
      * destruct (andb (Nat.eqb (length st) 0) (is_postfix_start c)) eqn:Epfx.
        -- exfalso. cbn [snd] in Hsnd. discriminate Hsnd.
        -- rewrite bstack_ok_cons, Eq in Hb.
           destruct (andb (match st with nil => true | _ => false end)
                       (orb (orb (orb (opens (String c s')) (Ascii.eqb c (ch 58)))
                                 (andb (is_space c) (op_after s')))
                            (Ascii.eqb c (ch 44)))) eqn:Eseam; [ discriminate Hb | ].
           destruct (is_bopen c) eqn:Ebo.
           ++ destruct (scan_rest f (S (length st)) s') as [ a rr ] eqn:Esr. cbn [snd] in Hsnd.
              apply (IH s' (cons (close_of c) st) ltac:(lia) Hb).
              cbn [Datatypes.length]. rewrite Esr; cbn [snd]; exact Hsnd.
           ++ destruct (is_bclose c) eqn:Ebc.
              ** destruct st as [ | top st' ]; [ discriminate Hb | ].
                 destruct (Ascii.eqb c top) eqn:Et; [ | discriminate Hb ].
                 cbn [Datatypes.length] in Hsnd.
                 destruct (scan_rest f (length st') s') as [ a rr ] eqn:Esr. cbn [snd] in Hsnd.
                 apply (IH s' st' ltac:(lia) Hb). rewrite Esr; cbn [snd]; exact Hsnd.
              ** destruct (scan_rest f (length st) s') as [ a rr ] eqn:Esr. cbn [snd] in Hsnd.
                 apply (IH s' st ltac:(lia) Hb). rewrite Esr; cbn [snd]; exact Hsnd.
Qed.

Lemma raw_ok_no_d0_break : forall s, raw_ok s = true -> has_d0_break s = false.
Proof.
  intros s H. unfold raw_ok in H. apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].  (* drop the outer [whole_base] conjunct *)
  apply andb_true_iff in H; destruct H as [ _ H ].
  apply andb_true_iff in H; destruct H as [ H _ ].
  apply andb_true_iff in H; destruct H as [ H _ ].
  apply negb_true_iff in H; exact H.
Qed.
(** [bstack_ok nil] of any scanned atom's text — from [satom_atomic] ([atomic] = [¬is_open] ∧ [bstack_ok nil]). *)
Lemma satom_bstack : forall sa, bstack_ok nil (satom_str sa) = true.
Proof.
  intro sa. pose proof (satom_atomic sa) as Hatm. unfold atomic in Hatm.
  destruct (satom_str sa) as [ | c0 r0 ]; [ discriminate Hatm | ].
  apply andb_true_iff in Hatm. destruct Hatm as [ _ Hbs ]. exact Hbs.
Qed.

(** [argl_forall P l] — [P] holds of every argument (the call analogue of [Forall] over the arg list). *)
Fixpoint argl_forall (P : GoExpr -> Prop) (l : ArgList) : Prop :=
  match l with ANil => True | ACons e r => P e /\ argl_forall P r end.
Lemma argl_forall_mono : forall (P Q : GoExpr -> Prop) l,
  (forall e, P e -> Q e) -> argl_forall P l -> argl_forall Q l.
Proof.
  induction l as [ | e r IH ]; intros Himp H; cbn [argl_forall] in *; [ exact I | ].
  destruct H as [ He Hr ]. split; [ apply Himp; exact He | apply IH; [ exact Himp | exact Hr ] ].
Qed.
Lemma argl_forall_lt_bound : forall args n, S (argl_size args) <= n -> argl_forall (fun e => esize e < n) args.
Proof.
  induction args as [ | e r IH ]; intros n Hn; [ exact I | ].
  cbn [argl_size] in Hn. cbn [argl_forall]. split; [ lia | apply IH; lia ].
Qed.
(** Build [argl_wf] (each arg [Pexpr]) from the size-IH: every arg is strictly smaller and [atomic_tree]. *)
Lemma argl_wf_build : forall args n,
  argl_forall (fun e => esize e < n) args -> atomic_arglist args ->
  (forall e', esize e' < n -> atomic_tree e' -> Pexpr e') -> argl_wf args.
Proof.
  induction args as [ | e r IH ]; intros n Hsz Hat Hsih; cbn in *; [ exact I | ].
  destruct Hsz as [ Hse Hsr ]. destruct Hat as [ Hae Har ]. split;
    [ apply Hsih; [ exact Hse | exact Hae ] | apply (IH n); assumption ].
Qed.

(** An atom's spine children are STRICTLY SMALLER than the atom (for the size-IH). *)
Lemma spine_child_size : forall a,
  Forall (fun o => match o with OSel _ => True | OIdx i => esize i < asize a
                   | OSlc lo hi => esize lo < asize a /\ esize hi < asize a
                   | OApply args => argl_forall (fun e => esize e < asize a) args end)
         (snd (spine a)).
Proof.
  assert (Hweak : forall a n, asize a <= n -> forall o,
    (match o with OSel _ => True | OIdx i => esize i < asize a
       | OSlc lo hi => esize lo < asize a /\ esize hi < asize a
       | OApply args => argl_forall (fun e => esize e < asize a) args end) ->
    (match o with OSel _ => True | OIdx i => esize i < n
       | OSlc lo hi => esize lo < n /\ esize hi < n
       | OApply args => argl_forall (fun e => esize e < n) args end)).
  { intros a n Hle o Ho. destruct o as [ g | i | lo hi | args ];
      [ exact I | lia | destruct Ho; split; lia
      | eapply argl_forall_mono; [ | exact Ho ]; intros e He; cbn beta in He |- *; lia ]. }
  induction a as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [spine asize].
  - cbn [snd]; constructor.
  - cbn [snd]; constructor.
  - cbn [snd]; constructor.
  - cbn [snd]; constructor.
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ eapply Forall_impl; [ | exact IH ]; intros o Ho; apply (Hweak a (S (asize a))); [ lia | exact Ho ]
      | apply Forall_cons; [ exact I | apply Forall_nil ] ].
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ eapply Forall_impl; [ | exact IH ]; intros o Ho; apply (Hweak a (S (asize a + esize i))); [ lia | exact Ho ]
      | apply Forall_cons; [ lia | apply Forall_nil ] ].
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ eapply Forall_impl; [ | exact IH ]; intros o Ho; apply (Hweak a (S (asize a + esize lo + esize hi))); [ lia | exact Ho ]
      | apply Forall_cons; [ split; lia | apply Forall_nil ] ].
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ eapply Forall_impl; [ | exact IH ]; intros o Ho; apply (Hweak a (S (S (asize a + argl_size args)))); [ lia | exact Ho ]
      | apply Forall_cons; [ apply argl_forall_lt_bound; lia | apply Forall_nil ] ].
Qed.
(** [sa_leaf_comp] / [sa_has_ops] vs the [spine] decomposition (the spine-free helpers compute exactly the
    [fst (spine sa)] composite-test / the [snd (spine sa) = nil] test). *)
Lemma sa_leaf_comp_spine : forall sa, sa_leaf_comp sa = is_comp_lead (satom_str (fst (spine sa))).
Proof.
  induction sa as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; cbn [sa_leaf_comp spine]; try reflexivity;
    (destruct (spine a) as [ b ops ]; cbn [fst] in *; exact IH).
Qed.
Lemma sa_has_ops_nil : forall sa, sa_has_ops sa = false -> snd (spine sa) = nil.
Proof. intros sa H. destruct sa; cbn [sa_has_ops] in H; (reflexivity || discriminate H). Qed.
(** [atomic_satom] recursively carries each index/slice CHILD's [atomic_tree] (the round-trip's side-condition
    for the children, recovered from the parent atom's [atomic_tree]). *)
Lemma atomic_satom_child : forall sa, atomic_satom sa ->
  Forall (fun o => match o with OSel _ => True | OIdx i => atomic_tree i
                   | OSlc lo hi => atomic_tree lo /\ atomic_tree hi
                   | OApply args => atomic_arglist args end) (snd (spine sa)).
Proof.
  induction sa as [ i | z | hz | r | a IH f | a IH i | a IH lo hi | a IH args ]; intro Hat; cbn [spine] in *;
    [ cbn [snd]; constructor | cbn [snd]; constructor | cbn [snd]; constructor | cbn [snd]; constructor | | | | ];
    cbn [atomic_satom] in Hat.
  - destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ apply IH; exact Hat | apply Forall_cons; [ exact I | apply Forall_nil ] ].
  - destruct Hat as [ Hata Hi ]. destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ apply IH; exact Hata | apply Forall_cons; [ exact Hi | apply Forall_nil ] ].
  - destruct Hat as [ Hata [ Hlo Hhi ] ]. destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ apply IH; exact Hata | apply Forall_cons; [ split; assumption | apply Forall_nil ] ].
  - destruct Hat as [ Hata Hargs ]. destruct (spine a) as [ b ops ]; cbn [snd] in *. apply Forall_app; split;
      [ apply IH; exact Hata | apply Forall_cons; [ exact Hargs | apply Forall_nil ] ].
Qed.
(** The per-op round-trip [Forall opwf]: a size-IH giving [Pexpr] for every strictly-smaller [atomic_tree]
    expr (the index/slice children, whose [atomic_tree] comes from [atomic_satom] via [atomic_satom_child]). *)
Lemma spine_opwf : forall sa,
  (forall e', esize e' < asize sa -> atomic_tree e' -> Pexpr e') -> atomic_satom sa ->
  Forall opwf (snd (spine sa)).
Proof.
  intros sa Hsih Hat. pose proof (spine_child_size sa) as Hcs. pose proof (atomic_satom_child sa Hat) as Hac.
  apply Forall_forall. intros o Hin. rewrite Forall_forall in Hcs, Hac.
  specialize (Hcs o Hin). specialize (Hac o Hin).
  destruct o as [ g | i | lo hi | args ]; cbn [opwf] in *.
  - exact I.
  - apply Hsih; [ exact Hcs | exact Hac ].
  - destruct Hcs as [ Hlo Hhi ]. destruct Hac as [ Halo Hahi ]. split; apply Hsih; assumption.
  - apply (argl_wf_build args (asize sa)); [ exact Hcs | exact Hac | exact Hsih ].
Qed.

(** [leading_ident] of [s ++ rest] is [leading_ident s] when [rest] is non-[is_idc]-led (or empty) — the
    leading identifier run stays within [s]. *)
Lemma leading_ident_app : forall s rest,
  (rest = EmptyString \/ exists c t, rest = String c t /\ is_idc c = false) ->
  leading_ident (s ++ rest)%string = leading_ident s.
Proof.
  induction s as [ | c s IH ]; intros rest Hrest; cbn [String.append leading_ident].
  - destruct Hrest as [ -> | [ rc [ rt [ -> Hc ] ] ] ]; cbn [leading_ident]; [ reflexivity | rewrite Hc; reflexivity ].
  - destruct (is_idc c) eqn:Eic; [ rewrite (IH rest Hrest); reflexivity | reflexivity ].
Qed.

(** [scan_base] reads an [op_clean] operand EXACTLY (it is now just [scan_rest]). *)
(** [scan_base] splits a leaf operand from its postfix spine EXACTLY.  Two cases (the [is_comp_lead]/[pops]
    disjunction): a COMPOSITE base ([is_comp_lead], from [atomic_tree]) carries NO spine ([pops = ""]) →
    [scan_base] reads it whole via [whole_base]; a NON-composite base takes the [scan_rest] branch, [op_clean]
    via [op_clean_of_bstack] (balance from [bstack_ok], whole-read from [whole_base]) → [scan_rest_clean]. *)
Lemma scan_base_correct : forall operand pops,
  operand <> EmptyString ->
  whole_base operand = true -> bstack_ok nil operand = true ->
  (pops = EmptyString \/ exists c t, pops = String c t /\ is_postfix_start c = true) ->
  (is_comp_lead operand = false \/ pops = EmptyString) ->
  scan_base (operand ++ pops)%string = (operand, pops).
Proof.
  intros operand pops Hne Hwb Hbs Hpops Hdisj.
  destruct Hdisj as [ Hnc | -> ].
  2:{ rewrite sapp_nil_r. unfold whole_base in Hwb.
      destruct (scan_base operand) as [ b r ] eqn:Esb.
      apply andb_true_iff in Hwb. destruct Hwb as [ Hb Hr ].
      apply String.eqb_eq in Hb. apply String.eqb_eq in Hr. subst b r. reflexivity. }
  (* NON-composite (is_comp_lead operand = false → not map/func/'['): scan_base = scan_rest for both *)
  apply orb_false_iff in Hnc. destruct Hnc as [ Hmapfunc Hlbm ].
  apply orb_false_iff in Hmapfunc. destruct Hmapfunc as [ Hmap Hfunc ].
  destruct operand as [ | c orest ]; [ congruence | ].
  change (Ascii.eqb c (ch 91) = false) in Hlbm.
  assert (Hpidc : pops = EmptyString \/ exists c0 t, pops = String c0 t /\ is_idc c0 = false).
  { destruct Hpops as [ -> | [ c0 [ t [ -> Hps ] ] ] ]; [ now left | right; exists c0, t; split; [ reflexivity | ] ].
    unfold is_postfix_start in Hps. apply orb_true_iff in Hps. destruct Hps as [ H | H ];
      [ apply orb_true_iff in H; destruct H as [ H | H ] | ]; apply Ascii.eqb_eq in H; subst c0; reflexivity. }
  (* scan_base reads (String c orest) via the scan_rest branch (not func/map/'[' led) *)
  assert (Hsb : scan_base (String c orest) = scan_rest (String.length (String c orest)) 0 (String c orest)).
  { unfold scan_base. rewrite Hfunc, Hmap, Hlbm. reflexivity. }
  assert (Hsr : scan_rest (String.length (String c orest)) 0 (String c orest) = (String c orest, EmptyString)).
  { unfold whole_base in Hwb. rewrite Hsb in Hwb.
    destruct (scan_rest (String.length (String c orest)) 0 (String c orest)) as [ b r ] eqn:Esr.
    apply andb_true_iff in Hwb. destruct Hwb as [ Hb Hr ].
    apply String.eqb_eq in Hb. apply String.eqb_eq in Hr. subst b r. reflexivity. }
  assert (Hoc : op_clean (String.length (String c orest)) 0 (String c orest) = true).
  { apply (op_clean_of_bstack (String.length (String c orest)) (String c orest) nil (le_n _) Hbs).
    cbn [Datatypes.length]. rewrite Hsr. reflexivity. }
  assert (Hsb2 : scan_base ((String c orest) ++ pops)%string
               = scan_rest (String.length ((String c orest) ++ pops)) 0 ((String c orest) ++ pops)).
  { unfold scan_base. rewrite (leading_ident_app (String c orest) pops Hpidc), Hfunc, Hmap.
    cbn [String.append]. rewrite Hlbm. reflexivity. }
  rewrite Hsb2, slen_app.
  exact (scan_rest_clean (String.length (String c orest)) (String c orest) 0 pops Hoc Hpops).
Qed.

(** [leading_ident] of an all-[is_idc] string is the whole string. *)
Lemma leading_ident_all_idc : forall s, all_idc s = true -> leading_ident s = s.
Proof.
  induction s as [ | c s IH ]; intro H; [ reflexivity | ].
  cbn [all_idc] in H. apply andb_true_iff in H. destruct H as [ Hc Hs ].
  cbn [leading_ident]. rewrite Hc, (IH Hs). reflexivity.
Qed.
(** A NON-composite [op_clean] operand is a WHOLE base: [scan_base] (the [scan_rest] branch) reads all of it. *)
Lemma whole_base_of_op_clean : forall s,
  op_clean (String.length s) 0 s = true -> is_comp_lead s = false -> whole_base s = true.
Proof.
  intros s Hoc Hcl. unfold is_comp_lead in Hcl. apply orb_false_iff in Hcl. destruct Hcl as [ Hmapfunc Hlb ].
  apply orb_false_iff in Hmapfunc. destruct Hmapfunc as [ Hmap Hfunc ].
  assert (Hscb : scan_base s = (s, EmptyString)).
  { assert (Hsb : scan_base s = scan_rest (String.length s) 0 s).
    { unfold scan_base. rewrite Hfunc, Hmap. destruct s as [ | c rest ]; [ reflexivity | ].
      change (Ascii.eqb c (ch 91) = false) in Hlb. rewrite Hlb. reflexivity. }
    rewrite Hsb.
    pose proof (scan_rest_clean (String.length s) s 0 EmptyString Hoc (or_introl eq_refl)) as Hc.
    rewrite sapp_nil_r, Nat.add_0_r in Hc. exact Hc. }
  unfold whole_base. rewrite Hscb. rewrite String.eqb_refl. reflexivity.
Qed.
(** A [go_ident] / [is_dec] leaf operand is NOT composite-led ('['-led nor "map"-led). *)
Lemma is_comp_lead_ident : forall s, go_ident s = true -> is_comp_lead s = false.
Proof.
  intros s H. pose proof (go_ident_all_idc s H) as Hidc. unfold is_comp_lead. apply orb_false_iff. split.
  - apply orb_false_iff. rewrite (leading_ident_all_idc s Hidc). split.
    + destruct (String.eqb s "map") eqn:E; [ apply String.eqb_eq in E; subst s; vm_compute in H; discriminate H | reflexivity ].
    + destruct (String.eqb s "func") eqn:E; [ apply String.eqb_eq in E; subst s; vm_compute in H; discriminate H | reflexivity ].
  - destruct s as [ | c rest ]; [ discriminate H | ].
    cbn [all_idc] in Hidc. apply andb_true_iff in Hidc. destruct Hidc as [ Hc _ ].
    apply (is_idc_eqb_false c 91 Hc). reflexivity.
Qed.
Lemma is_comp_lead_dec : forall s, is_dec s = true -> is_comp_lead s = false.
Proof.
  intros s H. unfold is_comp_lead. apply orb_false_iff.
  destruct s as [ | c rest ]; [ discriminate H | ]. unfold is_dec in H.
  destruct (Ascii.eqb c (ascii_of_nat 45)) eqn:Edash.
  - apply Ascii.eqb_eq in Edash. subst c. split; reflexivity.
  - apply andb_true_iff in H. destruct H as [ Hdc _ ]. split.
    + apply orb_false_iff. split.
      * cbn [leading_ident]. rewrite (is_dec_char_is_idc c Hdc).
        cbn [String.eqb]. destruct (Ascii.eqb c "m"%char) eqn:Em; [ apply Ascii.eqb_eq in Em; subst c; vm_compute in Hdc; discriminate Hdc | reflexivity ].
      * cbn [leading_ident]. rewrite (is_dec_char_is_idc c Hdc).
        cbn [String.eqb]. destruct (Ascii.eqb c "f"%char) eqn:Ef; [ apply Ascii.eqb_eq in Ef; subst c; vm_compute in Hdc; discriminate Hdc | reflexivity ].
    + apply (is_idc_eqb_false c 91 (is_dec_char_is_idc c Hdc)). reflexivity.
Qed.
(* [print_hex z] is '0'-led + all-[is_idc], so it is never a composite LEAD (not '['-led, not "map"/"func"). *)
Lemma print_hex_not_comp_lead : forall z, is_comp_lead (print_hex z) = false.
Proof.
  intro z. destruct (print_hex_head z) as [ rest Hph ].
  unfold is_comp_lead.
  rewrite (leading_ident_all_idc _ (print_hex_all_idc z)).
  rewrite Hph. reflexivity.
Qed.
(** Every LEAF operand ([SIdent]/[SIntLit]/[SRaw]) is a WHOLE base ([scan_base] reads it entirely). *)
Lemma leaf_whole_base : forall sa,
  match sa with SIdent _ => True | SIntLit _ => True | SHexLit _ => True | SRaw _ => True | _ => False end ->
  whole_base (satom_str sa) = true.
Proof.
  intros sa Hleaf. destruct sa as [ i | z | hz | r | a f | a i | a lo hi | a args ]; try contradiction; cbn [satom_str].
  - apply whole_base_of_op_clean;
      [ apply op_plain_op_clean, all_idc_op_plain, go_ident_all_idc, (proj2_sig i)
      | apply is_comp_lead_ident, (proj2_sig i) ].
  - apply whole_base_of_op_clean;
      [ apply op_plain_op_clean, is_dec_op_plain, is_dec_print_Z
      | apply is_comp_lead_dec, is_dec_print_Z ].
  - apply whole_base_of_op_clean;
      [ apply op_plain_op_clean, all_idc_op_plain, print_hex_all_idc
      | apply print_hex_not_comp_lead ].
  - pose proof (proj2_sig r) as Hraw. cbn beta in Hraw.
    unfold raw_ok in Hraw. apply andb_true_iff in Hraw. destruct Hraw as [ _ Hraw ].
    apply andb_true_iff in Hraw. destruct Hraw as [ _ Hwb ]. exact Hwb.
Qed.

(** [pops] of a non-empty op list is led by a postfix-start char ('.' / '['). *)
Lemma pops_postfix_led : forall ops,
  pops ops = EmptyString \/ exists c t, pops ops = String c t /\ is_postfix_start c = true.
Proof.
  destruct ops as [ | o ops' ]; [ left; reflexivity | right ].
  cbn [pops]. destruct o as [ f | i | lo hi | args ]; cbn [pop String.append]; eexists _, _; split; reflexivity.
Qed.

(** THE POSTFIX-ATOM ROUND-TRIP (the rewired [parse_primary] atom branch): [scan_atom] isolates the chunk,
    [scan_base] splits the leaf operand from the postfix spine, [build_base] recovers the operand,
    [ppost_ops] climbs the spine (children via the size-IH).  (NON-func-led operand for now; the func-lit
    sub-case is the remaining [scan_base] branch.) *)
Lemma parse_primary_atom : forall sa TAIL f,
  good_seam TAIL = true ->
  (forall e', esize e' < asize sa -> atomic_tree e' -> Pexpr e') ->
  3 * asize sa <= S f ->
  (is_comp_lead (satom_str (fst (spine sa))) = false \/ snd (spine sa) = nil) ->
  atomic_satom sa ->
  parse_primary (S f) (satom_str sa ++ TAIL)%string = Some (EAtom (AScanned sa), TAIL).
Proof.
  intros sa TAIL f Hgs Hsih Hfuel Hdisj Hat.
  assert (Hdisj' : is_comp_lead (satom_str (fst (spine sa))) = false \/ pops (snd (spine sa)) = EmptyString)
    by (destruct Hdisj as [ H | H ]; [ left; exact H | right; rewrite H; reflexivity ]).
  pose proof (atom_scanned_atomic (AScanned sa) eq_refl) as Hatm. cbn [atom_str] in Hatm.
  pose proof (atom_scanned_not_quote_led (AScanned sa) eq_refl) as Hqnq. cbn [atom_str] in Hqnq.
  destruct (satom_str sa) as [ | c s' ] eqn:Estr; [ cbn in Hatm; discriminate | ].
  rewrite parse_primary_S.
  assert (Hopen : is_open c = false).
  { unfold atomic in Hatm. apply andb_true_iff in Hatm. destruct Hatm as [ Hno _ ].
    apply negb_true_iff in Hno. exact Hno. }
  assert (Hq : Ascii.eqb c (ch 34) = false) by exact Hqnq.
  cbn [append]. rewrite Hopen, Hq.
  assert (Huol : is_unop_char c = false).
  { change (unary_op_led (String c s') = false). rewrite <- Estr.
    pose proof (atom_scanned_unary_op_led_false (AScanned sa) eq_refl) as HH. cbn [atom_str] in HH. exact HH. }
  rewrite Huol.
  assert (Hnp : andb (Ascii.eqb c (ch 45))
                     (match s' ++ TAIL with String c1 _ => is_open c1 | _ => false end)%string = false).
  { change (neg_paren_led (String c (s' ++ TAIL)) = false).
    change (String c (s' ++ TAIL))%string with ((String c s') ++ TAIL)%string.
    rewrite <- Estr. apply satom_not_neg_paren_app. }
  rewrite Hnp.
  assert (Hscan : scan_atom 0 ((String c s') ++ TAIL)%string = (String c s', TAIL))
    by (apply scan_atom_correct; [ exact Hatm | exact Hgs ]).
  change ((String c s') ++ TAIL)%string with (String c (s' ++ TAIL))%string in Hscan.
  rewrite Hscan.
  assert (Hsp : (String c s')%string = (satom_str (fst (spine sa)) ++ pops (snd (spine sa)))%string)
    by (rewrite <- Estr; apply print_spine).
  cbn -[scan_base build_base parse_postfix]. rewrite Hsp.
  rewrite (scan_base_correct (satom_str (fst (spine sa))) (pops (snd (spine sa)))
             (satom_nonempty (fst (spine sa)))
             (leaf_whole_base (fst (spine sa)) (spine_base_leaf sa))
             (satom_bstack (fst (spine sa)))
             (pops_postfix_led (snd (spine sa))) Hdisj').
  cbn -[build_base parse_postfix].
  rewrite (build_base_correct (fst (spine sa)) (spine_base_leaf sa)).
  cbn -[parse_postfix].
  rewrite <- (sapp_nil_r (pops (snd (spine sa)))).
  rewrite (ppost_ops (snd (spine sa)) (fst (spine sa)) EmptyString f
             (spine_opwf sa Hsih Hat) ltac:(pose proof (spine_fuel_a sa); lia)
             ltac:(intros c0 t0 Hc0; discriminate Hc0)).
  rewrite (spine_correct sa). reflexivity.
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
  - destruct base as [ s | o' l' r' | op e ]; cbn [esize] in Hn;
      [ pose proof (gsize_pos s); lia | lia | lia ].
  - destruct base as [ s | o' l' r' | op e ].
    + cbn [print_expr]. destruct F as [ | f ]; [ cbn in HF; lia | ].
      destruct s as [ sc | rs ].
      * cbn [atomic_tree atomic_atom] in Hat. destruct Hat as [ Hatm [ Hdis Hasat ] ].
        assert (Hdisj : is_comp_lead (satom_str (fst (spine sc))) = false \/ snd (spine sc) = nil)
          by (destruct Hdis as [ H | H ]; [ left; rewrite <- sa_leaf_comp_spine; exact H | right; apply sa_has_ops_nil; exact H ]).
        apply (parse_primary_atom sc TAIL f Hgs
                 ltac:(intros e' He' Ae'; apply Hsih; [ cbn [esize gsize]; exact He' | apply wf_always | exact Ae' ])
                 ltac:(cbn [esize gsize] in HF; lia) Hdisj Hasat).
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
    + (* EUnary op e — the four bare ops print [unop_text op ++ print_expr 6 e] (a recursive primary,
         dispatched by the single unary char); [UNeg] prints [-(print 0 e)] (dispatched by the [-(] prefix
         to a paren-primary on the operand). *)
      cbn [wf atomic_tree] in Hwf, Hat.
      assert (Hnu : forall oo, oo <> UNeg ->
                parse_primary F (print_expr bfl (EUnary oo e) ++ TAIL)%string = Some (EUnary oo e, TAIL)).
      { intros oo Hoo. rewrite (print_expr_unary oo e bfl Hoo).
        destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct (unop_text_char_of oo Hoo) as [ uc [ us [ Hut [ Hus [ Huc Hisu ] ] ] ] ].
        rewrite Hut, Hus. cbn [append]. rewrite parse_primary_S. cbn [append].
        rewrite (is_unop_not_open uc Hisu), (is_unop_not_quote uc Hisu), Hisu, Huc.
        rewrite (IHn e 6 TAIL f
                   ltac:(cbn [esize] in Hn; lia)
                   ltac:(intros e' He' We Ae; apply Hsih; [ cbn [esize]; lia | exact We | exact Ae ])
                   Hwf Hat
                   ltac:(apply Hsih; [ cbn [esize]; lia | exact Hwf | exact Hat ])
                   ltac:(destruct e as [ ? | o'' ? ? | ? ? ]; [ exact I | apply binop_prec_lt6 | exact I ])
                   Hgs
                   ltac:(cbn [esize] in HF; lia)).
        reflexivity. }
      destruct op; try (apply Hnu; discriminate).
      (* UNeg: "-(" ++ print_expr 0 e ++ ")" *)
      rewrite print_expr_uneg.
      destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
      destruct f as [ | f ]; [ cbn [esize] in HF; lia | ].
      rewrite sapp_assoc, parse_primary_negparen, parse_primary_paren.
      rewrite (sapp_assoc (print_expr 0 e) ")"%string TAIL).
      assert (Htl0 : tail_ok 0 (")" ++ TAIL)%string).
      { right; left. exists ")"%char, TAIL. split; [ cbn [append]; reflexivity | reflexivity ]. }
      assert (HPe : Pexpr e) by (apply Hsih; [ cbn [esize]; lia | exact Hwf | exact Hat ]).
      rewrite (HPe 0 0 (")" ++ TAIL)%string f (Nat.le_0_l _) Htl0 ltac:(cbn [esize] in HF |- *; lia)).
      cbn [append]. reflexivity.
Qed.

(** THE UNIVERSAL ROUND-TRIP — by strong induction on tree size.  [Hunwr] proves the cases where [e]
    prints UNWRAPPED at [ctx] (an atom, or an [EBin] with [ctx <= prec]); the dispatch below sends an
    atom and the unwrapped [EBin] straight to it, and a WRAPPED [EBin] (prec < ctx) — whose text is
    "(" ++ (e printed unwrapped at prec) ++ ")" — through the paren rule to [Hunwr] at the SAME [e].  No
    circularity: [Hunwr] recurses only into strictly smaller sub-trees (operands and base) via the IH. *)
Lemma print_parse_expr_n : forall n e, esize e <= n -> wf e -> atomic_tree e -> Pexpr e.
Proof.
  induction n as [ | n IH ]; intros e Hsz Hwf Hat;
    [ destruct e as [ s | | ]; cbn [esize] in Hsz; [ pose proof (gsize_pos s); lia | lia | lia ] | ].
  assert (Hunwr : forall k ctx rest F, k <= ctx -> tail_ok k rest -> 3 * esize e < F ->
            match e with EAtom _ => True | EUnary _ _ => True | EBin o _ _ => ctx <= binop_prec o end ->
            parse_expr F k (print_expr ctx e ++ rest) = Some (e, rest)).
  { intros k ctx rest F Hk Htl HF Hctx. destruct e as [ s | o l r | op e0 ].
    - (* EAtom s — split: a STRING LITERAL via [parse_primary_strlit], any other atom via [_scanned] *)
      cbn [print_expr].
      destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
      destruct f0 as [ | f1 ]; [ cbn [esize] in HF; pose proof (gsize_pos s); lia | ].
      assert (Hgs : good_seam rest = true) by (apply (tail_ok_good_seam k); exact Htl).
      assert (Hpp : parse_primary (S f1) (atom_str s ++ rest)%string = Some (EAtom s, rest)).
      { destruct s as [ sc | rs ].
        + cbn [atomic_tree atomic_atom] in Hat. destruct Hat as [ Hatm [ Hdis Hasat ] ].
          assert (Hdisj : is_comp_lead (satom_str (fst (spine sc))) = false \/ snd (spine sc) = nil)
            by (destruct Hdis as [ H | H ]; [ left; rewrite <- sa_leaf_comp_spine; exact H | right; apply sa_has_ops_nil; exact H ]).
          apply (parse_primary_atom sc rest f1 Hgs
                   ltac:(intros e' He' Ae'; apply IH; [ cbn [esize gsize] in Hsz; lia | apply wf_always | exact Ae' ])
                   ltac:(cbn [esize gsize] in HF; lia) Hdisj Hasat).
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
    - (* EUnary op e0 — a PRIMARY (NOT ctx-wrapped).  The four bare ops dispatch on the single unary char to
         [parse_primary_base] on the operand; [UNeg] prints [-(print 0 e0)], dispatched by the [-(] prefix to a
         paren-primary on [e0].  [Pexpr e0] comes from the OUTER strong IH (not circular). *)
      cbn [wf atomic_tree] in Hwf, Hat.
      assert (Hgs : good_seam rest = true) by (apply (tail_ok_good_seam k); exact Htl).
      assert (Hnu : forall oo, oo <> UNeg ->
                parse_expr F k (print_expr ctx (EUnary oo e0) ++ rest)%string = Some (EUnary oo e0, rest)).
      { intros oo Hoo. rewrite (print_expr_unary oo e0 ctx Hoo), sapp_assoc.
        destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
        destruct f0 as [ | f1 ]; [ cbn [esize] in HF; lia | ].
        destruct (unop_text_char_of oo Hoo) as [ uc [ us [ Hut [ Hus [ Huc Hisu ] ] ] ] ].
        assert (Hpp : parse_primary (S f1) (unop_text oo ++ (print_expr 6 e0 ++ rest))%string
                    = Some (EUnary oo e0, rest)).
        { rewrite Hut, Hus. cbn [append]. rewrite parse_primary_S. cbn [append].
          rewrite (is_unop_not_open uc Hisu), (is_unop_not_quote uc Hisu), Hisu, Huc.
          rewrite (parse_primary_base (esize e0) e0 6 rest f1 (le_n _)
                     ltac:(intros e' He' We Ae; apply (IH e'); [ cbn [esize] in Hsz; lia | exact We | exact Ae ])
                     Hwf Hat
                     ltac:(apply (IH e0); [ cbn [esize] in Hsz; lia | exact Hwf | exact Hat ])
                     ltac:(destruct e0 as [ ? | o'' ? ? | ? ? ]; [ exact I | apply binop_prec_lt6 | exact I ])
                     Hgs ltac:(cbn [esize] in HF; lia)).
          reflexivity. }
        rewrite parse_expr_S, Hpp. apply tail_ok_climb_stop. exact Htl. }
      destruct op; try (apply Hnu; discriminate).
      (* UNeg: "-(" ++ print_expr 0 e0 ++ ")" — peeled by [-(] to a paren-primary on [e0] *)
      rewrite print_expr_uneg.
      destruct F as [ | f0 ]; [ cbn [esize] in HF; lia | ].
      destruct f0 as [ | f1 ]; [ cbn [esize] in HF; lia | ].
      destruct f1 as [ | f2 ]; [ cbn [esize] in HF; lia | ].
      assert (Hpp : parse_primary (S (S f2)) (("-(" ++ print_expr 0 e0 ++ ")") ++ rest)%string
                  = Some (EUnary UNeg e0, rest)).
      { rewrite sapp_assoc, parse_primary_negparen, parse_primary_paren.
        rewrite (sapp_assoc (print_expr 0 e0) ")"%string rest).
        assert (Htl0 : tail_ok 0 (")" ++ rest)%string)
          by (right; left; exists ")"%char, rest; split; [ cbn [append]; reflexivity | reflexivity ]).
        rewrite ((IH e0 ltac:(cbn [esize] in Hsz; lia) Hwf Hat) 0 0 (")" ++ rest)%string f2 (Nat.le_0_l _) Htl0
                   ltac:(cbn [esize] in HF |- *; lia)).
        cbn [append]. reflexivity. }
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

(** The headline.  [wf e] holds for EVERY [e] by construction ([wf_always]: [EAtom] carries an [Atom] with
    its [atom_ok = atomic && balanced_b] proof IN THE TYPE, so a malformed atom is unrepresentable) — hence no
    [wf] side-condition.  [atomic_tree e] is a GENUINE premise (the rule-2 composite-no-spine restriction is
    NOT universal); it is NOT assumed of the plugin — [build_atom] DECIDES it ([atomic_tree_b]) and rejects
    any atom failing it, so [build_atom_roundtrip] is unconditional over everything the plugin recovers.
    [print_expr] emits text the Rocq [parse_expr] re-reads to the SAME tree (precedence-correct, not merely
    balanced).  HONEST SCOPE: printer/parser SELF-CONSISTENCY for the Rocq grammar — NOT yet a theorem about
    Go's OWN parser (a Go-subset recognition theorem is the remaining gap, #10). *)
Theorem print_parse_expr : forall e, atomic_tree e ->
  parse_expr (3 * esize e + 3) 0 (print_expr 0 e) = Some (e, "").
Proof.
  intros e Hat.
  rewrite <- (sapp_nil_r (print_expr 0 e)).
  apply (print_parse_expr_n (esize e) e (le_n _) (wf_always e) Hat);
    [ lia | left; reflexivity | lia ].
Qed.

(** FAITHFULNESS COROLLARY — INJECTIVITY of the expression printer (the analog of [print_ty_inj], now for
    [GoExpr]): two expressions that print alike re-parse to the same tree, hence are equal.  So the emitted
    expression text NEVER conflates two distinct expressions — derived directly from the (unconditional)
    round-trip, lifting both parses to a common fuel via [parse_mono]. *)
Corollary print_expr_inj : forall e1 e2, atomic_tree e1 -> atomic_tree e2 ->
  print_expr 0 e1 = print_expr 0 e2 -> e1 = e2.
Proof.
  intros e1 e2 Ha1 Ha2 He.
  set (F := 3 * esize e1 + 3 + (3 * esize e2 + 3)).
  assert (HF1 : 3 * esize e1 + 3 <= F) by (unfold F; lia).
  assert (HF2 : 3 * esize e2 + 3 <= F) by (unfold F; lia).
  assert (R1 : parse_expr F 0 (print_expr 0 e1) = Some (e1, "")).
  { apply (proj1 (parse_mono F _ HF1)). apply print_parse_expr; exact Ha1. }
  assert (R2 : parse_expr F 0 (print_expr 0 e2) = Some (e2, "")).
  { apply (proj1 (parse_mono F _ HF2)). apply print_parse_expr; exact Ha2. }
  rewrite He in R1. rewrite R1 in R2. injection R2 as Ht. exact Ht.
Qed.

(** A printed (sub)expression spends at least HALF an [esize] unit per character: [esize e <= 2*|print| + 1].
    Every node prints >= 1 char (leaves are non-empty; [binop_text] is space-led, [unop_text] is one op char),
    and the sole over-count — [EUnary]'s [+2] fuel margin against its single op char — is absorbed by the
    factor 2.  This converts the round-trip's [asize]-based fuel into the [String.length]-based fuel
    [build_atom] needs (it is handed a STRING, not a tree, so it cannot compute [asize] directly). *)
Lemma size_le_2len1 :
  (forall e ctx, esize e <= 2 * String.length (print_expr ctx e) + 1) /\
  (forall a, gsize a <= 2 * String.length (atom_str a) + 1) /\
  (forall sa, asize sa <= 2 * String.length (satom_str sa) + 1) /\
  (forall args, argl_size args <= 2 * String.length (argl_str args) + 2).
Proof.
  apply GoTree_mutind.
  - (* EAtom a *) intros a IHa ctx. rewrite (print_expr_atom ctx a). cbn [esize]. exact IHa.
  - (* EBin o l r *) intros o l IHl r IHr ctx.
    cbn [esize]. specialize (IHl (binop_prec o)). specialize (IHr (S (binop_prec o))).
    destruct (binop_text_head_space o) as [ t Ht ].
    destruct (Nat.ltb (binop_prec o) ctx) eqn:E.
    + rewrite (print_expr_wrapped o l r ctx E), !slen_app, Ht. cbn [String.length]. lia.
    + rewrite (print_expr_unwrapped o l r ctx E), !slen_app, Ht. cbn [String.length]. lia.
  - (* EUnary op e *) intros op e IHe ctx. cbn [esize]. destruct op;
      try (match goal with |- context[EUnary ?o e] =>
             rewrite (print_expr_unary o e ctx ltac:(discriminate)) end;
           rewrite slen_app; cbn [unop_text String.length]; specialize (IHe 6); lia).
    (* UNeg prints "-(" ++ print 0 e ++ ")" — 3 chars over the operand, absorbed by the factor 2 *)
    rewrite print_expr_uneg, !slen_app. cbn [String.length]. specialize (IHe 0). lia.
  - (* AScanned sa *) intros sa IHsa. cbn [gsize atom_str]. exact IHsa.
  - (* AStringLit v *) intros v. cbn [gsize atom_str]. lia.
  - (* SIdent i *) intros i. cbn [asize satom_str]. lia.
  - (* SIntLit z *) intros z. cbn [asize satom_str]. lia.
  - (* SHexLit hz *) intros hz. cbn [asize satom_str]. lia.
  - (* SRaw r *) intros r. cbn [asize satom_str]. lia.
  - (* SSelector a f *) intros a IHa f. cbn [asize satom_str]. rewrite slen_app. cbn [String.length]. lia.
  - (* SIndex a i *) intros a IHa i IHi. cbn [asize satom_str]. specialize (IHi 0).
    rewrite slen_app; cbn [String.length]; rewrite slen_app; cbn [String.length]. lia.
  - (* SSlice a lo hi *) intros a IHa lo IHlo hi IHhi. cbn [asize satom_str].
    specialize (IHlo 0); specialize (IHhi 0).
    rewrite slen_app; cbn [String.length]; rewrite slen_app; cbn [String.length];
      rewrite slen_app; cbn [String.length]. lia.
  - (* SApply a args : satom_str a ++ "(" ++ argl_str args ++ ")" *)
    intros a IHa args IHargs. cbn [asize satom_str].
    rewrite !slen_app; cbn [String.length]; rewrite !slen_app; cbn [String.length]. lia.
  - (* ANil *) cbn [argl_size argl_str String.length]. lia.
  - (* ACons e args *) intros e IHe args IHargs. cbn [argl_size]. destruct args as [ | e2 args' ].
    + cbn [argl_str argl_size]. specialize (IHe 0). lia.
    + change (argl_str (ACons e (ACons e2 args')))
        with (print_expr 0 e ++ String (ch 44) (String (ch 32) (argl_str (ACons e2 args'))))%string.
      rewrite !slen_app; cbn [String.length]. specialize (IHe 0). lia.
Qed.

(** The round-trip holds for EVERY tree ([wf]/[atomic_tree] are vacuous) — the size-IH [build_atom] feeds to
    [parse_primary_atom] for an atom's index/slice children. *)
Lemma Pexpr_always : forall e, atomic_tree e -> Pexpr e.
Proof. intros e Hat. exact (print_parse_expr_n (esize e) e (le_n _) (wf_always e) Hat). Qed.

(** [build_atom cs] — the VERIFIED atom RECOVERY the plugin calls (review #4: re-check the erased [SAtom]
    proof at the boundary).  It runs the structured [parse_primary] (the postfix PrimaryExpr grammar) with
    enough fuel ([6*|cs|+3], justified by [size_le_2len1]) and demands FULL consumption: a string that is
    [satom_str sa] for some scanned atom [sa] is recovered as [Some (EAtom (AScanned sa))] (proved by
    [build_atom_str]); anything else returns [None], so [mk_atom] ABORTS (fail-loud) rather than emit a
    plausible-but-wrong atom. *)
Definition build_atom (cs : string) : option GoExpr :=
  match parse_primary (6 * String.length cs + 3) cs with
  | Some (e, EmptyString) => if atomic_tree_b e then Some e else None
  | _ => None
  end.

(** [build_atom]'s output is PROVABLY [atomic_tree] (review #8 P0-3): the [atomic_tree_b] guard rejects any
    recovered atom that is not — so [print_parse_expr]'s premise is ENFORCED at the recovery boundary, never
    assumed of go.ml.  A composite literal carrying a postfix spine ([ []int{1,2,3}[0] ], valid Go but
    unemitted) is REJECTED here ([build_atom_rejects_comp_spine] below), not silently round-trip-mismatched. *)
Lemma build_atom_atomic_tree : forall cs e, build_atom cs = Some e -> atomic_tree e.
Proof.
  intros cs e H. unfold build_atom in H.
  destruct (parse_primary (6 * String.length cs + 3) cs) as [ [e' r] | ]; [ | discriminate H ].
  destruct r as [ | c r' ]; [ | discriminate H ].
  destruct (atomic_tree_b e') eqn:Eb; [ | discriminate H ].
  injection H as <-. apply (proj1 atomic_tree_b_refl). exact Eb.
Qed.

(** Hence the round-trip is UNCONDITIONAL over everything [build_atom] recovers — no caller supplies the
    [atomic_tree] premise; [build_atom] discharges it.  This is the honest printer guarantee for the plugin's
    recovery path: what [build_atom] accepts, [print_expr] reparses to EXACTLY itself. *)
Theorem build_atom_roundtrip : forall cs e, build_atom cs = Some e ->
  parse_expr (3 * esize e + 3) 0 (print_expr 0 e) = Some (e, "").
Proof. intros cs e H. apply print_parse_expr, (build_atom_atomic_tree cs e H). Qed.

(** [list_to_argl] — pack a [list GoExpr] into the mutual [ArgList] that [SApply] carries. *)
Fixpoint list_to_argl (xs : list GoExpr) : ArgList :=
  match xs with nil => ANil | cons e r => ACons e (list_to_argl r) end.
(** ★[build_apply callee args] — the VERIFIED DIRECT constructor for an APPLICATION node (review #9: CONSTRUCT
    syntax, do NOT rescue strings).  The plugin hands the ALREADY-BUILT [callee] [GoExpr] (a scanned atom — an
    identifier / selector / nested application) and the ALREADY-BUILT [args] (each a verified [GoExpr]); this
    packs them into [SApply] and RE-CHECKS [atomic_tree_b], so the result is GUARANTEED to round-trip
    ([print_parse_expr]'s premise is ENFORCED here, never assumed of go.ml).  A callee that is not a scanned
    atom, or a non-[atomic_tree] result, returns [None] → the plugin fails loud.  No string is printed-then-
    reparsed — this is the construction path that replaces [pp_expr → string → build_atom] for calls. *)
Definition build_apply (callee : GoExpr) (args : list GoExpr) : option GoExpr :=
  match callee with
  | EAtom (AScanned sa) =>
      let e := EAtom (AScanned (SApply sa (list_to_argl args))) in
      if atomic_tree_b e then Some e else None
  | _ => None
  end.
Lemma build_apply_atomic_tree : forall callee args e, build_apply callee args = Some e -> atomic_tree e.
Proof.
  intros callee args e H. unfold build_apply in H. destruct callee as [ [ sa | v ] | | ]; try discriminate H.
  destruct (atomic_tree_b (EAtom (AScanned (SApply sa (list_to_argl args))))) eqn:Eb; [ | discriminate H ].
  injection H as <-. apply (proj1 atomic_tree_b_refl). exact Eb.
Qed.
(** Hence an [SApply] the plugin constructs DIRECTLY round-trips: [print_expr] reparses it to exactly itself —
    the honest verified guarantee for the structured application node (NOT a string-recovery). *)
Theorem build_apply_roundtrip : forall callee args e, build_apply callee args = Some e ->
  parse_expr (3 * esize e + 3) 0 (print_expr 0 e) = Some (e, "").
Proof. intros callee args e H. apply print_parse_expr, (build_apply_atomic_tree callee args e H). Qed.

(** [build_atom] recovers a SCANNED atom from its printed text ([AStringLit] is NOT scanned — it is
    recovered by [parse_strlit_prim], so excluded by the [atom_scanned] hypothesis).  The [atomic_tree_b]
    guard is satisfied because [atomic_atom g] holds (reflected to [atomic_atom_b g = true]). *)
Lemma build_atom_str : forall g, atom_scanned g = true -> atomic_atom g ->
  build_atom (atom_str g) = Some (EAtom g).
Proof.
  intros [ sa | v ] Hsc Hat; cbn [atom_scanned] in Hsc; [ clear Hsc | discriminate Hsc ].
  cbn [atom_str]. cbn [atomic_atom] in Hat. destruct Hat as [ Hatm [ Hdis Hasat ] ].
  assert (Hdisj : is_comp_lead (satom_str (fst (spine sa))) = false \/ snd (spine sa) = nil)
    by (destruct Hdis as [ H | H ]; [ left; rewrite <- sa_leaf_comp_spine; exact H | right; apply sa_has_ops_nil; exact H ]).
  assert (Hb : atomic_atom_b (AScanned sa) = true)
    by (apply (proj1 (proj2 atomic_tree_b_refl)); cbn [atomic_atom]; exact (conj Hatm (conj Hdis Hasat))).
  unfold build_atom.
  replace (6 * String.length (satom_str sa) + 3)
    with (S (6 * String.length (satom_str sa) + 2)) by lia.
  pose proof (parse_primary_atom sa "" (6 * String.length (satom_str sa) + 2) eq_refl
                (fun e' _ Ae' => Pexpr_always e' Ae')
                ltac:(pose proof (proj1 (proj2 (proj2 size_le_2len1)) sa); lia) Hdisj Hasat) as Hpp.
  rewrite sapp_nil_r in Hpp. rewrite Hpp. cbn [atomic_tree_b]. rewrite Hb. reflexivity.
Qed.

(** REVIEW #8 P0-3 REGRESSION TEST — a composite literal carrying a postfix index ([ []int{1,2,3}[0] ]) is
    valid Go but NOT [atomic_tree] (composite base + spine).  Before the [atomic_tree_b] guard, [build_atom]
    recovered it as [Some _] (a non-round-trippable atom escaping the printer guarantee).  Now REJECTED. *)
Example build_atom_rejects_comp_spine : build_atom "[]int{1,2,3}[0]" = None.
Proof. reflexivity. Qed.
Example build_atom_accepts_ident_index : exists e, build_atom "xs[0]" = Some e.
Proof. eexists. reflexivity. Qed.

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
(** One-level cons unfold (keeps the tail's [print_sep] FOLDED — [cbn] would expand it recursively). *)
Lemma print_sep_cons : forall sep x y zs,
  print_sep sep (x :: y :: zs) = (x ++ sep ++ print_sep sep (y :: zs))%string.
Proof. reflexivity. Qed.


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
Print Assumptions build_atom_str.
Print Assumptions print_sep_balanced.
(* review #9: the plugin-boundary BUILDER theorems are gated DIRECTLY (not "they only depend on gated ones"). *)
Print Assumptions build_atom_roundtrip.
Print Assumptions build_atom_atomic_tree.
Print Assumptions build_base_correct.
Print Assumptions build_apply_roundtrip.
Print Assumptions parse_args_roundtrip_mut.

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_expr print_sep print_float_hex atomic atom_ok go_ident nominal_type_ident is_dec raw_ok parse_Z strlit_ok strlit_value build_atom build_apply.
