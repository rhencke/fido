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

(** A func-lit parameter list [x T, y T] — each [name type] pair, ", "-separated.  (Defined here, before the
    expression mutual block, so the [EForceCall] printer — the structured func-lit-call — can use it.) *)
Fixpoint print_params (ps : list (Ident * GoTy)) : string :=
  match ps with
  | nil            => ""
  | (x, t) :: nil  => proj1_sig x ++ " " ++ print_ty t
  | (x, t) :: rest => proj1_sig x ++ " " ++ print_ty t ++ ", " ++ print_params rest
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

    [BinOp] is the operator enum; [binop_prec] / [binop_text] DERIVE its precedence and surface text from
    the constructor — the single source of truth, so no caller can mis-pair an operator with the wrong
    precedence.  Consumed by [Module Front]'s [gprint] (the verified frontend below), which parenthesises a
    sub-expression exactly when its [binop_prec] is looser than the context.  (The plugin's trusted OCaml
    [pp_prec] renders the same binary-operator tree as strings; [Front] is being built to replace it.) *)
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

(** UNARY operators: not / bitwise-complement / dereference / address-of / negate.  Single-char prefixes
    (Go: [!b] [^x] [*p] [&x] [-x]), binding TIGHTER than every binary operator.  ([+] unary is omitted — the
    plugin never emits it.)  [unop_text] gives the surface text; consumed by [Module Front]'s [gprint].
    [UNeg] (unary [-]) prints PARENTHESISED — [-(x)] — because a bare [-x] would collide with the [-5]
    negative literal, and [Front]'s parser dispatches the unambiguous two-char prefix [-(] to it (the other
    four print bare). *)
Inductive UnaryOp : Type := UNot | UXor | UDeref | UAddr | UNeg.
Definition unop_text (o : UnaryOp) : string :=
  match o with UNot => "!" | UXor => "^" | UDeref => "*" | UAddr => "&" | UNeg => "-" end.
Definition is_space (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 32).  (* ' ' *)
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
Fixpoint print_sep (sep : string) (xs : list string) : string :=
  match xs with
  | []        => ""
  | x :: xs'  => match xs' with
                 | []     => x
                 | _ :: _ => (x ++ sep ++ print_sep sep xs')%string
                 end
  end.
Module Front.

(** ---- TOKENS ---- the lexer's output alphabet.  Ambiguous operator chars ([* & ^ -]) are ONE token each;
    the PARSER decides prefix(unary)/infix(binary) by position (Wirth: the scanner classifies, the parser
    disambiguates).  Literals carry their SEMANTIC value ([Z]); identifiers carry a validated [Ident]. *)
Inductive Token : Type :=
  | TId  : Ident -> Token | TInt : Z -> Token
  | TPlus | TMinus | TStar | TSlash | TPercent | TAmp | TPipe | TCaret | TBang
  | TShl | TShr | TAndNot | TEq | TNe | TLt | TLe | TGt | TGe | TLand | TLor
  | TLP | TRP | TLB | TRB | TLC | TRC | TComma | TColon | TDot
  | TFunc | TReturn.

(** scan a maximal run of decimal digits off the head. *)
Fixpoint scan_digits (s : string) : string * string :=
  match s with
  | String c s' => if is_dec_char c then let (d, r) := scan_digits s' in (String c d, r) else (EmptyString, s)
  | EmptyString => (EmptyString, EmptyString)
  end.

(** the operator / delimiter scanner: MAXIMAL-MUNCH the token at the head [String c s'], return (token, rest). *)
Definition lex_op (c : ascii) (s' : string) : option (Token * string) :=
  if Ascii.eqb c (ch 40) then Some (TLP, s') else if Ascii.eqb c (ch 41) then Some (TRP, s')
  else if Ascii.eqb c (ch 91) then Some (TLB, s') else if Ascii.eqb c (ch 93) then Some (TRB, s')
  else if Ascii.eqb c (ch 123) then Some (TLC, s') else if Ascii.eqb c (ch 125) then Some (TRC, s')
  else if Ascii.eqb c (ch 44) then Some (TComma, s') else if Ascii.eqb c (ch 58) then Some (TColon, s')
  else if Ascii.eqb c (ch 46) then Some (TDot, s')
  else if Ascii.eqb c (ch 43) then Some (TPlus, s') else if Ascii.eqb c (ch 42) then Some (TStar, s')
  else if Ascii.eqb c (ch 47) then Some (TSlash, s') else if Ascii.eqb c (ch 37) then Some (TPercent, s')
  else if Ascii.eqb c (ch 94) then Some (TCaret, s') else if Ascii.eqb c (ch 45) then Some (TMinus, s')
  else if Ascii.eqb c (ch 60) then
    match s' with String d s'' => if Ascii.eqb d (ch 60) then Some (TShl, s'')
                                  else if Ascii.eqb d (ch 61) then Some (TLe, s'') else Some (TLt, s')
                | EmptyString => Some (TLt, s') end
  else if Ascii.eqb c (ch 62) then
    match s' with String d s'' => if Ascii.eqb d (ch 62) then Some (TShr, s'')
                                  else if Ascii.eqb d (ch 61) then Some (TGe, s'') else Some (TGt, s')
                | EmptyString => Some (TGt, s') end
  else if Ascii.eqb c (ch 61) then
    match s' with String d s'' => if Ascii.eqb d (ch 61) then Some (TEq, s'') else None | _ => None end
  else if Ascii.eqb c (ch 33) then
    match s' with String d s'' => if Ascii.eqb d (ch 61) then Some (TNe, s'') else Some (TBang, s')
                | _ => Some (TBang, s') end
  else if Ascii.eqb c (ch 38) then
    match s' with String d s'' => if Ascii.eqb d (ch 38) then Some (TLand, s'')
                                  else if Ascii.eqb d (ch 94) then Some (TAndNot, s'') else Some (TAmp, s')
                | _ => Some (TAmp, s') end
  else if Ascii.eqb c (ch 124) then
    match s' with String d s'' => if Ascii.eqb d (ch 124) then Some (TLor, s'') else Some (TPipe, s')
                | _ => Some (TPipe, s') end
  else None.

(** classify an identifier RUN: a keyword token ([func]/[return]) or a [go_ident]-validated [TId]. *)
Definition lex_ident (tok : string) : option Token :=
  if String.eqb tok "func" then Some TFunc
  else if String.eqb tok "return" then Some TReturn
  else match bool_dec (go_ident tok) true with left H => Some (TId (exist _ tok H)) | right _ => None end.

(** THE LEXER.  Skip whitespace; an [is_idstart] head is an identifier/keyword; a digit (or [-]+digit, the
    negative-literal form — binary [-] is always SPACED in the printer) is an integer; otherwise an
    operator/delimiter.  Fuel = input length (each token consumes >= 1 char, so it terminates). *)
Fixpoint lex_aux (fuel : nat) (s : string) : option (list Token) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => Some nil
    | String c s' =>
        if is_space c then lex_aux f s'
        else if is_idstart c then
          let (tok, rest) := scan_id s in
          match lex_ident tok with
          | Some t => match lex_aux f rest with Some l => Some (t :: l) | None => None end
          | None => None end
        else if is_dec_char c then
          let (num, rest) := scan_digits s in
          match lex_aux f rest with Some l => Some (TInt (parse_Z num) :: l) | None => None end
        else if andb (Ascii.eqb c (ch 45)) (match s' with String d _ => is_dec_char d | _ => false end) then
          let (num, rest) := scan_digits s' in
          match lex_aux f rest with Some l => Some (TInt (parse_Z (String c num)) :: l) | None => None end
        else
          match lex_op c s' with
          | Some (t, rest) => match lex_aux f rest with Some l => Some (t :: l) | None => None end
          | None => None end
    end
  end.
Definition lex (s : string) : option (list Token) := lex_aux (S (String.length s)) s.

Example lex_sum  : lex "a + b" = Some (TId (exist _ "a" eq_refl) :: TPlus :: TId (exist _ "b" eq_refl) :: nil).
Proof. vm_compute; reflexivity. Qed.
Example lex_call : lex "f(x, 42)"
  = Some (TId (exist _ "f" eq_refl) :: TLP :: TId (exist _ "x" eq_refl) :: TComma :: TInt 42 :: TRP :: nil).
Proof. vm_compute; reflexivity. Qed.
Example lex_neg  : lex "-7" = Some (TInt (-7) :: nil). Proof. vm_compute; reflexivity. Qed.
Example lex_ops  : lex "x << 2" = Some (TId (exist _ "x" eq_refl) :: TShl :: TInt 2 :: nil). Proof. vm_compute; reflexivity. Qed.
Example lex_cmp  : lex "a <= b && c"
  = Some (TId (exist _ "a" eq_refl) :: TLe :: TId (exist _ "b" eq_refl) :: TLand :: TId (exist _ "c" eq_refl) :: nil).
Proof. vm_compute; reflexivity. Qed.

(** ---- THE CLEAN AST ---- the Go expression grammar, fully structured.  No [SRaw], no [SAtom]/[GoAtom]
    intermediate.  CORE (grows: ECall/ESel/EIndex/ESlice/EConv/EFuncLit).  Literals carry their value. *)
Inductive GExpr : Type :=
  | EId  : Ident -> GExpr
  | EInt : Z -> GExpr
  | EUn  : UnaryOp -> GExpr -> GExpr
  | EBn  : BinOp -> GExpr -> GExpr -> GExpr.

(** A bare prefix operator applied DIRECTLY to another prefix operator is a LEXICAL hazard: [&] then [&]
    (nested [UAddr]) prints "&&" which the lexer maximal-munches to [TLand], and [&] then [^] (UAddr-of-
    UXor) prints "&^" -> [TAndNot] — a token MERGE on the LEFT of the seam (the seam is two-sided: a clean
    right-hand start does not suffice).  So a bare-unary operand that is itself a unary node is PARENTHESISED
    — making every unary seam a single-char delimiter ['('], which cannot munch into the operator before it.
    (This is exactly the precise seam discipline the round-trip needs; UNeg already self-parenthesises.) *)
Definition is_un (e : GExpr) : bool := match e with EUn _ _ => true | _ => false end.

(** ---- THE PRINTER ---- precedence-correct (reuses [binop_prec]/[binop_text]/[unop_text]); a binop wraps
    in parens exactly when its precedence [< ctx].  Mirrors the legacy [print_expr] over the clean AST. *)
Fixpoint gprint (ctx : nat) (e : GExpr) : string :=
  match e with
  | EId i  => proj1_sig i
  | EInt z => print_Z z
  | EUn o e => match o with
               | UNeg => ("-(" ++ gprint 0 e ++ ")")%string
               | _    => (unop_text o ++ "(" ++ gprint 0 e ++ ")")%string
               end
  | EBn o l r =>
      let p := binop_prec o in
      let inner := (gprint p l ++ binop_text o ++ gprint (S p) r)%string in
      if Nat.ltb p ctx then ("(" ++ inner ++ ")")%string else inner
  end.

(** ---- THE PARSER ---- recursive descent + precedence climbing over the TOKEN stream.  The ambiguous
    operator tokens are resolved by POSITION: a prefix [TStar]/[TAmp]/[TCaret]/[TBang] is a unary op
    ([parse_primary]); an infix one is a binary op ([infix_op] in [parse_climb]).  [TMinus]+[TLP] is the
    parenthesised unary minus [UNeg]; bare negative literals are already [TInt] from the lexer. *)
Definition infix_op (t : Token) : option BinOp :=
  match t with
  | TPlus => Some BAdd | TMinus => Some BSub | TStar => Some BMul | TSlash => Some BDiv
  | TPercent => Some BRem | TShl => Some BShl | TShr => Some BShr | TAmp => Some BAnd
  | TAndNot => Some BAndNot | TPipe => Some BOr | TCaret => Some BXor
  | TEq => Some BEq | TNe => Some BNe | TLt => Some BLt | TLe => Some BLe | TGt => Some BGt | TGe => Some BGe
  | TLand => Some BLAnd | TLor => Some BLOr
  | _ => None
  end.

Fixpoint parse_expr (fuel k : nat) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f => match parse_primary f toks with Some (l, r) => parse_climb f k l r | None => None end
  end
with parse_primary (fuel : nat) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TLP :: rest => match parse_expr f 0 rest with Some (e, TRP :: r) => Some (e, r) | _ => None end
    | TBang  :: rest => match parse_primary f rest with Some (e, r) => Some (EUn UNot e, r)   | None => None end
    | TCaret :: rest => match parse_primary f rest with Some (e, r) => Some (EUn UXor e, r)   | None => None end
    | TStar  :: rest => match parse_primary f rest with Some (e, r) => Some (EUn UDeref e, r) | None => None end
    | TAmp   :: rest => match parse_primary f rest with Some (e, r) => Some (EUn UAddr e, r)  | None => None end
    | TMinus :: TLP :: rest => match parse_expr f 0 rest with Some (e, TRP :: r) => Some (EUn UNeg e, r) | _ => None end
    | TId i :: rest  => Some (EId i, rest)
    | TInt z :: rest => Some (EInt z, rest)
    | _ => None
    end
  end
with parse_climb (fuel k : nat) (l : GExpr) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | t :: rest =>
        match infix_op t with
        | Some o => if Nat.leb k (binop_prec o)
                    then match parse_expr f (S (binop_prec o)) rest with
                         | Some (r, r2) => parse_climb f k (EBn o l r) r2
                         | None => None end
                    else Some (l, toks)
        | None => Some (l, toks)
        end
    | nil => Some (l, toks)
    end
  end.
Definition parse (toks : list Token) : option (GExpr * list Token) := parse_expr (S (List.length toks)) 0 toks.
(** parse a STRING end-to-end: [lex] then [parse].  The frontend's front door. *)
Definition parse_str (s : string) : option (GExpr * list Token) :=
  match lex s with Some toks => parse toks | None => None end.

(** END-TO-END round-trip by example: [parse_str (gprint 0 e) = Some (e, [])] — the printed AST lexes and
    parses back to itself.  (The general theorem [parse_str (gprint 0 e) = Some (e, [])] is next.) *)
Notation EX a := (EId (exist (fun s : string => go_ident s = true) a eq_refl)) (only parsing).
Example rt_id   : parse_str (gprint 0 (EX "x")) = Some (EX "x", nil). Proof. vm_compute; reflexivity. Qed.
Example rt_int  : parse_str (gprint 0 (EInt 42)) = Some (EInt 42, nil). Proof. vm_compute; reflexivity. Qed.
Example rt_add  : parse_str (gprint 0 (EBn BAdd (EX "a") (EX "b"))) = Some (EBn BAdd (EX "a") (EX "b"), nil).
Proof. vm_compute; reflexivity. Qed.
Example rt_prec : parse_str (gprint 0 (EBn BAdd (EX "a") (EBn BMul (EX "b") (EX "c"))))
                = Some (EBn BAdd (EX "a") (EBn BMul (EX "b") (EX "c")), nil).  (* a + b*c — no parens *)
Proof. vm_compute; reflexivity. Qed.
Example rt_wrap : parse_str (gprint 0 (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c")))
                = Some (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c"), nil).  (* (a + b)*c — parens recovered *)
Proof. vm_compute; reflexivity. Qed.
Example rt_un   : parse_str (gprint 0 (EUn UNot (EBn BEq (EX "a") (EX "b"))))
                = Some (EUn UNot (EBn BEq (EX "a") (EX "b")), nil).  (* !(a == b) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_neg  : parse_str (gprint 0 (EUn UNeg (EX "x"))) = Some (EUn UNeg (EX "x"), nil).  (* -(x) *)
Proof. vm_compute; reflexivity. Qed.
(* the nested-bare-unary LEXICAL HAZARD: without the operand parens these print "&&x"/"&^x" and lex to
   [TLand]/[TAndNot] — a left-side token merge.  With the fix they print "&(&x)"/"&(^x)" and round-trip. *)
Example rt_addr_addr : parse_str (gprint 0 (EUn UAddr (EUn UAddr (EX "x"))))
                     = Some (EUn UAddr (EUn UAddr (EX "x")), nil).
Proof. vm_compute; reflexivity. Qed.
Example rt_addr_xor  : parse_str (gprint 0 (EUn UAddr (EUn UXor (EX "x"))))
                     = Some (EUn UAddr (EUn UXor (EX "x")), nil).
Proof. vm_compute; reflexivity. Qed.

(** ---- THE CANONICAL TOKEN LIST ---- [gtokens ctx e] is the token list [gprint ctx e] lexes to.  Mirrors
    [gprint]'s structure exactly; [op_token]/[prefix_token] are the inverses of [infix_op]/[prefix_op].
    This is the bridge for the general round-trip: [lex (gprint ctx e) = Some (gtokens ctx e)] (lexer side)
    and [parse_expr F (gtokens ctx e ++ rest) = Some (e, rest)] (parser side), composed. *)
Definition op_token (o : BinOp) : Token :=
  match o with
  | BAdd => TPlus | BSub => TMinus | BMul => TStar | BDiv => TSlash | BRem => TPercent
  | BShl => TShl | BShr => TShr | BAnd => TAmp | BAndNot => TAndNot | BOr => TPipe | BXor => TCaret
  | BEq => TEq | BNe => TNe | BLt => TLt | BLe => TLe | BGt => TGt | BGe => TGe
  | BLAnd => TLand | BLOr => TLor
  end.
Definition prefix_token (o : UnaryOp) : Token :=
  match o with UNot => TBang | UXor => TCaret | UDeref => TStar | UAddr => TAmp | UNeg => TMinus end.

Fixpoint gtokens (ctx : nat) (e : GExpr) : list Token :=
  match e with
  | EId i  => TId i :: nil
  | EInt z => TInt z :: nil
  | EUn o e => match o with
               | UNeg => TMinus :: TLP :: (gtokens 0 e ++ TRP :: nil)
               | _    => prefix_token o :: TLP :: (gtokens 0 e ++ TRP :: nil)
               end
  | EBn o l r =>
      let p := binop_prec o in
      let inner := (gtokens p l ++ op_token o :: gtokens (S p) r)%list in
      if Nat.ltb p ctx then TLP :: (inner ++ TRP :: nil) else inner
  end.

(** [op_token]/[prefix_token] really invert the parser's token classifiers. *)
Lemma infix_op_token : forall o, infix_op (op_token o) = Some o.
Proof. destruct o; reflexivity. Qed.

(** [gtokens] is the RIGHT spec: it is exactly what [lex (gprint ctx e)] yields (validated; the universal
    lemma [lex (gprint ctx e) = Some (gtokens ctx e)] is the next step). *)
Example gtok_add  : lex (gprint 0 (EBn BAdd (EX "a") (EX "b"))) = Some (gtokens 0 (EBn BAdd (EX "a") (EX "b"))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_wrap : lex (gprint 0 (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c")))
                  = Some (gtokens 0 (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c"))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_un   : lex (gprint 0 (EUn UNot (EBn BEq (EX "a") (EX "b"))))
                  = Some (gtokens 0 (EUn UNot (EBn BEq (EX "a") (EX "b")))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_neg  : lex (gprint 0 (EUn UNeg (EX "x"))) = Some (gtokens 0 (EUn UNeg (EX "x"))).
Proof. vm_compute; reflexivity. Qed.
(* the hazard, at the lexer level: [lex (gprint ..)] still equals [gtokens ..] for nested bare unaries —
   the direct witness at each dangerous maximal-munch seam ("&&" -> TLand, "&^" -> TAndNot). *)
Example gtok_addr_addr : lex (gprint 0 (EUn UAddr (EUn UAddr (EX "x"))))
                       = Some (gtokens 0 (EUn UAddr (EUn UAddr (EX "x")))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_addr_xor  : lex (gprint 0 (EUn UAddr (EUn UXor (EX "x"))))
                       = Some (gtokens 0 (EUn UAddr (EUn UXor (EX "x")))).
Proof. vm_compute; reflexivity. Qed.

(** ---- M3b GROUNDWORK: lexer fuel MONOTONICITY ---- adding fuel never changes a [Some] answer.  Needed to
    bridge the fuel when composing [lex] over a concatenation (the per-token decrement makes [S (length s)]
    exact, so a sub-lex with more-than-enough fuel still agrees).  Induction on [f]; each char-step recurses
    with the same discriminants, so the [Some] result is preserved by the IH on the tail. *)
Lemma lex_aux_mono : forall f s ts f',
  lex_aux f s = Some ts -> f <= f' -> lex_aux f' s = Some ts.
Proof.
  induction f as [ | f IH ]; intros s ts f' H Hle; [ discriminate H | ].
  destruct f' as [ | f' ]; [ lia | ].
  assert (Hle' : f <= f') by lia.
  destruct s as [ | c s' ]; [ exact H | ].
  cbn [lex_aux] in H |- *.
  destruct (is_space c).
  { exact (IH _ _ _ H Hle'). }
  destruct (is_idstart c).
  { destruct (scan_id (String c s')) as [tok rest].
    destruct (lex_ident tok) as [t | ]; [ | exact H ].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
  destruct (is_dec_char c).
  { destruct (scan_digits (String c s')) as [num rest].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
  destruct (andb (Ascii.eqb c (ch 45)) (match s' with String d _ => is_dec_char d | _ => false end)).
  { destruct (scan_digits s') as [num rest].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
  { destruct (lex_op c s') as [[t rest] | ]; [ | exact H ].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
Qed.

(** ---- M3b: the LEXER ROUND-TRIP groundwork ---- the seam predicate + the scanner-splitting lemmas.
    [clean_start rest] = the next char cannot EXTEND an identifier/number token (it is not an id-char), so
    a token ending just before [rest] is complete — exactly the boundary [gprint] emits between subtrees
    (a space, a ')', or end-of-string).  This is the two-sided seam condition the round-trip needs. *)
Definition clean_start (rest : string) : bool :=
  match rest with EmptyString => true | String c _ => negb (is_idc c) end.

Lemma is_dec_char_is_idc : forall c, is_dec_char c = true -> is_idc c = true.
Proof.
  intro c. unfold is_dec_char, is_idc. intro H. apply andb_prop in H.
  destruct H as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

(** A clean-start string scans NO identifier / NO digit run — the scanners stop immediately. *)
Lemma scan_id_clean : forall b, clean_start b = true -> scan_id b = (EmptyString, b).
Proof.
  intros [ | c b' ] H; [ reflexivity | ].
  unfold clean_start in H. cbn [scan_id]. destruct (is_idc c); [ discriminate H | reflexivity ].
Qed.

Lemma scan_digits_clean : forall b, clean_start b = true -> scan_digits b = (EmptyString, b).
Proof.
  intros [ | c b' ] H; [ reflexivity | ].
  unfold clean_start in H. cbn [scan_digits]. destruct (is_dec_char c) eqn:E; [ | reflexivity ].
  apply is_dec_char_is_idc in E. rewrite E in H. discriminate H.
Qed.

(** [scan_id] / [scan_digits] split an all-id / all-decimal PREFIX off a clean-start REST exactly. *)
Lemma scan_id_app : forall a b, all_idc a = true -> clean_start b = true -> scan_id (a ++ b) = (a, b).
Proof.
  induction a as [ | c a' IH ]; intros b Ha Hb.
  - apply scan_id_clean; exact Hb.
  - cbn [all_idc] in Ha. apply andb_prop in Ha. destruct Ha as [Hc Ha'].
    cbn [String.append scan_id]. rewrite Hc. rewrite (IH b Ha' Hb). reflexivity.
Qed.

Lemma scan_digits_app : forall a b, all_dec a = true -> clean_start b = true -> scan_digits (a ++ b) = (a, b).
Proof.
  induction a as [ | c a' IH ]; intros b Ha Hb.
  - apply scan_digits_clean; exact Hb.
  - cbn [all_dec] in Ha. apply andb_prop in Ha. destruct Ha as [Hc Ha'].
    cbn [String.append scan_digits]. rewrite Hc. rewrite (IH b Ha' Hb). reflexivity.
Qed.

(** An identifier-start char is never a space. *)
Lemma is_idstart_not_space : forall c, is_idstart c = true -> is_space c = false.
Proof.
  intro c. unfold is_space. intro H.
  destruct (Ascii.eqb c (ascii_of_nat 32)) eqn:E; [ | reflexivity ].
  exfalso. apply Ascii.eqb_eq in E. subst c. vm_compute in H. discriminate H.
Qed.

(** [lex_ident] on a [go_ident] string yields exactly [TId] of that ident (the keyword guards do not fire
    — a [go_ident] is never a keyword — and the [bool_dec] proof equals the carried one by UIP-on-bool). *)
Lemma lex_ident_go : forall s (Hs : go_ident s = true), lex_ident s = Some (TId (exist _ s Hs)).
Proof.
  intros s Hs. unfold lex_ident.
  destruct (String.eqb s "func") eqn:Ef.
  { apply String.eqb_eq in Ef. subst s. vm_compute in Hs. discriminate Hs. }
  destruct (String.eqb s "return") eqn:Er.
  { apply String.eqb_eq in Er. subst s. vm_compute in Hs. discriminate Hs. }
  destruct (bool_dec (go_ident s) true) as [H | H].
  - assert (E : H = Hs) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
  - exfalso. apply H. exact Hs.
Qed.

(** LEAF (identifier): lexing [gprint (EId i) ++ rest = proj1_sig i ++ rest] yields [TId i] then [rest]'s
    tokens — given a clean seam and enough fuel.  ([gtokens (EId i) = [TId i]].) *)
Lemma lex_gprint_id : forall (i : Ident) rest fuel tr,
  clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length (proj1_sig i) + String.length rest) <= fuel ->
  lex_aux fuel (proj1_sig i ++ rest) = Some (TId i :: tr).
Proof.
  intros [s Hs] rest fuel tr Hclean Hrest Hfuel. simpl proj1_sig in *.
  destruct s as [ | c0 s0 ]; [ vm_compute in Hs; discriminate Hs | ].
  destruct fuel as [ | f ]; [ cbn in Hfuel; lia | ].
  pose proof Hs as Hgo. unfold go_ident in Hgo. apply andb_prop in Hgo. destruct Hgo as [Hia _].
  apply andb_prop in Hia. destruct Hia as [Hidstart Hallidc].
  cbn [lex_aux String.append].
  rewrite (is_idstart_not_space _ Hidstart), Hidstart.
  replace (scan_id (String c0 (s0 ++ rest))) with (String c0 s0, rest)
    by (symmetry; apply (scan_id_app (String c0 s0) rest Hallidc Hclean)).
  rewrite (lex_ident_go (String c0 s0) Hs).
  assert (Hle : S (String.length rest) <= f) by (cbn in Hfuel; lia).
  rewrite (lex_aux_mono _ _ _ _ Hrest Hle). reflexivity.
Qed.

(** Digit-shape facts for the integer leaf (re-proved; the originals died in the SRaw teardown). *)
Lemma is_dec_char_dec_digit : forall n, (n < 10)%nat -> is_dec_char (dec_digit n) = true.
Proof.
  intros n Hn. unfold dec_digit, is_dec_char.
  rewrite Ascii.nat_ascii_embedding by lia.
  apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

Lemma all_dec_z_digits : forall fuel z acc, (0 <= z)%Z -> all_dec acc = true ->
  all_dec (z_digits fuel z acc) = true.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hz Hacc; [ exact Hacc | ].
  cbn [z_digits].
  assert (Hd : is_dec_char (dec_digit (Z.to_nat (z mod 10))) = true).
  { apply is_dec_char_dec_digit.
    assert (0 <= z mod 10 < 10)%Z by (apply Z.mod_pos_bound; lia). lia. }
  destruct (z / 10 =? 0)%Z.
  - cbn [all_dec]. rewrite Hd. exact Hacc.
  - apply IH; [ apply Z.div_pos; lia | cbn [all_dec]; rewrite Hd; exact Hacc ].
Qed.

Lemma is_dec_char_not_idstart : forall c, is_dec_char c = true -> is_idstart c = false.
Proof.
  intros c H. unfold is_dec_char in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1, H2. unfold is_idstart; cbv zeta.
  assert (E1 : Nat.leb 65 (nat_of_ascii c) = false) by (apply Nat.leb_gt; lia).
  assert (E2 : Nat.leb 97 (nat_of_ascii c) = false) by (apply Nat.leb_gt; lia).
  assert (E3 : Nat.eqb (nat_of_ascii c) 95 = false) by (apply Nat.eqb_neq; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

Lemma is_dec_char_not_space : forall c, is_dec_char c = true -> is_space c = false.
Proof.
  intros c H. unfold is_dec_char in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1. unfold is_space.
  destruct (Ascii.eqb c (ascii_of_nat 32)) eqn:E; [ | reflexivity ].
  exfalso. apply Ascii.eqb_eq in E. subst c.
  rewrite Ascii.nat_ascii_embedding in H1 by lia. lia.
Qed.

(** [z_digits] (with [S]-fuel from an empty accumulator) is non-empty — every print_Z digit run has a
    leading digit, so the lexer's first-char dispatch sees a [is_dec_char]. *)
Lemma z_digits_acc_ne : forall f z acc, acc <> EmptyString -> z_digits f z acc <> EmptyString.
Proof.
  induction f as [ | f IH ]; intros z acc Hacc; [ exact Hacc | ].
  cbn [z_digits]. destruct (z / 10 =? 0)%Z; [ discriminate | apply IH; discriminate ].
Qed.

Lemma z_digits_S_ne : forall f z, z_digits (S f) z EmptyString <> EmptyString.
Proof.
  intros f z. cbn [z_digits]. destruct (z / 10 =? 0)%Z; [ discriminate | apply z_digits_acc_ne; discriminate ].
Qed.

(** Lexing a non-empty all-decimal run [D] (no leading '-') yields [TInt (parse_Z D)] then [rest]. *)
Lemma lex_pos_dec : forall D rest fuel tr,
  all_dec D = true -> D <> EmptyString -> clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length D + String.length rest) <= fuel ->
  lex_aux fuel (D ++ rest) = Some (TInt (parse_Z D) :: tr).
Proof.
  intros D rest fuel tr Hdec Hne Hclean Hrest Hfuel.
  destruct D as [ | d0 D' ]; [ contradiction | ].
  cbn [all_dec] in Hdec. apply andb_prop in Hdec. destruct Hdec as [Hd0 HD'].
  destruct fuel as [ | f ]; [ cbn in Hfuel; lia | ].
  assert (HdecD : all_dec (String d0 D') = true) by (cbn [all_dec]; rewrite Hd0; exact HD').
  cbn [lex_aux String.append].
  rewrite (is_dec_char_not_space _ Hd0), (is_dec_char_not_idstart _ Hd0), Hd0.
  replace (scan_digits (String d0 (D' ++ rest))) with (String d0 D', rest)
    by (symmetry; change (String d0 (D' ++ rest)) with ((String d0 D') ++ rest);
        apply (scan_digits_app (String d0 D') rest HdecD Hclean)).
  assert (Hle : S (String.length rest) <= f) by (cbn in Hfuel; lia).
  rewrite (lex_aux_mono _ _ _ _ Hrest Hle). reflexivity.
Qed.

(** Lexing a NEGATIVE literal ['-' ++ D] (D a non-empty all-decimal run) yields [TInt (parse_Z ('-'++D))]
    via the lexer's negative-literal branch (binary '-' is always SPACED in the printer, so an unspaced
    '-'+digit is unambiguously a literal). *)
Lemma lex_neg_dec : forall D rest fuel tr,
  all_dec D = true -> D <> EmptyString -> clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (S (String.length D) + String.length rest) <= fuel ->
  lex_aux fuel (String (ch 45) D ++ rest) = Some (TInt (parse_Z (String (ch 45) D)) :: tr).
Proof.
  intros D rest fuel tr Hdec Hne Hclean Hrest Hfuel.
  destruct D as [ | d0 D' ]; [ contradiction | ].
  cbn [all_dec] in Hdec. apply andb_prop in Hdec. destruct Hdec as [Hd0 HD'].
  destruct fuel as [ | f ]; [ cbn in Hfuel; lia | ].
  assert (HdecD : all_dec (String d0 D') = true) by (cbn [all_dec]; rewrite Hd0; exact HD').
  cbn [lex_aux String.append].
  replace (is_space (ch 45)) with false by reflexivity.
  replace (is_idstart (ch 45)) with false by reflexivity.
  replace (is_dec_char (ch 45)) with false by reflexivity.
  replace (Ascii.eqb (ch 45) (ch 45)) with true by reflexivity.
  rewrite Hd0.
  replace (scan_digits (String d0 (D' ++ rest))) with (String d0 D', rest)
    by (symmetry; change (String d0 (D' ++ rest)) with ((String d0 D') ++ rest);
        apply (scan_digits_app (String d0 D') rest HdecD Hclean)).
  assert (Hle : S (String.length rest) <= f) by (cbn in Hfuel; lia).
  rewrite (lex_aux_mono _ _ _ _ Hrest Hle). reflexivity.
Qed.

(** LEAF (integer): lexing [gprint (EInt z) ++ rest = print_Z z ++ rest] yields [TInt z] then [rest].
    Case on [print_Z]'s shape (0 / positive digits / '-'+digits) via the reflect views (which also reduce
    the [if]s); recover [z] from the scanned run by [print_parse_Z]. *)
Lemma lex_gprint_int : forall z rest fuel tr,
  clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length (print_Z z) + String.length rest) <= fuel ->
  lex_aux fuel (print_Z z ++ rest) = Some (TInt z :: tr).
Proof.
  intros z rest fuel tr Hclean Hrest Hfuel.
  replace (TInt z) with (TInt (parse_Z (print_Z z))) by (rewrite print_parse_Z; reflexivity).
  unfold print_Z in *.
  destruct (Z.eqb_spec z 0) as [Heq | Hne].
  - apply lex_pos_dec; [ reflexivity | discriminate | exact Hclean | exact Hrest | exact Hfuel ].
  - destruct (Z.ltb_spec z 0) as [Hlt | Hge].
    + change (("-" ++ z_digits (digit_fuel (- z)) (- z) "")%string)
        with (String (ch 45) (z_digits (digit_fuel (- z)) (- z) "")) in *.
      apply lex_neg_dec;
        [ apply all_dec_z_digits; [ lia | reflexivity ]
        | unfold digit_fuel; apply z_digits_S_ne | exact Hclean | exact Hrest | exact Hfuel ].
    + apply lex_pos_dec;
        [ apply all_dec_z_digits; [ lia | reflexivity ]
        | unfold digit_fuel; apply z_digits_S_ne | exact Hclean | exact Hrest | exact Hfuel ].
Qed.

(** BINOP SEAM: [binop_text o] is [" op "] (spaced both sides), so lexing [binop_text o ++ X] skips the
    leading space, lexes the operator to [op_token o], skips the trailing space, and continues on [X] —
    3 lexer steps, then [X].  The trailing space isolates [X] (no constraint on its head). *)
Lemma lex_binop_app : forall o X fuel tX,
  lex_aux (S (String.length X)) X = Some tX ->
  S (String.length (binop_text o) + String.length X) <= fuel ->
  lex_aux fuel (binop_text o ++ X) = Some (op_token o :: tX).
Proof.
  intros o X fuel tX HX Hfuel.
  destruct o; cbn [binop_text] in Hfuel;
    do 3 (destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ]);
    cbn;
    rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia);
    reflexivity.
Qed.

(** Single-char delimiter seams: '(' -> TLP, ')' -> TRP (one lexer step), and the [UNeg] prefix "-(" ->
    TMinus, TLP (two steps — '-' followed by '(' is NOT a negative literal, so it lexes as TMinus). *)
Lemma lex_lparen_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 40) X) = Some (TLP :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

Lemma lex_rparen_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 41) X) = Some (TRP :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

Lemma lex_minuslp_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (S (String.length X))) <= fuel ->
  lex_aux fuel (String (ch 45) (String (ch 40) X)) = Some (TMinus :: TLP :: tX).
Proof.
  intros X fuel tX HX Hfuel. do 2 (destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ]).
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

(** BARE-UNOP SEAM (after the [gprint] change to always parenthesise a bare-unary operand): [unop_text o]
    (o <> UNeg) is a single char ['!'/'^'/'*'/'&'] ALWAYS followed by '(' — a CONCRETE char that can never
    maximal-munch into a 2-char operator — so it lexes to [prefix_token o] then TLP then [X].  No
    first-char side condition is needed because the next char is fixed. *)
Lemma lex_unop_lp_app : forall o X fuel tX,
  o <> UNeg ->
  lex_aux (S (String.length X)) X = Some tX ->
  S (S (S (String.length X))) <= fuel ->
  lex_aux fuel (unop_text o ++ String (ch 40) X) = Some (prefix_token o :: TLP :: tX).
Proof.
  intros o X fuel tX HoNeg HX Hfuel.
  destruct o; try (exfalso; apply HoNeg; reflexivity);
    do 2 (destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ]);
    cbn; rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia); reflexivity.
Qed.

Lemma length_app : forall a b, String.length (a ++ b) = String.length a + String.length b.
Proof. induction a as [ | c a' IH ]; intro b; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

(** Every [binop_text] starts with a space, so the seam after it is clean. *)
Lemma clean_start_binop : forall o X, clean_start (binop_text o ++ X) = true.
Proof. destruct o; reflexivity. Qed.

End Front.

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

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_float_hex print_sep nominal_type_ident.
