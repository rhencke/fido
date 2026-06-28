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
               | _    => (unop_text o ++ (if is_un e then ("(" ++ gprint 0 e ++ ")")%string
                                          else gprint 6 e))%string
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
               | _    => prefix_token o :: (if is_un e then TLP :: (gtokens 0 e ++ TRP :: nil)
                                            else gtokens 6 e)
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
