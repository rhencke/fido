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

(** ============================================================================
    ---- EXPRESSIONS: OPERATOR PRECEDENCE ---- the first STRUCTURAL (recursive) piece of the printer to
    move into Rocq.  [go.ml]'s [pp_prec] renders a binary-operator tree, inserting parentheses ONLY
    where an operand's operator binds LOOSER than its context — get this wrong and [(a+b)*c] misprints
    as [a+b*c], silently changing the program's meaning.  This is the hardest correctness property of the
    structural printer, so it is the right first target.

    [GoExpr] models the tree the plugin assembles: [GERaw s] is a pre-rendered ATOM — an operand the
    plugin already printed (a literal, variable, call, field access): atomic, binds tightest, never needs
    wrapping — and [GEBin p op l r] is a LEFT-ASSOCIATIVE binary operator at precedence level [p] (lower
    [p] = looser).  [print_prec ctx e] renders [e] where the context demands precedence >= [ctx]: a
    [GEBin] at level [p] is parenthesized exactly when [p < ctx].  The operands recurse at [p] (left) and
    [S p] (right, one tighter — left-associativity), MIRRORING [pp_prec] byte-for-byte. *)
Inductive GoExpr : Type :=
  | GERaw : string -> GoExpr
  | GEBin : nat -> string -> GoExpr -> GoExpr -> GoExpr.

Fixpoint print_prec (ctx : nat) (e : GoExpr) : string :=
  match e with
  | GERaw s => s
  | GEBin p op l r =>
      let inner := (print_prec p l ++ op ++ print_prec (S p) r)%string in
      if Nat.ltb p ctx then ("(" ++ inner ++ ")")%string else inner
  end.

(** CHARACTERIZATION — [print_prec]'s exact behaviour, the basis of the safety proof below and of the
    byte-identical claim against [pp_prec]: an atom prints verbatim; a binop wraps iff [p < ctx]. *)
Lemma print_prec_raw : forall ctx s, print_prec ctx (GERaw s) = s.
Proof. reflexivity. Qed.
Lemma print_prec_unwrapped : forall p op l r ctx, Nat.ltb p ctx = false ->
  print_prec ctx (GEBin p op l r) = (print_prec p l ++ op ++ print_prec (S p) r)%string.
Proof. intros p op l r ctx H. cbn [print_prec]. rewrite H. reflexivity. Qed.
Lemma print_prec_wrapped : forall p op l r ctx, Nat.ltb p ctx = true ->
  print_prec ctx (GEBin p op l r) = ("(" ++ (print_prec p l ++ op ++ print_prec (S p) r) ++ ")")%string.
Proof. intros p op l r ctx H. cbn [print_prec]. rewrite H. reflexivity. Qed.

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

(** A well-bracketed-leaves predicate over the tree: every atom and operator is balanced. *)
Fixpoint wf (e : GoExpr) : Prop :=
  match e with
  | GERaw s => balanced s
  | GEBin _ op l r => balanced op /\ wf l /\ wf r
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
Lemma print_prec_depth_nneg : forall e ctx d, (0 <= d)%Z -> wf e ->
  depth d (print_prec ctx e) = d /\ nneg d (print_prec ctx e).
Proof.
  induction e as [ s | p op l IHl r IHr ]; intros ctx d Hd Hwf.
  - (* GERaw s *) cbn [print_prec wf] in *. destruct Hwf as [Hz Hn]. split.
    + rewrite depth_shift, Hz. lia.
    + apply (nneg_raise s 0 d); [ lia | exact Hn ].
  - (* GEBin p op l r *)
    cbn [wf] in Hwf. destruct Hwf as [Hop [Hwl Hwr]]. destruct Hop as [Hopz Hopn].
    destruct (IHl p d Hd Hwl) as [Hld Hln]. destruct (IHr (S p) d Hd Hwr) as [Hrd Hrn].
    (* the inner string [l ++ op ++ r] returns to [d] and never dips below it *)
    assert (Hinner_d : depth d (print_prec p l ++ op ++ print_prec (S p) r) = d).
    { rewrite !depth_app, Hld, (depth_shift op d), Hopz, Z.add_0_r, Hrd. reflexivity. }
    assert (Hinner0 : depth 0 (print_prec p l ++ op ++ print_prec (S p) r) = 0%Z)
      by (rewrite depth_shift in Hinner_d; lia).
    assert (Hinner_n : nneg d (print_prec p l ++ op ++ print_prec (S p) r)).
    { rewrite !nneg_app. split; [ exact Hln | ]. rewrite Hld. split.
      - apply (nneg_raise op 0 d); [ lia | exact Hopn ].
      - rewrite (depth_shift op d), Hopz, Z.add_0_r. exact Hrn. }
    destruct (Nat.ltb p ctx) eqn:E.
    + (* wrapped: "(" ++ inner ++ ")" *)
      rewrite (print_prec_wrapped p op l r ctx E). split.
      * rewrite depth_wrap. exact Hinner_d.
      * apply nneg_wrap; [ lia | exact Hinner0 | exact Hinner_n ].
    + (* not wrapped *)
      rewrite (print_prec_unwrapped p op l r ctx E).
      split; [ exact Hinner_d | exact Hinner_n ].
Qed.

Theorem print_prec_balanced : forall e ctx, wf e -> balanced (print_prec ctx e).
Proof.
  intros e ctx Hwf. unfold balanced.
  destruct (print_prec_depth_nneg e ctx 0 (Z.le_refl 0) Hwf) as [Hd Hn].
  split; assumption.
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

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_prec print_sep.
