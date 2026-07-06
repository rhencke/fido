(** ==================================================================================================
    GoNumeric — the AXIOM-FREE numeric model: Go's integer types as GENUINELY DISTINCT
    [Z]-carried records (fixed-width [GoI8]..[GoU64], full-width [GoI64]/[GoU64], platform
    [GoInt]/[GoUint]) and Go's floats on Rocq's [spec_float] (every operation a computable
    [Z]-arithmetic definition; no [PrimInt63]/[PrimFloat] anywhere).  Mined out of the frozen
    builtins.v monolith (plans/builtins-split.md wave 1); the DAG bottom — nothing here touches
    [IO]/[World].  ================================================================================ *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import StrictProp.   (* Squash: range invariants in SProp — wrapper equality decided by the carrier alone, no axiom *)

(** Signed integer types.
    [GoInt] models Go's platform [int] as a GENUINELY DISTINCT [Z]-carried record (defined just
    below the [GoI64] machinery it shares) — NOT a transparent alias.  Carried in the int64 range
    [[-2^63, 2^63)] exactly like [GoI64], so [+]/[-]/[*]/[/]/[%] are two's-complement-faithful and
    wrap at the true [2^63].  The 64-bit width choice is the only residual platform assumption
    (shared with [GoUint]).  Renders to Go [int]; the wrapper unboxes to its [Z] carrier at
    extraction, so a [GoInt] LITERAL is the proof-carrying [int_lit z (pf : in_i64 z)]
    (NoInline'd, plugin-folded), never a raw ctor (which would render the bare carrier,
    mis-typed [int64]).

    DISTINCTNESS is load-bearing: a transparent alias is freely cross-assignable in Rocq while the
    plugin renders each integer type as a DISTINCT Go type — [fun (x:GoInt) => (x:GoUint)] would
    extract to INVALID Go.  As distinct records [GoInt <> GoUint <> GoI64], that confusion is
    UNREPRESENTABLE.  One Rocq type per Go type: [int8]…[uint64] are [GoI8]/…/[GoU64], platform
    [uint] is [GoUint], [GoRune] is [GoI32]. *)
(* [GoInt] (the record) + [intwrap] are defined just after [i64wrap] below (they need [in_i64_wrap64]);
   [TInt64 : GoTypeTag GoInt] indexes it.  [int_lit]/[int_add]/… live with the [GoI64] ops. *)
(* [GoByte] (Go's [byte] = an alias for [uint8]) is bound after [GoU8] below, to
   the FAITHFUL [GoU8] record (NOT a bare-int placeholder). *)


(** Floating-point types — AXIOM-FREE, modelled on Rocq's [spec_float].
    [GoFloat64] is [SpecFloat.spec_float] — the IEEE-754 binary inductive over [Z] — so EVERY float
    operation is a COMPUTABLE [Z]-arithmetic definition ([SFadd]/[SFmul]/[SFdiv]/[SFcompare]/…)
    with NO primitive-float axiom in the trust base.  [GoFloat32] is an ABSTRACT binary32 wrapper
    over a [spec_float].  At extraction [GoFloat64]/[GoFloat32] → Go [float64]/[float32]; the SF
    ops lower BY NAME to the native Go float operators, and a CANONICAL [spec_float] LITERAL
    [S754_finite s m e] (= ±m·2^e) lowers to the EXACT Go hex-float literal [±0x<m>p<e>]
    (a NONCANONICAL literal is REJECTED at extraction — the plugin gates on the extracted
    [SpecFloat.bounded], because [SFeqb]/[SFcompare] are representation-sensitive). *)
From Stdlib Require Export Floats.SpecFloat.   (* Export: [spec_float] + its [S754_*] ctors visible downstream *)
From Fido Require Import digits.
(* [BinInt] gives [Z] for the FULL-WIDTH integer models; [Decimal] backs the float literal
   Number Notation.  No [Open Scope Z_scope] — [Z] use stays qualified ([Z.add]/…, [%Z] literals). *)
From Stdlib Require Import BinInt Decimal.
Notation GoFloat64 := spec_float.

(** [renorm prec emax v] re-expresses [v] in the UNIQUE canonical [(prec,emax)] representation (via
    [binary_normalize]).  This matters because [SFcompare]/[SFeqb] are REPRESENTATION-sensitive (they
    assume a canonical operand), so every [GoFloat64] must be binary64-canonical and every [GoFloat32]
    (the raw [S754_finite] constructor stays exported — the model's ops/literals produce canonical
    forms, and the PLUGIN refuses to extract a noncanonical literal via [SpecFloat.bounded])
    binary32-canonical.  The float ops/literals already output the canonical form for their format;
    [renorm] is needed only where a value CROSSES formats (the f32 round and the f32→f64 widen). *)
Definition cond_Zopp (b : bool) (m : Z) : Z := if b then Z.opp m else m.
Definition renorm (prec emax : Z) (v : spec_float) : spec_float :=
  match v with
  | S754_finite s m e => binary_normalize prec emax (cond_Zopp s (Zpos m)) e false
  | x => x   (* zero / infinity / nan are format-independent *)
  end.
(** The SIGN argument threads INERTLY through [binary_round] — it only reaches the result
    constructors ([shl_align]/[shr_fexp]/rounding are sign-blind), so NEGATION commutes with
    canonicalization.  NO window premise — underflow-to-zero, overflow-to-infinity
    and the nan guard all carry the flipped sign consistently. *)
Lemma binary_round_opp : forall prec emax s m e,
  binary_round prec emax (negb s) m e = SFopp (binary_round prec emax s m e).
Proof.
  intros prec emax s m e. unfold binary_round.
  match goal with |- context [shl_align ?a ?b ?c] =>
    destruct (shl_align a b c) as [mz ez] end.
  unfold binary_round_aux.
  match goal with |- context [shr_fexp ?p ?q ?a ?b ?c] =>
    destruct (shr_fexp p q a b c) as [mrs' e'] end.
  match goal with |- context [shr_fexp ?p ?q ?a ?b ?c] =>
    destruct (shr_fexp p q a b c) as [mrs'' e''] end.
  destruct (shr_m mrs'') as [|p'|p']; [reflexivity| |reflexivity].
  destruct (Z.leb e'' (Z.sub emax prec)); reflexivity.
Qed.
(** ---- [binary_round] EXACTNESS on the in-window class — an in-window
    mantissa/exponent comes back as the CANONICAL
    finite of the SAME value, NO rounding.  All positive/Z arithmetic on SpecFloat's own
    definitions: an exact left shift adds digits one-for-one ([digits2_pos_iter_xO]), so
    digits+exponent is SHIFT-INVARIANT, the [fexp] target reproduces itself, and both [shr_fexp]
    passes are ZERO shifts at [loc_Exact] ([round_nearest_even] is the identity there). *)
Lemma digits2_pos_iter_xO : forall d m,
  digits2_pos (Pos.iter xO m d) = Pos.add d (digits2_pos m).
Proof.
  induction d using Pos.peano_ind; intro m.
  - cbn [Pos.iter digits2_pos]. now rewrite Pos.add_1_l.
  - rewrite Pos.iter_succ. cbn [digits2_pos]. rewrite IHd, Pos.add_succ_l. reflexivity.
Qed.
Lemma iter_xO_val : forall d m,
  Zpos (Pos.iter xO m d) = (Zpos m * 2 ^ Zpos d)%Z.
Proof.
  induction d using Pos.peano_ind; intro m.
  - cbn [Pos.iter]. rewrite Z.pow_1_r. lia.
  - rewrite Pos.iter_succ, Pos2Z.inj_succ, Z.pow_succ_r by lia.
    change (Zpos (xO (Pos.iter xO m d))) with (2 * Zpos (Pos.iter xO m d))%Z.
    rewrite IHd. lia.
Qed.
Lemma shl_align_snd : forall m e T, (T <= e)%Z -> snd (shl_align m e T) = T.
Proof.
  intros m e T H. unfold shl_align.
  destruct (Z.sub T e) as [|p|d] eqn:E; cbn [snd].
  - assert (T - e = 0)%Z by exact E. lia.
  - exfalso. assert (T - e = Z.pos p)%Z by exact E. lia.
  - reflexivity.
Qed.
Lemma shl_align_digits : forall m e T,
  (T <= e)%Z ->
  (Zpos (digits2_pos (fst (shl_align m e T))) + snd (shl_align m e T)
   = Zpos (digits2_pos m) + e)%Z.
Proof.
  intros m e T H. unfold shl_align.
  destruct (Z.sub T e) as [|p|d] eqn:E; cbn [fst snd].
  - reflexivity.
  - exfalso. assert (T - e = Z.pos p)%Z by exact E. lia.
  - rewrite digits2_pos_iter_xO, Pos2Z.inj_add.
    assert (T - e = Z.neg d)%Z by exact E. lia.
Qed.
(** the aligned mantissa carries EXACTLY the original value ([m * 2^e = mz * 2^T]) *)
Lemma shl_align_fst_val : forall m e T,
  (T <= e)%Z ->
  Zpos (fst (shl_align m e T)) = (Zpos m * 2 ^ (e - T))%Z.
Proof.
  intros m e T H. unfold shl_align.
  destruct (Z.sub T e) as [|p|d] eqn:E; cbn [fst].
  - assert (T - e = 0)%Z by exact E.
    replace (e - T)%Z with 0%Z by lia. rewrite Z.pow_0_r. lia.
  - exfalso. assert (T - e = Z.pos p)%Z by exact E. lia.
  - rewrite iter_xO_val. assert (T - e = Z.neg d)%Z by exact E.
    replace (e - T)%Z with (Z.pos d) by lia. reflexivity.
Qed.
(** ★ THE EXACTNESS THEOREM: on the in-window class (mantissa within [prec] digits, exponent at
    or above [emin], digits+exponent at most [emax]), [binary_round] returns the CANONICAL finite
    — the shifted mantissa at the [fexp] target — with NO rounding, NO underflow-to-zero, NO
    overflow.  Combined with [shl_align_fst_val] the value is preserved exactly. *)
Lemma binary_round_exact : forall prec emax s m e,
  (Zpos (digits2_pos m) <= prec)%Z ->
  (emin prec emax <= e)%Z ->
  (Zpos (digits2_pos m) + e <= emax)%Z ->
  (2 <= emax)%Z ->
  binary_round prec emax s m e
  = S754_finite s
      (fst (shl_align m e (fexp prec emax (Zpos (digits2_pos m) + e))))
      (fexp prec emax (Zpos (digits2_pos m) + e)).
Proof.
  intros prec emax s m e Hd He Hde Hemax.
  assert (HT : (fexp prec emax (Zpos (digits2_pos m) + e) <= e)%Z)
    by (unfold fexp, emin in *; lia).
  assert (Hcap : Z.leb (fexp prec emax (Zpos (digits2_pos m) + e)) (emax - prec) = true)
    by (apply Z.leb_le; unfold fexp, emin in *; lia).
  unfold binary_round.
  pose proof (shl_align_snd m e _ HT) as Hsnd.
  pose proof (shl_align_digits m e _ HT) as Hdig.
  destruct (shl_align m e (fexp prec emax (Zpos (digits2_pos m) + e))) as [mz ez] eqn:Ea.
  cbn [fst snd] in Hsnd, Hdig. subst ez.
  unfold binary_round_aux, shr_fexp.
  cbn [Zdigits2].
  rewrite Hdig, Z.sub_diag.
  cbn [shr shr_record_of_loc shr_m shr_r shr_s loc_of_shr_record round_nearest_even Zdigits2].
  rewrite Hdig, Z.sub_diag.
  cbn [shr shr_record_of_loc shr_m].
  rewrite Hcap. reflexivity.
Qed.
Lemma shl_align_id : forall m e, shl_align m e e = (m, e).
Proof. intros. unfold shl_align. rewrite Z.sub_diag. reflexivity. Qed.
(** digits vs magnitude — the bridge from a magnitude window ([|m| < 2^k], the gate's spelling)
    to [binary_round_exact]'s digit premise: every positive needs at least [2^(digits-1)]. *)
Lemma digits2_pos_lower : forall p, (2 ^ Zpos (digits2_pos p) <= 2 * Zpos p)%Z.
Proof.
  (* every arithmetic step keeps [Z.pow] OUT of lia's goals (pow terms stay under explicit
     monotonicity lemmas — zify's pow handling is not assumed) *)
  induction p; cbn [digits2_pos].
  - rewrite Pos2Z.inj_succ, Z.pow_succ_r by apply Pos2Z.is_nonneg.
    apply Z.le_trans with (m := (2 * (2 * Zpos p))%Z).
    + apply (Zmult_le_compat_l _ _ 2); [exact IHp | lia].
    + rewrite Pos2Z.inj_xI. lia.
  - rewrite Pos2Z.inj_succ, Z.pow_succ_r by apply Pos2Z.is_nonneg.
    apply Z.le_trans with (m := (2 * (2 * Zpos p))%Z).
    + apply (Zmult_le_compat_l _ _ 2); [exact IHp | lia].
    + rewrite Pos2Z.inj_xO. lia.
  - cbn. lia.
Qed.
(** ---- MUL groundwork: the digit LOWER bound of a product, and [SFmul]'s
    [binary_round_aux]-on-the-raw-product arm rewritten as [binary_round] when the [fexp]
    target is at or above the raw exponent (then the inlined [shl_align] is the identity) — for
    canonical operand renders the target premise is derivable, so the wide bridge applies. *)
Lemma digits2_pos_upper : forall p, (Zpos p < 2 ^ Zpos (digits2_pos p))%Z.
Proof.
  induction p as [q IH|q IH|]; cbn [digits2_pos].
  - rewrite Pos2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Pos2Z.inj_xI. lia.
  - rewrite Pos2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Pos2Z.inj_xO. lia.
  - cbn. lia.
Qed.
Lemma digits2_pos_mul_lower : forall p q,
  (Zpos (digits2_pos p) + Zpos (digits2_pos q) - 1
   <= Zpos (digits2_pos (Pos.mul p q)))%Z.
Proof.
  intros p q.
  pose proof (digits2_pos_lower p) as Hp.
  pose proof (digits2_pos_lower q) as Hq.
  pose proof (digits2_pos_upper (Pos.mul p q)) as Hu.
  rewrite Pos2Z.inj_mul in Hu.
  set (dp := Zpos (digits2_pos p)) in *.
  set (dq := Zpos (digits2_pos q)) in *.
  set (dpq := Zpos (digits2_pos (Pos.mul p q))) in *.
  destruct (Z.le_gt_cases (dp + dq - 1) dpq) as [Hle|Hgt]; [exact Hle|exfalso].
  assert (Hpow : (2 ^ dpq <= 2 ^ (dp + dq - 2))%Z)
    by (apply Z.pow_le_mono_r; lia).
  assert (Hsplit : (2 ^ (dp + dq - 2) * 4 = 2 ^ dp * 2 ^ dq)%Z).
  { change 4%Z with (2 ^ 2)%Z. rewrite <- !Z.pow_add_r by lia.
    f_equal. lia. }
  assert (Hp0 : (0 < 2 ^ dp)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq0 : (0 < 2 ^ dq)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (HAB : (2 ^ dp * 2 ^ dq <= (2 * Zpos p) * (2 * Zpos q))%Z)
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (E : ((2 * Zpos p) * (2 * Zpos q) = 4 * (Zpos p * Zpos q))%Z) by ring.
  lia.
Qed.
Lemma binary_round_aux_of_round : forall prec emax s q e,
  (e <= fexp prec emax (Zpos (digits2_pos q) + e))%Z ->
  binary_round_aux prec emax s (Zpos q) e loc_Exact
  = binary_round prec emax s q e.
Proof.
  intros prec emax s q e He.
  unfold binary_round, shl_align.
  destruct (fexp prec emax (Zpos (digits2_pos q) + e) - e)%Z eqn:E;
    [reflexivity | reflexivity | exfalso; lia].
Qed.

Lemma digits2_pos_le_of_lt_pow : forall p k,
  (0 <= k)%Z -> (Zpos p < 2 ^ k)%Z -> (Zpos (digits2_pos p) <= k)%Z.
Proof.
  intros p k Hk Hlt.
  pose proof (digits2_pos_lower p) as Hlo.
  destruct (Z.leb_spec (Zpos (digits2_pos p)) k) as [|Hgt]; [assumption|].
  exfalso.
  assert (Hmono : (2 ^ (k + 1) <= 2 ^ Zpos (digits2_pos p))%Z)
    by (apply Z.pow_le_mono_r; lia).
  rewrite Z.pow_add_r in Hmono by lia.
  rewrite Z.pow_1_r in Hmono.
  assert (Hp2 : (2 * Zpos p < 2 * 2 ^ k)%Z)
    by (apply Zmult_lt_compat_l; [lia | exact Hlt]).
  apply (Z.lt_irrefl (2 ^ k * 2)%Z).
  eapply Z.le_lt_trans; [exact Hmono|].
  eapply Z.le_lt_trans; [exact Hlo|].
  replace (2 ^ k * 2)%Z with (2 * 2 ^ k)%Z by apply Z.mul_comm.
  exact Hp2.
Qed.

(** ---- exact-DIV groundwork.  [SFdiv]'s finite arm scales the dividend mantissa
    left ([SFdiv_core_binary]'s [s]-shift), divides by the divisor mantissa with
    [Z.div_eucl], and records the remainder as a LOCATION — on the fold-accepted class the
    remainder is ZERO ([m2 | m1] transports through the canonical-render shifts), the
    location is [loc_Exact], and the aux arm reduces to [binary_round] again. *)
Lemma digits2_pos_mul_upper : forall p q,
  (Zpos (digits2_pos (Pos.mul p q)) <= Zpos (digits2_pos p) + Zpos (digits2_pos q))%Z.
Proof.
  intros p q.
  apply digits2_pos_le_of_lt_pow; [lia|].
  pose proof (digits2_pos_upper p) as Hp.
  pose proof (digits2_pos_upper q) as Hq.
  rewrite Pos2Z.inj_mul, Z.pow_add_r by lia.
  apply Z.mul_lt_mono_nonneg; lia.
Qed.
Lemma digits2_pos_ge_of_pow_le : forall p k,
  (0 <= k)%Z -> (2 ^ k <= Zpos p)%Z -> (k + 1 <= Zpos (digits2_pos p))%Z.
Proof.
  intros p k Hk Hle.
  destruct (Z.le_gt_cases (k + 1) (Zpos (digits2_pos p))) as [H|H]; [exact H|exfalso].
  pose proof (digits2_pos_upper p) as Hu.
  assert (Hm : (2 ^ Zpos (digits2_pos p) <= 2 ^ k)%Z) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.
(** an exact power-of-two shift adds its exponent to the digit count, on the nose *)
Lemma digits2_pos_shift : forall p k q,
  (0 <= k)%Z -> Zpos q = (Zpos p * 2 ^ k)%Z ->
  Zpos (digits2_pos q) = (Zpos (digits2_pos p) + k)%Z.
Proof.
  intros p k q Hk Hq.
  pose proof (digits2_pos_lower p) as Hlp.
  pose proof (digits2_pos_upper p) as Hup.
  assert (Hpk : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hge : (Zpos (digits2_pos p) + k - 1 + 1 <= Zpos (digits2_pos q))%Z).
  { apply digits2_pos_ge_of_pow_le; [lia|].
    rewrite Hq.
    replace (Zpos (digits2_pos p) + k - 1)%Z
      with ((Zpos (digits2_pos p) - 1) + k)%Z by lia.
    rewrite Z.pow_add_r by lia.
    apply Z.mul_le_mono_nonneg_r; [lia|].
    assert (E : (2 ^ Zpos (digits2_pos p) = 2 * 2 ^ (Zpos (digits2_pos p) - 1))%Z).
    { replace (Zpos (digits2_pos p)) with (Z.succ (Zpos (digits2_pos p) - 1)) at 1 by lia.
      rewrite Z.pow_succ_r by lia. reflexivity. }
    lia. }
  assert (Hlt : (Zpos (digits2_pos q) <= Zpos (digits2_pos p) + k)%Z).
  { apply digits2_pos_le_of_lt_pow; [lia|].
    rewrite Hq, Z.pow_add_r by lia. nia. }
  lia.
Qed.
Lemma div_eucl_exact : forall a b,
  (0 < b)%Z -> (b | a)%Z -> Z.div_eucl a b = ((a / b)%Z, 0%Z).
Proof.
  intros a b Hb Hdiv.
  rewrite (surjective_pairing (Z.div_eucl a b)).
  f_equal.
  destruct (Z.mod_divide a b ltac:(lia)) as [_ Hmd].
  exact (Hmd Hdiv).
Qed.
Lemma new_location_exact : forall nb,
  new_location nb 0%Z = loc_Exact.
Proof.
  intros nb. unfold new_location, new_location_even, new_location_odd.
  destruct (Z.even nb); reflexivity.
Qed.
(** [renorm] IDEMPOTENCE on the in-window class: [binary_round]'s output is already canonical —
    re-normalizing it is the identity (its digits+exponent equals the input's, so the [fexp]
    target reproduces itself and the re-alignment is [shl_align_id]) — the idempotence the
    f32 wrappers consume (they re-round through [f32_of_f64]). *)
Lemma renorm_binary_round_idem : forall prec emax s m e,
  (Zpos (digits2_pos m) <= prec)%Z ->
  (emin prec emax <= e)%Z ->
  (Zpos (digits2_pos m) + e <= emax)%Z ->
  (2 <= emax)%Z ->
  renorm prec emax (binary_round prec emax s m e) = binary_round prec emax s m e.
Proof.
  intros prec emax s m e Hd He Hde Hemax.
  assert (HT : (fexp prec emax (Zpos (digits2_pos m) + e) <= e)%Z)
    by (unfold fexp, emin in *; lia).
  rewrite (binary_round_exact prec emax s m e Hd He Hde Hemax).
  pose proof (shl_align_snd m e _ HT) as Hsnd.
  pose proof (shl_align_digits m e _ HT) as Hdig.
  destruct (shl_align m e (fexp prec emax (Zpos (digits2_pos m) + e))) as [mz ez] eqn:Ea.
  cbn [fst snd] in Hsnd, Hdig |- *. subst ez.
  unfold renorm.
  assert (Hd2 : (Zpos (digits2_pos mz) <= prec)%Z) by (unfold fexp, emin in *; lia).
  assert (He2 : (emin prec emax <= fexp prec emax (Zpos (digits2_pos m) + e))%Z)
    by (unfold fexp, emin in *; lia).
  assert (Hde2 : (Zpos (digits2_pos mz) + fexp prec emax (Zpos (digits2_pos m) + e) <= emax)%Z)
    by lia.
  destruct s; cbn [cond_Zopp Z.opp binary_normalize];
    rewrite (binary_round_exact prec emax _ mz _ Hd2 He2 Hde2 Hemax);
    rewrite Hdig, shl_align_id; reflexivity.
Qed.
(** ---- RIGHT-SHIFT-THROUGH-ZEROS exactness: shifting
    a mantissa right through its own appended zero bits keeps the round/sticky bits FALSE, so
    the location stays exact.  [iter_pos] (SpecFloat's binary-structural iterator) and
    [Pos.iter] are both bridged to [Nat.iter], where the zeros walk is a plain induction. *)
Lemma pos_iter_nat : forall (A : Type) (f : A -> A) (x : A) n,
  Pos.iter f x n = Nat.iter (Pos.to_nat n) f x.
Proof.
  intros A f x n; revert x; induction n using Pos.peano_ind; intro x.
  - reflexivity.
  - rewrite Pos.iter_succ, Pos2Nat.inj_succ. cbn [Nat.iter]. now rewrite IHn.
Qed.
Lemma iter_pos_nat : forall (A : Type) (f : A -> A) n (x : A),
  @SpecFloat.iter_pos A f n x = Nat.iter (Pos.to_nat n) f x.
Proof.
  intros A f; induction n; intro x; cbn [SpecFloat.iter_pos].
  - rewrite 2!IHn, <- Nat.iter_add, <- Nat.iter_succ_r, Pos2Nat.inj_xI.
    f_equal. lia.
  - rewrite 2!IHn, <- Nat.iter_add, Pos2Nat.inj_xO.
    f_equal. lia.
  - reflexivity.
Qed.
Lemma nat_iter_shr1_zeros : forall k m,
  Nat.iter k shr_1 (Build_shr_record (Zpos (Nat.iter k xO m)) false false)
  = Build_shr_record (Zpos m) false false.
Proof.
  induction k; intro m; [reflexivity|].
  rewrite Nat.iter_succ_r.
  change (Nat.iter (S k) xO m) with (xO (Nat.iter k xO m)).
  cbn [shr_1 orb].
  apply IHk.
Qed.
(** exactly-[k] zero bits shifted out by exactly [k] steps: the mantissa's [xO]-chain is
    consumed with the record staying [(…, false, false)] — [loc_Exact] all the way. *)
Lemma iter_pos_shr1_zeros : forall k m,
  @SpecFloat.iter_pos shr_record shr_1 k (Build_shr_record (Zpos (Pos.iter xO m k)) false false)
  = Build_shr_record (Zpos m) false false.
Proof.
  intros k m. rewrite iter_pos_nat, pos_iter_nat. apply nat_iter_shr1_zeros.
Qed.
(** SUBTRACTION is ADDITION of the sign-flipped operand — [SFsub]'s own match agrees with
    [SFadd . SFopp] row by row ([Z.sub] IS [Z.add] of the opposite, definitionally, so even
    the finite arm closes by conversion after the sign split). *)
Lemma SFsub_as_add_opp : forall prec emax x y,
  SFsub prec emax x y = SFadd prec emax x (SFopp y).
Proof.
  intros prec emax x y.
  destruct x as [sx|sx| |sx mx ex]; destruct y as [sy|sy| |sy my ey];
    cbn [SFopp SFsub SFadd]; try reflexivity;
    try (destruct sx; destruct sy; reflexivity);
    try (destruct sy; reflexivity).
Qed.

(** ---- float32 (binary32), SOUND abstract model ----

    Go's [float32] is IEEE binary32.  A [GoFloat32] is carried by a [spec_float] holding a
    binary32-CANONICAL value; [f32_round v := renorm 24 128 v] is round-to-nearest-even at
    binary32, the unique canonical (24,128) form.  Invariant: the proof field [f32ok] witnesses
    the carrier is in the IMAGE of [f32_round] (binary32-representable), so [mkF32 v _] for a
    non-binary32 [v] is unconstructable and every inhabitant enters through a rounding smart
    constructor — widening [f64_of_f32] is SOUND.  ZERO axioms: provenance proofs are [eq_refl].
    At extraction [GoFloat32] erases to Go [float32] and [mkF32]/[f32val] to identity. *)
Definition f32_round (v : spec_float) : spec_float := renorm 24 128 v.
Record GoFloat32 : Type :=
  mkF32 { f32val : spec_float ; f32ok : exists a : spec_float, f32val = f32_round a }.
(** The only way IN: round a binary64 (or a literal) to binary32.  Provenance proof is
    [eq_refl] — the carrier is literally [f32_round a]. *)
Definition f32_of_f64 (a : GoFloat64) : GoFloat32 := mkF32 (f32_round a) (ex_intro _ a eq_refl).
(** A float32 LITERAL rounds at the Rocq boundary (Go rounds a typed constant the same way). *)
Definition f32_lit (a : GoFloat64) : GoFloat32 := f32_of_f64 a.

(** ---- float64 operations (axiom-free, on [spec_float] at binary64 = prec 53, emax 1024) ----
    Arithmetic OUTPUTS the binary64-canonical form given binary64-canonical inputs (so [f64_eqb] /
    ordering are correct).  Lowered BY NAME to the native Go float64 operators; bodies suppressed. *)
Definition f64_add (x y : GoFloat64) : GoFloat64 := SFadd 53 1024 x y.
Definition f64_sub (x y : GoFloat64) : GoFloat64 := SFsub 53 1024 x y.
Definition f64_mul (x y : GoFloat64) : GoFloat64 := SFmul 53 1024 x y.
Definition f64_div (x y : GoFloat64) : GoFloat64 := SFdiv 53 1024 x y.
Definition f64_opp (x : GoFloat64) : GoFloat64 := SFopp x.   (* IEEE sign flip (makes -0.0) *)
Definition f64_abs (x : GoFloat64) : GoFloat64 := SFabs x.
Definition f64_eqb (x y : GoFloat64) : bool := SFeqb x y.
Definition f64_ltb (x y : GoFloat64) : bool := SFltb x y.
Definition f64_leb (x y : GoFloat64) : bool := SFleb x y.

(** Exact [Z] (no rounding) → [spec_float]: mantissa [|z|], exponent 0 — a NON-canonical form, fed
    ONLY to [SFdiv]/[binary_normalize] (which normalise), never stored or compared directly. *)
Definition sf_of_Z (z : Z) : spec_float :=
  match z with Z0 => S754_zero false | Zpos p => S754_finite false p 0 | Zneg p => S754_finite true p 0 end.
(** Exact rational [num/den] → correctly-rounded binary64 (a single [SFdiv] round). *)
Definition f64_of_frac (num den : Z) : GoFloat64 := SFdiv 53 1024 (sf_of_Z num) (sf_of_Z den).

(** Float LITERAL Number Notation: a decimal [i.f] parses to the correctly-rounded binary64
    [spec_float] via [f64_of_frac] (numerator = the digit string [i++f], denominator = [10^(#f)]).
    Self-contained digit fold (no [DecimalZ]).  The notation REDUCES at parse time, so [1.5] becomes
    a concrete [S754_finite false 6755399441055744 (-52)] — which the extractor emits as the exact Go
    hex-float [0x18000000000000p-52] (= 1.5). *)
Fixpoint uint_to_Z (u : Decimal.uint) (acc : Z) : Z :=
  match u with
  | Decimal.Nil => acc
  | Decimal.D0 u => uint_to_Z u (acc*10) | Decimal.D1 u => uint_to_Z u (acc*10+1)
  | Decimal.D2 u => uint_to_Z u (acc*10+2) | Decimal.D3 u => uint_to_Z u (acc*10+3)
  | Decimal.D4 u => uint_to_Z u (acc*10+4) | Decimal.D5 u => uint_to_Z u (acc*10+5)
  | Decimal.D6 u => uint_to_Z u (acc*10+6) | Decimal.D7 u => uint_to_Z u (acc*10+7)
  | Decimal.D8 u => uint_to_Z u (acc*10+8) | Decimal.D9 u => uint_to_Z u (acc*10+9)
  end%Z.
Definition f64_of_decimal (d : Decimal.decimal) : option GoFloat64 :=
  (* [i.f × 10^e] (e = 0 for a plain decimal).  value = (digits i ++ digits f) × 10^(e − #frac). *)
  let '(i, f, e) := match d with
                    | Decimal.Decimal i f => (i, f, 0%Z)
                    | Decimal.DecimalExp i f e =>
                        (i, f, match e with Decimal.Pos u => uint_to_Z u 0 | Decimal.Neg u => Z.opp (uint_to_Z u 0) end)
                    end in
  let '(sign, u) := match i with Decimal.Pos u => (false, u) | Decimal.Neg u => (true, u) end in
  let fd  := Decimal.nb_digits f in
  let mag := (uint_to_Z u 0 * 10 ^ Z.of_nat fd + uint_to_Z f 0)%Z in
  let smag := (if sign then Z.opp mag else mag)%Z in
  let net := (e - Z.of_nat fd)%Z in
  Some (if (0 <=? net)%Z then f64_of_frac (smag * 10 ^ net) 1 else f64_of_frac smag (10 ^ (- net))).
Definition parse_f64 (n : Number.number) : option GoFloat64 :=
  match n with Number.Decimal d => f64_of_decimal d | Number.Hexadecimal _ => None end.
Definition print_f64 (_ : GoFloat64) : option Number.number := None.
Declare Scope go64_scope.
Delimit Scope go64_scope with go64.
Bind Scope go64_scope with spec_float.
Number Notation spec_float parse_f64 print_f64 : go64_scope.
(** Infix float64 arithmetic in [go64_scope] (standard precedence), so demos read [1.5 + 2.25]. *)
Notation "x + y" := (f64_add x y) (at level 50, left associativity) : go64_scope.
Notation "x - y" := (f64_sub x y) (at level 50, left associativity) : go64_scope.
Notation "x * y" := (f64_mul x y) (at level 40, left associativity) : go64_scope.
Notation "x / y" := (f64_div x y) (at level 40, left associativity) : go64_scope.



(* int64/uint64 range predicates + wrap-to-range, hoisted so the GoI64/GoU64 records can carry a
   RANGE invariant.  Z-carried (not int63): int64 = [-2^63, 2^63), uint64 = [0, 2^64). *)
Definition in_i64 (z : Z) : bool :=
  andb (-9223372036854775808 <=? z)%Z (z <? 9223372036854775808)%Z.
Definition wrap64 (z : Z) : Z :=
  (Z.modulo (z + 9223372036854775808) 18446744073709551616 - 9223372036854775808)%Z.
Definition in_u64 (z : Z) : bool :=
  andb (0 <=? z)%Z (z <? 18446744073709551616)%Z.
Definition wrapU64 (z : Z) : Z :=
  Z.modulo z 18446744073709551616%Z.
(* Sub-64 narrow range predicates.  Unsigned [uN] in [[0, 2^N)]; signed [iN] in
   [[-2^(N-1), 2^(N-1))]. *)
Definition in_u8  (z : Z) : bool := andb (0 <=? z)%Z (z <? 256)%Z.
Definition in_u16 (z : Z) : bool := andb (0 <=? z)%Z (z <? 65536)%Z.
Definition in_u32 (z : Z) : bool := andb (0 <=? z)%Z (z <? 4294967296)%Z.
Definition in_i8  (z : Z) : bool := andb (-128 <=? z)%Z (z <? 128)%Z.
Definition in_i16 (z : Z) : bool := andb (-32768 <=? z)%Z (z <? 32768)%Z.
Definition in_i32 (z : Z) : bool := andb (-2147483648 <=? z)%Z (z <? 2147483648)%Z.
(* Signed sub-64 sign-extend onto Z (mirrors [wrap64]): map any [z] into [[-2^(N-1), 2^(N-1))] by
   mod-then-sign-extend; identity on in-range values.  [in_iN_norm] : the result is always in range. *)
Definition i8_norm_z  (z : Z) : Z := (Z.modulo (z + 128) 256 - 128)%Z.
Definition i16_norm_z (z : Z) : Z := (Z.modulo (z + 32768) 65536 - 32768)%Z.
Definition i32_norm_z (z : Z) : Z := (Z.modulo (z + 2147483648) 4294967296 - 2147483648)%Z.
Lemma in_i8_norm  : forall z, in_i8  (i8_norm_z  z) = true.
Proof. intro z. unfold in_i8,  i8_norm_z.  pose proof (Z.mod_pos_bound (z + 128) 256 ltac:(lia)) as [Hlo Hhi]. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma in_i16_norm : forall z, in_i16 (i16_norm_z z) = true.
Proof. intro z. unfold in_i16, i16_norm_z. pose proof (Z.mod_pos_bound (z + 32768) 65536 ltac:(lia)) as [Hlo Hhi]. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma in_i32_norm : forall z, in_i32 (i32_norm_z z) = true.
Proof. intro z. unfold in_i32, i32_norm_z. pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296 ltac:(lia)) as [Hlo Hhi]. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.

(* Numeric-wrapper records, hoisted ABOVE GoTypeTag so TU8../TUnit can index them. *)
Record GoU8 := MkU8 { u8raw : Z ; u8ok : Squash (in_u8 u8raw = true) }.
Record GoI8 := MkI8 { i8raw : Z ; i8ok : Squash (in_i8 i8raw = true) }.
Record GoU16 := MkU16 { u16raw : Z ; u16ok : Squash (in_u16 u16raw = true) }.
Record GoI16 := MkI16 { i16raw : Z ; i16ok : Squash (in_i16 i16raw = true) }.
Record GoU32 := MkU32 { u32raw : Z ; u32ok : Squash (in_u32 u32raw = true) }.
Record GoI32 := MkI32 { i32raw : Z ; i32ok : Squash (in_i32 i32raw = true) }.
(* FULL-WIDTH signed int64 (Go spec "Numeric types").  Carried by [Z] in
   [[-2^63, 2^63)], faithful across the whole range, wrapping at the true [2^63].
   The wrapper ERASES at extraction; a [GoI64] value is a Go [int64] (native
   wrap), so the emitted ops need no mask. *)
Record GoI64 := MkI64 { i64raw : Z ; i64ok : Squash (in_i64 i64raw = true) }.
(* FULL-WIDTH unsigned 64-bit integer (Go spec: range [0, 2^64)).  Carried by
   [Z], faithful across the whole range, wrapping at [2^64].  The wrapper ERASES
   at extraction; a [GoU64] value is a Go [uint64] (native wrap), no mask. *)
Record GoU64 := MkU64 { u64raw : Z ; u64ok : Squash (in_u64 u64raw = true) }.

(* Go's platform-width UNSIGNED [uint] — a GENUINELY DISTINCT [Z]-carried record
   (NOT a transparent alias), faithful across [0, 2^64) exactly like [GoU64]; the 64-bit width
   choice is the only residual platform assumption (shared with [GoInt]).  [uintok] carries the
   range invariant [in_u64] AND (as a kept SProp field) defeats single-field-record unboxing, so
   the wrapper SURVIVES extraction as a distinct type (rendered Go [uint], struct decl suppressed,
   ctor/proj erased) instead of collapsing to its [Z] carrier — which gives [Tagged_GoUint := TUint]
   a UNIQUE resolution.  Literals are the range-checked [Number Notation] [(_)%uint]: an
   out-of-range constant is UNREPRESENTABLE (fails to parse), so there is no silent-wrap escape. *)
Record GoUint := MkUint { uintraw : Z ; uintok : Squash (in_u64 uintraw = true) }.
(* Go's [rune] is an alias for [int32] — the FAITHFUL [GoI32] record, so a [rune]
   value (e.g. [i32wrap c]) is a real, distinct int32. *)
Notation GoRune := GoI32.



(* [i64wrap] = wrap-to-int64-range + carry the (SProp) range proof, so [i64wrap (2^63) _] is
   unconstructable.  Hoisted here (before the narrow→int64 conversions at [i64_of_u8]… use it). *)
Lemma in_i64_wrap64 : forall z, in_i64 (wrap64 z) = true.
Proof.
  intro z. unfold in_i64, wrap64.
  pose proof (Z.mod_pos_bound (z + 9223372036854775808) 18446744073709551616 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
(* [wrap64] is the IDENTITY on the int64 range — the agreement backbone for every wrapped-vs-structural
   boundary lemma ([len_agrees_structural] below): a wrapped quantity IS the true one while it stays
   representable. *)
Lemma wrap64_small : forall z,
  (-9223372036854775808 <= z < 9223372036854775808)%Z -> wrap64 z = z.
Proof. intros z Hz. unfold wrap64. rewrite Z.mod_small; lia. Qed.
Definition i64wrap (z : Z) : GoI64 := MkI64 (wrap64 z) (squash (in_i64_wrap64 z)).

(* Go's platform-width SIGNED [int] — a GENUINELY DISTINCT [Z]-carried record, the
   EXACT [GoI64] shape rendered Go [int] instead of [int64].  Faithful across [[-2^63, 2^63)], wrapping
   at the true [2^63]; [intok] carries the range invariant AND (as a kept SProp field) defeats
   single-field unboxing so the wrapper survives extraction as a distinct type.  [intwrap] wraps an
   arbitrary [Z] into range (mirrors [i64wrap]) — the internal constructor for computed [GoInt]s. *)
Record GoInt := MkGoInt { intraw : Z ; intok : Squash (in_i64 intraw = true) }.
Definition intwrap (z : Z) : GoInt := MkGoInt (wrap64 z) (squash (in_i64_wrap64 z)).

(** ==================================================================================================
    THE NUMERIC OP LAYER — the pure Z-carried operations over the records above: fixed-width
    u8/i8..u32/i32 arithmetic, bitwise ops, shifts, conversions, EVIDENCE-CARRYING div/rem (a zero
    divisor is unrepresentable), the full-width GoI64/GoU64 ops + their proven arithmetic and
    boolean-algebra laws, untyped integer constants, and the exact int64 → float64 conversion.
    Entirely IO-free: records and their operations are ONE authority.  Mined out of the frozen
    builtins.v monolith (plans/builtins-split.md).
    ================================================================================================ *)

(** ---- Fixed-width unsigned integers (precise, computable models) ----

    A [uintN] value is [Z]-carried, kept reduced mod 2^N after EVERY operation —
    exactly Go's uintN arithmetic.  DEFINITIONS, not axioms: computable
    ([vm_compute] discharges concrete wrap facts), nothing added to the trust base.

    TYPE DISTINCTNESS (Go spec "Numeric types": numeric types are DISTINCT;
    explicit conversions required).  [GoU8] is its OWN record type, so Rocq
    REJECTS mixing a [uint8] with another integer type; the only way in is
    [u8_lit] (the untyped-constant conversion).  The plugin ERASES the wrapper at
    extraction ([MkU8]/[u8raw] → identity), and each op lowers to int64 + the
    explicit mask ([u8_add a b] → [(a + b) & 0xff]) — compilable BY CONSTRUCTION.
    [u8_no_implicit] (a [Fail]) is the build-checked proof that mixing is
    unrepresentable. *)
(* Go spec "Constants": a constant is typed at use with a REPRESENTABILITY check —
   "it is an error if the constant value cannot be represented as a value of the
   respective type".  So an out-of-range constant is a COMPILE ERROR, NOT a silent
   wrap.  [u8_lit] demands a proof the constant fits ([x < 256], discharged by
   [eq_refl] for a literal in range); there is no masking, so [u8_lit 300] is
   unrepresentable — exactly Go's "constant overflows uint8". *)
(** [Z.modulo z 256] is always in [0, 256) — the range invariant every [uint8] op preserves.
    [u8wrap] is the ONLY internal constructor of a computed [GoU8]: it reduces mod 256 and
    carries the (SProp-erased) proof, so the forged [MkU8 300 _] is UNCONSTRUCTABLE.  SProp ⇒
    proof irrelevance ⇒ two [GoU8] with equal [u8raw] are definitionally equal. *)
Lemma in_u8_mod256 : forall z, in_u8 (Z.modulo z 256) = true.
Proof.
  intro z. unfold in_u8.
  pose proof (Z.mod_pos_bound z 256 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u8wrap (z : Z) : GoU8 := MkU8 (Z.modulo z 256) (squash (in_u8_mod256 z)).
Definition u8_lit (z : Z) (pf : in_u8 z = true) : GoU8 := MkU8 z (squash pf).
Definition u8_add (a b : GoU8) : GoU8 := u8wrap (u8raw a + u8raw b).
Definition u8_sub (a b : GoU8) : GoU8 := u8wrap (u8raw a - u8raw b).
Definition u8_mul (a b : GoU8) : GoU8 := u8wrap (u8raw a * u8raw b).
Definition u8_eqb (a b : GoU8) : bool := Z.eqb (u8raw a) (u8raw b).
Definition u8_ltb (a b : GoU8) : bool := Z.ltb (u8raw a) (u8raw b).
Definition u8_leb (a b : GoU8) : bool := Z.leb (u8raw a) (u8raw b).

(* Build-checked: [uint8] and [int] do NOT mix — no implicit conversion. *)
Fail Definition u8_no_implicit (x : GoU8) : GoU8 := u8_add x (5 : nat).
(* Build-checked: an out-of-range constant is UNREPRESENTABLE (Go: "overflows uint8"). *)
Fail Definition u8_const_oob : GoU8 := u8_lit 300 eq_refl.
(* Build-checked: even the RAW constructor cannot forge an out-of-range uint8 — [MkU8] demands a
   proof [u8raw < 256]. *)
Fail Definition u8_forged : GoU8 := MkU8 300 (squash eq_refl).

(* Go's [byte] is a predeclared alias for [uint8] — the faithful [GoU8] record.
   So [s[i]] (a string byte) and a [uint8] are the SAME type, as in Go. *)
Notation GoByte := GoU8.

(** ---- Signed fixed-width integers ----

    [int8] in [-128, 128).  Go's int8 arithmetic wraps two's-complement.  Model:
    reduce mod 256 then SIGN-EXTEND onto [[-128,128)] — exactly Go's [int8(x)]
    conversion.  Comparison is SIGNED ([Z.ltb] on the sign-extended value → Go's
    signed int64 [<]).  The plugin emits the explicit int64 mask + sign-extend,
    e.g. [i8_add a b] → [((((a + b) & 0xff) ^ 0x80) - 0x80)].  Each width is a
    DISTINCT record (like [GoU8]); the wrapper erases at extraction. *)
(* [i8_norm_z] is hoisted up to the wrapper-record block (the GoI8 provenance invariant needs it).
   [i8wrap] is the internal constructor: normalize to 8-bit signed + carry the (trivial) provenance
   proof, so a forged [MkI8 200 _] is unconstructable (200 is not in [i8_norm_z]'s image). *)
Definition i8wrap (z : Z) : GoI8 := MkI8 (i8_norm_z z) (squash (in_i8_norm z)).
Definition i8_lit (z : Z) (pf : in_i8 z = true) : GoI8 := MkI8 z (squash pf).
Definition i8_add (a b : GoI8) : GoI8 := i8wrap (i8raw a + i8raw b).
Definition i8_sub (a b : GoI8) : GoI8 := i8wrap (i8raw a - i8raw b).
Definition i8_mul (a b : GoI8) : GoI8 := i8wrap (i8raw a * i8raw b).
Definition i8_eqb (a b : GoI8) : bool := Z.eqb (i8raw a) (i8raw b).
Definition i8_ltb (a b : GoI8) : bool := Z.ltb (i8raw a) (i8raw b).   (* SIGNED comparison *)
Definition i8_leb (a b : GoI8) : bool := Z.leb (i8raw a) (i8raw b).

(** Direct [>] / [>=] / [!=] for the fixed-width types, completing Go's six comparison
    operators (here for [uint8]/[int8] — representative; the plugin's [fw_is] recognizes
    the same op on EVERY width, so [u16]/[i16]/[u32]/[i32] are identical one-liners).
    Defined as the swapped [</<=] and [negb (==)] but recognized by name and lowered to
    the DIRECT Go operator. *)
Definition u8_gtb  (a b : GoU8) : bool := u8_ltb b a.
Definition u8_geb  (a b : GoU8) : bool := u8_leb b a.
Definition u8_neqb (a b : GoU8) : bool := negb (u8_eqb a b).
Definition i8_gtb  (a b : GoI8) : bool := i8_ltb b a.
Definition i8_geb  (a b : GoI8) : bool := i8_leb b a.
Definition i8_neqb (a b : GoI8) : bool := negb (i8_eqb a b).

(** [uint16] / [int16] — the same template at width 16 (mask [0xffff]; sign bit
    [0x8000]).  Still fully faithful on the 63-bit carrier: a 16-bit product is
    [< 2^32], far below the [2^62] boundary, so [mul] is exact too. *)
(** [land x 65535] is always [< 65536] — the [uint16] range invariant (parallel to [land255_lt256]).
    [u16wrap] masks + carries the SProp proof, so a forged [MkU16 70000 _] is unconstructable. *)
Lemma in_u16_mod65536 : forall z, in_u16 (Z.modulo z 65536) = true.
Proof.
  intro z. unfold in_u16.
  pose proof (Z.mod_pos_bound z 65536 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u16wrap (z : Z) : GoU16 := MkU16 (Z.modulo z 65536) (squash (in_u16_mod65536 z)).
Definition u16_lit (z : Z) (pf : in_u16 z = true) : GoU16 := MkU16 z (squash pf).
Definition u16_add (a b : GoU16) : GoU16 := u16wrap (u16raw a + u16raw b).
Definition u16_sub (a b : GoU16) : GoU16 := u16wrap (u16raw a - u16raw b).
Definition u16_mul (a b : GoU16) : GoU16 := u16wrap (u16raw a * u16raw b).
Definition u16_eqb (a b : GoU16) : bool := Z.eqb (u16raw a) (u16raw b).
Definition u16_ltb (a b : GoU16) : bool := Z.ltb (u16raw a) (u16raw b).
Definition u16_leb (a b : GoU16) : bool := Z.leb (u16raw a) (u16raw b).

(* [i16_norm_z] hoisted to the wrapper-record block (the GoI16 provenance invariant needs it).
   [i16wrap] = normalize + carry the trivial provenance proof, so [MkI16 40000 _] is unconstructable. *)
Definition i16wrap (z : Z) : GoI16 := MkI16 (i16_norm_z z) (squash (in_i16_norm z)).
Definition i16_lit (z : Z) (pf : in_i16 z = true) : GoI16 := MkI16 z (squash pf).
Definition i16_add (a b : GoI16) : GoI16 := i16wrap (i16raw a + i16raw b).
Definition i16_sub (a b : GoI16) : GoI16 := i16wrap (i16raw a - i16raw b).
Definition i16_mul (a b : GoI16) : GoI16 := i16wrap (i16raw a * i16raw b).
Definition i16_eqb (a b : GoI16) : bool := Z.eqb (i16raw a) (i16raw b).
Definition i16_ltb (a b : GoI16) : bool := Z.ltb (i16raw a) (i16raw b).
Definition i16_leb (a b : GoI16) : bool := Z.leb (i16raw a) (i16raw b).

(* Build-checked (Go spec "Numeric types": distinct types, no implicit mixing):
   neither a typed value of another numeric type nor an [int] may be passed. *)
Fail Definition i8_no_implicit  (x : GoI8)  : GoI8  := i8_add  x (5 : nat).
Fail Definition u16_no_implicit (x : GoU16) : GoU16 := u16_add x (5 : nat).
Fail Definition i16_no_implicit (x : GoI16) : GoI16 := i16_add x (5 : nat).
(* Cross-WIDTH too: [uint8] and [uint16] are distinct types — no implicit widen. *)
Fail Definition u8_u16_no_mix (x : GoU8) (y : GoU16) : GoU16 := u16_add y x.

(* Build-checked (Go spec "Constants"): out-of-range constants are UNREPRESENTABLE
   (a compile error), per width — no silent wrap. *)
Fail Definition i8_const_oob  : GoI8  := i8_lit  200    eq_refl.   (* > 127 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int8 — the provenance proof
   [in_i8 200 = true] is false (200 is not in the int8 range [-128,128)). *)
Fail Definition i8_forged : GoI8 := MkI8 200 (squash (ex_intro _ 200 eq_refl)).
Fail Definition u16_const_oob : GoU16 := u16_lit 70000  eq_refl.   (* >= 2^16 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint16 (SProp range proof). *)
Fail Definition u16_forged : GoU16 := MkU16 70000 (squash eq_refl).
Fail Definition i16_const_oob : GoI16 := i16_lit 40000  eq_refl.   (* > 32767 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int16 (provenance proof false). *)
Fail Definition i16_forged : GoI16 := MkI16 40000 (squash (ex_intro _ 40000 eq_refl)).

(** ---- Fixed-width bitwise operators (Go spec "Arithmetic operators": [& | ^ &^],
    and unary [^] complement) ----

    Bitwise AND / OR / XOR / AND-NOT and unary complement on the fixed-width
    types.  TOTAL and panic-free (unlike shifts, whose count can panic).
    Faithful by construction:
    - [uintN]: AND/OR/XOR of two in-range values stay in [0,2^N), so no mask is
      needed; AND-NOT and complement flip within the width via [lxor _ (2^N-1)].
    - [intN]: the sign-extended carrier already makes the raw bitwise op correct,
      but we re-[norm] (idempotent) so every result is manifestly a valid [intN].
    Go's [&^] (AND-NOT) and unary [^] (complement) are single operators.  The
    plugin emits the bare Go infix [& | ^ &^] / unary [^] (no wrap) — faithful
    because the operands are in range / sign-extended (verified on int64). *)
Definition u8_and     (a b : GoU8)  : GoU8  := u8wrap (Z.land (u8raw a) (u8raw b)).
Definition u8_or      (a b : GoU8)  : GoU8  := u8wrap (Z.lor  (u8raw a) (u8raw b)).
Definition u8_xor     (a b : GoU8)  : GoU8  := u8wrap (Z.lxor (u8raw a) (u8raw b)).
Definition u8_andnot  (a b : GoU8)  : GoU8  := u8wrap (Z.land (u8raw a) (Z.lxor (u8raw b) 255)).
Definition u8_not     (a   : GoU8)  : GoU8  := u8wrap (Z.lxor (u8raw a) 255).
Definition i8_and     (a b : GoI8)  : GoI8  := i8wrap (Z.land (i8raw a) (i8raw b)).
Definition i8_or      (a b : GoI8)  : GoI8  := i8wrap (Z.lor  (i8raw a) (i8raw b)).
Definition i8_xor     (a b : GoI8)  : GoI8  := i8wrap (Z.lxor (i8raw a) (i8raw b)).
Definition i8_andnot  (a b : GoI8)  : GoI8  := i8wrap (Z.land (i8raw a) (Z.lxor (i8raw b) 255)).
Definition i8_not     (a   : GoI8)  : GoI8  := i8wrap (Z.lxor (i8raw a) 255).
Definition u16_and    (a b : GoU16) : GoU16 := u16wrap (Z.land (u16raw a) (u16raw b)).
Definition u16_or     (a b : GoU16) : GoU16 := u16wrap (Z.lor  (u16raw a) (u16raw b)).
Definition u16_xor    (a b : GoU16) : GoU16 := u16wrap (Z.lxor (u16raw a) (u16raw b)).
Definition u16_andnot (a b : GoU16) : GoU16 := u16wrap (Z.land (u16raw a) (Z.lxor (u16raw b) 65535)).
Definition u16_not    (a   : GoU16) : GoU16 := u16wrap (Z.lxor (u16raw a) 65535).
Definition i16_and    (a b : GoI16) : GoI16 := i16wrap (Z.land (i16raw a) (i16raw b)).
Definition i16_or     (a b : GoI16) : GoI16 := i16wrap (Z.lor  (i16raw a) (i16raw b)).
Definition i16_xor    (a b : GoI16) : GoI16 := i16wrap (Z.lxor (i16raw a) (i16raw b)).
Definition i16_andnot (a b : GoI16) : GoI16 := i16wrap (Z.land (i16raw a) (Z.lxor (i16raw b) 65535)).
Definition i16_not    (a   : GoI16) : GoI16 := i16wrap (Z.lxor (i16raw a) 65535).

(* Build-checked: bitwise ops respect type distinctness too (no implicit mix). *)
Fail Definition u8_and_no_implicit (x : GoU8) : GoU8 := u8_and x (5 : nat).

(** ---- Fixed-width shifts (Go spec "Arithmetic operators": [<< >>]) ----

    Left / right shift on the fixed-width types.  Unlike the bitwise ops, a shift
    can PANIC: Go panics if the count is negative.  So — exactly like [div_nz] —
    the shift is EVIDENCE-CARRYING: it demands a proof the count is non-negative
    ([0 <= k], discharged by [eq_refl] for a literal), making the panic
    unreachable (safe-by-construction).  There is NO upper limit on the count
    (Go: an over-width shift gives 0 / sign-fill, not UB); the primitives agree —
    [lsl]/[lsr] give 0 for [k >= width], [asr] fills with the sign bit.
    - [<<]: [uintN] truncates to the width ([(x<<k) mod 2^N], via [land]); [intN]
      is two's-complement (sign-extend via [norm]).
    - [>>]: [uintN] is LOGICAL ([lsr]); [intN] is ARITHMETIC ([asr]) — sign-
      preserving, truncating toward −∞, NOT toward zero like [/] ([-3>>1 = -2],
      whereas [-3/2 = -1]).
    The plugin emits Go [x << k] / [x >> k]: for [>>], the int64 carrier is
    non-negative for [uintN] (so Go's [>>] is logical) and sign-extended for
    [intN] (so Go's [>>] is arithmetic) — both correct with no mask. *)
Definition u8_shl  (x : GoU8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU8  := u8wrap (Z.shiftl (u8raw x) (intraw k)).
Definition u8_shr  (x : GoU8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU8  := u8wrap (Z.shiftr (u8raw x) (intraw k)).
Definition i8_shl  (x : GoI8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI8  := i8wrap (Z.shiftl (i8raw x) (intraw k)).
Definition i8_shr  (x : GoI8)  (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI8  := i8wrap (Z.shiftr (i8raw x) (intraw k)).
Definition u16_shl (x : GoU16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU16 := u16wrap (Z.shiftl (u16raw x) (intraw k)).
Definition u16_shr (x : GoU16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU16 := u16wrap (Z.shiftr (u16raw x) (intraw k)).
Definition i16_shl (x : GoI16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI16 := i16wrap (Z.shiftl (i16raw x) (intraw k)).
Definition i16_shr (x : GoI16) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI16 := i16wrap (Z.shiftr (i16raw x) (intraw k)).

(* Build-checked: a NEGATIVE shift count is UNREPRESENTABLE (Go panics on it). *)
Fail Definition u8_shl_neg : GoU8 := u8_shl (u8_lit 1 eq_refl) (MkGoInt (-1)%Z (squash eq_refl)) eq_refl.

(** ---- Numeric conversions (Go spec "Conversions") ----

    "When converting between integer types, if the value is a signed integer, it
    is sign extended to implicit infinite precision ... It is then truncated to
    fit in the result type's size."  These are the EXPLICIT conversions the
    "Numeric types" rule requires to mix distinct types — the type checker rejects
    implicit mixing (the [*_no_implicit] [Fail]s), so a value crosses types only
    through one of these.

    Every conversion routes through the [int] carrier, which already holds each
    fixed-width value's exact mathematical value (sign-extended for [intN],
    zero-extended for [uintN]):
    - [int_of_FW] WIDENS to [int] — value preserved in the model (every [uintN]/[intN]
      fits in [int]), but EMITTED as a real cast [int(x)], NOT identity (a narrow Go value
      at an [int] boundary needs it).
    - [FW_of_int] NARROWS [int] to the width — TRUNCATE ([land] to [uintN], or
      mask+sign-extend [norm] to [intN]) — exactly Go's [uint8(x)]/[int8(x)].  No
      representability proof (unlike [*_lit]): a conversion truncates, it does not
      reject.  Composition handles cross-width ([uint8(int16val)] =
      [u8_of_int (int_of_i16 x)] = low 8 bits, faithful). *)
Definition int_of_u8  (x : GoU8)  : GoInt := intwrap (u8raw  x).
Definition int_of_i8  (x : GoI8)  : GoInt := intwrap (i8raw  x).
Definition int_of_u16 (x : GoU16) : GoInt := intwrap (u16raw x).
Definition int_of_i16 (x : GoI16) : GoInt := intwrap (i16raw x).
Definition u8_of_int  (x : GoInt) : GoU8  := u8wrap (intraw x).
Definition i8_of_int  (x : GoInt) : GoI8  := i8wrap (intraw x).
Definition u16_of_int (x : GoInt) : GoU16 := u16wrap (intraw x).
Definition i16_of_int (x : GoInt) : GoI16 := i16wrap (intraw x).

(* Build-checked: a conversion takes an [int], NOT another fixed-width type — so a
   cross-type conversion MUST go through [int] (e.g. [u8_of_int (int_of_i16 y)]),
   never [u8_of_int y] directly. *)
Fail Definition u8_of_i16_direct (y : GoI16) : GoU8 := u8_of_int y.

(** ---- Narrow -> full-width int64 WIDENING (Go [int64(x)]) ----
    Widen a fixed-width [uintN]/[intN] to the CANONICAL [int64] ([GoI64]).  The
    value is PRESERVED: an unsigned narrow ([0..2^N-1]) and a signed narrow
    ([-2^(N-1)..2^(N-1)-1]) both fit int64 exactly, so the carrier's [Z] reading
    ([uNraw]/[iNraw] — the value's SIGNED reading, correct for both: unsigned narrows
    are [< 2^32] and signed narrows hold their sign-extended value) is in
    range and lands unchanged in [GoI64].  Distinct from the narrow [int_of_FW]
    (which targets the index-[int]); these target the value-[int64].
    The body is a PURE [Z] re-wrap ([i64wrap] of the narrow's [Z] reading), but the
    EMITTED Go is a real widening cast [int64(x)], NOT identity — a narrow Go value
    at an int64 boundary needs the cast.  Machine-checked in main.v. *)
Definition i64_of_u8  (a : GoU8)  : GoI64 := i64wrap (u8raw  a).
Definition i64_of_i8  (a : GoI8)  : GoI64 := i64wrap (i8raw  a).
Definition i64_of_u16 (a : GoU16) : GoI64 := i64wrap (u16raw a).
Definition i64_of_i16 (a : GoI16) : GoI64 := i64wrap (i16raw a).
Definition i64_of_u32 (a : GoU32) : GoI64 := i64wrap (u32raw a).
Definition i64_of_i32 (a : GoI32) : GoI64 := i64wrap (i32raw a).

(** ---- Fixed-width division / remainder (Go spec "Arithmetic operators": [/ %]) ----
    EVIDENCE-CARRYING like [div_nz]: demand the divisor be non-zero (Go panics on a
    zero divisor), so the panic is unreachable (safe-by-construction).
    - [uintN]: the carrier is non-negative, so the SIGNED primitives [divs]/[mods]
      compute the UNSIGNED quotient/remainder; the result is in range (quotient
      <= dividend, |remainder| < divisor), no mask.
    - [intN]: SIGNED div/mod (truncate toward zero), wrapped to the width ([norm]) —
      this is where the most-negative / [-1] overflow lands: Go [int8(-128)/int8(-1)
      = -128] (two's-complement wrap), and [norm] gives exactly that. *)
Definition u8_div  (a b : GoU8)  (_ : (Z.eqb (u8raw b)  0) = false) : GoU8  := u8wrap (Z.quot (u8raw a) (u8raw b)).
Definition u8_mod  (a b : GoU8)  (_ : (Z.eqb (u8raw b)  0) = false) : GoU8  := u8wrap (Z.rem (u8raw a) (u8raw b)).
Definition i8_div  (a b : GoI8)  (_ : (Z.eqb (i8raw b)  0) = false) : GoI8  := i8wrap (Z.quot (i8raw a) (i8raw b)).
Definition i8_mod  (a b : GoI8)  (_ : (Z.eqb (i8raw b)  0) = false) : GoI8  := i8wrap (Z.rem (i8raw a) (i8raw b)).
Definition u16_div (a b : GoU16) (_ : (Z.eqb (u16raw b) 0) = false) : GoU16 := u16wrap (Z.quot (u16raw a) (u16raw b)).
Definition u16_mod (a b : GoU16) (_ : (Z.eqb (u16raw b) 0) = false) : GoU16 := u16wrap (Z.rem (u16raw a) (u16raw b)).
Definition i16_div (a b : GoI16) (_ : (Z.eqb (i16raw b) 0) = false) : GoI16 := i16wrap (Z.quot (i16raw a) (i16raw b)).
Definition i16_mod (a b : GoI16) (_ : (Z.eqb (i16raw b) 0) = false) : GoI16 := i16wrap (Z.rem (i16raw a) (i16raw b)).

(* Build-checked: a ZERO divisor is UNREPRESENTABLE (Go panics on it). *)
Fail Definition u8_div_zero : GoU8 := u8_div (u8_lit 1 eq_refl) (u8_lit 0 eq_refl) eq_refl.

(** ---- uint32 / int32 — the SAME template at width 32 ----

    Distinct [Z]-carried records, same as the narrower widths: every op
    (add/sub/mul, comparison, bitwise, shift, div/mod, conversions) reduces mod
    [2^32] (sign-extending for [int32]) — exact by construction on [Z].
    Machine-checked: [spec_u32_mul_wrap]/[spec_i32_mul_wrap] in main.v. *)
(** [land x (2^32-1)] is always [< 2^32] — the [uint32] range invariant (parallel to
    [land255_lt256]).  [u32wrap] masks + carries the SProp proof; forged [MkU32 5000000000 _] is
    unconstructable. *)
Lemma in_u32_mod : forall z, in_u32 (Z.modulo z 4294967296) = true.
Proof.
  intro z. unfold in_u32.
  pose proof (Z.mod_pos_bound z 4294967296 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u32wrap (z : Z) : GoU32 := MkU32 (Z.modulo z 4294967296) (squash (in_u32_mod z)).
Definition u32_lit (z : Z) (pf : in_u32 z = true) : GoU32 := MkU32 z (squash pf).
Definition u32_add (a b : GoU32) : GoU32 := u32wrap (u32raw a + u32raw b).
Definition u32_sub (a b : GoU32) : GoU32 := u32wrap (u32raw a - u32raw b).
Definition u32_mul (a b : GoU32) : GoU32 := u32wrap (u32raw a * u32raw b).
Definition u32_eqb (a b : GoU32) : bool := Z.eqb (u32raw a) (u32raw b).
Definition u32_ltb (a b : GoU32) : bool := Z.ltb (u32raw a) (u32raw b).
Definition u32_leb (a b : GoU32) : bool := Z.leb (u32raw a) (u32raw b).
Definition u32_and    (a b : GoU32) : GoU32 := u32wrap (Z.land (u32raw a) (u32raw b)).
Definition u32_or     (a b : GoU32) : GoU32 := u32wrap (Z.lor  (u32raw a) (u32raw b)).
Definition u32_xor    (a b : GoU32) : GoU32 := u32wrap (Z.lxor (u32raw a) (u32raw b)).
Definition u32_andnot (a b : GoU32) : GoU32 := u32wrap (Z.land (u32raw a) (Z.lxor (u32raw b) 4294967295)).
Definition u32_not    (a   : GoU32) : GoU32 := u32wrap (Z.lxor (u32raw a) 4294967295).
Definition u32_shl (x : GoU32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU32 := u32wrap (Z.shiftl (u32raw x) (intraw k)).
Definition u32_shr (x : GoU32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoU32 := u32wrap (Z.shiftr (u32raw x) (intraw k)).
Definition u32_div (a b : GoU32) (_ : (Z.eqb (u32raw b) 0) = false) : GoU32 := u32wrap (Z.quot (u32raw a) (u32raw b)).
Definition u32_mod (a b : GoU32) (_ : (Z.eqb (u32raw b) 0) = false) : GoU32 := u32wrap (Z.rem (u32raw a) (u32raw b)).
Definition int_of_u32 (x : GoU32) : GoInt := intwrap (u32raw x).
Definition u32_of_int (x : GoInt) : GoU32 := u32wrap (intraw x).

(* [i32_norm_z] hoisted to the wrapper-record block (the GoI32 provenance invariant needs it).
   [i32wrap] = normalize + carry the trivial provenance proof, so [MkI32 5000000000 _] is
   unconstructable. *)
Definition i32wrap (z : Z) : GoI32 := MkI32 (i32_norm_z z) (squash (in_i32_norm z)).
Definition i32_lit (z : Z) (pf : in_i32 z = true) : GoI32 := MkI32 z (squash pf).
Definition i32_add (a b : GoI32) : GoI32 := i32wrap (i32raw a + i32raw b).
Definition i32_sub (a b : GoI32) : GoI32 := i32wrap (i32raw a - i32raw b).
Definition i32_mul (a b : GoI32) : GoI32 := i32wrap (i32raw a * i32raw b).
Definition i32_eqb (a b : GoI32) : bool := Z.eqb (i32raw a) (i32raw b).
Definition i32_ltb (a b : GoI32) : bool := Z.ltb (i32raw a) (i32raw b).
Definition i32_leb (a b : GoI32) : bool := Z.leb (i32raw a) (i32raw b).

(** Direct [>] / [>=] / [!=] for the remaining fixed widths (u16/i16/u32/i32),
    completing Go's six comparison operators for EVERY integer type.  Same trivial
    pattern as u8/i8 (swapped [</<=], [negb (==)]) recognized by the generic [fw_is]. *)
Definition u16_gtb  (a b : GoU16) : bool := u16_ltb b a.
Definition u16_geb  (a b : GoU16) : bool := u16_leb b a.
Definition u16_neqb (a b : GoU16) : bool := negb (u16_eqb a b).
Definition i16_gtb  (a b : GoI16) : bool := i16_ltb b a.
Definition i16_geb  (a b : GoI16) : bool := i16_leb b a.
Definition i16_neqb (a b : GoI16) : bool := negb (i16_eqb a b).
Definition u32_gtb  (a b : GoU32) : bool := u32_ltb b a.
Definition u32_geb  (a b : GoU32) : bool := u32_leb b a.
Definition u32_neqb (a b : GoU32) : bool := negb (u32_eqb a b).
Definition i32_gtb  (a b : GoI32) : bool := i32_ltb b a.
Definition i32_geb  (a b : GoI32) : bool := i32_leb b a.
Definition i32_neqb (a b : GoI32) : bool := negb (i32_eqb a b).
Definition i32_and    (a b : GoI32) : GoI32 := i32wrap (Z.land (i32raw a) (i32raw b)).
Definition i32_or     (a b : GoI32) : GoI32 := i32wrap (Z.lor  (i32raw a) (i32raw b)).
Definition i32_xor    (a b : GoI32) : GoI32 := i32wrap (Z.lxor (i32raw a) (i32raw b)).
Definition i32_andnot (a b : GoI32) : GoI32 := i32wrap (Z.land (i32raw a) (Z.lxor (i32raw b) 4294967295)).
Definition i32_not    (a   : GoI32) : GoI32 := i32wrap (Z.lxor (i32raw a) 4294967295).
Definition i32_shl (x : GoI32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI32 := i32wrap (Z.shiftl (i32raw x) (intraw k)).
Definition i32_shr (x : GoI32) (k : GoInt) (_ : (Z.leb 0 (intraw k)) = true) : GoI32 := i32wrap (Z.shiftr (i32raw x) (intraw k)).
Definition i32_div (a b : GoI32) (_ : (Z.eqb (i32raw b) 0) = false) : GoI32 := i32wrap (Z.quot (i32raw a) (i32raw b)).
Definition i32_mod (a b : GoI32) (_ : (Z.eqb (i32raw b) 0) = false) : GoI32 := i32wrap (Z.rem (i32raw a) (i32raw b)).
Definition int_of_i32 (x : GoI32) : GoInt := intwrap (i32raw x).
Definition i32_of_int (x : GoInt) : GoI32 := i32wrap (intraw x).

(* Build-checked: u32/i32 are distinct, out-of-range constants unrepresentable. *)
Fail Definition u32_no_implicit (x : GoU32) : GoU32 := u32_add x (5 : nat).
Fail Definition u32_const_oob   : GoU32 := u32_lit 5000000000 eq_refl.   (* >= 2^32 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint32 (SProp range proof). *)
Fail Definition u32_forged : GoU32 := MkU32 5000000000 (squash eq_refl).
(* Build-checked: the RAW int32 constructor cannot forge an out-of-range value (provenance proof false). *)
Fail Definition i32_forged : GoI32 := MkI32 5000000000 (squash (ex_intro _ 5000000000 eq_refl)).

(** ---- int64 — FULL-WIDTH signed 64-bit (Go spec "Numeric types") ----

    The faithful model of Go's [int64] / (64-bit) [int]: carried by [Z] and
    normalised mod [2^64] into the signed range after every op.
    [wrap64] is the two's-complement wrap; it is the IDENTITY
    on in-range values (so a no-overflow op equals the exact mathematical result —
    [i64_add_no_overflow_exact] in main.v), and at the boundary [2^63-1 + 1] wraps to
    [-2^63] exactly like Go ([spec_i64_add_wrap]).  Extraction erases the wrapper and
    emits BARE Go int64 ops ([a + b], …): Go's int64 wraps natively at [2^64], so the
    mask the narrow widths need is here unnecessary.  Comparison is signed [Z]
    comparison — valid because every stored value is normalised into [-2^63, 2^63). *)
(* [wrap64]/[in_i64]/[i64wrap] are hoisted to the wrapper-record block. *)
(* Smart literal: DEMANDS the constant fit int64 (Go's compile-time representability
   check); an out-of-range literal is unrepresentable ([i64_const_oob] Fail). *)
Definition i64_lit (z : Z) (pf : in_i64 z = true) : GoI64 := MkI64 z (squash pf).
Definition i64_add (a b : GoI64) : GoI64 := i64wrap (i64raw a + i64raw b).
Definition i64_sub (a b : GoI64) : GoI64 := i64wrap (i64raw a - i64raw b).
Definition i64_mul (a b : GoI64) : GoI64 := i64wrap (i64raw a * i64raw b).
(* Unary negation (Go's unary [-]): [-x] = [0 - x] with the same two's-complement wrap
   (so [-MININT = MININT]).  Lowers to the DIRECT prefix [-x], not the encoded [0 - x]. *)
Definition i64_neg (a : GoI64) : GoI64 := i64wrap (wrap64 (Z.opp (i64raw a))).
Definition i64_eqb (a b : GoI64) : bool := Z.eqb (i64raw a) (i64raw b).
Definition i64_ltb (a b : GoI64) : bool := Z.ltb (i64raw a) (i64raw b).
Definition i64_leb (a b : GoI64) : bool := Z.leb (i64raw a) (i64raw b).

(* Platform-int [GoInt] ops — the EXACT [GoI64] shape, rendered with Go [int] operators
   instead of [int64].  [int_lit] is the proof-carrying literal (NoInline'd, plugin-folded — bare
   decimal in expression position, [int(N)] when a Go type must be pinned); arithmetic wraps at the
   true [2^63] via [wrap64].  [int_div]/[int_mod] are evidence-gated (nonzero divisor) — Go's truncated
   [/]/[%] ([Z.quot]/[Z.rem]); [MININT/-1] overflows and wraps to MININT, the TRUE int64 [-2^63]. *)
Definition int_lit (z : Z) (pf : in_i64 z = true) : GoInt := MkGoInt z (squash pf).
Definition int_add (a b : GoInt) : GoInt := intwrap (intraw a + intraw b).
Definition int_sub (a b : GoInt) : GoInt := intwrap (intraw a - intraw b).
Definition int_mul (a b : GoInt) : GoInt := intwrap (intraw a * intraw b).
Definition int_neg (a : GoInt) : GoInt := intwrap (wrap64 (Z.opp (intraw a))).
(* Go's unary [^x] on [int] — the two's-complement BITWISE COMPLEMENT, = [-x-1] = [Z.lnot] exactly
   (verified `go run`: ^3 = -4, ^-1 = 0, ^minint = maxint); a bijection on the int64 window, so the
   wrap is the identity here — [intwrap] kept for the carrier's range invariant. *)
Definition int_not (a : GoInt) : GoInt := intwrap (Z.lnot (intraw a)).
(* Go's BITWISE binops on [int] — total on the carrier (the two's-complement window is closed
   under [land]/[lor]/[lxor]; [&^] = AND NOT, [Z.land a (Z.lnot b)]); [intwrap] kept for the
   carrier's range invariant (verified `go run`: 3&1=1, 3|4=7, 3^1=2, 3&^1=2, 3&^2=1). *)
Definition int_and    (a b : GoInt) : GoInt := intwrap (Z.land (intraw a) (intraw b)).
Definition int_or     (a b : GoInt) : GoInt := intwrap (Z.lor  (intraw a) (intraw b)).
Definition int_xor    (a b : GoInt) : GoInt := intwrap (Z.lxor (intraw a) (intraw b)).
Definition int_andnot (a b : GoInt) : GoInt := intwrap (Z.land (intraw a) (Z.lnot (intraw b))).
(* Go's SHIFTS on [int] — the EXACT [i64_shl]/[i64_shr] shape: evidence-gated NONNEGATIVE count
   ([<<] wraps at [2^63] via [intwrap]'s [wrap64]; [>>] is the ARITHMETIC shift — [Z.shiftr] on a
   negative is floor division, Go's sign fill; verified `go run`: 3<<62 wraps negative, -3>>1 = -2,
   -3>>64 = -1).  The consumer saturates counts >= 64 BEFORE the op (GoSem's [int_shift_checked]),
   so the shift amount stays small. *)
Definition int_shl (x : GoInt) (k : Z) (_ : (0 <=? k)%Z = true) : GoInt := intwrap (Z.shiftl (intraw x) k).
Definition int_shr (x : GoInt) (k : Z) (_ : (0 <=? k)%Z = true) : GoInt := intwrap (Z.shiftr (intraw x) k).
Fail Definition int_shl_neg : GoInt := int_shl (intwrap 1%Z) (-1)%Z eq_refl.
Definition int_eqb (a b : GoInt) : bool := Z.eqb (intraw a) (intraw b).
Definition int_ltb (a b : GoInt) : bool := Z.ltb (intraw a) (intraw b).
Definition int_leb (a b : GoInt) : bool := Z.leb (intraw a) (intraw b).
Definition int_div (a b : GoInt) (_ : Z.eqb (intraw b) 0%Z = false) : GoInt := intwrap (wrap64 (Z.quot (intraw a) (intraw b))).
Definition int_mod (a b : GoInt) (_ : Z.eqb (intraw b) 0%Z = false) : GoInt := intwrap (wrap64 (Z.rem (intraw a) (intraw b))).

(** ── GoI64 ARITHMETIC has the commutative-semiring CORE mod 2^64 (signed two's-complement) — the
    signed analogue of the GoU64 laws.  Key: the SIGNED [wrap64] preserves the residue mod 2^64
    ([wrap64_residue]: [wrap64 z ≡ z]), so it is a ring homomorphism — an inner [wrap64] is absorbed
    across `+` / `*` ([wrap64_idem_*]); the rest mirrors GoU64. ── *)
Lemma wrap64_residue : forall z,
  (wrap64 z mod 18446744073709551616 = z mod 18446744073709551616)%Z.
Proof.
  intro z. unfold wrap64. rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. ring.
Qed.
Lemma wrap64_eq_of_mod : forall a b,
  (a mod 18446744073709551616 = b mod 18446744073709551616)%Z -> wrap64 a = wrap64 b.
Proof.
  intros a b H. unfold wrap64. f_equal.
  rewrite Zplus_mod, H, <- Zplus_mod. reflexivity.
Qed.
Lemma wrap64_idem_add_r : forall a b, wrap64 (a + wrap64 b) = wrap64 (a + b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zplus_mod, wrap64_residue, <- Zplus_mod. reflexivity. Qed.
Lemma wrap64_idem_add_l : forall a b, wrap64 (wrap64 a + b) = wrap64 (a + b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zplus_mod, wrap64_residue, <- Zplus_mod. reflexivity. Qed.
Lemma wrap64_idem_mul_r : forall a b, wrap64 (a * wrap64 b) = wrap64 (a * b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zmult_mod, wrap64_residue, <- Zmult_mod. reflexivity. Qed.
Lemma wrap64_idem_mul_l : forall a b, wrap64 (wrap64 a * b) = wrap64 (a * b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zmult_mod, wrap64_residue, <- Zmult_mod. reflexivity. Qed.

Lemma i64_ext : forall x y : GoI64, i64raw x = i64raw y -> x = y.
Proof. intros [rx px] [ry py] H. cbn in H. subst ry. reflexivity. Qed.
Lemma i64raw_add : forall a b, i64raw (i64_add a b) = wrap64 (i64raw a + i64raw b).
Proof. intros. reflexivity. Qed.
Lemma i64raw_mul : forall a b, i64raw (i64_mul a b) = wrap64 (i64raw a * i64raw b).
Proof. intros. reflexivity. Qed.

(** Keystone coding: a CONCRETE [nat] ↦ Go int64 ([GoI64]) coding with an HONEST round-trip.
    An injection [nat ↪ GoI64] with a left inverse is IMPOSSIBLE ([GoI64] is finite), so
    [keystone_prj (keystone_inj n) = n] holds ONLY for REPRESENTABLE [n] ([Z.of_nat n < 2^63]) —
    [keystone_roundtrip].  The concurrency Keystone bridge must rest on THIS bounded fact. *)
Definition keystone_inj (n : nat) : GoI64 := i64wrap (Z.of_nat n).
Definition keystone_prj (g : GoI64) : nat := Z.to_nat (i64raw g).
Lemma keystone_roundtrip : forall n,
  (Z.of_nat n < 9223372036854775808)%Z -> keystone_prj (keystone_inj n) = n.
Proof.
  intros n Hn. pose proof (Nat2Z.is_nonneg n) as Hpos.
  unfold keystone_prj, keystone_inj, i64wrap. cbn [i64raw]. unfold wrap64.
  rewrite Z.mod_small by lia.
  replace (Z.of_nat n + 9223372036854775808 - 9223372036854775808)%Z with (Z.of_nat n) by lia.
  apply Nat2Z.id.
Qed.
(** Representability predicate for the Keystone bridge: a value the [keystone] coding round-trips
    (fits a signed int64).  Defined here so the [Z]-scope stays in [GoNumeric.v] (concurrency.v has no ZArith). *)
Definition Vrep64 (n : nat) : Prop := (Z.of_nat n < 9223372036854775808)%Z.
Lemma Vrep64_0 : Vrep64 0.
Proof. unfold Vrep64. cbn. lia. Qed.

Lemma i64_add_comm : forall a b, i64_add a b = i64_add b a.
Proof. intros. apply i64_ext. rewrite !i64raw_add, (Z.add_comm (i64raw a)). reflexivity. Qed.
Lemma i64_mul_comm : forall a b, i64_mul a b = i64_mul b a.
Proof. intros. apply i64_ext. rewrite !i64raw_mul, (Z.mul_comm (i64raw a)). reflexivity. Qed.
Lemma i64_add_assoc : forall a b c, i64_add a (i64_add b c) = i64_add (i64_add a b) c.
Proof.
  intros. apply i64_ext. rewrite !i64raw_add.
  rewrite wrap64_idem_add_r, wrap64_idem_add_l. f_equal. ring.
Qed.
Lemma i64_mul_assoc : forall a b c, i64_mul a (i64_mul b c) = i64_mul (i64_mul a b) c.
Proof.
  intros. apply i64_ext. rewrite !i64raw_mul.
  rewrite wrap64_idem_mul_r, wrap64_idem_mul_l. f_equal. ring.
Qed.
Lemma i64_mul_add_distr_l : forall a b c,
  i64_mul a (i64_add b c) = i64_add (i64_mul a b) (i64_mul a c).
Proof.
  intros. apply i64_ext. rewrite !i64raw_add, !i64raw_mul, !i64raw_add.
  rewrite wrap64_idem_mul_r, wrap64_idem_add_l, wrap64_idem_add_r. f_equal. ring.
Qed.

(** [<] is a STRICT TOTAL ORDER on (signed) GoI64 and [<=] is antisymmetric — the int64 analogue of
    the GoU64 order laws (pure [Z]-order + [i64_ext]). *)
Lemma i64_ltb_irrefl : forall a, i64_ltb a a = false.
Proof. intros. unfold i64_ltb. apply Z.ltb_irrefl. Qed.
Lemma i64_ltb_trans : forall a b c, i64_ltb a b = true -> i64_ltb b c = true -> i64_ltb a c = true.
Proof. intros a b c Hab Hbc. unfold i64_ltb in *. apply Z.ltb_lt in Hab, Hbc. apply Z.ltb_lt. lia. Qed.
Lemma i64_lt_trichotomy : forall a b, i64_ltb a b = true \/ a = b \/ i64_ltb b a = true.
Proof.
  intros a b. unfold i64_ltb. destruct (Z.lt_trichotomy (i64raw a) (i64raw b)) as [H|[H|H]].
  - left. apply Z.ltb_lt. exact H.
  - right; left. apply i64_ext. exact H.
  - right; right. apply Z.ltb_lt. exact H.
Qed.
Lemma i64_leb_antisym : forall a b, i64_leb a b = true -> i64_leb b a = true -> a = b.
Proof.
  intros a b Hab Hba. unfold i64_leb in *. apply i64_ext.
  apply Z.le_antisymm; apply Z.leb_le; assumption.
Qed.

(* Integer absolute value.  Go has NO abs builtin for ints (only [math.Abs] for
   floats — and that needs an import), so it is written by hand with an [if] in
   VALUE position: [|a| = if a < 0 then -a else a].  Faithful across the WHOLE
   int64 range INCLUDING the [MININT] corner: [0 - MININT] is the exact [2^63],
   which [wrap64] lands back at [MININT] — exactly Go's two's-complement
   [0 - a] (the classic [abs(math.MinInt64) = math.MinInt64] overflow).  This is
   the canonical demo of the pure-function tail-match lowering: the
   body's [if] is a value-position match, lowered to an [if]/[else] whose arms
   each [return]. *)
Definition i64_abs (a : GoI64) : GoI64 :=
  if i64_ltb a (i64wrap 0) then i64_sub (i64wrap 0) a else a.
(* DIV/MOD: Go truncates toward ZERO ([Z.quot]/[Z.rem]) — NOT Coq's flooring
   [Z.div]/[Z.modulo] (which give [-7/2 = -4]).  Evidence-carrying non-zero divisor
   (Go panics on /0).  [wrap64] lands the lone overflow case [MININT / -1 = MININT]
   (the exact quotient [2^63] wraps to [-2^63], Go's two's-complement behaviour). *)
Definition i64_div (a b : GoI64) (_ : Z.eqb (i64raw b) 0%Z = false) : GoI64 := i64wrap (wrap64 (Z.quot (i64raw a) (i64raw b))).
Definition i64_mod (a b : GoI64) (_ : Z.eqb (i64raw b) 0%Z = false) : GoI64 := i64wrap (wrap64 (Z.rem (i64raw a) (i64raw b))).
(* BITWISE: Go int64 [& | ^ &^] and unary [^] on the 64-bit two's-complement value.
   [Z.land]/[lor]/[lxor]/[lnot] use infinite two's complement, which agrees on the
   low 64 bits; the result of in-range operands stays in range, so [wrap64] is the
   identity here (kept for uniformity).  Unary [^x = -x-1]. *)
Definition i64_and    (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.land (i64raw a) (i64raw b))).
Definition i64_or     (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.lor  (i64raw a) (i64raw b))).
Definition i64_xor    (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.lxor (i64raw a) (i64raw b))).
Definition i64_andnot (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.land (i64raw a) (Z.lnot (i64raw b)))).
Definition i64_not    (a   : GoI64) : GoI64 := i64wrap (wrap64 (Z.lnot (i64raw a))).
(* SHIFTS: [<<] wraps mod 2^64 ([wrap64 . Z.shiftl]); [>>] is ARITHMETIC (sign-
   filling) for signed = [Z.shiftr] (floor toward -inf, in range).  Evidence-
   carrying non-negative count (Go panics on a negative shift). *)
Definition i64_shl (x : GoI64) (k : Z) (_ : (0 <=? k)%Z = true) : GoI64 := i64wrap (wrap64 (Z.shiftl (i64raw x) k)).
Definition i64_shr (x : GoI64) (k : Z) (_ : (0 <=? k)%Z = true) : GoI64 := i64wrap (Z.shiftr (i64raw x) k).

(* Build-checked: a constant that does not fit int64 is UNREPRESENTABLE (Go's
   constant-overflow compile error), and int64 does not implicitly mix with [int]. *)
Fail Definition i64_const_oob : GoI64 := i64_lit 9223372036854775808%Z eq_refl.  (* = 2^63 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int64 (in_i64 proof false). *)
Fail Definition i64_forged : GoI64 := MkI64 9223372036854775808%Z (squash eq_refl).
Fail Definition i64_no_implicit (x : GoI64) : GoI64 := i64_add x (5 : nat).
(* Build-checked: a ZERO divisor / NEGATIVE shift count is UNREPRESENTABLE (Go panics). *)
Fail Definition i64_div_zero : GoI64 := i64_div (i64_lit 1%Z eq_refl) (i64_lit 0%Z eq_refl) eq_refl.
Fail Definition i64_shl_neg  : GoI64 := i64_shl (i64_lit 1%Z eq_refl) (-1)%Z eq_refl.

(** ---- GoU64: FULL-WIDTH unsigned 64-bit integer (Go spec "Numeric types") ----

    Carried by [Z], normalised into [[0, 2^64)] after every op by [wrapU64]
    (always non-negative — Z.modulo of a positive modulus is non-negative).
    Extraction erases the wrapper; a [GoU64] value is a Go [uint64], which wraps
    unsigned-natively at [2^64], so the emitted ops need no mask.

    Comparison uses [Z.ltb]/[Z.leb] on non-negative operands, which gives the
    unsigned order (Z order agrees with unsigned order for non-negative values).

    Division: [Z.div]/[Z.modulo] (floored) agree with Go's truncating uint64
    division since both dividend and divisor are non-negative (floor = truncate
    for non-negative).

    Bitwise: [Z.land]/[Z.lor]/[Z.lxor] on non-negative operands stay in
    [[0, 2^64)] — no mask needed.  [Z.lnot n = -(n+1)] is negative, so
    [wrapU64] brings it back to [2^64-1-n] (the 64-bit bitwise complement).
    [Z.land n (Z.lnot m)] for n ≥ 0 stays ≥ 0 (and < 2^64) — no wrap needed.

    Shifts: [<<] wraps mod [2^64] via [wrapU64 . Z.shiftl]; [>>] is LOGICAL
    (for unsigned, arithmetic = logical), so [Z.shiftr n k] is exact for n ≥ 0. *)
(* [in_u64]/[wrapU64] are hoisted to the wrapper-record block (the GoU64 range invariant needs them).
   [wrapU64 z = z mod 2^64] is always in range, so [u64wrap] carries the proof from one lemma; a forged
   [u64wrap (2^64) _] is unconstructable ([in_u64 (2^64)] is false). *)
Lemma in_u64_wrapU64 : forall z, in_u64 (wrapU64 z) = true.
Proof.
  intro z. unfold in_u64, wrapU64.
  pose proof (Z.mod_pos_bound z 18446744073709551616%Z ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u64wrap (z : Z) : GoU64 := MkU64 (wrapU64 z) (squash (in_u64_wrapU64 z)).
(* [u64_lit z _]: a uint64 constant; the proof is a representability check
   (must be in [0, 2^64)); an out-of-range literal is unrepresentable. *)
Definition u64_lit (z : Z) (pf : in_u64 z = true) : GoU64 := MkU64 z (squash pf).
(* Platform-uint [GoUint] literal — the EXACT [GoU64] shape: a proof-carrying smart
   constructor demanding [in_u64 z] (so [z] is in [[0, 2^64)]).  Like [u64_lit] it is [NoInline]'d and
   the plugin folds [uint_lit z _] → Go [uint(<decimal>)] — the wrapper unboxes to its [Z] carrier
   (SProp proof erased), so the [uint(…)] cast MUST come from this op (a raw [MkUint] would render the
   bare carrier, which Go infers as [int]).  An out-of-range constant is unrepresentable: [eq_refl]
   cannot prove [in_u64 z = true] when [z] ∉ [[0, 2^64)]. *)
Definition uint_lit (z : Z) (pf : in_u64 z = true) : GoUint := MkUint z (squash pf).
(* [uintwrap] — the TOTAL wrap into the platform-[uint] range (mod 2^64, [wrapU64] — Go's runtime
   [uint(x)] conversion semantics; [uint] is 64-bit here).  The proof-carrying [uint_lit] stays the
   fail-closed CONSTANT builder; this is the RUNTIME-conversion authority (GoSem tier R3). *)
Definition uintwrap (z : Z) : GoUint := MkUint (wrapU64 z) (squash (in_u64_wrapU64 z)).
Definition u64_add (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a + u64raw b)).
Definition u64_sub (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a - u64raw b)).
(* Unary negation: [-x] mod 2^64 (so [-1 = 2^64-1]).  Lowers to the prefix [-x]. *)
Definition u64_neg (a : GoU64) : GoU64 := u64wrap (wrapU64 (Z.opp (u64raw a))).
Definition u64_mul (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a * u64raw b)).
Definition u64_eqb (a b : GoU64) : bool := Z.eqb (u64raw a) (u64raw b).
Definition u64_ltb (a b : GoU64) : bool := Z.ltb (u64raw a) (u64raw b).
Definition u64_leb (a b : GoU64) : bool := Z.leb (u64raw a) (u64raw b).

(** ── GoU64 ARITHMETIC has the commutative-semiring CORE mod 2^64 — `+` and `*` are commutative,
    associative, and distributive — an algebraic-faithfulness check that the modelled uint64
    arithmetic has the expected structure (wraparound is a ring homomorphism Z → Z/2^64, so it
    preserves these).  Two [GoU64] with equal raw [Z] are EQUAL — the second (SProp range) field is
    proof-irrelevant ([u64_ext]) — so every law reduces to a [Z]-mod identity. ── *)
Lemma u64_ext : forall x y : GoU64, u64raw x = u64raw y -> x = y.
Proof. intros [rx px] [ry py] H. cbn in H. subst ry. reflexivity. Qed.

Lemma u64raw_add : forall a b, u64raw (u64_add a b) = wrapU64 (u64raw a + u64raw b).
Proof. intros. unfold u64_add, u64wrap. cbn. unfold wrapU64. apply Zmod_mod. Qed.
Lemma u64raw_mul : forall a b, u64raw (u64_mul a b) = wrapU64 (u64raw a * u64raw b).
Proof. intros. unfold u64_mul, u64wrap. cbn. unfold wrapU64. apply Zmod_mod. Qed.

Lemma u64_add_comm : forall a b, u64_add a b = u64_add b a.
Proof. intros. apply u64_ext. rewrite !u64raw_add, (Z.add_comm (u64raw a)). reflexivity. Qed.
Lemma u64_mul_comm : forall a b, u64_mul a b = u64_mul b a.
Proof. intros. apply u64_ext. rewrite !u64raw_mul, (Z.mul_comm (u64raw a)). reflexivity. Qed.

Lemma u64_add_assoc : forall a b c, u64_add a (u64_add b c) = u64_add (u64_add a b) c.
Proof.
  intros. apply u64_ext. rewrite !u64raw_add. unfold wrapU64.
  rewrite Z.add_mod_idemp_r, Z.add_mod_idemp_l by (intro H; discriminate H).
  f_equal. ring.
Qed.
Lemma u64_mul_assoc : forall a b c, u64_mul a (u64_mul b c) = u64_mul (u64_mul a b) c.
Proof.
  intros. apply u64_ext. rewrite !u64raw_mul. unfold wrapU64.
  rewrite Z.mul_mod_idemp_r, Z.mul_mod_idemp_l by (intro H; discriminate H).
  f_equal. ring.
Qed.
Lemma u64_mul_add_distr_l : forall a b c,
  u64_mul a (u64_add b c) = u64_add (u64_mul a b) (u64_mul a c).
Proof.
  intros. apply u64_ext. rewrite !u64raw_add, !u64raw_mul, !u64raw_add. unfold wrapU64.
  rewrite Z.mul_mod_idemp_r, Z.add_mod_idemp_l, Z.add_mod_idemp_r by (intro H; discriminate H).
  f_equal. ring.
Qed.

(** [<] is a STRICT TOTAL ORDER on GoU64 (irreflexive, transitive, trichotomous) and [<=] is
    antisymmetric — Go's comparison operators on uint64 are a well-behaved total order, a
    completeness check the value-witnesses don't give.  (Pure [Z]-order + [u64_ext]; the SProp range
    field is never needed.) *)
Lemma u64_ltb_irrefl : forall a, u64_ltb a a = false.
Proof. intros. unfold u64_ltb. apply Z.ltb_irrefl. Qed.
Lemma u64_ltb_trans : forall a b c, u64_ltb a b = true -> u64_ltb b c = true -> u64_ltb a c = true.
Proof. intros a b c Hab Hbc. unfold u64_ltb in *. apply Z.ltb_lt in Hab, Hbc. apply Z.ltb_lt. lia. Qed.
Lemma u64_lt_trichotomy : forall a b, u64_ltb a b = true \/ a = b \/ u64_ltb b a = true.
Proof.
  intros a b. unfold u64_ltb. destruct (Z.lt_trichotomy (u64raw a) (u64raw b)) as [H|[H|H]].
  - left. apply Z.ltb_lt. exact H.
  - right; left. apply u64_ext. exact H.
  - right; right. apply Z.ltb_lt. exact H.
Qed.
Lemma u64_leb_antisym : forall a b, u64_leb a b = true -> u64_leb b a = true -> a = b.
Proof.
  intros a b Hab Hba. unfold u64_leb in *. apply u64_ext.
  apply Z.le_antisymm; apply Z.leb_le; assumption.
Qed.

(** Direct [>] / [>=] / [!=] completing Go's six comparison operators for the
    canonical [int64]/[uint64].  We already emit [== < <=] directly; [>]/[>=] are the
    swapped [</<=] and [!=] is [negb (==)] — SEMANTICALLY identical to the encodings a
    program would otherwise write, but each is recognized by name and lowered to the
    DIRECT Go operator ([a > b], not [b < a]), so the emitted Go matches the source
    operator.  (The [int64] order is signed, the [uint64] order unsigned, inherited
    from [i64_ltb]/[u64_ltb].) *)
Definition i64_gtb  (a b : GoI64) : bool := i64_ltb b a.
Definition i64_geb  (a b : GoI64) : bool := i64_leb b a.
Definition i64_neqb (a b : GoI64) : bool := negb (i64_eqb a b).
Definition u64_gtb  (a b : GoU64) : bool := u64_ltb b a.
Definition u64_geb  (a b : GoU64) : bool := u64_leb b a.
Definition u64_neqb (a b : GoU64) : bool := negb (u64_eqb a b).
(* DIVISION: evidence-carrying non-zero divisor (Go panics on /0).  [Z.div] and
   [Z.modulo] are used here (floored) — for non-negative values they agree with
   Go's truncating division, so the result is exact.  No wrap needed: both
   results stay in [[0, 2^64)]. *)
Definition u64_div (a b : GoU64) (_ : Z.eqb (u64raw b) 0%Z = false) : GoU64 := u64wrap (Z.div    (u64raw a) (u64raw b)).
Definition u64_mod (a b : GoU64) (_ : Z.eqb (u64raw b) 0%Z = false) : GoU64 := u64wrap (Z.modulo (u64raw a) (u64raw b)).
Definition u64_and    (a b : GoU64) : GoU64 := u64wrap (Z.land (u64raw a) (u64raw b)).
Definition u64_or     (a b : GoU64) : GoU64 := u64wrap (Z.lor  (u64raw a) (u64raw b)).
Definition u64_xor    (a b : GoU64) : GoU64 := u64wrap (Z.lxor (u64raw a) (u64raw b)).
Definition u64_andnot (a b : GoU64) : GoU64 := u64wrap (Z.land (u64raw a) (Z.lnot (u64raw b))).
Definition u64_not    (a   : GoU64) : GoU64 := u64wrap (wrapU64 (Z.lnot (u64raw a))).
Definition u64_shl (x : GoU64) (k : Z) (_ : (0 <=? k)%Z = true) : GoU64 := u64wrap (wrapU64 (Z.shiftl (u64raw x) k)).
Definition u64_shr (x : GoU64) (k : Z) (_ : (0 <=? k)%Z = true) : GoU64 := u64wrap (Z.shiftr (u64raw x) k).

(* Build-checked: a constant >= 2^64 is UNREPRESENTABLE; uint64 does not
   implicitly mix with [int], [GoI64], or other types. *)
Fail Definition u64_const_oob : GoU64 := u64_lit 18446744073709551616%Z eq_refl.  (* = 2^64 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint64 (in_u64 proof false). *)
Fail Definition u64_forged : GoU64 := MkU64 18446744073709551616%Z (squash eq_refl).
Fail Definition u64_no_implicit (x : GoU64) : GoU64 := u64_add x (5 : nat).
(* Build-checked: a ZERO divisor / NEGATIVE shift count is UNREPRESENTABLE. *)
Fail Definition u64_div_zero : GoU64 := u64_div (u64_lit 1%Z eq_refl) (u64_lit 0%Z eq_refl) eq_refl.
Fail Definition u64_shl_neg  : GoU64 := u64_shl (u64_lit 1%Z eq_refl) (-1)%Z eq_refl.

(** ---- Bitwise BOOLEAN-ALGEBRA laws for GoU64 (the bitwise counterpart of the proven arithmetic
    semiring + total-order laws).  COMMUTATIVITY holds directly; ASSOCIATIVITY needs that [wrapU64]
    (mod 2⁶⁴) depends only on the LOW 64 bits — so an inner [wrapU64] under a bit-op can be pulled out
    ([wrapU64_bit_r]/[_l], one [Z.bits_inj'] each).  (Idempotence [a & a = a] is SProp-BLOCKED: it
    needs [u64raw a] in range, which the [Squash] seal hides from [Prop] — documented, not skipped.) *)
Lemma wrapU64_bit_r : forall (op : Z -> Z -> Z) (bf : bool -> bool -> bool),
  (forall x y n, Z.testbit (op x y) n = bf (Z.testbit x n) (Z.testbit y n)) ->
  forall a b, wrapU64 (op a (wrapU64 b)) = wrapU64 (op a b).
Proof.
  intros op bf Hspec a b. unfold wrapU64. change 18446744073709551616%Z with (2 ^ 64)%Z.
  apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Hspec.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma wrapU64_bit_l : forall (op : Z -> Z -> Z) (bf : bool -> bool -> bool),
  (forall x y n, Z.testbit (op x y) n = bf (Z.testbit x n) (Z.testbit y n)) ->
  forall a b, wrapU64 (op (wrapU64 a) b) = wrapU64 (op a b).
Proof.
  intros op bf Hspec a b. unfold wrapU64. change 18446744073709551616%Z with (2 ^ 64)%Z.
  apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Hspec.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma u64_and_comm : forall a b, u64_and a b = u64_and b a.
Proof. intros a b. apply u64_ext. unfold u64_and, u64wrap; cbn. f_equal. apply Z.land_comm. Qed.
Lemma u64_or_comm  : forall a b, u64_or a b = u64_or b a.
Proof. intros a b. apply u64_ext. unfold u64_or, u64wrap; cbn. f_equal. apply Z.lor_comm. Qed.
Lemma u64_xor_comm : forall a b, u64_xor a b = u64_xor b a.
Proof. intros a b. apply u64_ext. unfold u64_xor, u64wrap; cbn. f_equal. apply Z.lxor_comm. Qed.

Lemma u64_and_assoc : forall a b c, u64_and a (u64_and b c) = u64_and (u64_and a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_and, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.land andb Z.land_spec), (wrapU64_bit_l Z.land andb Z.land_spec).
  f_equal. apply Z.land_assoc.
Qed.
Lemma u64_or_assoc : forall a b c, u64_or a (u64_or b c) = u64_or (u64_or a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_or, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.lor orb Z.lor_spec), (wrapU64_bit_l Z.lor orb Z.lor_spec).
  f_equal. apply Z.lor_assoc.
Qed.
Lemma u64_xor_assoc : forall a b c, u64_xor a (u64_xor b c) = u64_xor (u64_xor a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_xor, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.lxor xorb Z.lxor_spec), (wrapU64_bit_l Z.lxor xorb Z.lxor_spec).
  f_equal. symmetry. apply Z.lxor_assoc.
Qed.

(** ---- GoI64 / GoU64 are THE canonical Go int64 / uint64 ----

    [GoI64]/[GoU64] (the [Z]-carried full-width types) are the faithful models of
    Go's [int64]/[uint64].  These abbreviations + scopes make them as ERGONOMIC as
    a primitive: [42%i64] is a range-checked int64 literal, [(a + b)%i64] is
    full-width addition.

    The literal parser ([i64_of_Z]/[u64_of_Z]) RANGE-CHECKS at PARSE TIME,
    returning [None] for an out-of-range numeral — an over-wide literal is
    REJECTED, exactly Go's untyped-constant overflow compile error.  The parser's
    range check is the proof, so the literal builds the raw [MkI64]/[MkU64] with
    no separate [_lit] obligation. *)
Notation int64  := GoI64.
Notation uint64 := GoU64.

Definition i64_of_Z (z : Z) : option GoI64 := if in_i64 z then Some (i64wrap z) else None.  (* wrap64 z = z under the guard *)
Definition Z_of_i64 (x : GoI64) : Z := i64raw x.
Definition u64_of_Z (z : Z) : option GoU64 := if in_u64 z then Some (u64wrap z) else None.  (* wrapU64 z = z under the guard *)
Definition Z_of_u64 (x : GoU64) : Z := u64raw x.

Declare Scope i64_scope.
Delimit Scope i64_scope with i64.
Bind Scope i64_scope with GoI64.
Number Notation GoI64 i64_of_Z Z_of_i64 : i64_scope.
Infix "+"  := i64_add : i64_scope.
Infix "-"  := i64_sub : i64_scope.
Infix "*"  := i64_mul : i64_scope.
Infix "=?" := i64_eqb : i64_scope.
Infix "<?" := i64_ltb : i64_scope.
Infix "<=?" := i64_leb : i64_scope.

Declare Scope u64_scope.
Delimit Scope u64_scope with u64.
Bind Scope u64_scope with GoU64.
Number Notation GoU64 u64_of_Z Z_of_u64 : u64_scope.
Infix "+"  := u64_add : u64_scope.
Infix "-"  := u64_sub : u64_scope.
Infix "*"  := u64_mul : u64_scope.
Infix "=?" := u64_eqb : u64_scope.
Infix "<?" := u64_ltb : u64_scope.
Infix "<=?" := u64_leb : u64_scope.

(* Build-checked: an out-of-range literal is REJECTED AT PARSE (Go untyped-constant
   overflow).  [2^63] overflows int64 (max [2^63-1]); [2^64] overflows uint64. *)
Fail Definition i64_lit_oob : GoI64 := (9223372036854775808)%i64.   (* = 2^63 *)
Fail Definition u64_lit_oob : GoU64 := (18446744073709551616)%u64.  (* = 2^64 *)
(* Platform-uint: the proof-carrying [uint_lit] range-checks too — [eq_refl] cannot prove
   [in_u64 (2^64) = true], so an out-of-range platform-uint constant is unrepresentable. *)
Fail Definition uint_lit_oob : GoUint := uint_lit 18446744073709551616 eq_refl.  (* = 2^64 *)

(** ---- Full-width int64 <-> uint64 CONVERSIONS (Go spec "Conversions") ----
    Go's [uint64(x)] / [int64(x)] between the two 64-bit integer types REINTERPRET
    the same 64-bit two's-complement pattern: the value is unchanged when it fits
    the target, otherwise it is the mod-2^64 representative (a negative int64 maps to
    its 2^64-complement uint64; a uint64 >= 2^63 maps to a negative int64).  The
    Z-carried model makes this EXACT — re-normalise the raw [Z] into the target's
    range — with NO rounding or loss (unlike int<->float).  [int_of_FW]/[FW_of_int]
    cover the NARROW widths; these are the full-width pair (distinct because [GoU64]
    lowers to a real Go [uint64], not [int64]). *)
Definition u64_of_i64 (a : GoI64) : GoU64 := u64wrap (wrapU64 (i64raw a)).
Definition i64_of_u64 (a : GoU64) : GoI64 := i64wrap (wrap64  (u64raw a)).

(* Reinterpret is mod-2^64 on both sides, so the two normalisers AGREE after a
   round-trip: [wrap64 (wrapU64 z) = wrap64 z] (both reduce mod 2^64 first). *)
Lemma wrap64_wrapU64 : forall z, wrap64 (wrapU64 z) = wrap64 z.
Proof.
  intro z. unfold wrap64, wrapU64.
  rewrite Zplus_mod_idemp_l.   (* (z mod 2^64 + 2^63) mod 2^64 = (z + 2^63) mod 2^64 *)
  reflexivity.
Qed.

(** SIGNED↔UNSIGNED bitwise FAITHFULNESS — Go: [a & b == int64(uint64(a) & uint64(b))].
    The signed bitwise op equals the SIGNED REINTERPRETATION of the UNSIGNED op on the two's-complement
    bit patterns, so [i64_and]/[_or]/[_xor] are FAITHFUL to Go's int64/uint64 bitwise agreement.  Proof:
    cancel the double mod-2⁶⁴ ([wrapU64_idem]), pull each [wrapU64] out through the bit-op
    ([wrapU64_bit_l]/[_r]), then collapse [wrap64 ∘ wrapU64 = wrap64]. *)
Lemma wrapU64_idem : forall z, wrapU64 (wrapU64 z) = wrapU64 z.
Proof. intro z. unfold wrapU64. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma i64_and_via_u64 : forall a b,
  i64_and a b = i64_of_u64 (u64_and (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_and i64_of_u64 u64_and u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.land andb Z.land_spec), (wrapU64_bit_r Z.land andb Z.land_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.
Lemma i64_or_via_u64 : forall a b,
  i64_or a b = i64_of_u64 (u64_or (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_or i64_of_u64 u64_or u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.lor orb Z.lor_spec), (wrapU64_bit_r Z.lor orb Z.lor_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.
Lemma i64_xor_via_u64 : forall a b,
  i64_xor a b = i64_of_u64 (u64_xor (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_xor i64_of_u64 u64_xor u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.lxor xorb Z.lxor_spec), (wrapU64_bit_r Z.lxor xorb Z.lxor_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.

(** ---- Untyped INTEGER constants (Go spec "Constants") ----

    A Go untyped constant is ARBITRARY-PRECISION: constant arithmetic is exact (no
    width, no wrap), and the constant acquires a fixed-width TYPE only at the point of
    USE, where a representability check fires — a constant that does not fit is a
    COMPILE ERROR, not a runtime wrap.  We model an untyped int constant as [Z], its
    arithmetic as [Z] arithmetic (exact), and the type-at-use conversion as
    [i64c]/[u64c]: each EVALUATES the closed [Z] expression with [vm_compute] (real
    bignums, so an INTERMEDIATE may exceed the target width — e.g. [1 << 70] — as long
    as the final value fits) to a literal, then converts demanding [in_i64]/[in_u64].
    An out-of-range constant FAILS to elaborate (the [now vm_compute] proof of
    representability cannot be built) — the analog of Go's untyped-constant overflow.
    The literal the notation produces lowers via the existing [i64_lit]/[u64_lit] fold;
    no plugin change — the arbitrary precision lives entirely in [vm_compute]. *)
Notation i64c e :=
  (i64_lit ltac:(let v := eval vm_compute in (e : Z) in exact v) ltac:(now vm_compute))
  (only parsing).
Notation u64c e :=
  (u64_lit ltac:(let v := eval vm_compute in (e : Z) in exact v) ltac:(now vm_compute))
  (only parsing).

(** ---- int64 → float64 conversion (Go spec "Conversions") ----

    Go [float64(i)] converts an [int64] to an IEEE double; values past 2^53 ROUND (the
    double's mantissa), exactly as Go does.  We round the EXACT signed [Z] mantissa ONCE to
    binary64 via [SpecFloat.binary_normalize] at format (53, 1024) — axiom-free, round-to-
    nearest-even, spanning the whole int64 range.  Recognised BY NAME → native Go [float64(i)]
    (machine-checked by [f64_of_i64_pos]/[f64_of_i64_neg] in main.v); the [binary_normalize]
    body is suppressed.  The reverse — float64→int64 TRUNCATION ([i64_of_f64]) — is modelled
    DIRECTLY on the [spec_float] representation below (no truncation primitive needed). *)
Definition f64_of_i64 (a : GoI64) : GoFloat64 := binary_normalize 53 1024 (i64raw a) 0 false.

(** int64 → narrow (Go [uint8(x)] / [int8(x)] / … / [int32(x)]): TRUNCATE to the low W bits.
    A [GoU8]/[GoI8]/… erases to the same int64 carrier as a [GoI64], so the conversion is
    EXACTLY the narrow-from-int truncation ([fw_wrap]: mask to W bits, sign-extend for [iN]) —
    lowered to Go's native [(x & 0xFF)] / sign-extended form, identical to [uN_of_int].  The model
    masks the [Z] carrier directly ([uNwrap]/[iNwrap] on [i64raw a]): for [W < 64] the low W bits
    of [i64raw a] are [(i64raw a) mod 2^W].
    The [wrap] body never reaches the emitted Go — the op is recognized by name (`fw_is r "of_i64"`)
    and its decl suppressed (`fixed_width_op`), exactly as the [of_int] narrows are. *)
Definition u8_of_i64  (a : GoI64) : GoU8  := u8wrap (i64raw a).
Definition i8_of_i64  (a : GoI64) : GoI8  := i8wrap (i64raw a).
Definition u16_of_i64 (a : GoI64) : GoU16 := u16wrap (i64raw a).
Definition i16_of_i64 (a : GoI64) : GoI16 := i16wrap (i64raw a).
Definition u32_of_i64 (a : GoI64) : GoU32 := u32wrap (i64raw a).
Definition i32_of_i64 (a : GoI64) : GoI32 := i32wrap (i64raw a).

(** int → float64 (Go [float64(i)]): the IEEE double NEAREST the integer (EXACT for |i| < 2^53,
    rounds beyond — exactly Go's rule).  Rounds the EXACT [Z] mantissa ONCE via [binary_normalize] at
    (53, 1024) — the SAME axiom-free Z→float path as [f64_of_i64] / [f32_of_int].  Recognized by name
    → native [float64(i)]; the [spec_float] body is suppressed.  Machine-checked by [f64_of_int_pos]/
    [f64_of_int_neg] (main.v). *)
Definition f64_of_int (i : GoInt) : GoFloat64 := binary_normalize 53 1024 (intraw i) 0 false.

(** float64 → int64 (Go [int64(f)]): TRUNCATE toward zero.  [GoFloat64] is [spec_float], so
    the decomposition is DIRECT — a finite [f = S754_finite s m e] is [(-1)^s * m * 2^e] ([m]
    positive, [e : Z]), no float-decomposition primitive.  The truncated MAGNITUDE is
    [m * 2^e] when [e >= 0] (an exact integer) or [m / 2^(-e)] when [e < 0] (the FLOOR of the
    positive magnitude = truncation toward zero); the sign is applied AFTER, so it rounds toward
    zero — exactly Go's rule.  [i64_of_f64] is recognised BY NAME → native [int64(f)] (the
    [f64_trunc_Z] body suppressed); machine-checked (witnesses in main.v).  *Bounded deviation:*
    NaN / ±Inf / out-of-int64-range inputs are IMPLEMENTATION-DEFINED in Go (spec "Conversions");
    the model gives [0] (and [wrap64] folds overflow) — a documented model gap on those corners;
    the FINITE in-range case (the common use) is faithful and machine-checked. *)
Definition f64_trunc_Z (f : GoFloat64) : Z :=
  match f with
  | S754_finite s m e =>
      let mag := if Z.leb 0 e then (Zpos m * 2 ^ e)%Z else (Zpos m / 2 ^ (- e))%Z in
      if s then (- mag)%Z else mag
  | _ => 0%Z
  end.
Definition i64_of_f64 (f : GoFloat64) : GoI64 := i64wrap (wrap64 (f64_trunc_Z f)).

(** float64 → uint64 (Go [uint64(f)]): TRUNCATE toward zero — the exact parallel of [i64_of_f64],
    only wrapping into the unsigned range.  In-range ([0 <= trunc f < 2^64]) it is faithful (the
    verified [f64_trunc_Z]); out of range is Go-implementation-defined, where the defined wrap is
    an acceptable choice.  Lowered to native [uint64(f)]; the [spec_float]-match body suppressed. *)
Definition u64_of_f64 (f : GoFloat64) : GoU64 := u64wrap (wrapU64 (f64_trunc_Z f)).

(** uint64 → float64 (Go [float64(v)]): the CORRECTLY-ROUNDED double.  Rounds the EXACT [Z] mantissa
    (in [[0, 2^64)]) ONCE via [binary_normalize] at (53, 1024) — the SAME Z→float path as the int64/
    int conversions, spanning the WHOLE uint64 range in one shot.  Lowered to native [float64(v)];
    the body suppressed. *)
Definition f64_of_u64 (a : GoU64) : GoFloat64 := binary_normalize 53 1024 (u64raw a) 0 false.

(** UNTYPED FLOAT CONSTANTS — exact rationals, rounded ONCE at the typed boundary.  Go folds
    constant float arithmetic at ARBITRARY precision, rounding only when the constant acquires a
    type: [const x float64 = 0.1 + 0.2] is [float64(3/10) = 0.3] EXACTLY, NOT the runtime
    [0.1+0.2 = 0.30000000000000004] (which rounds each operand THEN adds).  Fido's runtime floats
    ([spec_float] arithmetic) give the runtime answer; this models the CONSTANT one.  An [FConst] is an exact
    rational [num/den]; [fc_add]/[fc_sub]/[fc_mul] are EXACT ([Q]-style cross-multiply, no
    rounding); [f64_of_fconst] rounds exactly ONCE (its own contract below is the rounding
    authority).  MODEL + machine-checked; the plugin's FConst-fold lowers a CONSTANT
    expression whose int64-CHECKED endpoints fold — beyond int64 the fold declines and
    extraction fails loud. *)
(** The denominator is a [positive] — exactly the shape of Coq's [QArith.Q] — so a Go
    float CONSTANT is an EXACT *nonzero-denominator* rational and can NEVER denote ±Inf
    or NaN.  A malformed [den = 0] constant is UNCONSTRUCTABLE by
    type, so the extractor's [den = 0] fold guard is a dead defensive boundary rather than
    a reachable path.  [Bind Scope] keeps [mkFC n d] literals parsing [d] as a positive. *)
Record FConst := mkFC { fc_num : Z ; fc_den : positive }.
Bind Scope positive_scope with positive.
Definition fc_add (a b : FConst) : FConst :=
  mkFC (fc_num a * Zpos (fc_den b) + fc_num b * Zpos (fc_den a)) (Pos.mul (fc_den a) (fc_den b)).
Definition fc_sub (a b : FConst) : FConst :=
  mkFC (fc_num a * Zpos (fc_den b) - fc_num b * Zpos (fc_den a)) (Pos.mul (fc_den a) (fc_den b)).
Definition fc_mul (a b : FConst) : FConst := mkFC (fc_num a * fc_num b) (Pos.mul (fc_den a) (fc_den b)).
(** Constant DIVISION is EVIDENCE-CARRYING: Go constant division by zero is a COMPILE error,
    so [fc_div] DEMANDS a proof the divisor's numerator is nonzero — a constant [/0] cannot be
    written.  The denominator stays strictly positive by
    folding the divisor's SIGN into the numerator:
      (na/da)/(nb/db) = (na·db)/(da·nb) = (sgn(nb)·na·db)/(da·|nb|). *)
Definition fc_div (a b : FConst) (hb : fc_num b <> 0%Z) : FConst :=
  mkFC (Z.sgn (fc_num b) * fc_num a * Zpos (fc_den b))
       (Pos.mul (fc_den a) (Z.to_pos (Z.abs (fc_num b)))).  (* (a/b)/(c/d) = ad/bc, den kept > 0 *)
(** ([sf_of_Z] — exact [Z] → [spec_float] — is defined up with the float64 ops.) *)
(** Exact float CONSTANT → float64 — round the EXACT rational [num/den] ONCE to binary64 via [SFdiv]
    of the EXACT-integer spec_floats (no intermediate binary64), so correctly-rounded for ALL num/den,
    not just [< 2^53].  Lowered to Go [float64(num.0 / den.0)] (untyped-constant division, single
    round). *)
Definition f64_of_fconst (a : FConst) : GoFloat64 :=
  SFdiv 53 1024 (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a))).

(** FLOAT32 arithmetic — faithful binary32 (prec 24, emax 128) via [SpecFloat], then routed
    back through [f32_of_f64] so the result re-enters the abstract type WITH its provenance
    proof ([eq_refl]).  The extra round is the IDENTITY in reality (an [SFadd]/… result is
    already in binary32 format), so this stays faithful — exactly Go's [float32] arithmetic
    (single round-to-nearest-even at binary32).  Lowered BY NAME to native Go [float32]
    [+]/[-]/[*]/[/]; the SpecFloat body (and the [f32val]/[mkF32] wrapping) is suppressed. *)
Definition f32_add (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFadd 24 128 (f32val x) (f32val y)).
Definition f32_sub (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFsub 24 128 (f32val x) (f32val y)).
Definition f32_mul (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFmul 24 128 (f32val x) (f32val y)).
Definition f32_div (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SFdiv 24 128 (f32val x) (f32val y)).

(** float32 COMPARISON.  The carrier holds a binary32-CANONICAL value and a comparison performs
    NO rounding, so [SFltb]/[SFleb]/[SFeqb] on [f32val] ARE the float32 comparisons (both operands
    are binary32-canonical, so [SFcompare]'s representation-sensitivity is satisfied).  Lowered to
    native Go [float32] [<]/[<=]/[==]/[>]/[>=]/[!=].  Same NaN subtlety as float64: [f32_geb]/
    [f32_gtb] are the SWAPPED [leb]/[ltb] (so a NaN operand makes [>=]/[>] FALSE), [f32_neqb] is
    [negb (eqb)]. *)
Definition f32_ltb  (x y : GoFloat32) : bool := SFltb (f32val x) (f32val y).
Definition f32_leb  (x y : GoFloat32) : bool := SFleb (f32val x) (f32val y).
Definition f32_eqb  (x y : GoFloat32) : bool := SFeqb (f32val x) (f32val y).
Definition f32_gtb  (x y : GoFloat32) : bool := SFltb (f32val y) (f32val x).
Definition f32_geb  (x y : GoFloat32) : bool := SFleb (f32val y) (f32val x).
Definition f32_neqb (x y : GoFloat32) : bool := negb (SFeqb (f32val x) (f32val y)).

(** float32 → float64 WIDENING is EXACT (a binary32 value is exactly a binary64): the carrier
    re-canonicalised to binary64 ([renorm 53 1024] — exact, no rounding, since binary32 ⊂ binary64),
    SOUND because [f32ok] guarantees the carrier is binary32-representable.  Lowered to Go
    [float64(x)].  (Narrowing [f32_of_f64] / [f32_lit] is defined up top, with the type.) *)
Definition f64_of_f32 (x : GoFloat32) : GoFloat64 := renorm 53 1024 (f32val x).

(** DIRECT integer → float32 (Go [float32(x)]) — round the EXACT integer ONCE to binary32 via
    [binary_normalize] at format (24, 128).  This is NOT [f32_of_f64 (f64_of_int x)] (= Go
    [float32(float64(x))]): for |x| > 2^53 the int→float64 step ALREADY rounds, and the second
    round to binary32 can DISAGREE — double rounding.  (E.g. [x = 2^61 + 2^37 + 1]: direct rounds
    UP to [2^61 + 2^38]; via float64 the low bit is lost onto the float32 midpoint and ties-to-even
    rounds DOWN to [2^61].)  Lowered to Go's direct [float32(x)] cast (single round). *)
Definition f32_of_i64 (a : GoI64) : GoFloat32 :=
  f32_of_f64 (binary_normalize 24 128 (i64raw a) 0 false).
Definition f32_of_u64 (a : GoU64) : GoFloat32 :=
  f32_of_f64 (binary_normalize 24 128 (u64raw a) 0 false).
Definition f32_of_int (i : GoInt) : GoFloat32 :=
  f32_of_f64 (binary_normalize 24 128 (intraw i) 0 false).

(** DIRECT exact float CONSTANT → float32 (Go [float32(num.0 / den.0)]): round the EXACT rational
    [num/den] ONCE to binary32 via [SFdiv] of the EXACT-integer spec_floats (no intermediate binary64
    — so correct for ALL [num], [den], unlike [f32_of_f64 (f64_of_fconst …)] which double-rounds when
    [|num| > 2^53]: e.g. [2305843146652647425/1] rounds to [2^61+2^38] here but [2^61] via float64).
    [SFdiv] handles arbitrary mantissas, so this is the correctly-rounded rational→binary32. *)
Definition f32_of_fconst (a : FConst) : GoFloat32 :=
  f32_of_f64 (SFdiv 24 128 (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a)))).

(** float32 unary NEGATION — EXACT (IEEE sign-flip, makes [-0.0]); re-enter the abstract type
    (the round is the identity on the sign-flipped, still-representable value).  Lowered to Go
    [-x].  Same role as [f64_opp] for float64. *)
Definition f32_neg (x : GoFloat32) : GoFloat32 := f32_of_f64 (SFopp (f32val x)).

(** [min]/[max] on float32 (Go "min and max") — the SAME two IEEE corners as float64, decided on
    the binary32 carriers: NaN propagation ([eqb v v = false]) and signed zero ([min(-0,+0) = -0],
    [max(-0,+0) = +0], via [1/v]).  Each returns the chosen OPERAND, already a valid [GoFloat32],
    so there is no re-rounding.  Lowered to Go [min]/[max] on float32. *)
Definition f32_min (x y : GoFloat32) : GoFloat32 :=
  if negb (SFeqb (f32val x) (f32val x)) then x            (* x is NaN → NaN *)
  else if negb (SFeqb (f32val y) (f32val y)) then y       (* y is NaN → NaN *)
  else if SFltb (f32val x) (f32val y) then x
  else if SFltb (f32val y) (f32val x) then y
  else if SFeqb (f32val x) (S754_zero false)
       then (if SFltb (SFdiv 24 128 (sf_of_Z 1) (f32val x)) (S754_zero false) then x else y)   (* min wants -0 *)
       else x.
Definition f32_max (x y : GoFloat32) : GoFloat32 :=
  if negb (SFeqb (f32val x) (f32val x)) then x
  else if negb (SFeqb (f32val y) (f32val y)) then y
  else if SFltb (f32val x) (f32val y) then y
  else if SFltb (f32val y) (f32val x) then x
  else if SFeqb (f32val x) (S754_zero false)
       then (if SFltb (SFdiv 24 128 (sf_of_Z 1) (f32val x)) (S754_zero false) then y else x)   (* max wants +0 *)
       else x.

(** ==================================================================================================
    [min]/[max] (Go 1.21 predeclared builtins) on int/int64/uint64 — each type's own order — and
    the FAITHFUL float [min]/[max] + direct [>]/[>=]/[!=] float comparisons (NaN propagation,
    signed-zero rule, [>=] is the SWAPPED [leb], never [¬(<)]).  Pure; mined out of the frozen
    builtins.v monolith (plans/builtins-split.md).
    ================================================================================================ *)

(** [min]/[max] (Go 1.21 predeclared builtins) on [int] — the smaller / larger of
    two values, by the SIGNED ordering (Go's int [<]), so [go_min] = Go [min(a,b)]
    and [go_max] = Go [max(a,b)] for the [int] type.  Computable (so [go_min 3 5 =
    3] is a THEOREM); the plugin lowers the call to Go's builtin.  (Go's [min]/[max]
    also apply to floats — with NaN/`-0` corner cases — and strings; those follow
    once those orderings are settled.) *)
Definition go_min (a b : GoInt) : GoInt := if int_ltb a b then a else b.
Definition go_max (a b : GoInt) : GoInt := if int_ltb a b then b else a.

(** [min]/[max] on the CANONICAL full-width types: [int64] ([GoI64], SIGNED order via
    [i64_ltb]) and [uint64] ([GoU64], UNSIGNED order via [u64_ltb]) — each exactly Go's
    [min(a,b)]/[max(a,b)] for that type.  Computable theorems; the plugin lowers each
    call to the Go builtin.  No carrier bridge (the comparison is the type's own [<]). *)
Definition i64_min (a b : GoI64) : GoI64 := if i64_ltb a b then a else b.
Definition i64_max (a b : GoI64) : GoI64 := if i64_ltb a b then b else a.
Definition u64_min (a b : GoU64) : GoU64 := if u64_ltb a b then a else b.
Definition u64_max (a b : GoU64) : GoU64 := if u64_ltb a b then b else a.

(** [min]/[max] on FLOAT (Go spec "min and max" — the float rules).  A naive
    [if a < b] is WRONG on two IEEE corners that Go's builtin handles, so we model
    them faithfully (the body is suppressed; each call lowers to Go's [min]/[max],
    which does the same):
    - NaN PROPAGATION: if either argument is a NaN, the result is a NaN.  Detected by
      [eqb x x = false] (only NaN is unequal to itself).
    - SIGNED ZERO: when the two are numerically EQUAL and are [±0], [max] yields [+0]
      and [min] yields [-0] (Go treats [+0 > -0]).  Detected by [eqb a 0] (both are
      [±0]) and [1/a < 0] (a is the negative zero, since [1 / -0 = -inf]).
    Otherwise the smaller / larger by [ltb].  Machine-checked on all these corners. *)
Definition f64_min (a b : GoFloat64) : GoFloat64 :=
  if negb (SFeqb a a) then a            (* a is NaN → NaN *)
  else if negb (SFeqb b b) then b       (* b is NaN → NaN *)
  else if SFltb a b then a
  else if SFltb b a then b
  else (* numerically equal (incl. ±0) *)
    if SFeqb a (S754_zero false)
    then (if SFltb (SFdiv 53 1024 (sf_of_Z 1) a) (S754_zero false) then a else b)   (* min wants -0 *)
    else a.
Definition f64_max (a b : GoFloat64) : GoFloat64 :=
  if negb (SFeqb a a) then a            (* a is NaN → NaN *)
  else if negb (SFeqb b b) then b       (* b is NaN → NaN *)
  else if SFltb a b then b
  else if SFltb b a then a
  else (* numerically equal (incl. ±0) *)
    if SFeqb a (S754_zero false)
    then (if SFltb (SFdiv 53 1024 (sf_of_Z 1) a) (S754_zero false) then b else a)   (* max wants +0 *)
    else a.

(** Direct [>] / [>=] / [!=] for float64.  CRUCIAL NaN subtlety: [>=] is NOT
    [¬(<)] — with a NaN operand, [a >= b] is FALSE (Go/IEEE), whereas [¬(a < b)]
    would be TRUE.  So [f64_geb] is the SWAPPED [leb] ([b <= a]), and [f64_gtb] the
    swapped [ltb] — both correctly false on NaN.  [f64_neqb] IS [negb (eqb)] (a NaN
    compares UNEQUAL to everything, so [a != b] is true — matching [negb false]). *)
Definition f64_gtb  (a b : GoFloat64) : bool := SFltb b a.
Definition f64_geb  (a b : GoFloat64) : bool := SFleb b a.
Definition f64_neqb (a b : GoFloat64) : bool := negb (SFeqb a b).
