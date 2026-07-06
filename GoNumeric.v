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

