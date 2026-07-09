(** ==================================================================================================
    GoComplex — Go's complex numbers (spec "Complex numbers"): [GoComplex128] as a pair of
    [GoFloat64]s, the predeclared [complex]/[real]/[imag], component-wise +/-, the exact
    Gauss product, faithful complex division, and ==/!= — all PURE over the spec_float layer.
    ================================================================================================ *)

From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.

(** ---- Complex numbers (Go spec "Complex numbers"; the predeclared [complex]/[real]/
    [imag] builtins) ----  A [complex128] is a pair of [float64] components.  We model it
    as a 2-field record over [float]; the plugin renders the type as Go's native
    [complex128] and lowers [go_complex]/[go_real]/[go_imag] to the predeclared builtins
    [complex(re, im)] / [real(c)] / [imag(c)] (the record's struct decl, constructor, and
    projections are all suppressed — recognised by operation name, like the numint
    wrappers).  Construction/extraction are PROVABLE ([go_real (go_complex re im) = re]). *)
Record GoComplex128 : Type := MkComplex128 { c_re : GoFloat64 ; c_im : GoFloat64 }.
Definition go_complex (re im : GoFloat64) : GoComplex128 := MkComplex128 re im.
Definition go_real (c : GoComplex128) : GoFloat64 := c_re c.
Definition go_imag (c : GoComplex128) : GoFloat64 := c_im c.

Example go_real_complex : forall re im, go_real (go_complex re im) = re.
Proof. reflexivity. Qed.
Example go_imag_complex : forall re im, go_imag (go_complex re im) = im.
Proof. reflexivity. Qed.

(** Complex ARITHMETIC — Go's [+] / [-] on complex128.  These are COMPONENT-WISE (each
    component is a single IEEE float add/sub), so the model is faithful including the
    Inf/NaN corners, and it lowers to the native Go [+] / [-].  *([*] and [/] are DEFERRED:
    Go's complex multiply/divide carry rounding-order subtleties — naive cross-products for
    [*], Smith's scaling algorithm for [/] in the runtime — that a faithful model must match
    exactly; a careful follow-up, not approximated here.)* *)
Definition complex_add (a b : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_add (c_re a) (c_re b)) (f64_add (c_im a) (c_im b)).
Definition complex_sub (a b : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_sub (c_re a) (c_re b)) (f64_sub (c_im a) (c_im b)).

(** Build-checked: each component of the sum/difference is the float add/sub of the
    corresponding components (so the native [a + b] computes exactly what Go does). *)
Example complex_add_components : forall a b,
  go_real (complex_add a b) = f64_add (go_real a) (go_real b)
  /\ go_imag (complex_add a b) = f64_add (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.
Example complex_sub_components : forall a b,
  go_real (complex_sub a b) = f64_sub (go_real a) (go_real b)
  /\ go_imag (complex_sub a b) = f64_sub (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.

(** Complex COMPARISON — Go's [==] / [!=] on complex128.  Two complex values are equal iff
    BOTH components are equal (Go spec "Comparison operators"); float [==] is EXACT, so this
    is faithful including the NaN corner ([NaN != NaN] ⇒ a complex with a NaN component is
    never [==] itself).  Lowers to the native Go [==] / [!=]. *)
Definition complex_eqb (a b : GoComplex128) : bool :=
  andb (f64_eqb (c_re a) (c_re b)) (f64_eqb (c_im a) (c_im b)).
Definition complex_neqb (a b : GoComplex128) : bool := negb (complex_eqb a b).

(** Build-checked: equality is the component-wise float-[==] conjunction (so the native
    [a == b] decides exactly what Go's complex [==] does). *)
Example complex_eqb_components : forall a b,
  complex_eqb a b = andb (f64_eqb (go_real a) (go_real b)) (f64_eqb (go_imag a) (go_imag b)).
Proof. reflexivity. Qed.

(** Complex MULTIPLY — Go's [*] on complex128.  The Go spec underspecifies the rounding of
    complex multiply, and the gc compiler inlines the NAIVE cross-product formula
    [(ac − bd) + (ad + bc)i] (it does NOT implement C99 Annex G's Inf/NaN recovery — only
    DIVISION calls a runtime helper).  This model uses exactly that naive formula, so it
    matches gc bit-for-bit including the Inf/NaN corners (both are naive IEEE), and lowers
    to the native Go [*].  *([/] is still DEFERRED: gc's [runtime.complex128div] uses
    Smith's scaling algorithm — a different computation a faithful model must port exactly.)* *)
Definition complex_mul (a b : GoComplex128) : GoComplex128 :=
  MkComplex128
    (f64_sub (f64_mul (c_re a) (c_re b)) (f64_mul (c_im a) (c_im b)))
    (f64_add (f64_mul (c_re a) (c_im b)) (f64_mul (c_im a) (c_re b))).

(** Build-checked: the real/imag parts are exactly gc's naive cross products. *)
Example complex_mul_components : forall a b,
  go_real (complex_mul a b)
    = f64_sub (f64_mul (go_real a) (go_real b)) (f64_mul (go_imag a) (go_imag b))
  /\ go_imag (complex_mul a b)
    = f64_add (f64_mul (go_real a) (go_imag b)) (f64_mul (go_imag a) (go_real b)).
Proof. intros. split; reflexivity. Qed.

(** Complex unary NEGATION — Go's [-c] on complex128.  Negates BOTH components, each a
    single IEEE float sign-flip [f64_opp], so faithful including signed zero — note
    [-c] (sign-flip) differs from [(0+0i) - c] on a zero component ([opp (+0) = -0] but
    [0 - (+0) = +0]); we use the sign-flip, matching Go's unary [-].  Lowers to native [-c]. *)
Definition complex_neg (c : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_opp (c_re c)) (f64_opp (c_im c)).

Example complex_neg_components : forall c,
  go_real (complex_neg c) = f64_opp (go_real c)
  /\ go_imag (complex_neg c) = f64_opp (go_imag c).
Proof. intros. split; reflexivity. Qed.

(** Complex DIVIDE — Go's [/] on complex128.  Unlike [*] (a naive inline), gc lowers [/]
    to [runtime.complex128div], which uses SMITH'S scaling algorithm (divide through by the
    larger-magnitude denominator component, for numerical stability).  This model is exactly
    that algorithm — operand-for-operand the gc source — and it lowers to the native Go [/].
    (The Annex-G-style Inf/NaN recovery postamble for DEGENERATE divisors is modelled too —
    see the branch comment below.) *)
Definition complex_div (n m : GoComplex128) : GoComplex128 :=
  let nr := c_re n in let ni := c_im n in
  let mr := c_re m in let mi := c_im m in
  (* branch on which denominator component is larger in magnitude — Go uses [|mr| >= |mi|], i.e.
     [|mi| <= |mr|].  We compare ABSOLUTE VALUES via [f64_abs] (= [SpecFloat.SFabs], axiom-free):
     abs never overflows, so the branch matches Go even for huge components (a squared-magnitude
     compare would collapse to [Inf <= Inf] and pick the wrong branch).  Sound even though
     [math.Abs] would need an import: [complex_div] lowers to the NATIVE Go [/] (body PROOF-ONLY,
     suppressed by name), so the [abs] is never extracted.
    The DEGENERATE-divisor postamble (C99 Annex G.5.1 step 3 — zero / Inf / NaN denominators) is
    PORTED operand-for-operand from gc's [runtime.complex128div], so the model matches Go on ALL
    inputs, not just finite ones.  NaN/Inf are detected with [spec_float] primitives ([eqb x x] /
    [|x| = +Inf]); [copysign_inf]/[inf2one] reproduce gc's [math.Copysign] (sign of a zero via
    [1.0 / c = -Inf]).  All proof-only — [complex_div] still lowers to native Go [/], whose
    runtime applies exactly this recovery. *)
  let isnan := fun x => negb (f64_eqb x x) in
  let isinf := fun x => f64_eqb (f64_abs x) (S754_infinity false) in
  let isfin := fun x => negb (orb (isnan x) (isinf x)) in
  (* sign bit set (x < 0, or x = -0 detected via 1.0/-0 = -Inf) *)
  let negs  := fun x => orb (f64_ltb x (0%go64))
                            (f64_eqb (f64_div (1%go64) x) (S754_infinity true)) in
  let copysign_inf := fun c => if negs c then (S754_infinity true) else (S754_infinity false) in (* Copysign(+Inf, c) *)
  let inf2one := fun x => let g := if isinf x then (1%go64) else (0%go64) in
                          if negs x then f64_opp g else g in       (* Copysign(isInf?1:0, x) *)
  let res :=
    if f64_leb (f64_abs mi) (f64_abs mr) then
      let ratio := f64_div mi mr in
      let denom := f64_add mr (f64_mul ratio mi) in
      MkComplex128 (f64_div (f64_add nr (f64_mul ni ratio)) denom)
                   (f64_div (f64_sub ni (f64_mul nr ratio)) denom)
    else
      let ratio := f64_div mr mi in
      let denom := f64_add mi (f64_mul ratio mr) in
      MkComplex128 (f64_div (f64_add (f64_mul nr ratio) ni) denom)
                   (f64_div (f64_sub (f64_mul ni ratio) nr) denom) in
  (* Annex-G recovery: only when BOTH components came out NaN (a degenerate divisor) *)
  if andb (isnan (c_re res)) (isnan (c_im res)) then
    let a := nr in let b := ni in let c := mr in let d := mi in
    if andb (andb (f64_eqb c (0%go64)) (f64_eqb d (0%go64)))
            (orb (negb (isnan a)) (negb (isnan b)))                          (* m == 0, n not all-NaN *)
    then MkComplex128 (f64_mul (copysign_inf c) a) (f64_mul (copysign_inf c) b)
    else if andb (orb (isinf a) (isinf b)) (andb (isfin c) (isfin d))        (* Inf numerator / finite denom *)
    then let a' := inf2one a in let b' := inf2one b in
         MkComplex128 (f64_mul (S754_infinity false) (f64_add (f64_mul a' c) (f64_mul b' d)))
                      (f64_mul (S754_infinity false) (f64_sub (f64_mul b' c) (f64_mul a' d)))
    else if andb (orb (isinf c) (isinf d)) (andb (isfin a) (isfin b))        (* finite numerator / Inf denom *)
    then let c' := inf2one c in let d' := inf2one d in
         MkComplex128 (f64_mul (0%go64) (f64_add (f64_mul a c') (f64_mul b d')))
                      (f64_mul (0%go64) (f64_sub (f64_mul b c') (f64_mul a d')))
    else res
  else res.

(** Witness (machine-checked): on a large divisor where BOTH components square to [+Inf]
    (|mi|, |mr| ≳ 1e154) but |mi| > |mr|, a squared-magnitude branch [mi² <= mr²] wrongly reduces
    to [Inf <= Inf = true] (picks the |mr|-branch), while [|mi| <= |mr|] correctly yields [false]
    (the |mi|-branch) — exactly Go's [|mr| >= |mi|].  ([0x1p550] = 2^550, [0x1p600] = 2^600.) *)
Example complex_div_branch_overflow_fixed :
  let mr := binary_normalize 53 1024 1 550 false in let mi := binary_normalize 53 1024 1 600 false in  (* 2^550, 2^600 *)
     f64_leb (f64_mul mi mi) (f64_mul mr mr) = true    (* squared: WRONG branch *)
  /\ f64_leb (f64_abs mi)    (f64_abs mr)    = false.  (* abs:     RIGHT branch *)
Proof. vm_compute. split; reflexivity. Qed.
(** DEGENERATE divisors recover per Annex G (not the bare-Smith NaN).  Finite
    nonzero / ZERO yields infinities; finite / Inf yields zero — matching gc's runtime.complex128div. *)
Example complex_div_by_zero_is_inf :   (* (1+2i)/(0+0i) = (+Inf, +Inf) *)
  f64_eqb (c_re (complex_div (go_complex (1%go64) (2%go64)) (go_complex (0%go64) (0%go64)))) (S754_infinity false) = true
  /\ f64_eqb (c_im (complex_div (go_complex (1%go64) (2%go64)) (go_complex (0%go64) (0%go64)))) (S754_infinity false) = true.
Proof. vm_compute. split; reflexivity. Qed.
Example complex_div_by_inf_is_zero :   (* (1+1i)/(Inf+Inf i) = (0, 0) *)
  f64_eqb (c_re (complex_div (go_complex (1%go64) (1%go64)) (go_complex (S754_infinity false) (S754_infinity false)))) (0%go64) = true
  /\ f64_eqb (c_im (complex_div (go_complex (1%go64) (1%go64)) (go_complex (S754_infinity false) (S754_infinity false)))) (0%go64) = true.
Proof. vm_compute. split; reflexivity. Qed.
