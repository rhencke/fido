(** Fido entry point. *)

From Fido Require Import preamble.
From Stdlib Require Import Numbers.Cyclic.Int63.Uint63.
From Stdlib Require Import Numbers.Cyclic.Int63.Sint63.
From Stdlib Require Import Floats.PrimFloat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope uint63_scope.
Open Scope float_scope.

Definition add (n m : int) : int := PrimInt63.add n m.

Theorem add_comm : forall n m : int, add n m = add m n.
Proof. intros n m. unfold add. apply Uint63.add_comm. Qed.

Theorem add_assoc : forall n m p : int, add n (add m p) = add (add n m) p.
Proof. intros n m p. unfold add. apply Uint63.add_assoc. Qed.

Definition sub (n m : int) : int := PrimInt63.sub n m.

(** Foundational accuracy: [int] is interpreted with SIGNED (Sint63) semantics,
    matching Go's [int64].  In Go, [2 - 5] is [-3]; the signed model agrees.
    (The old unsigned reading would wrongly give [2^63 - 3].)  This lemma is
    machine-checked, so the model provably matches what the extracted Go does. *)
Example sub_signed_matches_go : Sint63.to_Z (sub 2 5) = (-3)%Z.
Proof. now vm_compute. Qed.

(** WHY the plugin REJECTS [Nat.sub] (Coq nat → Go uint): nat subtraction is
    TRUNCATED monus, so [3 - 5 = 0] — lowering it to Go uint's WRAPPING [-]
    ([3 - 5 = 2^64-2]) would be silently wrong.  Machine-checked, so the rejection
    rests on a fact, not a hunch. *)
Example nat_sub_is_truncated : Nat.sub 3 5 = 0%nat.
Proof. reflexivity. Qed.

(** WHY the plugin REJECTS the UNSIGNED [PrimInt63.ltb]/[leb] for [int]: on a
    high-bit value they disagree with Go's SIGNED int64 [<].  Take [-1]
    ([PrimInt63.sub 0 1], i.e. the large [2^63-1] unsigned): unsigned [ltb (-1) 0]
    is [false], but the SIGNED [Sint63.ltb (-1) 0] is [true] — and Go's [-1 < 0]
    on int64 is [true].  So only the signed form (which [Sint63.ltb] reduces to)
    matches Go.  Both machine-checked. *)
Example ltb_unsigned_neg_false : PrimInt63.ltb (PrimInt63.sub 0 1) 0 = false.
Proof. now vm_compute. Qed.
Example ltb_signed_neg_true : Sint63.ltb (PrimInt63.sub 0 1) 0 = true.
Proof. now vm_compute. Qed.

(** OVERFLOW IS PROVABLE — the thing Go cannot do.  Go silently wraps integer
    overflow at runtime and only catches *constant* overflow at compile time.
    Here, "this addition does not overflow" is a Rocq predicate, and when it
    holds the machine result equals the EXACT mathematical sum (no wrap). *)
Definition no_overflow_add (n m : int) : Prop :=
  (Sint63.to_Z Sint63.min_int <= Sint63.to_Z n + Sint63.to_Z m
                                <= Sint63.to_Z Sint63.max_int)%Z.

Theorem add_no_overflow_exact : forall n m : int,
  no_overflow_add n m ->
  Sint63.to_Z (PrimInt63.add n m) = (Sint63.to_Z n + Sint63.to_Z m)%Z.
Proof.
  intros n m H. unfold no_overflow_add in H.
  rewrite Sint63.to_Z_min, Sint63.to_Z_max in H.
  rewrite (Sint63.to_Z_cmodwB (PrimInt63.add n m)).
  rewrite Uint63.add_spec, Sint63.cmod_mod.
  rewrite <- (Sint63.cmod_mod (Uint63.to_Z n + Uint63.to_Z m)).
  replace ((Uint63.to_Z n + Uint63.to_Z m) mod wB)%Z
     with ((Sint63.to_Z n + Sint63.to_Z m) mod wB)%Z by
    (rewrite (Zplus_mod (Sint63.to_Z n) (Sint63.to_Z m));
     rewrite !Sint63.to_Z_mod_Uint63to_Z; reflexivity).
  rewrite Sint63.cmod_mod.
  apply Sint63.cmod_small. lia.
Qed.

(** Concrete instance, machine-checked: 10^12 + 2·10^12 does not overflow and
    is exactly 3·10^12. *)
Example add_exact_demo :
  Sint63.to_Z (PrimInt63.add 1000000000000 2000000000000) = 3000000000000%Z.
Proof. now vm_compute. Qed.

(** Honest about the limit: at the top of the (62-bit) range, addition wraps —
    so [no_overflow_add] fails there and [add_no_overflow_exact] does not apply.
    The model knows exactly where it wraps, which is what makes overflow
    provable: you prove you stay below the boundary. *)
Example add_wraps_at_boundary :
  Sint63.to_Z (PrimInt63.add Sint63.max_int 1) = Sint63.to_Z Sint63.min_int.
Proof. now vm_compute. Qed.

(** SAFE-BY-CONSTRUCTION ARITHMETIC.  Go's [+]/[-]/[*] silently WRAP on overflow;
    overflow-freedom is a *provable* property here (above), but raw [add]/[sub]/
    [mul] don't *force* you to prove it.  [add_nz]/[sub_nz]/[mul_nz] do: each
    DEMANDS a proof that the exact mathematical result is in range, then extracts
    to the raw machine op — which the proof has shown does not wrap, so the result
    equals the exact value (by the [*_no_overflow_exact] theorems).  Raw [add]/
    [sub]/[mul] remain the opt-in WRAPPING forms (like div_nz vs the raw divide).
    The in-range proof is discharged by [now vm_compute] for concrete operands. *)
Definition no_overflow_sub (n m : int) : Prop :=
  (Sint63.to_Z Sint63.min_int <= Sint63.to_Z n - Sint63.to_Z m
                                <= Sint63.to_Z Sint63.max_int)%Z.
Definition no_overflow_mul (n m : int) : Prop :=
  (Sint63.to_Z Sint63.min_int <= Sint63.to_Z n * Sint63.to_Z m
                                <= Sint63.to_Z Sint63.max_int)%Z.

Theorem sub_no_overflow_exact : forall n m : int,
  no_overflow_sub n m ->
  Sint63.to_Z (PrimInt63.sub n m) = (Sint63.to_Z n - Sint63.to_Z m)%Z.
Proof.
  intros n m H. unfold no_overflow_sub in H.
  rewrite Sint63.to_Z_min, Sint63.to_Z_max in H.
  rewrite (Sint63.to_Z_cmodwB (PrimInt63.sub n m)).
  rewrite Uint63.sub_spec, Sint63.cmod_mod.
  rewrite <- (Sint63.cmod_mod (Uint63.to_Z n - Uint63.to_Z m)).
  replace ((Uint63.to_Z n - Uint63.to_Z m) mod wB)%Z
     with ((Sint63.to_Z n - Sint63.to_Z m) mod wB)%Z by
    (rewrite (Zminus_mod (Sint63.to_Z n) (Sint63.to_Z m));
     rewrite !Sint63.to_Z_mod_Uint63to_Z; reflexivity).
  rewrite Sint63.cmod_mod.
  apply Sint63.cmod_small. lia.
Qed.

Theorem mul_no_overflow_exact : forall n m : int,
  no_overflow_mul n m ->
  Sint63.to_Z (PrimInt63.mul n m) = (Sint63.to_Z n * Sint63.to_Z m)%Z.
Proof.
  intros n m H. unfold no_overflow_mul in H.
  rewrite Sint63.to_Z_min, Sint63.to_Z_max in H.
  rewrite (Sint63.to_Z_cmodwB (PrimInt63.mul n m)).
  rewrite Uint63.mul_spec, Sint63.cmod_mod.
  rewrite <- (Sint63.cmod_mod (Uint63.to_Z n * Uint63.to_Z m)).
  replace ((Uint63.to_Z n * Uint63.to_Z m) mod wB)%Z
     with ((Sint63.to_Z n * Sint63.to_Z m) mod wB)%Z by
    (rewrite (Zmult_mod (Sint63.to_Z n) (Sint63.to_Z m));
     rewrite !Sint63.to_Z_mod_Uint63to_Z; reflexivity).
  rewrite Sint63.cmod_mod.
  (* the product is non-linear; abstract it so the bounds are linear for [lia] *)
  apply Sint63.cmod_small.
  set (p := (Sint63.to_Z n * Sint63.to_Z m)%Z) in *. lia.
Qed.

Definition add_nz (n m : int) (_ : no_overflow_add n m) : int := PrimInt63.add n m.
Definition sub_nz (n m : int) (_ : no_overflow_sub n m) : int := PrimInt63.sub n m.
Definition mul_nz (n m : int) (_ : no_overflow_mul n m) : int := PrimInt63.mul n m.

(** Machine-checked: the guarded ops give the exact mathematical result.
    ([now vm_compute] discharges the in-range obligation: [vm_compute] unfolds
    [Z.le] to a comparison, which [now]'s finisher closes — [lia] cannot, as it
    no longer sees arithmetic.) *)
Example add_nz_exact :
  Sint63.to_Z (add_nz 1000000000000 2000000000000 ltac:(now vm_compute))
  = 3000000000000%Z.
Proof. now vm_compute. Qed.
Example mul_nz_exact :
  Sint63.to_Z (mul_nz 1000000 1000000 ltac:(now vm_compute)) = 1000000000000%Z.
Proof. now vm_compute. Qed.

(** Arithmetic you can only call with a proven-in-range result.  Prints
    10^12 + 2·10^12 = 3·10^12 (proven no wrap) and 1000·1000 = 10^6. *)
Definition overflow_safe_demo : IO unit :=
  println [ any (add_nz 1000000000000 2000000000000 ltac:(now vm_compute))
          ; any (mul_nz 1000 1000 ltac:(now vm_compute)) ].
  (* prints: 3000000000000 1000000 *)

(** SAFE-BY-CONSTRUCTION DIVISION (closes the div-by-zero gap).  Go panics on
    [n / 0]; Rocq's division is total ([_ / 0 = 0]).  Emitting a raw [/] would be
    silently unsound, so the plugin emits no bare integer [/]/[%].  Instead
    [div_nz]/[mod_nz] are evidence-carrying: they DEMAND a proof that the divisor
    is non-zero ([(d =? 0) = false], discharged by [eq_refl] for a literal), and
    only then extract to Go's unguarded [n / d] / [n % d] — the proof has already
    ruled out the panic.  Underneath they are [PrimInt63.divs]/[mods], the signed
    primitives that truncate toward zero exactly like Go's int64.  (Raw
    [PrimInt63.divs] remains the escape hatch — Go panics on a zero divisor.) *)
Definition div_nz (n d : int) (_ : (d =? 0)%uint63 = false) : int := PrimInt63.divs n d.
Definition mod_nz (n d : int) (_ : (d =? 0)%uint63 = false) : int := PrimInt63.mods n d.

(** Machine-checked: the guarded division matches Go's truncation toward zero,
    including the signed case Go and Rocq agree on ([-7 / 2 = -3], [-7 % 2 = -1]
    — not the flooring [-4], [1]). *)
Example div_nz_trunc_neg : Sint63.to_Z (div_nz (-7)%sint63 2 eq_refl) = (-3)%Z.
Proof. now vm_compute. Qed.
Example mod_nz_trunc_neg : Sint63.to_Z (mod_nz (-7)%sint63 2 eq_refl) = (-1)%Z.
Proof. now vm_compute. Qed.

(** Division you can only call with a proven-nonzero divisor.  Prints 17/5 = 3
    and 17%5 = 2.  The [eq_refl] discharges [(5 =? 0) = false] at compile time. *)
Definition div_demo : IO unit :=
  println [any (div_nz 17 5 eq_refl); any (mod_nz 17 5 eq_refl)].   (* prints: 3 2 *)

(** float64 is Rocq's primitive [PrimFloat] = IEEE 754 double, the same as Go's
    float64, so arithmetic agrees bit-for-bit.  This exercises the otherwise-
    unused float primitive end-to-end.  (Go's [println] formats float64 in
    scientific notation — that is Go's builtin behaviour, captured by the
    golden.) *)
Definition float_demo : IO unit :=
  println [ any (PrimFloat.add 1.5 2.25)%float     (* 3.75 *)
          ; any (PrimFloat.div 1.0 4.0)%float ].   (* 0.25 (exact in binary) *)

(** Float COMPARISON lowers to Go's [<]/[<=]/[==] on [float64].  Both Coq's
    [PrimFloat] and Go follow IEEE 754, so the semantics match exactly — including
    NaN (every comparison with NaN is false) and signed zero ([0.0 == -0.0]).
    Comparisons bind looser than arithmetic, so [a + b < c] needs no parens. *)
Definition float_cmp_demo : IO unit :=
  bind (println [any (PrimFloat.ltb 1.5 2.5)%float]) (fun _ =>   (* 1.5 < 2.5  → true  *)
  bind (println [any (PrimFloat.leb 2.5 2.5)%float]) (fun _ =>   (* 2.5 <= 2.5 → true  *)
  bind (println [any (PrimFloat.eqb 1.5 1.5)%float]) (fun _ =>   (* 1.5 == 1.5 → true  *)
  println [any (PrimFloat.ltb 3.0 2.0)%float]))).               (* 3.0 < 2.0  → false *)

(** IEEE NaN faithfulness, MACHINE-CHECKED (Coq side): a NaN ([0.0/0.0]) is
    unordered — [NaN == NaN] and [NaN < x] are both [false].  This is exactly Go's
    float64 behaviour, so lowering [eqb]/[ltb] to [==]/[<] is faithful on the
    corner cases, not merely on ordinary values.  ([float_nan_demo] below shows
    Go agreeing at runtime.) *)
Example nan_eqb_false : PrimFloat.eqb (PrimFloat.div 0 0) (PrimFloat.div 0 0) = false.
Proof. now vm_compute. Qed.
Example nan_ltb_false : PrimFloat.ltb (PrimFloat.div 0 0) 1 = false.
Proof. now vm_compute. Qed.

(** Runtime witness (Go side) of the same NaN corner cases.  [z] is an opaque
    [float64] parameter (call site passes [0.0]) so [z/z] is a *runtime* NaN —
    a literal [0.0/0.0] would be a Go *compile-time* division-by-zero error. *)
Definition float_nan_demo (z : float) : IO unit :=
  bind (println [any (PrimFloat.eqb (PrimFloat.div z z) (PrimFloat.div z z))%float]) (fun _ =>
  println [any (PrimFloat.ltb (PrimFloat.div z z) 1)%float]).   (* NaN==NaN → false ; NaN<1 → false *)

(** Float unary negation [PrimFloat.opp] → Go [-x], IEEE-exact (flips the sign
    bit), needing no package import.  Ordinary values: [opp 1.5 = -1.5] and
    [opp (opp 2.0) = 2.0]. *)
Definition float_opp_demo : IO unit :=
  bind (println [any (PrimFloat.opp 1.5)%float]) (fun _ =>               (* -1.5 *)
  println [any (PrimFloat.opp (PrimFloat.opp 2.0))%float]).             (* 2.0 *)

(** The IEEE corner case: [opp] yields NEGATIVE zero, distinct in sign from [+0.0]
    (even though [-0.0 == +0.0]).  Witnessed by [1 / -0 = -inf < 0] (whereas
    [1 / +0 = +inf], not [< 0]).  MACHINE-CHECKED on the Coq side; the runtime
    [float_opp_sign_demo] — with an opaque [z := 0.0], so no untyped-constant
    folding of [-0.0] to [+0.0] — shows Go agrees. *)
Example opp_zero_is_neg :
  PrimFloat.ltb (PrimFloat.div 1 (PrimFloat.opp 0)) 0 = true.
Proof. now vm_compute. Qed.
Definition float_opp_sign_demo (z : float) : IO unit :=
  println [any (PrimFloat.ltb (PrimFloat.div 1 (PrimFloat.opp z)) 0)%float].  (* true *)

(** uint8 (byte): a precise, COMPUTABLE model of Go's 8-bit unsigned arithmetic.
    Each op masks the result back to [0,256), so it wraps mod 256 exactly like Go.
    The wrap is MACHINE-CHECKED (the model is just [land]/[add] on PrimInt63, which
    [vm_compute] reduces) — not asserted.  Note the contrast with [Nat.sub]: uint8
    subtraction genuinely WRAPS ([0 - 1 = 255]), which we model faithfully, whereas
    Coq's [Nat.sub] truncates ([0 - 1 = 0]) and is therefore rejected. *)
Example u8_add_wraps : u8_add (u8_lit 200) (u8_lit 100) = u8_lit 44.
Proof. now vm_compute. Qed.                                   (* 300 mod 256 = 44 *)
Example u8_mul_wraps : u8_mul (u8_lit 255) (u8_lit 255) = u8_lit 1.
Proof. now vm_compute. Qed.                                   (* 65025 mod 256 = 1 *)
Example u8_sub_wraps : u8_sub (u8_lit 0) (u8_lit 1) = u8_lit 255.
Proof. now vm_compute. Qed.                                   (* 0 - 1 wraps to 255 *)
Definition u8_demo : IO unit :=
  bind (println [any (u8_add (u8_lit 200) (u8_lit 100))]) (fun _ =>   (* 44  *)
  bind (println [any (u8_mul (u8_lit 255) (u8_lit 255))]) (fun _ =>   (* 1   *)
  bind (println [any (u8_sub (u8_lit 0)   (u8_lit 1))])   (fun _ =>   (* 255 *)
  println [any (u8_ltb (u8_lit 10) (u8_lit 20))]))).                  (* true *)

(** int8 (signed): the SAME template extended to two's-complement.  [int8(150)] is
    [-106] (150 sign-extended from 8 bits), and the wrap is machine-checked.  The
    sign-extension is the harder case the model must get right. *)
Example i8_add_wraps : i8_add (i8_lit 100) (i8_lit 50) = i8_lit (-106).
Proof. now vm_compute. Qed.                          (* 100+50=150 → -106 *)
Example i8_sub_wraps : i8_sub (i8_lit (-128)) (i8_lit 1) = i8_lit 127.
Proof. now vm_compute. Qed.                          (* -128 - 1 wraps to 127 *)
Definition i8_demo : IO unit :=
  bind (println [any (i8_add (i8_lit 100) (i8_lit 50))])      (fun _ =>   (* -106 *)
  bind (println [any (i8_sub (i8_lit (-128)) (i8_lit 1))])    (fun _ =>   (* 127  *)
  bind (println [any (i8_lit (-100))])                        (fun _ =>   (* -100 *)
  println [any (i8_ltb (i8_lit (-5)) (i8_lit 3))]))).                     (* true *)

(** uint16 / int16: the SAME template at width 16, fully faithful on the carrier
    (16-bit products are [< 2^32], far below [2^62], so [mul] is exact).  The
    plugin recognises every [uN_*]/[iN_*] width with one parser — these needed
    only the Rocq definitions, no new plugin code. *)
Example u16_mul_wraps : u16_mul (u16_lit 1000) (u16_lit 1000) = u16_lit 16960.
Proof. now vm_compute. Qed.                    (* 1000000 mod 65536 = 16960 *)
Example i16_add_wraps : i16_add (i16_lit 30000) (i16_lit 10000) = i16_lit (-25536).
Proof. now vm_compute. Qed.                    (* 40000 wraps to -25536 in int16 *)
Definition u16_demo : IO unit :=
  bind (println [any (u16_add (u16_lit 60000) (u16_lit 10000))]) (fun _ =>   (* 4464 *)
  bind (println [any (u16_mul (u16_lit 1000)  (u16_lit 1000))])  (fun _ =>   (* 16960 *)
  println [any (i16_add (i16_lit 30000) (i16_lit 10000))])).                 (* -25536 *)

(** Operator-precedence PARENS: nested arithmetic parenthesises only where the
    precedence requires it ([a*b + c] no parens; [(a+b) * c] needs them).  gofmt
    handles the spacing (it tightens to [a*b+c]); the printer handles the parens. *)
Definition prec_demo : IO unit :=
  let a := 2%uint63 in let b := 3%uint63 in let c := 4%uint63 in
  println [ any (PrimInt63.add (PrimInt63.mul a b) c)     (* a*b + c   = 10 *)
          ; any (PrimInt63.mul (PrimInt63.add a b) c) ].  (* (a+b) * c = 20 *)

(** Negative integer LITERALS print correctly.  [int] is signed (Sint63) whose
    underlying representation is unsigned, so a naive printer would emit [-7] as
    the unsigned 9223372036854775801 — the plugin must emit the signed decimal. *)
Definition neglit_demo : IO unit :=
  println [any (-7)%sint63; any (-1)%sint63; any (-2147483648)%sint63].
  (* prints: -7 -1 -2147483648 *)

(** Panic with [n], then recover it and print [n] and [n+1].
    Demonstrates the full panic → catch → type_assert cycle. *)
Definition panic_and_recover (n : int) : IO unit :=
  catch
    (@panic unit (any n))
    (fun v =>
     bind (type_assert TInt64 v) (fun recovered =>
     println [any recovered; any (add recovered 1)])).

(** Map reads are now in [IO] (they observe the map's current contents), so [sz]/
    [hit]/[mis] are [bind]-sequenced after the writes — and the old box/assert
    roundtrip is gone ([map_get_or] returns the value directly). *)
Definition map_demo : IO unit :=
  bind (map_make_typed TInt64 TInt64) (fun m =>            (* make(map[int64]int64) *)
  bind (map_set (1:int) (100:int) m) (fun _ =>            (* m[1] = 100 *)
  bind (map_set (2:int) (200:int) m) (fun _ =>            (* m[2] = 200 *)
  bind (map_set (3:int) (300:int) m) (fun _ =>            (* m[3] = 300 *)
  bind (map_set (2:int) (999:int) m) (fun _ =>            (* m[2] = 999  (overwrite) *)
  bind (map_len m) (fun sz =>
  bind (@map_get_or int int (2:int) (0:int) m) (fun hit =>  (* key present → 999 *)
  bind (@map_get_or int int (9:int) (0:int) m) (fun mis =>  (* key absent  → 0   *)
  println [any sz; any hit; any mis])))))))).             (* prints: 3 999 0 *)

Definition slice_demo : IO unit :=
  let xs := slice_of_list TInt64 [1%uint63; 2%uint63; 3%uint63; 4%uint63; 5%uint63] in
  let n  := len xs in
  bind (slice_get TInt64 xs (2:int)) (fun v =>   (* xs[2] = 3, valid *)
  println [any n; any v] >>'                      (* prints: 5 3 *)
  catch
    (bind (@slice_get int TInt64 xs (9:int)) (fun _ =>  (* xs[9] panics — OOB *)
     ret tt))
    (fun _ => println [any false])).              (* caught: prints false *)

(** Buffered channel: send 42, close, then recv_ok twice.
    First recv: value=42, ok=true  (buffered value still present after close).
    Second recv: value=0,  ok=false (channel drained and closed). *)
Definition chan_demo : IO unit :=
  bind (make_chan_buf TInt64 1) (fun ch =>
  bind (send ch (42 : int))    (fun _ =>
  bind (close_chan ch)          (fun _ =>
  recv_ok TInt64 ch             (fun x ok =>
  bind (println [any x; any ok]) (fun _ =>        (* prints: 42 true *)
  recv_ok TInt64 ch              (fun x2 ok2 =>
  println [any x2; any ok2])))))).

(** Unbuffered channel + goroutine: the goroutine sends while main recvs.
    The pattern that required goroutines — unbuffered send deadlocks solo. *)
Definition goroutine_demo : IO unit :=
  bind (make_chan TInt64)              (fun ch =>
  bind (go_spawn (send ch (42 : int))) (fun _ =>
  bind (recv TInt64 ch)               (fun x =>
  println [any x]))).                  (* prints: 42 *)

(** Session-typed ping-pong, with LINEAR sessions (the indexed monad [Sess]).
    Protocol (client view): send int → recv int → end.  The server realises the
    dual: recv int → send int → end.  The protocol state lives in the TYPE
    INDEX, so wrong order/direction/payload AND non-linear misuse (double-send,
    incomplete protocol) are all Rocq compile-time errors — there is no endpoint
    value to reuse. *)

Definition PingPong : Proto := PSend int (PRecv int PEnd).

(* Client and server are inlined into [run_session] so the plugin lowers each
   role's body directly against the shared channel.  Their *types* (below) still
   pin them to [PingPong] / [dual PingPong] ending at [PEnd], so the linearity
   guarantee holds; the [Fail] tests cover the rejections. *)
Definition session_demo : IO unit :=
  run_session
    (* client : Sess PingPong PEnd unit — send 21, recv, print *)
    (sbind (ssend (21 : int)) (fun _ =>
     sbind (srecv TInt64) (fun result =>
     slift (println [any result]))))          (* prints: 42 *)
    (* server : Sess (dual PingPong) PEnd unit — recv n, send n+n *)
    (sbind (srecv TInt64) (fun n =>
     ssend (add n n))).

(** ---- Protocol compliance is enforced at compile time ----

    Each [Fail] below asserts that the enclosed definition does NOT type-check.
    The build runs these: if any violation ever started compiling, [Fail] would
    error and break the build.  They are machine-checked proofs that the session
    discipline rejects misuse, at zero runtime cost. *)

(* Receiving first violates the protocol head (PSend ≠ PRecv) — type error. *)
Fail Definition bad_recv_first : Sess PingPong PEnd unit :=
  sbind (srecv TInt64) (fun _ => sret tt).

(* Sending a bool where the protocol pins int — type error. *)
Fail Definition bad_send_type : Sess PingPong PEnd unit :=
  sbind (ssend true) (fun _ => sret tt).

(* Stopping before [PEnd]: the ascribed type demands the protocol be fully
   consumed, so an incomplete session is a type error. *)
Fail Definition bad_incomplete : Sess PingPong PEnd unit :=
  ssend (21 : int).

(* NON-LINEAR double send — the violation the old CPS API silently ACCEPTED.
   After one [ssend] the state is [PRecv int PEnd]; a second [ssend] needs
   [PSend] at the head, so it no longer type-checks. *)
Fail Definition bad_double_send : Sess PingPong PEnd unit :=
  sbind (ssend (21 : int)) (fun _ =>
  sbind (ssend (99 : int)) (fun _ => sret tt)).

(* The server's dual receives first; sending first is a type error. *)
Fail Definition bad_server_sends : Sess (dual PingPong) PEnd unit :=
  sbind (ssend (1 : int)) (fun _ => sret tt).

(** A longer protocol: the client sends two numbers, the server replies with
    their sum.  Exercises consecutive same-direction steps — two sends in a row
    (client), two receives in a row (server) — which ping-pong does not. *)

Definition Adder : Proto := PSend int (PSend int (PRecv int PEnd)).

Definition adder_demo : IO unit :=
  run_session
    (* client : Sess Adder PEnd unit — send 20, send 22, recv sum, print *)
    (sbind (ssend (20 : int)) (fun _ =>
     sbind (ssend (22 : int)) (fun _ =>
     sbind (srecv TInt64) (fun sum =>
     slift (println [any sum])))))            (* prints: 42 *)
    (* server : Sess (dual Adder) PEnd unit — recv a, recv b, send a+b *)
    (sbind (srecv TInt64) (fun a =>
     sbind (srecv TInt64) (fun b =>
     ssend (add a b)))).

(** ---- Control flow: if/else (step 7a) ----

    [if c then _ else _] is Rocq sugar for [match c with true | false]; the
    plugin lowers it to a Go [if]/[else] statement.  Two positions:

    [sign_demo] uses the branch in tail position (each arm is a statement).
    [pick_demo] uses it as an IO value feeding a continuation — the plugin
    threads the continuation into both arms (bind distributes over case). *)

Definition sign_demo (n : int) : IO unit :=
  if Sint63.ltb n 10                  (* SIGNED comparison, faithful to Go int64 *)
  then println [any n; any true]      (* n < 10  → e.g. "5 true"   *)
  else println [any n; any false].    (* n >= 10 → e.g. "20 false" *)

Definition pick_demo (b : bool) : IO unit :=
  bind (if b then ret (1 : int) else ret (2 : int)) (fun x =>
  println [any x]).                    (* b → 1, else 2 *)

(** Signed subtraction extracts to Go's [2 - 5] and prints [-3] — the runtime
    counterpart of [sub_signed_matches_go]. *)
Definition neg_demo : IO unit :=
  println [any (sub (2 : int) (5 : int))].   (* Go prints: -3 *)

Definition control_flow_demo : IO unit :=
  bind (sign_demo (5 : int))  (fun _ =>   (* prints: 5 true  *)
  bind (sign_demo (20 : int)) (fun _ =>   (* prints: 20 false *)
  bind (pick_demo true)       (fun _ =>   (* prints: 1 *)
  neg_demo))).                            (* prints: -3 *)

(** Boolean operators [andb]/[orb]/[negb] lower to Go's [&&]/[||]/[!].  The
    operands are pure, total [bool] values, so Go's short-circuit evaluation is
    observationally identical (no effects, no divergence to skip).  Parameters
    are opaque [bool]s (typed [bool] in Go), so the operators survive extraction
    rather than constant-folding, and precedence is exercised: the last line is
    [(a || b) && c], so the looser [||] is parenthesised inside [&&]. *)
Definition bool_op_demo (a b c : bool) : IO unit :=
  bind (println [any (andb a b)]) (fun _ =>          (* a && b *)
  bind (println [any (orb  a b)]) (fun _ =>          (* a || b *)
  bind (println [any (negb b)])   (fun _ =>          (* !b *)
  println [any (andb (orb a b) c)]))).               (* (a || b) && c *)

(** The primary use of the boolean operators: COMPOUND CONDITIONS in [if].  Each
    [if] is a match on [bool] whose scrutinee is a compound expression, so the
    condition lowers to Go's [a && b] / [a || b] / [!a] directly inside the
    [if (...)].  One conditional per function (mirroring [sign_demo]) so the
    [bind] continuation follows the call as a single statement — chaining several
    inline [if]s in one [bind] instead would duplicate the continuation into both
    arms (see the "inline-if continuation duplication" note in CLAUDE.md). *)
Definition and_cond (a b : int) : IO unit :=
  if andb (Sint63.ltb a 10) (Sint63.ltb b 10)         (* a<10 && b<10 *)
  then println [any (1 : int)] else println [any (0 : int)].
Definition or_cond (a b : int) : IO unit :=
  if orb (Sint63.ltb a 10) (Sint63.ltb b 10)          (* a<10 || b<10 *)
  then println [any (1 : int)] else println [any (0 : int)].
Definition not_cond (a : int) : IO unit :=
  if negb (Sint63.ltb a 10)                           (* !(a<10) *)
  then println [any (1 : int)] else println [any (0 : int)].
Definition cond_op_demo : IO unit :=
  bind (and_cond 3 4)  (fun _ =>   (* T && T → 1 *)
  bind (or_cond 30 4)  (fun _ =>   (* F || T → 1 *)
  not_cond 30)).                   (* !F      → 1 *)

(** Regression for inline-[if] continuation de-duplication: three INLINE [if]s
    chained in one [bind], each discarding its [unit] result.  Because the result
    is discarded, the continuation is emitted ONCE after each [if] (both arms fall
    through) instead of being duplicated into both arms — so this lowers to three
    flat sequential [if/else]s, not a 2^2-copy tree.  Prints 1 / 0 / 1. *)
Definition inline_if_demo : IO unit :=
  bind (if Sint63.ltb 3 10  then println [any (1:int)] else println [any (0:int)]) (fun _ =>
  bind (if Sint63.ltb 30 10 then println [any (1:int)] else println [any (0:int)]) (fun _ =>
  if Sint63.ltb 5 10        then println [any (1:int)] else println [any (0:int)])).

(** [map_get_opt] is an IO read; binding it then matching the [option] lowers to
    Go's comma-ok lookup: [bind (map_get_opt k m) (fun o => match o with Some v =>
    _ | None => _)] becomes [if v, ok := m[k]; ok { _ } else { _ }] — no [option]
    value is built. *)
Definition lookup_demo : IO unit :=
  bind (map_make_typed TInt64 TInt64) (fun m =>
  bind (map_set (7 : int) (700 : int) m) (fun _ =>
  bind (bind (map_get_opt (7 : int) m) (fun o =>   (* present → 700 true *)
        match o with
        | Some v => println [any v; any true]
        | None   => println [any false]
        end)) (fun _ =>
  bind (map_get_opt (9 : int) m) (fun o =>          (* absent → false *)
  match o with
  | Some v => println [any v; any true]
  | None   => println [any false]
  end)))).

(** List/slice match: [match xs with [] | x :: rest] lowers to
    [if len(xs) == 0 { … } else { x := xs[0]; rest := xs[1:]; … }].
    The [cons] arm binds two variables (head and tail) — a two-binder case the
    earlier matches did not exercise. *)
Definition list_demo : IO unit :=
  let xs := slice_of_list TInt64 [10%uint63; 20%uint63; 30%uint63] in
  match xs with
  | nil         => println [any false]
  | cons x rest => println [any x; any (len rest)]   (* head=10, len tail=2 *)
  end.

(** Safe slice access: [slice_at_ok] bounds-checks and forces handling the
    out-of-bounds case, so it cannot panic — the safe-by-construction default,
    versus the [slice_get] escape hatch used in [slice_demo] above. *)
Definition slice_safe_demo : IO unit :=
  let xs := slice_of_list TInt64 [10%uint63; 20%uint63; 30%uint63] in
  slice_at_ok TInt64 xs (1 : int) (fun v ok =>      (* in bounds → 20 true *)
  bind (println [any v; any ok]) (fun _ =>
  slice_at_ok TInt64 xs (9 : int) (fun v2 ok2 =>    (* above range → 0 false *)
  bind (println [any v2; any ok2]) (fun _ =>
  (* runtime-NEGATIVE index (sub 0 1 = -1) — a *constant* negative index is a Go
     compile error, so use a computed one; the lower-bound check must reject it. *)
  slice_at_ok TInt64 xs (sub 0 1) (fun v3 ok3 =>    (* negative (signed) → 0 false *)
  println [any v3; any ok3]))))).

(** Safe type assertion: [type_assert_safe] is Go's [v, ok := x.(T)] — no panic
    on a type mismatch, the caller handles [ok = false].  Safe-by-construction
    default versus the [type_assert] escape hatch.  We assert on a recovered
    panic value [r : GoAny] (a genuine [any], like [panic_and_recover]). *)
Definition assert_safe_demo (n : int) : IO unit :=
  catch (@panic unit (any n))
    (fun r =>
     type_assert_safe TInt64 r (fun v ok =>        (* r holds int64 → n true *)
     bind (println [any v; any ok]) (fun _ =>
     type_assert_safe TBool r (fun b ok2 =>        (* r is not a bool → false false *)
     println [any b; any ok2])))).

(** Capture in a goto loop: each iteration defers [println iv].  The loop-temp
    [iv] is captured BY VALUE per iteration, so the deferred calls (LIFO at
    return) print 2, 1, 0 — not 2, 2, 2 (which a shared cell would give). *)
Definition defer_loop_demo : IO unit :=
  bind (ref_new (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>
      if Sint63.ltb iv 3 then
        bind (defer_call (println [any iv]))  (fun _ =>
        bind (ref_set i (add iv 1))           (fun _ =>
        ret (Jump 0%nat)))
      else ret (Jump 1%nat)) ;
    ret Done
  ]).

(** Function-scoped defer: [defer_call] runs at function return, LIFO across all
    defers — distinct from block-scoped [with_defer].  Prints 3, then 2, then 1. *)
Definition defer_demo : IO unit :=
  bind (defer_call (println [any (1 : int)])) (fun _ =>   (* runs 3rd (LIFO) *)
  bind (defer_call (println [any (2 : int)])) (fun _ =>   (* runs 2nd *)
  println [any (3 : int)])).                               (* runs now *)

(** Mutable local variable: declare, read, reassign, read again — straight-line
    (no control flow, so trivially scope-correct). *)
Definition mut_demo : IO unit :=
  bind (ref_new (10 : int))        (fun r =>  (* r := 10        *)
  bind (ref_get TInt64 r)          (fun a =>  (* a := r  (= 10) *)
  bind (ref_set r (add a 5))       (fun _ =>  (* r = a + 5 (= 15) *)
  bind (ref_get TInt64 r)          (fun b =>  (* b := r  (= 15) *)
  println [any b])))).                         (* prints 15 *)

(** Backward-goto counting loop: a [Ref] counter + [goto] back to the header.
    The read [iv := ref_get i] cannot use [:=] (it re-runs each iteration), so
    its declaration is hoisted to [var iv int64] (dominating the loop) and
    assigned with [=].  [ref_set] also assigns with [=].  Prints 0,1,2. *)
Definition count_demo : IO unit :=
  bind (ref_new (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>            (* block 0: loop header *)
      if Sint63.ltb iv 3 then
        bind (println [any iv])      (fun _ =>
        bind (ref_set i (add iv 1))  (fun _ =>
        ret (Jump 0%nat)))                        (* goto block0 (backward) *)
      else ret (Jump 1%nat)) ;                    (* exit *)
    ret Done                                       (* block 1 *)
  ]).

(** Control flow as a goto-CFG.  Three blocks; block 0 conditionally jumps to
    the merge (block 2), skipping block 1.  The structurer lifts this to a clean
    one-armed [if !early { println(2) }] — block 1 runs only when not early.
    early ⇒ 1,3 ; else ⇒ 1,2,3. *)
Definition cond_goto_demo (early : bool) : IO unit :=
  run_blocks 0%nat [
    bind (println [any (1 : int)]) (fun _ =>
      if early then ret (Jump 2%nat) else ret (Jump 1%nat)) ;
    bind (println [any (2 : int)]) (fun _ => ret (Jump 2%nat)) ;
    bind (println [any (3 : int)]) (fun _ => ret Done)
  ].

(** Diamond: block 0 branches to two non-empty arms (blocks 1 and 2) that
    reconverge at the merge (block 3).  The structurer finds the merge (the
    immediate post-dominator) and lifts this to [if b { 10 } else { 20 }; 99],
    emitting the merge once.  b ⇒ 1,10,99 ; else ⇒ 1,20,99. *)
Definition diamond_demo (b : bool) : IO unit :=
  run_blocks 0%nat [
    bind (println [any (1 : int)]) (fun _ =>
      if b then ret (Jump 1%nat) else ret (Jump 2%nat)) ;
    bind (println [any (10 : int)]) (fun _ => ret (Jump 3%nat)) ;
    bind (println [any (20 : int)]) (fun _ => ret (Jump 3%nat)) ;
    bind (println [any (99 : int)]) (fun _ => ret Done)
  ].

(** Loop containing a branch: a counting loop (block 0 header, block 3 the
    increment/loop tail) whose body has an in-loop one-armed [if] (block 1 → 2).
    Exercises the relooper nesting a conditional inside a [for]: the header
    becomes [for { … if iv < 3 { … } else { break } }], and block 1's branch a
    nested [if … < 1 { println(100) }].  Counter is a [Ref], re-read per block
    (separate goto-blocks don't share Rocq scope).  Prints 100, 0, 1, 2. *)
Definition loopif_demo : IO unit :=
  bind (ref_new (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: header *)
      if Sint63.ltb iv 3 then ret (Jump 1%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 1: in-loop branch *)
      if Sint63.ltb iv 1 then ret (Jump 2%nat) else ret (Jump 3%nat)) ;
    bind (println [any (100 : int)]) (fun _ => ret (Jump 3%nat)) ;  (* block 2: first-iter marker *)
    bind (ref_get TInt64 i) (fun iv =>                              (* block 3: body, incr, loop *)
    bind (println [any iv]) (fun _ =>
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat)))) ;
    ret Done                                                        (* block 4: exit *)
  ]).

(** Nested loops: an outer counter [i] (header block 0, tail block 4) wrapping an
    inner counter [j] (header block 2, tail block 3).  Exercises the relooper
    nesting one [for] inside another — [loopctx] stacks, so the inner [jv >= 2]
    exit becomes the inner [break] (to block 4) and the outer [iv >= 2] exit the
    outer [break] (to block 5).  Two [Ref]s; [j] is reset each outer pass.
    Prints 0,1 (inner, i=0) then 0,1 (inner, i=1). *)
Definition nested_loop_demo : IO unit :=
  bind (ref_new (0 : int)) (fun i =>
  bind (ref_new (0 : int)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header *)
      if Sint63.ltb iv 2 then ret (Jump 1%nat) else ret (Jump 5%nat)) ;
    bind (ref_set j (0 : int)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if Sint63.ltb jv 2 then ret (Jump 3%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: inner body *)
    bind (println [any jv]) (fun _ =>
    bind (ref_set j (add jv 1)) (fun _ => ret (Jump 2%nat)))) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 4: outer tail *)
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat))) ;
    ret Done                                                        (* block 5: exit *)
  ])).

(** Early return from inside a loop: block 1 returns ([Done]) when [iv] reaches 2,
    mid-loop — distinct from the loop's normal [break] (block 0 → block 3) and the
    post-loop code.  The relooper emits [return] for the in-loop [Done], [break]
    for the exit edge, and the block-3 tail after the [for].  Prints 0, 1, then
    returns (so block 3's 999 is never reached). *)
Definition early_return_demo : IO unit :=
  bind (ref_new (0 : int)) (fun i =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: header *)
      if Sint63.ltb iv 9 then ret (Jump 1%nat) else ret (Jump 3%nat)) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 1: early return *)
      if Sint63.ltb iv 2 then ret (Jump 2%nat) else ret Done) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 2: body, incr, loop *)
    bind (println [any iv]) (fun _ =>
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat)))) ;
    bind (println [any (999 : int)]) (fun _ => ret Done)           (* block 3: normal exit *)
  ]).

(** Labeled break: from inside the inner loop, block 3 jumps to the *outer*
    loop's exit (block 6) when [jv] reaches 2 — escaping both loops at once.
    That is more than the innermost loop can [break], so the relooper labels the
    outer [for] [L0:] and emits [break L0].  The inner loop is multi-exit (its
    normal exit is block 5, plus the labeled escape to block 6), which the
    primary-exit analysis accepts.  Prints 0, 1, 2 then stops entirely. *)
Definition labeled_break_demo : IO unit :=
  bind (ref_new (0 : int)) (fun i =>
  bind (ref_new (0 : int)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header *)
      if Sint63.ltb iv 3 then ret (Jump 1%nat) else ret (Jump 6%nat)) ;
    bind (ref_set j (0 : int)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if Sint63.ltb jv 3 then ret (Jump 3%nat) else ret (Jump 5%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: print; break L0 at 2 *)
    bind (println [any jv]) (fun _ =>
      if Sint63.ltb jv 2 then ret (Jump 4%nat) else ret (Jump 6%nat))) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 4: inner tail, j++ *)
    bind (ref_set j (add jv 1)) (fun _ => ret (Jump 2%nat))) ;
    bind (ref_get TInt64 i) (fun iv =>                              (* block 5: outer tail, i++ *)
    bind (ref_set i (add iv 1)) (fun _ => ret (Jump 0%nat))) ;
    ret Done                                                        (* block 6: exit *)
  ])).

(** Labeled continue: from inside the inner loop, block 3 jumps to the *outer*
    header (block 0) once [jv] reaches 1 — abandoning the inner loop to restart
    the outer one.  That escapes the innermost loop, so it lowers to
    [continue L0] (the outer [for] is labeled).  The outer header increments [i]
    so it still terminates.  Prints 0, 1 (inner, i=0) then 0, 1 (i=1). *)
Definition labeled_continue_demo : IO unit :=
  bind (ref_new (0 : int)) (fun i =>
  bind (ref_new (0 : int)) (fun j =>
  run_blocks 0%nat [
    bind (ref_get TInt64 i) (fun iv =>                              (* block 0: outer header, i++ *)
    bind (ref_set i (add iv 1)) (fun _ =>
      if Sint63.ltb iv 2 then ret (Jump 1%nat) else ret (Jump 5%nat))) ;
    bind (ref_set j (0 : int)) (fun _ => ret (Jump 2%nat)) ;        (* block 1: reset j *)
    bind (ref_get TInt64 j) (fun jv =>                              (* block 2: inner header *)
      if Sint63.ltb jv 3 then ret (Jump 3%nat) else ret (Jump 4%nat)) ;
    bind (ref_get TInt64 j) (fun jv =>                              (* block 3: print; continue L0 *)
    bind (println [any jv]) (fun _ =>
    bind (ref_set j (add jv 1)) (fun _ =>
      if Sint63.ltb jv 1 then ret (Jump 2%nat) else ret (Jump 0%nat)))) ;
    ret (Jump 0%nat) ;                                              (* block 4: inner exit → outer *)
    ret Done                                                        (* block 5: exit *)
  ])).

(** Irreducible CFG (a two-entry loop): block 0 jumps into the {1,2} cycle at
    *either* block 1 or block 2, so neither dominates the other and there is no
    back-edge to make a loop header.  No structured [for] can express this, so it
    takes the raw labels+goto fallback — the completeness guarantee that *any*
    control flow lowers, structured or not.  enter_high ⇒ 2,1,2,1,2 ; else ⇒
    1,2,1,2. *)
Definition irreducible_demo (enter_high : bool) : IO unit :=
  bind (ref_new (0 : int)) (fun n =>
  run_blocks 0%nat [
    (if enter_high then ret (Jump 2%nat) else ret (Jump 1%nat)) ;  (* block 0: two-entry *)
    bind (ref_get TInt64 n) (fun nv =>                             (* block 1 *)
    bind (println [any (1 : int)]) (fun _ =>
    bind (ref_set n (add nv 1)) (fun _ => ret (Jump 2%nat)))) ;
    bind (ref_get TInt64 n) (fun nv =>                             (* block 2 *)
    bind (println [any (2 : int)]) (fun _ =>
    bind (ref_set n (add nv 1)) (fun _ =>
      if Sint63.ltb nv 3 then ret (Jump 1%nat) else ret (Jump 3%nat)))) ;
    ret Done                                                       (* block 3: exit *)
  ]).

(** Bounded loop: [for_each] over a slice lowers to a Go [for ... range]. *)
Definition foreach_demo : IO unit :=
  let xs := slice_of_list TInt64 [10%uint63; 20%uint63; 30%uint63] in
  for_each xs (fun x => println [any x]).   (* prints 10 / 20 / 30 *)

(** Fold: sum a slice into an accumulator — lowers to an accumulator [for]
    loop ([total := 0; for _, x := range xs { total = total + x }]). *)
Definition sum_demo : IO unit :=
  let xs    := slice_of_list TInt64 [1%uint63; 2%uint63; 3%uint63; 4%uint63] in
  let total := slice_fold xs (0 : int) (fun acc x => add acc x) in
  println [any total].   (* 1+2+3+4 = 10 *)

Definition main_effect : IO unit :=
  bind (println [any (add 1 2)])       (fun _ =>   (* prints: 3 *)
  bind (panic_and_recover (add 40 2))  (fun _ =>   (* prints: 42 43 *)
  bind div_demo                        (fun _ =>   (* prints: 3 2 *)
  bind overflow_safe_demo              (fun _ =>   (* prints: 3000000000000 1000000 *)
  bind float_demo                      (fun _ =>   (* prints: 3.75 / 0.25 (sci) *)
  bind float_cmp_demo                  (fun _ =>   (* prints: true / true / true / false *)
  bind (float_nan_demo 0)              (fun _ =>   (* prints: false / false (NaN unordered) *)
  bind float_opp_demo                  (fun _ =>   (* prints: -1.5 / 2.0 *)
  bind (float_opp_sign_demo 0)         (fun _ =>   (* prints: true (opp made -0 at runtime) *)
  bind u8_demo                         (fun _ =>   (* prints: 44 / 1 / 255 / true *)
  bind i8_demo                         (fun _ =>   (* prints: -106 / 127 / -100 / true *)
  bind u16_demo                        (fun _ =>   (* prints: 4464 / 16960 / -25536 *)
  bind prec_demo                       (fun _ =>   (* prints: 10 20 *)
  bind neglit_demo                     (fun _ =>   (* prints: -7 -1 -2147483648 *)
  bind map_demo                        (fun _ =>   (* prints: 3 999 0 *)
  bind slice_demo                      (fun _ =>   (* prints: 5 3 / false *)
  bind chan_demo                       (fun _ =>   (* prints: 42 true / 0 false *)
  bind goroutine_demo                  (fun _ =>   (* prints: 42 *)
  bind session_demo                    (fun _ =>   (* prints: 42 *)
  bind adder_demo                      (fun _ =>   (* prints: 42 *)
  bind control_flow_demo               (fun _ =>   (* prints: 5 true / 20 false / 1 *)
  bind (bool_op_demo true false true)  (fun _ =>   (* prints: false / true / true / true *)
  bind cond_op_demo                    (fun _ =>   (* prints: 1 / 1 / 1 *)
  bind inline_if_demo                  (fun _ =>   (* prints: 1 / 0 / 1 *)
  bind lookup_demo                     (fun _ =>   (* prints: 700 true / false *)
  bind list_demo                       (fun _ =>   (* prints: 10 2 *)
  bind slice_safe_demo                 (fun _ =>   (* prints: 20 true / 0 false *)
  bind (assert_safe_demo (7 : int))    (fun _ =>   (* prints: 7 true / false false *)
  bind foreach_demo                    (fun _ =>   (* prints: 10 / 20 / 30 *)
  bind sum_demo                        (fun _ =>   (* prints: 10 *)
  bind (cond_goto_demo true)           (fun _ =>   (* prints: 1 / 3 *)
  bind (cond_goto_demo false)          (fun _ =>   (* prints: 1 / 2 / 3 *)
  bind (diamond_demo true)             (fun _ =>   (* prints: 1 / 10 / 99 *)
  bind (diamond_demo false)            (fun _ =>   (* prints: 1 / 20 / 99 *)
  bind loopif_demo                     (fun _ =>   (* prints: 100 / 0 / 1 / 2 *)
  bind nested_loop_demo                (fun _ =>   (* prints: 0 / 1 / 0 / 1 *)
  bind early_return_demo               (fun _ =>   (* prints: 0 / 1 *)
  bind labeled_break_demo              (fun _ =>   (* prints: 0 / 1 / 2 *)
  bind labeled_continue_demo           (fun _ =>   (* prints: 0 / 1 / 0 / 1 *)
  bind (irreducible_demo false)        (fun _ =>   (* prints: 1 / 2 / 1 / 2 *)
  bind (irreducible_demo true)         (fun _ =>   (* prints: 2 / 1 / 2 / 1 / 2 *)
  bind mut_demo                        (fun _ =>   (* prints: 15 *)
  bind count_demo                      (fun _ =>   (* prints: 0 / 1 / 2 *)
  bind defer_demo                      (fun _ =>   (* prints: 3 / 2 / 1 *)
  bind defer_loop_demo                 (fun _ =>   (* prints: 2 / 1 / 0 *)
  ret tt))))))))))))))))))))))))))))))))))))))))))))).

Go Main Extraction main "main_effect".
