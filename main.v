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

(** Operator precedence in the printer (step 7b): nested arithmetic prints with
    Go precedence, parenthesising only where needed.  [a*b + c] needs no parens
    ([*] binds tighter than [+]); [(a+b) * c] does (the [+] is looser than the
    surrounding [*]).  Uses the raw [PrimInt63] ops to force infix nesting. *)
Definition prec_demo : IO unit :=
  let a := 2%uint63 in let b := 3%uint63 in let c := 4%uint63 in
  println [ any (PrimInt63.add (PrimInt63.mul a b) c)     (* a*b + c   = 10 *)
          ; any (PrimInt63.mul (PrimInt63.add a b) c) ].  (* (a+b) * c = 20 *)

(** Panic with [n], then recover it and print [n] and [n+1].
    Demonstrates the full panic → catch → type_assert cycle. *)
Definition panic_and_recover (n : int) : IO unit :=
  catch
    (@panic unit (any n))
    (fun v =>
     bind (type_assert TInt64 v) (fun recovered =>
     println [any recovered; any (add recovered 1)])).

Definition map_demo : IO unit :=
  bind (map_make_typed TInt64 TInt64) (fun m =>   (* make(map[int64]int64) *)
  bind (map_set (1:int) (100:int) m) (fun _ =>   (* m[1] = 100 *)
  bind (map_set (2:int) (200:int) m) (fun _ =>   (* m[2] = 200 *)
  bind (map_set (3:int) (300:int) m) (fun _ =>   (* m[3] = 300 *)
  bind (map_set (2:int) (999:int) m) (fun _ =>   (* m[2] = 999  (overwrite) *)
  let sz  := map_len m in
  let hit := @map_get_or int int (2:int) (0:int) m in  (* key present → 999 *)
  let mis := @map_get_or int int (9:int) (0:int) m in  (* key absent  → 0   *)
  bind (type_assert TInt64 (any hit)) (fun hit64 =>
  bind (type_assert TInt64 (any mis)) (fun mis64 =>
  println [any sz; any hit64; any mis64]))))))).  (* prints: 3 999 0 *)

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

(** Matching on [map_get_opt] lowers to Go's comma-ok lookup:
    [match map_get_opt k m with Some v => _ | None => _] becomes
    [if v, ok := m[k]; ok { _ } else { _ }] — no [option] value is built. *)
Definition lookup_demo : IO unit :=
  bind (map_make_typed TInt64 TInt64) (fun m =>
  bind (map_set (7 : int) (700 : int) m) (fun _ =>
  bind (match map_get_opt (7 : int) m with    (* present → 700 true *)
        | Some v => println [any v; any true]
        | None   => println [any false]
        end) (fun _ =>
  match map_get_opt (9 : int) m with           (* absent → false *)
  | Some v => println [any v; any true]
  | None   => println [any false]
  end))).

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
  slice_at_ok TInt64 xs (-1)%sint63 (fun v3 ok3 =>  (* NEGATIVE (signed) → 0 false *)
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
  bind prec_demo                       (fun _ =>   (* prints: 10 20 *)
  bind map_demo                        (fun _ =>   (* prints: 3 999 0 *)
  bind slice_demo                      (fun _ =>   (* prints: 5 3 / false *)
  bind chan_demo                       (fun _ =>   (* prints: 42 true / 0 false *)
  bind goroutine_demo                  (fun _ =>   (* prints: 42 *)
  bind session_demo                    (fun _ =>   (* prints: 42 *)
  bind adder_demo                      (fun _ =>   (* prints: 42 *)
  bind control_flow_demo               (fun _ =>   (* prints: 5 true / 20 false / 1 *)
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
  ret tt)))))))))))))))))))))))))))))))).

Go Main Extraction main "main_effect".
