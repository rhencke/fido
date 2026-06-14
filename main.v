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

(** Session-typed ping-pong.
    Protocol (client view): send int → recv int → end.
    The server sees the dual:   recv int → send int → end.
    The Rocq type checker statically enforces that each side
    follows its role — swapping send/recv is a type error. *)

Definition PingPong : Proto := PSend int (PRecv int PEnd).

Definition ping_server (ep : SessEndpoint (dual PingPong)) : IO unit :=
  (* dual PingPong = PRecv int (PSend int PEnd) *)
  sess_recv TInt64 ep (fun n ep' =>
  sess_send ep' (add n n) (fun ep'' =>
  sess_close ep'')).

Definition ping_client (ep : SessEndpoint PingPong) : IO unit :=
  sess_send ep (21 : int) (fun ep' =>
  sess_recv TInt64 ep' (fun result ep'' =>
  bind (sess_close ep'') (fun _ =>
  println [any result]))).     (* prints: 42 *)

Definition session_demo : IO unit :=
  make_sess (fun client_ep server_ep =>
  bind (go_spawn (ping_server server_ep)) (fun _ =>
  ping_client client_ep)).

(** ---- Protocol compliance is enforced at compile time ----

    Each [Fail] below asserts that the enclosed definition does NOT
    type-check.  The build runs these: if any protocol violation ever
    started compiling, [Fail] would error and break the build.  They are
    machine-checked proofs that the session type discipline rejects misuse,
    at zero runtime cost. *)

(* Protocol sends first; receiving first is a type error
   (PSend ≠ PRecv at the head of the protocol). *)
Fail Definition bad_recv_first (ep : SessEndpoint PingPong) : IO unit :=
  sess_recv TInt64 ep (fun _ ep' => sess_close ep').

(* Protocol sends an int; sending a bool is a type error
   (the payload type is pinned to int by the endpoint). *)
Fail Definition bad_send_type (ep : SessEndpoint PingPong) : IO unit :=
  sess_send ep true (fun ep' => sess_close ep').

(* The protocol is not finished; closing now is a type error
   (sess_close demands SessEndpoint PEnd). *)
Fail Definition bad_close_early (ep : SessEndpoint PingPong) : IO unit :=
  sess_close ep.

(* The server's dual receives first; sending first is a type error. *)
Fail Definition bad_server_sends (ep : SessEndpoint (dual PingPong)) : IO unit :=
  sess_send ep (1 : int) (fun ep' => sess_close ep').

(** A longer protocol: the client sends two numbers, the server replies with
    their sum.  Exercises consecutive same-direction steps on one channel —
    two sends in a row (client) and two receives in a row (server) — which
    ping-pong does not cover. *)

Definition Adder : Proto := PSend int (PSend int (PRecv int PEnd)).

Definition adder_server (ep : SessEndpoint (dual Adder)) : IO unit :=
  (* dual Adder = PRecv int (PRecv int (PSend int PEnd)) *)
  sess_recv TInt64 ep  (fun a ep1 =>
  sess_recv TInt64 ep1 (fun b ep2 =>
  sess_send ep2 (add a b) (fun ep3 =>
  sess_close ep3))).

Definition adder_client (ep : SessEndpoint Adder) : IO unit :=
  sess_send ep (20 : int)  (fun ep1 =>
  sess_send ep1 (22 : int) (fun ep2 =>
  sess_recv TInt64 ep2     (fun sum ep3 =>
  bind (sess_close ep3) (fun _ =>
  println [any sum])))).     (* prints: 42 *)

Definition adder_demo : IO unit :=
  make_sess (fun client_ep server_ep =>
  bind (go_spawn (adder_server server_ep)) (fun _ =>
  adder_client client_ep)).

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
  slice_at_ok TInt64 xs (9 : int) (fun v2 ok2 =>    (* out of bounds → 0 false *)
  println [any v2; any ok2]))).

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

(** Bounded loop: [for_each] over a slice lowers to a Go [for ... range]. *)
Definition foreach_demo : IO unit :=
  let xs := slice_of_list TInt64 [10%uint63; 20%uint63; 30%uint63] in
  for_each xs (fun x => println [any x]).   (* prints 10 / 20 / 30 *)

Definition main_effect : IO unit :=
  bind (println [any (add 1 2)])       (fun _ =>   (* prints: 3 *)
  bind (panic_and_recover (add 40 2))  (fun _ =>   (* prints: 42 43 *)
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
  ret tt)))))))))))))).

Go Main Extraction main "main_effect".
