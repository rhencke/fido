(** Fido entry point. *)

From Fido Require Import preamble.
From Stdlib Require Import Numbers.Cyclic.Int63.Uint63.
From Stdlib Require Import Floats.PrimFloat.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope uint63_scope.
Open Scope float_scope.

Definition add (n m : int) : int := PrimInt63.add n m.

Theorem add_comm : forall n m : int, add n m = add m n.
Proof. intros n m. unfold add. apply Uint63.add_comm. Qed.

Theorem add_assoc : forall n m p : int, add n (add m p) = add (add n m) p.
Proof. intros n m p. unfold add. apply Uint63.add_assoc. Qed.

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

Definition main_effect : IO unit :=
  bind (println [any (add 1 2)])       (fun _ =>   (* prints: 3 *)
  bind (panic_and_recover (add 40 2))  (fun _ =>   (* prints: 42 43 *)
  bind map_demo                        (fun _ =>   (* prints: 3 999 0 *)
  bind slice_demo                      (fun _ =>   (* prints: 5 3 / false *)
  bind chan_demo                       (fun _ =>   (* prints: 42 true / 0 false *)
  bind goroutine_demo                  (fun _ =>   (* prints: 42 *)
  bind session_demo                    (fun _ =>   (* prints: 42 *)
  bind adder_demo                      (fun _ =>   (* prints: 42 *)
  ret tt)))))))).

Go Main Extraction main "main_effect".
