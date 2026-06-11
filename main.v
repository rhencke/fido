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

Definition main_effect : IO unit :=
  bind (println [any (add 1 2)])       (fun _ =>   (* prints: 3 *)
  bind (panic_and_recover (add 40 2))  (fun _ =>   (* prints: 42 43 *)
  bind map_demo                        (fun _ =>   (* prints: 3 999 0 *)
  bind slice_demo                      (fun _ =>   (* prints: 5 3 / false *)
  ret tt)))).

Go Main Extraction main "main_effect".
