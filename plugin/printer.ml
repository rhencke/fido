
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

module Nat =
 struct
  (** val sub : nat -> nat -> nat **)

  let rec sub n0 m =
    match n0 with
    | O -> n0
    | S k -> (match m with
              | O -> n0
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n0 m =
    leb (S n0) m

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
 end

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> False
| Cons (a, l0) -> (match f a with
                   | True -> True
                   | False -> existsb f l0)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val zero : ascii **)

let zero =
  Ascii (False, False, False, False, False, False, False, False)

(** val one : ascii **)

let one =
  Ascii (True, False, False, False, False, False, False, False)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
| Ascii (a1, a2, a3, a4, a5, a6, a7, _) ->
  Ascii (c, a1, a2, a3, a4, a5, a6, a7)

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | O -> zero
    | S n' ->
      (match p with
       | XI p' -> shift True (loop n' p')
       | XO p' -> shift False (loop n' p')
       | XH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> ascii **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> ascii **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| Nil -> N0
| Cons (b, l') ->
  N.add (match b with
         | True -> Npos XH
         | False -> N0)
    (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : ascii -> n **)

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (Cons (a0, (Cons (a1, (Cons (a2, (Cons (a3, (Cons (a4, (Cons
    (a5, (Cons (a6, (Cons (a7, Nil))))))))))))))))

(** val nat_of_ascii : ascii -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> False)

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Pos.of_succ_nat n1)

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0
 end

(** val is_idc : ascii -> bool **)

let is_idc c =
  let n0 = nat_of_ascii c in
  (match match match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))))))))))))))))))) n0 with
               | True ->
                 Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S
                   O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               | False -> False with
         | True -> True
         | False ->
           (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    n0 with
            | True ->
              Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S
                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            | False -> False) with
   | True -> True
   | False ->
     (match match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S
                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    n0 with
            | True ->
              Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S
                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            | False -> False with
      | True -> True
      | False ->
        Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_idstart : ascii -> bool **)

let is_idstart c =
  let n0 = nat_of_ascii c in
  (match match match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       n0 with
               | True ->
                 Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               | False -> False with
         | True -> True
         | False ->
           (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S
                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    n0 with
            | True ->
              Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S
                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            | False -> False) with
   | True -> True
   | False ->
     Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val all_idc : string -> bool **)

let rec all_idc = function
| EmptyString -> True
| String (c, s') -> (match is_idc c with
                     | True -> all_idc s'
                     | False -> False)

(** val is_type_keyword : string -> bool **)

let is_type_keyword s =
  existsb (eqb1 s) (Cons ((String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, True, True, True, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), (String ((Ascii (False, True, True, False, True,
    True, False, False)), (String ((Ascii (False, False, True, False, True,
    True, False, False)), EmptyString)))))))))), (Cons ((String ((Ascii
    (True, False, False, True, False, True, True, False)), (String ((Ascii
    (False, True, True, True, False, True, True, False)), (String ((Ascii
    (False, False, True, False, True, True, True, False)), (String ((Ascii
    (True, True, False, False, True, True, False, False)), (String ((Ascii
    (False, True, False, False, True, True, False, False)),
    EmptyString)))))))))), (Cons ((String ((Ascii (True, False, False, True,
    False, True, True, False)), (String ((Ascii (False, True, True, True,
    False, True, True, False)), (String ((Ascii (False, False, True, False,
    True, True, True, False)), (String ((Ascii (True, False, False, False,
    True, True, False, False)), (String ((Ascii (False, True, True, False,
    True, True, False, False)), EmptyString)))))))))), (Cons ((String ((Ascii
    (True, False, False, True, False, True, True, False)), (String ((Ascii
    (False, True, True, True, False, True, True, False)), (String ((Ascii
    (False, False, True, False, True, True, True, False)), (String ((Ascii
    (False, False, False, True, True, True, False, False)),
    EmptyString)))))))), (Cons ((String ((Ascii (True, False, False, True,
    False, True, True, False)), (String ((Ascii (False, True, True, True,
    False, True, True, False)), (String ((Ascii (False, False, True, False,
    True, True, True, False)), EmptyString)))))), (Cons ((String ((Ascii
    (True, False, True, False, True, True, True, False)), (String ((Ascii
    (True, False, False, True, False, True, True, False)), (String ((Ascii
    (False, True, True, True, False, True, True, False)), (String ((Ascii
    (False, False, True, False, True, True, True, False)), (String ((Ascii
    (False, True, True, False, True, True, False, False)), (String ((Ascii
    (False, False, True, False, True, True, False, False)),
    EmptyString)))))))))))), (Cons ((String ((Ascii (True, False, True,
    False, True, True, True, False)), (String ((Ascii (True, False, False,
    True, False, True, True, False)), (String ((Ascii (False, True, True,
    True, False, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), (String ((Ascii (True, True, False,
    False, True, True, False, False)), (String ((Ascii (False, True, False,
    False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    EmptyString)))))))))))), (Cons ((String ((Ascii (True, False, True,
    False, True, True, True, False)), (String ((Ascii (True, False, False,
    True, False, True, True, False)), (String ((Ascii (False, True, True,
    True, False, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), (String ((Ascii (False, False, False,
    True, True, True, False, False)), EmptyString)))))))))), (Cons ((String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, False, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString)))))))), (Cons ((String ((Ascii (False, True, False, False,
    False, True, True, False)), (String ((Ascii (True, True, True, True,
    False, True, True, False)), (String ((Ascii (True, True, True, True,
    False, True, True, False)), (String ((Ascii (False, False, True, True,
    False, True, True, False)), EmptyString)))))))), (Cons ((String ((Ascii
    (True, True, False, False, True, True, True, False)), (String ((Ascii
    (False, False, True, False, True, True, True, False)), (String ((Ascii
    (False, True, False, False, True, True, True, False)), (String ((Ascii
    (True, False, False, True, False, True, True, False)), (String ((Ascii
    (False, True, True, True, False, True, True, False)), (String ((Ascii
    (True, True, True, False, False, True, True, False)),
    EmptyString)))))))))))), (Cons ((String ((Ascii (False, True, True,
    False, False, True, True, False)), (String ((Ascii (False, False, True,
    True, False, True, True, False)), (String ((Ascii (True, True, True,
    True, False, True, True, False)), (String ((Ascii (True, False, False,
    False, False, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), (String ((Ascii (False, True, True,
    False, True, True, False, False)), (String ((Ascii (False, False, True,
    False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, False, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    EmptyString)))))))))))))), (Cons ((String ((Ascii (True, True, False,
    False, False, True, True, False)), (String ((Ascii (False, False, False,
    True, False, True, True, False)), (String ((Ascii (True, False, False,
    False, False, True, True, False)), (String ((Ascii (False, True, True,
    True, False, True, True, False)), EmptyString)))))))), (Cons ((String
    ((Ascii (True, False, True, True, False, True, True, False)), (String
    ((Ascii (True, False, False, False, False, True, True, False)), (String
    ((Ascii (False, False, False, False, True, True, True, False)),
    EmptyString)))))), Nil))))))))))))))))))))))))))))))))

(** val go_keyword : string -> bool **)

let go_keyword s =
  existsb (eqb1 s) (Cons ((String ((Ascii (False, True, False, False, False,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (True, True, False, True, False,
    True, True, False)), EmptyString)))))))))), (Cons ((String ((Ascii (True,
    True, False, False, False, True, True, False)), (String ((Ascii (True,
    False, False, False, False, True, True, False)), (String ((Ascii (True,
    True, False, False, True, True, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)), EmptyString)))))))),
    (Cons ((String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString)))))))), (Cons ((String ((Ascii (True, True, False,
    False, False, True, True, False)), (String ((Ascii (True, True, True,
    True, False, True, True, False)), (String ((Ascii (False, True, True,
    True, False, True, True, False)), (String ((Ascii (True, True, False,
    False, True, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), EmptyString)))))))))), (Cons ((String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, False, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)),
    EmptyString)))))))))))))))), (Cons ((String ((Ascii (False, False, True,
    False, False, True, True, False)), (String ((Ascii (True, False, True,
    False, False, True, True, False)), (String ((Ascii (False, True, True,
    False, False, True, True, False)), (String ((Ascii (True, False, False,
    False, False, True, True, False)), (String ((Ascii (True, False, True,
    False, True, True, True, False)), (String ((Ascii (False, False, True,
    True, False, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), EmptyString)))))))))))))), (Cons
    ((String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    EmptyString)))))))))), (Cons ((String ((Ascii (True, False, True, False,
    False, True, True, False)), (String ((Ascii (False, False, True, True,
    False, True, True, False)), (String ((Ascii (True, True, False, False,
    True, True, True, False)), (String ((Ascii (True, False, True, False,
    False, True, True, False)), EmptyString)))))))), (Cons ((String ((Ascii
    (False, True, True, False, False, True, True, False)), (String ((Ascii
    (True, False, False, False, False, True, True, False)), (String ((Ascii
    (False, False, True, True, False, True, True, False)), (String ((Ascii
    (False, False, True, True, False, True, True, False)), (String ((Ascii
    (False, False, True, False, True, True, True, False)), (String ((Ascii
    (False, False, False, True, False, True, True, False)), (String ((Ascii
    (False, True, False, False, True, True, True, False)), (String ((Ascii
    (True, True, True, True, False, True, True, False)), (String ((Ascii
    (True, False, True, False, True, True, True, False)), (String ((Ascii
    (True, True, True, False, False, True, True, False)), (String ((Ascii
    (False, False, False, True, False, True, True, False)),
    EmptyString)))))))))))))))))))))), (Cons ((String ((Ascii (False, True,
    True, False, False, True, True, False)), (String ((Ascii (True, True,
    True, True, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, True, False)), EmptyString)))))), (Cons
    ((String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    EmptyString)))))))), (Cons ((String ((Ascii (True, True, True, False,
    False, True, True, False)), (String ((Ascii (True, True, True, True,
    False, True, True, False)), EmptyString)))), (Cons ((String ((Ascii
    (True, True, True, False, False, True, True, False)), (String ((Ascii
    (True, True, True, True, False, True, True, False)), (String ((Ascii
    (False, False, True, False, True, True, True, False)), (String ((Ascii
    (True, True, True, True, False, True, True, False)), EmptyString)))))))),
    (Cons ((String ((Ascii (True, False, False, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, False, True, True,
    False)), EmptyString)))), (Cons ((String ((Ascii (True, False, False,
    True, False, True, True, False)), (String ((Ascii (True, False, True,
    True, False, True, True, False)), (String ((Ascii (False, False, False,
    False, True, True, True, False)), (String ((Ascii (True, True, True,
    True, False, True, True, False)), (String ((Ascii (False, True, False,
    False, True, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), EmptyString)))))))))))), (Cons ((String
    ((Ascii (True, False, False, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (False, True, True, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, False, True, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)),
    EmptyString)))))))))))))))))), (Cons ((String ((Ascii (True, False, True,
    True, False, True, True, False)), (String ((Ascii (True, False, False,
    False, False, True, True, False)), (String ((Ascii (False, False, False,
    False, True, True, True, False)), EmptyString)))))), (Cons ((String
    ((Ascii (False, False, False, False, True, True, True, False)), (String
    ((Ascii (True, False, False, False, False, True, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, True, False, True, False, True, True, False)), (String
    ((Ascii (True, False, False, False, False, True, True, False)), (String
    ((Ascii (True, True, True, False, False, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)),
    EmptyString)))))))))))))), (Cons ((String ((Ascii (False, True, False,
    False, True, True, True, False)), (String ((Ascii (True, False, False,
    False, False, True, True, False)), (String ((Ascii (False, True, True,
    True, False, True, True, False)), (String ((Ascii (True, True, True,
    False, False, True, True, False)), (String ((Ascii (True, False, True,
    False, False, True, True, False)), EmptyString)))))))))), (Cons ((String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)),
    EmptyString)))))))))))), (Cons ((String ((Ascii (True, True, False,
    False, True, True, True, False)), (String ((Ascii (True, False, True,
    False, False, True, True, False)), (String ((Ascii (False, False, True,
    True, False, True, True, False)), (String ((Ascii (True, False, True,
    False, False, True, True, False)), (String ((Ascii (True, True, False,
    False, False, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), EmptyString)))))))))))), (Cons ((String
    ((Ascii (True, True, False, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString)))))))))))), (Cons ((String ((Ascii (True, True, False,
    False, True, True, True, False)), (String ((Ascii (True, True, True,
    False, True, True, True, False)), (String ((Ascii (True, False, False,
    True, False, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), (String ((Ascii (True, True, False,
    False, False, True, True, False)), (String ((Ascii (False, False, False,
    True, False, True, True, False)), EmptyString)))))))))))), (Cons ((String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, False, True, True, True, True, False)), (String
    ((Ascii (False, False, False, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)),
    EmptyString)))))))), (Cons ((String ((Ascii (False, True, True, False,
    True, True, True, False)), (String ((Ascii (True, False, False, False,
    False, True, True, False)), (String ((Ascii (False, True, False, False,
    True, True, True, False)), EmptyString)))))),
    Nil))))))))))))))))))))))))))))))))))))))))))))))))))

(** val go_ident : string -> bool **)

let go_ident s = match s with
| EmptyString -> False
| String (c, _) ->
  (match match is_idstart c with
         | True -> all_idc s
         | False -> False with
   | True -> negb (go_keyword s)
   | False -> False)

(** val nominal_type_ident : string -> bool **)

let nominal_type_ident s =
  match go_ident s with
  | True -> negb (is_type_keyword s)
  | False -> False

type ident = string

type tyName = string

type goTy =
| GTInt
| GTInt64
| GTBool
| GTString
| GTFloat64
| GTFloat32
| GTUint
| GTU8
| GTI8
| GTU16
| GTI16
| GTU32
| GTI32
| GTU64
| GTPtr of goTy
| GTSlice of goTy
| GTChan of goTy
| GTMap of goTy * goTy
| GTNamed of tyName

(** val print_ty : goTy -> string **)

let rec print_ty = function
| GTInt ->
  String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString)))))
| GTInt64 ->
  String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    EmptyString)))))))))
| GTBool ->
  String ((Ascii (False, True, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    EmptyString)))))))
| GTString ->
  String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    EmptyString)))))))))))
| GTFloat64 ->
  String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    EmptyString)))))))))))))
| GTFloat32 ->
  String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, False, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    EmptyString)))))))))))))
| GTUint ->
  String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString)))))))
| GTU8 ->
  String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, True, True, False, False)),
    EmptyString)))))))))
| GTI8 ->
  String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, True, True, False, False)),
    EmptyString)))))))
| GTU16 ->
  String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    EmptyString)))))))))))
| GTI16 ->
  String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    EmptyString)))))))))
| GTU32 ->
  String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, False, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    EmptyString)))))))))))
| GTI32 ->
  String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, False, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    EmptyString)))))))))
| GTU64 ->
  String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    EmptyString)))))))))))
| GTPtr u ->
  append (String ((Ascii (False, True, False, True, False, True, False,
    False)), EmptyString)) (print_ty u)
| GTSlice u ->
  append (String ((Ascii (True, True, False, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, True, False, True,
    False)), EmptyString)))) (print_ty u)
| GTChan u ->
  append (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, False, False, False, False, True, False,
    False)), EmptyString)))))))))) (print_ty u)
| GTMap (k, v) ->
  append (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (True, True, False, True, True, False, True,
    False)), EmptyString))))))))
    (append (print_ty k)
      (append (String ((Ascii (True, False, True, True, True, False, True,
        False)), EmptyString)) (print_ty v)))
| GTNamed n0 -> n0

(** val strip : string -> string -> string option **)

let rec strip p s =
  match p with
  | EmptyString -> Some s
  | String (pc, p') ->
    (match s with
     | EmptyString -> None
     | String (sc, s') ->
       (match eqb0 pc sc with
        | True -> strip p' s'
        | False -> None))

(** val dec_digit : nat -> ascii **)

let dec_digit n0 =
  ascii_of_nat
    (add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S O)))))))))))))))))))))))))))))))))))))))))))))))) n0)

(** val z_digits : nat -> z -> string -> string **)

let rec z_digits fuel z0 acc =
  match fuel with
  | O -> acc
  | S f ->
    let d = dec_digit (Z.to_nat (Z.modulo z0 (Zpos (XO (XI (XO XH)))))) in
    (match Z.eqb (Z.div z0 (Zpos (XO (XI (XO XH))))) Z0 with
     | True -> String (d, acc)
     | False ->
       z_digits f (Z.div z0 (Zpos (XO (XI (XO XH))))) (String (d, acc)))

(** val digit_fuel : z -> nat **)

let digit_fuel z0 =
  S (Z.to_nat (Z.log2 z0))

(** val print_Z : z -> string **)

let print_Z z0 =
  match Z.eqb z0 Z0 with
  | True ->
    String ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)
  | False ->
    (match Z.ltb z0 Z0 with
     | True ->
       append (String ((Ascii (True, False, True, True, False, True, False,
         False)), EmptyString))
         (z_digits (digit_fuel (Z.opp z0)) (Z.opp z0) EmptyString)
     | False -> z_digits (digit_fuel z0) z0 EmptyString)

(** val dval : ascii -> z **)

let dval c =
  Z.of_nat
    (sub (nat_of_ascii c) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))

(** val parseZ_pos : z -> string -> z **)

let rec parseZ_pos acc = function
| EmptyString -> acc
| String (c, s') ->
  parseZ_pos (Z.add (Z.mul acc (Zpos (XO (XI (XO XH))))) (dval c)) s'

(** val parse_Z : string -> z **)

let parse_Z s = match s with
| EmptyString -> Z0
| String (c, s') ->
  (match eqb0 c
           (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))) with
   | True -> Z.opp (parseZ_pos Z0 s')
   | False -> parseZ_pos Z0 s)

(** val ch : nat -> ascii **)

let ch =
  ascii_of_nat

(** val hexdig : nat -> ascii **)

let hexdig n0 =
  ascii_of_nat
    (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S O)))))))))) with
     | True ->
       add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))) n0
     | False ->
       add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         n0)

(** val esc_byte : nat -> string -> string **)

let esc_byte b acc =
  match Nat.eqb b (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))) with
  | True ->
    String
      ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      (String
      ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))),
      acc)))
  | False ->
    (match Nat.eqb b (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
     | True ->
       String
         ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (String
         ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         acc)))
     | False ->
       (match Nat.eqb b (S (S (S (S (S (S (S (S (S (S O)))))))))) with
        | True ->
          String
            ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S
               O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            (String
            ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S
               O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            acc)))
        | False ->
          (match Nat.eqb b (S (S (S (S (S (S (S (S (S O))))))))) with
           | True ->
             String
               ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
               (String
               ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
               acc)))
           | False ->
             (match Nat.eqb b (S (S (S (S (S (S (S (S (S (S (S (S (S
                      O))))))))))))) with
              | True ->
                String
                  ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
                  (String
                  ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S
                     O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
                  acc)))
              | False ->
                (match match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S O)))))))))))))))))))))))))))))))) b with
                       | True ->
                         Nat.ltb b (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S
                           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       | False -> False with
                 | True -> String ((ch b), acc)
                 | False ->
                   String
                     ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S
                        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
                     (String
                     ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S
                        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
                     (String
                     ((hexdig
                        (Nat.div b (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S O)))))))))))))))))),
                     (String
                     ((hexdig
                        (Nat.modulo b (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S O)))))))))))))))))),
                     acc))))))))))))

(** val esc_string : string -> string **)

let rec esc_string = function
| EmptyString -> EmptyString
| String (c, rest) -> esc_byte (nat_of_ascii c) (esc_string rest)

(** val print_string_lit : string -> string **)

let print_string_lit s =
  String
    ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))),
    (append (esc_string s) (String
      ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))),
      EmptyString))))

(** val unhex : ascii -> nat **)

let unhex c =
  let v = nat_of_ascii c in
  (match Nat.leb v (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
   | True ->
     sub v (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))
   | False ->
     sub v (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val unescape : string -> string **)

let rec unescape = function
| EmptyString -> EmptyString
| String (c1, rest) ->
  (match Nat.eqb (nat_of_ascii c1) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
   | True ->
     (match rest with
      | EmptyString -> EmptyString
      | String (c2, rest2) ->
        let d = nat_of_ascii c2 in
        (match Nat.eqb d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))))) with
         | True ->
           String
             ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O))))))))))))))))))))))))))))))))))),
             (unescape rest2))
         | False ->
           (match Nat.eqb d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
            | True ->
              String
                ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
                (unescape rest2))
            | False ->
              (match Nat.eqb d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
               | True ->
                 String ((ch (S (S (S (S (S (S (S (S (S (S O))))))))))),
                   (unescape rest2))
               | False ->
                 (match Nat.eqb d (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                  | True ->
                    String ((ch (S (S (S (S (S (S (S (S (S O)))))))))),
                      (unescape rest2))
                  | False ->
                    (match Nat.eqb d (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S
                             O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                     | True ->
                       String
                         ((ch (S (S (S (S (S (S (S (S (S (S (S (S (S
                            O)))))))))))))),
                         (unescape rest2))
                     | False ->
                       (match Nat.eqb d (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S
                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                        | True ->
                          (match rest2 with
                           | EmptyString -> EmptyString
                           | String (h1, s0) ->
                             (match s0 with
                              | EmptyString -> EmptyString
                              | String (h2, rest3) ->
                                String
                                  ((ch
                                     (add
                                       (mul (S (S (S (S (S (S (S (S (S (S (S
                                         (S (S (S (S (S O))))))))))))))))
                                         (unhex h1))
                                       (unhex h2))),
                                  (unescape rest3))))
                        | False -> EmptyString)))))))
   | False -> String (c1, (unescape rest)))

(** val but_last : string -> string **)

let rec but_last = function
| EmptyString -> EmptyString
| String (c, rest) ->
  (match rest with
   | EmptyString -> EmptyString
   | String (_, _) -> String (c, (but_last rest)))

(** val is_strlit : string -> bool **)

let is_strlit a = match a with
| EmptyString -> False
| String (c, rest) ->
  (match eqb0 c
           (ch (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))))) with
   | True ->
     (match rest with
      | EmptyString -> False
      | String (_, _) -> eqb1 (print_string_lit (unescape (but_last rest))) a)
   | False -> False)

(** val hex_digits : nat -> z -> string -> string **)

let rec hex_digits fuel z0 acc =
  match fuel with
  | O -> acc
  | S f ->
    let d = hexdig (Z.to_nat (Z.modulo z0 (Zpos (XO (XO (XO (XO XH))))))) in
    (match Z.eqb (Z.div z0 (Zpos (XO (XO (XO (XO XH)))))) Z0 with
     | True -> String (d, acc)
     | False ->
       hex_digits f (Z.div z0 (Zpos (XO (XO (XO (XO XH)))))) (String (d, acc)))

(** val print_hex : z -> string **)

let print_hex z0 =
  append (String ((Ascii (False, False, False, False, True, True, False,
    False)), (String ((Ascii (False, False, False, True, True, True, True,
    False)), EmptyString))))
    (match Z.eqb z0 Z0 with
     | True ->
       String ((Ascii (False, False, False, False, True, True, False,
         False)), EmptyString)
     | False -> hex_digits (digit_fuel z0) z0 EmptyString)

(** val print_float_hex : bool -> z -> z -> string **)

let print_float_hex sign mant exp =
  append
    (match sign with
     | True ->
       String ((Ascii (True, False, True, True, False, True, False, False)),
         EmptyString)
     | False -> EmptyString)
    (append (print_hex mant)
      (append (String ((Ascii (False, False, False, False, True, True, True,
        False)), EmptyString)) (print_Z exp)))

type binOp =
| BMul
| BDiv
| BRem
| BShl
| BShr
| BAnd
| BAndNot
| BAdd
| BSub
| BOr
| BXor
| BEq
| BNe
| BLt
| BLe
| BGt
| BGe
| BLAnd
| BLOr

(** val binop_prec : binOp -> nat **)

let binop_prec = function
| BAdd -> S (S (S (S O)))
| BSub -> S (S (S (S O)))
| BOr -> S (S (S (S O)))
| BXor -> S (S (S (S O)))
| BEq -> S (S (S O))
| BNe -> S (S (S O))
| BLt -> S (S (S O))
| BLe -> S (S (S O))
| BGt -> S (S (S O))
| BGe -> S (S (S O))
| BLAnd -> S (S O)
| BLOr -> S O
| _ -> S (S (S (S (S O))))

(** val binop_text : binOp -> string **)

let binop_text = function
| BMul ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, False, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BDiv ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BRem ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BShl ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, True, True, False, False)),
    (String ((Ascii (False, False, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BShr ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, True, True, True, False, False)),
    (String ((Ascii (False, True, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BAnd ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BAndNot ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, False, False)),
    (String ((Ascii (False, True, True, True, True, False, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BAdd ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, True, False, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BSub ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BOr ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BXor ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, True, True, False, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BEq ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, True, True, True, False, False)),
    (String ((Ascii (True, False, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BNe ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, False, False, False, True, False, False)),
    (String ((Ascii (True, False, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BLt ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BLe ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, True, True, False, False)),
    (String ((Ascii (True, False, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BGt ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))
| BGe ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, True, True, True, False, False)),
    (String ((Ascii (True, False, True, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BLAnd ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, False, False)),
    (String ((Ascii (False, True, True, False, False, True, False, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))
| BLOr ->
  String ((Ascii (False, False, False, False, False, True, False, False)),
    (String ((Ascii (False, False, True, True, True, True, True, False)),
    (String ((Ascii (False, False, True, True, True, True, True, False)),
    (String ((Ascii (False, False, False, False, False, True, False, False)),
    EmptyString)))))))

(** val op_order : binOp list **)

let op_order =
  Cons (BShl, (Cons (BShr, (Cons (BAndNot, (Cons (BLAnd, (Cons (BLOr, (Cons
    (BEq, (Cons (BNe, (Cons (BLe, (Cons (BGe, (Cons (BMul, (Cons (BDiv, (Cons
    (BRem, (Cons (BAnd, (Cons (BAdd, (Cons (BSub, (Cons (BOr, (Cons (BXor,
    (Cons (BLt, (Cons (BGt, Nil)))))))))))))))))))))))))))))))))))))

(** val op_match_in : binOp list -> string -> (binOp, string) prod option **)

let rec op_match_in tbl s =
  match tbl with
  | Nil -> None
  | Cons (o, tl) ->
    (match strip (binop_text o) s with
     | Some r -> Some (Pair (o, r))
     | None -> op_match_in tl s)

(** val op_match : string -> (binOp, string) prod option **)

let op_match s =
  op_match_in op_order s

(** val is_space : ascii -> bool **)

let is_space c =
  eqb0 c
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))

(** val is_op_char : ascii -> bool **)

let is_op_char c =
  let n0 = nat_of_ascii c in
  (match match match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))))))))))))) with
               | True -> True
               | False ->
                 Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S
                   O))))))))))))))))))))))))))))))))))))))))))))))) with
         | True -> True
         | False ->
           (match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S O))))))))))))))))))))))))))))))))))))) with
            | True -> True
            | False ->
              Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S
                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
   | True -> True
   | False ->
     (match match match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                  | True -> True
                  | False ->
                    Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))) with
            | True -> True
            | False ->
              (match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
               | True -> True
               | False ->
                 Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S
                   O)))))))))))))))))))))))))))))))))))))))))))) with
      | True -> True
      | False ->
        (match match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S
                       O))))))))))))))))))))))))))))))))))))))))))))) with
               | True -> True
               | False ->
                 Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
         | True -> True
         | False ->
           (match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S
                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
            | True -> True
            | False ->
              Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))))))))

(** val is_bopen : ascii -> bool **)

let is_bopen c =
  match match eqb0 c
                (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S O))))))))))))))))))))))))))))))))))))))))) with
        | True -> True
        | False ->
          eqb0 c
            (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
  | True -> True
  | False ->
    eqb0 c
      (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_bclose : ascii -> bool **)

let is_bclose c =
  match match eqb0 c
                (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))) with
        | True -> True
        | False ->
          eqb0 c
            (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
  | True -> True
  | False ->
    eqb0 c
      (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_open : ascii -> bool **)

let is_open c =
  eqb0 c
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))

(** val opens : string -> bool **)

let opens s =
  match op_match s with
  | Some _ -> True
  | None -> False

(** val op_after : string -> bool **)

let op_after = function
| EmptyString -> False
| String (c, _) -> is_op_char c

(** val close_of : ascii -> ascii **)

let close_of c =
  match eqb0 c
          (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))) with
  | True ->
    ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))
  | False ->
    (match eqb0 c
             (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S
               O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
     | True ->
       ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | False ->
       ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val bstack_ok : ascii list -> string -> bool **)

let rec bstack_ok st = function
| EmptyString -> (match st with
                  | Nil -> True
                  | Cons (_, _) -> False)
| String (c, s') ->
  (match match st with
         | Nil ->
           (match opens (String (c, s')) with
            | True -> True
            | False ->
              (match is_space c with
               | True -> op_after s'
               | False -> False))
         | Cons (_, _) -> False with
   | True -> False
   | False ->
     (match is_bopen c with
      | True -> bstack_ok (Cons ((close_of c), st)) s'
      | False ->
        (match is_bclose c with
         | True ->
           (match st with
            | Nil -> False
            | Cons (top, st') ->
              (match eqb0 c top with
               | True -> bstack_ok st' s'
               | False -> False))
         | False -> bstack_ok st s')))

(** val atomic : string -> bool **)

let atomic s = match s with
| EmptyString -> False
| String (c, _) ->
  (match negb (is_open c) with
   | True -> bstack_ok Nil s
   | False -> False)

(** val pv : ascii -> z **)

let pv c =
  match eqb0 c
          (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))) with
  | True -> Zpos XH
  | False ->
    (match eqb0 c
             (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S O)))))))))))))))))))))))))))))))))))))))))) with
     | True -> Zneg XH
     | False -> Z0)

(** val depth : z -> string -> z **)

let rec depth d = function
| EmptyString -> d
| String (c, s') -> depth (Z.add d (pv c)) s'

(** val nneg_b : z -> string -> bool **)

let rec nneg_b d = function
| EmptyString -> True
| String (c, s') ->
  (match Z.leb Z0 (Z.add d (pv c)) with
   | True -> nneg_b (Z.add d (pv c)) s'
   | False -> False)

(** val balanced_b : string -> bool **)

let balanced_b s =
  match Z.eqb (depth Z0 s) Z0 with
  | True -> nneg_b Z0 s
  | False -> False

(** val atom_ok : string -> bool **)

let atom_ok s =
  match atomic s with
  | True -> balanced_b s
  | False -> False

(** val is_dec_char : ascii -> bool **)

let is_dec_char c =
  match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))
          (nat_of_ascii c) with
  | True ->
    Nat.leb (nat_of_ascii c) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | False -> False

(** val all_dec : string -> bool **)

let rec all_dec = function
| EmptyString -> True
| String (c, s') ->
  (match is_dec_char c with
   | True -> all_dec s'
   | False -> False)

(** val is_dec : string -> bool **)

let is_dec = function
| EmptyString -> False
| String (c, rest) ->
  (match eqb0 c
           (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))) with
   | True ->
     (match rest with
      | EmptyString -> False
      | String (_, _) -> all_dec rest)
   | False -> (match is_dec_char c with
               | True -> all_dec rest
               | False -> False))

(** val strlit_ok : string -> bool **)

let strlit_ok s =
  match atom_ok s with
  | True -> is_strlit s
  | False -> False

(** val raw_ok : string -> bool **)

let raw_ok s =
  match match match match atom_ok s with
                    | True -> negb (go_ident s)
                    | False -> False with
              | True -> negb (is_dec s)
              | False -> False with
        | True -> negb (is_strlit s)
        | False -> False with
  | True -> negb (go_keyword s)
  | False -> False

type goAtom =
| AIdent of ident
| AIntLit of z
| AStringLit of string
| ARaw of string

(** val atom_str : goAtom -> string **)

let atom_str = function
| AIdent i -> i
| AIntLit z0 -> print_Z z0
| AStringLit r -> r
| ARaw r -> r

type goExpr =
| EAtom of goAtom
| EBin of binOp * goExpr * goExpr

(** val print_expr : nat -> goExpr -> string **)

let rec print_expr ctx = function
| EAtom a -> atom_str a
| EBin (o, l, r) ->
  let p = binop_prec o in
  let inner =
    append (print_expr p l) (append (binop_text o) (print_expr (S p) r))
  in
  (match Nat.ltb p ctx with
   | True ->
     append (String ((Ascii (False, False, False, True, False, True, False,
       False)), EmptyString))
       (append inner (String ((Ascii (True, False, False, True, False, True,
         False, False)), EmptyString)))
   | False -> inner)

(** val print_sep : string -> string list -> string **)

let rec print_sep sep = function
| Nil -> EmptyString
| Cons (x, xs') ->
  (match xs' with
   | Nil -> x
   | Cons (_, _) -> append x (append sep (print_sep sep xs')))
