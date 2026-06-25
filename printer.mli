
type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

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

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module N :
 sig
  val of_nat : nat -> n
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val zero : ascii

val one : ascii

val shift : bool -> ascii -> ascii

val ascii_of_pos : positive -> ascii

val ascii_of_N : n -> ascii

val ascii_of_nat : nat -> ascii

type string =
| EmptyString
| String of ascii * string

val append : string -> string -> string

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val to_nat : z -> nat

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z
 end

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
| GTNamed of string

val print_ty : goTy -> string

val dec_digit : nat -> ascii

val z_digits : nat -> z -> string -> string

val print_Z : z -> string
