(** ============================================================================
    GoSem.v — the AST's BEHAVIORAL semantics as a BRIDGE into cmd.v (ARCHITECTURE.md §GoSem).
    No second universe: [denote_program : Program -> option (Cmd unit)] translates a GoAst program into
    cmd.v's proven command tree (reusing [run_cmd]/[cbind], the GoSafe gate, the model's own value
    ctors) — single-authority, faithful.

    SLICE 1 (partial): denotes println/print/panic/return/blank-assign/defer + effectful call args,
    over the exact-or-absent [eval_value] fold, the runtime GTInt tier R1–R8 (R8 = the engine's own
    bitwise + heterogeneous-shift rows), and the typed-runtime tier T1–T5 (ONE shared evaluator,
    [reval_val_with]; [denote_expr] is a thin wrapper).
    FAITHFUL-OR-ABSENT: the right behavior or [None] ("not modeled yet", never "invalid" and never
    wrong).  [gosem_sound]: denotation ⊆ [SupportedProgram]; NOT the converse, NOT [BehaviorSafe].
    Absence boundaries are PINNED, not prose — [gosem_frontier_surface] is the ONE gated authority,
    and its Coq definition is the ONLY member list (this header deliberately enumerates none of it).
    Public zero-axiom surfaces (topic-split, composed, manifest-gated): [gosem_trust_surface]
    (core / float / slice-index / runtime-int / map / frontier) + [gosem_string_authority_surface].
    ============================================================================ *)
From Fido Require Import GoAst GoTypes GoSafe cmd preamble.   (* [preamble] re-exports [builtins]: [GoAny]/[anyt]/[intwrap]/[World]/[w_log]/[Outcome]/[ORet] *)
From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.

(** Box an integer-constant VALUE [z] of int type [t] as the MODEL's runtime [GoAny] — or [None].  FAILS CLOSED
    at the BOUNDARY: it first checks [int_const_repr z t] (is [z] representable in [t]?), so an out-of-range [z]
    yields [None] HERE, not a silently [*wrap]-mangled value — exactness does NOT rely on a caller having gated
    (rule 4: evidence at the builder).  When in range the [*wrap] constructor is IDENTITY, so it builds EXACTLY
    the model's value (e.g. [int64(3)] -> [anyt TI64 (i64wrap 3)] = [MkI64 3], what the model's [println]
    carries).  [GTUint] is boxed via [mk_uint] below (the model's proof-carrying [uint_lit]); floats go through
    [box_float] below. *)

(** Box a [GTUint] (Go platform [uint]) CONSTANT [z].  The model's [GoUint] carries an [in_u64] PROOF, so
    [mk_uint] discharges it self-soundly via a dependent match on [in_u64 z] — NOT caller-gated ([None] if
    [z] ∉ [[0,2^64)]).  [box_int]'s [int_const_repr] guard already restricts [z] to [GTUint]'s conservative
    [[0,2^32-1]] ⊂ [[0,2^64)], where [uint_lit z] is the model's EXACT uint value [z] (the [GoU64] shape). *)
Definition mk_uint (z : Z) : option GoAny :=
  (match in_u64 z as b return (in_u64 z = b -> option GoAny) with
   | true  => fun pf => Some (anyt TUint (uint_lit z pf))
   | false => fun _  => None
   end) eq_refl.

Definition box_int (t : GoTy) (z : Z) : option GoAny :=
  if int_const_repr z t then
    match t with
    | GTInt   => Some (anyt TInt64 (intwrap z))   (* Go [int]  -> [GoInt] *)
    | GTInt64 => Some (anyt TI64  (i64wrap z))     (* Go [int64]-> [GoI64] (Z-carried) *)
    | GTU8    => Some (anyt TU8   (u8wrap  z))
    | GTI8    => Some (anyt TI8   (i8wrap  z))
    | GTU16   => Some (anyt TU16  (u16wrap z))
    | GTI16   => Some (anyt TI16  (i16wrap z))
    | GTU32   => Some (anyt TU32  (u32wrap z))
    | GTI32   => Some (anyt TI32  (i32wrap z))
    | GTU64   => Some (anyt TU64  (u64wrap z))
    | GTUint  => mk_uint z   (* Go platform [uint] -> [GoUint], via the model's proof-carrying [uint_lit] *)
    | _       => None        (* non-integer [t] *)
    end
  else None.

(** Box a float-CONSTANT VALUE — the EXACT dyadic [m * 2^e] a [PtFloatConst] of type [t] carries — as the
    MODEL's runtime [GoAny], or [None].  The dyadic IS the model's shape ([spec_float]'s [S754_finite s p e]
    = ±p·2^e), so [sf_of_dyadic] is a direct constructor and [renorm 53 1024] / [f32_lit] canonicalize it —
    EXACT inside [float_dyadic_repr]'s window (the SAME guard [ptype]'s folds use, re-checked HERE so an
    out-of-window value fails closed — no rounded-lie value).  An INTEGER dyadic [(z, 0)] boxes to exactly
    the old integer form ([sf_of_dyadic z 0 = sf_of_Z z] definitionally per sign case). *)
Definition sf_of_dyadic (m e : Z) : spec_float :=
  match m with
  | Z0 => S754_zero false
  | Zpos p => S754_finite false p e
  | Zneg p => S754_finite true p e
  end.
Definition box_float (t : GoTy) (m e : Z) : option GoAny :=
  if float_dyadic_repr t m e then
    match t with
    | GTFloat64 => Some (anyt TFloat64 (renorm 53 1024 (sf_of_dyadic m e)))   (* canonical binary64 *)
    | GTFloat32 => Some (anyt TFloat32 (f32_lit (sf_of_dyadic m e)))           (* canonical binary32 (exact in-window) *)
    | _         => None
    end
  else None.

(** ---- The PER-NODE float-fold checker (consumed by the [floats_checked] BOUNDARY below — the boundary,
    at [eval_value]'s top, is what makes the no-bypass claim; [fsf_checked] alone is NOT an authority: its
    int-constant conversion leaves deliberately do NOT recurse, the boundary's full-syntax recursion
    covers them) ---- [ptype] folds float-const arithmetic exactly (sealed dyadics); the checker
    verifies every node with the CONSTANT-fold operation layer ([sf_const_binop]/[sf_const_neg]
    below — the width's IEEE table under [sf_pos_zero] zero-sign erasure: Go constants are exact
    rationals with NO signed zero, so the fold authority is the constant rule; raw [SF*] zero
    signs belong to RUNTIME paths only).  CLAIM HYGIENE: for the
    ACCEPTED exact-dyadic subset the model value agrees with the printed Go constant expression's
    observable value (Go may CONSTANT-fold these at compile time — no "same runtime op" claim);
    non-exact/rounding cases are REJECTED until the general dyadic↔SF agreement theorem lands.
    [fsf_checked] verifies ONE float-constant node against the const op on the verified operand carriers
    (recursing through float operands and float-to-float conversions; cross-width via
    [f32_of_f64]/[f64_of_f32]); a disagreeing node is ABSENT ([None]), never wrong.  (For NONZERO
    results no disagreement should exist — IEEE ops are correctly rounded, so an exactly
    representable result is returned exactly; ZERO results are verified under the constant rule.
    PROVING acceptance total on the admitted class — the general dyadic↔[SF*] class theorem,
    plans/dyadic-sf-agreement.md — would let this runtime re-verification be dropped.) *)
Definition sf_eqb_struct (x y : spec_float) : bool :=
  match x, y with
  | S754_zero s1, S754_zero s2 => Bool.eqb s1 s2
  | S754_infinity s1, S754_infinity s2 => Bool.eqb s1 s2
  | S754_nan, S754_nan => true
  | S754_finite s1 m1 e1, S754_finite s2 m2 e2 =>
      andb (Bool.eqb s1 s2) (andb (Pos.eqb m1 m2) (Z.eqb e1 e2))
  | _, _ => false
  end.
(** The boxed CARRIER of a dyadic at width [t] (binary64: the canonical spec_float; binary32: the
    [f32val] carrier). *)
Definition sf_render (t : GoTy) (m e : Z) : option spec_float :=
  match t with
  | GTFloat64 => Some (renorm 53 1024 (sf_of_dyadic m e))
  | GTFloat32 => Some (f32val (f32_lit (sf_of_dyadic m e)))
  | _ => None
  end.
Definition sf_model_binop (t : GoTy) (op : BinOp) : option (spec_float -> spec_float -> spec_float) :=
  match t with
  | GTFloat64 =>
      match op with
      | BAdd => Some f64_add | BSub => Some f64_sub | BMul => Some f64_mul | BDiv => Some f64_div
      | _ => None
      end
  | GTFloat32 =>
      match op with
      | BAdd => Some (fun x y => f32val (f32_add (f32_lit x) (f32_lit y)))
      | BSub => Some (fun x y => f32val (f32_sub (f32_lit x) (f32_lit y)))
      | BMul => Some (fun x y => f32val (f32_mul (f32_lit x) (f32_lit y)))
      | BDiv => Some (fun x y => f32val (f32_div (f32_lit x) (f32_lit y)))
      | _ => None
      end
  | _ => None
  end.
(** ---- The CONSTANT-fold operation layer — Go's exact-rational constant semantics, split from
    the runtime IEEE ops for the WHOLE checker (not per-op): constants have NO signed zero, so a
    CONSTANT operation's ZERO result is [+0] whatever zero sign the runtime op carries
    ([SFmul +0 (-1) = -0] and [SFdiv +0 (-1) = -0], but the constants [0 * -1] and [0 / -1] ARE
    the rational 0 — gc folds them to [+0]; same for [SFopp +0 = -0] vs [-(0.0)],
    go-run-verified [1/x = +Inf]).  [sf_pos_zero] is the ONE erasure authority;
    [sf_const_binop]/[sf_const_neg] wrap the width's IEEE table with it and are the ONLY
    verification ops [fsf_checked] uses (the conversion arms need none — their inputs are dyadic
    RENDERS, whose zeros are already [+0]).  NONZERO results are untouched (erasure inert), so
    acceptance still means "the value IS the exact fold"; the raw [SF*]/[f32_*] ops keep their
    IEEE zero signs for RUNTIME paths (none live yet — [PtRunFloat] is class-absent). *)
Definition sf_pos_zero (v : spec_float) : spec_float :=
  match v with S754_zero _ => S754_zero false | x => x end.
Definition sf_const_binop (t : GoTy) (op : BinOp) : option (spec_float -> spec_float -> spec_float) :=
  match sf_model_binop t op with
  | Some f => Some (fun x y => sf_pos_zero (f x y))
  | None => None
  end.
Definition sf_const_neg (t : GoTy) : option (spec_float -> spec_float) :=
  match t with
  | GTFloat64 => Some (fun x => sf_pos_zero (SFopp x))
  | GTFloat32 => Some (fun x => sf_pos_zero (f32val (f32_neg (f32_lit x))))
  | _ => None
  end.
(** the zero rows sealed at the LAYER: ANY zero result of a constant op is [+0] — width- and
    op-generic (multiplication/division by a negative constant included, where the runtime rows
    leak [xorb] signs) *)
Lemma sf_const_binop_zero_erased : forall t op f g x y s,
  sf_model_binop t op = Some g ->
  sf_const_binop t op = Some f ->
  g x y = S754_zero s ->
  f x y = S754_zero false.
Proof.
  intros t op f g x y s Hg Hf Hz. unfold sf_const_binop in Hf.
  rewrite Hg in Hf. injection Hf as <-. cbv beta. rewrite Hz. reflexivity.
Qed.
Lemma sf_const_neg_zero_erased : forall t f s,
  sf_const_neg t = Some f -> f (S754_zero s) = S754_zero false.
Proof.
  intros t f s H; destruct t; try discriminate H; injection H as <-; destruct s; reflexivity.
Qed.
(** A float-op OPERAND's verified carrier at [t] — a same-typed float const (recursively verified via
    [rec], instantiated with [fsf_checked] itself) or an untyped int const in the exact interval (Go
    converts it to [t]; a leaf).  Parametrized so the Fixpoint below can use it mid-definition; the
    instance [fsf_operand] names it for the theorems. *)
Definition fsf_operand_with (rec : GExpr -> option spec_float) (t : GoTy) (a : GExpr)
  : option spec_float :=
  match ptype a with
  | Some (PtIntConst z) =>
      if int_in_float_exact_interval t z
      then sf_render t (dy_m (dy_make z 0)) (dy_e (dy_make z 0)) else None
  | Some (PtFloatConst ta _) => if numty_eqb ta t then rec a else None
  | _ => None
  end.
Fixpoint fsf_checked (e : GExpr) : option spec_float :=
  match ptype e with
  | Some (PtFloatConst t d) =>
      match sf_render t (dy_m d) (dy_e d) with
      | None => None
      | Some vr =>
          match e with
          | EBn op a b =>
              match fsf_operand_with fsf_checked t a, fsf_operand_with fsf_checked t b,
                    sf_const_binop t op with
              | Some va, Some vb, Some f => if sf_eqb_struct (f va vb) vr then Some vr else None
              | _, _, _ => None
              end
          | EUn _ a =>
              match fsf_operand_with fsf_checked t a, sf_const_neg t with
              | Some va, Some fneg => if sf_eqb_struct (fneg va) vr then Some vr else None
              | _, _ => None
              end
          | ECall _ (a :: nil) =>
              (* the scalar float CONVERSION [float64(x)]/[float32(x)] *)
              match ptype a with
              | Some (PtIntConst _) | Some (PtTIntConst _ _) => Some vr   (* leaf: int-const source, no fold inside *)
              | Some (PtFloatConst ta _) =>
                  match fsf_checked a with
                  | Some va =>
                      if numty_eqb ta t
                      then (if sf_eqb_struct va vr then Some vr else None)                   (* same-width identity *)
                      else match t, ta with
                           | GTFloat32, GTFloat64 =>                                        (* narrow via the model's f32_of_f64 *)
                               if sf_eqb_struct (f32val (f32_of_f64 va)) vr then Some vr else None
                           | GTFloat64, GTFloat32 =>                                        (* widen via the model's f64_of_f32 *)
                               if sf_eqb_struct (f64_of_f32 (f32_lit va)) vr then Some vr else None
                           | _, _ => None
                           end
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      end
  | _ => None
  end.
Definition fsf_operand : GoTy -> GExpr -> option spec_float := fsf_operand_with fsf_checked.

(** THE FLOAT BOUNDARY — [floats_checked e]: EVERY subexpression of [e] whose [ptype] is a float
    CONSTANT passes [fsf_checked] (plain syntax recursion into ALL children — slice elements, map keys
    and values, conversion sources, either operand — so a float fold LAUNDERED through an integer
    conversion like [int(float64(3)*float64(2))], a comparison operand, a string-conversion source, or a
    literal element is still reached and re-verified).  [eval_value] checks this ONCE at its top — the
    single value-denotation entry every consumer flows through — so no denoted value anywhere depends on
    an unverified float fold ([eval_value_floats_checked] below is the structural seal). *)
Definition fc_node (e : GExpr) : bool :=
  match ptype e with
  | Some (PtFloatConst _ _) => match fsf_checked e with Some _ => true | None => false end
  | _ => true
  end.
Fixpoint floats_checked (e : GExpr) : bool :=
  fc_node e
  && match e with
     | EId _ | EInt _ | EStr _ | EHex _ => true
     | EUn _ a => floats_checked a
     | EBn _ a b => floats_checked a && floats_checked b
     | ESel a _ => floats_checked a
     | EIndex a i => floats_checked a && floats_checked i
     | ESlice a lo hi => floats_checked a && floats_checked lo && floats_checked hi
     | ECall f args => floats_checked f && forallb floats_checked args
     | EAssert a _ => floats_checked a
     | EConv _ a => floats_checked a
     | ESliceLit _ es => forallb floats_checked es
     | EMapLit _ _ kvs => forallb (fun kv => floats_checked (fst kv) && floats_checked (snd kv)) kvs
     end.

(** STRUCTURAL RECURSION GATES for the float boundary — one definitional equation per [GExpr]
    constructor, ALL 14 (child-carrying: binop/comparison operands, the unary operand, call args incl.
    scalar/string conversion sources, slice elements, map KEYS and VALUES, index/slice children, [ESel]/
    [EAssert]/[EConv] sources; plus the four leaves).  Deleting any recursive child branch of
    [floats_checked] FALSIFIES its equation — Coq breaks, not just a review.  Gated in
    [gosem_trust_surface]. *)
Lemma floats_checked_children_eqs :
  (forall o a b, floats_checked (EBn o a b) = fc_node (EBn o a b) && (floats_checked a && floats_checked b))
  /\ (forall o a, floats_checked (EUn o a) = fc_node (EUn o a) && floats_checked a)
  /\ (forall f args, floats_checked (ECall f args)
        = fc_node (ECall f args) && (floats_checked f && forallb floats_checked args))
  /\ (forall t es, floats_checked (ESliceLit t es) = fc_node (ESliceLit t es) && forallb floats_checked es)
  /\ (forall kt vt kvs, floats_checked (EMapLit kt vt kvs)
        = fc_node (EMapLit kt vt kvs)
          && forallb (fun kv => floats_checked (fst kv) && floats_checked (snd kv)) kvs)
  /\ (forall a i, floats_checked (EIndex a i) = fc_node (EIndex a i) && (floats_checked a && floats_checked i))
  /\ (forall c a, floats_checked (EConv c a) = fc_node (EConv c a) && floats_checked a)
  /\ (forall a f, floats_checked (ESel a f) = fc_node (ESel a f) && floats_checked a)
  /\ (forall a lo hi, floats_checked (ESlice a lo hi)
        = fc_node (ESlice a lo hi) && (floats_checked a && floats_checked lo && floats_checked hi))
  /\ (forall a t, floats_checked (EAssert a t) = fc_node (EAssert a t) && floats_checked a)
  /\ (forall i, floats_checked (EId i) = fc_node (EId i) && true)
  /\ (forall z, floats_checked (EInt z) = fc_node (EInt z) && true)
  /\ (forall str, floats_checked (EStr str) = fc_node (EStr str) && true)
  /\ (forall h, floats_checked (EHex h) = fc_node (EHex h) && true).
Proof. repeat split; intros; reflexivity. Qed.

(** The COMPARISON [BinOp]s fold a constant integer pair to a [bool] ([>]/[>=] reuse [<]/[<=] with swapped
    operands).  Arithmetic / [BLAnd] / [BLOr] are NOT comparisons -> [None] HERE; the logical [&&]/[||] are
    handled separately by [eval_bool] (which recurses on their bool operands). *)
Definition cmp_op (op : BinOp) : option (Z -> Z -> bool) :=
  match op with
  | BEq => Some Z.eqb
  | BNe => Some (fun x y => negb (Z.eqb x y))
  | BLt => Some Z.ltb
  | BLe => Some Z.leb
  | BGt => Some (fun x y => Z.ltb y x)
  | BGe => Some (fun x y => Z.leb y x)
  | _   => None
  end.

(** The constant VALUE of an INTEGER operand (the true value as [Z], so [Z]-comparison IS the Go
    comparison), via [ptype]; [None] for a FLOAT (its dyadic value compares via [const_dy] below), a
    RUNTIME, or a non-numeric operand (so a comparison with a [len(..)] operand is honestly absent). *)
Definition const_z (e : GExpr) : option Z :=
  match ptype e with
  | Some (PtIntConst z) | Some (PtTIntConst _ z) => Some z
  | _ => None
  end.
(** The exact DYADIC value of a FLOAT-constant operand — after [dy_align] the mantissa pair compares
    exactly as the values do, so the SAME [Z] comparators fold float comparisons with no rounding.
    ([ptype]'s comparison gate already forces both operands to the same float type.) *)
Definition const_dy (e : GExpr) : option (Z * Z) :=
  match ptype e with
  | Some (PtFloatConst _ d) => Some (dy_m d, dy_e d)
  | _ => None
  end.

(** The constant string VALUE of a supported [PtStr] expr — THE SINGLE string-value authority (both
    [eval_value]'s [PtStr] arm AND [eval_bool]'s string comparisons consult it).  Folds a LITERAL [EStr s], the
    CONCATENATION [a + b] (Go [+] on strings = byte [String.append], exact), and the CONVERSION [string(a)]
    (mirroring [conv_to_scalar]'s [GTString] cases: an identity string source, or an ASCII rune [z ∈ [0,127]]
    whose UTF-8 IS the single byte [z]).  SEALED under [ptype = PtStr] (never folds ill-typed [`"a" + 1`]).
    ABSENT ([None], honestly): a multi-byte rune [string(200)] and any runtime string. *)
Fixpoint eval_str (e : GExpr) : option string :=
  match ptype e with
  | Some PtStr =>   (* SEAL: fold ONLY what [ptype] validated as a string *)
      match e with
      | EStr s        => Some s
      | EBn BAdd a b  => match eval_str a, eval_str b with
                         | Some sa, Some sb => Some (String.append sa sb)
                         | _, _ => None
                         end
      | ECall (EId i) (a :: nil) =>   (* the string conversion [string(a)] — MIRRORS [conv_to_scalar]'s [GTString] cases *)
          if String.eqb (proj1_sig i) "string"
          then match ptype a with
               | Some PtStr => eval_str a   (* string SOURCE: the identity conversion [string("a"+"b")] = its bytes *)
               | Some (PtIntConst z) | Some (PtTIntConst _ z) =>
                   (* rune conversion.  FAITHFUL-OR-ABSENT: fold ONLY code points [0,127], whose UTF-8 encoding IS
                      the single byte [z] ([string(65)] = ["A"]) — trivially exact.  A rune >127 (multi-byte UTF-8)
                      or an out-of-range/negative rune (Go yields [U+FFFD]) is NOT folded — absent, never wrong. *)
                   if andb (Z.leb 0 z) (Z.leb z 127)
                   then Some (String (Ascii.ascii_of_nat (Z.to_nat z)) EmptyString)
                   else None
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

(** The 6 COMPARISON ops on STRING constants — DELEGATED to the MODEL's string order, named by their FULLY
    QUALIFIED paths ([Fido.builtins.str_eqb] / [str_neqb] / [str_ltb] / [str_gtb] / [str_geb], the byte-wise
    unsigned Go order, plugin-lowered to the native Go operators).  The qualified names make the live path
    SHADOW-IMMUNE: a local/nested [str_ltb] in GoSem cannot reroute it (the [str_cmp_*_model] pins below prove
    each branch IS the qualified model constant).  GoSem forks NO string order; [<=] is DERIVED from the model's
    [>=] ([s <= t] iff [t >= s]).  Non-comparison ops -> [None]. *)
Definition str_cmp_op (op : BinOp) : option (GoString -> GoString -> bool) :=
  match op with
  | BEq => Some Fido.builtins.str_eqb
  | BNe => Some Fido.builtins.str_neqb
  | BLt => Some Fido.builtins.str_ltb
  | BLe => Some (fun s t => Fido.builtins.str_geb t s)   (* [s <= t]  iff  [t >= s] — derived from the model order, not re-implemented *)
  | BGt => Some Fido.builtins.str_gtb
  | BGe => Some Fido.builtins.str_geb
  | _   => None
  end.

(** Fold a CONSTANT bool to its [bool], else [None] (bool VALUE lives here: [ptype] keeps [PtBool] value-less).
    SELF-SEALED: every entry (top + each recursive call) first demands [ptype e = Some PtBool], so a
    [ptype]-rejected compare (e.g. mixed-width [int64(1)==int32(1)]) returns [None], not a fabricated value — the
    precondition is enforced here, not assumed of the caller.  Reuses [ptype]'s numeric operand values
    ([const_z]) / string constants ([eval_str], the single string-value authority), recursing over the 6 numeric
    or string-constant COMPARISONs, the LOGICAL [&&]/[||]/[!], and the identity [bool(x)].  A runtime-operand or
    multi-byte-rune leaf is honestly absent ([None]). *)
Fixpoint eval_bool (e : GExpr) : option bool :=
  match ptype e with
  | Some PtBool =>   (* SEAL: fold ONLY what [ptype] validated as a bool *)
      match e with
      | EUn UNot a    => match eval_bool a with Some x => Some (negb x) | None => None end
      | EBn BLAnd a b => match eval_bool a, eval_bool b with Some x, Some y => Some (andb x y) | _, _ => None end
      | EBn BLOr  a b => match eval_bool a, eval_bool b with Some x, Some y => Some (orb  x y) | _, _ => None end
      | EBn op a b =>
          match cmp_op op, const_z a, const_z b with
          | Some cmp, Some x, Some y => Some (cmp x y)                      (* integer comparison *)
          | _, _, _ =>
          match cmp_op op, const_dy a, const_dy b with
          | Some cmp, Some da, Some db =>
              let '(x, y) := dy_align da db in Some (cmp x y)               (* float comparison — exact after alignment *)
          | _, _, _ =>
              match str_cmp_op op, eval_str a, eval_str b with
              | Some scmp, Some s, Some t => Some (scmp s t)               (* string-CONSTANT comparison (any [eval_str]-folded operand, via [str_cmp_op]) *)
              | _, _, _ =>
                  match op, eval_bool a, eval_bool b with                 (* else [==]/[!=] of two bool sub-bools *)
                  | BEq, Some x, Some y => Some (Bool.eqb x y)
                  | BNe, Some x, Some y => Some (negb (Bool.eqb x y))
                  | _, _, _ => None
                  end
              end
          end
          end
      | ECall (EId f) (a :: nil) =>                                        (* identity bool CONVERSION [bool(x)] *)
          if String.eqb (proj1_sig f) "bool" then eval_bool a else None
      | _ => None
      end
  | _ => None
  end.

(** Evaluate EVERY element of an int-slice LITERAL to its boxed value, ALL-or-[None].  Each element is gated by
    [ptype]'s OWN check ([assignable_to_ty ce t] — a wrong-typed constant like [int64(1)] in an [[]int] is
    declined exactly as [ptype] declines it; proved: [eval_int_slice_elems_forall_assignable] /
    [eval_slice_index_supported]) and must be a CONSTANT boxable to [t]: Go constructs the WHOLE literal before
    indexing, so a runtime / panicking element — even an unselected one — makes the fold [None], never a wrong
    value. *)
Fixpoint eval_int_slice_elems (t : GoTy) (es : list GExpr) : option (list GoAny) :=
  match es with
  | [] => Some []
  | el :: rest =>
      match ptype el with
      | Some ce =>
          if assignable_to_ty ce t                                          (* SEAL: [ptype]'s OWN element check — a wrong-typed const is REJECTED, as in [ptype] *)
          then match int_const_val ce with
               | Some z => match box_int t z, eval_int_slice_elems t rest with
                           | Some v, Some vs => Some (v :: vs)
                           | _, _ => None
                           end
               | None => None                                               (* runtime / non-int-const element ([PtRunInt]) -> whole literal undenoted *)
               end
          else None                                                         (* assignable-to-[t] FAILS ([int64(1)] in [[]int]) -> [ptype] rejects; so do we *)
      | None => None
      end
  end.

(** INTERNAL (core-only) ptype-driven scalar fold — NOT a float boundary and NOT directly consumable as a
    trusted denotation path: its [PtFloatConst] arm runs only the PER-NODE [fsf_checked]; the child-position
    coverage lives in [eval_value]'s [floats_checked] boundary (and [map_entries_evaluable] carries the
    boundary itself).  A numeric / string / bool CONSTANT evaluates to the model value its [ptype] category
    carries ([box_int]/[box_float] attach it, FAILING CLOSED out of range); everything else is [None]. *)
Local Definition eval_value_ptype_core (e : GExpr) : option GoAny :=
  match ptype e with
  | Some (PtIntConst z)     => box_int GTInt z                                                 (* untyped const -> default [int], range-checked *)
  | Some (PtTIntConst t z)  => box_int t z                                                     (* typed int const (conversion / typed arith) *)
  | Some (PtFloatConst t d) =>
      match fsf_checked e with                                            (* the PER-NODE agreement check; child positions are the [floats_checked] boundary's job *)
      | Some _ => box_float t (dy_m d) (dy_e d)
      | None => None
      end
  | Some PtStr              => match eval_str e with Some s => Some (anyt TString s) | None => None end  (* a string CONSTANT: literal / concatenation / string-or-rune conversion ([PtStr] carries no value; [eval_str] folds it) *)
  | Some PtBool             => match eval_bool e with Some b => Some (anyt TBool b) | None => None end   (* a CONSTANT bool: comparison / logical fold *)
  | _                       => None
  end.

(** EVALUABILITY of every entry of an integer-keyed MAP literal, ALL-or-nothing — the whole-literal
    discipline of [eval_int_slice_elems]: Go constructs the ENTIRE literal before [len], so a runtime /
    wrong-typed key or value — even one irrelevant to the queried length — declines the check, never a wrong
    verdict.  Each entry is gated by [ptype]'s OWN map-arm checks ([assignable_to_ty] on BOTH sides + an
    integer-CONSTANT key; proved ⊆ [ptype]: [eval_map_len_supported]) and must fully EVALUATE (key boxable
    to [kt]; value folded by the CONSTANT default [eval_value_ptype_core] — a supported RUNTIME value like
    [len([]int{2})] declines: absent, not wrong, [map_len_eval_absent]).  Deliberately a [bool],
    NOT a list of boxed pairs: [len] needs only "construction completes, panic-free" + the count, and a pair
    list boxed by the DEFAULT fold would carry default-typed values (a [map[int]uint8] value boxed as [int])
    — semantically misleading entries nothing may consume.  A target-typed map VALUE evaluator is future
    work (with map indexing), not smuggled in through [len]. *)
Fixpoint map_entries_evaluable (kt vt : GoTy) (kvs : list (GExpr * GExpr)) : bool :=
  match kvs with
  | [] => true
  | (k, v) :: rest =>
      match ptype k, ptype v with
      | Some ck, Some cv =>
          assignable_to_ty ck kt && assignable_to_ty cv vt
          && match int_const_val ck with
             | Some z => match box_int kt z with Some _ => true | None => false end
             | None => false
             end
          && match eval_value_ptype_core v with Some _ => true | None => false end
          && floats_checked k && floats_checked v   (* BOUNDARY-CARRYING: a laundered fold in a key or value is re-verified even if this helper is consumed outside [eval_value] *)
          && map_entries_evaluable kt vt rest
      | _, _ => false
      end
  end.

(** Evaluate a value expr to the model's [GoAny], else [None].  FAITHFUL: the ptype-driven arm folds a numeric /
    string / bool constant ([ptype] → VALUE+TYPE, [box_int]/[box_float] attach the model value, FAILING CLOSED
    out of range); a separate [EIndex (ESliceLit..)] arm folds a CONSTANT in-bounds int-slice index by
    evaluating the WHOLE literal ([eval_int_slice_elems] — ALL elements, so a runtime/panicking/out-of-range
    element rejects it) and indexing.  Its accept-boundary is [ptype]'s OWN — elements gated by
    [assignable_to_ty] and the constant index by [(0<=?k) && int_const_repr k GTInt], the SAME checks [ptype]'s
    slice arm uses — so the arm accepts NO expression [ptype] rejects (proved: [eval_slice_index_supported]); it
    is a SUBSET, not a second, looser classifier.  Scalar coverage exercised — the [eval_value_good] table (gated by [eval_value_good_ok]) folds:
    integer constants (conversions / in-range [uint] via [mk_uint] / arithmetic / complement, EXCLUDING
    platform-[uint] complement), exact-DYADIC FLOAT constants (fractional arithmetic included), string constants ([eval_str]), and constant
    bools ([eval_bool]); slice-index folds pinned by [slice_index_*] below; [len] of a fully-evaluable int-slice
    literal folds to its length ([eval_len_reduces]) and [len] of a fully-evaluable integer-keyed MAP literal to
    its entry count ([eval_map_len_reduces] — under the gate's OWN conditions, [goty_supported] value type +
    [nodup_z]-distinct constant keys, so the count IS Go's [len]).  ABSENT ([None], honestly): [len] of a literal with runtime ELEMENTS or of a map literal with a
    runtime VALUE, runtime operands ([int(x)] of a runtime [x], runtime comparisons), OOB / runtime slice INDEX,
    out-of-range or COMPLEMENTED [uint], a rounding (non-exact) float op, multi-byte-rune — never wrong. *)
Local Definition eval_value_core (e : GExpr) : option GoAny :=
  match e with
  | EIndex (ESliceLit t es) idx =>
      (* CONSTANT in-bounds index into an INT-slice literal -> the k-th element.  The WHOLE literal is evaluated
         first ([eval_int_slice_elems] — Go builds the literal before indexing, so a runtime/panicking/malformed
         element, even unselected, declines the fold), then the boxed value list is indexed ([nth_error]: OOB ->
         [None]; a runtime index has [int_const_val = None]).  [ptype] still classifies the whole [PtRunInt]. *)
      if is_int_goty t
      then match ptype idx with
           | Some ci =>
               match int_const_val ci with
               | Some k => if (0 <=? k)%Z && int_const_repr k GTInt                          (* [ptype]'s OWN constant-index boundary: nonneg + int-representable (conservative 32-bit) *)
                           then match eval_int_slice_elems t es with
                                | Some vs => nth_error vs (Z.to_nat k)                         (* IN-BOUNDS -> the k-th value; OOB -> None *)
                                | None => None                                                (* a runtime/panicking element -> undenoted *)
                                end
                           else None                                                          (* negative, or non-int-representable (unsupported), constant *)
               | None => None                                                                 (* runtime index (B3) *)
               end
           | None => None
           end
      else None
  | ECall (EId f) (ESliceLit t es :: nil) =>
      (* [len] of a FULLY-EVALUABLE int-slice LITERAL folds to its length, boxed as Go's [int] ([box_int GTInt]
         — range-checked, fail-closed).  Go evaluates the literal (ALL elements) before [len], so a
         runtime/panicking element declines the fold ([eval_int_slice_elems] — same whole-literal discipline as
         the index arm; [ptype] still classifies the call [PtRunInt GTInt], like the index).  [len] of a STRING
         literal already folds via [ptype] ([PtIntConst]); [len] of a non-int-element slice stays honestly
         absent ([len] of a fully-evaluable MAP literal folds in its OWN arm below).  Any OTHER call with a
         slice-literal argument falls through to the ptype-driven default unchanged. *)
      if String.eqb (proj1_sig f) "len" && is_int_goty t
      then match eval_int_slice_elems t es with
           | Some vs => box_int GTInt (Z.of_nat (length vs))
           | None => None
           end
      else eval_value_ptype_core e
  | ECall (EId f) (EMapLit kt vt kvs :: nil) =>
      (* [len] of a FULLY-EVALUABLE integer-keyed MAP literal folds to its entry count, boxed as Go's [int].
         Go constructs the literal (ALL keys and values) before [len], so a runtime / wrong-typed key or value
         declines the fold ([map_entries_evaluable] — the whole-literal discipline).  The arm carries the
         GATE's OWN side conditions — [goty_supported vt] (an invalid nested map-key type like
         [map[int]map[[]int]int{}] must NEVER receive behavior, even empty) and the [nodup_z] distinctness
         check ([map_key_vals], [ptype]'s own key list) without which a duplicate-key literal (invalid Go)
         would fold [length kvs], which is NOT the map's [len].  [ptype] still classifies the call
         [PtRunInt GTInt] (a map is not a constant).  Any OTHER call with a map-literal argument falls
         through to the ptype-driven default unchanged. *)
      if String.eqb (proj1_sig f) "len" && is_int_goty kt && goty_supported vt
         && nodup_z (map_key_vals kvs) && map_entries_evaluable kt vt kvs
      then box_int GTInt (Z.of_nat (length kvs))
      else eval_value_ptype_core e
  | _ => eval_value_ptype_core e
  end.

(** [eval_value] = the float boundary, ONCE, then the evaluator core.  Every value consumer
    ([denote_expr]/[eval_args]/[folded_arg]/the statement layer) enters here, so the boundary covers
    slice elements, map entries, comparison operands, and conversion sources uniformly — no per-consumer
    validators. *)
Definition eval_value (e : GExpr) : option GoAny :=
  if floats_checked e then eval_value_core e else None.

(** The structural SEAL: a denoted value implies the whole expression passed the float boundary — every
    [PtFloatConst] subexpression, at any depth, was re-verified against the CONSTANT-fold layer
    ([sf_const_binop]/[sf_const_neg]). *)
Theorem eval_value_floats_checked : forall e v, eval_value e = Some v -> floats_checked e = true.
Proof.
  intros e v H. unfold eval_value in H.
  destruct (floats_checked e); [reflexivity | discriminate H].
Qed.

(** ---- EFFECTFUL expression denotation + the RUNTIME-value tier (R1–R8; this section is the live
    authority — the surfaces bundle its theorems).  Supported programs are CLOSED, so runtime integer
    values are DETERMINED.  [reval_int] evaluates the [GTInt] fragment with the MODEL'S OWN ops on the
    model's own carrier; constants enter through [eval_value] (the single fold authority) via the
    checked [unbox_int]; [/]/[%] are the evidence-carrying [int_div]/[int_mod] (nonzero proof from the
    guarding test; a determined zero divisor panics [rt_div_zero]).  [RPanic] = a determined runtime
    panic; [None] = absent (never wrong).  Per-arm semantics are documented at each arm. *)
Definition unbox_int (v : GoAny) : option GoInt :=
  match v with
  | existT _ _ (pair x tag) =>
      match tag in GoTypeTag A return A -> option GoInt with
      | TInt64 => fun x0 => Some x0
      | _ => fun _ => None
      end x
  end.
Inductive RRes : Type := RVal (v : GoInt) | RPanic (p : GoAny).
(** The CHECKED length result — through [box_int] (the ONE fail-closed [GTInt] builder: a length outside
    Fido's conservative range DECLINES, never wraps) and the sealed [unbox_int]; no raw [intwrap] of a
    source-derived length anywhere in the tier. *)
Definition rval_len (n : nat) : option RRes :=
  match box_int GTInt (Z.of_nat n) with
  | Some v => match unbox_int v with Some x => Some (RVal x) | None => None end
  | None => None
  end.
(** A representable count boxes to EXACTLY the wrapped length — the discharge lemma for the tier's
    [rval_len] side conditions (a count outside the conservative window declines, fail-closed). *)
Lemma rval_len_repr : forall n,
  int_const_repr (Z.of_nat n) GTInt = true ->
  rval_len n = Some (RVal (intwrap (Z.of_nat n))).
Proof. intros n H. unfold rval_len, box_int. rewrite H. reflexivity. Qed.
(** Element CONSTRUCTION for the runtime tier — evaluate every element of an int-slice literal
    left-to-right through [rec] (instantiated with [reval_int]): all values, or the FIRST panicking
    element (aborting construction — the verified go-run order), or [None] (absent).  Parametrized (the
    [fsf_operand_with] pattern) so the Fixpoint below can use it mid-definition and theorems can name the
    instance [reval_elems]. *)
Inductive RElems : Type := REVals (vs : list GoInt) | REPanic (p : GoAny).
Definition reval_elems_with (rec : GExpr -> option RRes) : list GExpr -> option RElems :=
  fix go (l : list GExpr) : option RElems :=
    match l with
    | nil => Some (REVals nil)
    | x :: r =>
        match rec x with
        | Some (RVal v) =>
            match go r with
            | Some (REVals vs) => Some (REVals (v :: vs))
            | other => other
            end
        | Some (RPanic p) => Some (REPanic p)
        | None => None
        end
    end.
(** Tier R3 EXIT boxing — a width conversion OUT of the [GTInt] runtime fragment, computed with the
    MODEL'S OWN per-width wrap (Go's runtime conversion TRUNCATES mod 2^w — the wraps ARE that
    semantics; the SAME wraps [box_int] renders constants with, minus its constant-range gate, which
    would be WRONG here: Go does not reject an out-of-range runtime conversion, it wraps).  [GTInt] is
    deliberately [None]: the same-width [int(x)] lives INSIDE [reval_int] (one authority per target).
    Non-integer targets are unreachable under the caller's [PtRunInt] guard; defensive [None]. *)
Definition wrap_runint (t : GoTy) (z : Z) : option GoAny :=
  match t with
  | GTInt64 => Some (anyt TI64  (i64wrap z))
  | GTU8    => Some (anyt TU8   (u8wrap  z))
  | GTI8    => Some (anyt TI8   (i8wrap  z))
  | GTU16   => Some (anyt TU16  (u16wrap z))
  | GTI16   => Some (anyt TI16  (i16wrap z))
  | GTU32   => Some (anyt TU32  (u32wrap z))
  | GTI32   => Some (anyt TI32  (i32wrap z))
  | GTU64   => Some (anyt TU64  (u64wrap z))
  | GTUint  => Some (anyt TUint (uintwrap z))
  | _       => None
  end.

(** Tier T2 raw READING — the mathematical value a boxed integer carrier represents (a signed carrier
    reads signed, an unsigned one nonnegative).  Go's integer conversion converts the VALUE — "sign
    extended to implicit infinite precision; otherwise ... zero extended", then truncated (spec,
    Conversions) — which is exactly read-then-[wrap_runint]: sign/zero extension IS the carrier's raw
    value.  A non-integer tag is [None] (fail-closed: a bool/string/float-tagged source never
    converts here). *)
Definition runint_raw (g : GoAny) : option Z :=
  match g with
  | existT _ _ (pair x tag) =>
      match tag in GoTypeTag A return A -> option Z with
      | TInt64 => fun v => Some (intraw v)  | TUint => fun v => Some (uintraw v)
      | TU8    => fun v => Some (u8raw v)   | TI8   => fun v => Some (i8raw v)
      | TU16   => fun v => Some (u16raw v)  | TI16  => fun v => Some (i16raw v)
      | TU32   => fun v => Some (u32raw v)  | TI32  => fun v => Some (i32raw v)
      | TI64   => fun v => Some (i64raw v)  | TU64  => fun v => Some (u64raw v)
      | _      => fun _ => None
      end x
  end.

(** Tier R4 comparison dispatch — the verdict function per comparison [BinOp], built ONLY from the
    model's own [int_eqb]/[int_ltb]/[int_leb] ([!=] is the negation of [==]; [>]/[>=] are the argument
    swap — Go's exact [int] comparison semantics).  [None] = not a comparison ([&&]/[||] operate on
    BOOLS, never the int fragment; arithmetic never yields the bool exit). *)
Definition cmp_verdict (o : BinOp) : option (GoInt -> GoInt -> bool) :=
  match o with
  | BEq => Some int_eqb
  | BNe => Some (fun x y => negb (int_eqb x y))
  | BLt => Some int_ltb
  | BLe => Some int_leb
  | BGt => Some (fun x y => int_ltb y x)
  | BGe => Some (fun x y => int_leb y x)
  | _ => None
  end.

(** ---- THE SHARED VALUE EVALUATOR (one authority — no per-consumer drift) ----
    [RAny] is the full-typed runtime result ([GoAny] value or panic).  [rexit_with] is THE one spelling
    of the fragment EXITS — the R3 width conversion and the R4 bool comparison — parametrized over the
    int-fragment engine (the [fsf_operand_with] pattern) so [reval_int]'s map arm and [denote_expr]
    consume literally the same code.  [reval_val_with] is the whole value pipeline: the constant fold,
    then the [GTInt] fragment (boxed [TInt64]), then the exits. *)
Inductive RAny : Type := RAVal (g : GoAny) | RAPanic (p : GoAny).
(** Tier T1 typed-unary dispatch — the per-width MODEL op for a unary op at a non-GTInt integer
    width, on the boxed carrier (the [unbox_int] tag-convoy pattern per width).  [^] covers all eight
    fixed widths; [-] only [i64]/[u64] (no narrow-neg model ops); [GTUint] has NO ops — every hole is
    an explicit [None] (absent); the matrix is sealed below: [typed_unop_tag_exact] + the qualified branch pins + the COMPLETE hole theorem [typed_unop_holes_none]. *)
Definition typed_unop (o : UnaryOp) (t : GoTy) (g : GoAny) : option GoAny :=
  match g with
  | existT _ _ (pair x tag) =>
      match o, t with
      | UXor, GTU8    => match tag in GoTypeTag A return A -> option GoAny with
                         | TU8  => fun v => Some (anyt TU8  (u8_not v))  | _ => fun _ => None end x
      | UXor, GTI8    => match tag in GoTypeTag A return A -> option GoAny with
                         | TI8  => fun v => Some (anyt TI8  (i8_not v))  | _ => fun _ => None end x
      | UXor, GTU16   => match tag in GoTypeTag A return A -> option GoAny with
                         | TU16 => fun v => Some (anyt TU16 (u16_not v)) | _ => fun _ => None end x
      | UXor, GTI16   => match tag in GoTypeTag A return A -> option GoAny with
                         | TI16 => fun v => Some (anyt TI16 (i16_not v)) | _ => fun _ => None end x
      | UXor, GTU32   => match tag in GoTypeTag A return A -> option GoAny with
                         | TU32 => fun v => Some (anyt TU32 (u32_not v)) | _ => fun _ => None end x
      | UXor, GTI32   => match tag in GoTypeTag A return A -> option GoAny with
                         | TI32 => fun v => Some (anyt TI32 (i32_not v)) | _ => fun _ => None end x
      | UXor, GTInt64 => match tag in GoTypeTag A return A -> option GoAny with
                         | TI64 => fun v => Some (anyt TI64 (i64_not v)) | _ => fun _ => None end x
      | UXor, GTU64   => match tag in GoTypeTag A return A -> option GoAny with
                         | TU64 => fun v => Some (anyt TU64 (u64_not v)) | _ => fun _ => None end x
      | UNeg, GTInt64 => match tag in GoTypeTag A return A -> option GoAny with
                         | TI64 => fun v => Some (anyt TI64 (i64_neg v)) | _ => fun _ => None end x
      | UNeg, GTU64   => match tag in GoTypeTag A return A -> option GoAny with
                         | TU64 => fun v => Some (anyt TU64 (u64_neg v)) | _ => fun _ => None end x
      | _, _ => None
      end
  end.

(** The tag↔width matcher — the SPEC [typed_unop]'s matrix is sealed against. *)
Definition tag_matches (t : GoTy) (g : GoAny) : bool :=
  match g with
  | existT _ _ (pair _ tag) =>
      match t, tag with
      | GTInt, TInt64 | GTInt64, TI64 | GTU8, TU8 | GTI8, TI8 | GTU16, TU16 | GTI16, TI16
      | GTU32, TU32 | GTI32, TI32 | GTU64, TU64 | GTUint, TUint => true
      | _, _ => false
      end
  end.
(** MATRIX SOUNDNESS: a [Some] result arises ONLY from a payload whose tag matches the width — a
    mismatched-tag payload can never be operated on wrongly — and the RESULT carries the same width's
    tag (consumed by the well-taggedness invariant below). *)
Lemma typed_unop_tag_exact : forall o t g r,
  typed_unop o t g = Some r -> tag_matches t g = true /\ tag_matches t r = true.
Proof.
  intros o t g r H. destruct g as [A [x tag]].
  destruct o; destruct t; cbn in H; try discriminate H;
    destruct tag; try discriminate H;
    injection H as <-; split; reflexivity.
Qed.
(** MATRIX TOTALITY on the live cells: a MATCHING tag always computes (with the holes' complement,
    every [(o, t, tag)] cell is decided — live → the model op; anything else → [None]). *)
Lemma typed_unop_live_total : forall o t g,
  tag_matches t g = true ->
  ((o = UXor /\ is_int_goty t = true /\ numty_eqb t GTInt = false /\ numty_eqb t GTUint = false)
   \/ (o = UNeg /\ (t = GTInt64 \/ t = GTU64))) ->
  exists r, typed_unop o t g = Some r.
Proof.
  intros o t g Hm Hlive. destruct g as [A [x tag]].
  destruct Hlive as [[-> [Hi [Ht Hu]]] | [-> [-> | ->]]].
  - destruct t; try discriminate Hi; try discriminate Ht; try discriminate Hu;
      destruct tag; try discriminate Hm; eexists; reflexivity.
  - destruct tag; try discriminate Hm; eexists; reflexivity.
  - destruct tag; try discriminate Hm; eexists; reflexivity.
Qed.

(** ---- Tier T3 — SAME-WIDTH typed BINARY dispatch ----
    The nine arithmetic/bitwise ops on a non-[GTInt] fixed-width carrier pair (comparisons are the R4
    [PtBool] exit; shifts are HETEROGENEOUS — the T5 dispatch below).  [GTUint] has NO model ops — a hole row
    ([typed_binop_uint_none]); [GTInt] lives in [reval_int]'s own arm ([typed_binop_gtint_none]). *)
Definition typed_arith_op (o : BinOp) : bool :=
  match o with
  | BAdd | BSub | BMul | BDiv | BRem | BAnd | BOr | BXor | BAndNot => true
  | _ => false
  end.

(** The evidence-carrying DIVISION/REMAINDER convoy, factored ONCE over a width's (tag, raw, op)
    triple: a raw-ZERO divisor is Go's runtime panic ([rt_div_zero]); a nonzero one produces the
    MODEL op's value with the very test as its evidence (rule 4 — the R6 convoy, made generic). *)
Definition div_checked {A : Type} (tag : GoTypeTag A) (raw : A -> Z)
    (op : forall a b : A, Z.eqb (raw b) 0 = false -> A) (a b : A) : RAny :=
  (match Z.eqb (raw b) 0 as z return Z.eqb (raw b) 0 = z -> RAny with
   | true  => fun _  => RAPanic rt_div_zero
   | false => fun pf => RAVal (anyt tag (op a b pf))
   end) eq_refl.
Lemma div_checked_cases : forall (A : Type) (tag : GoTypeTag A) raw op (a b : A),
  div_checked tag raw op a b = RAPanic rt_div_zero
  \/ exists pf, div_checked tag raw op a b = RAVal (anyt tag (op a b pf)).
Proof.
  intros A tag raw op a b. unfold div_checked.
  assert (K : forall z (pf : Z.eqb (raw b) 0 = z),
      (match z as z0 return Z.eqb (raw b) 0 = z0 -> RAny with
       | true  => fun _   => RAPanic rt_div_zero
       | false => fun pf0 => RAVal (anyt tag (op a b pf0))
       end) pf = RAPanic rt_div_zero
      \/ exists pf1, (match z as z0 return Z.eqb (raw b) 0 = z0 -> RAny with
          | true  => fun _   => RAPanic rt_div_zero
          | false => fun pf0 => RAVal (anyt tag (op a b pf0))
          end) pf = RAVal (anyt tag (op a b pf1))).
  { intros z pf. destruct z; [left; reflexivity | right; exists pf; reflexivity]. }
  exact (K _ eq_refl).
Qed.
Lemma div_checked_zero : forall (A : Type) (tag : GoTypeTag A) raw op (a b : A),
  Z.eqb (raw b) 0 = true -> div_checked tag raw op a b = RAPanic rt_div_zero.
Proof.
  intros A tag raw op a b Hz. unfold div_checked.
  assert (K : forall z (pf : Z.eqb (raw b) 0 = z), z = true ->
      (match z as z0 return Z.eqb (raw b) 0 = z0 -> RAny with
       | true  => fun _   => RAPanic rt_div_zero
       | false => fun pf0 => RAVal (anyt tag (op a b pf0))
       end) pf = RAPanic rt_div_zero).
  { intros z pf Hzt. destruct z; [reflexivity | discriminate Hzt]. }
  exact (K _ eq_refl Hz).
Qed.
Lemma div_checked_nonzero : forall (A : Type) (tag : GoTypeTag A) raw op (a b : A),
  Z.eqb (raw b) 0 = false ->
  exists pf, div_checked tag raw op a b = RAVal (anyt tag (op a b pf)).
Proof.
  intros A tag raw op a b Hz.
  destruct (div_checked_cases A tag raw op a b) as [Ep | Ev]; [|exact Ev].
  exfalso. unfold div_checked in Ep.
  assert (K : forall z (pf : Z.eqb (raw b) 0 = z), z = false ->
      (match z as z0 return Z.eqb (raw b) 0 = z0 -> RAny with
       | true  => fun _   => RAPanic rt_div_zero
       | false => fun pf0 => RAVal (anyt tag (op a b pf0))
       end) pf = RAPanic rt_div_zero -> False).
  { intros z pf Hzf Hp. destruct z; [discriminate Hzf | discriminate Hp]. }
  exact (K _ eq_refl Hz Ep).
Qed.

Definition typed_binop (o : BinOp) (t : GoTy) (ga gb : GoAny) : option RAny :=
  if typed_arith_op o then
    match t with
    | GTU8 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU8 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TU8 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TU8 (u8_add va vb)))
                    | BSub => Some (RAVal (anyt TU8 (u8_sub va vb)))
                    | BMul => Some (RAVal (anyt TU8 (u8_mul va vb)))
                    | BDiv => Some (div_checked TU8 u8raw u8_div va vb)
                    | BRem => Some (div_checked TU8 u8raw u8_mod va vb)
                    | BAnd => Some (RAVal (anyt TU8 (u8_and va vb)))
                    | BOr  => Some (RAVal (anyt TU8 (u8_or  va vb)))
                    | BXor => Some (RAVal (anyt TU8 (u8_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TU8 (u8_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTI8 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI8 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TI8 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TI8 (i8_add va vb)))
                    | BSub => Some (RAVal (anyt TI8 (i8_sub va vb)))
                    | BMul => Some (RAVal (anyt TI8 (i8_mul va vb)))
                    | BDiv => Some (div_checked TI8 i8raw i8_div va vb)
                    | BRem => Some (div_checked TI8 i8raw i8_mod va vb)
                    | BAnd => Some (RAVal (anyt TI8 (i8_and va vb)))
                    | BOr  => Some (RAVal (anyt TI8 (i8_or  va vb)))
                    | BXor => Some (RAVal (anyt TI8 (i8_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TI8 (i8_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTU16 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU16 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TU16 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TU16 (u16_add va vb)))
                    | BSub => Some (RAVal (anyt TU16 (u16_sub va vb)))
                    | BMul => Some (RAVal (anyt TU16 (u16_mul va vb)))
                    | BDiv => Some (div_checked TU16 u16raw u16_div va vb)
                    | BRem => Some (div_checked TU16 u16raw u16_mod va vb)
                    | BAnd => Some (RAVal (anyt TU16 (u16_and va vb)))
                    | BOr  => Some (RAVal (anyt TU16 (u16_or  va vb)))
                    | BXor => Some (RAVal (anyt TU16 (u16_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TU16 (u16_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTI16 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI16 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TI16 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TI16 (i16_add va vb)))
                    | BSub => Some (RAVal (anyt TI16 (i16_sub va vb)))
                    | BMul => Some (RAVal (anyt TI16 (i16_mul va vb)))
                    | BDiv => Some (div_checked TI16 i16raw i16_div va vb)
                    | BRem => Some (div_checked TI16 i16raw i16_mod va vb)
                    | BAnd => Some (RAVal (anyt TI16 (i16_and va vb)))
                    | BOr  => Some (RAVal (anyt TI16 (i16_or  va vb)))
                    | BXor => Some (RAVal (anyt TI16 (i16_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TI16 (i16_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTU32 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU32 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TU32 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TU32 (u32_add va vb)))
                    | BSub => Some (RAVal (anyt TU32 (u32_sub va vb)))
                    | BMul => Some (RAVal (anyt TU32 (u32_mul va vb)))
                    | BDiv => Some (div_checked TU32 u32raw u32_div va vb)
                    | BRem => Some (div_checked TU32 u32raw u32_mod va vb)
                    | BAnd => Some (RAVal (anyt TU32 (u32_and va vb)))
                    | BOr  => Some (RAVal (anyt TU32 (u32_or  va vb)))
                    | BXor => Some (RAVal (anyt TU32 (u32_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TU32 (u32_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTI32 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI32 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TI32 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TI32 (i32_add va vb)))
                    | BSub => Some (RAVal (anyt TI32 (i32_sub va vb)))
                    | BMul => Some (RAVal (anyt TI32 (i32_mul va vb)))
                    | BDiv => Some (div_checked TI32 i32raw i32_div va vb)
                    | BRem => Some (div_checked TI32 i32raw i32_mod va vb)
                    | BAnd => Some (RAVal (anyt TI32 (i32_and va vb)))
                    | BOr  => Some (RAVal (anyt TI32 (i32_or  va vb)))
                    | BXor => Some (RAVal (anyt TI32 (i32_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TI32 (i32_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTInt64 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI64 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TI64 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TI64 (i64_add va vb)))
                    | BSub => Some (RAVal (anyt TI64 (i64_sub va vb)))
                    | BMul => Some (RAVal (anyt TI64 (i64_mul va vb)))
                    | BDiv => Some (div_checked TI64 i64raw i64_div va vb)
                    | BRem => Some (div_checked TI64 i64raw i64_mod va vb)
                    | BAnd => Some (RAVal (anyt TI64 (i64_and va vb)))
                    | BOr  => Some (RAVal (anyt TI64 (i64_or  va vb)))
                    | BXor => Some (RAVal (anyt TI64 (i64_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TI64 (i64_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTU64 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU64 => fun va =>
                match tagb in GoTypeTag B return B -> option RAny with
                | TU64 => fun vb =>
                    match o with
                    | BAdd => Some (RAVal (anyt TU64 (u64_add va vb)))
                    | BSub => Some (RAVal (anyt TU64 (u64_sub va vb)))
                    | BMul => Some (RAVal (anyt TU64 (u64_mul va vb)))
                    | BDiv => Some (div_checked TU64 u64raw u64_div va vb)
                    | BRem => Some (div_checked TU64 u64raw u64_mod va vb)
                    | BAnd => Some (RAVal (anyt TU64 (u64_and va vb)))
                    | BOr  => Some (RAVal (anyt TU64 (u64_or  va vb)))
                    | BXor => Some (RAVal (anyt TU64 (u64_xor va vb)))
                    | BAndNot => Some (RAVal (anyt TU64 (u64_andnot va vb)))
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | _ => None
    end
  else None.

(** MATRIX SOUNDNESS: a value result arises ONLY from a matched-tag pair, and carries the width's
    tag (consumed by the well-taggedness invariant). *)
Lemma typed_binop_tag_exact : forall o t ga gb g,
  typed_binop o t ga gb = Some (RAVal g) ->
  tag_matches t ga = true /\ tag_matches t gb = true /\ tag_matches t g = true.
Proof.
  intros o t [A [xa taga]] [B [xb tagb]] g H.
  unfold typed_binop in H.
  destruct o; cbv beta iota delta [typed_arith_op] in H; try discriminate H;
  destruct t; cbv beta iota in H; try discriminate H;
  destruct taga; cbv beta iota in H; try discriminate H;
  destruct tagb; cbv beta iota in H; try discriminate H;
  first
    [ (injection H as <-; repeat split; reflexivity)
    | (injection H as He;
       edestruct div_checked_cases as [Ep | [pf Ev]];
       [ rewrite Ep in He; discriminate He
       | rewrite Ev in He; injection He as <-; repeat split; reflexivity ]) ].
Qed.
(** The ONLY panic the table produces is the division-by-zero panic, from [/] or [%]. *)
Lemma typed_binop_panic_div : forall o t ga gb p,
  typed_binop o t ga gb = Some (RAPanic p) ->
  p = rt_div_zero /\ (o = BDiv \/ o = BRem).
Proof.
  intros o t [A [xa taga]] [B [xb tagb]] p H.
  unfold typed_binop in H.
  destruct o; cbv beta iota delta [typed_arith_op] in H; try discriminate H;
  destruct t; cbv beta iota in H; try discriminate H;
  destruct taga; cbv beta iota in H; try discriminate H;
  destruct tagb; cbv beta iota in H; try discriminate H;
  first
    [ discriminate H
    | (injection H as He;
       edestruct div_checked_cases as [Ep | [pf Ev]];
       [ rewrite Ep in He; injection He as <-; split; [reflexivity | auto]
       | rewrite Ev in He; discriminate He ]) ].
Qed.
(** MATRIX TOTALITY on the live rows: matching tags at a fixed non-[GTInt]/non-[GTUint] width always
    compute — a value or the division panic, never a silent hole. *)
Lemma typed_binop_live_total : forall o t ga gb,
  typed_arith_op o = true ->
  tag_matches t ga = true -> tag_matches t gb = true ->
  numty_eqb t GTInt = false -> numty_eqb t GTUint = false -> is_int_goty t = true ->
  exists r, typed_binop o t ga gb = Some r.
Proof.
  intros o t [A [xa taga]] [B [xb tagb]] Ho Ha Hb Hgi Hgu Hi.
  destruct o; try discriminate Ho;
  destruct t; try discriminate Hi; try discriminate Hgi; try discriminate Hgu;
  destruct taga; try discriminate Ha;
  destruct tagb; try discriminate Hb;
  eexists; reflexivity.
Qed.
(** The hole rows, each [None] for EVERY payload pair: non-arith ops (shifts/comparisons/logicals),
    the [GTInt] row (the engine's own arm), the op-less [GTUint] row, and non-integer widths. *)
Lemma typed_binop_nonarith_none : forall o t ga gb,
  typed_arith_op o = false -> typed_binop o t ga gb = None.
Proof. intros o t ga gb H. unfold typed_binop. rewrite H. reflexivity. Qed.
Lemma typed_binop_gtint_none : forall o ga gb, typed_binop o GTInt ga gb = None.
Proof. intros o ga gb. unfold typed_binop. destruct (typed_arith_op o); reflexivity. Qed.
Lemma typed_binop_uint_none : forall o ga gb, typed_binop o GTUint ga gb = None.
Proof. intros o ga gb. unfold typed_binop. destruct (typed_arith_op o); reflexivity. Qed.
Lemma typed_binop_nonint_none : forall o t ga gb,
  is_int_goty t = false -> typed_binop o t ga gb = None.
Proof.
  intros o t ga gb H. unfold typed_binop.
  destruct (typed_arith_op o); [destruct t; try discriminate H; reflexivity | reflexivity].
Qed.

(** T3 operand MATERIALIZATION — Go's mixed-operand rule, WIDTH-SEALED at this boundary (not by
    caller discipline): a RUNTIME operand must be classified AT the width and evaluates at full
    power ([rv]); an UNTYPED int constant CONVERTS to the width through [box_int]'s repr-gated
    boxing; a TYPED constant must already BE the width ([numty_eqb] — Go forbids a typed [uint8]
    constant as an [int64] operand; cross-width is [None], pinned
    [typed_operand_cross_width_none]).  Anything else is absent fail-closed; a constant never
    panics ([typed_operand_panic_runtime]). *)
Definition typed_operand (rv : GExpr -> option RAny) (t : GoTy) (e : GExpr) : option RAny :=
  match ptype e with
  | Some (PtRunInt s) => if numty_eqb s t then rv e else None
  | Some (PtIntConst z) =>
      match box_int t z with
      | Some g => Some (RAVal g)
      | None => None
      end
  | Some (PtTIntConst s z) =>
      if numty_eqb s t
      then match box_int t z with
           | Some g => Some (RAVal g)
           | None => None
           end
      else None
  | _ => None
  end.
Lemma numty_eqb_refl_int : forall t, is_int_goty t = true -> numty_eqb t t = true.
Proof. intros t H; destruct t; try discriminate H; reflexivity. Qed.
Lemma box_int_repr_total : forall t z,
  is_int_goty t = true -> numty_eqb t GTUint = false -> int_const_repr z t = true ->
  exists g, box_int t z = Some g.
Proof.
  intros t z Hi Hu Hr. unfold box_int. rewrite Hr.
  destruct t; try discriminate Hi; try discriminate Hu; eexists; reflexivity.
Qed.
(** ---- Tier T4 — SAME-WIDTH typed COMPARISON dispatch ----
    The six comparison ops on a non-[GTInt] fixed-width carrier pair, each row the width's own MODEL
    op ([*_eqb/neqb/ltb/leb/gtb/geb] — the derived ops are model Definitions, pinned per width).
    Comparisons never panic; [GTUint] is a hole row; [GTInt] lives in the R4 engine path. *)
Definition cmp_binop (o : BinOp) : bool :=
  match o with BEq | BNe | BLt | BLe | BGt | BGe => true | _ => false end.
Definition typed_cmp (o : BinOp) (t : GoTy) (ga gb : GoAny) : option bool :=
  if cmp_binop o then
    match t with
    | GTU8 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TU8 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TU8 => fun vb =>
                    match o with
                    | BEq => Some (u8_eqb va vb)
                    | BNe => Some (u8_neqb va vb)
                    | BLt => Some (u8_ltb va vb)
                    | BLe => Some (u8_leb va vb)
                    | BGt => Some (u8_gtb va vb)
                    | BGe => Some (u8_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTI8 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TI8 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TI8 => fun vb =>
                    match o with
                    | BEq => Some (i8_eqb va vb)
                    | BNe => Some (i8_neqb va vb)
                    | BLt => Some (i8_ltb va vb)
                    | BLe => Some (i8_leb va vb)
                    | BGt => Some (i8_gtb va vb)
                    | BGe => Some (i8_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTU16 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TU16 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TU16 => fun vb =>
                    match o with
                    | BEq => Some (u16_eqb va vb)
                    | BNe => Some (u16_neqb va vb)
                    | BLt => Some (u16_ltb va vb)
                    | BLe => Some (u16_leb va vb)
                    | BGt => Some (u16_gtb va vb)
                    | BGe => Some (u16_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTI16 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TI16 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TI16 => fun vb =>
                    match o with
                    | BEq => Some (i16_eqb va vb)
                    | BNe => Some (i16_neqb va vb)
                    | BLt => Some (i16_ltb va vb)
                    | BLe => Some (i16_leb va vb)
                    | BGt => Some (i16_gtb va vb)
                    | BGe => Some (i16_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTU32 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TU32 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TU32 => fun vb =>
                    match o with
                    | BEq => Some (u32_eqb va vb)
                    | BNe => Some (u32_neqb va vb)
                    | BLt => Some (u32_ltb va vb)
                    | BLe => Some (u32_leb va vb)
                    | BGt => Some (u32_gtb va vb)
                    | BGe => Some (u32_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTI32 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TI32 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TI32 => fun vb =>
                    match o with
                    | BEq => Some (i32_eqb va vb)
                    | BNe => Some (i32_neqb va vb)
                    | BLt => Some (i32_ltb va vb)
                    | BLe => Some (i32_leb va vb)
                    | BGt => Some (i32_gtb va vb)
                    | BGe => Some (i32_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTInt64 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TI64 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TI64 => fun vb =>
                    match o with
                    | BEq => Some (i64_eqb va vb)
                    | BNe => Some (i64_neqb va vb)
                    | BLt => Some (i64_ltb va vb)
                    | BLe => Some (i64_leb va vb)
                    | BGt => Some (i64_gtb va vb)
                    | BGe => Some (i64_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | GTU64 =>
        match ga, gb with
        | existT _ _ (pair xa taga), existT _ _ (pair xb tagb) =>
            match taga in GoTypeTag A return A -> option bool with
            | TU64 => fun va =>
                match tagb in GoTypeTag B return B -> option bool with
                | TU64 => fun vb =>
                    match o with
                    | BEq => Some (u64_eqb va vb)
                    | BNe => Some (u64_neqb va vb)
                    | BLt => Some (u64_ltb va vb)
                    | BLe => Some (u64_leb va vb)
                    | BGt => Some (u64_gtb va vb)
                    | BGe => Some (u64_geb va vb)
                    | _ => None
                    end
                | _ => fun _ => None
                end xb
            | _ => fun _ => None
            end xa
        end
    | _ => None
    end
  else None.
(** The COMPARISON WIDTH — the runtime operand pins it; two int CONSTANTS fall back to the [GTInt]
    engine (Go's untyped default — where today's fold/engine already decide them); anything else
    (floats, bools, strings) is [None] here. *)
Definition cmp_width (ca cb : option PTy) : option GoTy :=
  match ca, cb with
  | Some (PtRunInt s), _ => Some s
  | _, Some (PtRunInt s) => Some s
  | Some ca', Some cb' =>
      match int_const_val ca', int_const_val cb' with
      | Some _, Some _ => Some GTInt
      | _, _ => None
      end
  | _, _ => None
  end.
(** MATRIX SOUNDNESS/TOTALITY/HOLES — the [typed_binop] seal set, comparison edition. *)
Lemma typed_cmp_tag_exact : forall o t ga gb v,
  typed_cmp o t ga gb = Some v ->
  tag_matches t ga = true /\ tag_matches t gb = true.
Proof.
  intros o t [A [xa taga]] [B [xb tagb]] v H.
  unfold typed_cmp in H.
  destruct o; cbv beta iota delta [cmp_binop] in H; try discriminate H;
  destruct t; cbv beta iota in H; try discriminate H;
  destruct taga; cbv beta iota in H; try discriminate H;
  destruct tagb; cbv beta iota in H; try discriminate H;
  split; reflexivity.
Qed.
Lemma typed_cmp_live_total : forall o t ga gb,
  cmp_binop o = true ->
  tag_matches t ga = true -> tag_matches t gb = true ->
  numty_eqb t GTInt = false -> numty_eqb t GTUint = false -> is_int_goty t = true ->
  exists v, typed_cmp o t ga gb = Some v.
Proof.
  intros o t [A [xa taga]] [B [xb tagb]] Ho Ha Hb Hgi Hgu Hi.
  destruct o; try discriminate Ho;
  destruct t; try discriminate Hi; try discriminate Hgi; try discriminate Hgu;
  destruct taga; try discriminate Ha;
  destruct tagb; try discriminate Hb;
  eexists; reflexivity.
Qed.
Lemma typed_cmp_noncmp_none : forall o t ga gb,
  cmp_binop o = false -> typed_cmp o t ga gb = None.
Proof. intros o t ga gb H. unfold typed_cmp. rewrite H. reflexivity. Qed.
Lemma typed_cmp_gtint_none : forall o ga gb, typed_cmp o GTInt ga gb = None.
Proof. intros o ga gb. unfold typed_cmp. destruct (cmp_binop o); reflexivity. Qed.
Lemma typed_cmp_uint_none : forall o ga gb, typed_cmp o GTUint ga gb = None.
Proof. intros o ga gb. unfold typed_cmp. destruct (cmp_binop o); reflexivity. Qed.
Lemma typed_cmp_nonint_none : forall o t ga gb,
  is_int_goty t = false -> typed_cmp o t ga gb = None.
Proof.
  intros o t ga gb H. unfold typed_cmp.
  destruct (cmp_binop o); [destruct t; try discriminate H; reflexivity | reflexivity].
Qed.
(** ---- Tier T5 — HETEROGENEOUS typed SHIFT dispatch ----
    Go's shift is NOT a same-width binop: the LEFT operand fixes the result width; the COUNT is an
    independent integer of ANY width.  A NEGATIVE runtime count PANICS ([rt_shift_neg], gc's exact
    payload, go-run-verified); a count >= 64 SATURATES to 64 before the model op — for a carrier of
    <= 64 bits, shifting by >= 64 IS shifting by 64 ([<<]: >= w trailing zero bits, 0 mod 2^w;
    [>>]: exhausted to 0 / the sign fill; go-run-verified [uint8(3) << ^uint64(3)] = 0) — so NO
    GATE-ADMITTED count is unmodelled: a CONSTANT count is read off [ptype]'s own value
    ([shift_count]'s direct read, TOTAL — [shift_count_const_total]), a RUNTIME count off its
    carrier.  Small widths take the model's [GoInt] count, [i64]/[u64] the raw
    [Z] count, each behind its own nonneg-evidence convoy. *)
Definition shift_op (o : BinOp) : bool := match o with BShl | BShr => true | _ => false end.
Definition shift_amount (z : Z) : GoInt := intwrap (Z.min z 64).
Lemma shift_amount_nonneg : forall z,
  (0 <=? z)%Z = true -> Z.leb 0 (intraw (shift_amount z)) = true.
Proof.
  intros z Hz. unfold shift_amount, intwrap. cbn [intraw].
  apply Z.leb_le. apply Z.leb_le in Hz. unfold wrap64.
  rewrite Z.mod_small by lia. lia.
Qed.
Definition shift_checked_small {A : Type} (tag : GoTypeTag A)
    (op : A -> forall k : GoInt, Z.leb 0 (intraw k) = true -> A) (x : A) (z : Z) : option RAny :=
  (match (0 <=? z)%Z as b return (0 <=? z)%Z = b -> option RAny with
   | false => fun _ => Some (RAPanic rt_shift_neg)
   | true => fun _ =>
       (match Z.leb 0 (intraw (shift_amount z)) as b2
              return Z.leb 0 (intraw (shift_amount z)) = b2 -> option RAny with
        | true  => fun pf => Some (RAVal (anyt tag (op x (shift_amount z) pf)))
        | false => fun _  => None
        end) eq_refl
   end) eq_refl.
Definition shift_checked_wide {A : Type} (tag : GoTypeTag A)
    (op : A -> forall k : Z, (0 <=? k)%Z = true -> A) (x : A) (z : Z) : option RAny :=
  (match (0 <=? z)%Z as b return (0 <=? z)%Z = b -> option RAny with
   | false => fun _ => Some (RAPanic rt_shift_neg)
   | true => fun _ =>
       (match (0 <=? Z.min z 64)%Z as b2 return (0 <=? Z.min z 64)%Z = b2 -> option RAny with
        | true  => fun pf => Some (RAVal (anyt tag (op x (Z.min z 64) pf)))
        | false => fun _  => None
        end) eq_refl
   end) eq_refl.
Lemma shift_checked_small_cases : forall (A : Type) (tag : GoTypeTag A) op (x : A) z,
  ((0 <=? z)%Z = false /\ shift_checked_small tag op x z = Some (RAPanic rt_shift_neg))
  \/ ((0 <=? z)%Z = true
      /\ exists pf, shift_checked_small tag op x z
                    = Some (RAVal (anyt tag (op x (shift_amount z) pf)))).
Proof.
  intros A tag op x z. unfold shift_checked_small.
  assert (K2 : forall b2 (pf2 : Z.leb 0 (intraw (shift_amount z)) = b2), b2 = true ->
      exists pf, (match b2 as b0 return Z.leb 0 (intraw (shift_amount z)) = b0 -> option RAny with
                  | true  => fun pf0 => Some (RAVal (anyt tag (op x (shift_amount z) pf0)))
                  | false => fun _   => None
                  end) pf2 = Some (RAVal (anyt tag (op x (shift_amount z) pf)))).
  { intros b2 pf2 Hb2. destruct b2; [eexists; reflexivity | discriminate Hb2]. }
  assert (K : forall b (pfb : (0 <=? z)%Z = b),
      ((0 <=? z)%Z = false
       /\ (match b as b0 return (0 <=? z)%Z = b0 -> option RAny with
           | false => fun _ => Some (RAPanic rt_shift_neg)
           | true => fun _ =>
               (match Z.leb 0 (intraw (shift_amount z)) as b2
                      return Z.leb 0 (intraw (shift_amount z)) = b2 -> option RAny with
                | true  => fun pf => Some (RAVal (anyt tag (op x (shift_amount z) pf)))
                | false => fun _  => None
                end) eq_refl
           end) pfb = Some (RAPanic rt_shift_neg))
      \/ ((0 <=? z)%Z = true
          /\ exists pf, (match b as b0 return (0 <=? z)%Z = b0 -> option RAny with
              | false => fun _ => Some (RAPanic rt_shift_neg)
              | true => fun _ =>
                  (match Z.leb 0 (intraw (shift_amount z)) as b2
                         return Z.leb 0 (intraw (shift_amount z)) = b2 -> option RAny with
                   | true  => fun pf0 => Some (RAVal (anyt tag (op x (shift_amount z) pf0)))
                   | false => fun _  => None
                   end) eq_refl
              end) pfb = Some (RAVal (anyt tag (op x (shift_amount z) pf))))).
  { intros b pfb. destruct b.
    - right. split; [exact pfb|]. exact (K2 _ eq_refl (shift_amount_nonneg z pfb)).
    - left. split; [exact pfb | reflexivity]. }
  exact (K _ eq_refl).
Qed.
Lemma shift_checked_wide_cases : forall (A : Type) (tag : GoTypeTag A) op (x : A) z,
  ((0 <=? z)%Z = false /\ shift_checked_wide tag op x z = Some (RAPanic rt_shift_neg))
  \/ ((0 <=? z)%Z = true
      /\ exists pf, shift_checked_wide tag op x z
                    = Some (RAVal (anyt tag (op x (Z.min z 64) pf)))).
Proof.
  intros A tag op x z. unfold shift_checked_wide.
  assert (K2 : forall b2 (pf2 : (0 <=? Z.min z 64)%Z = b2), b2 = true ->
      exists pf, (match b2 as b0 return (0 <=? Z.min z 64)%Z = b0 -> option RAny with
                  | true  => fun pf0 => Some (RAVal (anyt tag (op x (Z.min z 64) pf0)))
                  | false => fun _   => None
                  end) pf2 = Some (RAVal (anyt tag (op x (Z.min z 64) pf)))).
  { intros b2 pf2 Hb2. destruct b2; [eexists; reflexivity | discriminate Hb2]. }
  assert (K : forall b (pfb : (0 <=? z)%Z = b),
      ((0 <=? z)%Z = false
       /\ (match b as b0 return (0 <=? z)%Z = b0 -> option RAny with
           | false => fun _ => Some (RAPanic rt_shift_neg)
           | true => fun _ =>
               (match (0 <=? Z.min z 64)%Z as b2 return (0 <=? Z.min z 64)%Z = b2 -> option RAny with
                | true  => fun pf => Some (RAVal (anyt tag (op x (Z.min z 64) pf)))
                | false => fun _  => None
                end) eq_refl
           end) pfb = Some (RAPanic rt_shift_neg))
      \/ ((0 <=? z)%Z = true
          /\ exists pf, (match b as b0 return (0 <=? z)%Z = b0 -> option RAny with
              | false => fun _ => Some (RAPanic rt_shift_neg)
              | true => fun _ =>
                  (match (0 <=? Z.min z 64)%Z as b2 return (0 <=? Z.min z 64)%Z = b2 -> option RAny with
                   | true  => fun pf0 => Some (RAVal (anyt tag (op x (Z.min z 64) pf0)))
                   | false => fun _  => None
                   end) eq_refl
              end) pfb = Some (RAVal (anyt tag (op x (Z.min z 64) pf))))).
  { intros b pfb. destruct b.
    - right. split; [exact pfb|].
      assert (Hm : (0 <=? Z.min z 64)%Z = true)
        by (apply Z.leb_le; apply Z.leb_le in pfb; lia).
      exact (K2 _ eq_refl Hm).
    - left. split; [exact pfb | reflexivity]. }
  exact (K _ eq_refl).
Qed.

Definition typed_shift (o : BinOp) (t : GoTy) (ga : GoAny) (z : Z) : option RAny :=
  if shift_op o then
    match t with
    | GTU8 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU8 => fun va =>
                match o with
                | BShl => shift_checked_small TU8 u8_shl va z
                | BShr => shift_checked_small TU8 u8_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | GTI8 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI8 => fun va =>
                match o with
                | BShl => shift_checked_small TI8 i8_shl va z
                | BShr => shift_checked_small TI8 i8_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | GTU16 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU16 => fun va =>
                match o with
                | BShl => shift_checked_small TU16 u16_shl va z
                | BShr => shift_checked_small TU16 u16_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | GTI16 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI16 => fun va =>
                match o with
                | BShl => shift_checked_small TI16 i16_shl va z
                | BShr => shift_checked_small TI16 i16_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | GTU32 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU32 => fun va =>
                match o with
                | BShl => shift_checked_small TU32 u32_shl va z
                | BShr => shift_checked_small TU32 u32_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | GTI32 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI32 => fun va =>
                match o with
                | BShl => shift_checked_small TI32 i32_shl va z
                | BShr => shift_checked_small TI32 i32_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | GTInt64 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TI64 => fun va =>
                match o with
                | BShl => shift_checked_wide TI64 i64_shl va z
                | BShr => shift_checked_wide TI64 i64_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | GTU64 =>
        match ga with
        | existT _ _ (pair xa taga) =>
            match taga in GoTypeTag A return A -> option RAny with
            | TU64 => fun va =>
                match o with
                | BShl => shift_checked_wide TU64 u64_shl va z
                | BShr => shift_checked_wide TU64 u64_shr va z
                | _ => None
                end
            | _ => fun _ => None
            end xa
        end
    | _ => None
    end
  else None.
(** The COUNT layer — full evaluation, then the raw reading off ANY int carrier. *)
Definition shift_count (rv : GExpr -> option RAny) (e : GExpr) : option (Z + GoAny) :=
  (* A CONSTANT count is read off [ptype]'s OWN value directly — TOTAL on the gate's admitted
     class ([shift_count_const_total] needs no evaluation premise).  The boxed path would be a
     side-condition leak: [box_int]'s conservative default-[int] window is a VALUE range, not a
     COUNT range, and would drop a VALID untyped count like [2^31]; the gate's shift row is the
     one count authority ([is_neg_const] + [untyped_count_overflow]).  Only a RUNTIME count
     evaluates ([rv], at its own width — panics propagate). *)
  match ptype e with
  | Some (PtIntConst z)    => Some (inl z)
  | Some (PtTIntConst _ z) => Some (inl z)
  | _ =>
      match rv e with
      | Some (RAVal g) => match runint_raw g with Some z => Some (inl z) | None => None end
      | Some (RAPanic p) => Some (inr p)
      | None => None
      end
  end.
(** The typed-shift seal set. *)
Lemma typed_shift_tag_exact : forall o t ga z g,
  typed_shift o t ga z = Some (RAVal g) ->
  tag_matches t ga = true /\ tag_matches t g = true.
Proof.
  intros o t [A [xa taga]] z g H.
  unfold typed_shift in H.
  destruct o; cbv beta iota delta [shift_op] in H; try discriminate H;
  destruct t; cbv beta iota in H; try discriminate H;
  destruct taga; cbv beta iota in H; try discriminate H;
  first
    [ (edestruct shift_checked_small_cases as [[Ez Ep] | [Ez [pf Ev]]];
       [ rewrite Ep in H; discriminate H
       | rewrite Ev in H; injection H as <-; split; reflexivity ])
    | (edestruct shift_checked_wide_cases as [[Ez Ep] | [Ez [pf Ev]]];
       [ rewrite Ep in H; discriminate H
       | rewrite Ev in H; injection H as <-; split; reflexivity ]) ].
Qed.
Lemma typed_shift_panic_neg : forall o t ga z p,
  typed_shift o t ga z = Some (RAPanic p) ->
  p = rt_shift_neg /\ (0 <=? z)%Z = false.
Proof.
  intros o t [A [xa taga]] z p H.
  unfold typed_shift in H.
  destruct o; cbv beta iota delta [shift_op] in H; try discriminate H;
  destruct t; cbv beta iota in H; try discriminate H;
  destruct taga; cbv beta iota in H; try discriminate H;
  first
    [ (edestruct shift_checked_small_cases as [[Ez Ep] | [Ez [pf Ev]]];
       [ rewrite Ep in H; injection H as <-; split; [reflexivity | exact Ez]
       | rewrite Ev in H; discriminate H ])
    | (edestruct shift_checked_wide_cases as [[Ez Ep] | [Ez [pf Ev]]];
       [ rewrite Ep in H; injection H as <-; split; [reflexivity | exact Ez]
       | rewrite Ev in H; discriminate H ]) ].
Qed.
Lemma typed_shift_live_total : forall o t ga z,
  shift_op o = true ->
  tag_matches t ga = true ->
  numty_eqb t GTInt = false -> numty_eqb t GTUint = false -> is_int_goty t = true ->
  exists r, typed_shift o t ga z = Some r.
Proof.
  intros o t [A [xa taga]] z Ho Ha Hgi Hgu Hi.
  destruct o; try discriminate Ho;
  destruct t; try discriminate Hi; try discriminate Hgi; try discriminate Hgu;
  destruct taga; try discriminate Ha;
  unfold typed_shift; cbv beta iota;
  first
    [ (edestruct shift_checked_small_cases as [[Ez Ep] | [Ez [pf Ev]]]; eexists;
       first [exact Ep | exact Ev])
    | (edestruct shift_checked_wide_cases as [[Ez Ep] | [Ez [pf Ev]]]; eexists;
       first [exact Ep | exact Ev]) ].
Qed.
Lemma typed_shift_nonshift_none : forall o t ga z,
  shift_op o = false -> typed_shift o t ga z = None.
Proof. intros o t ga z H. unfold typed_shift. rewrite H. reflexivity. Qed.
Lemma typed_shift_gtint_none : forall o ga z, typed_shift o GTInt ga z = None.
Proof. intros o ga z. unfold typed_shift. destruct (shift_op o); reflexivity. Qed.
Lemma typed_shift_uint_none : forall o ga z, typed_shift o GTUint ga z = None.
Proof. intros o ga z. unfold typed_shift. destruct (shift_op o); reflexivity. Qed.
Lemma typed_shift_nonint_none : forall o t ga z,
  is_int_goty t = false -> typed_shift o t ga z = None.
Proof.
  intros o t ga z H. unfold typed_shift.
  destruct (shift_op o); [destruct t; try discriminate H; reflexivity | reflexivity].
Qed.

(** ---- Tier R8 — the GTInt ENGINE's bitwise + shift dispatch ----
    The engine's own [GoInt] carrier takes the four bitwise binops as TOTAL model ops through ONE
    dispatch authority ([int_bitop]) and the two shifts through a count-checked convoy
    ([int_shift_checked] — [shift_checked_wide]'s exact shape at the engine's result type [RRes]):
    a NEGATIVE count panics [rt_shift_neg] (gc's exact payload), a count >= 64 SATURATES
    ([Z.min z 64] — exact for the 64-bit carrier), and the model op takes the raw [Z] count behind
    the nonneg-evidence convoy.  go-run-verified: 3&1=1, 3|4=7, 3^1=2, 3&^2=1, 3<<62 wraps
    negative, 3<<huge = 0, -3>>huge = -1, -3>>1 = -2, a negative runtime count panics. *)
Definition int_bitop (o : BinOp) : option (GoInt -> GoInt -> GoInt) :=
  match o with
  | BAnd    => Some int_and
  | BOr     => Some int_or
  | BXor    => Some int_xor
  | BAndNot => Some int_andnot
  | _       => None
  end.
Definition int_shift_op (o : BinOp) : option (GoInt -> forall k : Z, (0 <=? k)%Z = true -> GoInt) :=
  match o with
  | BShl => Some int_shl
  | BShr => Some int_shr
  | _    => None
  end.
Definition int_shift_checked
    (op : GoInt -> forall k : Z, (0 <=? k)%Z = true -> GoInt) (x : GoInt) (z : Z) : option RRes :=
  (match (0 <=? z)%Z as b return (0 <=? z)%Z = b -> option RRes with
   | false => fun _ => Some (RPanic rt_shift_neg)
   | true => fun _ =>
       (match (0 <=? Z.min z 64)%Z as b2 return (0 <=? Z.min z 64)%Z = b2 -> option RRes with
        | true  => fun pf => Some (RVal (op x (Z.min z 64) pf))
        | false => fun _  => None
        end) eq_refl
   end) eq_refl.
Lemma int_shift_checked_cases : forall op (x : GoInt) z,
  ((0 <=? z)%Z = false /\ int_shift_checked op x z = Some (RPanic rt_shift_neg))
  \/ ((0 <=? z)%Z = true
      /\ exists pf, int_shift_checked op x z = Some (RVal (op x (Z.min z 64) pf))).
Proof.
  intros op x z. unfold int_shift_checked.
  assert (K2 : forall b2 (pf2 : (0 <=? Z.min z 64)%Z = b2), b2 = true ->
      exists pf, (match b2 as b0 return (0 <=? Z.min z 64)%Z = b0 -> option RRes with
                  | true  => fun pf0 => Some (RVal (op x (Z.min z 64) pf0))
                  | false => fun _   => None
                  end) pf2 = Some (RVal (op x (Z.min z 64) pf))).
  { intros b2 pf2 Hb2. destruct b2; [eexists; reflexivity | discriminate Hb2]. }
  assert (K : forall b (pfb : (0 <=? z)%Z = b),
      ((0 <=? z)%Z = false
       /\ (match b as b0 return (0 <=? z)%Z = b0 -> option RRes with
           | false => fun _ => Some (RPanic rt_shift_neg)
           | true => fun _ =>
               (match (0 <=? Z.min z 64)%Z as b2 return (0 <=? Z.min z 64)%Z = b2 -> option RRes with
                | true  => fun pf => Some (RVal (op x (Z.min z 64) pf))
                | false => fun _  => None
                end) eq_refl
           end) pfb = Some (RPanic rt_shift_neg))
      \/ ((0 <=? z)%Z = true
          /\ exists pf, (match b as b0 return (0 <=? z)%Z = b0 -> option RRes with
              | false => fun _ => Some (RPanic rt_shift_neg)
              | true => fun _ =>
                  (match (0 <=? Z.min z 64)%Z as b2 return (0 <=? Z.min z 64)%Z = b2 -> option RRes with
                   | true  => fun pf0 => Some (RVal (op x (Z.min z 64) pf0))
                   | false => fun _  => None
                   end) eq_refl
              end) pfb = Some (RVal (op x (Z.min z 64) pf)))).
  { intros b pfb. destruct b.
    - right. split; [exact pfb|].
      assert (Hm : (0 <=? Z.min z 64)%Z = true)
        by (apply Z.leb_le; apply Z.leb_le in pfb; lia).
      exact (K2 _ eq_refl Hm).
    - left. split; [exact pfb | reflexivity]. }
  exact (K _ eq_refl).
Qed.

Definition rexit_with (rec : GExpr -> option RRes) (rv : GExpr -> option RAny) (e : GExpr) : option RAny :=
  match e with
  | ECall (EId f) (a :: nil) =>
      (* tiers R3+T2, the EXIT half — a width conversion to a non-[GTInt] integer target: [ptype]'s
         [PtRunInt t] on a one-arg call can ONLY be [conv_to_scalar] (or [len]/[cap], which are
         [GTInt] — excluded here) — PROVED, not asserted: [ptype_call_runint_conv] seals [t] to an
         integer keyword target, on which [wrap_runint] is total ([wrap_runint_total]).  T2: the ARG
         evaluates at FULL power ([rv]), so a chain through a non-[GTInt] intermediate
         ([int64(uint8(len ..))]) converts exactly like Go — read the carrier's value ([runint_raw]),
         wrap into the target.  A non-integer-tagged source (a runtime FLOAT — CLASS-absent,
         [reval_val_runfloat_none]) is absent fail-closed.  A panicking arg panics (Go's order). *)
      match ptype e with
      | Some (PtRunInt t) =>
          if numty_eqb t GTInt then None else
          match rv a with
          | Some (RAVal g) =>
              match runint_raw g with
              | Some z =>
                  match wrap_runint t z with
                  | Some g' => Some (RAVal g')
                  | None => None
                  end
              | None => None
              end
          | Some (RAPanic p) => Some (RAPanic p)
          | None => None
          end
      | _ => None
      end
  | EUn o a =>
      (* tier T1 — typed unary on a non-GTInt runtime carrier ([^int64(len ..)] etc.): the outer
         [ptype] pins the width [t] (the GTInt case lives in [reval_int]); the ARG evaluates at FULL
         power ([rv] — so an R3-converted operand works), then [typed_unop] applies the width's model
         op on the boxed carrier.  A hole in the op table ([GTUint], narrow [-]) is absent. *)
      match ptype e with
      | Some (PtRunInt t) =>
          if numty_eqb t GTInt then None else
          match rv a with
          | Some (RAVal g)   => match typed_unop o t g with
                                | Some g' => Some (RAVal g')
                                | None => None
                                end
          | Some (RAPanic p) => Some (RAPanic p)
          | None => None
          end
      | _ => None
      end
  | EBn o a b =>
      (* tiers R4+T4 — the runtime bool COMPARISON exit: [ptype e = PtBool] on a binop is a
         comparison (or [&&]/[||] — dispatched away by [cmp_verdict]/[cmp_binop]); [cmp_width] picks the
         operand width (the runtime operand pins it; two int constants default to [GTInt] — Go's
         untyped rule).  At [GTInt] the R4 engine path runs unchanged; at a FIXED width the T4 typed
         path runs (operands through the width-sealed [typed_operand], the verdict the width's own
         model op).  A panicking operand panics LEFT-to-right (Go's order), before any comparison.
         tier T3 — the [PtRunInt t] case is SAME-WIDTH typed arithmetic/bitwise: each operand goes
         through [typed_operand] (WIDTH-SEALED: a runtime operand classified AT the width runs at
         FULL power via [rv]; an UNTYPED int constant CONVERTS to the width; a TYPED constant must
         already BE the width — Go's rules), then [typed_binop] applies the width's model op (a
         value, or the division-by-zero panic — [div_checked]).  A hole row ([GTUint], shifts) is
         absent. *)
      match ptype e with
      | Some PtBool =>
          match cmp_width (ptype a) (ptype b) with
          | Some t =>
              if numty_eqb t GTInt then
                (* the R4 [GTInt] engine path — unchanged *)
                match cmp_verdict o with
                | None => None
                | Some cmp =>
                    match rec a with
                    | Some (RVal va) =>
                        match rec b with
                        | Some (RVal vb) => Some (RAVal (anyt TBool (cmp va vb)))
                        | Some (RPanic p) => Some (RAPanic p)
                        | None => None
                        end
                    | Some (RPanic p) => Some (RAPanic p)
                    | None => None
                    end
                end
              else
                (* tier T4 — SAME-WIDTH typed comparison: operands through the width-sealed
                   [typed_operand], the verdict from the width's own model op ([typed_cmp]).
                   Panics propagate left-to-right; holes ([GTUint]) are absent. *)
                match typed_operand rv t a with
                | Some (RAVal ga) =>
                    match typed_operand rv t b with
                    | Some (RAVal gb) =>
                        match typed_cmp o t ga gb with
                        | Some v => Some (RAVal (anyt TBool v))
                        | None => None
                        end
                    | Some (RAPanic p) => Some (RAPanic p)
                    | None => None
                    end
                | Some (RAPanic p) => Some (RAPanic p)
                | None => None
                end
          | None => None
          end
      | Some (PtRunInt t) =>
          if numty_eqb t GTInt then None else
          match typed_operand rv t a with
          | Some (RAVal ga) =>
              if typed_arith_op o then
                match typed_operand rv t b with
                | Some (RAVal gb) => typed_binop o t ga gb
                | Some (RAPanic p) => Some (RAPanic p)
                | None => None
                end
              else if shift_op o then
                (* tier T5 — the COUNT is read by the sealed count layer ([shift_count]): a
                   CONSTANT count directly off the gate's own value (total on the admitted class),
                   a RUNTIME count at FULL power at ITS OWN width; the width-sealed left operand
                   feeds [typed_shift]. *)
                match shift_count rv b with
                | Some (inl z) => typed_shift o t ga z
                | Some (inr p) => Some (RAPanic p)
                | None => None
                end
              else None
          | Some (RAPanic p) => Some (RAPanic p)
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.
Definition reval_val_with (rec : GExpr -> option RRes) : GExpr -> option RAny :=
  fix rv (e : GExpr) : option RAny :=
    match eval_value e with
    | Some v => Some (RAVal v)
    | None =>
        match rec e with
        | Some (RVal x)   => Some (RAVal (anyt TInt64 x))
        | Some (RPanic p) => Some (RAPanic p)
        | None => rexit_with rec rv e
        end
    end.
(* One-step unfolding equation (the fix reduces only on constructors; [destruct e] closes each case). *)
Lemma reval_val_with_eq : forall rec e,
  reval_val_with rec e
  = match eval_value e with
    | Some v => Some (RAVal v)
    | None =>
        match rec e with
        | Some (RVal x)   => Some (RAVal (anyt TInt64 x))
        | Some (RPanic p) => Some (RAPanic p)
        | None => rexit_with rec (reval_val_with rec) e
        end
    end.
Proof. intros rec e. destruct e; reflexivity. Qed.
(** Map-literal CONSTRUCTION for the runtime tier (R5) — walk ALL the (key, value) PAIRS, evaluating
    each VALUE through the FULL shared evaluator (so a value ANY tier denotes — R3 width conversions and
    R4 comparisons included — constructs; ONE authority with [denote_expr], no drift).  ⚠ Go leaves the
    EVALUATION ORDER of a map literal's assignments UNSPECIFIED (spec, "Order of evaluation"), so a
    panic is denoted ONLY when it is mechanically ORDER-INDEPENDENT (values in this fragment are
    effect-free, so a SINGLE panicking value panics under every schedule; two-plus are ambiguous and
    absent) — the AUTHORITY is the quantified class seal just below ([rconstr_vals_ok_iff] /
    [rconstr_vals_panic_sound] / [rconstr_vals_two_panics_absent]), not this prose.  Keys are
    constants under the [PtRunInt] guard and cannot panic.  The value is bound by the PAIR pattern so
    the enclosing [Fixpoint]'s guard accepts the recursion. *)
Inductive RConstr : Type := RCOk | RCPanic (p : GoAny).
Definition rconstr_vals_with (rval : GExpr -> option RAny) : list (GExpr * GExpr) -> option RConstr :=
  fix go (l : list (GExpr * GExpr)) : option RConstr :=
    match l with
    | nil => Some RCOk
    | (_, v) :: r =>
        match rval v, go r with
        | Some (RAVal _),  rest        => rest
        | Some (RAPanic p), Some RCOk  => Some (RCPanic p)   (* the ONLY panic — order-independent *)
        | Some (RAPanic _), _          => None               (* a second panic (or an absent rest): ambiguous, absent *)
        | None, _ => None
        end
    end.

(** ★ THE WALKER'S CLASS SEAL — quantified characterization of [rconstr_vals_with] (manifest-gated),
    the AUTHORITY for the order-independence claim (the fixtures below are witnesses, not the guard):
    [RCOk] iff EVERY value evaluates to a value ([rconstr_vals_ok_iff]); [RCPanic p] only with an
    exactly-one decomposition — SOME position panics [p] and every OTHER value evaluates
    ([rconstr_vals_panic_sound]); and ANY list containing TWO panicking values — arbitrary prefix /
    middle / suffix — is [None] ([rconstr_vals_two_panics_absent]): a source-order semantics cannot
    be reintroduced while these hold. *)
Definition rval_is_val (rval : GExpr -> option RAny) (kv : GExpr * GExpr) : bool :=
  match rval (snd kv) with Some (RAVal _) => true | _ => false end.
Lemma rconstr_vals_with_cons : forall rval k v r,
  rconstr_vals_with rval ((k, v) :: r)
  = match rval v, rconstr_vals_with rval r with
    | Some (RAVal _),  rest        => rest
    | Some (RAPanic p), Some RCOk  => Some (RCPanic p)
    | Some (RAPanic _), _          => None
    | None, _ => None
    end.
Proof. reflexivity. Qed.
Lemma rconstr_vals_ok_iff : forall rval l,
  rconstr_vals_with rval l = Some RCOk <-> forallb (rval_is_val rval) l = true.
Proof.
  intros rval l; induction l as [| [k v] r IH].
  - cbn. split; reflexivity.
  - rewrite rconstr_vals_with_cons. cbn [forallb].
    unfold rval_is_val at 1. cbn [snd].
    destruct (rval v) as [[g|q]|].
    + cbv beta iota. rewrite andb_true_l. exact IH.
    + destruct (rconstr_vals_with rval r) as [[|q']|];
        cbv beta iota; rewrite andb_false_l;
        split; intro H; discriminate H.
    + cbv beta iota. rewrite andb_false_l. split; intro H; discriminate H.
Qed.
Lemma rconstr_vals_panic_sound : forall rval l p,
  rconstr_vals_with rval l = Some (RCPanic p) ->
  exists l1 kv l2, l = l1 ++ kv :: l2
    /\ rval (snd kv) = Some (RAPanic p)
    /\ forallb (rval_is_val rval) (l1 ++ l2) = true.
Proof.
  intros rval l; induction l as [| [k v] r IH]; intros p H.
  - cbn in H. discriminate H.
  - rewrite rconstr_vals_with_cons in H.
    destruct (rval v) as [[g|q]|] eqn:Ev; cbv beta iota in H.
    + destruct (IH p H) as [l1 [kv [l2 [-> [Hp Hok]]]]].
      exists ((k, v) :: l1), kv, l2. split; [reflexivity|]. split; [exact Hp|].
      cbn [app forallb]. unfold rval_is_val at 1. cbn [snd]. rewrite Ev.
      rewrite andb_true_l. exact Hok.
    + destruct (rconstr_vals_with rval r) as [[|q']|] eqn:Er; try discriminate H.
      injection H as <-.
      exists nil, (k, v), r. split; [reflexivity|]. split; [cbn [snd]; exact Ev|].
      cbn [app]. exact (proj1 (rconstr_vals_ok_iff rval r) Er).
    + discriminate H.
Qed.
Theorem rconstr_vals_two_panics_absent : forall rval l1 kv1 l2 kv2 l3 p1 p2,
  rval (snd kv1) = Some (RAPanic p1) ->
  rval (snd kv2) = Some (RAPanic p2) ->
  rconstr_vals_with rval (l1 ++ kv1 :: l2 ++ kv2 :: l3) = None.
Proof.
  intros rval l1 kv1 l2 kv2 l3 p1 p2 H1 H2.
  assert (Hnok : forall lm, rconstr_vals_with rval (lm ++ kv2 :: l3) <> Some RCOk).
  { intros lm Hok. apply (proj1 (rconstr_vals_ok_iff _ _)) in Hok.
    rewrite forallb_app in Hok. apply andb_true_iff in Hok as [_ Hok].
    cbn [forallb] in Hok. unfold rval_is_val in Hok.
    rewrite H2 in Hok. rewrite andb_false_l in Hok. discriminate Hok. }
  induction l1 as [| [k v] r IH].
  - cbn [app]. destruct kv1 as [k1 v1]. cbn [snd] in H1.
    rewrite rconstr_vals_with_cons. rewrite H1. cbv beta iota.
    destruct (rconstr_vals_with rval (l2 ++ kv2 :: l3)) as [[|q]|] eqn:Er;
      cbv beta iota; [exfalso; exact (Hnok l2 Er) | reflexivity | reflexivity].
  - cbn [app]. rewrite rconstr_vals_with_cons.
    destruct (rval v) as [[g|q]|]; cbv beta iota.
    + exact IH.
    + destruct (rconstr_vals_with rval (r ++ kv1 :: l2 ++ kv2 :: l3)) as [[|q']|] eqn:Er;
        cbv beta iota; [| reflexivity | reflexivity].
      exfalso. apply (proj1 (rconstr_vals_ok_iff _ _)) in Er.
      rewrite forallb_app in Er. apply andb_true_iff in Er as [_ Er].
      cbn [forallb] in Er. unfold rval_is_val in Er.
      destruct kv1 as [k1 v1]. cbn [snd] in H1, Er.
      rewrite H1 in Er. rewrite andb_false_l in Er. discriminate Er.
    + reflexivity.
Qed.

Fixpoint reval_int (e : GExpr) : option RRes :=
  match eval_value e with
  | Some v => match unbox_int v with Some x => Some (RVal x) | None => None end
  | None =>
      match ptype e with
      | Some (PtRunInt t) =>
          if negb (numty_eqb t GTInt) then None else
          match e with
          | ECall (EId f) (ESliceLit et es :: nil) =>
              if String.eqb (proj1_sig f) "len" && is_int_goty et
              then match reval_elems_with reval_int es with
                   | Some (REVals vs)  => rval_len (length vs)
                   | Some (REPanic p)  => Some (RPanic p)   (* a panicking element ABORTS construction *)
                   | None => None
                   end
              else None
          | ECall (EId f) (EMapLit kt vt kvs :: nil) =>
              (* tier R5 — [len] of a map literal whose VALUES are runtime: Go CONSTRUCTS the literal
                 (every entry evaluated, in an UNSPECIFIED order) before [len]; the count is the number of
                 DISTINCT keys.  The arm carries the FOLD arm's own side conditions — [is_int_goty kt],
                 [goty_supported vt] (an invalid nested value type must never receive behavior), and
                 [nodup_z] over [ptype]'s own constant-key list (the count IS Go's [len], never a
                 duplicate-key miscount; the outer [PtRunInt] guard already forces all-constant keys —
                 [ptype]'s map arm rejects runtime keys — so this is the fold's defense-in-depth
                 mirrored) — then evaluates EVERY VALUE through the FULL shared evaluator
                 ([rconstr_vals_with (reval_val_with reval_int)] — R3-converted and R4-compared values
                 construct exactly as they denote standalone): all values → the entry count via the
                 checked [rval_len]; a SINGLE panicking value → that panic; TWO panicking values / an
                 absent value → absent (Go leaves map-literal order unspecified — sealed by the
                 walker's class theorems, [rconstr_vals_two_panics_absent] et al.). *)
              if String.eqb (proj1_sig f) "len" && is_int_goty kt && goty_supported vt
                 && nodup_z (map_key_vals kvs)
              then match rconstr_vals_with (reval_val_with reval_int) kvs with
                   | Some RCOk        => rval_len (length kvs)
                   | Some (RCPanic p) => Some (RPanic p)
                   | None => None
                   end
              else None
          | ECall (EId f) (a :: nil) =>
              (* tiers R3+T2, the IN-fragment half — [int(x)]: Go's conversion INTO [int], via the
                 model's own [intwrap] on the source carrier's raw value.  T2: the ARG evaluates at
                 FULL power ([reval_val_with] over THIS engine — the map arm's precedent), so a chain
                 through a non-[GTInt] intermediate ([int(uint8(len ..))]) converts exactly like Go.
                 A non-integer-tagged source ([int(<runtime float>)]) is absent fail-closed
                 ([runint_raw]; CLASS-absent, [reval_val_runfloat_none]).  Non-[GTInt] targets EXIT
                 the fragment in [rexit_with]. *)
              if String.eqb (proj1_sig f) "int"
              then match reval_val_with reval_int a with
                   | Some (RAVal g) =>
                       match runint_raw g with
                       | Some z => Some (RVal (intwrap z))
                       | None => None
                       end
                   | Some (RAPanic p) => Some (RPanic p)
                   | None => None
                   end
              else None
          | EIndex (ESliceLit et es) idx =>
              (* tier R2 — the RUNTIME slice INDEX: Go evaluates the literal (construction, abort on a
                 panicking element) THEN the index; in-bounds yields the element, out-of-bounds (negative
                 or >= length) PANICS with the MODEL's own [rt_index_oob i n] — the EXACT Go payload
                 (index and length rendered; a negative index omits the length part — verified against
                 gc via go run; [slice_idx_get]'s payload, shared).  The outer [PtRunInt GTInt] guard
                 pins the element type to [GTInt]. *)
              match reval_elems_with reval_int es with
              | Some (REVals vs) =>
                  match reval_int idx with
                  | Some (RVal vi) =>
                      if andb (Z.leb 0 (intraw vi)) (Z.ltb (intraw vi) (Z.of_nat (length vs)))
                      then match nth_error vs (Z.to_nat (intraw vi)) with
                           | Some v => Some (RVal v)
                           | None => None   (* unreachable under the bounds check; fail-closed *)
                           end
                      else Some (RPanic (rt_index_oob (intraw vi) (length vs)))
                  | Some (RPanic p) => Some (RPanic p)
                  | None => None
                  end
              | Some (REPanic p) => Some (RPanic p)
              | None => None
              end
          | EBn o a b =>
              if shift_op o then
                (* tier R8 — the GTInt SHIFT: the LEFT operand is the engine's own fragment
                   (evaluated FIRST — a panicking left fires before the count, Go's order); the
                   COUNT is read by T5's sealed count layer ([shift_count] over the shared
                   evaluator — a CONSTANT count directly off the gate's value, a RUNTIME count at
                   its own width, so a [uint8]-counted GTInt shift works), then the checked convoy
                   applies the dispatched model op ([int_shift_checked]: a NEGATIVE count panics
                   [rt_shift_neg], counts >= 64 saturate). *)
                match reval_int a with
                | Some (RVal va) =>
                    match shift_count (reval_val_with reval_int) b with
                    | Some (inl z) =>
                        match int_shift_op o with
                        | Some f => int_shift_checked f va z
                        | None => None   (* unreachable under [shift_op o = true]; fail-closed *)
                        end
                    | Some (inr p) => Some (RPanic p)
                    | None => None
                    end
                | Some (RPanic p) => Some (RPanic p)
                | None => None
                end
              else
              match reval_int a, reval_int b with
              | Some (RPanic p), _ => Some (RPanic p)            (* left-to-right: a panicking LEFT operand fires first *)
              | Some (RVal _), Some (RPanic p) => Some (RPanic p)
              | Some (RVal va), Some (RVal vb) =>
                  match o with
                  | BAdd => Some (RVal (int_add va vb))
                  | BSub => Some (RVal (int_sub va vb))
                  | BMul => Some (RVal (int_mul va vb))
                  | BDiv =>
                      (* the model's EVIDENCE-CARRYING division, its nonzero proof produced by the very
                         test that guards the branch (the dependent convoy) — no raw division spelling *)
                      (match Z.eqb (intraw vb) 0 as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
                       | true  => fun _  => Some (RPanic rt_div_zero)
                       | false => fun pf => Some (RVal (int_div va vb pf))
                       end) eq_refl
                  | BRem =>
                      (* the model's EVIDENCE-CARRYING remainder ([int_mod] = Go's truncated [%]),
                         the same dependent convoy as [BDiv] *)
                      (match Z.eqb (intraw vb) 0 as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
                       | true  => fun _  => Some (RPanic rt_div_zero)
                       | false => fun pf => Some (RVal (int_mod va vb pf))
                       end) eq_refl
                  | _ =>
                      (* tier R8 — the GTInt BITWISE rows ([& | ^ &^]): TOTAL model ops through the
                         ONE dispatch authority ([int_bitop]).  Everything else is fail-closed
                         (shifts are routed above; comparison/logical binops never classify
                         [PtRunInt]). *)
                      match int_bitop o with
                      | Some f => Some (RVal (f va vb))
                      | None => None
                      end
                  end
              | _, _ => None
              end
          | EUn o a =>
              (* tiers R6/R7 — runtime unary MINUS via the model's own [int_neg] (two's-complement,
                 wraps at 2^63 like Go) and runtime [^] COMPLEMENT via [int_not] ([-x-1] = [Z.lnot],
                 verified `go run`).  [!] operates on BOOLS, never the int fragment — absent. *)
              match o with
              | UNeg =>
                  match reval_int a with
                  | Some (RVal v) => Some (RVal (int_neg v))
                  | other => other
                  end
              | UXor =>
                  match reval_int a with
                  | Some (RVal v) => Some (RVal (int_not v))
                  | other => other
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Definition reval_elems : list GExpr -> option RElems := reval_elems_with reval_int.
Definition reval_val : GExpr -> option RAny := reval_val_with reval_int.
Definition rconstr_vals : list (GExpr * GExpr) -> option RConstr := rconstr_vals_with (reval_val_with reval_int).

Definition denote_expr (e : GExpr) : option (Cmd GoAny * bool) :=
  (* the FLOAT boundary once at the top, then THE shared value evaluator ([reval_val_with reval_int]:
     constant fold -> the GTInt runtime fragment -> the R3/R4 exits) — the SAME pipeline the map arm's
     construction walk consumes, so no consumer can drift. *)
  if negb (floats_checked e) then None else
  match reval_val_with reval_int e with
  | Some (RAVal v)   => Some (CRet v, false)
  | Some (RAPanic p) => Some (CPan p, true)
  | None => None
  end.

(** The pure inclusion: an expression the fold gives a value to denotes to exactly [CRet] of that value
    (fall-through — a pure expression cannot terminate control flow). *)
Lemma denote_expr_pure : forall e v, eval_value e = Some v -> denote_expr e = Some (CRet v, false).
Proof.
  intros e v H. unfold denote_expr.
  rewrite (eval_value_floats_checked e v H). cbn [negb].
  rewrite reval_val_with_eq, H. reflexivity.
Qed.

(** ★ CLASS — the determined divide-by-zero PANICS, through the runtime tier: a SUPPORTED runtime
    [GTInt] [/] or [%] whose operands BOTH evaluate ([reval_int] values) with divisor raw 0 denotes to
    [CPan rt_div_zero] (Go's exact runtime panic value) — for the WHOLE reval-evaluable fragment (the
    dividend may itself be a runtime value now, e.g. [len([]int{len([]int{1})}) / len([]int{})]). *)
Lemma denote_expr_div_zero : forall o a b va vb,
  (o = BDiv \/ o = BRem) ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  reval_int b = Some (RVal vb) ->
  Z.eqb (intraw vb) 0 = true ->
  denote_expr (EBn o a b) = Some (CPan rt_div_zero, true).
Proof.
  intros o a b va vb Ho Hfc Hpt Ha Hb Hz.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hgoal : reval_int (EBn o a b) = Some (RPanic rt_div_zero));
    [| unfold denote_expr; rewrite Hfc; cbn [negb];
       unfold reval_val_with; rewrite Hev, Hgoal; reflexivity ].
  cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb].
  rewrite Ha, Hb.
  destruct Ho as [-> | ->].
  - (* BDiv: eliminate the dependent convoy by generalizing the scrutinee AND its proof together *)
    assert (K : forall (z : bool) (pf : Z.eqb (intraw vb) 0 = z), z = true ->
              (match z as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
               | true  => fun _   => Some (RPanic rt_div_zero)
               | false => fun pf0 => Some (RVal (int_div va vb pf0))
               end) pf = Some (RPanic rt_div_zero)).
    { intros z pf Hzt. destruct z; [reflexivity | discriminate Hzt]. }
    rewrite (K _ eq_refl Hz). reflexivity.
  - (* BRem: the same convoy elimination, [int_mod] in the false branch *)
    assert (K : forall (z : bool) (pf : Z.eqb (intraw vb) 0 = z), z = true ->
              (match z as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
               | true  => fun _   => Some (RPanic rt_div_zero)
               | false => fun pf0 => Some (RVal (int_mod va vb pf0))
               end) pf = Some (RPanic rt_div_zero)).
    { intros z pf Hzt. destruct z; [reflexivity | discriminate Hzt]. }
    rewrite (K _ eq_refl Hz). reflexivity.
Qed.

(** ★ CLASS (tier R2) — the four universal RUNTIME-INDEX denotation theorems, one per outcome of the
    [EIndex (ESliceLit..)] arm, each quantified over the WHOLE reval-evaluable fragment (fixtures like
    [runtime_index_runs]/[slice_index_panics_denote] are witnesses of these classes, not the claim).
    Shared side conditions = the tier's exact firing contract: the float boundary passed, [ptype]
    classifies the whole expression [PtRunInt GTInt], and the constant fold is ABSENT ([eval_value =
    None] is a genuine hypothesis here, not derivable from [ptype] — an all-constant IN-BOUNDS index
    folds while still classified [PtRunInt]). *)
(** In-bounds: construction succeeds, the index is a value within [[0, length)] — the denotation IS the
    indexed element (and the theorem carries TOTALITY: a true bounds check guarantees the element exists). *)
Lemma denote_expr_index_in_bounds : forall et es idx vs vi,
  floats_checked (EIndex (ESliceLit et es) idx) = true ->
  ptype (EIndex (ESliceLit et es) idx) = Some (PtRunInt GTInt) ->
  eval_value (EIndex (ESliceLit et es) idx) = None ->
  reval_elems es = Some (REVals vs) ->
  reval_int idx = Some (RVal vi) ->
  andb (Z.leb 0 (intraw vi)) (Z.ltb (intraw vi) (Z.of_nat (length vs))) = true ->
  exists v, nth_error vs (Z.to_nat (intraw vi)) = Some v /\
    denote_expr (EIndex (ESliceLit et es) idx) = Some (CRet (anyt TInt64 v), false).
Proof.
  intros et es idx vs vi Hfc Hpt Hev Hes Hidx Hb.
  assert (Hlt : (Z.to_nat (intraw vi) < length vs)%nat).
  { apply andb_prop in Hb; destruct Hb as [Hle Hltz].
    apply Z.leb_le in Hle. apply Z.ltb_lt in Hltz.
    rewrite <- (Nat2Z.id (length vs)). apply Z2Nat.inj_lt; lia. }
  pose proof (proj2 (nth_error_Some vs (Z.to_nat (intraw vi))) Hlt) as Hne.
  destruct (nth_error vs (Z.to_nat (intraw vi))) as [v|] eqn:Hnth;
    [| exfalso; apply Hne; reflexivity].
  exists v. split; [reflexivity|].
  assert (Hr : reval_int (EIndex (ESliceLit et es) idx) = Some (RVal v)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes, Hidx, Hb, Hnth. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
(** Out-of-bounds (negative or >= length): the denotation PANICS with the model's exact
    [rt_index_oob i n] — index raw and STRUCTURAL constructed length, the Go payload. *)
Lemma denote_expr_index_oob : forall et es idx vs vi,
  floats_checked (EIndex (ESliceLit et es) idx) = true ->
  ptype (EIndex (ESliceLit et es) idx) = Some (PtRunInt GTInt) ->
  eval_value (EIndex (ESliceLit et es) idx) = None ->
  reval_elems es = Some (REVals vs) ->
  reval_int idx = Some (RVal vi) ->
  andb (Z.leb 0 (intraw vi)) (Z.ltb (intraw vi) (Z.of_nat (length vs))) = false ->
  denote_expr (EIndex (ESliceLit et es) idx)
    = Some (CPan (rt_index_oob (intraw vi) (length vs)), true).
Proof.
  intros et es idx vs vi Hfc Hpt Hev Hes Hidx Hb.
  assert (Hr : reval_int (EIndex (ESliceLit et es) idx)
               = Some (RPanic (rt_index_oob (intraw vi) (length vs)))).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes, Hidx, Hb. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
(** A panicking ELEMENT aborts construction (the verified go-run order): ITS panic is the denotation —
    the index is never consulted. *)
Lemma denote_expr_index_elem_panic : forall et es idx p,
  floats_checked (EIndex (ESliceLit et es) idx) = true ->
  ptype (EIndex (ESliceLit et es) idx) = Some (PtRunInt GTInt) ->
  eval_value (EIndex (ESliceLit et es) idx) = None ->
  reval_elems es = Some (REPanic p) ->
  denote_expr (EIndex (ESliceLit et es) idx) = Some (CPan p, true).
Proof.
  intros et es idx p Hfc Hpt Hev Hes.
  assert (Hr : reval_int (EIndex (ESliceLit et es) idx) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
(** A panicking INDEX (after successful construction) panics with ITS payload — Go's evaluation order
    (literal first, then index). *)
Lemma denote_expr_index_idx_panic : forall et es idx vs p,
  floats_checked (EIndex (ESliceLit et es) idx) = true ->
  ptype (EIndex (ESliceLit et es) idx) = Some (PtRunInt GTInt) ->
  eval_value (EIndex (ESliceLit et es) idx) = None ->
  reval_elems es = Some (REVals vs) ->
  reval_int idx = Some (RPanic p) ->
  denote_expr (EIndex (ESliceLit et es) idx) = Some (CPan p, true).
Proof.
  intros et es idx vs p Hfc Hpt Hev Hes Hidx.
  assert (Hr : reval_int (EIndex (ESliceLit et es) idx) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes, Hidx. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.

(** ★ CLASS (tiers R3+T2) — the WIDTH-CONVERSION denotation theorems, quantified over the whole
    reval-evaluable fragment (T2: the source is ANY full-evaluator value — chains through non-[GTInt]
    intermediates included) and SEALED to [ptype]'s own boundary: any one-arg call classified
    [PtRunInt t] with [t ≠ GTInt] is NECESSARILY a [conv_to_scalar] conversion to an INTEGER keyword
    target ([ptype_call_runint_conv] — [len]/[cap] classify [GTInt]), whose OPERAND is runtime-int- or
    runtime-float-classified ([ptype_call_runint_conv_arg] — the split is PROVED exhaustive), and on
    which the exit boxing is TOTAL ([wrap_runint_total]).  A panicking arg panics first (Go's operand
    order).  [denote_expr_conv_runs] below is the INTERNAL raw-premise form — a proof step for the
    SEALED public pair ([denote_expr_conv_runs_sealed] for exit targets,
    [denote_expr_conv_int_runs_sealed] for the [int] target), NOT exported;
    [denote_expr_conv_panic] is the public panic-propagation lemma. *)
Lemma conv_to_scalar_runint : forall ca t' t,
  conv_to_scalar ca t' = Some (PtRunInt t) -> t' = t /\ is_int_goty t = true.
Proof.
  intros ca t' t H.
  destruct t'; simpl in H; destruct ca; try discriminate;
    repeat match type of H with
           | (if ?b then _ else _) = _ => destruct b; try discriminate
           end;
    inversion H; subst; split; reflexivity.
Qed.
Lemma ptype_call_runint_conv : forall f a t,
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  is_int_goty t = true.
Proof.
  intros f a t H Ht. cbn [ptype] in H.
  destruct (ptype a) as [ca|]; [|discriminate].
  destruct (String.eqb (proj1_sig f) "len").
  - destruct a; destruct ca; try discriminate H;
      inversion H; subst; discriminate Ht.
  - destruct (String.eqb (proj1_sig f) "cap").
    + destruct ca; try discriminate H. inversion H; subst. discriminate Ht.
    + destruct (classify (proj1_sig f)) as [t'|]; [|discriminate].
      exact (proj2 (conv_to_scalar_runint ca t' t H)).
Qed.
Lemma wrap_runint_total : forall t z,
  is_int_goty t = true -> numty_eqb t GTInt = false ->
  exists g, wrap_runint t z = Some g.
Proof.
  intros t z Hi Ht; destruct t; try discriminate Hi; try discriminate Ht;
    eexists; reflexivity.
Qed.
(** The raw reading is TOTAL on any payload whose tag matches an INTEGER width (consumed by the
    sealed T2 theorem: the well-taggedness invariant supplies the match). *)
Lemma runint_raw_total : forall s g,
  is_int_goty s = true -> tag_matches s g = true -> exists z, runint_raw g = Some z.
Proof.
  intros s [A [x tag]] Hs Hm; destruct s; try discriminate Hs;
    destruct tag; try discriminate Hm; eexists; reflexivity.
Qed.
(** The conversion SOURCE-shape seal: a [conv_to_scalar] result of [PtRunInt _] can only arise from a
    runtime-int or runtime-float operand (the two runtime rows of the integer-target arm). *)
Lemma conv_to_scalar_runint_src : forall ca t' t,
  conv_to_scalar ca t' = Some (PtRunInt t) ->
  (exists s, ca = PtRunInt s) \/ (exists s, ca = PtRunFloat s).
Proof.
  intros ca t' t H.
  destruct t'; simpl in H; destruct ca; try discriminate H;
    repeat match type of H with
           | (if ?b then _ else _) = _ => destruct b; try discriminate H
           end;
    eauto.
Qed.
Lemma ptype_call_runint_conv_arg : forall f a t,
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  (exists s, ptype a = Some (PtRunInt s)) \/ (exists s, ptype a = Some (PtRunFloat s)).
Proof.
  intros f a t H Ht. cbn [ptype] in H.
  destruct (ptype a) as [ca|] eqn:Hpa; [|discriminate].
  destruct (String.eqb (proj1_sig f) "len").
  - destruct a; destruct ca; try discriminate H;
      inversion H; subst; discriminate Ht.
  - destruct (String.eqb (proj1_sig f) "cap").
    + destruct ca; try discriminate H. inversion H; subst. discriminate Ht.
    + destruct (classify (proj1_sig f)) as [t'|]; [|discriminate].
      destruct (conv_to_scalar_runint_src ca t' t H) as [[s ->]|[s ->]];
        [left|right]; exists s; reflexivity.
Qed.
(** Shape facts scoping the special [len]-fold arms away from the conversion class theorems: a
    slice/map LITERAL classifies [PtAgg]/[PtMap] (never runtime-numeric), an aggregate source never
    converts, and [GTInt] is [classify]-reachable ONLY by the keyword "int". *)
Lemma ptype_slicelit_shape : forall et es p, ptype (ESliceLit et es) = Some p -> p = PtAgg.
Proof.
  intros et es p H. cbn [ptype] in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; try discriminate H
         end.
  injection H as H. subst p. reflexivity.
Qed.
Lemma ptype_maplit_shape : forall kt vt kvs p, ptype (EMapLit kt vt kvs) = Some p -> p = PtMap.
Proof.
  intros kt vt kvs p H. cbn [ptype] in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; try discriminate H
         end.
  injection H as H. subst p. reflexivity.
Qed.
Lemma conv_to_scalar_agg_none : forall t', conv_to_scalar PtAgg t' = None.
Proof. intro t'; destruct t'; reflexivity. Qed.
Lemma conv_to_scalar_map_none : forall t', conv_to_scalar PtMap t' = None.
Proof. intro t'; destruct t'; reflexivity. Qed.
Lemma ptype_call_slicelit_shape : forall f et es p,
  ptype (ECall (EId f) (ESliceLit et es :: nil)) = Some p -> p = PtRunInt GTInt.
Proof.
  intros f et es p H. cbn [ptype] in H.
  match type of H with
  | context [if ?b then Some PtAgg else None] => destruct b
  end; cbv beta iota in H; [|discriminate H].
  destruct (String.eqb (proj1_sig f) "len"); cbv beta iota in H;
  [injection H as <-; reflexivity|].
  destruct (String.eqb (proj1_sig f) "cap"); cbv beta iota in H;
  [injection H as <-; reflexivity|].
  destruct (classify (proj1_sig f)) as [t'|]; cbv beta iota in H;
  [rewrite conv_to_scalar_agg_none in H; discriminate H | discriminate H].
Qed.
Lemma ptype_call_maplit_shape : forall f kt vt kvs p,
  ptype (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some p -> p = PtRunInt GTInt.
Proof.
  intros f kt vt kvs p H. cbn [ptype] in H.
  match type of H with
  | context [if ?b then Some PtMap else None] => destruct b
  end; cbv beta iota in H; [|discriminate H].
  destruct (String.eqb (proj1_sig f) "len"); cbv beta iota in H;
  [injection H as <-; reflexivity|].
  destruct (String.eqb (proj1_sig f) "cap"); cbv beta iota in H;
  [discriminate H|].
  destruct (classify (proj1_sig f)) as [t'|]; cbv beta iota in H;
  [rewrite conv_to_scalar_map_none in H; discriminate H | discriminate H].
Qed.
Lemma classify_gtint_name : forall s, classify s = Some GTInt -> String.eqb s "int" = true.
Proof.
  intros s H. unfold classify in H.
  destruct (String.eqb s "int64"); [discriminate H|].
  destruct (String.eqb s "int32"); [discriminate H|].
  destruct (String.eqb s "int16"); [discriminate H|].
  destruct (String.eqb s "int8");  [discriminate H|].
  destruct (String.eqb s "int") eqn:E; [reflexivity|].
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; try discriminate H
         end.
Qed.
(** A [PtRunInt GTInt]-classified one-arg call with a RUNTIME-INT operand IS the [int(x)] conversion
    (the [len]/[cap] rows contradict the operand's class; [classify] pins the name) — so the sealed
    [int]-target theorem below needs NO name premise. *)
Lemma ptype_call_runint_int_name : forall f a s,
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt GTInt) ->
  ptype a = Some (PtRunInt s) ->
  String.eqb (proj1_sig f) "int" = true.
Proof.
  intros f a s H Hpa. cbn [ptype] in H. rewrite Hpa in H. cbv beta iota in H.
  destruct (String.eqb (proj1_sig f) "len") eqn:El.
  - cbv beta iota in H. destruct a; cbv beta iota in H; discriminate H.
  - destruct (String.eqb (proj1_sig f) "cap") eqn:Ec.
    + cbv beta iota in H. discriminate H.
    + destruct (classify (proj1_sig f)) as [t'|] eqn:Ecl; cbv beta iota in H; [|discriminate H].
      destruct (conv_to_scalar_runint _ _ _ H) as [-> _].
      exact (classify_gtint_name _ Ecl).
Qed.
(** A one-arg call whose OPERAND is a slice/map literal never classifies [PtRunFloat]: [len]/[cap]
    give [PtRunInt]; a conversion of an aggregate source is rejected. *)
Lemma ptype_call_lit_not_runfloat : forall f a s,
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunFloat s) ->
  match a with ESliceLit _ _ | EMapLit _ _ _ => False | _ => True end.
Proof.
  intros f a s H.
  destruct a; try exact I; cbn [ptype] in H.
  - (* ESliceLit *)
    match type of H with
    | context [if ?b then Some PtAgg else None] => destruct b
    end; cbv beta iota in H; [|discriminate H].
    destruct (String.eqb (proj1_sig f) "len"); cbv beta iota in H; [discriminate H|].
    destruct (String.eqb (proj1_sig f) "cap"); cbv beta iota in H; [discriminate H|].
    destruct (classify (proj1_sig f)) as [t'|]; cbv beta iota in H;
      [rewrite conv_to_scalar_agg_none in H; discriminate H | discriminate H].
  - (* EMapLit *)
    match type of H with
    | context [if ?b then Some PtMap else None] => destruct b
    end; cbv beta iota in H; [|discriminate H].
    destruct (String.eqb (proj1_sig f) "len"); cbv beta iota in H; [discriminate H|].
    destruct (String.eqb (proj1_sig f) "cap"); cbv beta iota in H; [discriminate H|].
    destruct (classify (proj1_sig f)) as [t'|]; cbv beta iota in H;
      [rewrite conv_to_scalar_map_none in H; discriminate H | discriminate H].
Qed.

(** ---- The T3 BINOP shape seal: what operand shapes can sit under a [PtRunInt]-classified
    arithmetic binop — both-runtime, or ONE runtime + ONE int-constant ([num_arith]'s mixed rows,
    carrying ptype's own repr/width admission facts).  The sealed T3 theorem covers the WHOLE split:
    an UNTYPED constant operand CONVERTS to the binop's width, a TYPED one is already AT it
    ([typed_operand], width-sealed at the boundary). *)
Lemma numty_eqb_eq : forall t1 t2, numty_eqb t1 t2 = true -> t1 = t2.
Proof. intros t1 t2 H; destruct t1; destruct t2; try discriminate H; reflexivity. Qed.
Lemma dy_fold_at_float : forall t df a b pt,
  dy_fold_at t df a b = Some pt -> exists d, pt = PtFloatConst t d.
Proof.
  intros t df a b pt H. unfold dy_fold_at in H.
  destruct df as [f|]; [|discriminate].
  destruct (f a b) as [[m e']|]; [|discriminate].
  destruct (float_dyadic_repr _ _ _); [|discriminate].
  injection H as <-. eexists. reflexivity.
Qed.
Lemma num_arith_runint_args : forall f df cl cr t,
  num_arith f df cl cr = Some (PtRunInt t) ->
  (cl = PtRunInt t /\ cr = PtRunInt t)
  \/ ((exists z, (cl = PtIntConst z /\ int_const_repr z t = true) \/ cl = PtTIntConst t z)
      /\ cr = PtRunInt t)
  \/ ((exists z, (cr = PtIntConst z /\ int_const_repr z t = true) \/ cr = PtTIntConst t z)
      /\ cl = PtRunInt t).
Proof.
  intros f df cl cr t H.
  destruct cl; destruct cr; cbn [num_arith] in H; try discriminate H;
  repeat match type of H with
         | (if numty_eqb ?x ?y then _ else _) = _ =>
             let E := fresh "E" in destruct (numty_eqb x y) eqn:E;
             [apply numty_eqb_eq in E; subst; cbv beta iota in H | discriminate H]
         | (if ?b then _ else _) = _ =>
             let R := fresh "R" in destruct b eqn:R;
             [cbv beta iota in H | discriminate H]
         end;
  try discriminate H;
  try (let Ed := fresh "Ed" in
       destruct (dy_fold_at_float _ _ _ _ _ H) as [? Ed]; discriminate Ed);
  injection H as He; subst;
  first
    [ (left; split; reflexivity)
    | (right; left; split; [eexists; left; split; [reflexivity | assumption] | reflexivity])
    | (right; left; split; [eexists; right; reflexivity | reflexivity])
    | (right; right; split; [eexists; left; split; [reflexivity | assumption] | reflexivity])
    | (right; right; split; [eexists; right; reflexivity | reflexivity]) ].
Qed.
(** [BAdd]'s string-concatenation row never yields a numeric class — strip it to [num_binop]. *)
Lemma ptype_add_str_row : forall cl cr t,
  (match cl, cr with PtStr, PtStr => Some PtStr | _, _ => num_binop BAdd cl cr end)
    = Some (PtRunInt t) ->
  num_binop BAdd cl cr = Some (PtRunInt t).
Proof. intros cl cr t H; destruct cl; try exact H; destruct cr; try exact H; discriminate H. Qed.
Lemma num_binop_arith_runint : forall o cl cr t,
  typed_arith_op o = true ->
  num_binop o cl cr = Some (PtRunInt t) ->
  (cl = PtRunInt t /\ cr = PtRunInt t)
  \/ ((exists z, (cl = PtIntConst z /\ int_const_repr z t = true) \/ cl = PtTIntConst t z)
      /\ cr = PtRunInt t)
  \/ ((exists z, (cr = PtIntConst z /\ int_const_repr z t = true) \/ cr = PtTIntConst t z)
      /\ cl = PtRunInt t).
Proof.
  intros o cl cr t Ho H.
  destruct o; try discriminate Ho; cbn [num_binop] in H;
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; try discriminate H
         end;
  exact (num_arith_runint_args _ _ _ _ _ H).
Qed.
Lemma ptype_binop_runint_args : forall o a b t,
  typed_arith_op o = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  (ptype a = Some (PtRunInt t) /\ ptype b = Some (PtRunInt t))
  \/ ((exists z, (ptype a = Some (PtIntConst z) /\ int_const_repr z t = true)
                 \/ ptype a = Some (PtTIntConst t z))
      /\ ptype b = Some (PtRunInt t))
  \/ ((exists z, (ptype b = Some (PtIntConst z) /\ int_const_repr z t = true)
                 \/ ptype b = Some (PtTIntConst t z))
      /\ ptype a = Some (PtRunInt t)).
Proof.
  intros o a b t Ho H. cbn [ptype] in H.
  destruct (ptype a) as [cl|] eqn:Ea; [|discriminate H].
  destruct (ptype b) as [cr|] eqn:Eb; [|discriminate H].
  cbv beta iota in H.
  destruct o; try discriminate Ho;
  ( first [ apply ptype_add_str_row in H | idtac ];
    destruct (num_binop_arith_runint _ _ _ _ Ho H)
      as [[-> ->] | [[[z [[-> R] | ->]] ->] | [[z [[-> R] | ->]] ->]]];
    [ left; split; reflexivity
    | right; left; split; [exists z; left; split; [reflexivity | exact R] | reflexivity]
    | right; left; split; [exists z; right; reflexivity | reflexivity]
    | right; right; split; [exists z; left; split; [reflexivity | exact R] | reflexivity]
    | right; right; split; [exists z; right; reflexivity | reflexivity] ] ).
Qed.

(** ---- The T4 COMPARISON shape seal, mirroring the binop one: [num_comparable]'s int rows admit
    both-runtime or one-runtime-one-int-constant at the SAME width ([cmp_width] — the runtime
    operand pins it); the bool/string [eq_comparable] rows and the float rows are excluded by
    [cmp_width] itself. *)
Lemma eq_comparable_num : forall cl cr t,
  eq_comparable cl cr = true ->
  cmp_width (Some cl) (Some cr) = Some t ->
  num_comparable cl cr = true.
Proof.
  intros cl cr t Hc Hw. destruct cl; destruct cr; try exact Hc;
  cbn [cmp_width int_const_val] in Hw; discriminate Hw.
Qed.
Lemma ord_comparable_num : forall cl cr t,
  ord_comparable cl cr = true ->
  cmp_width (Some cl) (Some cr) = Some t ->
  num_comparable cl cr = true.
Proof.
  intros cl cr t Hc Hw. destruct cl; destruct cr; try exact Hc;
  cbn [cmp_width int_const_val] in Hw; discriminate Hw.
Qed.
Lemma num_comparable_width_args : forall cl cr t,
  num_comparable cl cr = true ->
  cmp_width (Some cl) (Some cr) = Some t ->
  numty_eqb t GTInt = false ->
  (cl = PtRunInt t /\ cr = PtRunInt t)
  \/ ((exists z, (cl = PtIntConst z /\ int_const_repr z t = true) \/ cl = PtTIntConst t z)
      /\ cr = PtRunInt t)
  \/ ((exists z, (cr = PtIntConst z /\ int_const_repr z t = true) \/ cr = PtTIntConst t z)
      /\ cl = PtRunInt t).
Proof.
  intros cl cr t Hc Hw Ht.
  destruct cl; destruct cr; cbn [num_comparable] in Hc; try discriminate Hc;
  cbn [cmp_width int_const_val] in Hw; try discriminate Hw;
  injection Hw as He; subst;
  try (apply numty_eqb_eq in Hc; subst);
  first
    [ discriminate Ht
    | (left; split; reflexivity)
    | (right; left; split; [eexists; left; split; [reflexivity | assumption] | reflexivity])
    | (right; left; split; [eexists; right; reflexivity | reflexivity])
    | (right; right; split; [eexists; left; split; [reflexivity | assumption] | reflexivity])
    | (right; right; split; [eexists; right; reflexivity | reflexivity]) ].
Qed.
Lemma ptype_cmp_bool_args : forall o a b t,
  cmp_binop o = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some t ->
  numty_eqb t GTInt = false ->
  (ptype a = Some (PtRunInt t) /\ ptype b = Some (PtRunInt t))
  \/ ((exists z, (ptype a = Some (PtIntConst z) /\ int_const_repr z t = true)
                 \/ ptype a = Some (PtTIntConst t z))
      /\ ptype b = Some (PtRunInt t))
  \/ ((exists z, (ptype b = Some (PtIntConst z) /\ int_const_repr z t = true)
                 \/ ptype b = Some (PtTIntConst t z))
      /\ ptype a = Some (PtRunInt t)).
Proof.
  intros o a b t Ho Hpt Hw Ht. cbn [ptype] in Hpt.
  destruct (ptype a) as [cl|] eqn:Ea; [|discriminate Hpt].
  destruct (ptype b) as [cr|] eqn:Eb; [|discriminate Hpt].
  cbv beta iota in Hpt.
  destruct o; try discriminate Ho;
  ( match type of Hpt with
    | (if ?c then _ else _) = _ =>
        let Ec := fresh "Ec" in destruct c eqn:Ec; [|discriminate Hpt]
    end;
    let Hn := fresh "Hn" in
    assert (Hn : num_comparable cl cr = true)
      by (first [ exact (eq_comparable_num _ _ _ Ec Hw)
                | exact (ord_comparable_num _ _ _ Ec Hw) ]);
    destruct (num_comparable_width_args _ _ _ Hn Hw Ht)
      as [[-> ->] | [[[z [[-> R] | ->]] ->] | [[z [[-> R] | ->]] ->]]];
    [ left; split; reflexivity
    | right; left; split; [exists z; left; split; [reflexivity | exact R] | reflexivity]
    | right; left; split; [exists z; right; reflexivity | reflexivity]
    | right; right; split; [exists z; left; split; [reflexivity | exact R] | reflexivity]
    | right; right; split; [exists z; right; reflexivity | reflexivity] ] ).
Qed.

(** ---- The T5 SHIFT shape seal: a [PtRunInt t]-classified shift ([t] ≠ [GTInt]) has a LEFT
    operand that is runtime-at-[t] or a typed constant AT [t] ([ptype]'s own shift rows), and a
    COUNT that is a runtime integer of SOME width or an int constant ([is_int_cat], nonneg by
    [is_neg_const]). *)
Lemma ptype_shift_runint_args : forall o a b t,
  shift_op o = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  (ptype a = Some (PtRunInt t) \/ (exists z', ptype a = Some (PtTIntConst t z')))
  /\ ((exists s, ptype b = Some (PtRunInt s))
      \/ (exists cb z0, ptype b = Some cb /\ int_const_val cb = Some z0)).
Proof.
  intros o a b t Ho Hpt Ht. cbn [ptype] in Hpt.
  destruct (ptype a) as [cl|] eqn:Ea; [|discriminate Hpt].
  destruct (ptype b) as [cr|] eqn:Eb; [|discriminate Hpt].
  cbv beta iota in Hpt.
  destruct o; try discriminate Ho;
  ( cbn [num_binop] in Hpt;
    match type of Hpt with
    | (if ?bb then _ else _) = _ =>
        let E := fresh "E" in
        destruct bb eqn:E; cbv beta iota in Hpt; [|discriminate Hpt]
    end;
    apply andb_true_iff in E; destruct E as [Eil Eir];
    repeat match type of Hpt with
    | (if ?bb then _ else _) = _ =>
        destruct bb; cbv beta iota in Hpt; [discriminate Hpt|]
    end;
    destruct cl; cbv beta iota in Hpt; try discriminate Hpt;
    [ (destruct (int_const_val cr) eqn:Ec; cbv beta iota in Hpt;
       [ repeat match type of Hpt with
                | (if ?bb then _ else _) = _ =>
                    destruct bb; cbv beta iota in Hpt; try discriminate Hpt
                end; try discriminate Hpt
       | injection Hpt as <-; discriminate Ht ])
    | (destruct (int_const_val cr) eqn:Ec; cbv beta iota in Hpt;
       [ repeat match type of Hpt with
                | (if ?bb then _ else _) = _ =>
                    destruct bb; cbv beta iota in Hpt; try discriminate Hpt
                end; try discriminate Hpt
       | injection Hpt as <-; split;
         [ right; eexists; reflexivity
         | destruct cr; try discriminate Eir;
           try (cbn in Ec; discriminate Ec);
           left; eexists; reflexivity ] ])
    | (injection Hpt as <-; split;
       [ left; reflexivity
       | destruct cr; try discriminate Eir;
         first [ (left; eexists; reflexivity)
               | (right; eexists; eexists; split; reflexivity) ] ]) ] ).
Qed.

(** A [rexit_with] exit fires only for [PtRunInt]/[PtBool]-classified nodes — any other class
    computes [None] (feeds the count layer's const-totality: a const-classified operand's value can
    only come from the FOLD). *)
Lemma rexit_nonexit_class_none : forall e c,
  ptype e = Some c ->
  match c with PtRunInt _ => false | PtBool => false | _ => true end = true ->
  rexit_with reval_int (reval_val_with reval_int) e = None.
Proof.
  intros e c Hpt Hc.
  destruct e as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c0 e0|et es|kt vt kvs|str|hx];
    cbn [rexit_with]; try reflexivity.
  - rewrite Hpt. destruct c; try discriminate Hc; reflexivity.
  - rewrite Hpt. destruct c; try discriminate Hc; reflexivity.
  - destruct fn; try reflexivity.
    destruct args as [|a0 [|? ?]]; try reflexivity.
    rewrite Hpt. destruct c; try discriminate Hc; reflexivity.
Qed.

(** ---- The classifier's TYPED-CONST REPR invariant: every [PtTIntConst t z] the classifier
    produces has [z] representable at [t] — every producing row re-checks [int_const_repr], so this
    is a one-level case walk, not an induction.  Feeds the T3 operand width seal's totality
    ([typed_operand_const_total]). *)
Lemma num_arith_tint_repr : forall f df cl cr t z,
  num_arith f df cl cr = Some (PtTIntConst t z) -> int_const_repr z t = true.
Proof.
  intros f df cl cr t z H.
  destruct cl; destruct cr; cbn [num_arith] in H; try discriminate H;
  repeat first
    [ discriminate H
    | (injection H as H1 H2; subst; assumption)
    | (let Ed := fresh "Ed" in
       destruct (dy_fold_at_float _ _ _ _ _ H) as [? Ed]; discriminate Ed)
    | (cbv beta iota zeta in H;
       match type of H with
       | (if ?b then _ else _) = _ =>
           let R := fresh "R" in destruct b eqn:R; [ idtac | try discriminate H ]
       | context [match ?x with _ => _ end] => destruct x
       end) ].
Qed.
Lemma ptype_add_str_row_tint : forall cl cr t z,
  (match cl, cr with PtStr, PtStr => Some PtStr | _, _ => num_binop BAdd cl cr end)
    = Some (PtTIntConst t z) ->
  num_binop BAdd cl cr = Some (PtTIntConst t z).
Proof. intros cl cr t z H; destruct cl; try exact H; destruct cr; try exact H; discriminate H. Qed.
Lemma num_binop_tint_repr : forall o cl cr t z,
  num_binop o cl cr = Some (PtTIntConst t z) -> int_const_repr z t = true.
Proof.
  intros o cl cr t z H.
  destruct o; cbn [num_binop] in H;
  repeat first
    [ discriminate H
    | exact (num_arith_tint_repr _ _ _ _ _ _ H)
    | (injection H as H1 H2; subst; assumption)
    | (cbv beta iota zeta in H;
       match type of H with
       | (if ?b then _ else _) = _ =>
           let R := fresh "R" in destruct b eqn:R; [ idtac | try discriminate H ]
       | context [match ?x with _ => _ end] => destruct x
       end) ].
Qed.
Lemma conv_to_scalar_tint_repr : forall ca t' t z,
  conv_to_scalar ca t' = Some (PtTIntConst t z) -> int_const_repr z t = true.
Proof.
  intros ca t' t z H.
  destruct t'; destruct ca; cbn [conv_to_scalar] in H; try discriminate H;
  repeat first
    [ discriminate H
    | (injection H as H1 H2; subst; assumption)
    | (cbv beta iota zeta in H;
       match type of H with
       | (if ?b then _ else _) = _ =>
           let R := fresh "R" in destruct b eqn:R; [ idtac | try discriminate H ]
       | context [match ?x with _ => _ end] => destruct x
       end) ].
Qed.
Lemma ptype_tint_const_repr : forall e t z,
  ptype e = Some (PtTIntConst t z) -> int_const_repr z t = true.
Proof.
  intros e t z H.
  destruct e; cbn [ptype] in H; try discriminate H;
  repeat first
    [ discriminate H
    | exact (conv_to_scalar_tint_repr _ _ _ _ H)
    | exact (num_binop_tint_repr _ _ _ _ _ H)
    | exact (num_binop_tint_repr _ _ _ _ _ (ptype_add_str_row_tint _ _ _ _ H))
    | (injection H as H1 H2; subst; assumption)
    | (cbv beta iota zeta in H;
       match type of H with
       | (if ?b then _ else _) = _ =>
           let R := fresh "R" in destruct b eqn:R; [ idtac | try discriminate H ]
       | context [match ?x with _ => _ end] => destruct x
       end) ].
Qed.
Lemma denote_expr_conv_runs : forall f a t g z,
  floats_checked (ECall (EId f) (a :: nil)) = true ->
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  eval_value (ECall (EId f) (a :: nil)) = None ->
  reval_val a = Some (RAVal g) ->
  runint_raw g = Some z ->
  exists g', wrap_runint t z = Some g'
    /\ denote_expr (ECall (EId f) (a :: nil)) = Some (CRet g', false).
Proof.
  intros f a t g z Hfc Hpt Ht Hev Ha Hz.
  destruct (wrap_runint_total t z
              (ptype_call_runint_conv f a t Hpt Ht) Ht) as [g' Hw].
  exists g'. split; [exact Hw|].
  assert (He : reval_int (ECall (EId f) (a :: nil)) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (ECall (EId f) (a :: nil))
                = Some (RAVal g')).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Hz. cbv beta iota. rewrite Hw. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
Lemma denote_expr_conv_panic : forall f a t p,
  floats_checked (ECall (EId f) (a :: nil)) = true ->
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  eval_value (ECall (EId f) (a :: nil)) = None ->
  reval_val a = Some (RAPanic p) ->
  denote_expr (ECall (EId f) (a :: nil)) = Some (CPan p, true).
Proof.
  intros f a t p Hfc Hpt Ht Hev Ha.
  assert (He : reval_int (ECall (EId f) (a :: nil)) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (ECall (EId f) (a :: nil))
                = Some (RAPanic p)).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.

(** ★ CLASS (tier R4) — the runtime bool COMPARISON denotation theorems, quantified over the whole
    reval-evaluable fragment: a binop [ptype] classifies [PtBool] whose op is a COMPARISON
    ([cmp_verdict o = Some cmp] — the class-scoping dispatch; [&&]/[||] are [None] there) and whose
    operands both evaluate in the [GTInt] runtime fragment denotes to the model's own verdict, boxed
    [TBool].  A panicking operand panics LEFT-to-right (Go's order), before any comparison. *)
Lemma denote_expr_cmp_runs : forall o a b va vb cmp,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some GTInt ->
  eval_value (EBn o a b) = None ->
  cmp_verdict o = Some cmp ->
  reval_int a = Some (RVal va) ->
  reval_int b = Some (RVal vb) ->
  denote_expr (EBn o a b) = Some (CRet (anyt TBool (cmp va vb)), false).
Proof.
  intros o a b va vb cmp Hfc Hpt Hw Hev Hc Ha Hb.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, He. cbv beta iota.
  unfold rexit_with. cbv beta iota.
  rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota.
  cbn [numty_eqb]. cbv beta iota.
  rewrite Hc. cbv beta iota.
  rewrite Ha. cbv beta iota. rewrite Hb. reflexivity.
Qed.
Lemma denote_expr_cmp_left_panic : forall o a b p cmp,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some GTInt ->
  eval_value (EBn o a b) = None ->
  cmp_verdict o = Some cmp ->
  reval_int a = Some (RPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b p cmp Hfc Hpt Hw Hev Hc Ha.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, He. cbv beta iota.
  unfold rexit_with. cbv beta iota.
  rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota.
  cbn [numty_eqb]. cbv beta iota.
  rewrite Hc. cbv beta iota.
  rewrite Ha. reflexivity.
Qed.
Lemma denote_expr_cmp_right_panic : forall o a b va p cmp,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some GTInt ->
  eval_value (EBn o a b) = None ->
  cmp_verdict o = Some cmp ->
  reval_int a = Some (RVal va) ->
  reval_int b = Some (RPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b va p cmp Hfc Hpt Hw Hev Hc Ha Hb.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, He. cbv beta iota.
  unfold rexit_with. cbv beta iota.
  rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota.
  cbn [numty_eqb]. cbv beta iota.
  rewrite Hc. cbv beta iota.
  rewrite Ha. cbv beta iota. rewrite Hb. reflexivity.
Qed.

(** ★ CLASS (tier R5) — the map-value [len] denotation theorems, quantified over the whole
    reval-evaluable fragment: [len] of a map literal [ptype] classifies [PtRunInt GTInt] (which forces
    ALL-CONSTANT DISTINCT keys — [ptype]'s map arm), under the fold arm's own side conditions, whose
    VALUES all evaluate through the SHARED evaluator ([rconstr_vals] = the same [reval_val_with
    reval_int] pipeline [denote_expr] consumes — R3/R4-form values included) denotes to the
    DISTINCT-KEY COUNT (boxed through the checked
    [rval_len] — [int_const_repr] on the count is the fail-closed representability boundary, discharged
    by [rval_len_repr]); a SINGLE panicking VALUE panics — order-independence sealed by the walker's
    class theorems ([rconstr_vals_panic_sound]/[rconstr_vals_two_panics_absent]). *)
Lemma denote_expr_maplen_runs : forall f kt vt kvs,
  floats_checked (ECall (EId f) (EMapLit kt vt kvs :: nil)) = true ->
  ptype (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some (PtRunInt GTInt) ->
  eval_value (ECall (EId f) (EMapLit kt vt kvs :: nil)) = None ->
  (String.eqb (proj1_sig f) "len" && is_int_goty kt && goty_supported vt
     && nodup_z (map_key_vals kvs))%bool = true ->
  rconstr_vals kvs = Some RCOk ->
  int_const_repr (Z.of_nat (length kvs)) GTInt = true ->
  denote_expr (ECall (EId f) (EMapLit kt vt kvs :: nil))
    = Some (CRet (anyt TInt64 (intwrap (Z.of_nat (length kvs)))), false).
Proof.
  intros f kt vt kvs Hfc Hpt Hev Hcond Hvals Hrepr.
  assert (Hr : reval_int (ECall (EId f) (EMapLit kt vt kvs :: nil))
               = Some (RVal (intwrap (Z.of_nat (length kvs))))).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbn [numty_eqb negb].
    rewrite Hcond. cbv beta iota.
    unfold rconstr_vals in Hvals. rewrite Hvals. cbv beta iota.
    exact (rval_len_repr (length kvs) Hrepr). }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_maplen_panic : forall f kt vt kvs p,
  floats_checked (ECall (EId f) (EMapLit kt vt kvs :: nil)) = true ->
  ptype (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some (PtRunInt GTInt) ->
  eval_value (ECall (EId f) (EMapLit kt vt kvs :: nil)) = None ->
  (String.eqb (proj1_sig f) "len" && is_int_goty kt && goty_supported vt
     && nodup_z (map_key_vals kvs))%bool = true ->
  rconstr_vals kvs = Some (RCPanic p) ->
  denote_expr (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some (CPan p, true).
Proof.
  intros f kt vt kvs p Hfc Hpt Hev Hcond Hvals.
  assert (Hr : reval_int (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbn [numty_eqb negb].
    rewrite Hcond. cbv beta iota.
    unfold rconstr_vals in Hvals. rewrite Hvals. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.

(** ---- THE WELL-TAGGEDNESS SEAL (T1's open obligation, closed) ----
    [ptype_int_ok]: every [PtRunInt t]/[PtTIntConst t _] the classifier produces carries an INTEGER
    keyword width.  [reval_val_typed]: a [reval_val] VALUE's tag matches its [ptype] width — so the
    typed-unary dispatch is total on the live cells with NO caller-side premise
    ([denote_expr_typed_unop_runs_sealed]). *)
Definition pty_int_ok (p : PTy) : bool :=
  match p with PtRunInt t | PtTIntConst t _ => is_int_goty t | _ => true end.
Lemma num_arith_int_ok : forall f df cl cr pt,
  pty_int_ok cl = true -> pty_int_ok cr = true ->
  num_arith f df cl cr = Some pt -> pty_int_ok pt = true.
Proof.
  intros f df cl cr pt Hl Hr H.
  destruct cl; destruct cr; cbn in *; try discriminate H;
    repeat match type of H with
           | (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate H
           end;
    try (injection H as <-; cbn in *; first [assumption | reflexivity]);
    apply dy_fold_at_float in H; destruct H as [dcst ->]; reflexivity.
Qed.
Lemma num_binop_int_ok : forall o cl cr pt,
  pty_int_ok cl = true -> pty_int_ok cr = true ->
  num_binop o cl cr = Some pt -> pty_int_ok pt = true.
Proof.
  intros o cl cr pt Hl Hr H. destruct o; cbn in H; try discriminate H;
    try (exact (num_arith_int_ok _ _ _ _ _ Hl Hr H));
    repeat match type of H with
           | (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate H
           end;
    try (exact (num_arith_int_ok _ _ _ _ _ Hl Hr H)).
  (* the shift arm: outputs untyped-const fold / PtRunInt GTInt / typed rows carrying an input width *)
  all: destruct cl; try discriminate H; cbn in Hl;
       try (destruct (int_const_val cr) as [b0|] eqn:Ecv);
       repeat match type of H with
              | (if ?b then _ else _) = _ => destruct b eqn:?; try discriminate H
              end;
       injection H as <-; cbn; first [assumption | reflexivity].
Qed.
Lemma conv_to_scalar_int_ok : forall ca t' pt,
  conv_to_scalar ca t' = Some pt -> pty_int_ok pt = true.
Proof.
  intros ca t' pt H.
  destruct t'; simpl in H; destruct ca; try discriminate H;
    repeat match type of H with
           | (if ?b then _ else _) = _ => destruct b; try discriminate H
           end;
    injection H as <-; reflexivity.
Qed.
Lemma ptype_int_ok : forall e pt, ptype e = Some pt -> pty_int_ok pt = true.
Proof.
  induction e using GExpr_ind'; intros pt Hp; cbn [ptype] in Hp.
  - (* EId *) destruct (String.eqb _ _); [injection Hp as <-; reflexivity | discriminate Hp].
  - (* EInt *) injection Hp as <-. reflexivity.
  - (* EUn *)
    destruct (ptype e) as [c|]; [|discriminate Hp].
    specialize (IHe _ eq_refl).
    destruct o; try discriminate Hp.
    + (* UNot *) destruct c; try discriminate Hp. injection Hp as <-. reflexivity.
    + (* UXor *) destruct c; try discriminate Hp; cbv zeta in Hp;
        try (destruct (complement_const _ _) as [r|] eqn:Ecc in Hp; try discriminate Hp);
        repeat match type of Hp with
               | (if ?b then _ else _) = _ => destruct b; try discriminate Hp
               end;
        injection Hp as <-; cbn in *; first [assumption | reflexivity].
    + (* UNeg *) destruct c; try discriminate Hp; cbv zeta in Hp;
        repeat match type of Hp with
               | (if ?b then _ else _) = _ => destruct b; try discriminate Hp
               end;
        injection Hp as <-; cbn in *; first [assumption | reflexivity].
  - (* EBn *)
    destruct (ptype e1) as [cl|]; [|discriminate Hp].
    destruct (ptype e2) as [cr|]; [|discriminate Hp].
    specialize (IHe1 _ eq_refl). specialize (IHe2 _ eq_refl).
    destruct o;
      try (exact (num_binop_int_ok _ _ _ _ IHe1 IHe2 Hp));
      try (destruct cl; destruct cr; try discriminate Hp;
           first [ injection Hp as <-; reflexivity
                 | exact (num_binop_int_ok _ _ _ _ IHe1 IHe2 Hp) ]);
      try (destruct (eq_comparable _ _); [injection Hp as <-; reflexivity | discriminate Hp]);
      try (destruct (ord_comparable _ _); [injection Hp as <-; reflexivity | discriminate Hp]);
      try (destruct (andb _ _); [injection Hp as <-; reflexivity | discriminate Hp]).
  - (* ESel *) discriminate Hp.
  - (* EIndex *)
    destruct e1; try discriminate Hp.
    destruct (andb _ _) eqn:Eg; [|discriminate Hp].
    apply andb_true_iff in Eg as [Ei _].
    destruct (ptype e2) as [ci|]; [|discriminate Hp].
    destruct (is_int_cat ci); [|discriminate Hp].
    destruct (int_const_val ci) as [k|];
      [destruct (andb _ _); [|discriminate Hp]|];
      injection Hp as <-; exact Ei.
  - (* ESlice *) discriminate Hp.
  - (* ECall *)
    destruct e; try discriminate Hp.
    destruct args as [|a [|? ?]]; try discriminate Hp.
    destruct (ptype a) as [ca|]; [|discriminate Hp].
    destruct (String.eqb (proj1_sig i) "len").
    + destruct a; try destruct ca; try discriminate Hp; injection Hp as <-; reflexivity.
    + destruct (String.eqb (proj1_sig i) "cap").
      * destruct ca; try discriminate Hp. injection Hp as <-. reflexivity.
      * destruct (classify (proj1_sig i)) as [t'|]; [|discriminate Hp].
        exact (conv_to_scalar_int_ok _ _ _ Hp).
  - (* EAssert *) discriminate Hp.
  - (* EConv *)
    destruct c; try discriminate Hp;
      destruct (goty_supported _); try discriminate Hp;
      destruct (ptype e) as [c0|]; try discriminate Hp;
      destruct c0; try discriminate Hp; injection Hp as <-; reflexivity.
  - (* ESliceLit *)
    destruct (andb _ _); [injection Hp as <-; reflexivity | discriminate Hp].
  - (* EMapLit *)
    destruct (andb _ _); [injection Hp as <-; reflexivity | discriminate Hp].
  - (* EStr *) injection Hp as <-. reflexivity.
  - (* EHex *) injection Hp as <-. reflexivity.
Qed.

(* Support seals for [reval_val_typed]. *)
Lemma box_int_tag : forall t z g, box_int t z = Some g -> tag_matches t g = true.
Proof.
  intros t z g H. unfold box_int in H.
  destruct (int_const_repr z t); [|discriminate H].
  destruct t; try discriminate H; try (injection H as <-; reflexivity).
  (* GTUint via the mk_uint convoy *)
  unfold mk_uint in H.
  assert (K : forall b (pf : in_u64 z = b),
            (match b as b0 return (in_u64 z = b0 -> option GoAny) with
             | true  => fun pf0 => Some (anyt TUint (uint_lit z pf0))
             | false => fun _   => None
             end) pf = Some g -> tag_matches GTUint g = true).
  { intros b pf Hb. destruct b; [injection Hb as <-; reflexivity | discriminate Hb]. }
  exact (K _ eq_refl H).
Qed.
Lemma wrap_runint_tag : forall t z g, wrap_runint t z = Some g -> tag_matches t g = true.
Proof. intros t z g H; destruct t; try discriminate H; injection H as <-; reflexivity. Qed.
Lemma eval_int_slice_elems_tags : forall t es vs,
  eval_int_slice_elems t es = Some vs ->
  forall v, In v vs -> tag_matches t v = true.
Proof.
  intros t es; induction es as [|e es' IH]; intros vs H v Hin; cbn in H.
  - injection H as <-. destruct Hin.
  - destruct (ptype e) as [ce|]; [|discriminate H].
    destruct (assignable_to_ty ce t); [|discriminate H].
    destruct (int_const_val ce) as [z|]; [|discriminate H].
    destruct (box_int t z) as [g0|] eqn:Hb; [|discriminate H].
    destruct (eval_int_slice_elems t es') as [vs'|] eqn:He; [|discriminate H].
    injection H as <-. destruct Hin as [<-|Hin].
    + exact (box_int_tag _ _ _ Hb).
    + exact (IH _ eq_refl _ Hin).
Qed.

Lemma reval_int_runint : forall a r,
  eval_value a = None -> reval_int a = Some r -> ptype a = Some (PtRunInt GTInt).
Proof.
  intros a r Hev Hr; destruct a; cbn [reval_int] in Hr; rewrite Hev in Hr; cbv beta iota in Hr;
    destruct (ptype _) as [pt|] eqn:Ept; try discriminate Hr;
    destruct pt; try discriminate Hr;
    match type of Hr with
    | (if negb (numty_eqb ?tt GTInt) then _ else _) = _ =>
        destruct (numty_eqb tt GTInt) eqn:Et; cbn in Hr; try discriminate Hr;
        (assert (tt = GTInt) by (destruct tt; cbn in Et; congruence); subst; first [reflexivity | exact Ept])
    end.
Qed.
Lemma eval_value_runint_tag : forall a t v,
  ptype a = Some (PtRunInt t) -> eval_value a = Some v -> tag_matches t v = true.
Proof.
  intros a t v Hpt Hv. unfold eval_value in Hv.
  destruct (floats_checked a); [|discriminate Hv].
  destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
    cbn [eval_value_core] in Hv;
    try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv).
  - (* EIndex e1 e2 *)
    destruct e1 as [| | | | | | | | | |et es| | |];
      try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv).
    cbn [ptype] in Hpt.
    destruct (is_int_goty et) eqn:Ei; [|discriminate Hv].
    cbn [andb] in Hpt. cbv beta iota in Hv.
    match type of Hpt with
    | context [forallb ?f es] => destruct (forallb f es) eqn:Ef; [|discriminate Hpt]
    end.
    cbv beta iota in Hpt.
    destruct (ptype e2) as [ci|]; [|discriminate Hv].
    cbv beta iota in Hv, Hpt.
    destruct (is_int_cat ci) eqn:Eic; [|discriminate Hpt].
    cbv beta iota in Hpt.
    destruct (int_const_val ci) as [k|] eqn:Ecv; [|discriminate Hv].
    cbv beta iota in Hv, Hpt.
    match type of Hv with
    | context [if ?b then _ else _] => destruct b eqn:Ek; [|discriminate Hv]
    end.
    cbv beta iota in Hv, Hpt.
    destruct (eval_int_slice_elems et es) as [vs|] eqn:Ee; [|discriminate Hv].
    cbv beta iota in Hv.
    injection Hpt as <-.
    exact (eval_int_slice_elems_tags _ _ _ Ee _ (nth_error_In _ _ Hv)).
  - (* ECall fn args *)
    destruct fn as [i| | | | | | | | | | | | |];
      try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv).
    destruct args as [|a0 [|? ?]];
      try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv);
      [| destruct a0; unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv ].
    destruct a0 as [| | | | | | | | | |et es|mkt mvt mkvs| |];
      try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv).
    + (* len of ESliceLit *)
      destruct (andb (String.eqb (proj1_sig i) "len") (is_int_goty et)) eqn:Ea;
        [|unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv].
      destruct (eval_int_slice_elems et es) as [vs|]; [|discriminate Hv].
      apply andb_true_iff in Ea as [El' _].
      cbn [ptype] in Hpt.
      match type of Hpt with
      | context [if ?b then Some PtAgg else None] =>
          destruct b; cbv beta iota in Hpt; [|discriminate Hpt]
      end.
      rewrite El' in Hpt. cbv beta iota in Hpt.
      injection Hpt as <-. exact (box_int_tag _ _ _ Hv).
    + (* len of EMapLit *)
      destruct (andb _ _) eqn:Ea;
        [|unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; discriminate Hv].
      apply andb_true_iff in Ea as [Ea1 _]. apply andb_true_iff in Ea1 as [Ea2 _].
      apply andb_true_iff in Ea2 as [Ea3 _]. apply andb_true_iff in Ea3 as [El' _].
      cbn [ptype] in Hpt.
      match type of Hpt with
      | context [if ?b then Some PtMap else None] =>
          destruct b; cbv beta iota in Hpt; [|discriminate Hpt]
      end.
      rewrite El' in Hpt. cbv beta iota in Hpt.
      injection Hpt as <-. exact (box_int_tag _ _ _ Hv).
Qed.

(** NO runtime-float expression EVALUATES (the constant fold): [eval_value]'s ptype-driven default is
    [None] on [PtRunFloat], and the special fold arms (slice-index / [len]) never classify
    [PtRunFloat] — the eval half of the runtime-float ABSENCE class. *)
Lemma eval_value_runfloat_none : forall a s,
  ptype a = Some (PtRunFloat s) -> eval_value a = None.
Proof.
  intros a s Hpt. unfold eval_value.
  destruct (floats_checked a); [|reflexivity].
  destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
    cbn [eval_value_core];
    try (unfold eval_value_ptype_core; rewrite Hpt; reflexivity).
  - (* EIndex: the slice-index fold's [ptype] leaves are [PtRunInt]/[None] *)
    destruct e1 as [| | | | | | | | | |t es| | |];
      try (unfold eval_value_ptype_core; rewrite Hpt; reflexivity).
    exfalso. cbn [ptype] in Hpt.
    repeat match type of Hpt with
           | (if ?b then _ else _) = _ => destruct b; try discriminate Hpt
           | (match ?x with Some _ => _ | None => _ end) = _ =>
               destruct x; try discriminate Hpt
           end.
  - (* ECall: the [len]-fold arms need a literal arg, whose call never classifies [PtRunFloat] *)
    destruct fn as [i| | | | | | | | | | | | |];
      try (unfold eval_value_ptype_core; rewrite Hpt; reflexivity).
    destruct args as [|a0 [|? ?]];
      try (unfold eval_value_ptype_core; rewrite Hpt; reflexivity);
      [| destruct a0; unfold eval_value_ptype_core; rewrite Hpt; reflexivity ].
    pose proof (ptype_call_lit_not_runfloat i a0 s Hpt) as Hlit.
    destruct a0 as [| | | | | | | | | |t es|mkt mvt mkvs| |];
      try (unfold eval_value_ptype_core; rewrite Hpt; reflexivity);
      destruct Hlit.
Qed.

(** The FOLD's tag for CONST-classified expressions: an untyped int constant boxes at [GTInt]'s
    tag, a typed one at ITS width (feeds the shift count's const-totality). *)
Lemma eval_value_const_int_tag : forall e v,
  eval_value e = Some v ->
  match ptype e with
  | Some (PtIntConst _) => tag_matches GTInt v = true
  | Some (PtTIntConst s _) => tag_matches s v = true
  | _ => True
  end.
Proof.
  intros e v Hv.
  destruct (ptype e) as [c|] eqn:Hpt; [|exact I].
  destruct c; try exact I;
  ( unfold eval_value in Hv; destruct (floats_checked e); [|discriminate Hv];
    destruct e as [i|z0|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c0 e0|et es|kt vt kvs|str|hx];
      cbn [eval_value_core] in Hv;
      try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; cbv beta iota in Hv;
           exact (box_int_tag _ _ _ Hv));
    [ destruct e1 as [| | | | | | | | | |t0 es0| | |];
        try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; cbv beta iota in Hv;
             exact (box_int_tag _ _ _ Hv));
      exfalso; cbn [ptype] in Hpt;
      repeat match type of Hpt with
             | (if ?bb then _ else _) = _ => destruct bb; try discriminate Hpt
             | (match ?x with Some _ => _ | None => _ end) = _ =>
                 destruct x; try discriminate Hpt
             end
    | destruct fn as [i0| | | | | | | | | | | | |];
        try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; cbv beta iota in Hv;
             exact (box_int_tag _ _ _ Hv));
      destruct args as [|a0 [|? ?]];
        try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; cbv beta iota in Hv;
             exact (box_int_tag _ _ _ Hv));
        [| destruct a0; unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv;
           cbv beta iota in Hv; exact (box_int_tag _ _ _ Hv) ];
      destruct a0 as [| | | | | | | | | |t0 es0|mkt mvt mkvs| |];
        try (unfold eval_value_ptype_core in Hv; rewrite Hpt in Hv; cbv beta iota in Hv;
             exact (box_int_tag _ _ _ Hv));
      [ pose proof (ptype_call_slicelit_shape _ _ _ _ Hpt) as Esh; discriminate Esh
      | pose proof (ptype_call_maplit_shape _ _ _ _ _ Hpt) as Esh; discriminate Esh ] ] ).
Qed.

(** THE WELL-TAGGEDNESS INVARIANT — a [reval_val] VALUE's tag matches its [ptype] width.  A destruct,
    not an induction: each exit's result tag comes from its own dispatch seal ([wrap_runint_tag],
    [typed_unop_tag_exact]); the fold and the GTInt engine come from [eval_value_runint_tag] and
    [reval_int_runint]. *)
Theorem reval_val_typed : forall a t g,
  ptype a = Some (PtRunInt t) ->
  reval_val a = Some (RAVal g) ->
  tag_matches t g = true.
Proof.
  intros a t g Hpt Hg. unfold reval_val in Hg. rewrite reval_val_with_eq in Hg.
  destruct (eval_value a) as [v|] eqn:Hev.
  { injection Hg as <-. exact (eval_value_runint_tag a t v Hpt Hev). }
  destruct (reval_int a) as [[x|p]|] eqn:Hri.
  { injection Hg as <-.
    pose proof (reval_int_runint a _ Hev Hri) as Hgi.
    rewrite Hpt in Hgi. injection Hgi as ->. reflexivity. }
  { discriminate Hg. }
  destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
    cbn [rexit_with] in Hg; try discriminate Hg.
  - (* EUn: the T1 arm *)
    rewrite Hpt in Hg. cbv beta iota in Hg.
    destruct (numty_eqb t GTInt); cbv beta iota in Hg; [discriminate Hg|].
    destruct (reval_val_with reval_int a0) as [[g'|p]|]; cbv beta iota in Hg; try discriminate Hg.
    destruct (typed_unop o t g') as [g''|] eqn:Hu; cbv beta iota in Hg; [|discriminate Hg].
    injection Hg as <-. exact (proj2 (typed_unop_tag_exact _ _ _ _ Hu)).
  - (* EBn: the R4 bool exit is excluded by [Hpt]; the T3 typed-arith exit's result tag comes from
       its own dispatch seal *)
    rewrite Hpt in Hg. cbv beta iota in Hg.
    destruct (numty_eqb t GTInt); cbv beta iota in Hg; [discriminate Hg|].
    destruct (typed_operand (reval_val_with reval_int) t l) as [[ga|p]|];
      cbv beta iota in Hg; try discriminate Hg.
    destruct (typed_arith_op o); cbv beta iota in Hg.
    + destruct (typed_operand (reval_val_with reval_int) t r) as [[gb|p]|];
        cbv beta iota in Hg; try discriminate Hg.
      exact (proj2 (proj2 (typed_binop_tag_exact _ _ _ _ _ Hg))).
    + destruct (shift_op o); cbv beta iota in Hg; [|discriminate Hg].
      destruct (shift_count (reval_val_with reval_int) r) as [[z|p]|];
        cbv beta iota in Hg; try discriminate Hg.
      exact (proj2 (typed_shift_tag_exact _ _ _ _ _ Hg)).
  - (* ECall: the R3+T2 exit *)
    destruct fn; try discriminate Hg.
    destruct args as [|a0 [|? ?]]; try discriminate Hg.
    rewrite Hpt in Hg. cbv beta iota in Hg.
    destruct (numty_eqb t GTInt); cbv beta iota in Hg; [discriminate Hg|].
    destruct (reval_val_with reval_int a0) as [[g0|p]|]; cbv beta iota in Hg; try discriminate Hg.
    destruct (runint_raw g0) as [z|]; cbv beta iota in Hg; [|discriminate Hg].
    destruct (wrap_runint t z) as [g'|] eqn:Hw; cbv beta iota in Hg; [|discriminate Hg].
    injection Hg as <-. exact (wrap_runint_tag _ _ _ Hw).
Qed.
(** THE RUNTIME-FLOAT ABSENCE CLASS THEOREM (evaluator level): NO [PtRunFloat]-classified expression
    evaluates — not the fold ([eval_value_runfloat_none]), not the [GTInt] engine (its [PtRunInt]
    guard), not an exit (each arm's [ptype]/[PtBool] guard).  QUANTIFIED over the class, so no
    consumer — a conversion source, a map value, a typed-unary operand — can receive a runtime-float
    value before the float arc models one. *)
Theorem reval_val_runfloat_none : forall a s,
  ptype a = Some (PtRunFloat s) -> reval_val a = None.
Proof.
  intros a s Hpt. unfold reval_val. rewrite reval_val_with_eq.
  rewrite (eval_value_runfloat_none a s Hpt).
  assert (Hri : reval_int a = None).
  { destruct a; cbn [reval_int];
      rewrite (eval_value_runfloat_none _ _ Hpt); cbv beta iota;
      rewrite Hpt; reflexivity. }
  rewrite Hri. cbv beta iota.
  destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
    cbn [rexit_with]; try reflexivity.
  - (* EUn *) rewrite Hpt. reflexivity.
  - (* EBn *) rewrite Hpt. reflexivity.
  - (* ECall *)
    destruct fn; try reflexivity.
    destruct args as [|a0 [|? ?]]; try reflexivity.
    rewrite Hpt. reflexivity.
Qed.
(** ---- The OPERAND layer sealed ([typed_operand]): the runtime row IS the full evaluator, the
    const row is TOTAL on [ptype]'s own admitted shapes and tags at the WIDTH, and a panic can only
    come from the runtime row. *)
Lemma typed_operand_runint : forall rv t s e,
  ptype e = Some (PtRunInt s) -> numty_eqb s t = true -> typed_operand rv t e = rv e.
Proof.
  intros rv t s e Hpt Hn. unfold typed_operand. rewrite Hpt, Hn. reflexivity.
Qed.
Lemma typed_operand_typed : forall t e g,
  is_int_goty t = true ->
  (ptype e = Some (PtRunInt t)
   \/ (exists z, ptype e = Some (PtIntConst z) \/ ptype e = Some (PtTIntConst t z))) ->
  typed_operand reval_val t e = Some (RAVal g) ->
  tag_matches t g = true.
Proof.
  intros t e g Hi Hc H; unfold typed_operand in H.
  destruct Hc as [Hpt | [z [Hpt | Hpt]]]; rewrite Hpt in H; cbv beta iota in H.
  - rewrite (numty_eqb_refl_int t Hi) in H. cbv beta iota in H.
    exact (reval_val_typed e t g Hpt H).
  - destruct (box_int t z) eqn:B; [|discriminate H].
    injection H as <-; exact (box_int_tag _ _ _ B).
  - rewrite (numty_eqb_refl_int t Hi) in H. cbv beta iota in H.
    destruct (box_int t z) eqn:B; [|discriminate H].
    injection H as <-; exact (box_int_tag _ _ _ B).
Qed.
Lemma typed_operand_const_total : forall t e z,
  is_int_goty t = true -> numty_eqb t GTUint = false ->
  ((ptype e = Some (PtIntConst z) /\ int_const_repr z t = true)
   \/ ptype e = Some (PtTIntConst t z)) ->
  exists g, typed_operand reval_val t e = Some (RAVal g).
Proof.
  intros t e z Hi Hu Hc. unfold typed_operand.
  destruct Hc as [[Hpt Hr] | Hpt]; rewrite Hpt; cbv beta iota.
  - destruct (box_int_repr_total t z Hi Hu Hr) as [g B]. rewrite B. eexists; reflexivity.
  - rewrite (numty_eqb_refl_int t Hi). cbv beta iota.
    pose proof (ptype_tint_const_repr e t z Hpt) as Hr.
    destruct (box_int_repr_total t z Hi Hu Hr) as [g B]. rewrite B. eexists; reflexivity.
Qed.
Lemma typed_operand_panic_runtime : forall rv t e p,
  typed_operand rv t e = Some (RAPanic p) ->
  exists s, ptype e = Some (PtRunInt s) /\ numty_eqb s t = true
            /\ rv e = Some (RAPanic p).
Proof.
  intros rv t e p H. unfold typed_operand in H.
  destruct (ptype e) as [c|]; [|discriminate H].
  destruct c; cbv beta iota in H;
  try discriminate H;
  repeat match type of H with
         | (if ?bb then _ else _) = _ =>
             let E := fresh "E" in destruct bb eqn:E; cbv beta iota in H; [|discriminate H]
         end;
  try (match type of H with
       | context [box_int ?tt ?zz] => destruct (box_int tt zz); discriminate H
       end);
  eexists; split; [reflexivity | split; [assumption | exact H]].
Qed.

(** The COUNT layer sealed: an evaluated count is rawable — a RUNTIME count via the well-taggedness
    invariant; a CONSTANT count via the fold's own int box (its value can only come from the fold:
    the engine demands [PtRunInt GTInt] and every exit demands [PtRunInt]/[PtBool],
    [rexit_nonexit_class_none]). *)
Lemma shift_count_runint_total : forall s b gb,
  ptype b = Some (PtRunInt s) ->
  reval_val b = Some (RAVal gb) ->
  exists z, shift_count reval_val b = Some (inl z).
Proof.
  intros s b gb Hpt Hb.
  pose proof (reval_val_typed b s gb Hpt Hb) as Htag.
  pose proof (ptype_int_ok _ _ Hpt) as Hi. cbn in Hi.
  destruct (runint_raw_total s gb Hi Htag) as [z Hz].
  exists z. unfold shift_count. rewrite Hpt, Hb, Hz. reflexivity.
Qed.
(** ★ CONST-count TOTALITY from the GATE ALONE — no evaluation premise, for ANY evaluator, and
    the count is EXACTLY [ptype]'s own value: the direct read makes it impossible for the count
    layer to leak a gate-admitted constant (the review-R8 side-condition-leak class killed
    structurally, not per-witness). *)
Lemma shift_count_const_total : forall rv b c z,
  ptype b = Some c -> int_const_val c = Some z ->
  shift_count rv b = Some (inl z).
Proof.
  intros rv b c z Hpt Hic. unfold shift_count. rewrite Hpt.
  destruct c; cbn [int_const_val] in Hic; try discriminate Hic;
    injection Hic as ->; reflexivity.
Qed.
(** the count's NONNEGATIVITY comes from the GATE too ([is_neg_const] guards every shift
    classification) — no caller-side [(0 <=? z) = true] premise needed for const counts *)
Lemma num_binop_shift_count_nonneg : forall o cl cr t z,
  shift_op o = true ->
  num_binop o cl cr = Some (PtRunInt t) ->
  int_const_val cr = Some z ->
  (0 <=? z)%Z = true.
Proof.
  intros o cl cr t z Ho Hnb Hic.
  destruct o; try discriminate Ho;
  ( cbn [num_binop] in Hnb;
    destruct (andb (is_int_cat cl) (is_int_cat cr)); cbv beta iota in Hnb; [|discriminate Hnb];
    destruct (is_neg_const cr) eqn:En; cbv beta iota in Hnb; [discriminate Hnb|];
    unfold is_neg_const in En; rewrite Hic in En;
    apply Z.leb_le; apply Z.ltb_ge in En; exact En ).
Qed.
Lemma ptype_shift_count_const_nonneg : forall o a b t c z,
  shift_op o = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  ptype b = Some c -> int_const_val c = Some z ->
  (0 <=? z)%Z = true.
Proof.
  intros o a b t c z Ho Hpt Hb Hic. cbn [ptype] in Hpt.
  destruct (ptype a) as [cl|] eqn:Ea; [|discriminate Hpt].
  rewrite Hb in Hpt. cbv beta iota in Hpt.
  destruct o; try discriminate Ho;
    exact (num_binop_shift_count_nonneg _ _ _ _ _ Ho Hpt Hic).
Qed.

(** The unary [ptype] boundary: a [PtRunInt]-classified unary node's OPERAND is classified at the SAME
    width (the [UNeg]/[UXor] rows preserve [PtRunInt t]; every const row yields a const category). *)
Lemma ptype_unary_runint : forall o a t,
  ptype (EUn o a) = Some (PtRunInt t) -> ptype a = Some (PtRunInt t).
Proof.
  intros o a t H. cbn [ptype] in H.
  destruct (ptype a) as [c|] eqn:Hpa; [|discriminate H].
  destruct o; try discriminate H; destruct c; try discriminate H; cbv zeta in H;
    try (destruct (complement_const _ _) as [r|] in H; try discriminate H);
    repeat match type of H with
           | (if ?b then _ else _) = _ => destruct b; try discriminate H
           end;
    injection H as <-; first [reflexivity | exact Hpa].
Qed.

(** ★ CLASS (T1).  [denote_expr_typed_unop_runs] is the INTERNAL dispatch-hypothesis form (a proof
    step for the sealed theorem below — NOT exported); the PUBLIC theorem is
    [denote_expr_typed_unop_runs_sealed], which derives the dispatch fact from [ptype] via the
    well-taggedness invariant. *)
Lemma denote_expr_typed_unop_runs : forall o a t g g',
  floats_checked (EUn o a) = true ->
  ptype (EUn o a) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  eval_value (EUn o a) = None ->
  reval_val a = Some (RAVal g) ->
  typed_unop o t g = Some g' ->
  denote_expr (EUn o a) = Some (CRet g', false).
Proof.
  intros o a t g g' Hfc Hpt Ht Hev Ha Hu.
  assert (He : reval_int (EUn o a) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EUn o a) = Some (RAVal g')).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Hu. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
Lemma denote_expr_typed_unop_panic : forall o a t p,
  floats_checked (EUn o a) = true ->
  ptype (EUn o a) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  eval_value (EUn o a) = None ->
  reval_val a = Some (RAPanic p) ->
  denote_expr (EUn o a) = Some (CPan p, true).
Proof.
  intros o a t p Hfc Hpt Ht Hev Ha.
  assert (He : reval_int (EUn o a) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EUn o a) = Some (RAPanic p)).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.

(** ★ THE SEALED T1 THEOREM — NO caller-side dispatch premise: [ptype] pins the operand's width
    ([ptype_unary_runint]) and its int-ness ([ptype_int_ok]); the WELL-TAGGEDNESS invariant
    ([reval_val_typed]) forces the payload's tag; [typed_unop_live_total] then computes.  The
    live-cell hypothesis only SCOPES the class (the [^]-non-uint / [-]-i64/u64 cells — the holes are
    pinned absent at the fixture site). *)
Theorem denote_expr_typed_unop_runs_sealed : forall o a t g,
  floats_checked (EUn o a) = true ->
  ptype (EUn o a) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  eval_value (EUn o a) = None ->
  reval_val a = Some (RAVal g) ->
  ((o = UXor /\ numty_eqb t GTUint = false) \/ (o = UNeg /\ (t = GTInt64 \/ t = GTU64))) ->
  exists g', typed_unop o t g = Some g'
    /\ tag_matches t g' = true
    /\ denote_expr (EUn o a) = Some (CRet g', false).
Proof.
  intros o a t g Hfc Hpt Ht Hev Ha Hlive.
  pose proof (ptype_unary_runint o a t Hpt) as Hpa.
  pose proof (ptype_int_ok _ _ Hpt) as Hint. cbn in Hint.
  pose proof (reval_val_typed a t g Hpa Ha) as Htag.
  destruct (typed_unop_live_total o t g Htag) as [g' Hu].
  { destruct Hlive as [[-> Hu8]|[-> Hw]]; [left|right]; auto. }
  exists g'. split; [exact Hu|]. split.
  - exact (proj2 (typed_unop_tag_exact _ _ _ _ Hu)).
  - exact (denote_expr_typed_unop_runs o a t g g' Hfc Hpt Ht Hev Ha Hu).
Qed.

(** ★ THE SEALED T2 THEOREM — the conversion exit is TOTAL on every evaluated RUNTIME-INT-classified
    source, with NO caller-side raw/wrap premise: the operand-shape split is PROVED exhaustive
    ([ptype_call_runint_conv_arg] — a [PtRunInt]-classified one-arg call's operand is [PtRunInt] or
    [PtRunFloat]); on the [PtRunInt] side the well-taggedness invariant ([reval_val_typed]) forces the
    payload's tag, on which the raw reading is total ([runint_raw_total]) and the target wrap is total
    ([wrap_runint_total]).  The [PtRunFloat] complement is CLASS-absent
    ([denote_expr_conv_float_src_absent] below, on [reval_val_runfloat_none]; supported-side witness
    [runtime_float_source_conv_absent]) — the float arc, not this one. *)
Theorem denote_expr_conv_runs_sealed : forall f a t s g,
  floats_checked (ECall (EId f) (a :: nil)) = true ->
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  eval_value (ECall (EId f) (a :: nil)) = None ->
  ptype a = Some (PtRunInt s) ->
  reval_val a = Some (RAVal g) ->
  exists z g', runint_raw g = Some z
    /\ wrap_runint t z = Some g'
    /\ tag_matches t g' = true
    /\ denote_expr (ECall (EId f) (a :: nil)) = Some (CRet g', false).
Proof.
  intros f a t s g Hfc Hpt Ht Hev Hpa Ha.
  pose proof (ptype_int_ok _ _ Hpa) as Hs. cbn in Hs.
  pose proof (reval_val_typed a s g Hpa Ha) as Htag.
  destruct (runint_raw_total s g Hs Htag) as [z Hz].
  destruct (denote_expr_conv_runs f a t g z Hfc Hpt Ht Hev Ha Hz) as [g' [Hw Hd]].
  exists z, g'.
  repeat split; [exact Hz | exact Hw | exact (wrap_runint_tag _ _ _ Hw) | exact Hd].
Qed.

(** ★ THE SEALED T2 THEOREM, [int]-TARGET HALF — [reval_int]'s own [int(x)] arm, same seal: NO
    caller-side raw premise and NO name premise (a [PtRunInt GTInt]-classified one-arg call with a
    runtime-int operand IS [int(x)] — [ptype_call_runint_int_name]); the invariant forces the
    payload's tag, the raw reading is total, and [intwrap] needs no wrap witness. *)
Theorem denote_expr_conv_int_runs_sealed : forall f a s g,
  floats_checked (ECall (EId f) (a :: nil)) = true ->
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt GTInt) ->
  eval_value (ECall (EId f) (a :: nil)) = None ->
  ptype a = Some (PtRunInt s) ->
  reval_val a = Some (RAVal g) ->
  exists z, runint_raw g = Some z
    /\ denote_expr (ECall (EId f) (a :: nil)) = Some (CRet (anyt TInt64 (intwrap z)), false).
Proof.
  intros f a s g Hfc Hpt Hev Hpa Ha.
  pose proof (ptype_call_runint_int_name f a s Hpt Hpa) as Hfeq.
  pose proof (ptype_int_ok _ _ Hpa) as Hs. cbn in Hs.
  pose proof (reval_val_typed a s g Hpa Ha) as Htag.
  destruct (runint_raw_total s g Hs Htag) as [z Hz].
  exists z. split; [exact Hz|].
  unfold reval_val in Ha.
  assert (He : reval_int (ECall (EId f) (a :: nil)) = Some (RVal (intwrap z))).
  { cbn [reval_int]. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
    cbn [numty_eqb negb]. cbv beta iota.
    destruct a as [i|z0|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      cbv beta iota;
      try (rewrite Hfeq; cbv beta iota; rewrite Ha; cbv beta iota; rewrite Hz; reflexivity).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He. reflexivity.
Qed.

(** ★ THE RUNTIME-FLOAT SOURCE CLASS THEOREM — the [PtRunFloat] half of
    [ptype_call_runint_conv_arg]'s split, QUANTIFIED over every integer target ([GTInt] included) and
    every float-classified source: the conversion is ABSENT, because no runtime-float expression
    evaluates at all ([reval_val_runfloat_none]).
    ⚠ Scope of the runtime-INT side, stated exactly: it is decided AS A FUNCTION OF THE SOURCE'S OWN
    EVALUATION OUTCOME — value ⟹ wrapped value (the sealed runs pair), panic ⟹ that panic
    ([denote_expr_conv_panic] / [denote_expr_conv_int_panic]), ABSENT ⟹ absent
    ([denote_expr_conv_src_absent] below): a conversion never decides MORE than its source, and
    [PtRunInt] classification alone NEVER implies denotation (an absent-source witness is pinned,
    [runtime_conv_absent_src_pinned]). *)
Theorem denote_expr_conv_float_src_absent : forall f a t s,
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt t) ->
  ptype a = Some (PtRunFloat s) ->
  denote_expr (ECall (EId f) (a :: nil)) = None.
Proof.
  intros f a t s Hpt Hpa.
  pose proof (reval_val_runfloat_none a s Hpa) as Hrv. unfold reval_val in Hrv.
  unfold denote_expr.
  destruct (floats_checked (ECall (EId f) (a :: nil))) eqn:Hfc; cbn [negb]; [|reflexivity].
  assert (Hev : eval_value (ECall (EId f) (a :: nil)) = None).
  { unfold eval_value. rewrite Hfc.
    destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      try (cbn [eval_value_core]; unfold eval_value_ptype_core; rewrite Hpt; reflexivity).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  assert (Hri : reval_int (ECall (EId f) (a :: nil)) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
    destruct (numty_eqb t GTInt); cbn [negb]; cbv beta iota; [|reflexivity].
    destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      cbv beta iota;
      try (destruct (String.eqb (proj1_sig f) "int"); cbv beta iota;
           [rewrite Hrv; reflexivity | reflexivity]).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  rewrite reval_val_with_eq, Hev, Hri. cbv beta iota.
  cbn [rexit_with]. rewrite Hpt. cbv beta iota.
  destruct (numty_eqb t GTInt); cbv beta iota; [reflexivity|].
  rewrite Hrv. reflexivity.
Qed.

(** ★ THE ABSENT-SOURCE PROPAGATION THEOREM — the third outcome of the runtime-int side: an operand
    that is itself ABSENT (supported-but-undenoted — a shift, a typed hole) makes the conversion
    absent too, for BOTH target halves ([GTInt] included).  Faithful-or-absent composes: the
    conversion adds no behavior its source does not have. *)
Theorem denote_expr_conv_src_absent : forall f a t s,
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt t) ->
  ptype a = Some (PtRunInt s) ->
  reval_val a = None ->
  denote_expr (ECall (EId f) (a :: nil)) = None.
Proof.
  intros f a t s Hpt Hpa Hrv. unfold reval_val in Hrv.
  unfold denote_expr.
  destruct (floats_checked (ECall (EId f) (a :: nil))) eqn:Hfc; cbn [negb]; [|reflexivity].
  assert (Hev : eval_value (ECall (EId f) (a :: nil)) = None).
  { unfold eval_value. rewrite Hfc.
    destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      try (cbn [eval_value_core]; unfold eval_value_ptype_core; rewrite Hpt; reflexivity).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  assert (Hri : reval_int (ECall (EId f) (a :: nil)) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
    destruct (numty_eqb t GTInt); cbn [negb]; cbv beta iota; [|reflexivity].
    destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      cbv beta iota;
      try (destruct (String.eqb (proj1_sig f) "int"); cbv beta iota;
           [rewrite Hrv; reflexivity | reflexivity]).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  rewrite reval_val_with_eq, Hev, Hri. cbv beta iota.
  cbn [rexit_with]. rewrite Hpt. cbv beta iota.
  destruct (numty_eqb t GTInt); cbv beta iota; [reflexivity|].
  rewrite Hrv. reflexivity.
Qed.

(** The [int]-target PANIC propagation, completing the outcome trichotomy for that half
    ([denote_expr_conv_panic] is the exit-target one). *)
Theorem denote_expr_conv_int_panic : forall f a s p,
  floats_checked (ECall (EId f) (a :: nil)) = true ->
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt GTInt) ->
  eval_value (ECall (EId f) (a :: nil)) = None ->
  ptype a = Some (PtRunInt s) ->
  reval_val a = Some (RAPanic p) ->
  denote_expr (ECall (EId f) (a :: nil)) = Some (CPan p, true).
Proof.
  intros f a s p Hfc Hpt Hev Hpa Ha.
  pose proof (ptype_call_runint_int_name f a s Hpt Hpa) as Hfeq.
  unfold reval_val in Ha.
  assert (He : reval_int (ECall (EId f) (a :: nil)) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
    cbn [numty_eqb negb]. cbv beta iota.
    destruct a as [i|z0|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      cbv beta iota;
      try (rewrite Hfeq; cbv beta iota; rewrite Ha; reflexivity).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He. reflexivity.
Qed.

(** ★ THE SEALED T3 THEOREM — SAME-WIDTH typed arithmetic/bitwise over the FULL operand-shape
    split ([ptype_binop_runint_args]: both-runtime, or one runtime + one int-CONSTANT — an untyped
    constant CONVERTS to the binop's width, a typed one is already AT it; [typed_operand],
    width-sealed, total on ptype's own shapes by [typed_operand_const_total]): both operand tags are forced ([typed_operand_typed]), the dispatch
    is total on live rows ([typed_binop_live_total]), and the result is decided per OUTCOME — the
    model op's VALUE (tagged at the width) or the division-by-zero PANIC; operand panics propagate
    left-to-right (only the runtime row can panic, [typed_operand_panic_runtime]) and ABSENT
    operands stay absent (the companion lemmas below) — never decided by classification alone.
    [GTUint] is the hole row ([typed_binop_uint_none], pinned [typed_binop_uint_program_absent]);
    shifts are the T5 exit (their own sealed theorem below). *)
Theorem denote_expr_typed_binop_runs_sealed : forall o a b t ga gb,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false -> numty_eqb t GTUint = false ->
  typed_arith_op o = true ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAVal ga) ->
  typed_operand reval_val t b = Some (RAVal gb) ->
  exists r, typed_binop o t ga gb = Some r
    /\ denote_expr (EBn o a b)
       = Some (match r with RAVal g => (CRet g, false) | RAPanic p => (CPan p, true) end)
    /\ (forall g, r = RAVal g -> tag_matches t g = true).
Proof.
  intros o a b t ga gb Hfc Hpt Ht Hu Ho Hev Ha Hb.
  pose proof (ptype_int_ok _ _ Hpt) as Hi. cbn in Hi.
  pose proof (ptype_binop_runint_args o a b t Ho Hpt) as Hshape.
  assert (Hta : tag_matches t ga = true).
  { apply (typed_operand_typed t a ga Hi); [|exact Ha].
    destruct Hshape as [[Hpa _] | [[[z [[Hpa _] | Hpa]] _] | [_ Hpa]]];
      [ left; exact Hpa
      | right; exists z; left; exact Hpa
      | right; exists z; right; exact Hpa
      | left; exact Hpa ]. }
  assert (Htb : tag_matches t gb = true).
  { apply (typed_operand_typed t b gb Hi); [|exact Hb].
    destruct Hshape as [[_ Hpb] | [[_ Hpb] | [[z [[Hpb _] | Hpb]] _]]];
      [ left; exact Hpb
      | left; exact Hpb
      | right; exists z; left; exact Hpb
      | right; exists z; right; exact Hpb ]. }
  destruct (typed_binop_live_total o t ga gb Ho Hta Htb Ht Hu Hi) as [r Hr].
  exists r.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some r).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Ho. cbv beta iota.
    rewrite Hb. cbv beta iota. exact Hr. }
  split; [exact Hr|]. split.
  - unfold denote_expr. rewrite Hfc. cbn [negb].
    rewrite reval_val_with_eq, Hev, He, Hrx.
    destruct r as [g|p]; reflexivity.
  - intros g ->. exact (proj2 (proj2 (typed_binop_tag_exact _ _ _ _ _ Hr))).
Qed.
Lemma denote_expr_typed_binop_left_panic : forall o a b t p,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b t p Hfc Hpt Ht Hev Ha.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some (RAPanic p)).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
Lemma denote_expr_typed_binop_right_panic : forall o a b t ga p,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  typed_arith_op o = true ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAVal ga) ->
  typed_operand reval_val t b = Some (RAPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b t ga p Hfc Hpt Ht Ho Hev Ha Hb.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some (RAPanic p)).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Ho. cbv beta iota.
    rewrite Hb. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
(** The ABSENT-operand propagation (the trichotomy's third outcome, binop edition): a typed binop
    never decides more than its operands — left absent, or left evaluated and right absent, keeps
    the whole node absent. *)
Theorem denote_expr_typed_binop_src_absent : forall o a b t,
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  typed_arith_op o = true ->
  (typed_operand reval_val t a = None
   \/ (exists ga, typed_operand reval_val t a = Some (RAVal ga)
                  /\ typed_operand reval_val t b = None)) ->
  denote_expr (EBn o a b) = None.
Proof.
  intros o a b t Hpt Ht Ho Habs.
  unfold denote_expr.
  destruct (floats_checked (EBn o a b)) eqn:Hfc; cbn [negb]; [|reflexivity].
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  rewrite reval_val_with_eq, Hev, He. cbv beta iota.
  cbn [rexit_with]. rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
  destruct Habs as [Hna | [ga [Ha Hnb]]].
  - unfold reval_val in Hna. rewrite Hna. reflexivity.
  - unfold reval_val in Ha, Hnb. rewrite Ha. cbv beta iota. rewrite Ho. cbv beta iota.
    rewrite Hnb. reflexivity.
Qed.

(** A [cmp_width] result other than [GTInt] is an INT width (it comes from a [PtRunInt] operand —
    [ptype_int_ok]; the both-const fallback is [GTInt]). *)
Lemma cmp_width_int : forall a b t,
  cmp_width (ptype a) (ptype b) = Some t ->
  numty_eqb t GTInt = false ->
  is_int_goty t = true.
Proof.
  intros a b t Hw Ht. unfold cmp_width in Hw.
  destruct (ptype a) as [ca|] eqn:Ea.
  - destruct ca; cbv beta iota in Hw;
    try (injection Hw as <-;
         pose proof (ptype_int_ok _ _ Ea) as Hi; cbn in Hi; exact Hi);
    (destruct (ptype b) as [cb|] eqn:Eb; cbv beta iota in Hw; [|discriminate Hw]);
    destruct cb; cbv beta iota in Hw;
    try (injection Hw as <-;
         pose proof (ptype_int_ok _ _ Eb) as Hi; cbn in Hi; exact Hi);
    repeat match type of Hw with
           | (match ?x with Some _ => _ | None => _ end) = _ =>
               destruct x; cbv beta iota in Hw; [|discriminate Hw]
           end;
    try discriminate Hw;
    injection Hw as <-; discriminate Ht.
  - destruct (ptype b) as [cb|] eqn:Eb; cbv beta iota in Hw; [|discriminate Hw];
    destruct cb; cbv beta iota in Hw; try discriminate Hw;
    injection Hw as <-;
    pose proof (ptype_int_ok _ _ Eb) as Hi; cbn in Hi; exact Hi.
Qed.

(** ★ THE SEALED T4 THEOREM — SAME-WIDTH typed COMPARISONS over the FULL operand-shape split
    ([ptype_cmp_bool_args] — both-runtime, or one runtime + one int-constant under the operand
    WIDTH SEAL): both tags forced ([typed_operand_typed]), the dispatch total on live rows
    ([typed_cmp_live_total]), the verdict the width's own model op, boxed [TBool].  Comparisons
    never panic themselves; operand panics propagate left-to-right and ABSENT operands stay absent
    (companions below).  [GTUint] is the hole row ([typed_cmp_uint_none], pinned
    [typed_cmp_uint_program_absent]); the [GTInt] width is the R4 engine path. *)
Theorem denote_expr_typed_cmp_runs_sealed : forall o a b t ga gb,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some t ->
  numty_eqb t GTInt = false -> numty_eqb t GTUint = false ->
  cmp_binop o = true ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAVal ga) ->
  typed_operand reval_val t b = Some (RAVal gb) ->
  exists v, typed_cmp o t ga gb = Some v
    /\ denote_expr (EBn o a b) = Some (CRet (anyt TBool v), false).
Proof.
  intros o a b t ga gb Hfc Hpt Hw Ht Hu Ho Hev Ha Hb.
  pose proof (cmp_width_int a b t Hw Ht) as Hi.
  pose proof (ptype_cmp_bool_args o a b t Ho Hpt Hw Ht) as Hshape.
  assert (Hta : tag_matches t ga = true).
  { apply (typed_operand_typed t a ga Hi); [|exact Ha].
    destruct Hshape as [[Hpa _] | [[[z [[Hpa _] | Hpa]] _] | [_ Hpa]]];
      [ left; exact Hpa | right; exists z; left; exact Hpa
      | right; exists z; right; exact Hpa | left; exact Hpa ]. }
  assert (Htb : tag_matches t gb = true).
  { apply (typed_operand_typed t b gb Hi); [|exact Hb].
    destruct Hshape as [[_ Hpb] | [[_ Hpb] | [[z [[Hpb _] | Hpb]] _]]];
      [ left; exact Hpb | left; exact Hpb
      | right; exists z; left; exact Hpb | right; exists z; right; exact Hpb ]. }
  destruct (typed_cmp_live_total o t ga gb Ho Hta Htb Ht Hu Hi) as [v Hv].
  exists v.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAVal (anyt TBool v))).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Hb. cbv beta iota. rewrite Hv. reflexivity. }
  split; [exact Hv|].
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
Lemma denote_expr_typed_cmp_left_panic : forall o a b t p,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some t ->
  numty_eqb t GTInt = false ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b t p Hfc Hpt Hw Ht Hev Ha.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAPanic p)).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
Lemma denote_expr_typed_cmp_right_panic : forall o a b t ga p,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some t ->
  numty_eqb t GTInt = false ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAVal ga) ->
  typed_operand reval_val t b = Some (RAPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b t ga p Hfc Hpt Hw Ht Hev Ha Hb.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAPanic p)).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Hb. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
(** The ABSENT-operand propagation, comparison edition ([eval_value = None] is a premise here: a
    PtBool node's fold goes through [eval_bool], which the runs pins exercise separately). *)
Theorem denote_expr_typed_cmp_src_absent : forall o a b t,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some PtBool ->
  cmp_width (ptype a) (ptype b) = Some t ->
  numty_eqb t GTInt = false ->
  eval_value (EBn o a b) = None ->
  (typed_operand reval_val t a = None
   \/ (exists ga, typed_operand reval_val t a = Some (RAVal ga)
                  /\ typed_operand reval_val t b = None)) ->
  denote_expr (EBn o a b) = None.
Proof.
  intros o a b t Hfc Hpt Hw Ht Hev Habs.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He. cbv beta iota.
  cbn [rexit_with]. rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota.
  rewrite Ht. cbv beta iota.
  destruct Habs as [Hna | [ga [Ha Hnb]]].
  - unfold reval_val in Hna. rewrite Hna. reflexivity.
  - unfold reval_val in Ha, Hnb. rewrite Ha. cbv beta iota. rewrite Hnb. reflexivity.
Qed.

(** ★ THE SEALED T5 THEOREM — HETEROGENEOUS typed SHIFTS over [ptype]'s own shape split
    ([ptype_shift_runint_args]: the LEFT is runtime-at-[t] or a typed constant AT [t] — the operand
    width seal covers both; the COUNT is any-width runtime or an int constant, read by the sealed
    count layer — a CONSTANT count directly off the gate's own value, TOTAL with NO evaluation
    premise ([shift_count_const_total]), a RUNTIME count off its evaluated carrier
    ([shift_count_runint_total])).  The result is decided per OUTCOME: the width's model op's VALUE, or
    the NEGATIVE-COUNT panic ([typed_shift_panic_neg] — gc's exact payload); operand/count panics
    propagate left-to-right; ABSENT sides stay absent.  [GTUint] left is the hole row
    ([typed_shift_uint_none], pinned [typed_shift_uint_program_absent]); an untyped-const LEFT
    classifies [GTInt] — the ENGINE's own R8 row runs it ([gtint_shift_runs]; [typed_shift]
    itself stays op-less there, [typed_shift_gtint_none]). *)
Theorem denote_expr_typed_shift_runs_sealed : forall o a b t ga z,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false -> numty_eqb t GTUint = false ->
  shift_op o = true ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAVal ga) ->
  shift_count reval_val b = Some (inl z) ->
  exists r, typed_shift o t ga z = Some r
    /\ denote_expr (EBn o a b)
       = Some (match r with RAVal g => (CRet g, false) | RAPanic p => (CPan p, true) end)
    /\ (forall g, r = RAVal g -> tag_matches t g = true).
Proof.
  intros o a b t ga z Hfc Hpt Ht Hu Ho Hev Ha Hcnt.
  pose proof (ptype_int_ok _ _ Hpt) as Hi. cbn in Hi.
  pose proof (ptype_shift_runint_args o a b t Ho Hpt Ht) as [Hleft _].
  assert (Hna : typed_arith_op o = false)
    by (destruct o; try discriminate Ho; reflexivity).
  assert (Hta : tag_matches t ga = true).
  { apply (typed_operand_typed t a ga Hi); [|exact Ha].
    destruct Hleft as [Hpa | [z' Hpa]];
      [ left; exact Hpa | right; exists z'; right; exact Hpa ]. }
  destruct (typed_shift_live_total o t ga z Ho Hta Ht Hu Hi) as [r Hr].
  exists r.
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hcnt.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some r).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Hna. cbv beta iota.
    rewrite Ho. cbv beta iota. rewrite Hcnt. cbv beta iota. exact Hr. }
  split; [exact Hr|]. split.
  - unfold denote_expr. rewrite Hfc. cbn [negb].
    rewrite reval_val_with_eq, Hev, He, Hrx.
    destruct r as [g|p]; reflexivity.
  - intros g ->. exact (proj2 (typed_shift_tag_exact _ _ _ _ _ Hr)).
Qed.
(** the T5 CONST-count corollary — the count premise DERIVED from the gate ([shift_count_const_total]),
    so a fixed-width shift with any gate-admitted constant count needs no count-side condition *)
Lemma denote_expr_typed_shift_const_count_runs : forall o a b t ga c z,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false -> numty_eqb t GTUint = false ->
  shift_op o = true ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAVal ga) ->
  ptype b = Some c -> int_const_val c = Some z ->
  exists r, typed_shift o t ga z = Some r
    /\ denote_expr (EBn o a b)
       = Some (match r with RAVal g => (CRet g, false) | RAPanic p => (CPan p, true) end)
    /\ (forall g, r = RAVal g -> tag_matches t g = true).
Proof.
  intros o a b t ga c z Hfc Hpt Ht Hu Ho Hev Ha Hb Hic.
  apply (denote_expr_typed_shift_runs_sealed o a b t ga z Hfc Hpt Ht Hu Ho Hev Ha).
  exact (shift_count_const_total _ _ _ _ Hb Hic).
Qed.
(** The COUNT-side panic propagation (the left already evaluated; Go's order). *)
Lemma denote_expr_typed_shift_count_panic : forall o a b t ga p,
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  shift_op o = true ->
  eval_value (EBn o a b) = None ->
  typed_operand reval_val t a = Some (RAVal ga) ->
  shift_count reval_val b = Some (inr p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b t ga p Hfc Hpt Ht Ho Hev Ha Hcnt.
  assert (Hna : typed_arith_op o = false)
    by (destruct o; try discriminate Ho; reflexivity).
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hcnt.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAPanic p)).
  { unfold rexit_with. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
    rewrite Ha. cbv beta iota. rewrite Hna. cbv beta iota.
    rewrite Ho. cbv beta iota. rewrite Hcnt. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He, Hrx. reflexivity.
Qed.
(** The ABSENT-side propagation, shift edition — BOTH fail-closed paths: the LEFT operand absent,
    or the left evaluated and the COUNT absent. *)
Theorem denote_expr_typed_shift_src_absent : forall o a b t,
  ptype (EBn o a b) = Some (PtRunInt t) ->
  numty_eqb t GTInt = false ->
  shift_op o = true ->
  (typed_operand reval_val t a = None
   \/ (exists ga, typed_operand reval_val t a = Some (RAVal ga)
                  /\ shift_count reval_val b = None)) ->
  denote_expr (EBn o a b) = None.
Proof.
  intros o a b t Hpt Ht Ho Habs.
  assert (Hna : typed_arith_op o = false)
    by (destruct o; try discriminate Ho; reflexivity).
  unfold denote_expr.
  destruct (floats_checked (EBn o a b)) eqn:Hfc; cbn [negb]; [|reflexivity].
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (He : reval_int (EBn o a b) = None).
  { cbn [reval_int]. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  rewrite reval_val_with_eq, Hev, He. cbv beta iota.
  cbn [rexit_with]. rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
  destruct Habs as [Hna2 | [ga [Ha Hcnt]]].
  - unfold reval_val in Hna2. rewrite Hna2. reflexivity.
  - unfold reval_val in Ha, Hcnt.
    rewrite Ha. cbv beta iota. rewrite Hna. cbv beta iota.
    rewrite Ho. cbv beta iota. rewrite Hcnt. reflexivity.
Qed.


(** ★ DISPATCH AUTHORITY PINS (gated) — [cmp_verdict]'s WHOLE dispatch table.  Each comparison branch
    IS, by reflexivity, the FULLY QUALIFIED model constant [Fido.builtins.int_eqb]/[int_ltb]/[int_leb]
    ([!=] the negation, [>]/[>=] the argument swap) — the [str_cmp_op] authority-pin pattern, immune to
    name shadowing: a branch rerouted to any local helper breaks a pin and fails the gated build.
    [cmp_verdict_complete] then seals EVERY [BinOp] constructor by case analysis — the six comparisons
    to those verdicts and every other constructor to [None] — so no future explicit arithmetic/shift/
    logical mapping can drift in while the surface stays green. *)
Example cmp_verdict_eq_model : cmp_verdict BEq = Some Fido.builtins.int_eqb.                          Proof. reflexivity. Qed.
Example cmp_verdict_ne_model : cmp_verdict BNe = Some (fun x y => negb (Fido.builtins.int_eqb x y)).  Proof. reflexivity. Qed.
Example cmp_verdict_lt_model : cmp_verdict BLt = Some Fido.builtins.int_ltb.                          Proof. reflexivity. Qed.
Example cmp_verdict_le_model : cmp_verdict BLe = Some Fido.builtins.int_leb.                          Proof. reflexivity. Qed.
Example cmp_verdict_gt_model : cmp_verdict BGt = Some (fun x y => Fido.builtins.int_ltb y x).         Proof. reflexivity. Qed.
Example cmp_verdict_ge_model : cmp_verdict BGe = Some (fun x y => Fido.builtins.int_leb y x).         Proof. reflexivity. Qed.
Example cmp_verdict_complete : forall o,
  cmp_verdict o = match o with
                  | BEq => Some Fido.builtins.int_eqb
                  | BNe => Some (fun x y => negb (Fido.builtins.int_eqb x y))
                  | BLt => Some Fido.builtins.int_ltb
                  | BLe => Some Fido.builtins.int_leb
                  | BGt => Some (fun x y => Fido.builtins.int_ltb y x)
                  | BGe => Some (fun x y => Fido.builtins.int_leb y x)
                  | _ => None
                  end.
Proof. intro o; destruct o; reflexivity. Qed.

(** ★ CLASS (R1/R6 values) — the evidence-carrying DIVISION and REMAINDER value theorems (the zero
    cases are [denote_expr_div_zero]) and runtime unary MINUS, quantified over the reval-evaluable
    fragment.  [int_div]/[int_mod]/[int_neg] are the model's own ops; the quantified [pf] is the
    nonzero evidence — the ops ignore its identity definitionally, so any proof yields the same value. *)
Lemma denote_expr_div_runs : forall a b va vb (pf : Z.eqb (intraw vb) 0 = false),
  floats_checked (EBn BDiv a b) = true ->
  ptype (EBn BDiv a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  reval_int b = Some (RVal vb) ->
  denote_expr (EBn BDiv a b) = Some (CRet (anyt TInt64 (int_div va vb pf)), false).
Proof.
  intros a b va vb pf Hfc Hpt Ha Hb.
  assert (Hev : eval_value (EBn BDiv a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hr : reval_int (EBn BDiv a b) = Some (RVal (int_div va vb pf))).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha, Hb.
    assert (K : forall (z : bool) (pf0 : Z.eqb (intraw vb) 0 = z), z = false ->
              (match z as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
               | true  => fun _   => Some (RPanic rt_div_zero)
               | false => fun pf1 => Some (RVal (int_div va vb pf1))
               end) pf0 = Some (RVal (int_div va vb pf))).
    { intros z pf0 Hz. destruct z; [discriminate Hz|].
      unfold int_div. reflexivity. }
    exact (K _ eq_refl pf). }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_rem_runs : forall a b va vb (pf : Z.eqb (intraw vb) 0 = false),
  floats_checked (EBn BRem a b) = true ->
  ptype (EBn BRem a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  reval_int b = Some (RVal vb) ->
  denote_expr (EBn BRem a b) = Some (CRet (anyt TInt64 (int_mod va vb pf)), false).
Proof.
  intros a b va vb pf Hfc Hpt Ha Hb.
  assert (Hev : eval_value (EBn BRem a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hr : reval_int (EBn BRem a b) = Some (RVal (int_mod va vb pf))).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha, Hb.
    assert (K : forall (z : bool) (pf0 : Z.eqb (intraw vb) 0 = z), z = false ->
              (match z as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
               | true  => fun _   => Some (RPanic rt_div_zero)
               | false => fun pf1 => Some (RVal (int_mod va vb pf1))
               end) pf0 = Some (RVal (int_mod va vb pf))).
    { intros z pf0 Hz. destruct z; [discriminate Hz|].
      unfold int_mod. reflexivity. }
    exact (K _ eq_refl pf). }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
(** ---- Tier R8 sealed — the GTInt BITWISE + SHIFT rows ----
    DISPATCH AUTHORITY (gated): each live row IS, by reflexivity, the FULLY QUALIFIED model op —
    a rerouted row breaks a pin and fails the build. *)
Example int_bitop_and_model    : int_bitop BAnd    = Some Fido.builtins.int_and.    Proof. reflexivity. Qed.
Example int_bitop_or_model     : int_bitop BOr     = Some Fido.builtins.int_or.     Proof. reflexivity. Qed.
Example int_bitop_xor_model    : int_bitop BXor    = Some Fido.builtins.int_xor.    Proof. reflexivity. Qed.
Example int_bitop_andnot_model : int_bitop BAndNot = Some Fido.builtins.int_andnot. Proof. reflexivity. Qed.
Example int_shift_op_shl_model : int_shift_op BShl = Some Fido.builtins.int_shl.    Proof. reflexivity. Qed.
Example int_shift_op_shr_model : int_shift_op BShr = Some Fido.builtins.int_shr.    Proof. reflexivity. Qed.
(* completeness: the dispatches are live on EXACTLY their ops — no silent hole, no silent widening *)
Lemma int_bitop_complete : forall o,
  (exists f, int_bitop o = Some f) <-> (o = BAnd \/ o = BOr \/ o = BXor \/ o = BAndNot).
Proof.
  intro o; split.
  - intros [f Hf]; destruct o; try discriminate Hf; auto.
  - intro H; destruct o;
      first [ eexists; reflexivity
            | exfalso; destruct H as [H|[H|[H|H]]]; discriminate H ].
Qed.
Lemma int_shift_op_complete : forall o,
  (exists f, int_shift_op o = Some f) <-> shift_op o = true.
Proof.
  intro o; split.
  - intros [f Hf]; destruct o; try discriminate Hf; reflexivity.
  - intro H; destruct o; try discriminate H; eexists; reflexivity.
Qed.
(** ★ CLASS — GTInt BITWISE runs: a supported runtime [GTInt] [& | ^ &^] whose operands both
    evaluate denotes to the dispatched model op's value (the engine row IS [int_bitop]'s row).
    go-run-verified: 3&1=1, 3|4=7, 3^1=2, 3&^1=2, 3&^2=1. *)
Lemma denote_expr_bitwise_runs : forall o f a b va vb,
  int_bitop o = Some f ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  reval_int b = Some (RVal vb) ->
  denote_expr (EBn o a b) = Some (CRet (anyt TInt64 (f va vb)), false).
Proof.
  intros o f a b va vb Hop Hfc Hpt Ha Hb.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hs : shift_op o = false)
    by (destruct o; try discriminate Hop; reflexivity).
  assert (Hr : reval_int (EBn o a b) = Some (RVal (f va vb))).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha, Hb.
    destruct o; try discriminate Hop;
      cbn [int_bitop] in Hop; injection Hop as <-; reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
(** the panic sides, Go's left-to-right order — a panicking LEFT fires before the right operand,
    a panicking RIGHT fires after an evaluated left *)
Lemma denote_expr_bitwise_left_panic : forall o f a b p,
  int_bitop o = Some f ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o f a b p Hop Hfc Hpt Ha.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hs : shift_op o = false)
    by (destruct o; try discriminate Hop; reflexivity).
  assert (Hr : reval_int (EBn o a b) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_bitwise_right_panic : forall o f a b va p,
  int_bitop o = Some f ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  reval_int b = Some (RPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o f a b va p Hop Hfc Hpt Ha Hb.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hs : shift_op o = false)
    by (destruct o; try discriminate Hop; reflexivity).
  assert (Hr : reval_int (EBn o a b) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha, Hb. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
(** ★ CLASS — the GTInt SHIFT decided per OUTCOME (T5's discipline at the engine's own width):
    the dispatched model op's value on a NONNEGATIVE count (>= 64 saturating — exact for the
    64-bit carrier), the NEGATIVE-count panic (gc's payload), a panicking LEFT or COUNT
    propagated in Go's order (left before count). *)
Lemma denote_expr_int_shift_runs : forall o f a b va z,
  int_shift_op o = Some f ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  shift_count (reval_val_with reval_int) b = Some (inl z) ->
  (0 <=? z)%Z = true ->
  exists pf,
    denote_expr (EBn o a b) = Some (CRet (anyt TInt64 (f va (Z.min z 64) pf)), false).
Proof.
  intros o f a b va z Hop Hfc Hpt Ha Hcnt Hz.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hs : shift_op o = true)
    by (destruct o; try discriminate Hop; reflexivity).
  destruct (int_shift_checked_cases f va z) as [[Ez _] | [_ [pf Ev]]]; [congruence|].
  exists pf.
  assert (Hr : reval_int (EBn o a b) = Some (RVal (f va (Z.min z 64) pf))).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. cbv beta iota. rewrite Hcnt.
    cbv beta iota. rewrite Hop. cbv beta iota. exact Ev. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
(** ★ the CONST-count class sealed to the GATE: NO count-evaluation premise at all — totality
    ([shift_count_const_total]) and nonnegativity ([ptype_shift_count_const_nonneg]) both come
    from [ptype]'s own shift classification, so the only outcome premise left is the LEFT
    operand's.  (An untyped count past the conservative platform-[uint] window never reaches
    here — [untyped_count_overflow] rejects it AT the gate, pinned [shift_bigconst_gate].) *)
Lemma denote_expr_int_shift_const_count_runs : forall o f a b va c z,
  int_shift_op o = Some f ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  ptype b = Some c -> int_const_val c = Some z ->
  exists pf,
    denote_expr (EBn o a b) = Some (CRet (anyt TInt64 (f va (Z.min z 64) pf)), false).
Proof.
  intros o f a b va c z Hop Hfc Hpt Ha Hb Hic.
  assert (Hs : shift_op o = true)
    by (destruct o; try discriminate Hop; reflexivity).
  apply (denote_expr_int_shift_runs o f a b va z Hop Hfc Hpt Ha).
  - exact (shift_count_const_total _ _ _ _ Hb Hic).
  - exact (ptype_shift_count_const_nonneg o a b GTInt c z Hs Hpt Hb Hic).
Qed.
Lemma denote_expr_int_shift_neg_panic : forall o a b va z,
  shift_op o = true ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  shift_count (reval_val_with reval_int) b = Some (inl z) ->
  (0 <=? z)%Z = false ->
  denote_expr (EBn o a b) = Some (CPan rt_shift_neg, true).
Proof.
  intros o a b va z Hs Hfc Hpt Ha Hcnt Hz.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hf : exists f, int_shift_op o = Some f)
    by (apply int_shift_op_complete; exact Hs).
  destruct Hf as [f Hop].
  destruct (int_shift_checked_cases f va z) as [[_ Ep] | [Ez _]]; [|congruence].
  assert (Hr : reval_int (EBn o a b) = Some (RPanic rt_shift_neg)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. cbv beta iota. rewrite Hcnt.
    cbv beta iota. rewrite Hop. cbv beta iota. exact Ep. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_int_shift_left_panic : forall o a b p,
  shift_op o = true ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RPanic p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b p Hs Hfc Hpt Ha.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hr : reval_int (EBn o a b) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_int_shift_count_panic : forall o a b va p,
  shift_op o = true ->
  floats_checked (EBn o a b) = true ->
  ptype (EBn o a b) = Some (PtRunInt GTInt) ->
  reval_int a = Some (RVal va) ->
  shift_count (reval_val_with reval_int) b = Some (inr p) ->
  denote_expr (EBn o a b) = Some (CPan p, true).
Proof.
  intros o a b va p Hs Hfc Hpt Ha Hcnt.
  assert (Hev : eval_value (EBn o a b) = None).
  { unfold eval_value. rewrite Hfc. cbn [eval_value_core].
    unfold eval_value_ptype_core. rewrite Hpt. reflexivity. }
  assert (Hr : reval_int (EBn o a b) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. cbv beta iota. rewrite Hcnt. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_neg_runs : forall a va,
  floats_checked (EUn UNeg a) = true ->
  ptype (EUn UNeg a) = Some (PtRunInt GTInt) ->
  eval_value (EUn UNeg a) = None ->
  reval_int a = Some (RVal va) ->
  denote_expr (EUn UNeg a) = Some (CRet (anyt TInt64 (int_neg va)), false).
Proof.
  intros a va Hfc Hpt Hev Ha.
  assert (Hr : reval_int (EUn UNeg a) = Some (RVal (int_neg va))).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_neg_panic : forall a p,
  floats_checked (EUn UNeg a) = true ->
  ptype (EUn UNeg a) = Some (PtRunInt GTInt) ->
  eval_value (EUn UNeg a) = None ->
  reval_int a = Some (RPanic p) ->
  denote_expr (EUn UNeg a) = Some (CPan p, true).
Proof.
  intros a p Hfc Hpt Hev Ha.
  assert (Hr : reval_int (EUn UNeg a) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_not_runs : forall a va,
  floats_checked (EUn UXor a) = true ->
  ptype (EUn UXor a) = Some (PtRunInt GTInt) ->
  eval_value (EUn UXor a) = None ->
  reval_int a = Some (RVal va) ->
  denote_expr (EUn UXor a) = Some (CRet (anyt TInt64 (int_not va)), false).
Proof.
  intros a va Hfc Hpt Hev Ha.
  assert (Hr : reval_int (EUn UXor a) = Some (RVal (int_not va))).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.
Lemma denote_expr_not_panic : forall a p,
  floats_checked (EUn UXor a) = true ->
  ptype (EUn UXor a) = Some (PtRunInt GTInt) ->
  eval_value (EUn UXor a) = None ->
  reval_int a = Some (RPanic p) ->
  denote_expr (EUn UXor a) = Some (CPan p, true).
Proof.
  intros a p Hfc Hpt Hev Ha.
  assert (Hr : reval_int (EUn UXor a) = Some (RPanic p)).
  { cbn [reval_int]. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with]. rewrite Hev, Hr. reflexivity.
Qed.

Fixpoint eval_args (args : list GExpr) : option (list GoAny) :=
  match args with
  | [] => Some []
  | a :: rest =>
      match eval_value a, eval_args rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** The SINGLE effect-call authority — denote a supported CALL expression ([println]/[print]/[panic]) to its
    command PAIRED WITH the TERMINATES flag.  Gated on [expr_stmt_ok] (exactly [stmt_ok]'s gate for BOTH
    [GsExprStmt] and [GsDefer]), so every consumer keeps [denote] ⊆ the gate ([gosem_sound]).  Consumed by the
    expression-statement arm (the call runs NOW) and the [GsDefer] arm (the SAME call, deferred to run at
    function-scope return via [CDfr]) — one authority, so the deferred call can never denote differently from
    the immediate one. *)
(** Effectful ARGUMENT sequencing: evaluate each argument left-to-right through [denote_expr], collecting the
    values, WITH an explicit terminal flag.  A PANICKING argument STRUCTURALLY short-circuits: its [CPan] is
    the whole argument command, the flag is [true], and the REMAINING arguments — which Go NEVER evaluates —
    are NOT required to denote (they are already syntactically/type-gated by the caller's [expr_stmt_ok], the
    same gate/denotability split as a terminator's dead tail in [denote_body]).  All-pure arguments reduce
    DEFINITIONALLY to [(CRet [v1..vn], false)]. *)
Fixpoint denote_args (args : list GExpr) : option (Cmd (list GoAny) * bool) :=
  match args with
  | [] => Some (CRet [], false)
  | a :: rest =>
      match denote_expr a with
      | Some (ca, true)  => Some (cbind ca (fun _ => CRet []), true)   (* [a] PANICS: rest is unreachable — gated, not denoted *)
      | Some (ca, false) =>
          match denote_args rest with
          | Some (crest, term) => Some (cbind ca (fun v => cbind crest (fun vs => CRet (v :: vs))), term)
          | None => None
          end
      | None => None
      end
  end.

(** How a gated call is SCHEDULED — a SEALED two-constructor mode (not an arbitrary [Cmd unit -> Cmd unit],
    which could erase a panic): [CallNow] runs the call immediately; [CallDeferred] registers it via [CDfr]
    to run at function-scope return.  [sched] builds the only two valid shapes. *)
Inductive CallMode : Type := CallNow | CallDeferred.
Definition sched (m : CallMode) (c : Cmd unit) : Cmd unit :=
  match m with CallNow => c | CallDeferred => CDfr c (CRet tt) end.

(** The ONE call-shape authority.  The ARGUMENTS are sequenced OUTSIDE [sched] in both modes — Go evaluates a
    deferred call's arguments AT DEFER TIME (a panicking argument panics at the [defer] statement, not at
    return) — so the two modes' argument semantics cannot drift.  The TERMINATES flag is COMPUTED from the
    argument evaluation and the scheduling: an immediate [panic] terminates always (its own panic, or an
    argument's even earlier); an immediate print terminates iff its arguments panic; a DEFERRED call
    terminates iff its arguments panic (the deferred call itself falls through, running at return).
    Gated on [expr_stmt_ok] (exactly [stmt_ok]'s gate for both consumers). *)
Definition denote_call (m : CallMode) (e : GExpr) : option (Cmd unit * bool) :=
  if expr_stmt_ok e then
    match e with
    | ECall (EId f) args =>
        let fn := proj1_sig f in
        if String.eqb fn "panic"
        then match args with
             | a :: nil => match denote_expr a with
                           | Some (ca, aterm) =>
                               Some (cbind ca (fun v => sched m (CPan v)),
                                     match m with CallNow => true | CallDeferred => aterm end)
                           | None => None
                           end
             | _ => None
             end
        else match denote_args args with                      (* println / print *)
             | Some (cargs, aterm) =>
                 Some (cbind cargs (fun vs => sched m (COut (String.eqb fn "println") vs (CRet tt))), aterm)
             | None => None
             end
    | _ => None
    end
  else None.

(** The pure inclusion for argument lists: purely-evaluable args denote to exactly [CRet] of their values,
    fall-through (each element via [denote_expr_pure]; the [cbind]s of [CRet] collapse definitionally). *)
Lemma denote_args_pure : forall args vs, eval_args args = Some vs -> denote_args args = Some (CRet vs, false).
Proof.
  induction args as [|a rest IH]; cbn [eval_args denote_args]; intros vs H.
  - injection H as <-. reflexivity.
  - destruct (eval_value a) as [v|] eqn:Ea; [|discriminate H].
    destruct (eval_args rest) as [vs'|] eqn:Er; [|discriminate H].
    injection H as <-.
    rewrite (denote_expr_pure a v Ea), (IH vs' eq_refl). reflexivity.
Qed.

(** Translate ONE statement to its command PAIRED WITH a TERMINATES flag (successors unreachable), or [None] if
    unmodeled.  The flag makes [denote_stmt] the SINGLE control-flow authority ([denote_body] never re-decides);
    it is ESSENTIAL, not derivable (a [return] and a CONSTANT blank-assign both give [CRet tt] but differ
    stop/fall-through).  The effect arms go through [denote_call] (gated on [expr_stmt_ok] — [denote] ⊆ the
    gate, [gosem_sound]), and the flag is COMPUTED from the effects: [println]/[print] fall through UNLESS an
    argument panics; [panic] terminates; [return] terminates; a blank-assign terminates iff its expression
    panics; [defer <call>] falls through unless its (defer-time) arguments panic. *)
Definition denote_stmt (s : GoStmt) : option (Cmd unit * bool) :=
  match s with
  | GsReturn        => Some (CRet tt, true)    (* TERMINATES the body *)
  | GsBlankAssign e =>
      (* [_ = e] discards [e]'s VALUE but NOT its runtime EFFECTS — denoted through the EFFECTFUL
         [denote_expr]: a pure constant gives the fall-through [CRet tt] ([cbind] of its [CRet v] — the same
         command as before), and a determined runtime panic ([1 / len([]int{})]) gives its TRUE [CPan] (Go
         evaluates [e] and panics) — with [denote_expr]'s OWN terminal flag (a panicking blank-assign
         TERMINATES the body).  Runtime forms [denote_expr] does not cover stay honestly [None].
         [svalue e] is still required so [denote] ⊆ the gate ([stmt_ok]'s blank arm IS [svalue]). *)
      if svalue e then
        match denote_expr e with
        | Some (ce, eterm) => Some (cbind ce (fun _ => CRet tt), eterm)
        | None => None
        end
      else None
  | GsReturnVal _   => None                                        (* a value return is invalid in void [main] *)
  | GsExprStmt e    => denote_call CallNow e
  | GsDefer e =>
      (* [defer <call>] — FAITHFUL via [cmd.v]'s [CDfr], with Go's ARGUMENT TIMING modeled exactly: the
         arguments are evaluated NOW (a panicking argument panics AT the [defer] statement), and only the
         CALL-ON-VALUES is deferred to function-scope RETURN ([CallDeferred]; [run_defers], LIFO).  The flag
         is [denote_call]'s own accurate one: pure args FALL THROUGH (a [defer panic(v)] does not stop the
         body; ITS panic fires at return — [rc_defer_panic]); PANICKING args TERMINATE at the [defer]
         statement itself ([rc_defer_arg_panic]). *)
      denote_call CallDeferred e
  end.

Fixpoint denote_body (b : list GoStmt) : option (Cmd unit) :=
  match b with
  | [] => Some (CRet tt)
  | s :: rest =>
      match denote_stmt s with
      | None => None
      | Some (c, term) =>
          if term then
            (* [s] TERMINATES (return / panic, per [denote_stmt]'s flag): emit its command [c] (which stops —
               [CRet]/[CPan]); the REST is UNREACHABLE, so its DENOTABILITY is irrelevant — require only that it
               be SUPPORTED ([forallb stmt_ok rest], the gate).  Keeps [denote_body] ⊆ the gate while NOT making
               a terminator depend on a successor slice 1 cannot yet evaluate. *)
            (if forallb stmt_ok rest then Some c else None)
          else
            match denote_body rest with
            | Some k => Some (cbind c (fun _ => k))
            | None => None
            end
      end
  end.

Definition denote_program (p : Program) : option (Cmd unit) :=
  if String.eqb (proj1_sig (prog_pkg p)) "main"
  then denote_body (prog_body p)
  else None.

(** ---- GATE CONNECTION (the slice-1 earns-its-weight theorem): denotation ⊆ supportedness ----
    GoSem gives a behavior ONLY to a program GoSafe accepts.  Because each [denote_stmt] arm that returns
    [Some] is itself gated ([GsReturn] is always [stmt_ok]; [GsBlankAssign] on [svalue]; [GsExprStmt] under
    [expr_stmt_ok]), this is structural. *)
Lemma denote_call_ok : forall m e, denote_call m e <> None -> expr_stmt_ok e = true.
Proof. intros m e H. unfold denote_call in H. destruct (expr_stmt_ok e); [reflexivity | congruence]. Qed.

Lemma denote_stmt_sound : forall s, denote_stmt s <> None -> stmt_ok s = true.
Proof.
  intros s H. destruct s as [e| |e0|e|e]; simpl in *.
  - exact (denote_call_ok CallNow e H).                      (* GsExprStmt: gated on [expr_stmt_ok] *)
  - reflexivity.                                             (* GsReturn *)
  - congruence.                                              (* GsReturnVal: None *)
  - destruct (svalue e); [reflexivity | congruence].         (* GsBlankAssign: gated on [svalue] = stmt_ok *)
  - exact (denote_call_ok CallDeferred e H).                 (* GsDefer: the SAME [expr_stmt_ok] gate *)
Qed.

Lemma denote_body_sound : forall b, denote_body b <> None -> forallb stmt_ok b = true.
Proof.
  induction b as [|s rest IH]; simpl; intro H.
  - reflexivity.
  - destruct (denote_stmt s) as [[c term]|] eqn:Es; [|congruence].   (* denote_stmt s = None => denote_body = None *)
    apply andb_true_intro; split.
    + apply denote_stmt_sound. congruence.             (* stmt_ok s, uniform via [Es] *)
    + destruct term.                                   (* the [denote_stmt] flag: terminator gates rest on supportedness; else on denotability *)
      * destruct (forallb stmt_ok rest) eqn:Ef; [reflexivity | congruence].
      * destruct (denote_body rest) eqn:Er; [|congruence]. apply IH. congruence.
Qed.

Theorem gosem_sound : forall p, denote_program p <> None -> supported_program p = true.
Proof.
  intros p H. unfold denote_program in H. unfold supported_program.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main") eqn:Epkg; simpl in *.
  - apply denote_body_sound. exact H.
  - congruence.
Qed.

(** ---- DENOTABILITY IS DECIDABLE, characterized STRUCTURALLY (converse-direction companion of [gosem_sound]).
    [denotable_body] mirrors [denote_body]: a body denotes iff its head denotes AND — at a TERMINATOR — the
    unreachable rest is merely SUPPORTED, else the rest is itself denotable; [denote_body_dec] proves they
    AGREE.  A CHARACTERIZATION result, NOT [supported ⟹ denotes]: the [denotable_*] ⊊ [supported_*] gap
    is REPRESENTATIVELY witnessed by [undenoted_frontier] below (see its own comment for what it does and
    does NOT cover) — a
    [GsDefer] now denotes exactly when its deferred call does. *)
Fixpoint denotable_body (b : list GoStmt) : bool :=
  match b with
  | [] => true
  | s :: rest =>
      match denote_stmt s with
      | None            => false
      | Some (_, true)  => forallb stmt_ok rest      (* terminator: the UNREACHABLE rest need only be SUPPORTED *)
      | Some (_, false) => denotable_body rest        (* continuer: the rest must itself be DENOTABLE *)
      end
  end.

Theorem denote_body_dec : forall b, denote_body b <> None <-> denotable_body b = true.
Proof.
  induction b as [|s rest IH]; simpl.
  - split; intro H; congruence.                                       (* [] : Some (CRet tt) <> None and true = true *)
  - destruct (denote_stmt s) as [[c term]|] eqn:Es.
    + destruct term.
      * destruct (forallb stmt_ok rest); split; intro H; congruence.   (* terminator: gates rest on supportedness *)
      * destruct (denote_body rest) eqn:Er; split; intro H.            (* continuer: gates rest on denotability (IH + Er) *)
        -- apply (proj1 IH); congruence.
        -- congruence.
        -- congruence.
        -- apply (proj2 IH) in H; congruence.
    + split; intro H; congruence.                                     (* denote_stmt s = None => both reject *)
Qed.

Definition denotable_program (p : Program) : bool :=
  String.eqb (proj1_sig (prog_pkg p)) "main" && denotable_body (prog_body p).

Theorem denote_program_dec : forall p, denote_program p <> None <-> denotable_program p = true.
Proof.
  intro p. unfold denote_program, denotable_program.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main"); simpl.
  - apply denote_body_dec.
  - split; intro H; [congruence | discriminate].
Qed.

(** ---- COMPLETENESS FRAGMENT — [supported ⟹ denotes] for the PRINT/PRINTLN-of-FOLDED-ARGS fragment
    (AUTHORITY: [out_main_denotes]).  [folded_arg] is the EVAL-ONLY (constant-folded) printable-argument
    fragment — deliberately NARROWER than the live denotation boundary ([denote_expr], which since tiers
    R1–R8 also denotes RUNTIME-determined args: [runlen_e], the runtime index, the runtime width
    CONVERSION [runconv_e], the runtime bool COMPARISON [runbool_e], the runtime-map-value [len]
    [maplen_runval_e], the R6/R7 unary/[%] forms ([runneg_e]/[runrem_e]/[runnot_e]), and the R8
    bitwise/shift forms ([gtint_and_e]/[runshift_intleft_e]) — NOT
    folded, yet denoted): a [folded_arg] certainly
    denotes, so the SUFFICIENT converse below holds outright on this fragment; the converse for the
    runtime tier is future work.  Supported-but-UNDENOTED args remain — REPRESENTATIVE pinned
    witnesses live in [undenoted_frontier], whose Coq definition is the ONLY member list (this
    comment deliberately enumerates none of it; NON-EXHAUSTIVE — no theorem bounds the gap).
    [denotable_supported] pins denotable ⊆ supported. *)
Definition folded_arg (e : GExpr) : bool :=
  match eval_value e with Some _ => printable_arg_ok e | None => false end.

Lemma folded_arg_eval : forall e, folded_arg e = true -> eval_value e <> None.
Proof. intros e H Hn. unfold folded_arg in H. rewrite Hn in H. discriminate. Qed.

Lemma folded_arg_printable : forall e, folded_arg e = true -> printable_arg_ok e = true.
Proof. intros e H. unfold folded_arg in H. destruct (eval_value e); [exact H | discriminate]. Qed.

(** String CONCATENATION and CONVERSIONS DENOTE (the [eval_value] folds are in [eval_value_good]; these pin the
    stronger [folded_arg] — evaluable AND printable): [`"a" + "b"`], the ASCII rune [`string(65)`], the
    identity [`string("a"+"b")`]. *)
Example folded_arg_str_concat : folded_arg (EBn BAdd (EStr "a") (EStr "b")) = true.
Proof. vm_compute. reflexivity. Qed.
Example folded_arg_runeconv_ascii :
  folded_arg (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) = true.
Proof. vm_compute. reflexivity. Qed.

(** BOUNDARY PIN (keeps the converse EXACT — pins the FULL state, not just non-denotability): a MULTI-BYTE rune
    [`string(200)`] (UTF-8 = 2 bytes — [eval_str] folds only [0,127]) is SUPPORTED at the classifier AND the gate
    ([ptype] = [PtStr], [printable_arg_ok], so [println(string(200))] is a [supported_program]) yet ABSENT
    ([eval_value] = [None], so the program does NOT denote).  Pinning support+absence TOGETHER stops the boundary
    from silently sliding to "rejected" (if [ptype] dropped it) or "wrong" (if [eval] folded it).  Until
    multi-byte rune encoding is modelled, these stay OUTSIDE the denoted fragment, faithfully absent. *)
Definition runeconv_mb : GExpr := ECall (EId (mkIdent "string" eq_refl)) [EInt 200].
Definition runeconv_mb_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb]); GsReturn].
Example runeconv_multibyte_boundary :
  ptype runeconv_mb = Some PtStr                  (* SUPPORTED at the classifier (a valid [PtStr]) *)
  /\ printable_arg_ok runeconv_mb = true          (* ... and printable *)
  /\ supported_program runeconv_mb_prog = true    (* ... so [println(string(200))] IS a supported program *)
  /\ eval_value runeconv_mb = None                (* yet ABSENT: the multi-byte rune is not folded *)
  /\ denote_program runeconv_mb_prog = None.      (* ... so the SUPPORTED program does NOT denote (faithful-or-absent) *)
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma eval_args_denotable : forall args, forallb folded_arg args = true -> eval_args args <> None.
Proof.
  induction args as [|a rest IH]; simpl; intro H; [discriminate|].
  apply andb_true_iff in H as [Ha Hrest]. specialize (IH Hrest).
  pose proof (folded_arg_eval a Ha) as Hva.
  destruct (eval_value a); [|exfalso; apply Hva; reflexivity].
  destruct (eval_args rest); [discriminate | exfalso; apply IH; reflexivity].
Qed.

Lemma forallb_denotable_printable : forall args,
  forallb folded_arg args = true -> forallb printable_arg_ok args = true.
Proof.
  induction args as [|a rest IH]; simpl; intro H; [reflexivity|].
  apply andb_true_iff in H as [Ha Hrest]. rewrite (folded_arg_printable a Ha), (IH Hrest). reflexivity.
Qed.

(** THE CONVERSE AUTHORITY — [supported ⟹ denotes] on the PRINT/PRINTLN-of-FOLDED-ARGS fragment.  A
    [folded_arg] (EVALUATES + PRINTABLE) certainly denotes — sufficient, NOT the full denotation boundary
    (the runtime tier denotes more).  [out_call pr]: [println]
    (pr=true) / [print] (pr=false) — the gate admits both ([stmt_call_ok]), and [print] denotes identically with
    the [COut] flag FALSE.  ⚠ This is a FRAGMENT, NOT the whole supported output class in EITHER direction:
    the runtime tier denotes MORE than the folded fragment ([println(int64(len([]int{1})))] = [runconv_e] is
    NOT [folded_arg] yet DENOTES since tier R3 — [runtime_conv_runs]; the tier's own converse is future
    work), and some supported args do not denote AT ALL yet ([println(string(200))], the multi-byte
    rune — pinned by [out_boundary_runtime_undenoted]).  [println_main_denotes]
    below is the all-[println] COROLLARY. *)
Definition out_call (pr : bool) (args : list GExpr) : GExpr :=
  if pr then ECall (EId (mkIdent "println" eq_refl)) args
        else ECall (EId (mkIdent "print" eq_refl)) args.
Fixpoint out_main_body (stmts : list (bool * list GExpr)) : list GoStmt :=
  match stmts with
  | [] => [GsReturn]
  | (pr, args) :: rest => GsExprStmt (out_call pr args) :: out_main_body rest
  end.
Lemma expr_stmt_ok_out_denotable : forall f args,
  (proj1_sig f = "println"%string \/ proj1_sig f = "print"%string) -> forallb folded_arg args = true ->
  expr_stmt_ok (ECall (EId f) args) = true.
Proof.
  intros f args Hf Hargs. cbn [expr_stmt_ok stmt_call_ok].
  destruct Hf as [Hf|Hf]; rewrite Hf; cbn; rewrite (forallb_denotable_printable args Hargs); reflexivity.
Qed.
(** A print/println of denotable args denotes — as a CONTINUER ([Some (_, false)]): the shape [denotable_body]
    consumes when it is followed by more statements. *)
Lemma denote_out_denotable : forall f args,
  (proj1_sig f = "println"%string \/ proj1_sig f = "print"%string) -> forallb folded_arg args = true ->
  exists c, denote_stmt (GsExprStmt (ECall (EId f) args)) = Some (c, false).
Proof.
  intros f args Hf Hargs. cbn [denote_stmt]. unfold denote_call.
  rewrite (expr_stmt_ok_out_denotable f args Hf Hargs).
  destruct Hf as [Hf|Hf]; rewrite Hf; cbn;
    (destruct (eval_args args) as [vs|] eqn:Ea;
      [ rewrite (denote_args_pure args vs Ea); eexists; reflexivity
      | exfalso; exact (eval_args_denotable args Hargs Ea) ]).
Qed.
Lemma denote_out_call_denotable : forall pr args,
  forallb folded_arg args = true ->
  exists c, denote_stmt (GsExprStmt (out_call pr args)) = Some (c, false).
Proof.
  intros pr args Hargs. destruct pr; cbn [out_call].
  - exact (denote_out_denotable (mkIdent "println" eq_refl) args (or_introl eq_refl) Hargs).
  - exact (denote_out_denotable (mkIdent "print" eq_refl) args (or_intror eq_refl) Hargs).
Qed.
Lemma out_main_denotable : forall stmts,
  forallb (fun s => forallb folded_arg (snd s)) stmts = true -> denotable_body (out_main_body stmts) = true.
Proof.
  induction stmts as [|[pr args] rest IH]; intro H.
  - reflexivity.
  - cbn in H. apply andb_true_iff in H as [Hargs Hrest]. cbn [out_main_body].
    destruct (denote_out_call_denotable pr args Hargs) as [c Hc].
    cbn [denotable_body]. rewrite Hc. exact (IH Hrest).
Qed.
Theorem out_main_denotes : forall stmts,
  forallb (fun s => forallb folded_arg (snd s)) stmts = true ->
  denote_program (mkProgram (mkIdent "main" eq_refl) (out_main_body stmts)) <> None.
Proof.
  intros stmts H. apply (proj2 (denote_program_dec _)).
  cbn [denotable_program prog_pkg prog_body proj1_sig]. exact (out_main_denotable stmts H).
Qed.

Corollary denotable_supported : forall p, denotable_program p = true -> supported_program p = true.
Proof. intros p H. apply gosem_sound, (proj2 (denote_program_dec p)), H. Qed.

(** Grounding fixture: a multi-statement `func main(){ println("a"); println("b"); return }` — its
    denotability is pinned in [gosem_denotability_decisions] below. *)
Definition gosem_strlit_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "a"]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "b"]); GsReturn].

(** [println_main_denotes] — the all-[println] COROLLARY of [out_main_denotes]: a `main` body of N
    [println(args)] (every arg [folded_arg]) + [return] denotes.  [println_main_body] is [out_main_body] with
    every flag [true] ([println_main_body_out]); kept for the [gosem_strlit] / `_runs` demos. *)
Fixpoint println_main_body (arglists : list (list GExpr)) : list GoStmt :=
  match arglists with
  | [] => [GsReturn]
  | args :: rest => GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) args) :: println_main_body rest
  end.
Lemma println_main_body_out : forall arglists,
  println_main_body arglists = out_main_body (map (fun a => (true, a)) arglists).
Proof.
  induction arglists as [|args rest IH]; [reflexivity|].
  cbn [println_main_body out_main_body map out_call]. rewrite IH. reflexivity.
Qed.
Lemma folded_arglists_out : forall arglists,
  forallb (forallb folded_arg) arglists = true ->
  forallb (fun s => forallb folded_arg (snd s)) (map (fun a => (true, a)) arglists) = true.
Proof.
  induction arglists as [|args rest IH]; [reflexivity|].
  cbn; intro H; apply andb_true_iff in H as [Ha Hr]; rewrite Ha; cbn; exact (IH Hr).
Qed.
Theorem println_main_denotes : forall arglists,
  forallb (forallb folded_arg) arglists = true ->
  denote_program (mkProgram (mkIdent "main" eq_refl) (println_main_body arglists)) <> None.
Proof.
  intros arglists H. rewrite (println_main_body_out arglists).
  exact (out_main_denotes _ (folded_arglists_out arglists H)).
Qed.

(** Coverage (the all-[println] corollary): MIXED evaluable args — `println("a"); println(int64(3)); return`
    denotes (a string literal AND an integer-constant conversion), not just strings. *)
Example println_main_denotes_mixed :
  denote_program (mkProgram (mkIdent "main" eq_refl)
    (println_main_body [[EStr "a"]; [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]]])) <> None.
Proof. apply println_main_denotes. reflexivity. Qed.

(** Coverage: a MIXED print+println body denotes — [println("a"); print(int64(3)); return]. *)
Example out_main_denotes_mixed :
  denote_program (mkProgram (mkIdent "main" eq_refl)
    (out_main_body [(true, [EStr "a"]); (false, [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]])])) <> None.
Proof. apply out_main_denotes. reflexivity. Qed.
(** ONE spelling for the recurring effectful-fixture expressions (the aliasing discipline — no drift).
    [divzero_e]/[divzero_map_e] = the determined divide-by-zero through each empty-literal [len];
    [maplen_e] = a fully-evaluable map-[len] (DENOTES — [eval_value_good]/[rc_maplen]); [runlen_e] (a
    slice-[len] whose ELEMENT is runtime — DENOTES since tier R1, [runtime_tier_runs], though still
    eval-level absent); [runidx_e] (a RUNTIME slice index — DENOTES since tier R2, [runtime_index_runs]);
    [runconv_e] (a RUNTIME width conversion — DENOTES since tier R3, [runtime_conv_runs]); [runbool_e]
    (a RUNTIME bool comparison — DENOTES since tier R4, [runtime_bool_runs]) and [maplen_runval_e] (a
    map-[len] whose VALUE is runtime — DENOTES since tier R5, [runtime_maplen_runs]).  These are LOCAL
    fixture spellings; the pinned witness group for the gap is [undenoted_frontier] below. *)
Definition divzero_e : GExpr :=
  EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt []]).
Definition divzero_map_e : GExpr :=
  EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt GTInt []]).
Definition maplen_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]].
Definition runlen_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]].
Definition runidx_e : GExpr :=
  EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]).
Definition runconv_e : GExpr :=
  ECall (EId (mkIdent "int64" eq_refl)) [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]].
Definition runbool_e : GExpr :=
  EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0).
Definition maplen_runval_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTInt [(EInt 1, ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 2]])]].

(** BOUNDARY — the fragment is NOT the whole supported output class: [println(string(200))] (the
    MULTI-BYTE rune, [runeconv_mb]) is SUPPORTED (valid Go) yet its arg is an EVAL-PARTIAL constant
    GoSem does not fold (multi-byte rune encoding unmodelled; NOT [folded_arg]; not a runtime-tier form
    either), so the program does NOT denote ([runeconv_mb_prog] — the same program
    [runeconv_multibyte_boundary] pins; [eval_value runlen_e = None] remains the strictness pin for
    the EVAL-level [eval_len_supported] inclusion). *)
Example out_boundary_runtime_undenoted :
  supported_program runeconv_mb_prog = true
  /\ folded_arg runeconv_mb = false
  /\ denote_program runeconv_mb_prog = None
  /\ eval_value runlen_e = None.   (* the eval-level strictness pin survives the tier: constant folds only *)
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ---- GENERAL statement-compositional CONVERSE: a body whose EVERY statement INDIVIDUALLY denotes is
    denotable, so its `main` DENOTES — generalizing [out_main_denotes] to ALL denoting statement forms
    interleaved, including a terminator followed by (supported) DEAD code.  SUFFICIENT, not necessary: a
    terminator's unreachable rest need only be SUPPORTED.  STILL CONDITIONAL on [stmt_denotable], NOT full
    [supported_program] — the gap is representatively witnessed by [undenoted_frontier] (see its comment). *)
Definition stmt_denotable (s : GoStmt) : bool :=
  match denote_stmt s with Some _ => true | None => false end.

Lemma stmt_denotable_ok : forall s, stmt_denotable s = true -> stmt_ok s = true.
Proof.
  intros s H. unfold stmt_denotable in H.
  destruct (denote_stmt s) eqn:Es; [|discriminate H].
  apply denote_stmt_sound. rewrite Es. discriminate.
Qed.

Lemma forallb_stmt_denotable_ok : forall b,
  forallb stmt_denotable b = true -> forallb stmt_ok b = true.
Proof.
  induction b as [|s rest IH]; [reflexivity|]. cbn [forallb]. intro H.
  apply andb_true_iff in H as [Hs Hr]. rewrite (stmt_denotable_ok s Hs). exact (IH Hr).
Qed.

Lemma denotable_body_of_stmts : forall b,
  forallb stmt_denotable b = true -> denotable_body b = true.
Proof.
  induction b as [|s rest IH]; [reflexivity|]. cbn [forallb denotable_body]. intro H.
  apply andb_true_iff in H as [Hs Hrest]. unfold stmt_denotable in Hs.
  destruct (denote_stmt s) as [[c term]|] eqn:Es; [|discriminate Hs].
  destruct term.
  - exact (forallb_stmt_denotable_ok rest Hrest).   (* terminator: unreachable rest need only be SUPPORTED *)
  - exact (IH Hrest).                                (* continuer: rest must itself be DENOTABLE *)
Qed.

Theorem denotable_stmts_main_denotes : forall b,
  forallb stmt_denotable b = true ->
  denote_program (mkProgram (mkIdent "main" eq_refl) b) <> None.
Proof.
  intros b H. apply (proj2 (denote_program_dec _)).
  cbn [denotable_program prog_pkg prog_body proj1_sig]. exact (denotable_body_of_stmts b H).
Qed.

(** Coverage — a MIXED body [out_main_denotes] CANNOT express: [println("a"); _ = int64(3); panic("boom");
    println("dead")] interleaves a continuer output call, a blank constant-assignment, a [panic] TERMINATOR,
    and a SUPPORTED dead tail — and DENOTES by APPLYING the general converse (not a black-box compute). *)
Example denotable_stmts_mixed_denotes :
  denote_program (mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "a"]);
     GsBlankAssign (ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]);
     GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "boom"]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "dead"])]) <> None.
Proof. apply denotable_stmts_main_denotes. reflexivity. Qed.

(** A value-carrying int-constant category ([int_const_val] = [Some]) IS an int category — so a constant slice
    INDEX satisfies [ptype]'s [is_int_cat] guard.  (Bridges the reduction hyps to [ptype]'s supportedness.) *)
Lemma int_const_val_is_int_cat :
  forall ci k, int_const_val ci = Some k -> is_int_cat ci = true.
Proof. intros ci k H; destruct ci; cbn in H; try discriminate; reflexivity. Qed.

(** The SEALED evaluator's accept-set ⊆ [ptype]'s element check: if [eval_int_slice_elems] succeeds, EVERY
    element is [assignable_to_ty _ t] — exactly [ptype]'s slice-literal [forallb] gate.  (Induction on [es].) *)
Lemma eval_int_slice_elems_forall_assignable :
  forall t es vs, eval_int_slice_elems t es = Some vs ->
    forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es = true.
Proof.
  intros t es. induction es as [|el rest IH]; intros vs H.
  - reflexivity.
  - cbn [forallb]. cbn [eval_int_slice_elems] in H.
    destruct (ptype el) as [ce|] eqn:Ec; [|discriminate H].          (* [destruct] reduces the [match ptype el] in BOTH goal and H *)
    destruct (assignable_to_ty ce t) eqn:Ea; [|discriminate H]. cbn [andb].
    destruct (int_const_val ce) as [z|] eqn:Ev; [|discriminate H].
    destruct (box_int t z) as [v|] eqn:Eb; [|discriminate H].
    destruct (eval_int_slice_elems t rest) as [vs'|] eqn:Er; [|discriminate H].
    exact (IH vs' eq_refl).   (* [destruct]'s substitution rewrote IH's premise to [Some vs' = Some vs] *)
Qed.

(** ★ SUPPORTEDNESS INCLUSION BRIDGE — the reduction's hypotheses IMPLY [ptype = Some (PtRunInt t)] (valid
    Rocq-Go).  A strict INCLUSION, not an equivalence: the fully-evaluable all-constant subfragment ⊊
    [ptype]-supported ([ptype] also admits a RUNTIME index / RUNTIME same-typed elements — EVAL-level absent,
    strictness pinned by [slice_index_supported_but_undenoted]; the runtime TIER denotes them since R2).  The
    evaluator consults [ptype]'s OWN element/index checks, so there is no looser private boundary. *)
Lemma eval_slice_index_supported :
  forall t es idx ci k vs,
    is_int_goty t = true ->
    ptype idx = Some ci ->
    int_const_val ci = Some k ->
    (0 <=? k)%Z = true ->
    int_const_repr k GTInt = true ->
    eval_int_slice_elems t es = Some vs ->
    ptype (EIndex (ESliceLit t es) idx) = Some (PtRunInt t).
Proof.
  intros t es idx ci k vs Ht Hp Hi Hk Hr Hv.
  pose proof (eval_int_slice_elems_forall_assignable t es vs Hv) as Hall.
  pose proof (int_const_val_is_int_cat ci k Hi) as Hcat.
  (* iota-only reductions ([cbv beta iota]) keep [int_const_repr]/[andb] FOLDED so [rewrite Hr]/[Hk] still find them;
     [cbn [ptype]] exposes the arm without touching the folded helpers. *)
  cbn [ptype].
  rewrite Ht, Hall. cbv beta iota delta [andb].
  rewrite Hp. cbv beta iota.
  rewrite Hcat. cbv beta iota.
  rewrite Hi. cbv beta iota.
  rewrite Hk, Hr. cbv beta iota delta [andb].
  reflexivity.
Qed.

(** ★ CLASS THEOREM — the generic reduction over the fully-evaluable all-constant slice-index subfragment (any
    int element type [t], any fully-evaluating literal [es], any non-negative int-representable constant [k]):
    [eval_value] of the index = [nth_error vs (Z.to_nat k)].  The two corollaries below discharge both
    [nth_error] cases — in-bounds ⇒ the k-th boxed element VALUE, OOB ⇒ [None] — for the whole subfragment. *)
Lemma eval_slice_index_reduces :
  forall t es idx ci k vs,
    floats_checked (EIndex (ESliceLit t es) idx) = true ->
    is_int_goty t = true ->
    ptype idx = Some ci ->
    int_const_val ci = Some k ->
    (0 <=? k)%Z = true ->
    int_const_repr k GTInt = true ->
    eval_int_slice_elems t es = Some vs ->
    eval_value (EIndex (ESliceLit t es) idx) = nth_error vs (Z.to_nat k).
Proof.
  intros t es idx ci k vs Hfc Ht Hp Hi Hk Hr Hv.
  unfold eval_value. rewrite Hfc.
  (* Expose the [EIndex (ESliceLit..)] arm ([cbn [eval_value]] keeps [is_int_goty t]/[int_const_repr] FOLDED —
     whitelist delta), then rewrite each scrutinee and IOTA-reduce (never full [cbn], which would unfold
     [int_const_repr] and defeat [rewrite Hr]) the match it heads before the next rewrite. *)
  cbn [eval_value_core].
  rewrite Ht. cbv beta iota.
  rewrite Hp. cbv beta iota.
  rewrite Hi. cbv beta iota.
  rewrite Hk, Hr. cbv beta iota delta [andb].
  rewrite Hv. reflexivity.
Qed.

(** CLASS — OOB DECLINED: a constant index AT OR PAST the (fully-evaluated) length folds to [None], for the
    whole fully-evaluable all-constant subfragment (never a wrong value — faithful-or-absent). *)
Lemma eval_slice_index_oob_class :
  forall t es idx ci k vs,
    floats_checked (EIndex (ESliceLit t es) idx) = true ->
    is_int_goty t = true ->
    ptype idx = Some ci ->
    int_const_val ci = Some k ->
    (0 <=? k)%Z = true ->
    int_const_repr k GTInt = true ->
    eval_int_slice_elems t es = Some vs ->
    (length vs <= Z.to_nat k)%nat ->
    eval_value (EIndex (ESliceLit t es) idx) = None.
Proof.
  intros t es idx ci k vs Hfc Ht Hp Hi Hk Hr Hv Hoob.
  rewrite (eval_slice_index_reduces t es idx ci k vs Hfc Ht Hp Hi Hk Hr Hv).
  apply (proj2 (nth_error_None vs (Z.to_nat k))). exact Hoob.
Qed.

(** CLASS — IN-BOUNDS FAITHFUL: a constant index STRICTLY WITHIN the length folds to the k-th boxed element
    VALUE (a real [Some], never [None]), for the whole fully-evaluable all-constant subfragment. *)
Lemma eval_slice_index_inbounds_class :
  forall t es idx ci k vs,
    floats_checked (EIndex (ESliceLit t es) idx) = true ->
    is_int_goty t = true ->
    ptype idx = Some ci ->
    int_const_val ci = Some k ->
    (0 <=? k)%Z = true ->
    int_const_repr k GTInt = true ->
    eval_int_slice_elems t es = Some vs ->
    (Z.to_nat k < length vs)%nat ->
    exists v, eval_value (EIndex (ESliceLit t es) idx) = Some v /\ nth_error vs (Z.to_nat k) = Some v.
Proof.
  intros t es idx ci k vs Hfc Ht Hp Hi Hk Hr Hv Hin.
  rewrite (eval_slice_index_reduces t es idx ci k vs Hfc Ht Hp Hi Hk Hr Hv).
  pose proof (proj2 (nth_error_Some vs (Z.to_nat k)) Hin) as Hne.
  destruct (nth_error vs (Z.to_nat k)) as [v|] eqn:E.
  - exists v. split; reflexivity.
  - exfalso. apply Hne. reflexivity.
Qed.

(** ★ CLASS THEOREM ([len]) — over the same fully-evaluable all-constant subfragment: [len] of a literal that
    FULLY evaluates folds to its LENGTH, boxed as Go's [int] (range-checked).  Go evaluates the literal before
    [len], so a runtime/panicking element declines the fold — the whole-literal discipline shared with the
    index arm. *)
Lemma eval_len_reduces : forall t es f vs,
  floats_checked (ECall (EId f) (ESliceLit t es :: nil)) = true ->
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty t = true ->
  eval_int_slice_elems t es = Some vs ->
  eval_value (ECall (EId f) (ESliceLit t es :: nil)) = box_int GTInt (Z.of_nat (length vs)).
Proof.
  intros t es f vs Hfc Hf Ht Hv.
  unfold eval_value. rewrite Hfc.
  cbn [eval_value_core].
  rewrite Hf, Ht. cbv beta iota delta [andb].
  rewrite Hv. reflexivity.
Qed.

(** ★ SUPPORTEDNESS INCLUSION BRIDGE ([len]) — the fold's hypotheses IMPLY [ptype = Some (PtRunInt GTInt)]
    (valid Rocq-Go; [ptype] classifies a slice-[len] RUNTIME, exactly as it does the index — the evaluator
    folds the determined VALUE without loosening the gate).  A strict INCLUSION at the EVAL level: [ptype]
    also admits [len] of a literal with runtime elements, which the CONSTANT fold leaves unfolded (the
    [eval_value runlen_e = None] conjunct of [out_boundary_runtime_undenoted]; the runtime TIER denotes it). *)
Lemma is_int_goty_supported : forall t, is_int_goty t = true -> goty_supported t = true.
Proof. destruct t; intro H; first [reflexivity | discriminate H]. Qed.

Lemma eval_len_supported : forall t es f vs,
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty t = true ->
  eval_int_slice_elems t es = Some vs ->
  ptype (ECall (EId f) (ESliceLit t es :: nil)) = Some (PtRunInt GTInt).
Proof.
  intros t es f vs Hf Ht Hv.
  pose proof (eval_int_slice_elems_forall_assignable t es vs Hv) as Hall.
  pose proof (is_int_goty_supported t Ht) as Hvt.
  cbn [ptype]. rewrite Hvt, Hall. cbv beta iota zeta delta [andb].
  rewrite Hf. cbv beta iota.
  reflexivity.
Qed.

(** The SEALED evaluability check's accept-set ⊆ [ptype]'s entry check: if [map_entries_evaluable] holds,
    EVERY entry passes exactly [ptype]'s map-arm [forallb] gate (integer-CONSTANT key, both sides
    assignable).  (Induction on [kvs] — the [eval_int_slice_elems_forall_assignable] discipline.) *)
Lemma map_entries_evaluable_forall_entry :
  forall kt vt kvs, map_entries_evaluable kt vt kvs = true ->
    forallb (fun kv => match kv with
                       | (k, v) =>
                           match ptype k, ptype v with
                           | Some ck, Some cv =>
                               match int_const_val ck with
                               | Some _ => andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                               | None => false
                               end
                           | _, _ => false
                           end
                       end) kvs = true.
Proof.
  intros kt vt kvs. induction kvs as [|[k v] rest IH]; intro H.
  - reflexivity.
  - cbn [forallb]. cbn [map_entries_evaluable] in H.
    destruct (ptype k) as [ck|] eqn:Ek; [|discriminate H].
    destruct (ptype v) as [cv|] eqn:Ev; [|discriminate H].
    destruct (assignable_to_ty ck kt) eqn:Ea1; [|discriminate H].
    destruct (assignable_to_ty cv vt) eqn:Ea2; [|discriminate H].
    destruct (int_const_val ck) as [z|] eqn:Ei; [|discriminate H].
    destruct (box_int kt z) as [bk|] eqn:Eb; [|discriminate H].
    destruct (eval_value_ptype_core v) as [bv|] eqn:Ebv; [|discriminate H].
    destruct (floats_checked k) eqn:Efk; [|discriminate H].
    destruct (floats_checked v) eqn:Efv; [|discriminate H].
    destruct (map_entries_evaluable kt vt rest) eqn:Er; [|discriminate H].
    exact (IH eq_refl).
Qed.

(** ★ CLASS THEOREM (map-[len]) — over the fully-evaluable all-constant-entry subfragment: [len] of a
    gate-supported-typed ([goty_supported]) integer-keyed map literal whose entries ALL evaluate (and whose constant keys
    are distinct — the gate's OWN [nodup_z] condition, so the entry count IS Go's [len]) folds to that
    count, boxed as Go's [int].  The side conditions are exactly the GATE's — never [is_int_goty kt]
    alone. *)
Lemma eval_map_len_reduces : forall kt vt kvs f,
  floats_checked (ECall (EId f) (EMapLit kt vt kvs :: nil)) = true ->
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty kt = true ->
  goty_supported vt = true ->
  nodup_z (map_key_vals kvs) = true ->
  map_entries_evaluable kt vt kvs = true ->
  eval_value (ECall (EId f) (EMapLit kt vt kvs :: nil)) = box_int GTInt (Z.of_nat (length kvs)).
Proof.
  intros kt vt kvs f Hfc Hf Ht Hvt Hnd Hev.
  unfold eval_value. rewrite Hfc.
  cbn [eval_value_core]. rewrite Hf, Ht, Hvt, Hnd, Hev. reflexivity.
Qed.

(** ★ SUPPORTEDNESS INCLUSION BRIDGE (map-[len]) — the fold's hypotheses IMPLY [ptype = Some (PtRunInt GTInt)]
    (valid Rocq-Go; the evaluator folds the determined count without loosening the gate).  A strict INCLUSION:
    [ptype] also admits a map literal with a RUNTIME value, which stays unfolded — strictness pinned by
    [map_len_eval_absent]. *)
Lemma eval_map_len_supported : forall kt vt kvs f,
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty kt = true ->
  goty_supported vt = true ->
  nodup_z (map_key_vals kvs) = true ->
  map_entries_evaluable kt vt kvs = true ->
  ptype (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some (PtRunInt GTInt).
Proof.
  intros kt vt kvs f Hf Ht Hvt Hnd Hev.
  pose proof (map_entries_evaluable_forall_entry kt vt kvs Hev) as Hall.
  unfold map_key_vals in Hnd.
  cbn [ptype]. rewrite Ht, Hvt, Hall, Hnd. cbv beta iota zeta delta [andb].
  rewrite Hf. cbv beta iota.
  reflexivity.
Qed.

(** ---- SLICE-INDEX fixtures (grouped; the CLASS theorems above are the authorities). ----
    DENOTING side: the [eval_value_good] rows [[]int{10,20}[1]]/[[0]]] (exact element values) + [rc_sliceidx]
    (end-to-end run).  DECLINED side, three layers on shared fixtures:
    - [slice_index_unsupported_ok]: invalid Go is REJECTED by [ptype] AND declined by [eval_value] — a
      wrong-typed element ([[]int{int64(1)}], not assignable to [int]) and a constant index over the
      CONSERVATIVE 32-bit [GTInt] ([2^40]); the evaluator's accept-set is never looser than [ptype]'s.
    - [slice_index_undenoted_ok]: [println(e); return] does NOT denote (and [eval_value e = None]) for the
      ptype-REJECTED shapes (the wrong-typed-element literal, an out-of-[uint8]-range element).  The VALID-Go
      OOB constant [[..][5]] and the runtime-PANICKING UNSELECTED element ([[]int{20, 1/len([]int{})}[0]],
      construction order verified `go run`) DENOTE their TRUE panics since tier R2 —
      [slice_index_panics_denote]. *)
Definition println_prog (e : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [e]); GsReturn].
Definition slice_index_unsupported : list GExpr :=
  [ EIndex (ESliceLit GTInt [ECall (EId (mkIdent "int64" eq_refl)) [EInt 1]]) (EInt 0)
  ; EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 1099511627776) ].
Example slice_index_unsupported_ok :
  forallb (fun e => match ptype e, eval_value e with None, None => true | _, _ => false end)
          slice_index_unsupported = true.
Proof. vm_compute. reflexivity. Qed.
Definition slice_index_undenoted : list GExpr :=
  [ EIndex (ESliceLit GTInt [ECall (EId (mkIdent "int64" eq_refl)) [EInt 1]]) (EInt 0)
  ; EIndex (ESliceLit GTU8 [EInt 300; EInt 1]) (EInt 1) ].
Example slice_index_undenoted_ok :
  forallb (fun e => match eval_value e, denote_program (println_prog e) with
                    | None, None => true | _, _ => false end)
          slice_index_undenoted = true.
Proof. vm_compute. reflexivity. Qed.
(** Since tier R2 the OOB CONSTANT index and the PANICKING-element construction DENOTE — to their TRUE
    runtime panics (the model's [rt_index_oob] / [rt_div_zero]), still EVAL-level absent: the behavioral
    boundary moved from non-denotation to a denoted [CPan] (which the panic-free gate rejects by
    [cmd_no_panic] — [GoSemSafe.panic_free_gate_slice]'s facts are unchanged). *)
Example slice_index_panics_denote : forall w,
  map (fun e => (eval_value e,
                 match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end))
      [ EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 5)
      ; EIndex (ESliceLit GTInt [EInt 20; EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt []])]) (EInt 0) ]
  = [ (None, Some (OPanic (rt_index_oob 5 2) w)) ; (None, Some (OPanic rt_div_zero w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
(** STRICT-SUBSET pin (GATED), at the EVAL level: a RUNTIME index and a RUNTIME same-typed element are
    [ptype]-SUPPORTED (valid Go) yet the CONSTANT fold leaves them absent — so [eval_slice_index_supported]
    is a strict INCLUSION, not equality.  (Since tier R2 BOTH shapes DENOTE through the runtime tier —
    [runtime_index_runs] — so the strictness claim is scoped to [eval_value] only.) *)
Example slice_index_supported_but_undenoted :
  ptype runidx_e = Some (PtRunInt GTInt)
  /\ eval_value runidx_e = None
  /\ ptype (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)) = Some (PtRunInt GTInt)
  /\ eval_value (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ★ RUNTIME-INDEX pins (tier R2, grouped): a RUNTIME in-bounds index yields the element
    ([]int{10,20}[len([]int{1})] prints 20); a runtime element under a CONSTANT index constructs then
    indexes ([]int{len([]int{1})}[0] prints 1); a runtime NEGATIVE index panics [rt_index_oob (-1) 2]
    (len([]int{1}) - len([]int{1,2}) = -1).  All supported (the gate unchanged). *)
Example runtime_index_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runidx_e
      ; EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)
      ; EIndex (ESliceLit GTInt [EInt 10; EInt 20])
               (EBn BSub (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])
                         (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2]])) ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 20) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (OPanic (rt_index_oob (-1) 2) w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_index_supported :
  forallb supported_program
    [ println_prog runidx_e
    ; println_prog (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)) ] = true.
Proof. vm_compute. reflexivity. Qed.

(** ★ RUNTIME-CONVERSION pins (tier R3, grouped): [int64(len([]int{1}))] EXITS the fragment at width
    int64 (prints 1 as the model's [GoI64]); [uint8(len([]int{1})*300)] TRUNCATES (Go's runtime wrap:
    300 mod 256 prints 44); [int(len([]int{1}))] is the IN-fragment same-width identity;
    [uint(len([]int{1}) - len([]int{1,2}))] WRAPS a negative runtime int to 2^64-1 (the [uintwrap]
    authority at a non-identity value); and a
    PANICKING arg panics FIRST ([int64(1/len([]int{}))] → [rt_div_zero] — Go evaluates the operand
    before converting).  All supported (the gate is unchanged). *)
Definition runconv_trunc_e : GExpr :=
  ECall (EId (mkIdent "uint8" eq_refl))
        [EBn BMul (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 300)].
Definition runconv_int_e : GExpr :=
  ECall (EId (mkIdent "int" eq_refl)) [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]].
Definition runconv_panic_e : GExpr :=
  ECall (EId (mkIdent "int64" eq_refl)) [divzero_e].
Definition runconv_uint_e : GExpr :=
  ECall (EId (mkIdent "uint" eq_refl))
        [EBn BSub (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])
                  (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2]])].
Example runtime_conv_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runconv_e ; runconv_trunc_e ; runconv_int_e ; runconv_uint_e ; runconv_panic_e ]
  = [ Some (ORet tt (w_log true (anyt TI64 (i64wrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 300) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TUint (uintwrap (-1)) :: nil) w))   (* uint(-1 runtime) = 2^64-1: the [uintwrap] branch exercised at a WRAPPING value *)
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_conv_supported :
  forallb supported_program
    [ println_prog runconv_e ; println_prog runconv_trunc_e
    ; println_prog runconv_int_e ; println_prog runconv_uint_e
    ; println_prog runconv_panic_e ] = true.
Proof. vm_compute. reflexivity. Qed.

(** ★ RUNTIME-BOOL pins (tier R4, grouped) — ALL SIX comparison operators on ASYMMETRIC operand pairs,
    each chosen so a drifted mapping (a swap in the wrong direction, a dropped negation, [<] confused
    with [<=]) flips the expected verdict.  The pairs as written: [==]/[!=] compare the RUNTIME
    [len([]int{1})] against the CONSTANT [0] (1 vs 0 — false then true, the negation); the four ORDER
    ops compare the two runtime lens ([len2 < len1] false, [len2 <= len1] false — strict AND non-strict
    in the wrong direction; [len2 > len1] true, [len1 >= len2] false — the argument swaps).  A
    PANICKING left operand panics before any comparison ([1/len([]int{}) == 1] → [rt_div_zero] — Go's
    order).  All supported (gate unchanged). *)
Definition runlen1_e : GExpr := ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]].
Definition runlen2_e : GExpr := ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2]].
Definition runbool_ne_e : GExpr := EBn BNe runlen1_e (EInt 0).
Definition runbool_lt_e : GExpr := EBn BLt runlen2_e runlen1_e.
Definition runbool_le_e : GExpr := EBn BLe runlen2_e runlen1_e.
Definition runbool_gt_e : GExpr := EBn BGt runlen2_e runlen1_e.
Definition runbool_ge_e : GExpr := EBn BGe runlen1_e runlen2_e.
Definition runbool_panic_e : GExpr := EBn BEq divzero_e (EInt 1).
Example runtime_bool_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runbool_e ; runbool_ne_e ; runbool_lt_e ; runbool_le_e ; runbool_gt_e ; runbool_ge_e
      ; runbool_panic_e ]
  = [ Some (ORet tt (w_log true (anyt TBool false :: nil) w))   (* 1 == 0 *)
    ; Some (ORet tt (w_log true (anyt TBool true  :: nil) w))   (* 1 != 0 *)
    ; Some (ORet tt (w_log true (anyt TBool false :: nil) w))   (* 2 <  1 *)
    ; Some (ORet tt (w_log true (anyt TBool false :: nil) w))   (* 2 <= 1 *)
    ; Some (ORet tt (w_log true (anyt TBool true  :: nil) w))   (* 2 >  1 *)
    ; Some (ORet tt (w_log true (anyt TBool false :: nil) w))   (* 1 >= 2 *)
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_bool_supported :
  forallb supported_program
    (map println_prog
      [ runbool_e ; runbool_ne_e ; runbool_lt_e ; runbool_le_e ; runbool_gt_e ; runbool_ge_e
      ; runbool_panic_e ]) = true.
Proof. vm_compute. reflexivity. Qed.

(** STRICT-SUBSET pin (GATED, map-[len]), at the EVAL level: a map literal whose VALUE is a same-typed
    RUNTIME int ([map[int]int{1: len([]int{2})}]) is [ptype]-SUPPORTED (valid Go) yet the CONSTANT fold
    leaves it absent — so [eval_map_len_supported] is a strict INCLUSION, not equality.  (Since tier R5
    the shape DENOTES through the runtime tier — [runtime_maplen_runs] — so the strictness claim is
    scoped to [eval_value] only.) *)
Example map_len_eval_absent :
  ptype maplen_runval_e = Some (PtRunInt GTInt)
  /\ eval_value maplen_runval_e = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ★ RUNTIME MAP-VALUE pins (tier R5, grouped): [len(map[int]int{1: len([]int{2})})] prints 1; a
    TWO-entry literal mixing a runtime and a constant value prints 2 (the fold declines it — one
    runtime value — so the COUNT comes from the tier); a SINGLE panicking value panics
    ([len(map[int]int{1: 1/len([]int{})})] → [rt_div_zero], before any output — order-independent);
    the shared-evaluator reach cases below; and the ORDER-AMBIGUITY witness: TWO distinct panicking
    values ([1/len([]int{})] and an OOB index) make the whole form ABSENT (supported, NOT denotable) —
    a WITNESS of the quantified seal [rconstr_vals_two_panics_absent], the class authority. *)
Definition maplen_run2_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTInt
          [(EInt 1, ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 2]]);
           (EInt 2, EInt 5)]].
Definition maplen_panic_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, divzero_e)]].
(** The SHARED-evaluator reach pins: values in R3-CONVERSION form ([int64(<runtime>)]), R4-COMPARISON
    form ([<runtime> == 1]), and a PANICKING R3-converted value construct/abort under a map literal
    EXACTLY as they denote standalone — one evaluator, no drift. *)
Definition maplen_i64_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTInt64 [(EInt 1, ECall (EId (mkIdent "int64" eq_refl))
                                               [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]])]].
Definition maplen_bool_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTBool [(EInt 1, EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 1))]].
Definition maplen_convpanic_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTInt64 [(EInt 1, ECall (EId (mkIdent "int64" eq_refl)) [divzero_e])]].
Definition maplen_ambig_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTInt
          [(EInt 1, divzero_e);
           (EInt 2, EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 5))]].
Example runtime_maplen_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ maplen_runval_e ; maplen_run2_e ; maplen_i64_e ; maplen_bool_e
      ; maplen_panic_e ; maplen_convpanic_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 2) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (OPanic rt_div_zero w)
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_maplen_supported :
  forallb supported_program
    (map println_prog [ maplen_runval_e ; maplen_run2_e ; maplen_i64_e ; maplen_bool_e
                      ; maplen_panic_e ; maplen_convpanic_e ; maplen_ambig_e ]) = true.
Proof. vm_compute. reflexivity. Qed.
Example runtime_maplen_ambiguous_absent :
  denotable_program (println_prog maplen_ambig_e) = false
  /\ denote_program (println_prog maplen_ambig_e) = None.
Proof. split; vm_compute; reflexivity. Qed.

(** The determined divide-by-zero through the MAP shape: [_ = 1 / len(map[int]int{})] is SUPPORTED (valid Go —
    a runtime integer division) and denotes+runs to the exact panic, like [rc_div_zero]'s slice shape (the
    runtime tier evaluates BOTH empty-literal [len] divisors to 0 through [eval_value]'s own folds — the
    constant tier stays the single fold authority). *)
Definition gosem_maplen_divzero_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign divzero_map_e].
Example maplen_divzero_runs : forall w,
  supported_program gosem_maplen_divzero_prog = true
  /\ match denote_program gosem_maplen_divzero_prog with
     | Some c => run_cmd 5 c w | None => None end = Some (OPanic rt_div_zero w).
Proof. intro w; split; vm_compute; reflexivity. Qed.

(** ★ RUNTIME-TIER pins (R1, grouped): the closed world DETERMINES runtime integer values, and the tier
    computes them with the MODEL'S OWN ops — [println(runlen_e)] (a len over a RUNTIME element) prints 1;
    a runtime [/] of runtime [len]s prints its quotient (the model's [int_div]); and a PANICKING element
    ABORTS literal construction ([println(len([]int{20, 1/len([]int{})}))] panics with [rt_div_zero]
    BEFORE any output — the verified go-run order).  All three SUPPORTED (the gate is unchanged). *)
Definition runtime_div_vals_e : GExpr :=
  EBn BDiv (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2; EInt 3; EInt 4; EInt 5; EInt 6]])
           (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2]]).
Definition panicking_elem_len_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 20; divzero_e]].
Example runtime_tier_runs : forall w,
  map (fun p => match denote_program p with Some c => run_cmd 5 c w | None => None end)
      [println_prog runlen_e; println_prog runtime_div_vals_e; println_prog panicking_elem_len_e]
  = [Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w));
     Some (ORet tt (w_log true (anyt TInt64 (intwrap 3) :: nil) w));
     Some (OPanic rt_div_zero w)].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_tier_supported :
  forallb supported_program
    [println_prog runlen_e; println_prog runtime_div_vals_e; println_prog panicking_elem_len_e] = true.
Proof. vm_compute. reflexivity. Qed.

(** ★ R6 pins (grouped): runtime unary MINUS ([-len([]int{1,2,3})] prints -3, the model's [int_neg]);
    nonzero runtime [%] ([7 % len([]int{1,2,3})] prints 1, the model's evidence-carrying [int_mod]);
    the NEGATIVE-dividend remainder ([-7 % len(..3)] prints -1 — Go's TRUNCATED [%], [Z.rem]'s sign);
    and a PANICKING unary operand propagates ([-(1/len([]int{}))] → [rt_div_zero]).  All supported. *)
Definition runlen3_e : GExpr := ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2; EInt 3]].
Definition runneg_e : GExpr := EUn UNeg runlen3_e.
Definition runrem_e : GExpr := EBn BRem (EInt 7) runlen3_e.
Definition runrem_neg_e : GExpr := EBn BRem (EUn UNeg (EInt 7)) runlen3_e.
Definition runneg_panic_e : GExpr := EUn UNeg divzero_e.
Example runtime_negrem_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runneg_e ; runrem_e ; runrem_neg_e ; runneg_panic_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap (-3)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap (-1)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_negrem_supported :
  forallb supported_program
    (map println_prog [ runneg_e ; runrem_e ; runrem_neg_e ; runneg_panic_e ]) = true.
Proof. vm_compute. reflexivity. Qed.

(** ★ R7 pins (grouped): runtime [^] COMPLEMENT via the model's [int_not] ([^len([]int{1,2,3})]
    prints -4 — the go-run-verified [-x-1]); a PANICKING operand propagates. *)
Definition runnot_e : GExpr := EUn UXor runlen3_e.
Definition runnot_panic_e : GExpr := EUn UXor divzero_e.
Example runtime_not_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runnot_e ; runnot_panic_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap (-4)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_not_supported :
  forallb supported_program (map println_prog [ runnot_e ; runnot_panic_e ]) = true.
Proof. vm_compute. reflexivity. Qed.

(** ★ T1 pins (typed unary, grouped): [^int64(len3)] and [^uint8(len3)] DENOTE at their widths via
    the model's [i64_not]/[u8_not] (the R3-converted operand evaluated at full power); [-int64(len3)]
    via [i64_neg]; a PANICKING typed operand propagates.  The HOLES stay absent — sealed by
    [typed_unop_holes_none] (every ptype-reachable absent cell, every payload) and witnessed
    eight-wide at the program level ([typed_unary_holes_absent]).
    [typed_unop]'s live branches are pinned against the QUALIFIED model ops and its holes to [None]
    ([typed_unop_*] below) — the dispatch cannot drift while the surface is green. *)
Definition runnot_i64_e : GExpr := EUn UXor (ECall (EId (mkIdent "int64" eq_refl)) [runlen3_e]).
Definition runnot_u8_e  : GExpr := EUn UXor (ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e]).
Definition runnot_uint_e : GExpr := EUn UXor (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]).
Definition runneg_i64_e : GExpr := EUn UNeg (ECall (EId (mkIdent "int64" eq_refl)) [runlen3_e]).
Definition runneg_u8_e  : GExpr := EUn UNeg (ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e]).
Definition runneg_i8_e  : GExpr := EUn UNeg (ECall (EId (mkIdent "int8" eq_refl)) [runlen3_e]).
Definition runneg_u16_e : GExpr := EUn UNeg (ECall (EId (mkIdent "uint16" eq_refl)) [runlen3_e]).
Definition runneg_i16_e : GExpr := EUn UNeg (ECall (EId (mkIdent "int16" eq_refl)) [runlen3_e]).
Definition runneg_u32_e : GExpr := EUn UNeg (ECall (EId (mkIdent "uint32" eq_refl)) [runlen3_e]).
Definition runneg_i32_e : GExpr := EUn UNeg (ECall (EId (mkIdent "int32" eq_refl)) [runlen3_e]).
Definition runneg_uint_e : GExpr := EUn UNeg (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]).
Definition runnot_panic_i64_e : GExpr :=
  EUn UXor (ECall (EId (mkIdent "int64" eq_refl)) [divzero_e]).
Example runtime_typed_unop_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runnot_i64_e ; runnot_u8_e ; runneg_i64_e ; runnot_panic_i64_e ]
  = [ Some (ORet tt (w_log true (anyt TI64 (i64_not (i64wrap 3)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8  (u8_not  (u8wrap  3)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TI64 (i64_neg (i64wrap 3)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_typed_unop_supported :
  forallb supported_program
    (map println_prog [ runnot_i64_e ; runnot_u8_e ; runneg_i64_e ; runnot_panic_i64_e ]) = true.
Proof. vm_compute. reflexivity. Qed.
Example typed_unary_holes_absent :
  forallb (fun e => supported_program (println_prog e)
                    && negb (denotable_program (println_prog e))
                    && match denote_program (println_prog e) with None => true | Some _ => false end)
          [ runnot_uint_e
          ; runneg_uint_e ; runneg_u8_e ; runneg_i8_e ; runneg_u16_e
          ; runneg_i16_e ; runneg_u32_e ; runneg_i32_e ] = true.
Proof. vm_compute. reflexivity. Qed.
(** DISPATCH AUTHORITY (gated): each live [typed_unop] branch IS the fully qualified model op; the
    holes are sealed by the COMPLETE quantified theorem [typed_unop_holes_none] below. *)
Example typed_unop_u8_model  : forall v, typed_unop UXor GTU8  (anyt TU8  v) = Some (anyt TU8  (Fido.builtins.u8_not v)).
Proof. reflexivity. Qed.
Example typed_unop_i8_model  : forall v, typed_unop UXor GTI8  (anyt TI8  v) = Some (anyt TI8  (Fido.builtins.i8_not v)).
Proof. reflexivity. Qed.
Example typed_unop_u16_model : forall v, typed_unop UXor GTU16 (anyt TU16 v) = Some (anyt TU16 (Fido.builtins.u16_not v)).
Proof. reflexivity. Qed.
Example typed_unop_i16_model : forall v, typed_unop UXor GTI16 (anyt TI16 v) = Some (anyt TI16 (Fido.builtins.i16_not v)).
Proof. reflexivity. Qed.
Example typed_unop_u32_model : forall v, typed_unop UXor GTU32 (anyt TU32 v) = Some (anyt TU32 (Fido.builtins.u32_not v)).
Proof. reflexivity. Qed.
Example typed_unop_i32_model : forall v, typed_unop UXor GTI32 (anyt TI32 v) = Some (anyt TI32 (Fido.builtins.i32_not v)).
Proof. reflexivity. Qed.
Example typed_unop_i64_model : forall v, typed_unop UXor GTInt64 (anyt TI64 v) = Some (anyt TI64 (Fido.builtins.i64_not v)).
Proof. reflexivity. Qed.
Example typed_unop_u64_model : forall v, typed_unop UXor GTU64 (anyt TU64 v) = Some (anyt TU64 (Fido.builtins.u64_not v)).
Proof. reflexivity. Qed.
Example typed_unop_neg_i64_model : forall v, typed_unop UNeg GTInt64 (anyt TI64 v) = Some (anyt TI64 (Fido.builtins.i64_neg v)).
Proof. reflexivity. Qed.
Example typed_unop_neg_u64_model : forall v, typed_unop UNeg GTU64 (anyt TU64 v) = Some (anyt TU64 (Fido.builtins.u64_neg v)).
Proof. reflexivity. Qed.
(** THE COMPLETE HOLE THEOREM — every ptype-reachable absent cell is [None] for EVERY payload
    (quantified over [GoAny], not fixtures): [^] at [GTUint], and [-] at every width below [i64]. *)
Theorem typed_unop_holes_none : forall g : GoAny,
  typed_unop UXor GTUint g = None
  /\ typed_unop UNeg GTUint g = None
  /\ typed_unop UNeg GTU8  g = None /\ typed_unop UNeg GTI8  g = None
  /\ typed_unop UNeg GTU16 g = None /\ typed_unop UNeg GTI16 g = None
  /\ typed_unop UNeg GTU32 g = None /\ typed_unop UNeg GTI32 g = None.
Proof. intros [A [x tag]]. repeat split; reflexivity. Qed.
(** T2 — conversion CHAINS through a non-[GTInt] intermediate DENOTE (both conversion arms evaluate
    their source at FULL power): the EXIT-target chain [int64(uint8(len ..))], the [GTInt]-target
    chain [int(uint8(len ..))], and the TRUNCATING chain [int8(^uint8(len ..))] (a T1 typed unary
    INSIDE a conversion: [^uint8(3)] = 252, zero-extended and wrapped to [i8] −4 — the non-identity
    witness; all three verified against gc via go run: 3, 3, −4).  These witnesses have EVALUATED
    sources; the TWO absent complements are pinned separately — the runtime-FLOAT source
    ([runtime_float_source_conv_absent] below) and the ABSENT runtime-int source
    ([runtime_conv_absent_src_pinned], the [denote_expr_conv_src_absent] class). *)
Definition runconv_chain_e : GExpr :=
  ECall (EId (mkIdent "int64" eq_refl))
        [ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e]].
Definition runconv_chain_int_e : GExpr :=
  ECall (EId (mkIdent "int" eq_refl))
        [ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e]].
Definition runconv_chain_trunc_e : GExpr :=
  ECall (EId (mkIdent "int8" eq_refl))
        [EUn UXor (ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e])].
Example typed_runtime_convchain_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runconv_chain_e ; runconv_chain_int_e ; runconv_chain_trunc_e ]
  = [ Some (ORet tt (w_log true (anyt TI64 (i64wrap 3) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 3) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TI8 (i8wrap 252) :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example typed_runtime_convchain_supported :
  forallb supported_program
    (map println_prog [ runconv_chain_e ; runconv_chain_int_e ; runconv_chain_trunc_e ]) = true.
Proof. vm_compute. reflexivity. Qed.
(** The RUNTIME-FLOAT SOURCE boundary: the ABSENCE is the gated CLASS pair
    ([reval_val_runfloat_none] — no [PtRunFloat]-classified expression evaluates at all;
    [denote_expr_conv_float_src_absent] — every integer-target conversion over such a source is
    absent, [GTInt] included).  This fixture pins what the class theorems cannot: the form is
    gate-SUPPORTED (supported-but-absent, the honest frontier membership) — flips with the float
    arc, not this one. *)
Definition runconv_float_src_e : GExpr :=
  ECall (EId (mkIdent "int64" eq_refl))
        [ECall (EId (mkIdent "float64" eq_refl)) [runlen3_e]].
Example runtime_float_source_conv_absent :
  ptype runconv_float_src_e = Some (PtRunInt GTInt64)
  /\ supported_program (println_prog runconv_float_src_e) = true
  /\ denotable_program (println_prog runconv_float_src_e) = false
  /\ denote_program (println_prog runconv_float_src_e) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.
(** T3 — SAME-WIDTH typed arithmetic/bitwise DENOTES on evaluated runtime operands: all nine ops
    exercised at [u8] (incl. the WRAP witness 252+252=248 and the division-by-zero panic on a
    zero-length source) plus the signed [i64] pair (7 and the sign witness −4 % 3 = −1) —
    go-run-verified against gc: 248, 9, 50, 2, 0, 255, 255, 252, 7, −1, panic. *)
Definition runb_u8   : GExpr := ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e].
Definition runb_u8n  : GExpr := EUn UXor runb_u8.
Definition runb_u8x5 : GExpr :=
  ECall (EId (mkIdent "uint8" eq_refl))
        [ECall (EId (mkIdent "len" eq_refl))
               [ESliceLit GTInt [EInt 1; EInt 2; EInt 3; EInt 4; EInt 5]]].
Definition runb_u8x0 : GExpr :=
  ECall (EId (mkIdent "uint8" eq_refl))
        [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt []]].
Definition runb_i64  : GExpr := ECall (EId (mkIdent "int64" eq_refl)) [runlen3_e].
Definition runb_i64n : GExpr := EUn UXor runb_i64.
Definition typed_binop_cases : list GExpr :=
  [ EBn BAdd runb_u8n runb_u8n ; EBn BMul runb_u8 runb_u8
  ; EBn BDiv runb_u8n runb_u8x5 ; EBn BRem runb_u8n runb_u8x5
  ; EBn BAnd runb_u8n runb_u8 ; EBn BOr runb_u8n runb_u8
  ; EBn BXor runb_u8n runb_u8 ; EBn BAndNot runb_u8n runb_u8
  ; EBn BSub runb_i64 runb_i64n ; EBn BRem runb_i64n runb_i64
  ; EBn BDiv runb_u8 runb_u8x0 ].
Example runtime_typed_binop_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      typed_binop_cases
  = [ Some (ORet tt (w_log true (anyt TU8 (u8wrap 504) :: nil) w))   (* 252+252 — the wrap *)
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 9)   :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 50)  :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 2)   :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 0)   :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 255) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 255) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 252) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TI64 (i64wrap 7) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TI64 (i64wrap (-1)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_typed_binop_supported :
  forallb supported_program (map println_prog typed_binop_cases) = true.
Proof. vm_compute. reflexivity. Qed.
(** The MIXED-CONST operand shapes ([ptype_binop_runint_args]'s const rows — one runtime + one
    int-constant operand, untyped OR typed, either order) DENOTE: an untyped constant CONVERTS to
    the binop's width, a typed one is already AT it ([typed_operand], width-sealed).  go-run-verified against gc: 4, 4, 4, 254 (the typed-const-left
    WRAP witness [uint8(1) - uint8(len a)] = 1−3), and the const-dividend / runtime-ZERO-divisor
    panic [1 % uint8(len([]int{}))]. *)
Definition runmixed_const_e : GExpr := EBn BAdd runb_u8 (EInt 1).
Definition runb_u8one : GExpr := ECall (EId (mkIdent "uint8" eq_refl)) [EInt 1].
Definition typed_mixed_cases : list GExpr :=
  [ runmixed_const_e                 (* untyped const RIGHT *)
  ; EBn BAdd (EInt 1) runb_u8        (* untyped const LEFT *)
  ; EBn BAdd runb_u8 runb_u8one      (* typed const RIGHT *)
  ; EBn BSub runb_u8one runb_u8      (* typed const LEFT — the wrap witness *)
  ; EBn BRem (EInt 1) runb_u8x0 ].   (* const dividend, runtime ZERO divisor — panics *)
Example typed_mixed_const_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      typed_mixed_cases
  = [ Some (ORet tt (w_log true (anyt TU8 (u8wrap 4) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 4) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 4) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap (-2)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example typed_mixed_const_supported :
  forallb supported_program (map println_prog typed_mixed_cases) = true.
Proof. vm_compute. reflexivity. Qed.
(** The WIDTH seal at the operand boundary ITSELF (not caller discipline): a typed [uint8] constant
    never cross-materializes at [int64], and the outer mixed-width binop is [ptype]-REJECTED. *)
Example typed_operand_cross_width_none :
  typed_operand reval_val GTInt64 runb_u8one = None.
Proof. vm_compute. reflexivity. Qed.
Example typed_binop_cross_width_rejected :
  ptype (EBn BAdd runb_u8one runb_i64) = None
  /\ supported_program (println_prog (EBn BAdd runb_u8one runb_i64)) = false.
Proof. split; vm_compute; reflexivity. Qed.
(** T4 — SAME-WIDTH typed COMPARISONS denote (all six ops at [u8], mixed-const both kinds, the
    signed [i64] pair) — go-run-verified against gc: true, false, true, false, true, false, true,
    false, true, true. *)
Definition typed_cmp_cases : list GExpr :=
  [ EBn BEq runb_u8 runb_u8 ; EBn BLt runb_u8n runb_u8 ; EBn BGt runb_u8n runb_u8
  ; EBn BNe runb_u8 runb_u8 ; EBn BLe runb_u8 runb_u8 ; EBn BGe runb_u8 runb_u8n
  ; EBn BEq runb_u8 (EInt 3)                                        (* mixed UNTYPED *)
  ; EBn BLt (EInt 3) runb_u8                                        (* mixed untyped LEFT *)
  ; EBn BEq runb_u8 (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 3]) (* mixed TYPED *)
  ; EBn BLt runb_i64n runb_i64 ].                                   (* signed i64 *)
Example runtime_typed_cmp_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      typed_cmp_cases
  = [ Some (ORet tt (w_log true (anyt TBool true  :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool false :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool true  :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool false :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool true  :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool false :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool true  :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool false :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool true  :: nil) w))
    ; Some (ORet tt (w_log true (anyt TBool true  :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_typed_cmp_supported :
  forallb supported_program (map println_prog typed_cmp_cases) = true.
Proof. vm_compute. reflexivity. Qed.
(** The [GTUint] comparison hole at program level + the cross-width comparison [ptype]-REJECTED. *)
Definition runuint_cmp_e : GExpr :=
  EBn BEq (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e])
          (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]).
Example typed_cmp_uint_program_absent :
  ptype runuint_cmp_e = Some PtBool
  /\ supported_program (println_prog runuint_cmp_e) = true
  /\ denotable_program (println_prog runuint_cmp_e) = false
  /\ denote_program (println_prog runuint_cmp_e) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.
Example typed_cmp_cross_width_rejected :
  ptype (EBn BEq runb_u8one runb_i64) = None
  /\ supported_program (println_prog (EBn BEq runb_u8one runb_i64)) = false.
Proof. split; vm_compute; reflexivity. Qed.
(** DISPATCH AUTHORITY (gated): each live [typed_cmp] row IS the fully qualified model op — one
    6-conjunct pin per width (the derived [neqb]/[gtb]/[geb] are model Definitions, pinned as such). *)
Example typed_cmp_u8_model : forall a b,
  typed_cmp BEq GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.builtins.u8_eqb a b)
  /\ typed_cmp BNe GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.builtins.u8_neqb a b)
  /\ typed_cmp BLt GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.builtins.u8_ltb a b)
  /\ typed_cmp BLe GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.builtins.u8_leb a b)
  /\ typed_cmp BGt GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.builtins.u8_gtb a b)
  /\ typed_cmp BGe GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.builtins.u8_geb a b).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_cmp_i8_model : forall a b,
  typed_cmp BEq GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.builtins.i8_eqb a b)
  /\ typed_cmp BNe GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.builtins.i8_neqb a b)
  /\ typed_cmp BLt GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.builtins.i8_ltb a b)
  /\ typed_cmp BLe GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.builtins.i8_leb a b)
  /\ typed_cmp BGt GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.builtins.i8_gtb a b)
  /\ typed_cmp BGe GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.builtins.i8_geb a b).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_cmp_u16_model : forall a b,
  typed_cmp BEq GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.builtins.u16_eqb a b)
  /\ typed_cmp BNe GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.builtins.u16_neqb a b)
  /\ typed_cmp BLt GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.builtins.u16_ltb a b)
  /\ typed_cmp BLe GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.builtins.u16_leb a b)
  /\ typed_cmp BGt GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.builtins.u16_gtb a b)
  /\ typed_cmp BGe GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.builtins.u16_geb a b).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_cmp_i16_model : forall a b,
  typed_cmp BEq GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.builtins.i16_eqb a b)
  /\ typed_cmp BNe GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.builtins.i16_neqb a b)
  /\ typed_cmp BLt GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.builtins.i16_ltb a b)
  /\ typed_cmp BLe GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.builtins.i16_leb a b)
  /\ typed_cmp BGt GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.builtins.i16_gtb a b)
  /\ typed_cmp BGe GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.builtins.i16_geb a b).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_cmp_u32_model : forall a b,
  typed_cmp BEq GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.builtins.u32_eqb a b)
  /\ typed_cmp BNe GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.builtins.u32_neqb a b)
  /\ typed_cmp BLt GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.builtins.u32_ltb a b)
  /\ typed_cmp BLe GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.builtins.u32_leb a b)
  /\ typed_cmp BGt GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.builtins.u32_gtb a b)
  /\ typed_cmp BGe GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.builtins.u32_geb a b).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_cmp_i32_model : forall a b,
  typed_cmp BEq GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.builtins.i32_eqb a b)
  /\ typed_cmp BNe GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.builtins.i32_neqb a b)
  /\ typed_cmp BLt GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.builtins.i32_ltb a b)
  /\ typed_cmp BLe GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.builtins.i32_leb a b)
  /\ typed_cmp BGt GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.builtins.i32_gtb a b)
  /\ typed_cmp BGe GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.builtins.i32_geb a b).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_cmp_i64_model : forall a b,
  typed_cmp BEq GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.builtins.i64_eqb a b)
  /\ typed_cmp BNe GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.builtins.i64_neqb a b)
  /\ typed_cmp BLt GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.builtins.i64_ltb a b)
  /\ typed_cmp BLe GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.builtins.i64_leb a b)
  /\ typed_cmp BGt GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.builtins.i64_gtb a b)
  /\ typed_cmp BGe GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.builtins.i64_geb a b).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_cmp_u64_model : forall a b,
  typed_cmp BEq GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.builtins.u64_eqb a b)
  /\ typed_cmp BNe GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.builtins.u64_neqb a b)
  /\ typed_cmp BLt GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.builtins.u64_ltb a b)
  /\ typed_cmp BLe GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.builtins.u64_leb a b)
  /\ typed_cmp BGt GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.builtins.u64_gtb a b)
  /\ typed_cmp BGe GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.builtins.u64_geb a b).
Proof. intros; repeat split; reflexivity. Qed.

(** The [GTUint] hole ROW at program level (the platform-uint carrier has NO model ops). *)
Definition runuint_binop_e : GExpr :=
  EBn BAdd (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e])
           (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]).
Example typed_binop_uint_program_absent :
  ptype runuint_binop_e = Some (PtRunInt GTUint)
  /\ supported_program (println_prog runuint_binop_e) = true
  /\ denotable_program (println_prog runuint_binop_e) = false
  /\ denote_program (println_prog runuint_binop_e) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.
(** DISPATCH AUTHORITY (gated): each live [typed_binop] row IS the fully qualified model op — one
    9-conjunct pin per width; [/] and [%] pin to the [div_checked] convoy over the width's
    evidence-carrying model op. *)
Example typed_binop_u8_model : forall a b,
  typed_binop BAdd GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.builtins.u8_add a b)))
  /\ typed_binop BSub GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.builtins.u8_sub a b)))
  /\ typed_binop BMul GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.builtins.u8_mul a b)))
  /\ typed_binop BDiv GTU8 (anyt TU8 a) (anyt TU8 b) = Some (div_checked TU8 Fido.builtins.u8raw Fido.builtins.u8_div a b)
  /\ typed_binop BRem GTU8 (anyt TU8 a) (anyt TU8 b) = Some (div_checked TU8 Fido.builtins.u8raw Fido.builtins.u8_mod a b)
  /\ typed_binop BAnd GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.builtins.u8_and a b)))
  /\ typed_binop BOr  GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.builtins.u8_or  a b)))
  /\ typed_binop BXor GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.builtins.u8_xor a b)))
  /\ typed_binop BAndNot GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.builtins.u8_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_binop_i8_model : forall a b,
  typed_binop BAdd GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.builtins.i8_add a b)))
  /\ typed_binop BSub GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.builtins.i8_sub a b)))
  /\ typed_binop BMul GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.builtins.i8_mul a b)))
  /\ typed_binop BDiv GTI8 (anyt TI8 a) (anyt TI8 b) = Some (div_checked TI8 Fido.builtins.i8raw Fido.builtins.i8_div a b)
  /\ typed_binop BRem GTI8 (anyt TI8 a) (anyt TI8 b) = Some (div_checked TI8 Fido.builtins.i8raw Fido.builtins.i8_mod a b)
  /\ typed_binop BAnd GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.builtins.i8_and a b)))
  /\ typed_binop BOr  GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.builtins.i8_or  a b)))
  /\ typed_binop BXor GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.builtins.i8_xor a b)))
  /\ typed_binop BAndNot GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.builtins.i8_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_binop_u16_model : forall a b,
  typed_binop BAdd GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.builtins.u16_add a b)))
  /\ typed_binop BSub GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.builtins.u16_sub a b)))
  /\ typed_binop BMul GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.builtins.u16_mul a b)))
  /\ typed_binop BDiv GTU16 (anyt TU16 a) (anyt TU16 b) = Some (div_checked TU16 Fido.builtins.u16raw Fido.builtins.u16_div a b)
  /\ typed_binop BRem GTU16 (anyt TU16 a) (anyt TU16 b) = Some (div_checked TU16 Fido.builtins.u16raw Fido.builtins.u16_mod a b)
  /\ typed_binop BAnd GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.builtins.u16_and a b)))
  /\ typed_binop BOr  GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.builtins.u16_or  a b)))
  /\ typed_binop BXor GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.builtins.u16_xor a b)))
  /\ typed_binop BAndNot GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.builtins.u16_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_binop_i16_model : forall a b,
  typed_binop BAdd GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.builtins.i16_add a b)))
  /\ typed_binop BSub GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.builtins.i16_sub a b)))
  /\ typed_binop BMul GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.builtins.i16_mul a b)))
  /\ typed_binop BDiv GTI16 (anyt TI16 a) (anyt TI16 b) = Some (div_checked TI16 Fido.builtins.i16raw Fido.builtins.i16_div a b)
  /\ typed_binop BRem GTI16 (anyt TI16 a) (anyt TI16 b) = Some (div_checked TI16 Fido.builtins.i16raw Fido.builtins.i16_mod a b)
  /\ typed_binop BAnd GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.builtins.i16_and a b)))
  /\ typed_binop BOr  GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.builtins.i16_or  a b)))
  /\ typed_binop BXor GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.builtins.i16_xor a b)))
  /\ typed_binop BAndNot GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.builtins.i16_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_binop_u32_model : forall a b,
  typed_binop BAdd GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.builtins.u32_add a b)))
  /\ typed_binop BSub GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.builtins.u32_sub a b)))
  /\ typed_binop BMul GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.builtins.u32_mul a b)))
  /\ typed_binop BDiv GTU32 (anyt TU32 a) (anyt TU32 b) = Some (div_checked TU32 Fido.builtins.u32raw Fido.builtins.u32_div a b)
  /\ typed_binop BRem GTU32 (anyt TU32 a) (anyt TU32 b) = Some (div_checked TU32 Fido.builtins.u32raw Fido.builtins.u32_mod a b)
  /\ typed_binop BAnd GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.builtins.u32_and a b)))
  /\ typed_binop BOr  GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.builtins.u32_or  a b)))
  /\ typed_binop BXor GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.builtins.u32_xor a b)))
  /\ typed_binop BAndNot GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.builtins.u32_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_binop_i32_model : forall a b,
  typed_binop BAdd GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.builtins.i32_add a b)))
  /\ typed_binop BSub GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.builtins.i32_sub a b)))
  /\ typed_binop BMul GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.builtins.i32_mul a b)))
  /\ typed_binop BDiv GTI32 (anyt TI32 a) (anyt TI32 b) = Some (div_checked TI32 Fido.builtins.i32raw Fido.builtins.i32_div a b)
  /\ typed_binop BRem GTI32 (anyt TI32 a) (anyt TI32 b) = Some (div_checked TI32 Fido.builtins.i32raw Fido.builtins.i32_mod a b)
  /\ typed_binop BAnd GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.builtins.i32_and a b)))
  /\ typed_binop BOr  GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.builtins.i32_or  a b)))
  /\ typed_binop BXor GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.builtins.i32_xor a b)))
  /\ typed_binop BAndNot GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.builtins.i32_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_binop_i64_model : forall a b,
  typed_binop BAdd GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.builtins.i64_add a b)))
  /\ typed_binop BSub GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.builtins.i64_sub a b)))
  /\ typed_binop BMul GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.builtins.i64_mul a b)))
  /\ typed_binop BDiv GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (div_checked TI64 Fido.builtins.i64raw Fido.builtins.i64_div a b)
  /\ typed_binop BRem GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (div_checked TI64 Fido.builtins.i64raw Fido.builtins.i64_mod a b)
  /\ typed_binop BAnd GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.builtins.i64_and a b)))
  /\ typed_binop BOr  GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.builtins.i64_or  a b)))
  /\ typed_binop BXor GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.builtins.i64_xor a b)))
  /\ typed_binop BAndNot GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.builtins.i64_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.
Example typed_binop_u64_model : forall a b,
  typed_binop BAdd GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.builtins.u64_add a b)))
  /\ typed_binop BSub GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.builtins.u64_sub a b)))
  /\ typed_binop BMul GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.builtins.u64_mul a b)))
  /\ typed_binop BDiv GTU64 (anyt TU64 a) (anyt TU64 b) = Some (div_checked TU64 Fido.builtins.u64raw Fido.builtins.u64_div a b)
  /\ typed_binop BRem GTU64 (anyt TU64 a) (anyt TU64 b) = Some (div_checked TU64 Fido.builtins.u64raw Fido.builtins.u64_mod a b)
  /\ typed_binop BAnd GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.builtins.u64_and a b)))
  /\ typed_binop BOr  GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.builtins.u64_or  a b)))
  /\ typed_binop BXor GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.builtins.u64_xor a b)))
  /\ typed_binop BAndNot GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.builtins.u64_andnot a b))).
Proof. intros; repeat split; reflexivity. Qed.

(** T5 — the SHIFT case table DENOTES (flipped in the landing commit, as pinned): both ops, a
    NON-GTInt count, [i64]/[u64] LEFT operands — each case's [ptype] RESULT WIDTH pinned by the
    STRUCTURAL [shift_case_shape] extractor, its run go-run-verified against gc (6, 1, 6, 6, 1).
    The EDGE pins below cover const/typed/HUGE (saturating) counts and the NEGATIVE-count panic;
    the [GTInt]-left (untyped-const left) and [GTUint]-left rows stay pinned absent. *)
Definition runshift_mixed_e : GExpr :=
  EBn BShl (ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e])
           (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]).
Definition runshift_shr_e : GExpr :=
  EBn BShr (ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e])
           (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]).
Definition runshift_i64count_e : GExpr :=
  EBn BShl (ECall (EId (mkIdent "uint8" eq_refl)) [runlen3_e])
           (ECall (EId (mkIdent "int64" eq_refl)) [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]).
Definition runshift_i64left_e : GExpr :=
  EBn BShl (ECall (EId (mkIdent "int64" eq_refl)) [runlen3_e])
           (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]).
Definition runshift_u64left_e : GExpr :=
  EBn BShr (ECall (EId (mkIdent "uint64" eq_refl)) [runlen3_e])
           (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]).
Definition typed_shift_cases : list GExpr :=
  [ runshift_mixed_e ; runshift_shr_e ; runshift_i64count_e ; runshift_i64left_e ; runshift_u64left_e ].
(** The SHAPE extractor — [Some] ONLY for a genuine shift node, carrying the op and BOTH operand
    classifications: swapping a witness for same-width arithmetic, dropping [BShr], or degrading the
    non-[GTInt] count to [GTInt] all change the extracted shape and break the pin below. *)
Definition shift_case_shape (e : GExpr) : option (BinOp * (option PTy * option PTy)) :=
  match e with
  | EBn BShl a b => Some (BShl, (ptype a, ptype b))
  | EBn BShr a b => Some (BShr, (ptype a, ptype b))
  | _ => None
  end.
Example typed_runtime_shift_runs : forall w,
  map shift_case_shape typed_shift_cases
    = [ Some (BShl, (Some (PtRunInt GTU8),    Some (PtRunInt GTInt)))
      ; Some (BShr, (Some (PtRunInt GTU8),    Some (PtRunInt GTInt)))
      ; Some (BShl, (Some (PtRunInt GTU8),    Some (PtRunInt GTInt64)))   (* the NON-GTInt count *)
      ; Some (BShl, (Some (PtRunInt GTInt64), Some (PtRunInt GTInt)))     (* the i64 LEFT *)
      ; Some (BShr, (Some (PtRunInt GTU64),   Some (PtRunInt GTInt))) ]   (* the u64 LEFT, BShr *)
  /\ map ptype typed_shift_cases
    = [ Some (PtRunInt GTU8) ; Some (PtRunInt GTU8) ; Some (PtRunInt GTU8)
      ; Some (PtRunInt GTInt64) ; Some (PtRunInt GTU64) ]
  /\ map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
        typed_shift_cases
     = [ Some (ORet tt (w_log true (anyt TU8 (u8wrap 6) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 1) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 6) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TI64 (i64wrap 6) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TU64 (u64wrap 1) :: nil) w)) ]
  /\ forallb supported_program (map println_prog typed_shift_cases) = true.
Proof. intro w. repeat split; vm_compute; reflexivity. Qed.
(** The shift EDGES: a constant count, a typed-width count, a HUGE count (saturates — gc gives 0),
    and the NEGATIVE runtime count (gc's exact panic payload) — go-run-verified: 12, 24, 0, panic. *)
Definition runshift_constcnt_e : GExpr := EBn BShl runb_u8 (EInt 2).
Definition runshift_typedcnt_e : GExpr := EBn BShl runb_u8 runb_u8.
Definition runshift_hugecnt_e  : GExpr :=
  EBn BShl runb_u8 (EUn UXor (ECall (EId (mkIdent "uint64" eq_refl)) [runlen3_e])).
Definition runshift_negcnt_e   : GExpr := EBn BShl runb_u8 runb_i64n.
Example typed_shift_edge_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runshift_constcnt_e ; runshift_typedcnt_e ; runshift_hugecnt_e ; runshift_negcnt_e ]
  = [ Some (ORet tt (w_log true (anyt TU8 (u8wrap 12) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 24) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 55340232221128654848) :: nil) w))
    ; Some (OPanic rt_shift_neg w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example typed_shift_edge_supported :
  forallb supported_program (map println_prog
    [ runshift_constcnt_e ; runshift_typedcnt_e ; runshift_hugecnt_e ; runshift_negcnt_e ]) = true.
Proof. vm_compute. reflexivity. Qed.
(** The GTInt LEFT rows now RUN through the engine (tier R8) — the former
    [typed_shift_gtint_left_absent] pin FLIPPED: an untyped-const left ([2 << len] — classifies
    [GTInt]), a runtime left with a WRAPPING const count ([len << 62] — negative like gc), a
    TYPED-width count ([len << uint8]), the HUGE count (saturates: << exhausts to 0), the
    sign-fill >> (-3 >> huge = -1), and the NEGATIVE runtime count (gc's exact panic payload) —
    go-run-verified: 16, -4611686018427387904, 24, 0, -1, panic.  The [uint] left stays the
    op-less hole row.  Bitwise: go-run-verified 1, 7, 2, 1. *)
Definition runshift_intleft_e  : GExpr := EBn BShl (EInt 2) runlen3_e.
Definition gtint_shift_wrap_e     : GExpr := EBn BShl runlen3_e (EInt 62).
Definition gtint_shift_typedcnt_e : GExpr := EBn BShl runlen3_e runb_u8.
Definition gtint_shift_huge_e     : GExpr :=
  EBn BShl runlen3_e (EUn UXor (ECall (EId (mkIdent "uint64" eq_refl)) [runlen3_e])).
Definition gtint_shift_signfill_e : GExpr :=
  EBn BShr (EBn BSub (EInt 0) runlen3_e)
           (EUn UXor (ECall (EId (mkIdent "uint64" eq_refl)) [runlen3_e])).
Definition gtint_shift_negcnt_e   : GExpr := EBn BShl runlen3_e (EBn BSub (EInt 0) runlen3_e).
Definition gtint_and_e    : GExpr := EBn BAnd    runlen3_e (EInt 1).
Definition gtint_or_e     : GExpr := EBn BOr     runlen3_e (EInt 4).
Definition gtint_xor_e    : GExpr := EBn BXor    runlen3_e (EInt 1).
Definition gtint_andnot_e : GExpr := EBn BAndNot runlen3_e (EInt 2).
Example gtint_shift_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ runshift_intleft_e ; gtint_shift_wrap_e ; gtint_shift_typedcnt_e
      ; gtint_shift_huge_e ; gtint_shift_signfill_e ; gtint_shift_negcnt_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 16) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 13835058055282163712) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 24) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 55340232221128654848) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap (-1)) :: nil) w))
    ; Some (OPanic rt_shift_neg w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example gtint_bitwise_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ gtint_and_e ; gtint_or_e ; gtint_xor_e ; gtint_andnot_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 7) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 2) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example gtint_shift_supported :
  forallb supported_program (map println_prog
    [ runshift_intleft_e ; gtint_shift_wrap_e ; gtint_shift_typedcnt_e
    ; gtint_shift_huge_e ; gtint_shift_signfill_e ; gtint_shift_negcnt_e ]) = true.
Proof. vm_compute. reflexivity. Qed.
(** The BIG-CONST count regressions (the review-R8 leak class): an untyped [2^31] count is
    outside [box_int]'s conservative default-[int] VALUE window yet a VALID Go count — read
    DIRECTLY off the gate it DENOTES saturated (go-run-verified: 0 at [int] and [uint8] left,
    0 for [>>]), and a TYPED [uint64] count past [2^32] stays live (valid Go on EVERY platform;
    go-run-verified 0).  One step past the conservative platform-[uint] window ([2^32], untyped)
    is MECHANICALLY unsupported ([untyped_count_overflow] — a 32-bit target could not compile
    it), never supported-but-undenoted. *)
Definition gtint_shift_bigconst_e : GExpr := EBn BShl runlen3_e (EInt 2147483648).
Definition gtint_shr_bigconst_e   : GExpr := EBn BShr runlen3_e (EInt 2147483648).
Definition u8_shift_bigconst_e    : GExpr := EBn BShl runb_u8   (EInt 2147483648).
Definition gtint_shift_typedbig_e : GExpr :=
  EBn BShl runlen3_e (ECall (EId (mkIdent "uint64" eq_refl)) [EInt 5000000000]).
Example shift_bigconst_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ gtint_shift_bigconst_e ; gtint_shr_bigconst_e ; u8_shift_bigconst_e ; gtint_shift_typedbig_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 55340232221128654848) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 0) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 55340232221128654848) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 55340232221128654848) :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example shift_bigconst_supported :
  forallb supported_program (map println_prog
    [ gtint_shift_bigconst_e ; gtint_shr_bigconst_e ; u8_shift_bigconst_e
    ; gtint_shift_typedbig_e ]) = true.
Proof. vm_compute. reflexivity. Qed.
Example shift_bigconst_gate :
  ptype (EBn BShl runlen3_e (EInt 4294967296)) = None
  /\ ptype (EBn BShl runb_u8 (EInt 4294967296)) = None
  /\ supported_program (println_prog (EBn BShl runlen3_e (EInt 4294967296))) = false
  /\ supported_program (println_prog (EBn BShl runb_u8 (EInt 4294967296))) = false.
Proof. repeat split; vm_compute; reflexivity. Qed.
Example gtint_bitwise_supported :
  forallb supported_program (map println_prog
    [ gtint_and_e ; gtint_or_e ; gtint_xor_e ; gtint_andnot_e ]) = true.
Proof. vm_compute. reflexivity. Qed.
Definition runshift_uintleft_e : GExpr :=
  EBn BShl (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]) (EInt 1).
Example typed_shift_uint_program_absent :
  ptype runshift_uintleft_e = Some (PtRunInt GTUint)
  /\ supported_program (println_prog runshift_uintleft_e) = true
  /\ denotable_program (println_prog runshift_uintleft_e) = false
  /\ denote_program (println_prog runshift_uintleft_e) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.
(** DISPATCH AUTHORITY (gated): each live [typed_shift] row IS the width's convoy over the fully
    qualified model op — one 2-conjunct pin per width. *)
Example typed_shift_u8_model : forall a z,
  typed_shift BShl GTU8 (anyt TU8 a) z = shift_checked_small TU8 Fido.builtins.u8_shl a z
  /\ typed_shift BShr GTU8 (anyt TU8 a) z = shift_checked_small TU8 Fido.builtins.u8_shr a z.
Proof. intros; split; reflexivity. Qed.
Example typed_shift_i8_model : forall a z,
  typed_shift BShl GTI8 (anyt TI8 a) z = shift_checked_small TI8 Fido.builtins.i8_shl a z
  /\ typed_shift BShr GTI8 (anyt TI8 a) z = shift_checked_small TI8 Fido.builtins.i8_shr a z.
Proof. intros; split; reflexivity. Qed.
Example typed_shift_u16_model : forall a z,
  typed_shift BShl GTU16 (anyt TU16 a) z = shift_checked_small TU16 Fido.builtins.u16_shl a z
  /\ typed_shift BShr GTU16 (anyt TU16 a) z = shift_checked_small TU16 Fido.builtins.u16_shr a z.
Proof. intros; split; reflexivity. Qed.
Example typed_shift_i16_model : forall a z,
  typed_shift BShl GTI16 (anyt TI16 a) z = shift_checked_small TI16 Fido.builtins.i16_shl a z
  /\ typed_shift BShr GTI16 (anyt TI16 a) z = shift_checked_small TI16 Fido.builtins.i16_shr a z.
Proof. intros; split; reflexivity. Qed.
Example typed_shift_u32_model : forall a z,
  typed_shift BShl GTU32 (anyt TU32 a) z = shift_checked_small TU32 Fido.builtins.u32_shl a z
  /\ typed_shift BShr GTU32 (anyt TU32 a) z = shift_checked_small TU32 Fido.builtins.u32_shr a z.
Proof. intros; split; reflexivity. Qed.
Example typed_shift_i32_model : forall a z,
  typed_shift BShl GTI32 (anyt TI32 a) z = shift_checked_small TI32 Fido.builtins.i32_shl a z
  /\ typed_shift BShr GTI32 (anyt TI32 a) z = shift_checked_small TI32 Fido.builtins.i32_shr a z.
Proof. intros; split; reflexivity. Qed.
Example typed_shift_i64_model : forall a z,
  typed_shift BShl GTInt64 (anyt TI64 a) z = shift_checked_wide TI64 Fido.builtins.i64_shl a z
  /\ typed_shift BShr GTInt64 (anyt TI64 a) z = shift_checked_wide TI64 Fido.builtins.i64_shr a z.
Proof. intros; split; reflexivity. Qed.
Example typed_shift_u64_model : forall a z,
  typed_shift BShl GTU64 (anyt TU64 a) z = shift_checked_wide TU64 Fido.builtins.u64_shl a z
  /\ typed_shift BShr GTU64 (anyt TU64 a) z = shift_checked_wide TU64 Fido.builtins.u64_shr a z.
Proof. intros; split; reflexivity. Qed.
(** The ABSENT-SOURCE conversion witness — [PtRunInt] classification alone NEVER implies denotation:
    a conversion over a supported-but-undenoted runtime-int source (a [GTUint]-carrier binop —
    the op-less hole row) is itself supported-but-undenoted, exactly
    [denote_expr_conv_src_absent]'s class at program level.  A
    future prose claim of "runtime-int source ⟹ denotes" breaks against this pin. *)
Definition runconv_absent_src_e : GExpr :=
  ECall (EId (mkIdent "int64" eq_refl)) [runuint_binop_e].
Example runtime_conv_absent_src_pinned :
  ptype runconv_absent_src_e = Some (PtRunInt GTInt64)
  /\ ptype runuint_binop_e = Some (PtRunInt GTUint)
  /\ supported_program (println_prog runconv_absent_src_e) = true
  /\ denotable_program (println_prog runconv_absent_src_e) = false
  /\ denote_program (println_prog runconv_absent_src_e) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** FAIL-CLOSED pins for an INVALID NESTED map type (the INVALID-Go class of the [goty_supported]
    authority — its valid-but-out-of-core class, ptr/chan map keys, is pinned surface-by-surface in
    [GoSafe.valid_unsupported_programs]):
    [map[int]map[[]int]int]
    hides a non-comparable slice KEY inside the VALUE type, so even the EMPTY literal is invalid Go — the
    gate REJECTS it at the ROOT ([ptype = None] ⇒ unsupported, never emitted) and NO layer assigns it
    behavior ([eval_value] / [reval_int] / [denote_program] all decline) through [len],
    [println(len(..))], and the divide-by-zero shape.  GoSafe's [bad_programs_rejected] carries the same
    witnesses at the gate level. *)
Definition maplen_invalid_vt_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []].
Example map_len_invalid_type_rejected :
  ptype (EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []) = None
  /\ ptype maplen_invalid_vt_e = None
  /\ eval_value maplen_invalid_vt_e = None
  /\ reval_int maplen_invalid_vt_e = None
  /\ supported_program (println_prog maplen_invalid_vt_e) = false
  /\ denote_program (println_prog maplen_invalid_vt_e) = None
  /\ supported_program (mkProgram (mkIdent "main" eq_refl)
       [GsBlankAssign (EBn BDiv (EInt 1) maplen_invalid_vt_e)]) = false
  /\ denote_program (mkProgram (mkIdent "main" eq_refl)
       [GsBlankAssign (EBn BDiv (EInt 1) maplen_invalid_vt_e)]) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** TIGHTNESS — WHERE the general converse's "sufficient, not necessary" comes from.  [stmt_terminates] just
    READS [denote_stmt]'s terminator flag (NOT a second authority).  On a TERMINATOR-FREE body the compositional
    converse is EXACT (an iff): the body denotes iff EVERY statement individually denotes.  The ONLY slack is the
    terminator escape — a terminator's UNREACHABLE rest need only be SUPPORTED, so a denotable body may carry an
    undenotable-but-supported DEAD tail (pinned by [denotable_body_escapes_stmt_denotable] below). *)
Definition stmt_terminates (s : GoStmt) : bool :=
  match denote_stmt s with Some (_, true) => true | _ => false end.

Lemma denotable_body_terminator_free_necessary : forall b,
  forallb (fun s => negb (stmt_terminates s)) b = true ->
  denotable_body b = true -> forallb stmt_denotable b = true.
Proof.
  induction b as [|s rest IH]; [reflexivity|].
  cbn [forallb denotable_body]. intros Htf Hden.
  apply andb_true_iff in Htf as [Hs Hrest]. apply negb_true_iff in Hs. unfold stmt_terminates in Hs.
  destruct (denote_stmt s) as [[c term]|] eqn:Es.
  - destruct term; [discriminate Hs|].                       (* terminator excluded by [terminator_free] *)
    apply andb_true_intro. split; [unfold stmt_denotable; rewrite Es; reflexivity | exact (IH Hrest Hden)].
  - discriminate Hden.                                       (* [denote_stmt s = None] => [denotable_body] false *)
Qed.

Corollary denotable_body_terminator_free_iff : forall b,
  forallb (fun s => negb (stmt_terminates s)) b = true ->
  (denotable_body b = true <-> forallb stmt_denotable b = true).
Proof.
  intros b Htf. split;
    [exact (denotable_body_terminator_free_necessary b Htf) | exact (denotable_body_of_stmts b)].
Qed.

(** The escape is REAL (the converse is genuinely sufficient-not-necessary): [return; println(string(200))]
    is a DENOTABLE body ([return] terminates; the multi-byte-rune-arg [println] is a SUPPORTED dead tail)
    whose tail does NOT denote, so [denotable_body = true] while [forallb stmt_denotable = false].  This body
    HAS a terminator — exactly why the iff above does not apply to it. *)
Example denotable_body_escapes_stmt_denotable :
  denotable_body [GsReturn;
    GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb])] = true
  /\ forallb stmt_denotable [GsReturn;
       GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb])] = false.
Proof. split; vm_compute; reflexivity. Qed.

(** ---- EXECUTABLE TOTALITY is UNIVERSAL, not GoSem's: cmd.v's gated [run_cmd_terminates] proves EVERY
    [Cmd unit] — defers included — runs to [Some] Outcome for enough fuel, so a denoted program always RUNS;
    GoSem needs no denotation-side totality layer.  Concrete end-to-end runs (with their EXACT output worlds,
    incl. the defer LIFO order and a deferred panic) are pinned by the typed [GoSemRequiredCategoryCoverage]
    fields below. *)

(** ---- End-to-end demo fixture with REAL OBSERVABLE OUTPUT: `func main(){ println("hi"); return }` runs
    through cmd.v's authoritative [run_cmd] to the very [w_log true ["hi"]] the model's own [println]
    produces — pinned as the typed field [rc_println_str] of [GoSemRequiredCategoryCoverage] below.
    DEFINITIONALLY [println_prog (EStr "hi")] — ONE spelling, so the [runs_to]-based field and this named
    fixture can never drift apart. *)
Definition gosem_demo_prog : Program := println_prog (EStr "hi").

(** REGRESSION fixture: [return] STOPS the body — `func main(){ return; println("after") }` is SUPPORTED yet
    prints NOTHING (the world is UNCHANGED).  Pinned as the typed field [rc_return_stops] of
    [GoSemRequiredCategoryCoverage] below. *)
Definition gosem_return_stops_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsReturn; GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "after"])].

(** UNIVERSAL TERMINATOR PROPERTY:
    a TERMINATOR ([return] / a denoted [panic]) must NOT depend on its UNREACHABLE successors DENOTING — only on
    their SUPPORTEDNESS.  Stated for ALL [s]/[c]/[rest]: whenever [denote_stmt] marks [s] terminating
    ([Some (c, true)]), [denote_body] emits [c] and gates the rest ONLY on [forallb stmt_ok rest], NEVER on
    [denote_body rest].  A UNIVERSAL lemma (over ALL [rest]), NOT a fixture keyed to one specific
    supported-but-undenotable successor — so it never erodes.  Such successors PERSIST, not vanish: a
    runtime-arg statement is supported yet eval-partial; the lemma holds for EVERY [rest] regardless of how
    [eval_value] grows. *)
Lemma denote_body_terminator_ignores_succ : forall s c rest,
  denote_stmt s = Some (c, true) ->
  denote_body (s :: rest) = (if forallb stmt_ok rest then Some c else None).
Proof. intros s c rest H. cbn [denote_body]. rewrite H. reflexivity. Qed.

(** The two terminators the lemma covers (so it is not vacuous): bare [return] -> [CRet tt], and a denoted
    [panic("x")] -> [CPan (anyt TString "x")], each with the [true] terminates-flag. *)
Example denote_stmt_terminators :
  denote_stmt GsReturn = Some (CRet tt, true)
  /\ denote_stmt (GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "x"]))
     = Some (CPan (anyt TString "x"), true).
Proof. split; vm_compute; reflexivity. Qed.

(** A denoted [panic] TERMINATES end-to-end in [OPanic] — pinned as the typed field [rc_panic] of
    [GoSemRequiredCategoryCoverage] below. *)
Definition gosem_panic_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "x"])].

(** The determined-DIVIDE-BY-ZERO fixture: `_ = 1 / len([]int{})` is SUPPORTED (a runtime integer division —
    a CONSTANT zero divisor would be a compile error), and now DENOTES to its TRUE behavior via [denote_expr]:
    the run PANICS with Go's exact runtime value [rt_div_zero] — pinned end-to-end as the typed field
    [rc_div_zero]. *)
Definition gosem_runtime_blank_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign divzero_e].

(** ARGUMENT-panic fixtures: a panicking ARGUMENT panics BEFORE its call runs.  [println(1/len([]int{}))]
    prints NOTHING (the call is never reached — [rc_arg_panic]); and a DEFERRED call's arguments evaluate AT
    DEFER TIME, so `defer println(1/len([]int{})); println("hi")` panics at the [defer] STATEMENT — the later
    "hi" never prints ([rc_defer_arg_panic]; contrast [rc_defer_panic], where the DEFERRED PANIC itself fires
    at return, AFTER the body's output). *)
Definition gosem_arg_panic_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]); GsReturn].
Definition gosem_defer_arg_panic_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "hi"]); GsReturn].

(** STRUCTURAL short-circuit regressions: after a KNOWN-panic argument, later ARGUMENTS and later STATEMENTS
    are unreachable — they must be SUPPORTED (the gate) but are NOT required to DENOTE.  The undenoted piece
    in each is the multi-byte rune ([runeconv_mb], supported-printable yet undenoted —
    [out_boundary_runtime_undenoted]): as a LATER ARG of
    the panicking call, as the SUCCESSOR statement, and as the successor of a DEFERRED panicking-arg call.
    Each program denotes and runs to [OPanic rt_div_zero] with NO output. *)
Definition gosem_arg_panic_tail_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [divzero_e; runeconv_mb]); GsReturn].
Definition gosem_arg_panic_succ_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb]); GsReturn].
Definition gosem_defer_arg_panic_succ_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb]); GsReturn].
Definition arg_panic_shortcircuit_progs : list Program :=
  [gosem_arg_panic_tail_prog; gosem_arg_panic_succ_prog; gosem_defer_arg_panic_succ_prog].
Example arg_panic_shortcircuit_runs : forall w,
  map (fun p => match denote_program p with Some c => run_cmd 5 c w | None => None end)
      arg_panic_shortcircuit_progs
  = map (fun _ => Some (OPanic rt_div_zero w)) arg_panic_shortcircuit_progs.
Proof. intro w. vm_compute. reflexivity. Qed.
Example arg_panic_shortcircuit_supported :
  forallb supported_program arg_panic_shortcircuit_progs = true.
Proof. vm_compute. reflexivity. Qed.

(** Defer fixture: `func main(){ defer println("bye"); return }` — DENOTES to a [CDfr] (the deferred
    [println] runs at function-scope return); pinned denotable in [gosem_denotability_decisions] and accepted
    by GoSemSafe's panic-free gate ([GoSemSafe.panic_free_gate_defer]). *)
Definition gosem_defer_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "bye"]); GsReturn].

(** Defer LIFO fixture: `defer println("a"); defer println("b"); println("hi"); return` — the body prints
    "hi", then the defers run at return in LIFO order ("b" was deferred LAST so runs FIRST, then "a"), exactly
    Go.  Pinned end-to-end as the typed field [rc_defer_lifo]. *)
Definition gosem_defer_lifo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "a"]);
             GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "b"]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "hi"]); GsReturn].

(** Deferred-PANIC fixture: `defer panic("boom"); println("hi"); return` — the deferral does NOT stop the body
    (the "hi" prints), then the deferred panic fires at return and the run ends in [OPanic].  Pinned end-to-end
    as the typed field [rc_defer_panic]; REJECTED by GoSemSafe's panic-free gate (a deferred panic IS a panic
    site — [GoSemSafe.panic_free_gate_defer]). *)
Definition gosem_defer_panic_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsDefer (ECall (EId (mkIdent "panic" eq_refl)) [EStr "boom"]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "hi"]); GsReturn].

(** ---- [eval_value] FOLD TABLE (grouped regression) ---- each LISTED row's constant [eval_value] denotes to
    the paired value, pinned as one [(expr, value)] list.  A BREADTH sample, NOT a completeness claim: some
    printable supported constants are honestly ABSENT (e.g. the multi-byte rune [string(200)], pinned by
    [runeconv_multibyte_boundary]).  Rows exercise: integer conversions/arith/complement (the model's EXACT
    value per signedness/width), exact-DYADIC FLOAT constants (conversions + [+]/[-]/[*]/exact-[/], fractional
    values included), constant BOOLs (numeric + string comparisons,
    [&&]/[||]/[!], [bool(x)]), string CONSTANTs (literal/concat/ASCII-rune/identity conv; high-byte order is
    UNSIGNED), the constant in-bounds slice-index, and the [len] folds (slice length / map entry count).  The
    [box_*]/[ptype] FAIL-CLOSED pins are separate below — those lock the GATE boundary, not a fold. *)
Definition eval_value_good : list (GExpr * GoAny) :=
  [ (ECall (EId (mkIdent "int64" eq_refl)) [EInt 3], anyt TI64 (i64wrap 3))
  ; (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 5], anyt TU8 (u8wrap 5))
  ; (ECall (EId (mkIdent "int8" eq_refl)) [EInt 127], anyt TI8 (i8wrap 127))
  ; (EBn BAdd (EInt 1) (EInt 2), anyt TInt64 (intwrap 3))
  ; (EUn UXor (ECall (EId (mkIdent "int64" eq_refl)) [EInt 5]), anyt TI64 (i64wrap (-6)))   (* ^int64(5) = bitwise NOT = -6 *)
  ; (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3], anyt TUint (uint_lit 3 eq_refl))
  ; (EBn BAdd (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "uint" eq_refl)) [EInt 4]), anyt TUint (uint_lit 7 eq_refl))
  ; (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3], anyt TFloat64 (renorm 53 1024 (sf_of_Z 3)))
  ; (ECall (EId (mkIdent "float32" eq_refl)) [EInt 5], anyt TFloat32 (f32_lit (sf_of_Z 5)))
  ; (EBn BDiv (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]),
     anyt TFloat64 (renorm 53 1024 (sf_of_dyadic 3 (-1))))   (* float64(3)/float64(2) = 1.5 — a FRACTIONAL dyadic fold *)
  ; (EBn BAdd (ECall (EId (mkIdent "float64" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]),
     anyt TFloat64 (renorm 53 1024 (sf_of_dyadic 3 0)))       (* float const + *)
  ; (EBn BSub (ECall (EId (mkIdent "float64" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]),
     anyt TFloat64 (renorm 53 1024 (sf_of_dyadic (-1) 0)))    (* float const -  (operand ORDER matters) *)
  ; (EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]),
     anyt TFloat64 (renorm 53 1024 (sf_of_dyadic 3 1)))       (* float const * *)
  ; (EBn BDiv (ECall (EId (mkIdent "float32" eq_refl)) [EInt 5]) (ECall (EId (mkIdent "float32" eq_refl)) [EInt 2]),
     anyt TFloat32 (f32_lit (sf_of_dyadic 5 (-1))))           (* float32 fractional — width-correct boxing *)
  ; (EBn BDiv (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (EInt 2),
     anyt TFloat64 (renorm 53 1024 (sf_of_dyadic 3 (-1))))    (* float const / UNTYPED int const (mixed) *)
  ; (ECall (EId (mkIdent "float64" eq_refl))
           [EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2])],
     anyt TFloat64 (renorm 53 1024 (sf_of_dyadic 3 1)))       (* float64(<fold>) — a NESTED fold under a conversion passes the RECURSIVE guard (no bypass) *)
  ; (ECall (EId (mkIdent "len" eq_refl))
           [EMapLit GTInt GTFloat64 [(EInt 1, EBn BDiv (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]))]],
     anyt TInt64 (intwrap 1))                                 (* a map VALUE containing a float fold — the evaluability check routes through the same guarded authority *)
  ; (ECall (EId (mkIdent "int" eq_refl))
           [EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2])],
     anyt TInt64 (intwrap 6))                                 (* int(<float fold>) — a fold LAUNDERED into an integer constant still crosses the [floats_checked] boundary *)
  ; (ECall (EId (mkIdent "float64" eq_refl))
           [ECall (EId (mkIdent "int" eq_refl))
                  [EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2])]],
     anyt TFloat64 (renorm 53 1024 (sf_of_dyadic 3 1)))       (* float64(int(<fold>)) — the re-floated laundering shape; the inner fold is boundary-verified *)
  ; (EBn BEq (EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]))
             (ECall (EId (mkIdent "float64" eq_refl)) [EInt 6]),
     anyt TBool true)                                         (* a COMPARISON whose operand is a fold — boundary-verified before the exact dyadic compare *)
  ; (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "int" eq_refl))
                                    [EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2])]])
            (EInt 0),
     anyt TInt64 (intwrap 6))                                 (* a SLICE ELEMENT holding a laundered fold *)
  ; (ECall (EId (mkIdent "len" eq_refl))
           [EMapLit GTInt GTInt [(ECall (EId (mkIdent "int" eq_refl))
                                        [EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2])], EInt 1)]],
     anyt TInt64 (intwrap 1))                                 (* a MAP KEY holding a laundered fold *)
  ; (ECall (EId (mkIdent "len" eq_refl)) [EStr "abc"], anyt TInt64 (intwrap 3))
  ; (EBn BAdd (EStr "a") (EStr "b"), anyt TString "ab")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EInt 65], anyt TString "A")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EStr "A"], anyt TString "A")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")], anyt TString "ab")
  ; (EBn BEq (EInt 1) (EInt 1), anyt TBool true)
  ; (EBn BLt (EInt 3) (EInt 5), anyt TBool true)
  ; (EBn BEq (EInt 1) (EInt 2), anyt TBool false)
  ; (EBn BEq (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]), anyt TBool true)
  ; (EBn BLt (EBn BDiv (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]))
             (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]), anyt TBool true)   (* 1.5 < 2.0 — the exact dyadic-aligned comparison *)
  ; (EBn BLAnd (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)), anyt TBool true)
  ; (EBn BLOr (EBn BEq (EInt 1) (EInt 2)) (EBn BLt (EInt 3) (EInt 5)), anyt TBool true)
  ; (EUn UNot (EBn BEq (EInt 1) (EInt 2)), anyt TBool true)
  ; (EBn BEq (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)), anyt TBool true)
  ; (EUn UNot (EBn BLAnd (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 3))), anyt TBool true)
  ; (ECall (EId (mkIdent "bool" eq_refl)) [EBn BEq (EInt 1) (EInt 1)], anyt TBool true)
  ; (EBn BEq (EStr "a") (EStr "a"), anyt TBool true)
  ; (EBn BNe (EStr "a") (EStr "b"), anyt TBool true)
  ; (EBn BLt (EStr "a") (EStr "b"), anyt TBool true)
  ; (EBn BLt (EStr "b") (EStr "a"), anyt TBool false)
  ; (EBn BLe (EStr "a") (EStr "a"), anyt TBool true)
  ; (EBn BGt (EStr "b") (EStr "a"), anyt TBool true)
  ; (EBn BLt (EStr "a") (EStr "ab"), anyt TBool true)
  ; (EBn BGe (EStr "b") (EStr "a"), anyt TBool true)
  ; (EBn BGe (EStr "a") (EStr "b"), anyt TBool false)
  ; (EBn BGt (EStr (String (Ascii.ascii_of_nat 200) EmptyString)) (EStr (String (Ascii.ascii_of_nat 100) EmptyString)), anyt TBool true)
  ; (EBn BEq (EBn BAdd (EStr "a") (EStr "b")) (EStr "ab"), anyt TBool true)
  ; (EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) (EStr "A"), anyt TBool true)
  ; (EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")]) (EStr "ab"), anyt TBool true)
  ; (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 1), anyt TInt64 (intwrap 20))   (* constant in-bounds slice-index -> the EXACT element value *)
  ; (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 0), anyt TInt64 (intwrap 10))
  ; (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2]], anyt TInt64 (intwrap 2))   (* len of a fully-evaluable literal -> its length as Go [int] *)
  ; (maplen_e, anyt TInt64 (intwrap 1))   (* len of a fully-evaluable integer-keyed MAP literal -> its (distinct-constant-key) entry count *)
  ].
Example eval_value_good_ok :
  map (fun p => eval_value (fst p)) eval_value_good = map (fun p => Some (snd p)) eval_value_good.
Proof. vm_compute. reflexivity. Qed.

(** BREADTH run-witness: every row of the fold table also RUNS end-to-end — [println(e); return] denotes and
    EXECUTES through cmd.v's authoritative [run_cmd] to the world logging the EXACT model value [v] the fold
    produced ([w_log true [v]]).  MANIFEST-GATED (in [gosem_trust_surface]).  NOTE this theorem is quantified
    OVER the table, so it does NOT by itself pin WHICH behaviors are present (a shrunk table still proves it);
    the required behavior CATEGORIES are pinned STANDALONE, table-independently, by [gosem_category_coverage]
    below. *)
Example eval_value_good_runs : forall w,
  map (fun p => match denote_program (println_prog (fst p)) with
                | Some c => run_cmd 5 c w | None => None end) eval_value_good
  = map (fun p => Some (ORet tt (w_log true (snd p :: nil) w))) eval_value_good.
Proof. intro w. vm_compute. reflexivity. Qed.

(** REQUIRED-CATEGORY COVERAGE as a TYPED obligation.  [runs_to e v] = [println(e); return] denotes and runs
    through cmd.v's [run_cmd] to the world logging [v].  The RECORD TYPE [GoSemRequiredCategoryCoverage] fixes,
    in its FIELD TYPES (one per required behavior category), the EXACT end-to-end behaviors the model must
    exhibit — string-literal PRINTLN, int CONVERSION, exact FLOAT, numeric-compare BOOL, string CONCAT,
    string-compare-of-concat BOOL, a constant in-bounds int-slice-literal INDEX, [len] of a fully-evaluable
    literal (slice AND integer-keyed map), a non-tail RETURN that stops the body with NO output, a denoted PANIC ending in [OPanic], defer
    LIFO ordering at return, a DEFERRED panic firing at return, the determined DIVIDE-BY-ZERO panicking with
    Go's exact runtime value, a panicking ARGUMENT pre-empting its call, and a deferred call's argument
    panicking AT DEFER TIME.  [gosem_category_coverage] inhabits that type, so it can be built ONLY by
    discharging EVERY field with the stated programs+values: a category cannot be dropped without editing this
    typed STATEMENT (the record), never silently by convention.  Table-INDEPENDENT (no reference to
    [eval_value_good]). *)
Definition runs_to (e : GExpr) (v : GoAny) : Prop :=
  forall w, match denote_program (println_prog e) with
            | Some c => run_cmd 5 c w | None => None end = Some (ORet tt (w_log true (v :: nil) w)).
Record GoSemRequiredCategoryCoverage : Prop := {
  rc_println_str : runs_to (EStr "hi") (anyt TString "hi");   (* covers [gosem_demo_prog], which IS [println_prog (EStr "hi")] by definition: observable output, the model's own [w_log] *)
  rc_conv      : runs_to (ECall (EId (mkIdent "int64"   eq_refl)) [EInt 3]) (anyt TI64 (i64wrap 3));
  rc_float     : runs_to (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (anyt TFloat64 (renorm 53 1024 (sf_of_Z 3)));
  rc_float_frac : runs_to (EBn BDiv (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]))
                          (anyt TFloat64 (renorm 53 1024 (sf_of_dyadic 3 (-1))));   (* a FRACTIONAL float constant folds+runs (1.5) *)
  rc_bool      : runs_to (EBn BEq (EInt 1) (EInt 1)) (anyt TBool true);
  rc_concat    : runs_to (EBn BAdd (EStr "a") (EStr "b")) (anyt TString "ab");
  rc_concatcmp : runs_to (EBn BEq (EBn BAdd (EStr "a") (EStr "b")) (EStr "ab")) (anyt TBool true);
  rc_sliceidx  : runs_to (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 1)) (anyt TInt64 (intwrap 20));  (* constant in-bounds int-slice index folds+runs to the element *)
  rc_len       : runs_to (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 10; EInt 20]]) (anyt TInt64 (intwrap 2));  (* len of a fully-evaluable literal folds+runs to its length *)
  rc_maplen    : runs_to maplen_e (anyt TInt64 (intwrap 1));  (* len of a fully-evaluable integer-keyed MAP literal folds+runs to its entry count *)
  rc_return_stops : forall w,                                 (* [return] STOPS the body: the successor println NEVER runs, world UNCHANGED *)
    match denote_program gosem_return_stops_prog with Some c => run_cmd 5 c w | None => None end
    = Some (ORet tt w);
  rc_panic : forall w,                                        (* a denoted [panic("x")] ends in [OPanic] with the model's exact value *)
    match denote_program gosem_panic_demo_prog with Some c => run_cmd 5 c w | None => None end
    = Some (OPanic (anyt TString "x") w);
  rc_defer_lifo : forall w,                                   (* defers run at RETURN, LIFO: body "hi", then "b" (deferred LAST, runs FIRST), then "a" *)
    match denote_program gosem_defer_lifo_prog with Some c => run_cmd 5 c w | None => None end
    = Some (ORet tt (w_log true (anyt TString "a" :: nil)
                      (w_log true (anyt TString "b" :: nil)
                        (w_log true (anyt TString "hi" :: nil) w))));
  rc_defer_panic : forall w,                                  (* a DEFERRED panic does NOT stop the body ("hi" prints) and fires at return *)
    match denote_program gosem_defer_panic_prog with Some c => run_cmd 5 c w | None => None end
    = Some (OPanic (anyt TString "boom") (w_log true (anyt TString "hi" :: nil) w));
  rc_div_zero : forall w,                                     (* the determined divide-by-zero PANICS with Go's exact runtime value *)
    match denote_program gosem_runtime_blank_prog with Some c => run_cmd 5 c w | None => None end
    = Some (OPanic rt_div_zero w);
  rc_arg_panic : forall w,                                    (* a PANICKING argument panics BEFORE the call — println prints NOTHING *)
    match denote_program gosem_arg_panic_prog with Some c => run_cmd 5 c w | None => None end
    = Some (OPanic rt_div_zero w);
  rc_defer_arg_panic : forall w,                              (* a deferred call's ARGS evaluate AT DEFER TIME: the panic fires at the defer statement — the later "hi" NEVER prints *)
    match denote_program gosem_defer_arg_panic_prog with Some c => run_cmd 5 c w | None => None end
    = Some (OPanic rt_div_zero w);
}.
Definition gosem_category_coverage : GoSemRequiredCategoryCoverage.
Proof. constructor; intro w; vm_compute; reflexivity. Qed.
Check gosem_category_coverage : GoSemRequiredCategoryCoverage.   (* the typed obligation, made explicit *)

(** ★ THE LIVE FOLD↔CONST-LAYER AGREEMENT THEOREMS — over [fsf_checked], the per-node checker the
    [floats_checked] BOUNDARY applies to every float-constant subexpression: whenever a binop / negation /
    conversion node is ACCEPTED, its value IS the CONSTANT-layer op ([sf_const_binop] /
    [sf_const_neg] — the IEEE table under zero-sign erasure; raw [sf_model_binop] is only the
    underlying table) applied to the verified operand carriers —
    both widths.  The boundary theorems ([eval_value_floats_checked] + [floats_checked_children_eqs])
    carry the no-bypass claim; these carry the per-node agreement.  Non-vacuous: the [eval_value_good]
    float rows (incl. the laundered/nested/map shapes) are accepted instances. *)
Lemma sf_eqb_struct_eq : forall x y, sf_eqb_struct x y = true -> x = y.
Proof.
  intros x y H; destruct x; destruct y; cbn in H; try discriminate H.
  - apply Bool.eqb_prop in H; subst; reflexivity.
  - apply Bool.eqb_prop in H; subst; reflexivity.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2]; apply andb_true_iff in H2 as [H2 H3].
    apply Bool.eqb_prop in H1; apply Pos.eqb_eq in H2; apply Z.eqb_eq in H3; subst; reflexivity.
Qed.
Theorem fsf_checked_binop_agrees : forall op a b t d f va vb vr,
  ptype (EBn op a b) = Some (PtFloatConst t d) ->
  sf_const_binop t op = Some f ->
  fsf_operand t a = Some va -> fsf_operand t b = Some vb ->
  fsf_checked (EBn op a b) = Some vr ->
  vr = f va vb.
Proof.
  intros op a b t d f va vb vr Hp Hf Ha Hb H.
  cbn [fsf_checked] in H. rewrite Hp in H. cbv beta iota in H.
  destruct (sf_render t (dy_m d) (dy_e d)) as [vr0|] eqn:Hr; [|discriminate H].
  unfold fsf_operand in Ha, Hb. rewrite Ha, Hb, Hf in H.
  destruct (sf_eqb_struct (f va vb) vr0) eqn:Heq; [|discriminate H].
  apply sf_eqb_struct_eq in Heq. injection H as <-. symmetry. exact Heq.
Qed.
Theorem fsf_checked_neg_agrees : forall uop a t d fneg va vr,
  ptype (EUn uop a) = Some (PtFloatConst t d) ->
  sf_const_neg t = Some fneg ->
  fsf_operand t a = Some va ->
  fsf_checked (EUn uop a) = Some vr ->
  vr = fneg va.
Proof.
  intros uop a t d fneg va vr Hp Hf Ha H.
  cbn [fsf_checked] in H. rewrite Hp in H. cbv beta iota in H.
  destruct (sf_render t (dy_m d) (dy_e d)) as [vr0|] eqn:Hr; [|discriminate H].
  unfold fsf_operand in Ha. rewrite Ha, Hf in H.
  destruct (sf_eqb_struct (fneg va) vr0) eqn:Heq; [|discriminate H].
  apply sf_eqb_struct_eq in Heq. injection H as <-. symmetry. exact Heq.
Qed.
Theorem fsf_checked_conv_same_agrees : forall g a t d ta da va vr,
  ptype (ECall g (a :: nil)) = Some (PtFloatConst t d) ->
  ptype a = Some (PtFloatConst ta da) ->
  numty_eqb ta t = true ->
  fsf_checked a = Some va ->
  fsf_checked (ECall g (a :: nil)) = Some vr ->
  vr = va.
Proof.
  intros g a t d ta da va vr Hp Hpa Hty Ha H.
  cbn [fsf_checked] in H. rewrite Hp in H. cbv beta iota in H.
  destruct (sf_render t (dy_m d) (dy_e d)) as [vr0|] eqn:Hr; [|discriminate H].
  rewrite Hpa, Ha, Hty in H.
  destruct (sf_eqb_struct va vr0) eqn:Heq; [|discriminate H].
  apply sf_eqb_struct_eq in Heq. injection H as <-. symmetry. exact Heq.
Qed.
Theorem fsf_checked_conv_narrow_agrees : forall g a d da va vr,
  ptype (ECall g (a :: nil)) = Some (PtFloatConst GTFloat32 d) ->
  ptype a = Some (PtFloatConst GTFloat64 da) ->
  fsf_checked a = Some va ->
  fsf_checked (ECall g (a :: nil)) = Some vr ->
  vr = f32val (f32_of_f64 va).
Proof.
  intros g a d da va vr Hp Hpa Ha H.
  cbn [fsf_checked] in H. rewrite Hp in H. cbv beta iota in H.
  destruct (sf_render GTFloat32 (dy_m d) (dy_e d)) as [vr0|] eqn:Hr; [|discriminate H].
  rewrite Hpa, Ha in H. cbn [numty_eqb] in H.
  destruct (sf_eqb_struct (f32val (f32_of_f64 va)) vr0) eqn:Heq; [|discriminate H].
  apply sf_eqb_struct_eq in Heq. injection H as <-. symmetry. exact Heq.
Qed.
Theorem fsf_checked_conv_widen_agrees : forall g a d da va vr,
  ptype (ECall g (a :: nil)) = Some (PtFloatConst GTFloat64 d) ->
  ptype a = Some (PtFloatConst GTFloat32 da) ->
  fsf_checked a = Some va ->
  fsf_checked (ECall g (a :: nil)) = Some vr ->
  vr = f64_of_f32 (f32_lit va).
Proof.
  intros g a d da va vr Hp Hpa Ha H.
  cbn [fsf_checked] in H. rewrite Hp in H. cbv beta iota in H.
  destruct (sf_render GTFloat64 (dy_m d) (dy_e d)) as [vr0|] eqn:Hr; [|discriminate H].
  rewrite Hpa, Ha in H. cbn [numty_eqb] in H.
  destruct (sf_eqb_struct (f64_of_f32 (f32_lit va)) vr0) eqn:Heq; [|discriminate H].
  apply sf_eqb_struct_eq in Heq. injection H as <-. symmetry. exact Heq.
Qed.

(** an ACCEPTED node's value IS its own dyadic's render — every [fsf_checked] arm returns the
    node-render [vr] (the checker never invents a value) *)
Lemma fsf_checked_render : forall e t d v,
  ptype e = Some (PtFloatConst t d) ->
  fsf_checked e = Some v ->
  sf_render t (dy_m d) (dy_e d) = Some v.
Proof.
  intros e t d v Hp H.
  destruct e; cbn [fsf_checked] in H; rewrite Hp in H; cbv beta iota in H;
    destruct (sf_render t (dy_m d) (dy_e d)) as [vr|] eqn:Hr; try discriminate H;
    repeat first
      [ discriminate H
      | (injection H as <-; reflexivity)
      | (match type of H with
         | (if ?b then _ else _) = _ => destruct b
         | context [match ?x with _ => _ end] => destruct x
         end) ].
Qed.
(** ★ the negation ARM's zero row: negating an ACCEPTED zero-valued float constant is ACCEPTED
    and folds to [+0] — Go's constant rule ([sf_const_neg] via [sf_pos_zero]), for BOTH widths.
    (Operand acceptance is a PREMISE — checker-level totality over the whole admitted class is
    rung 8, after rung 3's finite-render lemma; the binop zero rows are pinned end-to-end by
    [signed_zero_folds_run].) *)
Theorem fsf_checked_neg_zero_total : forall a t da v,
  ptype a = Some (PtFloatConst t da) -> dy_m da = Z0 ->
  fsf_checked a = Some v ->
  fsf_checked (EUn UNeg a) = Some (S754_zero false).
Proof.
  intros a t da v Hpa Hm Ha.
  pose proof (fsf_checked_render a t da v Hpa Ha) as Hren.
  rewrite Hm in Hren.
  destruct t; cbn [sf_render] in Hren; try discriminate Hren.
  - (* GTFloat64 *)
    cbn [sf_of_dyadic renorm] in Hren. injection Hren as <-.
    cbn [fsf_checked ptype]. rewrite Hpa. cbv beta iota. rewrite Hm.
    cbn [Z.opp dy_make dy_norm dy_m dy_e fst snd sf_render sf_of_dyadic renorm].
    unfold fsf_operand_with. rewrite Hpa. cbn [numty_eqb]. rewrite Ha.
    cbv beta iota. reflexivity.
  - (* GTFloat32 *)
    cbn [sf_of_dyadic] in Hren. cbv in Hren. injection Hren as <-.
    cbn [fsf_checked ptype]. rewrite Hpa. cbv beta iota. rewrite Hm.
    cbn [Z.opp dy_make dy_norm dy_m dy_e fst snd sf_render sf_of_dyadic].
    unfold fsf_operand_with. rewrite Hpa. cbn [numty_eqb]. rewrite Ha.
    cbv beta iota. cbv. reflexivity.
Qed.

(** ---- THE GENERAL dyadic↔SF AGREEMENT ARC (plans/dyadic-sf-agreement.md) — rung 1: NEGATION at
    binary64.  Unlike the [fsf_checked_*_agrees] theorems above (which state what acceptance of the
    per-node CONST-LAYER check means), this is checker-free: the dyadic fold's render IS the sign flip
    of the operand's render, proved once over the class ([binary_round_opp] — the sign threads
    inertly through canonicalization).  NO window premise; the [m <> 0] boundary is where CONSTANT
    and RUNTIME semantics split (constants have no signed zero) — the ZERO side is sealed at the
    CHECKER as [sf_const_neg]'s own case, ACCEPTED and denoting [+0]
    ([fsf_checked_neg_zero_total] + [negzero_const_runs]), never a caller obligation. *)
Theorem sf_render_neg_general_f64 : forall m e, m <> Z0 ->
  sf_render GTFloat64 (Z.opp m) e = option_map SFopp (sf_render GTFloat64 m e).
Proof.
  intros m e Hm.
  destruct m as [|p|p]; [contradiction (Hm eq_refl)| |];
    cbn [sf_render Z.opp sf_of_dyadic renorm option_map];
    unfold renorm, binary_normalize; cbn [cond_Zopp];
    f_equal.
  - exact (binary_round_opp 53 1024 false p e).
  - exact (binary_round_opp 53 1024 true p e).
Qed.
(** the [dy_norm] VALUE lemmas (the quotient every later rung states agreement through —
    GoTypes is Definitions-only, so they live here): the odd-split is sign-blind and already-split
    mantissas are fixed points *)
Lemma pos_odd_split_odd : forall p q k,
  pos_odd_split p = (q, k) -> pos_odd_split q = (q, 0%Z).
Proof.
  induction p as [p IH|p IH|]; intros q k H; cbn [pos_odd_split] in H.
  - injection H as <- <-. reflexivity.
  - destruct (pos_odd_split p) as [q' k']. injection H as <- <-.
    exact (IH _ _ eq_refl).
  - injection H as <- <-. reflexivity.
Qed.
Lemma dy_norm_opp : forall m e, dy_norm (Z.opp m) e = dy_neg (dy_norm m e).
Proof.
  intros [|p|p] e; cbn [Z.opp dy_norm];
    [reflexivity| |]; destruct (pos_odd_split p) as [q k]; reflexivity.
Qed.
Lemma dy_norm_idem : forall m e,
  dy_norm (fst (dy_norm m e)) (snd (dy_norm m e)) = dy_norm m e.
Proof.
  intros [|p|p] e; cbn [dy_norm]; [reflexivity| |];
    destruct (pos_odd_split p) as [q k] eqn:E; cbn [fst snd dy_norm];
    rewrite (pos_odd_split_odd p q k E); rewrite Z.add_0_r; reflexivity.
Qed.
(** a SEALED [DyConst] is a [dy_norm] fixed point (its [dy_ok] witness + idempotence) *)
Lemma dyconst_norm_fix : forall d : DyConst, dy_norm (dy_m d) (dy_e d) = (dy_m d, dy_e d).
Proof.
  intros [m e [m0 [e0 Hok]]]. cbn [dy_m dy_e].
  destruct (dy_norm m0 e0) as [m' e'] eqn:E.
  injection Hok as -> ->.
  pose proof (dy_norm_idem m0 e0) as Hi. rewrite E in Hi. cbn [fst snd] in Hi.
  exact Hi.
Qed.
(** the shape [ptype]'s unary-minus fold actually produces
    ([PtFloatConst t (dy_make (Z.opp (dy_m d)) (dy_e d))]) — the reseal is INERT: the sealed
    operand is normalized, and [dy_norm] commutes with negation *)
Corollary sf_render_fold_neg_general_f64 : forall d : DyConst, dy_m d <> Z0 ->
  sf_render GTFloat64 (dy_m (dy_make (Z.opp (dy_m d)) (dy_e d)))
                      (dy_e (dy_make (Z.opp (dy_m d)) (dy_e d)))
  = option_map SFopp (sf_render GTFloat64 (dy_m d) (dy_e d)).
Proof.
  intros d Hm. cbn [dy_make dy_m dy_e].
  rewrite dy_norm_opp, (dyconst_norm_fix d). cbn [dy_neg fst snd].
  exact (sf_render_neg_general_f64 _ _ Hm).
Qed.

(** FAIL-CLOSED pins (LOAD-BEARING, lock the GATE boundary — NOT folds): out-of-range boxing is [None]
    ([mk_uint]/[box_*] never carry a [*wrap]-mangled value); a mixed-WIDTH ill-typed compare [int64(1)==int32(1)]
    has [ptype = None] so [eval_bool]/[eval_value] fail closed (no fabricated [true]); the uint underflow
    [uint(3)-uint(5)] has [ptype = None] ⇒ [printable_arg_ok = false] ⇒ never emitted (the ROOT rejection, not
    the eval backstop).  A supported [ptype = Some PtBool] pins the two string/bool categories are ADMITTED. *)
Definition mixed_width_cmp : GExpr :=
  EBn BEq (ECall (EId (mkIdent "int64" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "int32" eq_refl)) [EInt 1]).
Definition uint_underflow_e := EBn BSub (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "uint" eq_refl)) [EInt 5]).
Example eval_value_failclosed :
  box_float GTFloat64 9007199254740993 0 = None
  /\ box_int GTU8 300 = None
  /\ ptype mixed_width_cmp = None /\ eval_bool mixed_width_cmp = None /\ eval_value mixed_width_cmp = None
  /\ ptype uint_underflow_e = None /\ printable_arg_ok uint_underflow_e = false
  /\ ptype (EBn BEq (EStr "a") (EStr "a")) = Some PtBool
  /\ ptype (ECall (EId (mkIdent "bool" eq_refl)) [EBn BEq (EInt 1) (EInt 1)]) = Some PtBool.
  (* slice-literal fail-closed rows (malformed element) live in [slice_index_undenoted_ok]; the runtime-panicking shapes DENOTE ([slice_index_panics_denote]) *)
Proof. repeat split; vm_compute; reflexivity. Qed.
(** faithful-or-absent: every supported-but-unfoldable form evaluates to [None], never a wrong value — a bool
    with a runtime [len] operand (even under [&&]), a MULTI-BYTE rune string operand ([string(200)], UTF-8 > 1
    byte — ASCII-rune/string-source/concat operands DO fold), an untyped const past the
    default-[int] range, an out-of-range [uint] conversion, the uint underflow (backstop behind the gate), a
    slice-literal [len] with a RUNTIME element, and a map-literal [len] with a RUNTIME value (both
    EVAL-level absent only — they DENOTE through the runtime tier). *)
Definition eval_absent : list GExpr :=
  [ EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)
  ; EBn BLAnd (EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)) (EBn BEq (EInt 2) (EInt 2))
  ; EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EInt 200]) (EStr "A")   (* MULTI-BYTE rune -> string absent (only [0,127] fold) *)
  ; EInt 2147483648
  ; ECall (EId (mkIdent "uint" eq_refl)) [EInt 4294967296]
  ; uint_underflow_e
  ; runlen_e            (* len over a RUNTIME slice element: EVAL-level absent (constant folds only) — DENOTES through the runtime tier ([runtime_tier_runs]) *)
  ; maplen_runval_e ].  (* len over a RUNTIME map value: EVAL-level absent (constant folds only) — DENOTES through the runtime tier ([runtime_maplen_runs]) *)
Example eval_absent_none : forallb (fun e => match eval_value e with None => true | Some _ => false end) eval_absent = true.
Proof. vm_compute. reflexivity. Qed.

(** DENOTABILITY-DECISION witnesses (grouped): [denotable_program] (the decidable predicate of
    [denote_program_dec]) agrees with whether each demo denotes — TRUE for the denoting demos (defer, the
    determined divide-by-zero, and the R3–R7 runtime forms included), FALSE (and
    [denote_program = None]) for the supported-but-undenoted multi-byte-rune program ([runeconv_mb_prog]). *)
Example gosem_denotability_decisions :
  forallb denotable_program
    [gosem_demo_prog; gosem_return_stops_prog; gosem_strlit_prog; gosem_defer_prog;
     gosem_runtime_blank_prog; gosem_arg_panic_prog; gosem_defer_arg_panic_prog;
     println_prog runlen_e; println_prog runconv_e; println_prog runbool_e;
     println_prog maplen_runval_e; println_prog runneg_e; println_prog runrem_e;
     println_prog runrem_neg_e; println_prog runneg_panic_e; println_prog runnot_e;
     println_prog runnot_panic_e] = true
  /\ forallb (fun p => negb (denotable_program p)) [runeconv_mb_prog] = true
  /\ forallb (fun p => match denote_program p with None => true | Some _ => false end)
       [runeconv_mb_prog] = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** REPRESENTATIVE named witnesses of the supported-but-undenoted gap, pinned as a group.
    ⚠ NON-EXHAUSTIVE, in BOTH senses: no theorem bounds the gap's extent (open work), AND known
    undenoted classes can have NO member here (e.g. [!] of a runtime bool comparison, runtime float
    forms) — this list is representative, never a coverage
    claim.  Members: the MULTI-BYTE-RUNE constant ([runeconv_mb] — an EVAL-PARTIAL constant, not a
    runtime form), the typed-unary hole representative [runnot_uint_e] (the class pinned eight-wide
    by [typed_unary_holes_absent], the cells sealed by [typed_unop_holes_none]), and the
    RUNTIME-FLOAT-source conversion [runconv_float_src_e] (CLASS-sealed —
    [reval_val_runfloat_none] / [denote_expr_conv_float_src_absent]; supported-side pin
    [runtime_float_source_conv_absent]).  Each member is pinned supported AND undenoted AND
    eval-level absent.  (SIGNED-ZERO constant folds are NOT members: the checker's authority is
    the CONSTANT-fold layer ([sf_const_binop]/[sf_const_neg] — zero-sign erasure), so
    [-(float64(0))] and the zero-binop shapes fold to [+0] and DENOTE — [negzero_const_runs] +
    [signed_zero_folds_run] below.) *)
Definition undenoted_frontier : list GExpr :=
  [ runeconv_mb
  ; runnot_uint_e
  ; runconv_float_src_e ].
Example undenoted_frontier_pinned :
  forallb (fun e => supported_program (println_prog e)
                    && negb (denotable_program (println_prog e))
                    && match eval_value e with None => true | Some _ => false end)
          undenoted_frontier = true.
Proof. vm_compute. reflexivity. Qed.
(** the SIGNED-ZERO policy pinned (gated): [-(float64(0))] is a CONSTANT, and Go's exact-rational
    constant rule has no [-0] — so it FOLDS, DENOTES, and prints the model's [+0], the value
    pinned BY CONSTRUCTOR here and made observably decisive by the model-level reciprocal probe
    ([reciprocal_sign_decisive] below).  The runtime op [SFopp] on a [+0] VALUE gives [-0] — a
    different (runtime) construct; the checker's fold authority is the CONSTANT layer
    ([sf_const_neg] is its negation row).  Ground-truthed against gc via go run during
    development ([1/x = +Inf] for the fold, [1/-z = -Inf] for the runtime op). *)
Definition negzero_const_e : GExpr :=
  EUn UNeg (ECall (EId (mkIdent "float64" eq_refl)) [EInt 0]).
Example negzero_const_runs : forall w,
  eval_value negzero_const_e = Some (anyt TFloat64 (S754_zero false))
  /\ supported_program (println_prog negzero_const_e) = true
  /\ denotable_program (println_prog negzero_const_e) = true
  /\ (match denote_program (println_prog negzero_const_e) with
      | Some c => run_cmd 5 c w | None => None end)
     = Some (ORet tt (w_log true (anyt TFloat64 (S754_zero false) :: nil) w)).
Proof. intro w. repeat split; vm_compute; reflexivity. Qed.
(** the BINOP zero rows pinned end-to-end, BOTH widths (review round 3): multiplication and
    division of a zero constant BY A NEGATIVE, and negation of such a product — the runtime rows
    carry [xorb] zero-sign leaks ([SFmul +0 -1 = -0]), the constant layer erases them
    ([sf_const_binop]).  Each folds, DENOTES, and prints the model's [+0]: the value pinned BY
    CONSTRUCTOR ([signed_zero_folds_eval]) and made observably decisive by the reciprocal probe
    ([reciprocal_sign_decisive]).  Ground-truthed against gc via go run during development
    ([1/x = +Inf] for all six constant folds, the runtime contrast [1/(r * -1) = -Inf]). *)
Definition zeromul_const_e : GExpr :=
  EBn BMul (ECall (EId (mkIdent "float64" eq_refl)) [EInt 0])
           (EUn UNeg (ECall (EId (mkIdent "float64" eq_refl)) [EInt 1])).
Definition zerodiv_const_e : GExpr :=
  EBn BDiv (ECall (EId (mkIdent "float64" eq_refl)) [EInt 0])
           (EUn UNeg (ECall (EId (mkIdent "float64" eq_refl)) [EInt 1])).
Definition negzeromul_const_e : GExpr := EUn UNeg zeromul_const_e.
Definition zeromul32_const_e : GExpr :=
  EBn BMul (ECall (EId (mkIdent "float32" eq_refl)) [EInt 0])
           (EUn UNeg (ECall (EId (mkIdent "float32" eq_refl)) [EInt 1])).
Definition zerodiv32_const_e : GExpr :=
  EBn BDiv (ECall (EId (mkIdent "float32" eq_refl)) [EInt 0])
           (EUn UNeg (ECall (EId (mkIdent "float32" eq_refl)) [EInt 1])).
Definition negzeromul32_const_e : GExpr := EUn UNeg zeromul32_const_e.
Example signed_zero_folds_eval :
  map eval_value
    [ zeromul_const_e ; zerodiv_const_e ; negzeromul_const_e
    ; zeromul32_const_e ; zerodiv32_const_e ; negzeromul32_const_e ]
  = [ Some (anyt TFloat64 (S754_zero false)) ; Some (anyt TFloat64 (S754_zero false))
    ; Some (anyt TFloat64 (S754_zero false))
    ; Some (anyt TFloat32 (f32_lit (S754_zero false))) ; Some (anyt TFloat32 (f32_lit (S754_zero false)))
    ; Some (anyt TFloat32 (f32_lit (S754_zero false))) ]
  /\ forallb supported_program (map println_prog
       [ zeromul_const_e ; zerodiv_const_e ; negzeromul_const_e
       ; zeromul32_const_e ; zerodiv32_const_e ; negzeromul32_const_e ]) = true
  /\ forallb denotable_program (map println_prog
       [ zeromul_const_e ; zerodiv_const_e ; negzeromul_const_e
       ; zeromul32_const_e ; zerodiv32_const_e ; negzeromul32_const_e ]) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.
Example signed_zero_folds_run : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd 5 c w | None => None end)
      [ zeromul_const_e ; zerodiv_const_e ; negzeromul_const_e
      ; zeromul32_const_e ; zerodiv32_const_e ; negzeromul32_const_e ]
  = [ Some (ORet tt (w_log true (anyt TFloat64 (S754_zero false) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TFloat64 (S754_zero false) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TFloat64 (S754_zero false) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TFloat32 (f32_lit (S754_zero false)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TFloat32 (f32_lit (S754_zero false)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TFloat32 (f32_lit (S754_zero false)) :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
(** the RECIPROCAL-SIGN probe, model-level and DECISIVE — the same observation gc distinguishes
    this class by: the model's [1 / (+0)] is [+Inf] and [1 / (-0)] is [-Inf] at BOTH widths
    ([f64_div]/[f32_div]'s finite/zero rows are sign-exact), so [signed_zero_folds_eval]'s
    by-constructor [+0] pins are OBSERVABLY decisive — a [-0] leaking through the layer would
    flip this gate, not just a constructor field. *)
Example reciprocal_sign_decisive :
  f64_div (renorm 53 1024 (sf_of_dyadic 1 0)) (S754_zero false) = S754_infinity false
  /\ f64_div (renorm 53 1024 (sf_of_dyadic 1 0)) (S754_zero true) = S754_infinity true
  /\ f32val (f32_div (f32_lit (sf_of_dyadic 1 0)) (f32_lit (S754_zero false))) = S754_infinity false
  /\ f32val (f32_div (f32_lit (sf_of_dyadic 1 0)) (f32_lit (S754_zero true))) = S754_infinity true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** All the demo programs above are SUPPORTED (each is emittable Go); grouped so the gate is pinned once. *)
Example demo_progs_supported :
  forallb supported_program
    [gosem_demo_prog; gosem_return_stops_prog; gosem_panic_demo_prog;
     gosem_runtime_blank_prog; gosem_defer_prog; gosem_defer_lifo_prog; gosem_defer_panic_prog;
     gosem_arg_panic_prog; gosem_defer_arg_panic_prog] = true.
Proof. reflexivity. Qed.

(** GOSEM TRUST SURFACE — the EXPLICIT, bounded set of public GoSem results certified zero-axiom,
    grouped into TOPIC surfaces (core / float / slice-index / runtime-int / map / frontier) and composed
    into ONE constant so a SINGLE [Print Assumptions] covers every transitive cone; the Docker manifest
    gate FAILS on any axiom (rule 3).  A theorem not bundled here is not claimed zero-axiom; to certify
    one, add it to its topic surface. *)
Definition gosem_core_surface :=
  (gosem_sound, denote_program_dec, denotable_supported, out_main_denotes, println_main_denotes,
   denotable_stmts_main_denotes, denotable_body_terminator_free_iff,
   eval_value_good_ok, eval_value_good_runs, eval_value_failclosed, eval_absent_none,
   denote_expr_pure, arg_panic_shortcircuit_runs, gosem_category_coverage).
Definition gosem_float_surface :=
  (fsf_checked_binop_agrees, fsf_checked_neg_agrees,
   fsf_checked_conv_same_agrees, fsf_checked_conv_narrow_agrees, fsf_checked_conv_widen_agrees,
   eval_value_floats_checked, floats_checked_children_eqs,
   Fido.builtins.binary_round_opp, sf_render_neg_general_f64, sf_render_fold_neg_general_f64,
   fsf_checked_render, fsf_checked_neg_zero_total, negzero_const_runs,
   sf_const_binop_zero_erased, sf_const_neg_zero_erased,
   signed_zero_folds_eval, signed_zero_folds_run, reciprocal_sign_decisive).
Definition gosem_slice_index_surface :=
  (eval_slice_index_supported, eval_slice_index_reduces, eval_slice_index_oob_class,
   eval_slice_index_inbounds_class, eval_len_reduces, eval_len_supported,
   slice_index_supported_but_undenoted,
   denote_expr_index_in_bounds, denote_expr_index_oob,
   denote_expr_index_elem_panic, denote_expr_index_idx_panic,
   runtime_index_runs, runtime_index_supported, slice_index_panics_denote).
(** SURFACE POLICY (2026-07-02 consolidation): a surface lists PUBLIC guarantees — sealed
    endpoint theorems, program-level runs/supported/absent pins, dispatch AUTHORITY pins, and
    demanded totality/boundary seals.  Internal helpers (shape splits, tag/totality/cases
    lemmas) are NOT listed: `Print Assumptions` on the endpoints pulls their whole cone, so
    they stay inside the gated trust base without noising the public contract. *)
Definition gosem_runtime_int_surface :=
  (denote_expr_div_zero, runtime_tier_runs, runtime_tier_supported,
   denote_expr_div_runs, denote_expr_rem_runs, denote_expr_neg_runs, denote_expr_neg_panic,
   denote_expr_not_runs, denote_expr_not_panic,
   runtime_negrem_runs, runtime_negrem_supported, runtime_not_runs, runtime_not_supported,
   denote_expr_conv_panic, denote_expr_conv_int_panic,
   denote_expr_conv_runs_sealed, denote_expr_conv_int_runs_sealed, denote_expr_conv_src_absent,
   typed_runtime_convchain_runs, typed_runtime_convchain_supported,
   denote_expr_cmp_runs, denote_expr_cmp_left_panic, denote_expr_cmp_right_panic,
   cmp_verdict_eq_model, cmp_verdict_ne_model, cmp_verdict_lt_model, cmp_verdict_le_model,
   cmp_verdict_gt_model, cmp_verdict_ge_model, cmp_verdict_complete,
   runtime_conv_runs, runtime_conv_supported, runtime_bool_runs, runtime_bool_supported,
   denote_expr_typed_unop_runs_sealed, denote_expr_typed_unop_panic,
   reval_val_typed,
   runtime_typed_unop_runs, runtime_typed_unop_supported,
   typed_unop_u8_model, typed_unop_i8_model, typed_unop_u16_model, typed_unop_i16_model,
   typed_unop_u32_model, typed_unop_i32_model, typed_unop_i64_model, typed_unop_u64_model,
   typed_unop_neg_i64_model, typed_unop_neg_u64_model,
   typed_unop_holes_none,
   denote_expr_typed_binop_runs_sealed, denote_expr_typed_binop_left_panic,
   denote_expr_typed_binop_right_panic, denote_expr_typed_binop_src_absent,
   typed_binop_nonarith_none, typed_binop_gtint_none, typed_binop_uint_none,
   typed_binop_nonint_none,
   typed_operand_cross_width_none, typed_binop_cross_width_rejected,
   denote_expr_typed_cmp_runs_sealed, denote_expr_typed_cmp_left_panic,
   denote_expr_typed_cmp_right_panic, denote_expr_typed_cmp_src_absent,
   typed_cmp_noncmp_none,
   typed_cmp_gtint_none, typed_cmp_uint_none, typed_cmp_nonint_none,
   runtime_typed_cmp_runs, runtime_typed_cmp_supported,
   typed_cmp_uint_program_absent, typed_cmp_cross_width_rejected,
   typed_cmp_u8_model, typed_cmp_i8_model, typed_cmp_u16_model, typed_cmp_i16_model,
   typed_cmp_u32_model, typed_cmp_i32_model, typed_cmp_i64_model, typed_cmp_u64_model,
   denote_expr_typed_shift_runs_sealed, denote_expr_typed_shift_count_panic,
   denote_expr_typed_shift_src_absent,
   typed_shift_nonshift_none, typed_shift_gtint_none, typed_shift_uint_none,
   typed_shift_nonint_none,
   shift_count_const_total,
   typed_runtime_shift_runs, typed_shift_edge_runs, typed_shift_edge_supported,
   typed_shift_u8_model, typed_shift_i8_model, typed_shift_u16_model, typed_shift_i16_model,
   typed_shift_u32_model, typed_shift_i32_model, typed_shift_i64_model, typed_shift_u64_model,
   int_bitop_and_model, int_bitop_or_model, int_bitop_xor_model, int_bitop_andnot_model,
   int_shift_op_shl_model, int_shift_op_shr_model, int_bitop_complete, int_shift_op_complete,
   denote_expr_bitwise_runs, denote_expr_bitwise_left_panic, denote_expr_bitwise_right_panic,
   denote_expr_int_shift_runs, denote_expr_int_shift_neg_panic,
   denote_expr_int_shift_left_panic, denote_expr_int_shift_count_panic,
   denote_expr_int_shift_const_count_runs, denote_expr_typed_shift_const_count_runs,
   shift_bigconst_runs, shift_bigconst_supported, shift_bigconst_gate,
   gtint_bitwise_runs, gtint_bitwise_supported, gtint_shift_runs, gtint_shift_supported,
   runtime_typed_binop_runs, runtime_typed_binop_supported,
   typed_mixed_const_runs, typed_mixed_const_supported,
   typed_binop_u8_model, typed_binop_i8_model, typed_binop_u16_model, typed_binop_i16_model,
   typed_binop_u32_model, typed_binop_i32_model, typed_binop_i64_model, typed_binop_u64_model).
Definition gosem_map_surface :=
  (eval_map_len_reduces, eval_map_len_supported, map_len_eval_absent, maplen_divzero_runs,
   map_len_invalid_type_rejected,
   denote_expr_maplen_runs, denote_expr_maplen_panic,
   runtime_maplen_runs, runtime_maplen_supported, runtime_maplen_ambiguous_absent,
   rconstr_vals_ok_iff, rconstr_vals_panic_sound, rconstr_vals_two_panics_absent).
Definition gosem_frontier_surface :=
  (undenoted_frontier_pinned,
   typed_unary_holes_absent, reval_val_runfloat_none, denote_expr_conv_float_src_absent,
   runtime_float_source_conv_absent, runtime_conv_absent_src_pinned,
   typed_binop_uint_program_absent,
   typed_shift_uint_program_absent).
(** The ONE composed public gate: [gosem_trust_surface] composes the topic surfaces above, and
    the topic surfaces DEFINE the current public contract (per the surface policy — endpoints
    and intentional pins; internal helpers ride the endpoints' assumption cones). *)
Definition gosem_trust_surface :=
  (gosem_core_surface, gosem_float_surface, gosem_slice_index_surface,
   gosem_runtime_int_surface, gosem_map_surface, gosem_frontier_surface).
Print Assumptions gosem_trust_surface.

(** ---- STRING-AUTHORITY PINS (gated): each of [str_cmp_op]'s six branches IS, by reflexivity, the FULLY
    QUALIFIED model constant [Fido.builtins.str_*] — so a fork that reroutes a branch breaks a pin and FAILS the
    build ([<=] = the model's [str_geb] with operands swapped).  Bundled into [gosem_string_authority_surface]
    so its [Print Assumptions] certifies the whole cone zero-axiom (the honest place for the "authority
    guarantee" claim); a fork that DIDN'T reroute a live branch would be dead code. *)
Example str_cmp_eq_model : str_cmp_op BEq = Some Fido.builtins.str_eqb.                     Proof. reflexivity. Qed.
Example str_cmp_ne_model : str_cmp_op BNe = Some Fido.builtins.str_neqb.                    Proof. reflexivity. Qed.
Example str_cmp_lt_model : str_cmp_op BLt = Some Fido.builtins.str_ltb.                     Proof. reflexivity. Qed.
Example str_cmp_le_model : str_cmp_op BLe = Some (fun s t => Fido.builtins.str_geb t s).    Proof. reflexivity. Qed.
Example str_cmp_gt_model : str_cmp_op BGt = Some Fido.builtins.str_gtb.                     Proof. reflexivity. Qed.
Example str_cmp_ge_model : str_cmp_op BGe = Some Fido.builtins.str_geb.                     Proof. reflexivity. Qed.
Definition gosem_string_authority_surface :=
  (str_cmp_eq_model, str_cmp_ne_model, str_cmp_lt_model, str_cmp_le_model, str_cmp_gt_model, str_cmp_ge_model).
Print Assumptions gosem_string_authority_surface.
