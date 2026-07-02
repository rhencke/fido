(** ============================================================================
    GoSem.v — the AST's BEHAVIORAL semantics as a BRIDGE into cmd.v (charter Phase 5; ARCHITECTURE.md §GoSem).
    GoSem forks NO second universe: [denote_program : Program -> option (Cmd unit)] TRANSLATES a GoAst program
    into cmd.v's proven command tree, reusing cmd.v's [run_cmd] interpreter + [cbind], the GoSafe gate
    ([expr_stmt_ok] / [svalue]), and the model's own value ctors ([anyt] / [intwrap]) — single-authority, faithful
    (a denoted [println] produces EXACTLY the [w_log] the model's [println] does).

    SLICE 1 (partial, to grow):
    - DENOTES a SUBSET of supported statements: [println]/[print] -> [COut] (the model's [w_log]); [panic] ->
      [CPan]; [return]/[panic] TERMINATE (their unreachable successors need only be SUPPORTED, not denotable);
      [_ = e] -> through the EFFECTFUL [denote_expr] (a constant falls through as [CRet]; a determined
      integer divide-by-zero panics with the model's [rt_div_zero]); [defer <call>] -> [CDfr] (the deferred
      call runs at function-scope return, LIFO — its ARGS evaluate at DEFER time).  Call ARGS are effectful
      ([denote_args] — a panicking arg panics before its call); values fold via [eval_value] (scalar
      constants, a CONSTANT in-bounds index into an ALL-CONSTANT int-slice literal [[]int{..}[k]], [len] of
      such a literal, and [len] of an ALL-CONSTANT integer-keyed ([goty_supported]-typed) map literal — the WHOLE literal is
      evaluated, so a runtime/panicking element or value rejects the fold; the folds are in the
      [eval_value_good] table below); and the RUNTIME tier [reval_int] (R1) denotes DETERMINED runtime
      integers with the MODEL'S OWN ops — runtime [len] (a panicking element aborts construction),
      [+ - * /] with the determined zero divisor panicking [rt_div_zero]; a runtime INDEX and width
      conversions are NOT yet denoted (tiers R2/R3).
    - FAITHFUL-OR-ABSENT: a supported program gets its RIGHT behavior or (not yet) NONE ([denote_program = None]) —
      NEVER a wrong one.  [None] means "not modeled yet", NOT "invalid".
    - [gosem_sound]: denotation ⊆ [SupportedProgram] (structural — [denote] consults the gate; a partial
      [eval_value] narrows only COMPLETENESS, never soundness).  NOT [supported ⇒ denotes] (the roadmap
      converse), and does NOT define [BehaviorSafe].
    - Public TRUST SURFACE (zero-axiom, [Print Assumptions]-gated): [gosem_trust_surface] +
      [gosem_string_authority_surface].  No axioms.
    ============================================================================ *)
From Fido Require Import GoAst GoTypes GoSafe cmd preamble.   (* [preamble] re-exports [builtins]: [GoAny]/[anyt]/[intwrap]/[World]/[w_log]/[Outcome]/[ORet] *)
From Stdlib Require Import String List Bool ZArith.
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
    covers them) ---- [ptype] folds float-const arithmetic exactly (sealed dyadics); the MODEL computes
    with its own [f64_*]/[f32_*]/[SFopp] spec_float ops (the very ops the emitted Go runs).
    [fsf_checked] verifies ONE float-constant node against the model op on the verified operand carriers
    (recursing through float operands and float-to-float conversions; cross-width via
    [f32_of_f64]/[f64_of_f32]); a disagreeing node is ABSENT ([None]), never wrong.  (Mathematically no
    disagreement should exist — IEEE ops are correctly rounded, so an exactly representable result is
    returned exactly; PROVING that once — the general dyadic↔[SF*] class theorem — would let this runtime
    re-verification be dropped, the stated frontier.) *)
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
Definition sf_model_neg (t : GoTy) : option (spec_float -> spec_float) :=
  match t with
  | GTFloat64 => Some SFopp
  | GTFloat32 => Some (fun x => f32val (f32_neg (f32_lit x)))
  | _ => None
  end.
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
                    sf_model_binop t op with
              | Some va, Some vb, Some f => if sf_eqb_struct (f va vb) vr then Some vr else None
              | _, _, _ => None
              end
          | EUn _ a =>
              match fsf_operand_with fsf_checked t a, sf_model_neg t with
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
    [len([]int{2})] declines: absent, not wrong, [map_len_supported_but_undenoted]).  Deliberately a [bool],
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
    [PtFloatConst] subexpression, at any depth, was re-verified against the model op. *)
Theorem eval_value_floats_checked : forall e v, eval_value e = Some v -> floats_checked e = true.
Proof.
  intros e v H. unfold eval_value in H.
  destruct (floats_checked e); [reflexivity | discriminate H].
Qed.

(** ---- EFFECTFUL expression denotation + the RUNTIME-value tier (plans/runtime-value-tier.md, R1).
    Supported programs are CLOSED, so every RUNTIME-classified integer value is DETERMINED.  [reval_int]
    evaluates the [GTInt] runtime fragment by computing with the MODEL'S OWN ops on the model's own
    carrier ([GoInt]) — constants enter through [eval_value] itself (the constant tier stays the single
    fold authority) via the checked [unbox_int]; [len] of an int-slice literal is the count of its
    CONSTRUCTED elements (evaluated left-to-right, the FIRST panicking element aborting construction —
    the verified go-run order; the length goes through [box_int]'s fail-closed [GTInt] builder —
    [rval_len]); [+ - *] are the model's [int_add]/[int_sub]/[int_mul]; [/] is the model's
    evidence-carrying [int_div], its nonzero proof produced by the guarding test itself, and a
    determined ZERO divisor is Go's runtime panic [rt_div_zero] ([%] by zero panics identically; a
    nonzero [%] has no model op yet — honestly absent).  [RPanic] = a determined runtime panic;
    [None] = not-yet-denotable (absent, never wrong).  This tier SUBSUMES the retired shape-based
    [divisor_zero] (its zero-judgment is now [eval_value]'s own fold of the divisor, through the leaf). *)
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
          | EIndex (ESliceLit et es) idx =>
              (* tier R2 — the RUNTIME slice INDEX: Go evaluates the literal (construction, abort on a
                 panicking element) THEN the index; in-bounds yields the element, out-of-bounds (negative
                 or >= length) PANICS with the MODEL's own [rt_index_oob] ([slice_idx_get]'s value — the
                 model's fixed-message posture, inherited).  The outer [PtRunInt GTInt] guard pins the
                 element type to [GTInt]. *)
              match reval_elems_with reval_int es with
              | Some (REVals vs) =>
                  match reval_int idx with
                  | Some (RVal vi) =>
                      if andb (Z.leb 0 (intraw vi)) (Z.ltb (intraw vi) (Z.of_nat (length vs)))
                      then match nth_error vs (Z.to_nat (intraw vi)) with
                           | Some v => Some (RVal v)
                           | None => None   (* unreachable under the bounds check; fail-closed *)
                           end
                      else Some (RPanic rt_index_oob)
                  | Some (RPanic p) => Some (RPanic p)
                  | None => None
                  end
              | Some (REPanic p) => Some (RPanic p)
              | None => None
              end
          | EBn o a b =>
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
                  | BRem => if Z.eqb (intraw vb) 0 then Some (RPanic rt_div_zero) else None
                  | _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Definition reval_elems : list GExpr -> option RElems := reval_elems_with reval_int.

Definition denote_expr (e : GExpr) : option (Cmd GoAny * bool) :=
  match eval_value e with
  | Some v => Some (CRet v, false)
  | None =>
      (* the RUNTIME tier — under the SAME float boundary [eval_value] enforces at its own top *)
      if negb (floats_checked e) then None else
      match reval_int e with
      | Some (RVal v)   => Some (CRet (anyt TInt64 v), false)
      | Some (RPanic p) => Some (CPan p, true)
      | None => None
      end
  end.

(** The pure inclusion: an expression the fold gives a value to denotes to exactly [CRet] of that value
    (fall-through — a pure expression cannot terminate control flow). *)
Lemma denote_expr_pure : forall e v, eval_value e = Some v -> denote_expr e = Some (CRet v, false).
Proof. intros e v H. unfold denote_expr. rewrite H. reflexivity. Qed.

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
  unfold denote_expr. rewrite Hev, Hfc. cbn [negb].
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
  - rewrite Hz. reflexivity.
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
    fragment — deliberately NARROWER than the live denotation boundary ([denote_expr], which since tier R1
    also denotes RUNTIME-determined args like [runlen_e]): a [folded_arg] certainly denotes, so the
    SUFFICIENT converse below holds outright on this fragment; the converse for the runtime tier is future
    work.  A runtime-index arg is neither folded nor yet denoted ([out_boundary_runtime_undenoted]); a
    supported-but-eval-partial constant (multi-byte rune [string(200)]) is pinned by
    [runeconv_multibyte_boundary].  [denotable_supported] pins denotable ⊆ supported. *)
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
    the [COut] flag FALSE.  ⚠ This is a FRAGMENT, NOT the whole supported output class — a print/println of a
    RUNTIME arg ([println(int64(len([]int{1})))]) is SUPPORTED but NOT [folded_arg], so it does NOT denote
    (pinned by [out_boundary_runtime_undenoted]); the runtime tier denotes MORE than this folded fragment
    covers — its converse is future work.  [println_main_denotes]
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
    [runconv_e] (a RUNTIME width conversion — undenoted until tier R3) and [maplen_runval_e] (a map-[len]
    whose VALUE is runtime).  These are LOCAL fixture spellings; the pinned witness group for the gap is
    [undenoted_frontier] below. *)
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
Definition maplen_runval_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTInt [(EInt 1, ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 2]])]].

(** BOUNDARY — the fragment is NOT the whole supported output class: [println(int64(len([]int{1})))]
    is SUPPORTED (valid Go) yet its arg is a RUNTIME width CONVERSION GoSem does not yet evaluate (tier
    R3; NOT [folded_arg] either — the eval level is constant-only), so the program does NOT denote.
    (The runtime-INDEX witness that used to sit here DENOTES through tier R2 — [runtime_index_runs];
    [eval_value runlen_e = None] remains the strictness pin for the EVAL-level [eval_len_supported]
    inclusion.) *)
Definition out_runtime_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runconv_e]); GsReturn].
Example out_boundary_runtime_undenoted :
  supported_program out_runtime_prog = true
  /\ folded_arg runconv_e = false
  /\ denote_program out_runtime_prog = None
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
    [ptype]-supported ([ptype] also admits a RUNTIME index / RUNTIME same-typed elements, undenoted — strictness
    pinned by [slice_index_supported_but_undenoted]).  The evaluator consults [ptype]'s OWN element/index checks,
    so there is no looser private boundary. *)
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
    [map_len_supported_but_undenoted]. *)
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
      VALID-Go OOB constant [[..][5]] (a slice OOB is a RUN-TIME panic, not a compile error — declined, never
      a wrong value), a runtime-PANICKING UNSELECTED element ([[]int{20, 1/len([]int{})}[0]] panics in Go
      during whole-literal construction, verified `go run` — hence [eval_int_slice_elems] evaluates ALL
      elements), the wrong-typed-element literal, and an out-of-[uint8]-range element.  Faithful-or-absent:
      declined-as-undenoted, NOT proven-unsafe. *)
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
  = [ (None, Some (OPanic rt_index_oob w)) ; (None, Some (OPanic rt_div_zero w)) ].
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
    indexes ([]int{len([]int{1})}[0] prints 1); a runtime NEGATIVE index panics [rt_index_oob]
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
    ; Some (OPanic rt_index_oob w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example runtime_index_supported :
  forallb supported_program
    [ println_prog runidx_e
    ; println_prog (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)) ] = true.
Proof. vm_compute. reflexivity. Qed.

(** STRICT-SUBSET pin (GATED, map-[len]): a map literal whose VALUE is a same-typed RUNTIME int
    ([map[int]int{1: len([]int{2})}]) is [ptype]-SUPPORTED (valid Go) yet undenoted at BOTH the expression
    and program level — so [eval_map_len_supported] is a strict INCLUSION, not equality; runtime values
    await runtime evaluation (B3). *)
Example map_len_supported_but_undenoted :
  ptype maplen_runval_e = Some (PtRunInt GTInt)
  /\ eval_value maplen_runval_e = None
  /\ denote_program (println_prog maplen_runval_e) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

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

(** The escape is REAL (the converse is genuinely sufficient-not-necessary): [return; println(runconv_e)]
    is a DENOTABLE body ([return] terminates; the runtime-arg [println] is a SUPPORTED dead tail) whose tail
    does NOT denote, so [denotable_body = true] while [forallb stmt_denotable = false].  This body HAS a
    terminator — exactly why the iff above does not apply to it. *)
Example denotable_body_escapes_stmt_denotable :
  denotable_body [GsReturn;
    GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runconv_e])] = true
  /\ forallb stmt_denotable [GsReturn;
       GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runconv_e])] = false.
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
    in each is the runtime width CONVERSION ([runconv_e], supported-printable yet undenoted —
    [out_boundary_runtime_undenoted]): as a LATER ARG of the panicking call, as the SUCCESSOR statement, and
    as the successor of a DEFERRED panicking-arg call.  Each program denotes and runs to [OPanic rt_div_zero]
    with NO output. *)
Definition gosem_arg_panic_tail_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [divzero_e; runconv_e]); GsReturn].
Definition gosem_arg_panic_succ_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runconv_e]); GsReturn].
Definition gosem_defer_arg_panic_succ_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runconv_e]); GsReturn].
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

(** ★ THE LIVE FOLD↔MODEL AGREEMENT THEOREMS — over [fsf_checked], the per-node checker the
    [floats_checked] BOUNDARY applies to every float-constant subexpression: whenever a binop / negation /
    conversion node is ACCEPTED, its value IS the model op applied to the verified operand carriers —
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
  sf_model_binop t op = Some f ->
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
  sf_model_neg t = Some fneg ->
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
  (* slice-literal fail-closed rows (runtime-panicking / malformed element) live in [slice_index_undenoted_ok] *)
Proof. repeat split; vm_compute; reflexivity. Qed.
(** faithful-or-absent: every supported-but-unfoldable form evaluates to [None], never a wrong value — a bool
    with a runtime [len] operand (even under [&&]), a MULTI-BYTE rune string operand ([string(200)], UTF-8 > 1
    byte — ASCII-rune/string-source/concat operands DO fold), an untyped const past the
    default-[int] range, an out-of-range [uint] conversion, the uint underflow (backstop behind the gate), a
    slice-literal [len] with a RUNTIME element, and a map-literal [len] with a RUNTIME value (runtime values
    await B3). *)
Definition eval_absent : list GExpr :=
  [ EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)
  ; EBn BLAnd (EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)) (EBn BEq (EInt 2) (EInt 2))
  ; EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EInt 200]) (EStr "A")   (* MULTI-BYTE rune -> string absent (only [0,127] fold) *)
  ; EInt 2147483648
  ; ECall (EId (mkIdent "uint" eq_refl)) [EInt 4294967296]
  ; uint_underflow_e
  ; runlen_e            (* len over a RUNTIME slice element: EVAL-level absent (constant folds only) — DENOTES through the runtime tier ([runtime_tier_runs]) *)
  ; maplen_runval_e ].  (* len over a RUNTIME map value: supported, honestly unfolded *)
Example eval_absent_none : forallb (fun e => match eval_value e with None => true | Some _ => false end) eval_absent = true.
Proof. vm_compute. reflexivity. Qed.

(** DENOTABILITY-DECISION witnesses (grouped): [denotable_program] (the decidable predicate of
    [denote_program_dec]) agrees with whether each demo denotes — TRUE for the denoting demos (defer and the
    determined divide-by-zero included), FALSE (and [denote_program = None]) for the supported-but-undenoted
    runtime-width-CONVERSION program ([out_runtime_prog]). *)
Example gosem_denotability_decisions :
  forallb denotable_program
    [gosem_demo_prog; gosem_return_stops_prog; gosem_strlit_prog; gosem_defer_prog;
     gosem_runtime_blank_prog; gosem_arg_panic_prog; gosem_defer_arg_panic_prog;
     println_prog runlen_e] = true
  /\ forallb (fun p => negb (denotable_program p)) [out_runtime_prog] = true
  /\ forallb (fun p => match denote_program p with None => true | Some _ => false end)
       [out_runtime_prog] = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** REPRESENTATIVE named witnesses of the supported-but-undenoted gap, pinned as a group.
    ⚠ NON-EXHAUSTIVE, in BOTH senses: no theorem bounds the gap's extent (open work), AND several
    known undenoted classes have NO member here yet (e.g. runtime unary [-]/[^], nonzero runtime [%],
    runtime float forms) — this list is representative, never a coverage claim.  Members: the
    MULTI-BYTE-RUNE constant ([runeconv_mb] — an EVAL-PARTIAL constant, not a runtime form), a RUNTIME
    width CONVERSION ([runconv_e] — tier R3), a RUNTIME bool COMPARISON ([len(..) == 0] — no runtime bool
    rule yet), and the runtime map VALUE ([maplen_runval_e] — needs its own map-value rule).  (The OOB
    constant index and the runtime index LEFT this list at tier R2 — they now DENOTE, as [rt_index_oob]
    panics or values: [runtime_index_runs].)  Each member is pinned supported AND undenoted AND eval-level
    absent. *)
Definition undenoted_frontier : list GExpr :=
  [ runeconv_mb
  ; runconv_e
  ; EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)
  ; maplen_runval_e ].
Example undenoted_frontier_pinned :
  forallb (fun e => supported_program (println_prog e)
                    && negb (denotable_program (println_prog e))
                    && match eval_value e with None => true | Some _ => false end)
          undenoted_frontier = true.
Proof. vm_compute. reflexivity. Qed.

(** All the demo programs above are SUPPORTED (each is emittable Go); grouped so the gate is pinned once. *)
Example demo_progs_supported :
  forallb supported_program
    [gosem_demo_prog; gosem_return_stops_prog; gosem_panic_demo_prog;
     gosem_runtime_blank_prog; gosem_defer_prog; gosem_defer_lifo_prog; gosem_defer_panic_prog;
     gosem_arg_panic_prog; gosem_defer_arg_panic_prog] = true.
Proof. reflexivity. Qed.

(** GOSEM TRUST SURFACE — the EXPLICIT, bounded set of public GoSem results certified zero-axiom.  Bundling the
    proof terms into ONE constant makes a SINGLE [Print Assumptions] cover their whole transitive cones; the
    Docker manifest gate captures the report and FAILS on any axiom (rule 3, manifest empty).  This is a seal
    for exactly this surface, NOT a module-wide claim — a theorem not bundled here is not claimed zero-axiom;
    to certify one, ADD it to the tuple. *)
Definition gosem_trust_surface :=
  (gosem_sound, denote_program_dec, denotable_supported, out_main_denotes, println_main_denotes,
   denotable_stmts_main_denotes, denotable_body_terminator_free_iff,
   eval_value_good_ok, eval_value_good_runs, eval_value_failclosed, eval_absent_none,
   eval_slice_index_supported, eval_slice_index_reduces, eval_slice_index_oob_class, eval_slice_index_inbounds_class,
   eval_len_reduces, eval_len_supported,
   eval_map_len_reduces, eval_map_len_supported, map_len_supported_but_undenoted, maplen_divzero_runs,
   map_len_invalid_type_rejected,
   fsf_checked_binop_agrees, fsf_checked_neg_agrees,
   fsf_checked_conv_same_agrees, fsf_checked_conv_narrow_agrees, fsf_checked_conv_widen_agrees,
   eval_value_floats_checked, floats_checked_children_eqs,
   denote_expr_pure, denote_expr_div_zero, runtime_tier_runs, runtime_tier_supported,
   runtime_index_runs, runtime_index_supported, slice_index_panics_denote,
   undenoted_frontier_pinned,
   arg_panic_shortcircuit_runs,
   slice_index_supported_but_undenoted,
   gosem_category_coverage).
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
