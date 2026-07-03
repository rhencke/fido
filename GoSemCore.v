(** ============================================================================
    GoSemCore.v — GoSem's pure FOLD/FLOAT layer (the ARCHITECTURE.md §3a physical split,
    file 1): box/render ([box_int]/[box_float]/[sf_render]), the CONSTANT-fold op layer
    ([sf_const_binop]/[sf_const_neg]), the [floats_checked] boundary machinery +
    [fsf_checked], and the dyadic↔SF* agreement arc (plans/dyadic-sf-agreement.md;
    rungs 1–6 landed: NEG, the window bridges, wide determinism, ADD + SUB raw at
    binary64, MUL + exact DIV at the CONSTANT-op layer; rung 7 (f32) in progress).
    NO EVALUATOR HERE: [eval_value] and its [Local] core live in GoSemDenote.v with the proofs
    that compute through them — the core must stay UNCALLABLE from importers (it would skip
    the [floats_checked] boundary; sealed by the [neg_float_boundary_bypass_*] negtests).
    Denotation + the runtime tiers live in GoSemDenote.v; the program-level fixture
    groups, demos + the gated surfaces live in GoSem.v (the composition point re-exporting
    both; the surfaces remain the public authority).
    ============================================================================ *)
From Fido Require Import GoAst GoTypes preamble.   (* [preamble] re-exports [builtins]: [GoAny]/[anyt]/[intwrap]/[World]/[w_log]/[Outcome]/[ORet] *)
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

(** rung 3's LIVE-BOUNDARY BRIDGE.  The float acceptance boundary is [ptype]'s CONSTRUCTION
    sites (every one repr-GUARDED — the invariant [ptype_float_const_repr] below) and
    [box_float] ([box_float_gate]); [sf_render] is RAW (it renders any dyadic; its exactness on
    ACCEPTED payloads comes from the invariant, never from [sf_render] itself).  The endpoint
    theorems [ptype_float_payload_{f64,f32}] split every accepted payload into ZERO or the
    [binary_round_exact] premises (digits-vs-magnitude via [digits2_pos_le_of_lt_pow]). *)
Lemma float_dyadic_repr_f64_premises : forall m e p,
  float_dyadic_repr GTFloat64 m e = true ->
  Z.abs m = Zpos p ->
  (Zpos (digits2_pos p) <= 53)%Z /\ (emin 53 1024 <= e)%Z
  /\ (Zpos (digits2_pos p) + e <= 1024)%Z.
Proof.
  intros m e p H Habs. unfold float_dyadic_repr in H.
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply andb_true_iff in H2; destruct H2 as [H2 H3].
  apply Z.ltb_lt in H1; apply Z.leb_le in H2; apply Z.leb_le in H3.
  rewrite Habs in H1. change 9007199254740992%Z with (2 ^ 53)%Z in H1.
  assert (Hd : (Zpos (digits2_pos p) <= 53)%Z)
    by (apply digits2_pos_le_of_lt_pow; [lia | exact H1]).
  split; [exact Hd|]. split; [unfold emin; lia|]. lia.
Qed.
Lemma float_dyadic_repr_f32_premises : forall m e p,
  float_dyadic_repr GTFloat32 m e = true ->
  Z.abs m = Zpos p ->
  (Zpos (digits2_pos p) <= 24)%Z /\ (emin 24 128 <= e)%Z
  /\ (Zpos (digits2_pos p) + e <= 128)%Z.
Proof.
  intros m e p H Habs. unfold float_dyadic_repr in H.
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply andb_true_iff in H2; destruct H2 as [H2 H3].
  apply Z.ltb_lt in H1; apply Z.leb_le in H2; apply Z.leb_le in H3.
  rewrite Habs in H1. change 16777216%Z with (2 ^ 24)%Z in H1.
  assert (Hd : (Zpos (digits2_pos p) <= 24)%Z)
    by (apply digits2_pos_le_of_lt_pow; [lia | exact H1]).
  split; [exact Hd|]. split; [unfold emin; lia|]. lia.
Qed.
(** the INVARIANT: every [ptype]-accepted [PtFloatConst] payload is IN-WINDOW — structural,
    because every construction site is repr-guarded (the [ptype_tint_const_repr] pattern). *)
Lemma ptype_add_str_row_float : forall cl cr t d,
  (match cl, cr with PtStr, PtStr => Some PtStr | _, _ => num_binop BAdd cl cr end)
    = Some (PtFloatConst t d) ->
  num_binop BAdd cl cr = Some (PtFloatConst t d).
Proof. intros cl cr t d H; destruct cl; try exact H; destruct cr; try exact H; discriminate H. Qed.
Lemma num_arith_float_repr : forall f df cl cr t d,
  num_arith f df cl cr = Some (PtFloatConst t d) ->
  float_dyadic_repr t (dy_m d) (dy_e d) = true.
Proof.
  intros f df cl cr t d H.
  destruct cl; destruct cr; cbn [num_arith] in H; try discriminate H;
  unfold dy_fold_at in H;
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
Lemma num_binop_float_repr : forall o cl cr t d,
  num_binop o cl cr = Some (PtFloatConst t d) ->
  float_dyadic_repr t (dy_m d) (dy_e d) = true.
Proof.
  intros o cl cr t d H.
  destruct o; cbn [num_binop] in H;
  repeat first
    [ discriminate H
    | exact (num_arith_float_repr _ _ _ _ _ _ H)
    | (injection H as H1 H2; subst; assumption)
    | (cbv beta iota zeta in H;
       match type of H with
       | (if ?b then _ else _) = _ =>
           let R := fresh "R" in destruct b eqn:R; [ idtac | try discriminate H ]
       | context [match ?x with _ => _ end] => destruct x
       end) ].
Qed.
Lemma conv_to_scalar_float_repr : forall ca t' t d,
  conv_to_scalar ca t' = Some (PtFloatConst t d) ->
  float_dyadic_repr t (dy_m d) (dy_e d) = true.
Proof.
  intros ca t' t d H.
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
Lemma ptype_float_const_repr : forall e t d,
  ptype e = Some (PtFloatConst t d) -> float_dyadic_repr t (dy_m d) (dy_e d) = true.
Proof.
  intros e t d H.
  destruct e; cbn [ptype] in H; try discriminate H;
  repeat first
    [ discriminate H
    | exact (conv_to_scalar_float_repr _ _ _ _ H)
    | exact (num_binop_float_repr _ _ _ _ _ H)
    | exact (num_binop_float_repr _ _ _ _ _ (ptype_add_str_row_float _ _ _ _ H))
    | (injection H as H1 H2; subst; assumption)
    | (cbv beta iota zeta in H;
       match type of H with
       | (if ?b then _ else _) = _ =>
           let R := fresh "R" in destruct b eqn:R; [ idtac | try discriminate H ]
       | context [match ?x with _ => _ end] => destruct x
       end) ].
Qed.
(** ★ the LIVE endpoints (gated): every ACCEPTED float payload is ZERO or satisfies
    [binary_round_exact]'s premises — the review-demanded zero/nonzero split over [ptype]
    itself, no caller-side window obligation left. *)
Theorem ptype_float_payload_f64 : forall e d,
  ptype e = Some (PtFloatConst GTFloat64 d) ->
  dy_m d = Z0
  \/ (exists p, Z.abs (dy_m d) = Zpos p
      /\ (Zpos (digits2_pos p) <= 53)%Z
      /\ (emin 53 1024 <= dy_e d)%Z
      /\ (Zpos (digits2_pos p) + dy_e d <= 1024)%Z).
Proof.
  intros e d Hp.
  pose proof (ptype_float_const_repr e _ _ Hp) as Hr.
  destruct (dy_m d) as [|q|q] eqn:Em; [left; reflexivity| |];
    right; exists q; (split; [reflexivity|]);
    exact (float_dyadic_repr_f64_premises _ _ q Hr eq_refl).
Qed.
Theorem ptype_float_payload_f32 : forall e d,
  ptype e = Some (PtFloatConst GTFloat32 d) ->
  dy_m d = Z0
  \/ (exists p, Z.abs (dy_m d) = Zpos p
      /\ (Zpos (digits2_pos p) <= 24)%Z
      /\ (emin 24 128 <= dy_e d)%Z
      /\ (Zpos (digits2_pos p) + dy_e d <= 128)%Z).
Proof.
  intros e d Hp.
  pose proof (ptype_float_const_repr e _ _ Hp) as Hr.
  destruct (dy_m d) as [|q|q] eqn:Em; [left; reflexivity| |];
    right; exists q; (split; [reflexivity|]);
    exact (float_dyadic_repr_f32_premises _ _ q Hr eq_refl).
Qed.
(** [box_float] is the VALUE-path gate: a boxed float implies the window. *)
Lemma box_float_gate : forall t m e v,
  box_float t m e = Some v -> float_dyadic_repr t m e = true.
Proof.
  intros t m e v H. unfold box_float in H.
  destruct (float_dyadic_repr t m e); [reflexivity | discriminate H].
Qed.

(** ---- rung 4 — VALUE-DETERMINISM of [binary_normalize] on the windowed class
    (plans/dyadic-sf-agreement.md).  No doubling induction needed: with [binary_round_exact]
    both representations reduce to closed canonical forms, and DIGITS+EXPONENT is invariant
    under the odd-core split ([pos_odd_split_digits]), so the [fexp] targets coincide and the
    aligned mantissas are value-equal positives. *)
Lemma pos_odd_split_val : forall p q k,
  pos_odd_split p = (q, k) -> (0 <= k)%Z /\ Zpos p = (Zpos q * 2 ^ k)%Z.
Proof.
  induction p as [p IH|p IH|]; intros q k H; cbn [pos_odd_split] in H.
  - injection H as <- <-. split; [lia|]. rewrite Z.pow_0_r. lia.
  - destruct (pos_odd_split p) as [q' k'] eqn:E. injection H as <- <-.
    destruct (IH _ _ eq_refl) as [Hk Hv].
    split; [lia|].
    rewrite Pos2Z.inj_xO, Hv, Z.pow_succ_r by exact Hk. ring.
  - injection H as <- <-. split; [lia|]. rewrite Z.pow_0_r. lia.
Qed.
Lemma pos_odd_split_digits : forall p q k,
  pos_odd_split p = (q, k) ->
  Zpos (digits2_pos p) = (Zpos (digits2_pos q) + k)%Z.
Proof.
  induction p as [p IH|p IH|]; intros q k H; cbn [pos_odd_split] in H.
  - injection H as <- <-. lia.
  - destruct (pos_odd_split p) as [q' k'] eqn:E. injection H as <- <-.
    pose proof (IH _ _ eq_refl) as Hd.
    cbn [digits2_pos]. rewrite Pos2Z.inj_succ. lia.
  - injection H as <- <-. lia.
Qed.
(** [binary_round] depends only on the ODD CORE and the total exponent — on the window. *)
Lemma binary_round_of_norm : forall prec emax s p e q a,
  pos_odd_split p = (q, a) ->
  (Zpos (digits2_pos p) <= prec)%Z ->
  (emin prec emax <= e)%Z ->
  (Zpos (digits2_pos p) + e <= emax)%Z ->
  (2 <= emax)%Z ->
  binary_round prec emax s p e = binary_round prec emax s q (e + a).
Proof.
  intros prec emax s p e q a Hsp Hd He Hde Hemax.
  destruct (pos_odd_split_val p q a Hsp) as [Ha Hv].
  pose proof (pos_odd_split_digits p q a Hsp) as Hdig.
  assert (Hdq : (Zpos (digits2_pos q) <= prec)%Z) by lia.
  assert (Heq : (emin prec emax <= e + a)%Z) by lia.
  assert (Hdeq : (Zpos (digits2_pos q) + (e + a) <= emax)%Z) by lia.
  rewrite (binary_round_exact prec emax s p e Hd He Hde Hemax).
  rewrite (binary_round_exact prec emax s q (e + a) Hdq Heq Hdeq Hemax).
  replace (Zpos (digits2_pos q) + (e + a))%Z with (Zpos (digits2_pos p) + e)%Z by lia.
  set (T := fexp prec emax (Zpos (digits2_pos p) + e)) in *.
  assert (HT : (T <= e)%Z) by (unfold T, fexp, emin in *; lia).
  assert (HTq : (T <= e + a)%Z) by lia.
  f_equal.
  apply Pos2Z.inj.
  rewrite (shl_align_fst_val p e T HT), (shl_align_fst_val q (e + a) T HTq).
  rewrite Hv.
  rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
  f_equal. f_equal. lia.
Qed.
(** ---- rung 5b — the WIDE bridge: [binary_round] on a RAW mantissa whose odd core is
    in-window agrees with [binary_round] of the core at the adjusted exponent — the raw digit
    count may EXCEED [prec] (the carry class).  Two regimes: if the [fexp] target stays at or
    below the raw exponent, the raw side is secretly in-window too (the target formula forces
    [digits <= prec]) and rung 4's [binary_round_of_norm] applies; otherwise the raw mantissa
    IS the core-canonical mantissa with [T-e] appended zero bits, and the 5a zeros walk
    ([iter_pos_shr1_zeros]) consumes them with the location staying exact. *)
Lemma binary_round_of_norm_wide : forall prec emax s p e q a,
  pos_odd_split p = (q, a) ->
  (Zpos (digits2_pos q) <= prec)%Z ->
  (emin prec emax <= e + a)%Z ->
  (Zpos (digits2_pos q) + (e + a) <= emax)%Z ->
  (2 <= emax)%Z ->
  binary_round prec emax s p e = binary_round prec emax s q (e + a).
Proof.
  intros prec emax s p e q a Hsp Hdq He Hde Hemax.
  destruct (pos_odd_split_val p q a Hsp) as [Ha Hv].
  pose proof (pos_odd_split_digits p q a Hsp) as Hdp.
  set (T := fexp prec emax (Zpos (digits2_pos q) + (e + a))) in *.
  assert (HTa : (T <= e + a)%Z) by (unfold T, fexp, emin in *; lia).
  destruct (Z.leb T e) eqn:Ecase.
  - (* the target at or below the raw exponent: the raw side is in-window after all *)
    apply Z.leb_le in Ecase.
    apply (binary_round_of_norm prec emax s p e q a Hsp); [| | |exact Hemax].
    + (* digits p <= prec: T >= digits p + e - prec always, so T <= e forces it *)
      unfold T, fexp, emin in *; lia.
    + (* emin <= e: emin <= T <= e *)
      unfold T, fexp, emin in *; lia.
    + lia.
  - (* the raw exponent below the target: shift back through the appended zeros *)
    apply Z.leb_gt in Ecase.
    (* the RHS in canonical form *)
    assert (Heq2 : (emin prec emax <= e + a)%Z) by exact He.
    rewrite (binary_round_exact prec emax s q (e + a) Hdq Heq2 Hde Hemax).
    pose proof (shl_align_snd q (e + a) _ HTa) as Hsndc.
    pose proof (shl_align_digits q (e + a) _ HTa) as Hdigc.
    pose proof (shl_align_fst_val q (e + a) _ HTa) as Hvalc.
    destruct (shl_align q (e + a) T) as [mc ezc] eqn:Ec.
    cbn [fst snd] in Hsndc, Hdigc, Hvalc |- *. subst ezc.
    (* the positive shift count k = T - e *)
    destruct (Z.sub T e) as [|kp|kp] eqn:Ek; [lia| |lia].
    (* the raw mantissa IS the canonical core mantissa with kp appended zeros *)
    assert (Hpiter : p = Pos.iter xO mc kp).
    { apply Pos2Z.inj. rewrite iter_xO_val, Hvalc, Hv.
      rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
      f_equal. f_equal. lia. }
    assert (Hcap : Z.leb T (emax - prec) = true)
      by (apply Z.leb_le; unfold T, fexp, emin in *; lia).
    (* dissolve the abbreviation so every rewrite below is syntactic on the raw terms; the
       destruct above could not abstract the goal's RAW occurrence (its subject named the
       folded [T]), so replace it explicitly *)
    unfold T in *.
    rewrite Ec. cbn [fst].
    (* walk the raw side *)
    unfold binary_round.
    rewrite Hdp.
    replace (Zpos (digits2_pos q) + a + e)%Z with (Zpos (digits2_pos q) + (e + a))%Z by lia.
    unfold shl_align. rewrite Ek. cbv beta iota.
    unfold binary_round_aux, shr_fexp.
    cbn [Zdigits2].
    rewrite Hdp.
    replace (Zpos (digits2_pos q) + a + e)%Z with (Zpos (digits2_pos q) + (e + a))%Z by lia.
    rewrite Ek.
    cbn [shr shr_record_of_loc].
    rewrite Hpiter, iter_pos_shr1_zeros.
    cbn [shr_m loc_of_shr_record shr_r shr_s round_nearest_even Zdigits2].
    replace (e + Zpos kp)%Z
      with (fexp prec emax (Zpos (digits2_pos q) + (e + a))) by lia.
    rewrite Hdigc, Z.sub_diag.
    cbn [shr shr_record_of_loc shr_m].
    rewrite Hcap. reflexivity.
Qed.

(** ★ the DETERMINISM endpoint (gated): [dy_norm]-equal representations normalize to the SAME
    canonical float, with the window premises on the SHARED NORMAL FORM only — the raw sides'
    digit counts are UNBOUNDED ([binary_round_of_norm_wide]), exactly what [SFadd]'s raw
    aligned sums need. *)
Theorem binary_normalize_wide_determined : forall prec emax m1 e1 m2 e2 s zq k,
  dy_norm m1 e1 = (zq, k) ->
  dy_norm m2 e2 = (zq, k) ->
  (zq = Z0 \/ exists q, Z.abs zq = Zpos q
     /\ (Zpos (digits2_pos q) <= prec)%Z /\ (emin prec emax <= k)%Z
     /\ (Zpos (digits2_pos q) + k <= emax)%Z) ->
  (2 <= emax)%Z ->
  binary_normalize prec emax m1 e1 s = binary_normalize prec emax m2 e2 s.
Proof.
  intros prec emax m1 e1 m2 e2 s zq k H1 H2 HW Hemax.
  destruct m1 as [|p1|p1]; destruct m2 as [|p2|p2];
    cbn [dy_norm] in H1, H2;
    try (destruct (pos_odd_split p1) as [q1 k1] eqn:E1);
    try (destruct (pos_odd_split p2) as [q2 k2] eqn:E2);
    injection H1 as <- <-;
    try discriminate H2;
    [ reflexivity | | ];
    injection H2 as Hq Hk;
    (destruct HW as [HW | [q [Habs W]]]; [discriminate HW|]);
    cbn [Z.abs] in Habs; injection Habs as <-;
    destruct W as [Wd [We Wde]];
    assert (Wd2 : (Zpos (digits2_pos q2) <= prec)%Z) by (rewrite Hq; exact Wd);
    assert (We2 : (emin prec emax <= e2 + k2)%Z) by (rewrite Hk; exact We);
    assert (Wde2 : (Zpos (digits2_pos q2) + (e2 + k2) <= emax)%Z)
      by (rewrite Hq, Hk; exact Wde);
    cbn [binary_normalize];
    rewrite (binary_round_of_norm_wide prec emax _ _ e1 q1 k1 E1 Wd We Wde Hemax);
    rewrite (binary_round_of_norm_wide prec emax _ _ e2 q2 k2 E2 Wd2 We2 Wde2 Hemax);
    rewrite Hq, Hk; reflexivity.
Qed.
(** the ASSEMBLY's per-operand characterization: a windowed NONZERO dyadic renders to a
    canonical finite whose SIGNED mantissa carries the value in DIFFERENCE form
    ([cond_Zopp s mc = m * 2^(e-T)], all exponents nonneg differences — [Z.pow] is zero on
    negatives, so absolute "m*2^e" values are never stated). *)
Lemma render_signed_value_gen : forall prec emax m e p,
  Z.abs m = Zpos p ->
  (Zpos (digits2_pos p) <= prec)%Z ->
  (emin prec emax <= e)%Z ->
  (Zpos (digits2_pos p) + e <= emax)%Z ->
  (2 <= emax)%Z ->
  exists s mc T,
    binary_normalize prec emax m e false = S754_finite s mc T
    /\ cond_Zopp s (Zpos mc) = (m * 2 ^ (e - T))%Z
    /\ (emin prec emax <= T)%Z /\ (T <= e)%Z.
Proof.
  intros prec emax m e p Habs Hd He Hde Hemax.
  assert (HT : (fexp prec emax (Zpos (digits2_pos p) + e) <= e)%Z)
    by (unfold fexp, emin in *; lia).
  assert (HTe : (emin prec emax <= fexp prec emax (Zpos (digits2_pos p) + e))%Z)
    by (unfold fexp, emin in *; lia).
  pose proof (shl_align_fst_val p e _ HT) as Hval.
  destruct m as [|p'|p']; cbn [Z.abs] in Habs; try discriminate Habs;
    injection Habs as ->.
  - exists false, (fst (shl_align p e (fexp prec emax (Zpos (digits2_pos p) + e)))),
           (fexp prec emax (Zpos (digits2_pos p) + e)).
    split; [|split; [|split]].
    + cbn [binary_normalize].
      exact (binary_round_exact prec emax false p e Hd He Hde Hemax).
    + cbn [cond_Zopp]. exact Hval.
    + exact HTe.
    + exact HT.
  - exists true, (fst (shl_align p e (fexp prec emax (Zpos (digits2_pos p) + e)))),
           (fexp prec emax (Zpos (digits2_pos p) + e)).
    split; [|split; [|split]].
    + cbn [binary_normalize].
      exact (binary_round_exact prec emax true p e Hd He Hde Hemax).
    + cbn [cond_Zopp].
      change (Zneg p) with (- Zpos p)%Z.
      rewrite Hval. ring.
    + exact HTe.
    + exact HT.
Qed.
Lemma render_signed_value_f64 : forall m e p,
  Z.abs m = Zpos p ->
  float_dyadic_repr GTFloat64 m e = true ->
  exists s mc T,
    binary_normalize 53 1024 m e false = S754_finite s mc T
    /\ cond_Zopp s (Zpos mc) = (m * 2 ^ (e - T))%Z
    /\ (emin 53 1024 <= T)%Z /\ (T <= e)%Z.
Proof.
  intros m e p Habs Hrep.
  destruct (float_dyadic_repr_f64_premises m e p Hrep Habs) as [Hd [He Hde]].
  exact (render_signed_value_gen 53 1024 m e p Habs Hd He Hde ltac:(lia)).
Qed.

(** the [sf_render]↔[binary_normalize] identity — the LIVE render is uniformly the
    normalizer (zero included). *)
Lemma renorm_sf_of_dyadic : forall prec emax m e,
  renorm prec emax (sf_of_dyadic m e) = binary_normalize prec emax m e false.
Proof.
  intros prec emax [|p|p] e;
    cbn [sf_of_dyadic renorm cond_Zopp Z.opp binary_normalize]; reflexivity.
Qed.
(** ★ the LIVE render endpoint (gated): on the gate's window, [sf_render GTFloat64] of a
    NONZERO dyadic is a canonical finite whose SIGNED mantissa carries the value in
    difference form. *)
Theorem sf_render_signed_value_f64 : forall m e p,
  Z.abs m = Zpos p ->
  float_dyadic_repr GTFloat64 m e = true ->
  exists s mc T,
    sf_render GTFloat64 m e = Some (S754_finite s mc T)
    /\ cond_Zopp s (Zpos mc) = (m * 2 ^ (e - T))%Z
    /\ (emin 53 1024 <= T)%Z /\ (T <= e)%Z.
Proof.
  intros m e p Habs Hrep.
  destruct (render_signed_value_f64 m e p Habs Hrep)
    as [s [mc [T [Hbn [Hv [He1 He2]]]]]].
  exists s, mc, T.
  split; [|split; [|split]]; [| exact Hv | exact He1 | exact He2].
  unfold sf_render. rewrite renorm_sf_of_dyadic, Hbn. reflexivity.
Qed.

(** ---- rung 5c's VALUE-UNIQUENESS kit: [dy_norm] is determined by the VALUE — aligned
    value-equal pairs normalize identically (the assembly needs this to identify [SFadd]'s raw
    sum over CANONICAL operand mantissas with [dy_add]'s sum over the DYADIC pairs). *)
Lemma pos_odd_split_iter : forall j m,
  pos_odd_split (Pos.iter xO m j)
  = (fst (pos_odd_split m), (snd (pos_odd_split m) + Zpos j)%Z).
Proof.
  induction j using Pos.peano_ind; intro m.
  - cbn [Pos.iter pos_odd_split].
    destruct (pos_odd_split m) as [q k]. cbn [fst snd]. f_equal; lia.
  - rewrite Pos.iter_succ. cbn [pos_odd_split].
    rewrite IHj.
    destruct (pos_odd_split m) as [q k]. cbn [fst snd].
    f_equal; rewrite Pos2Z.inj_succ; lia.
Qed.
Lemma dy_norm_value_unique : forall m1 e1 m2 e2,
  (e1 <= e2)%Z ->
  m1 = (m2 * 2 ^ (e2 - e1))%Z ->
  dy_norm m1 e1 = dy_norm m2 e2.
Proof.
  intros m1 e1 m2 e2 He Hv.
  destruct (Z.sub e2 e1) as [|dp|dp] eqn:Ed.
  - rewrite Z.pow_0_r, Z.mul_1_r in Hv. subst m1.
    assert (e1 = e2) by lia. subst. reflexivity.
  - destruct m2 as [|p2|p2].
    + rewrite Z.mul_0_l in Hv. subst m1. reflexivity.
    + assert (Hm1 : m1 = Zpos (Pos.iter xO p2 dp))
        by (rewrite iter_xO_val; exact Hv).
      rewrite Hm1.
      pose proof (pos_odd_split_iter dp p2) as Hit.
      unfold dy_norm. cbv beta iota. rewrite Hit.
      destruct (pos_odd_split p2) as [q k]. cbn [fst snd]. cbv beta iota.
      f_equal; lia.
    + assert (Hm1 : m1 = Zneg (Pos.iter xO p2 dp)).
      { change (Zneg (Pos.iter xO p2 dp)) with (- Zpos (Pos.iter xO p2 dp))%Z.
        rewrite iter_xO_val, Hv.
        change (Zneg p2) with (- Zpos p2)%Z. ring. }
      rewrite Hm1.
      pose proof (pos_odd_split_iter dp p2) as Hit.
      unfold dy_norm. cbv beta iota. rewrite Hit.
      destruct (pos_odd_split p2) as [q k]. cbn [fst snd]. cbv beta iota.
      f_equal; lia.
  - exfalso.
    assert (Hlt : (e2 - e1 < 0)%Z) by (rewrite Ed; lia).
    lia.
Qed.



(** THE one sign-flip authority at the normalizer (rung 1's identity, both widths): the sign
    threads inertly through canonicalization ([binary_round_opp]); every sign-flip fact below
    consumes THIS lemma. *)
Lemma binary_normalize_opp : forall prec emax m e,
  m <> Z0 ->
  binary_normalize prec emax (- m)%Z e false
  = SFopp (binary_normalize prec emax m e false).
Proof.
  intros prec emax m e Hm.
  destruct m as [|p|p]; [congruence| |].
  - change (- Zpos p)%Z with (Zneg p). cbn [binary_normalize].
    exact (binary_round_opp prec emax false p e).
  - change (- Zneg p)%Z with (Zpos p). cbn [binary_normalize].
    exact (binary_round_opp prec emax true p e).
Qed.
(** ---- THE GENERAL dyadic↔SF AGREEMENT ARC (plans/dyadic-sf-agreement.md) — rung 1: NEGATION at
    binary64.  Unlike the [fsf_checked_*_agrees] theorems above (which state what acceptance of the
    per-node CONST-LAYER check means), this is checker-free: the dyadic fold's render IS the sign flip
    of the operand's render, proved once over the class through the ONE normalizer sign-flip
    authority ([binary_normalize_opp] above).  NO window premise; the [m <> 0] boundary is where CONSTANT
    and RUNTIME semantics split (constants have no signed zero) — the ZERO side is sealed at the
    CHECKER as [sf_const_neg]'s own case, ACCEPTED and denoting [+0]
    ([fsf_checked_neg_zero_total] + [negzero_const_runs]), never a caller obligation. *)
Theorem sf_render_neg_general_f64 : forall m e, m <> Z0 ->
  sf_render GTFloat64 (Z.opp m) e = option_map SFopp (sf_render GTFloat64 m e).
Proof.
  intros m e Hm.
  unfold sf_render. rewrite !renorm_sf_of_dyadic. cbn [option_map].
  f_equal.
  exact (binary_normalize_opp 53 1024 m e Hm).
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

(** ---- rung 5c FINAL — the [SFadd] finite-arm ASSEMBLY.  The uniform endgame: once the raw
    quantity's [dy_norm] equals the result pair, the wide determinism endpoint closes the
    normalization equality under the RESULT's gate window. *)
Lemma repr_window_split_f64 : forall m e,
  float_dyadic_repr GTFloat64 m e = true ->
  m = Z0 \/ exists q, Z.abs m = Zpos q
     /\ (Zpos (digits2_pos q) <= 53)%Z /\ (emin 53 1024 <= e)%Z
     /\ (Zpos (digits2_pos q) + e <= 1024)%Z.
Proof.
  intros m e H. destruct m as [|q|q]; [left; reflexivity| |];
    right; exists q; (split; [reflexivity|]);
    exact (float_dyadic_repr_f64_premises _ _ q H eq_refl).
Qed.
Lemma normalize_result_agrees_gen : forall prec emax raw ez mr er,
  dy_norm raw ez = (mr, er) ->
  (mr = Z0 \/ exists q, Z.abs mr = Zpos q
     /\ (Zpos (digits2_pos q) <= prec)%Z /\ (emin prec emax <= er)%Z
     /\ (Zpos (digits2_pos q) + er <= emax)%Z) ->
  (2 <= emax)%Z ->
  binary_normalize prec emax raw ez false = binary_normalize prec emax mr er false.
Proof.
  intros prec emax raw ez mr er Hn Hwin Hemax.
  apply (binary_normalize_wide_determined prec emax raw ez mr er false mr er).
  - exact Hn.
  - pose proof (dy_norm_idem raw ez) as Hi. rewrite Hn in Hi. cbn [fst snd] in Hi.
    exact Hi.
  - exact Hwin.
  - exact Hemax.
Qed.
Lemma normalize_result_agrees_f64 : forall raw ez mr er,
  dy_norm raw ez = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  binary_normalize 53 1024 raw ez false = binary_normalize 53 1024 mr er false.
Proof.
  intros raw ez mr er Hn Hrep.
  exact (normalize_result_agrees_gen 53 1024 raw ez mr er Hn
           (repr_window_split_f64 mr er Hrep) ltac:(lia)).
Qed.
Lemma cond_Zopp_mul : forall s a b, cond_Zopp s (a * b)%Z = (cond_Zopp s a * b)%Z.
Proof. intros [|] a b; cbn [cond_Zopp]; ring. Qed.
(** the zero rows: [SFadd] returns the OTHER operand; the fold side collapses to the other
    dyadic via [dy_norm_value_unique] *)
Lemma f64_add_zero_left_f64 : forall e1 m2 e2 mr er p2,
  Z.abs m2 = Zpos p2 ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_add (Z0, e1) (m2, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  f64_add (binary_normalize 53 1024 Z0 e1 false) (binary_normalize 53 1024 m2 e2 false)
  = binary_normalize 53 1024 mr er false.
Proof.
  intros e1 m2 e2 mr er p2 Ha H2 Hadd Hr.
  destruct (render_signed_value_f64 m2 e2 p2 Ha H2) as [s2 [mc2 [T2 [Hbn2 _]]]].
  rewrite Hbn2. cbn [binary_normalize].
  unfold f64_add, SFadd. cbv beta iota.
  assert (Hsum : dy_norm m2 e2 = (mr, er)).
  { cbn [dy_add] in Hadd.
    destruct (Z.leb e1 e2) eqn:Eb in Hadd.
    - apply Z.leb_le in Eb.
      rewrite Z.add_0_l, Z.shiftl_mul_pow2 in Hadd by lia.
      rewrite <- Hadd.
      symmetry.
      apply (dy_norm_value_unique (m2 * 2 ^ (e2 - e1)) e1 m2 e2 Eb eq_refl).
    - rewrite Z.shiftl_0_l, Z.add_0_l in Hadd. exact Hadd. }
  rewrite <- Hbn2.
  exact (normalize_result_agrees_f64 m2 e2 mr er Hsum Hr).
Qed.
Lemma f64_add_zero_right_f64 : forall m1 e1 e2 mr er p1,
  Z.abs m1 = Zpos p1 ->
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  dy_add (m1, e1) (Z0, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  f64_add (binary_normalize 53 1024 m1 e1 false) (binary_normalize 53 1024 Z0 e2 false)
  = binary_normalize 53 1024 mr er false.
Proof.
  intros m1 e1 e2 mr er p1 Ha H1 Hadd Hr.
  destruct (render_signed_value_f64 m1 e1 p1 Ha H1) as [s1 [mc1 [T1 [Hbn1 _]]]].
  rewrite Hbn1. cbn [binary_normalize].
  unfold f64_add, SFadd. cbv beta iota.
  assert (Hsum : dy_norm m1 e1 = (mr, er)).
  { cbn [dy_add] in Hadd.
    destruct (Z.leb e1 e2) eqn:Eb in Hadd.
    - rewrite Z.shiftl_0_l, Z.add_0_r in Hadd. exact Hadd.
    - apply Z.leb_gt in Eb.
      rewrite Z.add_0_r, Z.shiftl_mul_pow2 in Hadd by lia.
      rewrite <- Hadd.
      symmetry.
      apply (dy_norm_value_unique (m1 * 2 ^ (e1 - e2)) e2 m1 e1); [lia | reflexivity]. }
  rewrite <- Hbn1.
  exact (normalize_result_agrees_f64 m1 e1 mr er Hsum Hr).
Qed.
(** the finite×finite core: SIGNED difference-form value algebra identifies [SFadd]'s raw
    aligned sum with [dy_add]'s exact fold *)
Lemma f64_add_finite_agrees : forall m1 e1 m2 e2 mr er p1 p2,
  Z.abs m1 = Zpos p1 -> Z.abs m2 = Zpos p2 ->
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_add (m1, e1) (m2, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  f64_add (binary_normalize 53 1024 m1 e1 false) (binary_normalize 53 1024 m2 e2 false)
  = binary_normalize 53 1024 mr er false.
Proof.
  intros m1 e1 m2 e2 mr er p1 p2 Ha1 Ha2 H1 H2 Hadd Hr.
  destruct (render_signed_value_f64 m1 e1 p1 Ha1 H1)
    as [s1 [mc1 [T1 [Hbn1 [Hv1 [HmT1 HTe1]]]]]].
  destruct (render_signed_value_f64 m2 e2 p2 Ha2 H2)
    as [s2 [mc2 [T2 [Hbn2 [Hv2 [HmT2 HTe2]]]]]].
  rewrite Hbn1, Hbn2.
  unfold f64_add, SFadd. cbv beta iota zeta.
  assert (Hz1 : (Z.min T1 T2 <= T1)%Z) by lia.
  assert (Hz2 : (Z.min T1 T2 <= T2)%Z) by lia.
  assert (HA : cond_Zopp s1 (Zpos (fst (shl_align mc1 T1 (Z.min T1 T2))))
               = (m1 * 2 ^ (e1 - Z.min T1 T2))%Z).
  { rewrite (shl_align_fst_val mc1 T1 _ Hz1), cond_Zopp_mul, Hv1.
    rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
    f_equal. f_equal. lia. }
  assert (HB : cond_Zopp s2 (Zpos (fst (shl_align mc2 T2 (Z.min T1 T2))))
               = (m2 * 2 ^ (e2 - Z.min T1 T2))%Z).
  { rewrite (shl_align_fst_val mc2 T2 _ Hz2), cond_Zopp_mul, Hv2.
    rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
    f_equal. f_equal. lia. }
  change SpecFloat.cond_Zopp with cond_Zopp.
  rewrite HA, HB.
  cbn [dy_add] in Hadd.
  assert (Hsum : dy_norm (m1 * 2 ^ (e1 - Z.min T1 T2) + m2 * 2 ^ (e2 - Z.min T1 T2))%Z
                         (Z.min T1 T2) = (mr, er)).
  { destruct (Z.leb e1 e2) eqn:Eb in Hadd.
    - apply Z.leb_le in Eb.
      rewrite Z.shiftl_mul_pow2 in Hadd by lia.
      rewrite <- Hadd.
      apply (dy_norm_value_unique _ _ _ e1); [lia|].
      rewrite Z.mul_add_distr_r.
      rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
      replace ((e2 - e1) + (e1 - Z.min T1 T2))%Z with (e2 - Z.min T1 T2)%Z by lia.
      reflexivity.
    - apply Z.leb_gt in Eb.
      rewrite Z.shiftl_mul_pow2 in Hadd by lia.
      rewrite <- Hadd.
      apply (dy_norm_value_unique _ _ _ e2); [lia|].
      rewrite Z.mul_add_distr_r.
      rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
      replace ((e1 - e2) + (e2 - Z.min T1 T2))%Z with (e1 - Z.min T1 T2)%Z by lia.
      reflexivity. }
  exact (normalize_result_agrees_f64 _ _ mr er Hsum Hr).
Qed.
(** the ADD agreement core over all shapes (SUB transports through it — [sf_render_sub_agrees_f64]) *)
Lemma f64_add_normalize_agrees : forall m1 e1 m2 e2 mr er,
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_add (m1, e1) (m2, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  f64_add (binary_normalize 53 1024 m1 e1 false) (binary_normalize 53 1024 m2 e2 false)
  = binary_normalize 53 1024 mr er false.
Proof.
  intros m1 e1 m2 e2 mr er H1 H2 Hadd Hr.
  destruct m1 as [|p1|p1].
  - destruct m2 as [|p2|p2].
    + (* both zero *)
      cbn [binary_normalize]. unfold f64_add, SFadd. cbv beta iota.
      cbn [dy_add] in Hadd.
      destruct (Z.leb e1 e2) in Hadd;
        rewrite Z.shiftl_0_l in Hadd; cbn [Z.add dy_norm] in Hadd;
        injection Hadd as <- <-; reflexivity.
    + exact (f64_add_zero_left_f64 e1 (Zpos p2) e2 mr er p2 eq_refl H2 Hadd Hr).
    + exact (f64_add_zero_left_f64 e1 (Zneg p2) e2 mr er p2 eq_refl H2 Hadd Hr).
  - destruct m2 as [|p2|p2].
    + exact (f64_add_zero_right_f64 (Zpos p1) e1 e2 mr er p1 eq_refl H1 Hadd Hr).
    + exact (f64_add_finite_agrees (Zpos p1) e1 (Zpos p2) e2 mr er p1 p2
               eq_refl eq_refl H1 H2 Hadd Hr).
    + exact (f64_add_finite_agrees (Zpos p1) e1 (Zneg p2) e2 mr er p1 p2
               eq_refl eq_refl H1 H2 Hadd Hr).
  - destruct m2 as [|p2|p2].
    + exact (f64_add_zero_right_f64 (Zneg p1) e1 e2 mr er p1 eq_refl H1 Hadd Hr).
    + exact (f64_add_finite_agrees (Zneg p1) e1 (Zpos p2) e2 mr er p1 p2
               eq_refl eq_refl H1 H2 Hadd Hr).
    + exact (f64_add_finite_agrees (Zneg p1) e1 (Zneg p2) e2 mr er p1 p2
               eq_refl eq_refl H1 H2 Hadd Hr).
Qed.
(** ★ ADD at binary64 (gated): on the gate's windows — operands AND result — the LIVE render
    of [dy_add]'s exact fold IS the model's [f64_add] of the operands' renders, every case
    (zero rows, cancellation, the raw-wide carry class); SUB follows below. *)
Theorem sf_render_add_agrees_f64 : forall m1 e1 m2 e2 mr er,
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_add (m1, e1) (m2, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  exists v1 v2,
    sf_render GTFloat64 m1 e1 = Some v1
    /\ sf_render GTFloat64 m2 e2 = Some v2
    /\ sf_render GTFloat64 mr er = Some (f64_add v1 v2).
Proof.
  intros m1 e1 m2 e2 mr er H1 H2 Hadd Hr.
  unfold sf_render. rewrite !renorm_sf_of_dyadic.
  do 2 eexists.
  split; [reflexivity|]. split; [reflexivity|].
  f_equal. symmetry.
  exact (f64_add_normalize_agrees m1 e1 m2 e2 mr er H1 H2 Hadd Hr).
Qed.
(** the window is symmetric in the mantissa sign *)
Lemma float_dyadic_repr_opp : forall t m e,
  float_dyadic_repr t m e = true -> float_dyadic_repr t (- m)%Z e = true.
Proof.
  intros t m e H. unfold float_dyadic_repr in *.
  destruct t; try discriminate H; rewrite Z.abs_opp; exact H.
Qed.
Lemma bn_opp_f64 : forall m e, m <> Z0 ->
  binary_normalize 53 1024 (- m)%Z e false
  = SFopp (binary_normalize 53 1024 m e false).
Proof. intros m e Hm. exact (binary_normalize_opp 53 1024 m e Hm). Qed.
(** ★ SUB at binary64 (gated) — rung 5 CLOSED (ADD + SUB): [dy_sub] is [dy_add] of the
    negation and [SFsub] is [SFadd] of the sign-flip ([SFsub_as_add_opp]), so the ADD closure
    transports; the [-0] second operand of a zero subtrahend is absorbed by [SFadd]'s
    sign-blind zero rows. *)
Theorem sf_render_sub_agrees_f64 : forall m1 e1 m2 e2 mr er,
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_sub (m1, e1) (m2, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  exists v1 v2,
    sf_render GTFloat64 m1 e1 = Some v1
    /\ sf_render GTFloat64 m2 e2 = Some v2
    /\ sf_render GTFloat64 mr er = Some (f64_sub v1 v2).
Proof.
  intros m1 e1 m2 e2 mr er H1 H2 Hsub Hr.
  unfold dy_sub in Hsub. cbn [dy_neg] in Hsub.
  unfold sf_render. rewrite !renorm_sf_of_dyadic.
  do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
  f_equal.
  unfold f64_sub. rewrite SFsub_as_add_opp.
  destruct m2 as [|p2|p2].
  - (* zero subtrahend: SFopp (+0) = -0, absorbed by the sign-blind rows *)
    cbn [Z.opp] in Hsub.
    change (binary_normalize 53 1024 0 e2 false) with (S754_zero false).
    cbn [SFopp].
    destruct m1 as [|p1|p1].
    + change (binary_normalize 53 1024 0 e1 false) with (S754_zero false).
      cbn [dy_add] in Hsub.
      destruct (Z.leb e1 e2) in Hsub;
        rewrite Z.shiftl_0_l in Hsub; cbn [Z.add dy_norm] in Hsub;
        injection Hsub as <- <-; reflexivity.
    + destruct (render_signed_value_f64 (Zpos p1) e1 p1 eq_refl H1)
        as [s1 [mc1 [T1 [Hbn1 _]]]].
      rewrite Hbn1. cbn [SFadd].
      assert (Hsum : dy_norm (Zpos p1) e1 = (mr, er)).
      { cbn [dy_add] in Hsub.
        destruct (Z.leb e1 e2) eqn:Eb in Hsub.
        - rewrite Z.shiftl_0_l, Z.add_0_r in Hsub. exact Hsub.
        - apply Z.leb_gt in Eb.
          rewrite Z.add_0_r, Z.shiftl_mul_pow2 in Hsub by lia.
          rewrite <- Hsub.
          symmetry.
          apply (dy_norm_value_unique (Zpos p1 * 2 ^ (e1 - e2)) e2 (Zpos p1) e1);
            [lia | reflexivity]. }
      rewrite <- Hbn1.
      symmetry.
      exact (normalize_result_agrees_f64 (Zpos p1) e1 mr er Hsum Hr).
    + destruct (render_signed_value_f64 (Zneg p1) e1 p1 eq_refl H1)
        as [s1 [mc1 [T1 [Hbn1 _]]]].
      rewrite Hbn1. cbn [SFadd].
      assert (Hsum : dy_norm (Zneg p1) e1 = (mr, er)).
      { cbn [dy_add] in Hsub.
        destruct (Z.leb e1 e2) eqn:Eb in Hsub.
        - rewrite Z.shiftl_0_l, Z.add_0_r in Hsub. exact Hsub.
        - apply Z.leb_gt in Eb.
          rewrite Z.add_0_r, Z.shiftl_mul_pow2 in Hsub by lia.
          rewrite <- Hsub.
          symmetry.
          apply (dy_norm_value_unique (Zneg p1 * 2 ^ (e1 - e2)) e2 (Zneg p1) e1);
            [lia | reflexivity]. }
      rewrite <- Hbn1.
      symmetry.
      exact (normalize_result_agrees_f64 (Zneg p1) e1 mr er Hsum Hr).
  - rewrite <- (bn_opp_f64 (Zpos p2) e2 ltac:(discriminate)).
    symmetry.
    exact (f64_add_normalize_agrees m1 e1 (- Zpos p2)%Z e2 mr er H1
             (float_dyadic_repr_opp _ _ _ H2) Hsub Hr).
  - rewrite <- (bn_opp_f64 (Zneg p2) e2 ltac:(discriminate)).
    symmetry.
    exact (f64_add_normalize_agrees m1 e1 (- Zneg p2)%Z e2 mr er H1
             (float_dyadic_repr_opp _ _ _ H2) Hsub Hr).
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

(** ---- rung 6 — MUL at binary64.  [SFmul]'s finite arm is [binary_round_aux] on the RAW
    product of the CANONICAL mantissas at the SUM exponent; for canonical operand renders
    the [fexp] target never sits below that exponent ([digits2_pos_mul_lower] + the window
    bounds), so the arm IS [binary_round] ([binary_round_aux_of_round]) and the wide-bridge
    endgame ([normalize_result_agrees_f64]) applies.  ⚠ the ENDPOINT is stated over the
    CONSTANT-op layer ([sf_pos_zero] of [f64_mul]): IEEE gives [(+0) * (negative) = -0], a
    RUNTIME zero sign Go's exact-rational constant fold never produces — the raw-op form of
    the ADD/SUB endpoints is FALSE on MUL's zero rows. *)
Lemma cond_Zopp_xorb_mul : forall s1 s2 a b,
  cond_Zopp (xorb s1 s2) (a * b)%Z = (cond_Zopp s1 a * cond_Zopp s2 b)%Z.
Proof. intros [|] [|] a b; cbn [xorb cond_Zopp]; ring. Qed.
Lemma dy_norm_nonzero : forall m e mr er,
  m <> Z0 -> dy_norm m e = (mr, er) -> mr <> Z0.
Proof.
  intros m e mr er Hm Hn.
  destruct m as [|p|p]; [congruence| |];
    cbn [dy_norm] in Hn; destruct (pos_odd_split p) as [q k];
    injection Hn as <- _; discriminate.
Qed.
Lemma binary_normalize_of_round : forall prec emax s q e,
  binary_round prec emax s q e
  = binary_normalize prec emax (cond_Zopp s (Zpos q)) e false.
Proof. intros prec emax [|] q e; reflexivity. Qed.
(** the render, CANONICALLY: [render_signed_value_f64]'s witness plus the two
    digit/exponent facts the MUL target premise needs — digits+exponent is shift-invariant
    ([shl_align_digits]) and the exponent IS the [fexp] target. *)
Lemma render_canonical_gen : forall prec emax m e p,
  Z.abs m = Zpos p ->
  (Zpos (digits2_pos p) <= prec)%Z ->
  (emin prec emax <= e)%Z ->
  (Zpos (digits2_pos p) + e <= emax)%Z ->
  (2 <= emax)%Z ->
  exists s mc T,
    binary_normalize prec emax m e false = S754_finite s mc T
    /\ cond_Zopp s (Zpos mc) = (m * 2 ^ (e - T))%Z
    /\ (Zpos (digits2_pos mc) + T = Zpos (digits2_pos p) + e)%Z
    /\ T = fexp prec emax (Zpos (digits2_pos p) + e)
    /\ (T <= e)%Z.
Proof.
  intros prec emax m e p Habs Hd He Hde Hemax.
  assert (HT : (fexp prec emax (Zpos (digits2_pos p) + e) <= e)%Z)
    by (unfold fexp, emin in *; lia).
  pose proof (shl_align_fst_val p e _ HT) as Hval.
  pose proof (shl_align_digits p e _ HT) as Hdig.
  pose proof (shl_align_snd p e _ HT) as Hsnd.
  destruct m as [|p'|p']; cbn [Z.abs] in Habs; try discriminate Habs;
    injection Habs as ->.
  - exists false, (fst (shl_align p e (fexp prec emax (Zpos (digits2_pos p) + e)))),
           (fexp prec emax (Zpos (digits2_pos p) + e)).
    split; [|split; [|split; [|split]]].
    + cbn [binary_normalize].
      exact (binary_round_exact prec emax false p e Hd He Hde Hemax).
    + cbn [cond_Zopp]. exact Hval.
    + lia.
    + reflexivity.
    + exact HT.
  - exists true, (fst (shl_align p e (fexp prec emax (Zpos (digits2_pos p) + e)))),
           (fexp prec emax (Zpos (digits2_pos p) + e)).
    split; [|split; [|split; [|split]]].
    + cbn [binary_normalize].
      exact (binary_round_exact prec emax true p e Hd He Hde Hemax).
    + cbn [cond_Zopp].
      change (Zneg p) with (- Zpos p)%Z.
      rewrite Hval. ring.
    + lia.
    + reflexivity.
    + exact HT.
Qed.
Lemma render_canonical_f64 : forall m e p,
  Z.abs m = Zpos p ->
  float_dyadic_repr GTFloat64 m e = true ->
  exists s mc T,
    binary_normalize 53 1024 m e false = S754_finite s mc T
    /\ cond_Zopp s (Zpos mc) = (m * 2 ^ (e - T))%Z
    /\ (Zpos (digits2_pos mc) + T = Zpos (digits2_pos p) + e)%Z
    /\ T = fexp 53 1024 (Zpos (digits2_pos p) + e)
    /\ (T <= e)%Z.
Proof.
  intros m e p Habs Hrep.
  destruct (float_dyadic_repr_f64_premises m e p Hrep Habs) as [Hd [He Hde]].
  exact (render_canonical_gen 53 1024 m e p Habs Hd He Hde ltac:(lia)).
Qed.
(** the finite×finite MUL core: both renders characterized canonically, the raw-product arm
    rewritten to [binary_round], the product value algebra aligned to the fold via
    [dy_norm_value_unique], the wide-determinism endgame closing it. *)
Lemma f64_mul_normalize_agrees : forall m1 e1 m2 e2 mr er p1 p2,
  Z.abs m1 = Zpos p1 -> Z.abs m2 = Zpos p2 ->
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_mul (m1, e1) (m2, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  f64_mul (binary_normalize 53 1024 m1 e1 false) (binary_normalize 53 1024 m2 e2 false)
  = binary_normalize 53 1024 mr er false.
Proof.
  intros m1 e1 m2 e2 mr er p1 p2 Ha1 Ha2 H1 H2 Hmul Hr.
  destruct (float_dyadic_repr_f64_premises m1 e1 p1 H1 Ha1) as [Hd1 [He1 Hde1]].
  destruct (float_dyadic_repr_f64_premises m2 e2 p2 H2 Ha2) as [Hd2 [He2 Hde2]].
  destruct (render_canonical_f64 m1 e1 p1 Ha1 H1)
    as [s1 [mc1 [T1 [Hbn1 [Hv1 [Hdig1 [Hfx1 HT1e]]]]]]].
  destruct (render_canonical_f64 m2 e2 p2 Ha2 H2)
    as [s2 [mc2 [T2 [Hbn2 [Hv2 [Hdig2 [Hfx2 HT2e]]]]]]].
  pose proof (digits2_pos_mul_lower mc1 mc2) as Hml.
  rewrite Hbn1, Hbn2.
  unfold f64_mul, SFmul. cbv beta iota.
  rewrite binary_round_aux_of_round by (unfold fexp, emin in *; lia).
  rewrite binary_normalize_of_round.
  apply normalize_result_agrees_f64; [| exact Hr].
  cbn [dy_mul] in Hmul. rewrite <- Hmul.
  apply dy_norm_value_unique; [lia|].
  rewrite Pos2Z.inj_mul, cond_Zopp_xorb_mul, Hv1, Hv2.
  replace ((e1 + e2) - (T1 + T2))%Z with ((e1 - T1) + (e2 - T2))%Z by lia.
  rewrite Z.pow_add_r by lia.
  ring.
Qed.
(** ★ MUL at binary64 (gated, CONST-layer): on the gate's windows — operands AND result —
    the LIVE render of [dy_mul]'s exact fold IS the CONSTANT-op layer's product
    ([sf_pos_zero] of [f64_mul]) of the operands' renders, every shape.  The erasure is
    exactly the checker's own op ([sf_const_binop]'s [BMul] row): a zero factor times a
    NEGATIVE operand is IEEE [-0] at the raw op, a runtime-only zero sign. *)
Theorem sf_render_mul_agrees_f64 : forall m1 e1 m2 e2 mr er,
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_mul (m1, e1) (m2, e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  exists v1 v2,
    sf_render GTFloat64 m1 e1 = Some v1
    /\ sf_render GTFloat64 m2 e2 = Some v2
    /\ sf_render GTFloat64 mr er = Some (sf_pos_zero (f64_mul v1 v2)).
Proof.
  intros m1 e1 m2 e2 mr er H1 H2 Hmul Hr.
  unfold sf_render. rewrite !renorm_sf_of_dyadic.
  do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
  f_equal.
  destruct m1 as [|q1|q1].
  - (* 0 * x : the fold is (0,0); the raw product is a signed zero, erased *)
    cbn [dy_mul Z.mul dy_norm] in Hmul. injection Hmul as <- <-.
    change (binary_normalize 53 1024 0 e1 false) with (S754_zero false).
    change (binary_normalize 53 1024 0 0 false) with (S754_zero false).
    destruct m2 as [|q2|q2].
    + change (binary_normalize 53 1024 0 e2 false) with (S754_zero false). reflexivity.
    + destruct (render_signed_value_f64 (Zpos q2) e2 q2 eq_refl H2)
        as [s2 [mc2 [T2 [Hbn2 _]]]].
      rewrite Hbn2. reflexivity.
    + destruct (render_signed_value_f64 (Zneg q2) e2 q2 eq_refl H2)
        as [s2 [mc2 [T2 [Hbn2 _]]]].
      rewrite Hbn2. reflexivity.
  - destruct m2 as [|q2|q2].
    + (* pos * 0 *)
      cbn [dy_mul Z.mul dy_norm] in Hmul. injection Hmul as <- <-.
      change (binary_normalize 53 1024 0 e2 false) with (S754_zero false).
      change (binary_normalize 53 1024 0 0 false) with (S754_zero false).
      destruct (render_signed_value_f64 (Zpos q1) e1 q1 eq_refl H1)
        as [s1 [mc1 [T1 [Hbn1 _]]]].
      rewrite Hbn1. destruct s1; reflexivity.
    + cbn [dy_mul Z.mul] in Hmul.
      pose proof (f64_mul_normalize_agrees (Zpos q1) e1 (Zpos q2) e2 mr er q1 q2
                    eq_refl eq_refl H1 H2 Hmul Hr) as Hcore.
      rewrite Hcore.
      destruct mr as [|pr|pr].
      * exfalso. eapply dy_norm_nonzero in Hmul; [exact (Hmul eq_refl) | discriminate].
      * destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
    + cbn [dy_mul Z.mul] in Hmul.
      pose proof (f64_mul_normalize_agrees (Zpos q1) e1 (Zneg q2) e2 mr er q1 q2
                    eq_refl eq_refl H1 H2 Hmul Hr) as Hcore.
      rewrite Hcore.
      destruct mr as [|pr|pr].
      * exfalso. eapply dy_norm_nonzero in Hmul; [exact (Hmul eq_refl) | discriminate].
      * destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
  - destruct m2 as [|q2|q2].
    + (* neg * 0 *)
      cbn [dy_mul Z.mul dy_norm] in Hmul. injection Hmul as <- <-.
      change (binary_normalize 53 1024 0 e2 false) with (S754_zero false).
      change (binary_normalize 53 1024 0 0 false) with (S754_zero false).
      destruct (render_signed_value_f64 (Zneg q1) e1 q1 eq_refl H1)
        as [s1 [mc1 [T1 [Hbn1 _]]]].
      rewrite Hbn1. destruct s1; reflexivity.
    + cbn [dy_mul Z.mul] in Hmul.
      pose proof (f64_mul_normalize_agrees (Zneg q1) e1 (Zpos q2) e2 mr er q1 q2
                    eq_refl eq_refl H1 H2 Hmul Hr) as Hcore.
      rewrite Hcore.
      destruct mr as [|pr|pr].
      * exfalso. eapply dy_norm_nonzero in Hmul; [exact (Hmul eq_refl) | discriminate].
      * destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
    + cbn [dy_mul Z.mul] in Hmul.
      pose proof (f64_mul_normalize_agrees (Zneg q1) e1 (Zneg q2) e2 mr er q1 q2
                    eq_refl eq_refl H1 H2 Hmul Hr) as Hcore.
      rewrite Hcore.
      destruct mr as [|pr|pr].
      * exfalso. eapply dy_norm_nonzero in Hmul; [exact (Hmul eq_refl) | discriminate].
      * destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
Qed.

(** ---- rung 6 — exact DIV at binary64.  [SFdiv_core_binary] left-shifts the dividend's
    canonical mantissa to [s = (T1-T2) - e'] (with [e'] the min of the quotient's [fexp]
    target and [T1-T2]) and divides with [Z.div_eucl], recording the remainder as the
    rounding LOCATION.  On the fold-accepted class ([Z.rem m1 m2 = 0]) the division is
    EXACT: the divisibility transports through the canonical shifts (the 2-power margin is
    [e' <= er], from the fexp arm of the min), the location is [loc_Exact], and the raw
    quotient — which is exactly the RESULT's mantissa shifted up by [er - e'] — reduces
    through [binary_round_aux_of_round] to the same wide endgame as ADD/MUL.  The endpoint
    is CONST-layer, like MUL: a zero dividend against a negative divisor is IEEE [-0]. *)
Lemma abs_cond_Zopp : forall s x, Z.abs (cond_Zopp s x) = Z.abs x.
Proof. intros [|] x; cbn [cond_Zopp]; [apply Z.abs_opp | reflexivity]. Qed.
Lemma xorb_xorb_cancel : forall s1 s2, xorb (xorb s1 s2) s2 = s1.
Proof. intros [|] [|]; reflexivity. Qed.
(** [dy_norm]'s VALUE decomposition (nonzero side): the normal form carries the value at a
    higher-or-equal exponent. *)
Lemma dy_norm_value : forall m e mr er,
  m <> Z0 ->
  dy_norm m e = (mr, er) ->
  (e <= er)%Z /\ m = (mr * 2 ^ (er - e))%Z.
Proof.
  intros m e mr er Hm H.
  destruct m as [|p|p]; [congruence| |]; cbn [dy_norm] in H;
    destruct (pos_odd_split p) as [q k] eqn:E;
    destruct (pos_odd_split_val p q k E) as [Hk Hv];
    injection H as <- <-;
    (split; [lia|]);
    replace (e + k - e)%Z with k by lia.
  - exact Hv.
  - change (Zneg p) with (- Zpos p)%Z. change (Zneg q) with (- Zpos q)%Z.
    rewrite Hv. ring.
Qed.
(** the finite×finite DIV core, over the fold's SPLIT pieces (the endpoint destructures
    [dy_div] once and feeds the divisibility + normalized quotient here). *)
Lemma f64_div_normalize_agrees : forall m1 e1 m2 e2 mr er p1 p2 pr,
  Z.abs m1 = Zpos p1 -> Z.abs m2 = Zpos p2 -> Z.abs mr = Zpos pr ->
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  Z.rem m1 m2 = 0%Z ->
  dy_norm (Z.quot m1 m2) (e1 - e2) = (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  f64_div (binary_normalize 53 1024 m1 e1 false) (binary_normalize 53 1024 m2 e2 false)
  = binary_normalize 53 1024 mr er false.
Proof.
  intros m1 e1 m2 e2 mr er p1 p2 pr Ha1 Ha2 Hamr H1 H2 Hrem Hnorm Hr.
  destruct (float_dyadic_repr_f64_premises m1 e1 p1 H1 Ha1) as [Hd1 [He1 Hde1]].
  destruct (float_dyadic_repr_f64_premises m2 e2 p2 H2 Ha2) as [Hd2 [He2 Hde2]].
  destruct (float_dyadic_repr_f64_premises mr er pr Hr Hamr) as [Hdr [Herm Hder]].
  destruct (render_canonical_f64 m1 e1 p1 Ha1 H1)
    as [s1 [mc1 [T1 [Hbn1 [Hv1 [Hdig1 [Hfx1 HT1e]]]]]]].
  destruct (render_canonical_f64 m2 e2 p2 Ha2 H2)
    as [s2 [mc2 [T2 [Hbn2 [Hv2 [Hdig2 [Hfx2 HT2e]]]]]]].
  assert (Hm2nz : m2 <> Z0) by lia.
  assert (Hm1q : m1 = (m2 * Z.quot m1 m2)%Z).
  { pose proof (Z.quot_rem m1 m2 Hm2nz) as Hqr. lia. }
  set (q0 := Z.quot m1 m2) in *.
  assert (Hq0nz : q0 <> Z0) by (intro E0; rewrite E0, Z.mul_0_r in Hm1q; lia).
  destruct (dy_norm_value q0 (e1 - e2) mr er Hq0nz Hnorm) as [Her Hq0].
  (* the renders' ABS value forms *)
  assert (Habs1 : Zpos mc1 = (Z.abs m1 * 2 ^ (e1 - T1))%Z).
  { pose proof (f_equal Z.abs Hv1) as HA.
    rewrite abs_cond_Zopp, Z.abs_mul,
      (Z.abs_eq (2 ^ (e1 - T1))) in HA by (apply Z.pow_nonneg; lia).
    cbn [Z.abs] in HA. exact HA. }
  assert (Habs2 : Zpos mc2 = (Z.abs m2 * 2 ^ (e2 - T2))%Z).
  { pose proof (f_equal Z.abs Hv2) as HA.
    rewrite abs_cond_Zopp, Z.abs_mul,
      (Z.abs_eq (2 ^ (e2 - T2))) in HA by (apply Z.pow_nonneg; lia).
    cbn [Z.abs] in HA. exact HA. }
  (* |m1| = |m2·mr|·2^(er-(e1-e2)) — digit bookkeeping through the fold *)
  assert (Hp1eq : Zpos p1 = (Zpos (Pos.mul p2 pr) * 2 ^ (er - (e1 - e2)))%Z).
  { rewrite <- Ha1, Hm1q, Hq0, !Z.abs_mul, Ha2, Hamr.
    rewrite (Z.abs_eq (2 ^ (er - (e1 - e2)))) by (apply Z.pow_nonneg; lia).
    rewrite Pos2Z.inj_mul. ring. }
  assert (Hdp1 : Zpos (digits2_pos p1)
                 = (Zpos (digits2_pos (Pos.mul p2 pr)) + (er - (e1 - e2)))%Z)
    by (apply digits2_pos_shift; [lia | exact Hp1eq]).
  pose proof (digits2_pos_mul_upper p2 pr) as Hmu.
  set (E' := Z.min
        (fexp 53 1024
           (Zpos (digits2_pos mc1) + T1 - (Zpos (digits2_pos mc2) + T2)))
        (T1 - T2)).
  assert (Hfa : (Zpos (digits2_pos mc1) + T1 - (Zpos (digits2_pos mc2) + T2))%Z
                = ((Zpos (digits2_pos p1) + e1) - (Zpos (digits2_pos p2) + e2))%Z) by lia.
  assert (HNle : ((Zpos (digits2_pos p1) + e1) - (Zpos (digits2_pos p2) + e2)
                  <= Zpos (digits2_pos pr) + er)%Z) by lia.
  assert (HE'fx : (E' <= fexp 53 1024 (Zpos (digits2_pos pr) + er))%Z).
  { unfold E'. rewrite Hfa. unfold fexp, emin in *. lia. }
  assert (HE'er : (E' <= er)%Z) by (unfold fexp, emin in HE'fx, Herm; lia).
  assert (HsE : (0 <= T1 - T2 - E')%Z) by (unfold E'; lia).
  (* the exact scaled division *)
  assert (Hm' : (Zpos mc1 * 2 ^ (T1 - T2 - E'))%Z
              = (Zpos mc2 * (Zpos pr * 2 ^ (er - E')))%Z).
  { rewrite Habs1, Habs2, Ha1, Ha2, Hp1eq, Pos2Z.inj_mul.
    assert (Hpw : (2 ^ (er - (e1 - e2)) * 2 ^ (e1 - T1) * 2 ^ (T1 - T2 - E')
                   = 2 ^ (e2 - T2) * 2 ^ (er - E'))%Z).
    { rewrite <- !Z.pow_add_r by lia. f_equal. lia. }
    transitivity ((Zpos p2 * Zpos pr)
                  * (2 ^ (er - (e1 - e2)) * 2 ^ (e1 - T1) * 2 ^ (T1 - T2 - E')))%Z;
      [ring|].
    rewrite Hpw. ring. }
  assert (Hdvd : (Zpos mc2 | Zpos mc1 * 2 ^ (T1 - T2 - E'))%Z)
    by (exists (Zpos pr * 2 ^ (er - E'))%Z; rewrite Hm'; ring).
  (* compute the core triple *)
  assert (Hcore : SFdiv_core_binary 53 1024 (Zpos mc1) T1 (Zpos mc2) T2
                = ((Zpos pr * 2 ^ (er - E'))%Z, E', loc_Exact)).
  { unfold SFdiv_core_binary. cbn [Zdigits2]. cbv zeta.
    fold E'.
    destruct (T1 - T2 - E')%Z as [|sp|sp] eqn:Es.
    - (* no shift: 2^0 *)
      rewrite Z.pow_0_r, Z.mul_1_r in Hm' , Hdvd.
      rewrite (div_eucl_exact (Zpos mc1) (Zpos mc2) ltac:(lia) Hdvd).
      cbv beta iota.
      rewrite new_location_exact.
      rewrite Hm', (Z.mul_comm (Zpos mc2)), Z.div_mul by lia.
      reflexivity.
    - rewrite (Z.shiftl_mul_pow2 (Zpos mc1) (Zpos sp)) by lia.
      rewrite <- Es in *.
      rewrite (div_eucl_exact _ (Zpos mc2) ltac:(lia) Hdvd).
      cbv beta iota.
      rewrite new_location_exact.
      rewrite Hm', (Z.mul_comm (Zpos mc2)), Z.div_mul by lia.
      reflexivity.
    - exfalso. lia.
  }
  (* the model arm *)
  rewrite Hbn1, Hbn2.
  unfold f64_div. cbn [SFdiv].
  rewrite Hcore. cbv beta iota.
  (* the raw quotient is positive: name its mantissa *)
  assert (HQpos : (0 < Zpos pr * 2 ^ (er - E'))%Z).
  { assert (0 < 2 ^ (er - E'))%Z by (apply Z.pow_pos_nonneg; lia). nia. }
  destruct (Zpos pr * 2 ^ (er - E'))%Z as [|qp|qp] eqn:HQ; [lia| |lia].
  assert (Hdq : Zpos (digits2_pos qp) = (Zpos (digits2_pos pr) + (er - E'))%Z)
    by (apply digits2_pos_shift; [lia | symmetry; exact HQ]).
  rewrite binary_round_aux_of_round
    by (rewrite Hdq;
        replace (Zpos (digits2_pos pr) + (er - E') + E')%Z
          with (Zpos (digits2_pos pr) + er)%Z by lia;
        exact HE'fx).
  rewrite binary_normalize_of_round.
  apply normalize_result_agrees_f64; [| exact Hr].
  (* the SIGNED quotient value, by cancelation — no sign case analysis *)
  assert (Hxx : xorb (xorb s1 s2) s2 = s1) by (destruct s1, s2; reflexivity).
  assert (HXmul : (cond_Zopp (xorb s1 s2) (Zpos qp) * (m2 * 2 ^ (e2 - T2)))%Z
                = ((mr * 2 ^ (er - E')) * (m2 * 2 ^ (e2 - T2)))%Z).
  { rewrite <- Hv2.
    rewrite <- cond_Zopp_xorb_mul, Hxx.
    assert (HQmc : (Zpos qp * Zpos mc2)%Z = (Zpos mc1 * 2 ^ (T1 - T2 - E'))%Z)
      by (rewrite <- HQ, Hm'; first [apply Z.mul_comm | ring | lia | nia]).
    rewrite HQmc.
    rewrite cond_Zopp_mul, Hv1, Hv2.
    rewrite Hm1q, Hq0.
    assert (Hpw : (2 ^ (er - (e1 - e2)) * 2 ^ (e1 - T1) * 2 ^ (T1 - T2 - E')
                   = 2 ^ (er - E') * 2 ^ (e2 - T2))%Z).
    { rewrite <- !Z.pow_add_r by lia. f_equal. lia. }
    transitivity ((m2 * mr)
                  * (2 ^ (er - (e1 - e2)) * 2 ^ (e1 - T1) * 2 ^ (T1 - T2 - E')))%Z;
      [ring|].
    rewrite Hpw. ring. }
  assert (Hnzf : (m2 * 2 ^ (e2 - T2))%Z <> 0%Z).
  { assert (0 < 2 ^ (e2 - T2))%Z by (apply Z.pow_pos_nonneg; lia).
    intro F. apply Z.mul_eq_0 in F. destruct F; lia. }
  pose proof (proj1 (Z.mul_cancel_r _ _ _ Hnzf) HXmul) as HX.
  rewrite HX.
  rewrite (dy_norm_value_unique (mr * 2 ^ (er - E'))%Z E' mr er HE'er eq_refl).
  pose proof (dy_norm_idem q0 (e1 - e2)) as Hidem.
  rewrite Hnorm in Hidem. cbn [fst snd] in Hidem.
  exact Hidem.
Qed.
(** ★ exact DIV at binary64 (gated, CONST-layer) — rung 6 CLOSED (MUL + exact DIV): on the
    gate's windows, whenever [dy_div] ACCEPTS (the divisor divides exactly; a zero divisor
    is [None]), the LIVE render of the exact quotient IS the CONSTANT-op layer's division
    ([sf_pos_zero] of [f64_div] — [sf_const_binop]'s [BDiv] row) of the operands' renders. *)
Theorem sf_render_div_agrees_f64 : forall m1 e1 m2 e2 mr er,
  float_dyadic_repr GTFloat64 m1 e1 = true ->
  float_dyadic_repr GTFloat64 m2 e2 = true ->
  dy_div (m1, e1) (m2, e2) = Some (mr, er) ->
  float_dyadic_repr GTFloat64 mr er = true ->
  exists v1 v2,
    sf_render GTFloat64 m1 e1 = Some v1
    /\ sf_render GTFloat64 m2 e2 = Some v2
    /\ sf_render GTFloat64 mr er = Some (sf_pos_zero (f64_div v1 v2)).
Proof.
  intros m1 e1 m2 e2 mr er H1 H2 Hdiv Hr.
  unfold sf_render. rewrite !renorm_sf_of_dyadic.
  do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
  f_equal.
  destruct m2 as [|q2|q2].
  - (* zero divisor: dy_div is None *)
    cbn [dy_div Z.eqb] in Hdiv. discriminate Hdiv.
  - destruct m1 as [|q1|q1].
    + (* 0 / pos *)
      cbn [dy_div Z.eqb Z.rem Z.quotrem Z.quot dy_norm] in Hdiv.
      injection Hdiv as <- <-.
      change (binary_normalize 53 1024 0 e1 false) with (S754_zero false).
      change (binary_normalize 53 1024 0 0 false) with (S754_zero false).
      destruct (render_signed_value_f64 (Zpos q2) e2 q2 eq_refl H2)
        as [s2 [mc2 [T2 [Hbn2 _]]]].
      rewrite Hbn2. reflexivity.
    + (* pos / pos *)
      cbn [dy_div Z.eqb] in Hdiv.
      destruct (Z.eqb (Z.rem (Zpos q1) (Zpos q2)) 0) eqn:Hrem; [|discriminate Hdiv].
      apply Z.eqb_eq in Hrem. injection Hdiv as Hnorm.
      assert (Hqnz : Z.quot (Zpos q1) (Zpos q2) <> Z0).
      { pose proof (Z.quot_rem (Zpos q1) (Zpos q2) ltac:(discriminate)) as Hqr.
        intro F. rewrite F, Z.mul_0_r in Hqr. lia. }
      destruct mr as [|pr|pr];
        [exact (False_ind _ (dy_norm_nonzero _ _ _ _ Hqnz Hnorm eq_refl))| |].
      * rewrite (f64_div_normalize_agrees (Zpos q1) e1 (Zpos q2) e2 (Zpos pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * rewrite (f64_div_normalize_agrees (Zpos q1) e1 (Zpos q2) e2 (Zneg pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
    + (* neg / pos *)
      cbn [dy_div Z.eqb] in Hdiv.
      destruct (Z.eqb (Z.rem (Zneg q1) (Zpos q2)) 0) eqn:Hrem; [|discriminate Hdiv].
      apply Z.eqb_eq in Hrem. injection Hdiv as Hnorm.
      assert (Hqnz : Z.quot (Zneg q1) (Zpos q2) <> Z0).
      { pose proof (Z.quot_rem (Zneg q1) (Zpos q2) ltac:(discriminate)) as Hqr.
        intro F. rewrite F, Z.mul_0_r in Hqr. lia. }
      destruct mr as [|pr|pr];
        [exact (False_ind _ (dy_norm_nonzero _ _ _ _ Hqnz Hnorm eq_refl))| |].
      * rewrite (f64_div_normalize_agrees (Zneg q1) e1 (Zpos q2) e2 (Zpos pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * rewrite (f64_div_normalize_agrees (Zneg q1) e1 (Zpos q2) e2 (Zneg pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
  - destruct m1 as [|q1|q1].
    + (* 0 / neg *)
      cbn [dy_div Z.eqb Z.rem Z.quotrem Z.quot dy_norm] in Hdiv.
      injection Hdiv as <- <-.
      change (binary_normalize 53 1024 0 e1 false) with (S754_zero false).
      change (binary_normalize 53 1024 0 0 false) with (S754_zero false).
      destruct (render_signed_value_f64 (Zneg q2) e2 q2 eq_refl H2)
        as [s2 [mc2 [T2 [Hbn2 _]]]].
      rewrite Hbn2. reflexivity.
    + (* pos / neg *)
      cbn [dy_div Z.eqb] in Hdiv.
      destruct (Z.eqb (Z.rem (Zpos q1) (Zneg q2)) 0) eqn:Hrem; [|discriminate Hdiv].
      apply Z.eqb_eq in Hrem. injection Hdiv as Hnorm.
      assert (Hqnz : Z.quot (Zpos q1) (Zneg q2) <> Z0).
      { pose proof (Z.quot_rem (Zpos q1) (Zneg q2) ltac:(discriminate)) as Hqr.
        intro F. rewrite F, Z.mul_0_r in Hqr. lia. }
      destruct mr as [|pr|pr];
        [exact (False_ind _ (dy_norm_nonzero _ _ _ _ Hqnz Hnorm eq_refl))| |].
      * rewrite (f64_div_normalize_agrees (Zpos q1) e1 (Zneg q2) e2 (Zpos pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * rewrite (f64_div_normalize_agrees (Zpos q1) e1 (Zneg q2) e2 (Zneg pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
    + (* neg / neg *)
      cbn [dy_div Z.eqb] in Hdiv.
      destruct (Z.eqb (Z.rem (Zneg q1) (Zneg q2)) 0) eqn:Hrem; [|discriminate Hdiv].
      apply Z.eqb_eq in Hrem. injection Hdiv as Hnorm.
      assert (Hqnz : Z.quot (Zneg q1) (Zneg q2) <> Z0).
      { pose proof (Z.quot_rem (Zneg q1) (Zneg q2) ltac:(discriminate)) as Hqr.
        intro F. rewrite F, Z.mul_0_r in Hqr. lia. }
      destruct mr as [|pr|pr];
        [exact (False_ind _ (dy_norm_nonzero _ _ _ _ Hqnz Hnorm eq_refl))| |].
      * rewrite (f64_div_normalize_agrees (Zneg q1) e1 (Zneg q2) e2 (Zpos pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zpos pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
      * rewrite (f64_div_normalize_agrees (Zneg q1) e1 (Zneg q2) e2 (Zneg pr) er q1 q2 pr
                   eq_refl eq_refl eq_refl H1 H2 Hrem Hnorm Hr).
        destruct (render_signed_value_f64 (Zneg pr) er pr eq_refl Hr)
          as [sr [mcr [Tr [Hbnr _]]]].
        rewrite Hbnr. reflexivity.
Qed.

(** ---- rung 7 groundwork — the f32 row's assembly kit: the deep bridges were already
    precision-generic, and the render/normalize assembly is now generic too; these are the
    binary32 instances. *)
Lemma repr_window_split_f32 : forall m e,
  float_dyadic_repr GTFloat32 m e = true ->
  m = Z0 \/ exists q, Z.abs m = Zpos q
     /\ (Zpos (digits2_pos q) <= 24)%Z /\ (emin 24 128 <= e)%Z
     /\ (Zpos (digits2_pos q) + e <= 128)%Z.
Proof.
  intros m e H. destruct m as [|q|q]; [left; reflexivity| |];
    right; exists q; (split; [reflexivity|]);
    exact (float_dyadic_repr_f32_premises _ _ q H eq_refl).
Qed.
Lemma render_signed_value_f32 : forall m e p,
  Z.abs m = Zpos p ->
  float_dyadic_repr GTFloat32 m e = true ->
  exists s mc T,
    binary_normalize 24 128 m e false = S754_finite s mc T
    /\ cond_Zopp s (Zpos mc) = (m * 2 ^ (e - T))%Z
    /\ (emin 24 128 <= T)%Z /\ (T <= e)%Z.
Proof.
  intros m e p Habs Hrep.
  destruct (float_dyadic_repr_f32_premises m e p Hrep Habs) as [Hd [He Hde]].
  exact (render_signed_value_gen 24 128 m e p Habs Hd He Hde ltac:(lia)).
Qed.
Lemma render_canonical_f32 : forall m e p,
  Z.abs m = Zpos p ->
  float_dyadic_repr GTFloat32 m e = true ->
  exists s mc T,
    binary_normalize 24 128 m e false = S754_finite s mc T
    /\ cond_Zopp s (Zpos mc) = (m * 2 ^ (e - T))%Z
    /\ (Zpos (digits2_pos mc) + T = Zpos (digits2_pos p) + e)%Z
    /\ T = fexp 24 128 (Zpos (digits2_pos p) + e)
    /\ (T <= e)%Z.
Proof.
  intros m e p Habs Hrep.
  destruct (float_dyadic_repr_f32_premises m e p Hrep Habs) as [Hd [He Hde]].
  exact (render_canonical_gen 24 128 m e p Habs Hd He Hde ltac:(lia)).
Qed.
Lemma normalize_result_agrees_f32 : forall raw ez mr er,
  dy_norm raw ez = (mr, er) ->
  float_dyadic_repr GTFloat32 mr er = true ->
  binary_normalize 24 128 raw ez false = binary_normalize 24 128 mr er false.
Proof.
  intros raw ez mr er Hn Hrep.
  exact (normalize_result_agrees_gen 24 128 raw ez mr er Hn
           (repr_window_split_f32 mr er Hrep) ltac:(lia)).
Qed.
