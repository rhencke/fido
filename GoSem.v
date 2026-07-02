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
      constants, a CONSTANT in-bounds index into an ALL-CONSTANT int-slice literal [[]int{..}[k]], and [len]
      of such a literal — the WHOLE literal is evaluated, so a runtime/panicking element rejects either; the
      scalar folds are in the [eval_value_good] table below; runtime / out-of-range / OOB values are NOT yet
      denoted).
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

(** Box a float-CONSTANT VALUE — an integer [z] that an EXACT float of type [t] ([GTFloat64]/[GTFloat32]) came
    from — as the MODEL's runtime [GoAny], or [None].  FAILS CLOSED at the boundary with the SAME guard [ptype]
    used to FORM [PtFloatConst] ([int_in_float_exact_interval]: is [z] in the CONTIGUOUS exactly-representable
    interval [[-2^53,2^53]] / [[-2^24,2^24]]?), so an out-of-interval [z] yields [None] HERE — no rounded-lie
    value.  In range the boxed value is the UNIQUE canonical binary64/binary32 form of [z] ([renorm 53 1024] /
    [f32_lit] over the model's [sf_of_Z]), EXACTLY the float the model carries (inside the interval EVERY
    integer is exact, so there is no rounding).  Float CONSTANT arithmetic / fractional literals never reach
    here — [PtFloatConst] carries an integer [z], and [ptype] does not fold them (over-rejected). *)
Definition box_float (t : GoTy) (z : Z) : option GoAny :=
  if int_in_float_exact_interval t z then
    match t with
    | GTFloat64 => Some (anyt TFloat64 (renorm 53 1024 (sf_of_Z z)))   (* canonical binary64 of [z] *)
    | GTFloat32 => Some (anyt TFloat32 (f32_lit (sf_of_Z z)))           (* [f32_lit] rounds-in to canonical binary32 (exact here) *)
    | _         => None
    end
  else None.

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

(** The constant VALUE of a numeric operand (an integer constant, or an exact-integer FLOAT constant — both
    carry the true value as [Z], so [Z]-comparison IS the Go comparison), via [ptype]; [None] for a RUNTIME or
    non-numeric operand (so a comparison with a [len(..)] operand is honestly absent, not folded wrong). *)
Definition const_z (e : GExpr) : option Z :=
  match ptype e with
  | Some (PtIntConst z) | Some (PtTIntConst _ z) | Some (PtFloatConst _ z) => Some z
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
          | Some cmp, Some x, Some y => Some (cmp x y)                      (* numeric comparison *)
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

(** The ptype-driven DEFAULT fold: a numeric / string / bool CONSTANT evaluates to the model value its [ptype]
    category carries ([box_int]/[box_float] attach it, FAILING CLOSED out of range); everything else is [None]. *)
Definition eval_value_ptype (e : GExpr) : option GoAny :=
  match ptype e with
  | Some (PtIntConst z)     => box_int GTInt z                                                 (* untyped const -> default [int], range-checked *)
  | Some (PtTIntConst t z)  => box_int t z                                                     (* typed int const (conversion / typed arith) *)
  | Some (PtFloatConst t z) => box_float t z                                                   (* typed float const (exact int-valued: [float64(3)], [-float32(5)]) *)
  | Some PtStr              => match eval_str e with Some s => Some (anyt TString s) | None => None end  (* a string CONSTANT: literal / concatenation / string-or-rune conversion ([PtStr] carries no value; [eval_str] folds it) *)
  | Some PtBool             => match eval_bool e with Some b => Some (anyt TBool b) | None => None end   (* a CONSTANT bool: comparison / logical fold *)
  | _                       => None
  end.

(** Evaluate EVERY entry of an integer-keyed MAP literal to its boxed [(key, value)] pair, ALL-or-[None] —
    the whole-literal discipline of [eval_int_slice_elems]: Go constructs the ENTIRE literal before [len],
    so a runtime / wrong-typed key or value — even one irrelevant to the queried length — makes the fold
    [None], never a wrong value.  Each entry is gated by [ptype]'s OWN map-arm checks ([assignable_to_ty]
    on BOTH sides + an integer-CONSTANT key; proved ⊆ [ptype]: [eval_map_len_supported]); values fold by
    the CONSTANT default [eval_value_ptype], so a supported RUNTIME value ([len([]int{2})]) declines the
    whole fold — absent, not wrong ([map_len_supported_but_undenoted]). *)
Fixpoint eval_map_entries (kt vt : GoTy) (kvs : list (GExpr * GExpr)) : option (list (GoAny * GoAny)) :=
  match kvs with
  | [] => Some []
  | (k, v) :: rest =>
      match ptype k, ptype v with
      | Some ck, Some cv =>
          if assignable_to_ty ck kt && assignable_to_ty cv vt
          then match int_const_val ck with
               | Some z =>
                   match box_int kt z, eval_value_ptype v, eval_map_entries kt vt rest with
                   | Some bk, Some bv, Some rest' => Some ((bk, bv) :: rest')
                   | _, _, _ => None
                   end
               | None => None
               end
          else None
      | _, _ => None
      end
  end.

(** [ptype]'s map-arm KEY-VALUE list, named (the [EMapLit] arm spells this [flat_map] inline; the inclusion
    proof [eval_map_len_supported] unfolds this name onto that exact term — a drift would break it). *)
Definition map_key_vals (kvs : list (GExpr * GExpr)) : list Z :=
  flat_map (fun kv => match kv with
                      | (k, _) =>
                          match ptype k with
                          | Some ck => match int_const_val ck with Some z => z :: nil | None => nil end
                          | None => nil
                          end
                      end) kvs.

(** Evaluate a value expr to the model's [GoAny], else [None].  FAITHFUL: the ptype-driven arm folds a numeric /
    string / bool constant ([ptype] → VALUE+TYPE, [box_int]/[box_float] attach the model value, FAILING CLOSED
    out of range); a separate [EIndex (ESliceLit..)] arm folds a CONSTANT in-bounds int-slice index by
    evaluating the WHOLE literal ([eval_int_slice_elems] — ALL elements, so a runtime/panicking/out-of-range
    element rejects it) and indexing.  Its accept-boundary is [ptype]'s OWN — elements gated by
    [assignable_to_ty] and the constant index by [(0<=?k) && int_const_repr k GTInt], the SAME checks [ptype]'s
    slice arm uses — so the arm accepts NO expression [ptype] rejects (proved: [eval_slice_index_supported]); it
    is a SUBSET, not a second, looser classifier.  Scalar coverage exercised — the [eval_value_good] table (gated by [eval_value_good_ok]) folds:
    integer constants (conversions / in-range [uint] via [mk_uint] / arithmetic / complement, EXCLUDING
    platform-[uint] complement), exact-integer FLOAT constants, string constants ([eval_str]), and constant
    bools ([eval_bool]); slice-index folds pinned by [slice_index_*] below; [len] of a fully-evaluable int-slice
    literal folds to its length ([eval_len_reduces]) and [len] of a fully-evaluable integer-keyed MAP literal to
    its entry count ([eval_map_len_reduces] — the gate's [nodup_z] makes constant keys distinct, so the count IS
    Go's [len]).  ABSENT ([None], honestly): [len] of a literal with runtime ELEMENTS or of a map literal with a
    runtime VALUE, runtime operands ([int(x)] of a runtime [x], runtime comparisons), OOB / runtime slice INDEX,
    out-of-range or COMPLEMENTED [uint], fractional/multi-byte-rune — never wrong. *)
Definition eval_value (e : GExpr) : option GoAny :=
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
      else eval_value_ptype e
  | ECall (EId f) (EMapLit kt vt kvs :: nil) =>
      (* [len] of a FULLY-EVALUABLE integer-keyed MAP literal folds to its entry count, boxed as Go's [int].
         Go constructs the literal (ALL keys and values) before [len], so a runtime / wrong-typed key or value
         declines the fold ([eval_map_entries] — the whole-literal discipline); the gate's distinctness check
         ([nodup_z], [ptype]'s own inline key list, named [map_key_vals]) is REQUIRED here too — without it a
         duplicate-key literal (invalid Go) would fold [length kvs], which is NOT the map's [len].  [ptype]
         still classifies the call [PtRunInt GTInt] (a map is not a constant).  Any OTHER call with a
         map-literal argument falls through to the ptype-driven default unchanged. *)
      if String.eqb (proj1_sig f) "len" && is_int_goty kt && nodup_z (map_key_vals kvs)
      then match eval_map_entries kt vt kvs with
           | Some ents => box_int GTInt (Z.of_nat (length ents))
           | None => None
           end
      else eval_value_ptype e
  | _ => eval_value_ptype e
  end.

(** ---- EFFECTFUL expression denotation (slice 1 of the runtime-panic layer).  Supported programs are CLOSED
    (free identifiers are rejected), so every expression's outcome is DETERMINED; what the pure [eval_value]
    cannot express is a PANICKING outcome.  [denote_expr] denotes an expression to a COMMAND: [CRet v] when the
    pure fold gives its value, [CPan rt_div_zero] for an integer [/] or [%] whose determined divisor is ZERO
    (Go's runtime "integer divide by zero" — a runtime panic, since [ptype] admits only a RUNTIME-classified
    zero divisor there: a CONSTANT zero divisor is a Go COMPILE error, rejected by [num_binop]).  Everything
    else is honestly [None].  The arm is SEALED to the classifier ([ptype = PtRunInt] required) and to the
    evaluator ([divisor_zero]'s zero-judgment provably AGREES with [eval_value] — [divisor_zero_eval]), so it
    is a subset of the supported fragment with no second folding authority. *)
Definition divisor_zero (b : GExpr) : bool :=
  match b with
  | ECall (EId f) (ESliceLit t es :: nil) =>
      String.eqb (proj1_sig f) "len" && is_int_goty t
      && match eval_int_slice_elems t es with Some nil => true | _ => false end
  | ECall (EId f) (EMapLit kt vt kvs :: nil) =>
      String.eqb (proj1_sig f) "len" && is_int_goty kt
      && match kvs with nil => true | _ => false end
  | _ => false
  end.

(** The SEAL: [divisor_zero]'s judgment IS the evaluator's — a zero-judged divisor evaluates to the boxed
    integer 0 (the [len] of an empty fully-evaluable SLICE or MAP literal). *)
Lemma divisor_zero_eval : forall b, divisor_zero b = true -> eval_value b = box_int GTInt 0.
Proof.
  intros b H. unfold divisor_zero in H.
  destruct b as [ | | | | | | | fe fargs | | | | | | ]; try discriminate H.
  destruct fe as [ f | | | | | | | | | | | | | ]; try discriminate H.
  destruct fargs as [|a rest]; try discriminate H.
  destruct a as [ | | | | | | | | | | t es | kt vt kvs | | ]; try discriminate H.
  - (* slice: [len([]t{})] *)
    destruct rest as [|? ?]; try discriminate H.
    apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [Hf Ht].
    destruct (eval_int_slice_elems t es) as [[|v vs]|] eqn:He; try discriminate H2.
    cbn [eval_value]. rewrite Hf, Ht. cbv beta iota delta [andb].
    rewrite He. reflexivity.
  - (* map: [len(map[kt]vt{})] *)
    destruct rest as [|? ?]; try discriminate H.
    apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [Hf Ht].
    destruct kvs as [|kv kvs']; [|discriminate H2].
    cbn [eval_value]. rewrite Hf, Ht. reflexivity.
Qed.

Definition denote_expr (e : GExpr) : option (Cmd GoAny * bool) :=
  match eval_value e with
  | Some v => Some (CRet v, false)
  | None =>
      match e with
      | EBn o a b =>
          match o with
          | BDiv | BRem =>
              match ptype e with
              | Some (PtRunInt _) =>                        (* SUPPORTED runtime INTEGER / or % (float /0 is ±Inf, not a panic — excluded by the guard) *)
                  match eval_value a, divisor_zero b with
                  | Some _, true => Some (CPan rt_div_zero, true)  (* the dividend evaluates cleanly, the divisor is determined 0 -> Go's runtime panic; TERMINATES *)
                  | _, _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

(** The pure inclusion: an expression the fold gives a value to denotes to exactly [CRet] of that value
    (fall-through — a pure expression cannot terminate control flow). *)
Lemma denote_expr_pure : forall e v, eval_value e = Some v -> denote_expr e = Some (CRet v, false).
Proof. intros e v H. unfold denote_expr. rewrite H. reflexivity. Qed.

(** ★ CLASS — the determined divide-by-zero PANICS: a SUPPORTED runtime integer [/] or [%] whose dividend
    evaluates cleanly and whose divisor is determined 0 denotes to [CPan rt_div_zero] (Go's exact runtime
    panic value).  Sealed by construction: the arm requires [ptype = Some (PtRunInt t)] (supported) and
    [divisor_zero] (which agrees with [eval_value] — [divisor_zero_eval]). *)
Lemma denote_expr_div_zero : forall o a b t va,
  (o = BDiv \/ o = BRem) ->
  ptype (EBn o a b) = Some (PtRunInt t) ->
  eval_value a = Some va ->
  divisor_zero b = true ->
  denote_expr (EBn o a b) = Some (CPan rt_div_zero, true).
Proof.
  intros o a b t va Ho Hpt Ha Hdz.
  unfold denote_expr.
  assert (Hev : eval_value (EBn o a b) = None).
  { cbn [eval_value]. unfold eval_value_ptype. rewrite Hpt. reflexivity. }
  rewrite Hev.
  destruct Ho as [-> | ->]; rewrite Hpt, Ha, Hdz; reflexivity.
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
    AGREE.  A CHARACTERIZATION result, NOT [supported ⟹ denotes]: the [denotable_*] ⊊ [supported_*] gap is the
    unmodeled VALUE forms (runtime [len]/[int(x)], fractional floats), which [eval_value] growth closes — a
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

(** ---- COMPLETENESS FRAGMENT — [supported ⟹ denotes] for the PRINT/PRINTLN-of-DENOTABLE-ARGS fragment
    (AUTHORITY: [out_main_denotes]).  NOT the whole supported output class: an ARG denotes iff it EVALUATES and
    is PRINTABLE ([denotable_arg] — exactly the per-arg denotation condition, so the converse holds OUTRIGHT on
    this fragment); a RUNTIME arg is supported but not [denotable_arg] ([out_boundary_runtime_undenoted]), and a
    supported-but-eval-partial constant (multi-byte rune [string(200)]) is pinned by
    [runeconv_multibyte_boundary].  [denotable_supported] pins denotable ⊆ supported — a STRICT inclusion (the
    gap: the eval-partial value forms). *)
Definition denotable_arg (e : GExpr) : bool :=
  match eval_value e with Some _ => printable_arg_ok e | None => false end.

Lemma denotable_arg_eval : forall e, denotable_arg e = true -> eval_value e <> None.
Proof. intros e H Hn. unfold denotable_arg in H. rewrite Hn in H. discriminate. Qed.

Lemma denotable_arg_printable : forall e, denotable_arg e = true -> printable_arg_ok e = true.
Proof. intros e H. unfold denotable_arg in H. destruct (eval_value e); [exact H | discriminate]. Qed.

(** String CONCATENATION and CONVERSIONS DENOTE (the [eval_value] folds are in [eval_value_good]; these pin the
    stronger [denotable_arg] — evaluable AND printable): [`"a" + "b"`], the ASCII rune [`string(65)`], the
    identity [`string("a"+"b")`]. *)
Example denotable_arg_str_concat : denotable_arg (EBn BAdd (EStr "a") (EStr "b")) = true.
Proof. vm_compute. reflexivity. Qed.
Example denotable_arg_runeconv_ascii :
  denotable_arg (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) = true.
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

Lemma eval_args_denotable : forall args, forallb denotable_arg args = true -> eval_args args <> None.
Proof.
  induction args as [|a rest IH]; simpl; intro H; [discriminate|].
  apply andb_true_iff in H as [Ha Hrest]. specialize (IH Hrest).
  pose proof (denotable_arg_eval a Ha) as Hva.
  destruct (eval_value a); [|exfalso; apply Hva; reflexivity].
  destruct (eval_args rest); [discriminate | exfalso; apply IH; reflexivity].
Qed.

Lemma forallb_denotable_printable : forall args,
  forallb denotable_arg args = true -> forallb printable_arg_ok args = true.
Proof.
  induction args as [|a rest IH]; simpl; intro H; [reflexivity|].
  apply andb_true_iff in H as [Ha Hrest]. rewrite (denotable_arg_printable a Ha), (IH Hrest). reflexivity.
Qed.

(** THE CONVERSE AUTHORITY — [supported ⟹ denotes] on the PRINT/PRINTLN-of-DENOTABLE-ARGS fragment.  A
    print/println arg denotes iff it EVALUATES + is PRINTABLE ([denotable_arg]).  [out_call pr]: [println]
    (pr=true) / [print] (pr=false) — the gate admits both ([stmt_call_ok]), and [print] denotes identically with
    the [COut] flag FALSE.  ⚠ This is a FRAGMENT, NOT the whole supported output class — a print/println of a
    RUNTIME arg ([println(len([]int{len([]int{1})}))]) is SUPPORTED but NOT [denotable_arg], so it does NOT denote
    (pinned by [out_boundary_runtime_undenoted]); widening [eval_value] widens this fragment.  [println_main_denotes]
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
  (proj1_sig f = "println"%string \/ proj1_sig f = "print"%string) -> forallb denotable_arg args = true ->
  expr_stmt_ok (ECall (EId f) args) = true.
Proof.
  intros f args Hf Hargs. cbn [expr_stmt_ok stmt_call_ok].
  destruct Hf as [Hf|Hf]; rewrite Hf; cbn; rewrite (forallb_denotable_printable args Hargs); reflexivity.
Qed.
(** A print/println of denotable args denotes — as a CONTINUER ([Some (_, false)]): the shape [denotable_body]
    consumes when it is followed by more statements. *)
Lemma denote_out_denotable : forall f args,
  (proj1_sig f = "println"%string \/ proj1_sig f = "print"%string) -> forallb denotable_arg args = true ->
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
  forallb denotable_arg args = true ->
  exists c, denote_stmt (GsExprStmt (out_call pr args)) = Some (c, false).
Proof.
  intros pr args Hargs. destruct pr; cbn [out_call].
  - exact (denote_out_denotable (mkIdent "println" eq_refl) args (or_introl eq_refl) Hargs).
  - exact (denote_out_denotable (mkIdent "print" eq_refl) args (or_intror eq_refl) Hargs).
Qed.
Lemma out_main_denotable : forall stmts,
  forallb (fun s => forallb denotable_arg (snd s)) stmts = true -> denotable_body (out_main_body stmts) = true.
Proof.
  induction stmts as [|[pr args] rest IH]; intro H.
  - reflexivity.
  - cbn in H. apply andb_true_iff in H as [Hargs Hrest]. cbn [out_main_body].
    destruct (denote_out_call_denotable pr args Hargs) as [c Hc].
    cbn [denotable_body]. rewrite Hc. exact (IH Hrest).
Qed.
Theorem out_main_denotes : forall stmts,
  forallb (fun s => forallb denotable_arg (snd s)) stmts = true ->
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
    [println(args)] (every arg [denotable_arg]) + [return] denotes.  [println_main_body] is [out_main_body] with
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
Lemma denotable_arglists_out : forall arglists,
  forallb (forallb denotable_arg) arglists = true ->
  forallb (fun s => forallb denotable_arg (snd s)) (map (fun a => (true, a)) arglists) = true.
Proof.
  induction arglists as [|args rest IH]; [reflexivity|].
  cbn; intro H; apply andb_true_iff in H as [Ha Hr]; rewrite Ha; cbn; exact (IH Hr).
Qed.
Theorem println_main_denotes : forall arglists,
  forallb (forallb denotable_arg) arglists = true ->
  denote_program (mkProgram (mkIdent "main" eq_refl) (println_main_body arglists)) <> None.
Proof.
  intros arglists H. rewrite (println_main_body_out arglists).
  exact (out_main_denotes _ (denotable_arglists_out arglists H)).
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
    slice-[len] whose ELEMENT is runtime) and [maplen_runval_e] (a map-[len] whose VALUE is runtime) = the
    supported-but-undenoted witnesses (runtime values await B3). *)
Definition divzero_e : GExpr :=
  EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt []]).
Definition divzero_map_e : GExpr :=
  EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt GTInt []]).
Definition maplen_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]].
Definition runlen_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]].
Definition maplen_runval_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl))
        [EMapLit GTInt GTInt [(EInt 1, ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 2]])]].

(** BOUNDARY — the fragment is NOT the whole supported output class: [println(len([]int{len([]int{1})}))] is
    SUPPORTED (valid Go) yet its arg is a [len] over a RUNTIME element GoSem does not fold (NOT
    [denotable_arg]), so the program does NOT denote.  (A fully-evaluable literal's [len] folds — this witness
    is the strictness pin for the [eval_len_supported] inclusion.) *)
Definition out_runtime_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runlen_e]); GsReturn].
Example out_boundary_runtime_undenoted :
  supported_program out_runtime_prog = true
  /\ denotable_arg runlen_e = false
  /\ denote_program out_runtime_prog = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ---- GENERAL statement-compositional CONVERSE: a body whose EVERY statement INDIVIDUALLY denotes is
    denotable, so its `main` DENOTES — generalizing [out_main_denotes] to ALL denoting statement forms
    interleaved, including a terminator followed by (supported) DEAD code.  SUFFICIENT, not necessary: a
    terminator's unreachable rest need only be SUPPORTED.  STILL CONDITIONAL on [stmt_denotable], NOT full
    [supported_program] — the gap is the eval-partial value forms (see the decidability note above). *)
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
    is_int_goty t = true ->
    ptype idx = Some ci ->
    int_const_val ci = Some k ->
    (0 <=? k)%Z = true ->
    int_const_repr k GTInt = true ->
    eval_int_slice_elems t es = Some vs ->
    eval_value (EIndex (ESliceLit t es) idx) = nth_error vs (Z.to_nat k).
Proof.
  intros t es idx ci k vs Ht Hp Hi Hk Hr Hv.
  (* Expose the [EIndex (ESliceLit..)] arm ([cbn [eval_value]] keeps [is_int_goty t]/[int_const_repr] FOLDED —
     whitelist delta), then rewrite each scrutinee and IOTA-reduce (never full [cbn], which would unfold
     [int_const_repr] and defeat [rewrite Hr]) the match it heads before the next rewrite. *)
  cbn [eval_value].
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
    is_int_goty t = true ->
    ptype idx = Some ci ->
    int_const_val ci = Some k ->
    (0 <=? k)%Z = true ->
    int_const_repr k GTInt = true ->
    eval_int_slice_elems t es = Some vs ->
    (length vs <= Z.to_nat k)%nat ->
    eval_value (EIndex (ESliceLit t es) idx) = None.
Proof.
  intros t es idx ci k vs Ht Hp Hi Hk Hr Hv Hoob.
  rewrite (eval_slice_index_reduces t es idx ci k vs Ht Hp Hi Hk Hr Hv).
  apply (proj2 (nth_error_None vs (Z.to_nat k))). exact Hoob.
Qed.

(** CLASS — IN-BOUNDS FAITHFUL: a constant index STRICTLY WITHIN the length folds to the k-th boxed element
    VALUE (a real [Some], never [None]), for the whole fully-evaluable all-constant subfragment. *)
Lemma eval_slice_index_inbounds_class :
  forall t es idx ci k vs,
    is_int_goty t = true ->
    ptype idx = Some ci ->
    int_const_val ci = Some k ->
    (0 <=? k)%Z = true ->
    int_const_repr k GTInt = true ->
    eval_int_slice_elems t es = Some vs ->
    (Z.to_nat k < length vs)%nat ->
    exists v, eval_value (EIndex (ESliceLit t es) idx) = Some v /\ nth_error vs (Z.to_nat k) = Some v.
Proof.
  intros t es idx ci k vs Ht Hp Hi Hk Hr Hv Hin.
  rewrite (eval_slice_index_reduces t es idx ci k vs Ht Hp Hi Hk Hr Hv).
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
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty t = true ->
  eval_int_slice_elems t es = Some vs ->
  eval_value (ECall (EId f) (ESliceLit t es :: nil)) = box_int GTInt (Z.of_nat (length vs)).
Proof.
  intros t es f vs Hf Ht Hv.
  cbn [eval_value].
  rewrite Hf, Ht. cbv beta iota delta [andb].
  rewrite Hv. reflexivity.
Qed.

(** ★ SUPPORTEDNESS INCLUSION BRIDGE ([len]) — the fold's hypotheses IMPLY [ptype = Some (PtRunInt GTInt)]
    (valid Rocq-Go; [ptype] classifies a slice-[len] RUNTIME, exactly as it does the index — the evaluator
    folds the determined VALUE without loosening the gate).  A strict INCLUSION: [ptype] also admits [len] of
    a literal with runtime elements, which stays unfolded ([out_boundary_runtime_undenoted]). *)
Lemma eval_len_supported : forall t es f vs,
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty t = true ->
  eval_int_slice_elems t es = Some vs ->
  ptype (ECall (EId f) (ESliceLit t es :: nil)) = Some (PtRunInt GTInt).
Proof.
  intros t es f vs Hf Ht Hv.
  pose proof (eval_int_slice_elems_forall_assignable t es vs Hv) as Hall.
  cbn [ptype]. rewrite Hall. cbv beta iota zeta.
  rewrite Hf. cbv beta iota.
  reflexivity.
Qed.

(** The SEALED map evaluator's accept-set ⊆ [ptype]'s entry check: if [eval_map_entries] succeeds, EVERY
    entry passes exactly [ptype]'s map-arm [forallb] gate (integer-CONSTANT key, both sides assignable).
    (Induction on [kvs] — the [eval_int_slice_elems_forall_assignable] discipline.) *)
Lemma eval_map_entries_forall_entry :
  forall kt vt kvs ents, eval_map_entries kt vt kvs = Some ents ->
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
  intros kt vt kvs. induction kvs as [|[k v] rest IH]; intros ents H.
  - reflexivity.
  - cbn [forallb]. cbn [eval_map_entries] in H.
    destruct (ptype k) as [ck|] eqn:Ek; [|discriminate H].
    destruct (ptype v) as [cv|] eqn:Ev; [|discriminate H].
    destruct (assignable_to_ty ck kt && assignable_to_ty cv vt) eqn:Ea; [|discriminate H].
    destruct (int_const_val ck) as [z|] eqn:Ei; [|discriminate H].
    destruct (box_int kt z) as [bk|] eqn:Eb; [|discriminate H].
    destruct (eval_value_ptype v) as [bv|] eqn:Ebv; [|discriminate H].
    destruct (eval_map_entries kt vt rest) as [rest'|] eqn:Er; [|discriminate H].
    cbn [andb]. exact (IH rest' eq_refl).
Qed.

(** ★ CLASS THEOREM (map-[len]) — over the fully-evaluable all-constant-entry subfragment: [len] of an
    integer-keyed map literal whose entries ALL evaluate (and whose constant keys are distinct — the gate's
    OWN [nodup_z] condition, so the entry count IS Go's [len]) folds to that count, boxed as Go's [int]. *)
Lemma eval_map_len_reduces : forall kt vt kvs f ents,
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty kt = true ->
  nodup_z (map_key_vals kvs) = true ->
  eval_map_entries kt vt kvs = Some ents ->
  eval_value (ECall (EId f) (EMapLit kt vt kvs :: nil)) = box_int GTInt (Z.of_nat (length ents)).
Proof.
  intros kt vt kvs f ents Hf Ht Hnd Hv.
  cbn [eval_value]. rewrite Hf, Ht, Hnd. cbv beta iota delta [andb].
  rewrite Hv. reflexivity.
Qed.

(** ★ SUPPORTEDNESS INCLUSION BRIDGE (map-[len]) — the fold's hypotheses IMPLY [ptype = Some (PtRunInt GTInt)]
    (valid Rocq-Go; the evaluator folds the determined count without loosening the gate).  A strict INCLUSION:
    [ptype] also admits a map literal with a RUNTIME value, which stays unfolded — strictness pinned by
    [map_len_supported_but_undenoted]. *)
Lemma eval_map_len_supported : forall kt vt kvs f ents,
  String.eqb (proj1_sig f) "len" = true ->
  is_int_goty kt = true ->
  nodup_z (map_key_vals kvs) = true ->
  eval_map_entries kt vt kvs = Some ents ->
  ptype (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some (PtRunInt GTInt).
Proof.
  intros kt vt kvs f ents Hf Ht Hnd Hv.
  pose proof (eval_map_entries_forall_entry kt vt kvs ents Hv) as Hall.
  unfold map_key_vals in Hnd.
  cbn [ptype]. rewrite Ht, Hall, Hnd. cbv beta iota zeta delta [andb].
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
  [ EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 5)
  ; EIndex (ESliceLit GTInt [EInt 20; EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt []])]) (EInt 0)
  ; EIndex (ESliceLit GTInt [ECall (EId (mkIdent "int64" eq_refl)) [EInt 1]]) (EInt 0)
  ; EIndex (ESliceLit GTU8 [EInt 300; EInt 1]) (EInt 1) ].
Example slice_index_undenoted_ok :
  forallb (fun e => match eval_value e, denote_program (println_prog e) with
                    | None, None => true | _, _ => false end)
          slice_index_undenoted = true.
Proof. vm_compute. reflexivity. Qed.
(** STRICT-SUBSET pin (GATED): a RUNTIME index and a RUNTIME same-typed element are [ptype]-SUPPORTED (valid
    Go) yet undenoted at BOTH the expression and program level — so [eval_slice_index_supported] is a strict
    INCLUSION, not equality; runtime cases await runtime values. *)
Example slice_index_supported_but_undenoted :
  ptype (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])) = Some (PtRunInt GTInt)
  /\ eval_value (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])) = None
  /\ denote_program (println_prog (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]))) = None
  /\ ptype (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)) = Some (PtRunInt GTInt)
  /\ eval_value (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)) = None
  /\ denote_program (println_prog (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0))) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

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
    a runtime integer division) and denotes+runs to the exact panic, like [rc_div_zero]'s slice shape
    ([divisor_zero] recognizes BOTH empty-literal [len] forms; sealed by [divisor_zero_eval]). *)
Definition gosem_maplen_divzero_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign divzero_map_e].
Example maplen_divzero_runs : forall w,
  supported_program gosem_maplen_divzero_prog = true
  /\ match denote_program gosem_maplen_divzero_prog with
     | Some c => run_cmd 5 c w | None => None end = Some (OPanic rt_div_zero w).
Proof. intro w; split; vm_compute; reflexivity. Qed.

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

(** The escape is REAL (the converse is genuinely sufficient-not-necessary): [return; println(runlen_e)]
    is a DENOTABLE body ([return] terminates; the runtime-arg [println] is a SUPPORTED dead tail) whose tail
    does NOT denote, so [denotable_body = true] while [forallb stmt_denotable = false].  This body HAS a
    terminator — exactly why the iff above does not apply to it. *)
Example denotable_body_escapes_stmt_denotable :
  denotable_body [GsReturn;
    GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runlen_e])] = true
  /\ forallb stmt_denotable [GsReturn;
       GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runlen_e])] = false.
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
    in each is the runtime-element [len] ([runlen_e], supported-printable yet undenoted —
    [out_boundary_runtime_undenoted]): as a LATER ARG of the panicking call, as the SUCCESSOR statement, and
    as the successor of a DEFERRED panicking-arg call.  Each program denotes and runs to [OPanic rt_div_zero]
    with NO output. *)
Definition gosem_arg_panic_tail_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [divzero_e; runlen_e]); GsReturn].
Definition gosem_arg_panic_succ_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runlen_e]); GsReturn].
Definition gosem_defer_arg_panic_succ_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [divzero_e]);
     GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runlen_e]); GsReturn].
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
    value per signedness/width), exact-integer FLOAT constants, constant BOOLs (numeric + string comparisons,
    [&&]/[||]/[!], [bool(x)]), string CONSTANTs (literal/concat/ASCII-rune/identity conv; high-byte order is
    UNSIGNED), and the constant in-bounds slice-index.  The [box_*]/[ptype] FAIL-CLOSED pins are separate below
    — those lock the GATE boundary, not a fold. *)
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
  ; (ECall (EId (mkIdent "len" eq_refl)) [EStr "abc"], anyt TInt64 (intwrap 3))
  ; (EBn BAdd (EStr "a") (EStr "b"), anyt TString "ab")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EInt 65], anyt TString "A")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EStr "A"], anyt TString "A")
  ; (ECall (EId (mkIdent "string" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")], anyt TString "ab")
  ; (EBn BEq (EInt 1) (EInt 1), anyt TBool true)
  ; (EBn BLt (EInt 3) (EInt 5), anyt TBool true)
  ; (EBn BEq (EInt 1) (EInt 2), anyt TBool false)
  ; (EBn BEq (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]) (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]), anyt TBool true)
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

(** FAIL-CLOSED pins (LOAD-BEARING, lock the GATE boundary — NOT folds): out-of-range boxing is [None]
    ([mk_uint]/[box_*] never carry a [*wrap]-mangled value); a mixed-WIDTH ill-typed compare [int64(1)==int32(1)]
    has [ptype = None] so [eval_bool]/[eval_value] fail closed (no fabricated [true]); the uint underflow
    [uint(3)-uint(5)] has [ptype = None] ⇒ [printable_arg_ok = false] ⇒ never emitted (the ROOT rejection, not
    the eval backstop).  A supported [ptype = Some PtBool] pins the two string/bool categories are ADMITTED. *)
Definition mixed_width_cmp : GExpr :=
  EBn BEq (ECall (EId (mkIdent "int64" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "int32" eq_refl)) [EInt 1]).
Definition uint_underflow_e := EBn BSub (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3]) (ECall (EId (mkIdent "uint" eq_refl)) [EInt 5]).
Example eval_value_failclosed :
  box_float GTFloat64 9007199254740993 = None
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
  ; runlen_e            (* len over a RUNTIME slice element: supported, honestly unfolded *)
  ; maplen_runval_e ].  (* len over a RUNTIME map value: supported, honestly unfolded *)
Example eval_absent_none : forallb (fun e => match eval_value e with None => true | Some _ => false end) eval_absent = true.
Proof. vm_compute. reflexivity. Qed.

(** DENOTABILITY-DECISION witnesses (grouped): [denotable_program] (the decidable predicate of
    [denote_program_dec]) agrees with whether each demo denotes — TRUE for the denoting demos (defer and the
    determined divide-by-zero included), FALSE (and [denote_program = None]) for the supported-but-undenoted
    runtime-element-[len] program ([out_runtime_prog]). *)
Example gosem_denotability_decisions :
  forallb denotable_program
    [gosem_demo_prog; gosem_return_stops_prog; gosem_strlit_prog; gosem_defer_prog;
     gosem_runtime_blank_prog; gosem_arg_panic_prog; gosem_defer_arg_panic_prog] = true
  /\ forallb (fun p => negb (denotable_program p)) [out_runtime_prog] = true
  /\ forallb (fun p => match denote_program p with None => true | Some _ => false end)
       [out_runtime_prog] = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

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
   denote_expr_pure, divisor_zero_eval, denote_expr_div_zero, arg_panic_shortcircuit_runs,
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
