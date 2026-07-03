(** ============================================================================
    GoSemDenote.v — the DENOTATION layer (the ARCHITECTURE.md §3a physical split, file 2):
    [eval_value] + its [Local] core (the float boundary's sealed evaluator — public access
    would bypass [floats_checked]; negtest-sealed), the runtime GTInt tier R1–R8 and the
    typed tiers T1–T5 over ONE shared evaluator, [denote_expr]/[denote_program] + the
    statement layer, [gosem_sound] (denotation ⊆ supportedness) + the compositional
    converses, and EVERY class theorem (tier seals, dispatch authorities, slice-index/map
    reductions).  ONE file by necessity, not the sketched RuntimeInt/Agg pair: these proofs
    compute through the [Local] evaluator core and the tier seals are denote-level, so no
    smaller Local-sealed cut exists without proof rewrites.
    Grounding/coverage examples stay ADJACENT to the theorems they pin; the program-level
    fixture GROUPS, demos, the frontier + the gated surfaces live downstream in GoSem.v
    (the composition point, which re-exports GoSemCore + this file).
    ============================================================================ *)
From Fido Require Import GoAst GoTypes GoSafe cmd preamble.   (* [preamble] re-exports [builtins]: [GoAny]/[anyt]/[intwrap]/[World]/[w_log]/[Outcome]/[ORet] *)
From Fido Require Import GoSemCore.
From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
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
    is a SUBSET, not a second, looser classifier.  Scalar coverage exercised — the [eval_value_good] table (downstream in GoSem.v, gated by [eval_value_good_ok]) folds:
    integer constants (conversions / in-range [uint] via [mk_uint] / arithmetic / complement, EXCLUDING
    platform-[uint] complement), exact-DYADIC FLOAT constants (fractional arithmetic included), string constants ([eval_str]), and constant
    bools ([eval_bool]); slice-index folds pinned by the [slice_index_*] fixtures (downstream in GoSem.v); [len] of a fully-evaluable int-slice
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

(** the CARRY-shape obligation pinned mechanically: an ACCEPTED normalized ADD
    result whose RAW aligned sum exceeds [prec] digits — [(2^53-1) + (2^53-1)] has raw sum
    [2^54-2] (54 digits, OUTSIDE [binary_round_exact]'s direct window) while the normalized
    result [(2^53-1, 1)] passes the gate AND the checker accepts the expression (the live path
    already exercises the raw-wide case, computed by [SFadd] on the raw mantissa).  So [ptype]
    does NOT reject this class — it is EXACTLY the wide bridge's domain
    ([binary_round_of_norm_wide] above): the agreement assembly must route through that
    bridge, never the narrow window alone. *)
Definition add_carry_e : GExpr :=
  EBn BAdd (ECall (EId (mkIdent "float64" eq_refl)) [EInt 9007199254740991])
           (ECall (EId (mkIdent "float64" eq_refl)) [EInt 9007199254740991]).
Example add_carry_raw_wide_accepted :
  Zpos (digits2_pos 18014398509481982%positive) = 54%Z
  /\ dy_norm 18014398509481982 0 = (9007199254740991%Z, 1%Z)
  /\ float_dyadic_repr GTFloat64 9007199254740991 1 = true
  /\ match ptype add_carry_e with
     | Some (PtFloatConst GTFloat64 d) =>
         andb (Z.eqb (dy_m d) 9007199254740991) (Z.eqb (dy_e d) 1)
     | _ => false
     end = true
  /\ eval_value add_carry_e
     = Some (anyt TFloat64 (S754_finite false 9007199254740991%positive 1)).
Proof. repeat split; vm_compute; reflexivity. Qed.

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
(** [_tc] layer: the CATEGORY AUTHORITY is a parameter [tc] — SEALED, not free.  Every arm
    consumes SHAPE OBLIGATIONS of its authority, so a forged classifier could smuggle behavior;
    the whole family is [Local], each of the five names pinned uncallable by its own negtest
    ([neg_tc_*_escape]).  The closed wrappers below instantiate [ptype] (the SAME function
    definitionally); any other instance can only be constructed in THIS file. *)
Local Definition typed_operand_tc (tc : GExpr -> option PTy) (rv : GExpr -> option RAny) (t : GoTy) (e : GExpr) : option RAny :=
  match tc e with
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
Definition typed_operand : (GExpr -> option RAny) -> GoTy -> GExpr -> option RAny :=
  typed_operand_tc ptype.
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
Local Definition shift_count_tc (tc : GExpr -> option PTy) (rv : GExpr -> option RAny) (e : GExpr) : option (Z + GoAny) :=
  (* A CONSTANT count is read off the category authority's OWN value directly — TOTAL on the gate's
     admitted class ([shift_count_const_total] needs no evaluation premise).  The boxed path would be a
     side-condition leak: [box_int]'s conservative default-[int] window is a VALUE range, not a
     COUNT range, and would drop a VALID untyped count like [2^31]; the gate's shift row is the
     one count authority ([is_neg_const] + [untyped_count_overflow]).  Only a RUNTIME count
     evaluates ([rv], at its own width — panics propagate). *)
  match tc e with
  | Some (PtIntConst z)    => Some (inl z)
  | Some (PtTIntConst _ z) => Some (inl z)
  | _ =>
      match rv e with
      | Some (RAVal g) => match runint_raw g with Some z => Some (inl z) | None => None end
      | Some (RAPanic p) => Some (inr p)
      | None => None
      end
  end.
Definition shift_count : (GExpr -> option RAny) -> GExpr -> option (Z + GoAny) :=
  shift_count_tc ptype.
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

(** The CLOSED leaf: no name resolves. *)
Local Definition leaf_closed : string -> option GoAny := fun _ => None.

(** EId-arm tag defense (the GTInt case is [unbox_int] in [reval_int_tc]): a resolved value is
    admitted only when its tag matches the bound category — a forged env is ABSENT. *)
Local Definition eid_exit_tag_ok (c : PTy) (g : GoAny) : bool :=
  match c with
  | PtRunInt t => andb (negb (numty_eqb t GTInt)) (tag_matches t g)
  | PtRunFloat t =>
      match g with
      | existT _ _ (pair _ tag) =>
          match t, tag with
          | GTFloat64, TFloat64 | GTFloat32, TFloat32 => true
          | _, _ => false
          end
      end
  | PtBool => match g with existT _ _ (pair _ tag) => match tag with TBool => true | _ => false end end
  | PtStr  => match g with existT _ _ (pair _ tag) => match tag with TString => true | _ => false end end
  | PtIntConst _ | PtTIntConst _ _ | PtFloatConst _ _ | PtAgg | PtMap | PtNil => false
  end.

Local Definition rexit_tc (tc : GExpr -> option PTy) (leaf : string -> option GoAny) (rec : GExpr -> option RRes) (rv : GExpr -> option RAny) (e : GExpr) : option RAny :=
  match e with
  | EId x =>
      (* the EXIT EId leaf: a bound name at a NON-GTInt scalar category resolves
         to its environment value, tag-checked against the authority ([eid_exit_tag_ok]); the
         closed leaf resolves nothing, so the closed engine is unchanged. *)
      match leaf (proj1_sig x) with
      | None => None
      | Some g =>
          match tc e with
          | Some c => if eid_exit_tag_ok c g then Some (RAVal g) else None
          | None => None
          end
      end
  | ECall (EId f) (a :: nil) =>
      (* the EXIT conversion (non-[GTInt] integer target): the authority's [PtRunInt t] on a
         one-arg call must be a CONVERSION shape (closed instance: [ptype_call_runint_conv];
         [wrap_runint_total]).  The arg evaluates at full power; a non-integer-tagged source is
         absent at [runint_raw] (closed: [reval_val_runfloat_none]; env float locals:
         [env_float_conv_class]).  A panicking arg panics. *)
      match tc e with
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
      (* typed unary on a non-GTInt runtime carrier: [tc] pins the width, the arg evaluates at
         full power, [typed_unop] applies the width's model op; op-table holes are absent. *)
      match tc e with
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
      (* the bool COMPARISON exit ([cmp_width] picks the operand width; GTInt runs the engine
         path, a fixed width the typed path via the width-sealed [typed_operand]) and the
         SAME-WIDTH typed arithmetic/bitwise case ([typed_binop]; [div_checked] panics).
         Panics propagate left-to-right; hole rows are absent. *)
      match tc e with
      | Some PtBool =>
          match cmp_width (tc a) (tc b) with
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
                match typed_operand_tc tc rv t a with
                | Some (RAVal ga) =>
                    match typed_operand_tc tc rv t b with
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
          match typed_operand_tc tc rv t a with
          | Some (RAVal ga) =>
              if typed_arith_op o then
                match typed_operand_tc tc rv t b with
                | Some (RAVal gb) => typed_binop o t ga gb
                | Some (RAPanic p) => Some (RAPanic p)
                | None => None
                end
              else if shift_op o then
                (* tier T5 — the COUNT is read by the sealed count layer ([shift_count_tc]): a
                   CONSTANT count directly off the AUTHORITY'S own value (count exactness is an
                   instance obligation; total on the closed instance's admitted class), a RUNTIME
                   count at FULL power at ITS OWN width; the width-sealed left operand
                   feeds [typed_shift]. *)
                match shift_count_tc tc rv b with
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
Definition rexit_with : (GExpr -> option RRes) -> (GExpr -> option RAny) -> GExpr -> option RAny :=
  rexit_tc ptype leaf_closed.

Local Definition reval_val_tc (tc : GExpr -> option PTy) (leaf : string -> option GoAny) (rec : GExpr -> option RRes) : GExpr -> option RAny :=
  fix rv (e : GExpr) : option RAny :=
    match eval_value e with
    | Some v => Some (RAVal v)
    | None =>
        match rec e with
        | Some (RVal x)   => Some (RAVal (anyt TInt64 x))
        | Some (RPanic p) => Some (RAPanic p)
        | None => rexit_tc tc leaf rec rv e
        end
    end.
Definition reval_val_with : (GExpr -> option RRes) -> GExpr -> option RAny :=
  reval_val_tc ptype leaf_closed.
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
    the AUTHORITY for the order-independence claim (the fixtures, downstream in GoSem.v, are witnesses, not the guard):
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

Local Definition reval_int_tc (tc : GExpr -> option PTy) (leaf : string -> option GoAny) : GExpr -> option RRes :=
  fix ri (e : GExpr) : option RRes :=
  match eval_value e with
  | Some v => match unbox_int v with Some x => Some (RVal x) | None => None end
  | None =>
      match tc e with
      | Some (PtRunInt t) =>
          if negb (numty_eqb t GTInt) then None else
          match e with
          | EId x =>
              (* the GTInt EId leaf: a bound [int] name resolves to its
                 environment value through [unbox_int] (the TInt64 tag check); the closed leaf
                 resolves nothing. *)
              match leaf (proj1_sig x) with
              | Some g => match unbox_int g with Some v => Some (RVal v) | None => None end
              | None => None
              end
          | ECall (EId f) (ESliceLit et es :: nil) =>
              if String.eqb (proj1_sig f) "len" && is_int_goty et
              then match reval_elems_with ri es with
                   | Some (REVals vs)  => rval_len (length vs)
                   | Some (REPanic p)  => Some (RPanic p)   (* a panicking element ABORTS construction *)
                   | None => None
                   end
              else None
          | ECall (EId f) (EMapLit kt vt kvs :: nil) =>
              (* [len] of a map literal with runtime VALUES: construct (every entry, unspecified
                 order) then count DISTINCT keys ([nodup_z] over the authority's key list — key
                 exactness is an instance obligation).  Values evaluate through the FULL shared
                 evaluator; one panicking value panics, two-plus/absent -> absent (order
                 unspecified — the walker's class theorems). *)
              if String.eqb (proj1_sig f) "len" && is_int_goty kt && goty_supported vt
                 && nodup_z (map_key_vals_with tc kvs)
              then match rconstr_vals_with (reval_val_tc tc leaf ri) kvs with
                   | Some RCOk        => rval_len (length kvs)
                   | Some (RCPanic p) => Some (RPanic p)
                   | None => None
                   end
              else None
          | ECall (EId f) (a :: nil) =>
              (* [int(x)] — conversion INTO [int] via [intwrap] on the carrier's raw value; the
                 arg evaluates at full power.  A non-integer-tagged source is absent at
                 [runint_raw] (closed: [reval_val_runfloat_none]; env floats:
                 [env_float_conv_class]).  Non-[GTInt] targets exit in [rexit_with]. *)
              if String.eqb (proj1_sig f) "int"
              then match reval_val_tc tc leaf ri a with
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
              (* the RUNTIME slice INDEX: literal construction (abort on a panicking element),
                 then the index; OOB panics with the model's exact [rt_index_oob] payload. *)
              match reval_elems_with ri es with
              | Some (REVals vs) =>
                  match ri idx with
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
                (* the GTInt SHIFT: LEFT first (Go's order), the COUNT via the sealed count
                   layer ([shift_count_tc]), then the checked convoy ([int_shift_checked]:
                   negative count panics, >= 64 saturates). *)
                match ri a with
                | Some (RVal va) =>
                    match shift_count_tc tc (reval_val_tc tc leaf ri) b with
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
              match ri a, ri b with
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
              (* runtime unary minus ([int_neg], wraps like Go) and complement ([int_not]);
                 [!] is bools-only — absent here. *)
              match o with
              | UNeg =>
                  match ri a with
                  | Some (RVal v) => Some (RVal (int_neg v))
                  | other => other
                  end
              | UXor =>
                  match ri a with
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

Definition reval_int : GExpr -> option RRes := reval_int_tc ptype leaf_closed.

(** Post-[cbn] normalizer: [cbn] refolds the engines' inner fixes to the CLOSED names
    but leaves the [_tc]-of-[ptype] wrapper applications; these [change]s put a goal/hypothesis
    back in the closed vocabulary (pure conversions — each closed name IS its [_tc ptype]
    instantiation by definition). *)
Local Ltac fold_tc :=
  repeat first
    [ progress change (reval_val_tc ptype leaf_closed reval_int) with (reval_val_with reval_int)
    | progress change (map_key_vals_with ptype) with map_key_vals
    | progress change (shift_count_tc ptype) with shift_count
    | progress change (typed_operand_tc ptype) with typed_operand
    | progress change (rexit_tc ptype leaf_closed) with rexit_with ].
Local Ltac fold_tc_in H :=
  repeat first
    [ progress change (reval_val_tc ptype leaf_closed reval_int) with (reval_val_with reval_int) in H
    | progress change (map_key_vals_with ptype) with map_key_vals in H
    | progress change (shift_count_tc ptype) with shift_count in H
    | progress change (typed_operand_tc ptype) with typed_operand in H
    | progress change (rexit_tc ptype leaf_closed) with rexit_with in H ].

(** ===== The ENV instance: [GoSafe.tcat G] + the value environment [env_get ρ], constructed
    behind the [_tc] seal.  At the EMPTY scope and env it IS the closed evaluator
    ([denote_expr_env_nil] — engines' extensionality + the [tcat_nil_ptype] bridge), so the
    spellings cannot drift.  The statement layer that BUILDS ρ is ABSENT;
    [denote_stmt (GsShortDecl _ _)] is [None]. *)
Definition Env : Type := list (string * GoAny).
Fixpoint env_get (ρ : Env) (x : string) : option GoAny :=
  match ρ with
  | nil => None
  | (n, g) :: ρ' => if String.eqb n x then Some g else env_get ρ' x
  end.
Local Definition reval_int_env (G : ScopeS) (ρ : Env) : GExpr -> option RRes :=
  reval_int_tc (tcat G) (env_get ρ).
Local Definition reval_val_env (G : ScopeS) (ρ : Env) : GExpr -> option RAny :=
  reval_val_tc (tcat G) (env_get ρ) (reval_int_env G ρ).
Definition denote_expr_env (G : ScopeS) (ρ : Env) (e : GExpr) : option (Cmd GoAny * bool) :=
  if negb (floats_checked e) then None else
  match reval_val_env G ρ e with
  | Some (RAVal v)   => Some (CRet v, false)
  | Some (RAPanic p) => Some (CPan p, true)
  | None => None
  end.

(** ENGINE EXTENSIONALITY — the engines only APPLY their authority/leaf, so pointwise-equal
    parameters give EQUAL engines (mutual statement = what the guard accepts).  Connects the env
    instance to the closed engine WITHOUT funext. *)
Local Lemma reval_engines_ext :
  forall (tc1 tc2 : GExpr -> option PTy) (l1 l2 : string -> option GoAny),
  (forall e, tc1 e = tc2 e) ->
  (forall x, l1 x = l2 x) ->
  forall e,
    reval_int_tc tc1 l1 e = reval_int_tc tc2 l2 e
    /\ reval_val_tc tc1 l1 (reval_int_tc tc1 l1) e
       = reval_val_tc tc2 l2 (reval_int_tc tc2 l2) e.
Proof.
  intros tc1 tc2 l1 l2 Htc Hl.
  fix IH 1. intro e.
  assert (Hval_of_int : reval_int_tc tc1 l1 e = reval_int_tc tc2 l2 e ->
            (rexit_tc tc1 l1 (reval_int_tc tc1 l1) (reval_val_tc tc1 l1 (reval_int_tc tc1 l1)) e
             = rexit_tc tc2 l2 (reval_int_tc tc2 l2) (reval_val_tc tc2 l2 (reval_int_tc tc2 l2)) e) ->
            reval_val_tc tc1 l1 (reval_int_tc tc1 l1) e
            = reval_val_tc tc2 l2 (reval_int_tc tc2 l2) e).
  { intros Hint Hexit. destruct e; cbn [reval_val_tc];
      (destruct (eval_value _) as [?|]; [reflexivity|]);
      rewrite Hint; destruct (reval_int_tc tc2 l2 _) as [[?|?]|]; try reflexivity; exact Hexit. }
  destruct e as [i|z|o e0|o l r|e0 f|e0 idx|e0 lo hi|e0 args|e0 T|c e0|t es|kt vt kvs|str|zc];
    try (split;
          [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
          | apply Hval_of_int;
            [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
            | cbn [rexit_tc]; rewrite ?Htc, ?Hl; reflexivity ] ]).
  - (* EUn *)
    split;
      [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?(proj1 (IH e0)); reflexivity
      | apply Hval_of_int;
        [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?(proj1 (IH e0)); reflexivity
        | cbn [rexit_tc]; rewrite ?Htc, ?Hl, ?(proj2 (IH e0)); reflexivity ] ].
  - (* EBn *)
    split;
      [ cbn [reval_int_tc]; unfold shift_count_tc;
        rewrite ?Htc, ?Hl, ?(proj1 (IH l)), ?(proj1 (IH r)), ?(proj2 (IH r)); reflexivity
      | apply Hval_of_int;
        [ cbn [reval_int_tc]; unfold shift_count_tc;
          rewrite ?Htc, ?Hl, ?(proj1 (IH l)), ?(proj1 (IH r)), ?(proj2 (IH r)); reflexivity
        | cbn [rexit_tc]; unfold typed_operand_tc, shift_count_tc;
          rewrite ?Htc, ?Hl, ?(proj1 (IH l)), ?(proj1 (IH r)),
                  ?(proj2 (IH l)), ?(proj2 (IH r)); reflexivity ] ].
  - (* EIndex *)
    destruct e0 as [ | | | | | | | | | |et l| | | ];
      try (split;
            [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
            | apply Hval_of_int;
              [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
              | cbn [rexit_tc]; rewrite ?Htc, ?Hl; reflexivity ] ]).
    assert (Hels : reval_elems_with (reval_int_tc tc1 l1) l
                   = reval_elems_with (reval_int_tc tc2 l2) l).
    { clear Hval_of_int. induction l as [|el l' IHl']; cbn [reval_elems_with]; [reflexivity|].
      rewrite (proj1 (IH el)), IHl'.
      destruct (reval_int_tc tc2 l2 el) as [[?|?]|]; reflexivity. }
    split;
      [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hels, ?(proj1 (IH idx)); reflexivity
      | apply Hval_of_int;
        [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hels, ?(proj1 (IH idx)); reflexivity
        | cbn [rexit_tc]; rewrite ?Htc, ?Hl; reflexivity ] ].
  - (* ECall *)
    destruct e0 as [i| | | | | | | | | | | | | ];
      try (destruct args as [|a0 [|b0 args']];
            (split;
             [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
             | apply Hval_of_int;
               [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
               | cbn [rexit_tc]; rewrite ?Htc, ?Hl; reflexivity ] ])).
    destruct args as [|a [|b0 args']];
      try (split;
            [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
            | apply Hval_of_int;
              [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl; reflexivity
              | cbn [rexit_tc]; rewrite ?Htc, ?Hl; reflexivity ] ]).
    pose proof (proj2 (IH a)) as Hva.
    destruct a as [ | | | | | | | | | |et l|mkt mvt kvl| | ];
      try (split;
            [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hva; reflexivity
            | apply Hval_of_int;
              [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hva; reflexivity
              | cbn [rexit_tc]; rewrite ?Htc, ?Hl, ?Hva; reflexivity ] ]).
    + (* a = ESliceLit *)
      assert (Hels : reval_elems_with (reval_int_tc tc1 l1) l
                     = reval_elems_with (reval_int_tc tc2 l2) l).
      { clear Hval_of_int Hva. induction l as [|el l' IHl']; cbn [reval_elems_with]; [reflexivity|].
        rewrite (proj1 (IH el)), IHl'.
        destruct (reval_int_tc tc2 l2 el) as [[?|?]|]; reflexivity. }
      split;
        [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hels, ?Hva; reflexivity
        | apply Hval_of_int;
          [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hels, ?Hva; reflexivity
          | cbn [rexit_tc]; rewrite ?Htc, ?Hl, ?Hva; reflexivity ] ].
    + (* a = EMapLit *)
      assert (Hmk : map_key_vals_with tc1 kvl = map_key_vals_with tc2 kvl).
      { clear Hval_of_int Hva. unfold map_key_vals_with.
        induction kvl as [|[k v] kvl' IHkv]; cbn; [reflexivity|].
        rewrite ?Htc, ?IHkv. reflexivity. }
      assert (Hcv : rconstr_vals_with (reval_val_tc tc1 l1 (reval_int_tc tc1 l1)) kvl
                    = rconstr_vals_with (reval_val_tc tc2 l2 (reval_int_tc tc2 l2)) kvl).
      { clear Hval_of_int Hva Hmk. induction kvl as [|[k v] kvl' IHkv]; cbn [rconstr_vals_with]; [reflexivity|].
        rewrite (proj2 (IH v)).
        destruct (reval_val_tc tc2 l2 (reval_int_tc tc2 l2) v) as [[?|?]|];
          first [ reflexivity | exact IHkv | rewrite IHkv; reflexivity ]. }
      split;
        [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hmk, ?Hcv, ?Hva; reflexivity
        | apply Hval_of_int;
          [ cbn [reval_int_tc]; rewrite ?Htc, ?Hl, ?Hmk, ?Hcv, ?Hva; reflexivity
          | cbn [rexit_tc]; rewrite ?Htc, ?Hl, ?Hva; reflexivity ] ].
Qed.
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

(** THE CLOSED COINCIDENCE — the env spelling at the EMPTY scope/env IS the closed evaluator
    (pointwise, funext-free).  Registered in [gosem_core_surface]. *)
Theorem denote_expr_env_nil : forall e, denote_expr_env scope_empty nil e = denote_expr e.
Proof.
  intro e. unfold denote_expr_env, denote_expr.
  destruct (negb (floats_checked e)); [reflexivity|].
  unfold reval_val_env, reval_int_env, reval_val_with, reval_int.
  rewrite (proj2 (reval_engines_ext (tcat scope_empty) ptype (env_get nil) leaf_closed
                    tcat_nil_ptype (fun x => eq_refl) e)).
  reflexivity.
Qed.

(** ENV pins: a bound [int] name resolves and computes; a TAG-FORGED environment and a FREE
    name are ABSENT. *)
Example env_eid_pins :
  match scope_declare scope_empty (mkIdent "x" eq_refl) (PtRunInt GTInt) with
  | Some G =>
      denote_expr_env G (("x"%string, anyt TInt64 (intwrap 5)) :: nil)
        (EId (mkIdent "x" eq_refl))
        = Some (CRet (anyt TInt64 (intwrap 5)), false)
      /\ denote_expr_env G (("x"%string, anyt TInt64 (intwrap 5)) :: nil)
           (EBn BAdd (EId (mkIdent "x" eq_refl)) (EInt 1))
           = Some (CRet (anyt TInt64 (intwrap 6)), false)
      /\ denote_expr_env G (("x"%string, anyt TBool true) :: nil)
           (EId (mkIdent "x" eq_refl)) = None
      /\ denote_expr_env G (("x"%string, anyt TInt64 (intwrap 5)) :: nil)
           (EId (mkIdent "y" eq_refl)) = None
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ENV FLOAT pins — direct evaluation + the forged-tag matrix, both widths (the closed
    runtime-float absence theorems are about the CLOSED instance only); the conversion face is
    [env_float_conv_class] below. *)
Example env_float_pins :
  match scope_declare scope_empty (mkIdent "f" eq_refl) (PtRunFloat GTFloat64),
        scope_declare scope_empty (mkIdent "g" eq_refl) (PtRunFloat GTFloat32) with
  | Some G64, Some G32 =>
      denote_expr_env G64 (("f"%string, anyt TFloat64 (S754_zero false)) :: nil)
        (EId (mkIdent "f" eq_refl))
        = Some (CRet (anyt TFloat64 (S754_zero false)), false)
      /\ denote_expr_env G32 (("g"%string, anyt TFloat32 (f32_lit (S754_zero false))) :: nil)
           (EId (mkIdent "g" eq_refl))
           = Some (CRet (anyt TFloat32 (f32_lit (S754_zero false))), false)
      /\ denote_expr_env G64 (("f"%string, anyt TFloat32 (f32_lit (S754_zero false))) :: nil)
           (EId (mkIdent "f" eq_refl)) = None
      /\ denote_expr_env G64 (("f"%string, anyt TInt64 (intwrap 5)) :: nil)
           (EId (mkIdent "f" eq_refl)) = None
      /\ denote_expr_env G32 (("g"%string, anyt TFloat64 (S754_zero false)) :: nil)
           (EId (mkIdent "g" eq_refl)) = None
      /\ denote_expr_env G32 (("g"%string, anyt TInt64 (intwrap 5)) :: nil)
           (EId (mkIdent "g" eq_refl)) = None
  | _, _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ★ THE ENV FLOAT CONVERSION CLASS — quantified over the LIVE conversion-head authority
    ([special_ident]'s image), BOTH widths, and EVERY payload: an integer-keyword conversion of
    a float-bound local is ABSENT (TAG-driven — [runint_raw] never reads the payload).
    [special_ident_name] pins each head's string; no parallel keyword list exists.  Env shape =
    the single well-tagged binding; forged tags are [env_float_pins]' matrix. *)
Example env_float_conv_class :
  forall (i : Ident) (t : GoTy) (v64 : GoFloat64) (v32 : GoFloat32),
  special_ident (proj1_sig i) = Some (SnType t) ->
  is_int_goty t = true ->
  match scope_declare scope_empty (mkIdent "f" eq_refl) (PtRunFloat GTFloat64),
        scope_declare scope_empty (mkIdent "g" eq_refl) (PtRunFloat GTFloat32) with
  | Some G64, Some G32 =>
      denote_expr_env G64 (("f"%string, anyt TFloat64 v64) :: nil)
        (ECall (EId i) (EId (mkIdent "f" eq_refl) :: nil)) = None
      /\ denote_expr_env G32 (("g"%string, anyt TFloat32 v32) :: nil)
           (ECall (EId i) (EId (mkIdent "g" eq_refl) :: nil)) = None
  | _, _ => False
  end.
Proof.
  intros [s Hi] t v64 v32 Hsi Hit.
  cbn [proj1_sig] in Hsi.
  pose proof (special_ident_name _ _ Hsi) as Hs.
  destruct t; try discriminate Hit; cbn [special_name_string] in Hs; subst s;
    vm_compute; split; reflexivity.
Qed.

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
       unfold reval_val_with, reval_val_tc; rewrite Hev, Hgoal; reflexivity ].
  cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb].
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
    [runtime_index_runs]/[slice_index_panics_denote], downstream in GoSem.v, are witnesses of
    these classes, not the claim).
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes, Hidx, Hb, Hnth. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes, Hidx, Hb. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb].
    unfold reval_elems in Hes. rewrite Hes, Hidx. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
Qed.

(** ★ CLASS (tiers R3+T2) — the WIDTH-CONVERSION denotation theorems, quantified over the whole
    reval-evaluable fragment (T2: the source is ANY full-evaluator value — chains through non-[GTInt]
    intermediates included) and SEALED to [ptype]'s own boundary: any one-arg call classified
    [PtRunInt t] with [t ≠ GTInt] is NECESSARILY a [conv_to_scalar] conversion to an INTEGER keyword
    target ([ptype_call_runint_conv] — the [SnLen]/[SnCap] table rows yield only [GTInt], so a
    non-[GTInt] width excludes them; [classify] covers scalar conversion keywords only), whose OPERAND is runtime-int- or
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
  destruct (special_ident (proj1_sig f)) as [sn|]; [|discriminate].
  destruct sn as [t'| | | | | |].
  - exact (proj2 (conv_to_scalar_runint ca t' t H)).
  - discriminate H.
  - destruct a; destruct ca; try discriminate H;
      inversion H; subst; discriminate Ht.
  - destruct ca; try discriminate H. inversion H; subst. discriminate Ht.
  - discriminate H.
  - discriminate H.
  - discriminate H.
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
  destruct (special_ident (proj1_sig f)) as [sn|]; [|discriminate].
  destruct sn as [t'| | | | | |].
  - destruct (conv_to_scalar_runint_src ca t' t H) as [[s ->]|[s ->]];
      [left|right]; exists s; reflexivity.
  - discriminate H.
  - destruct a; destruct ca; try discriminate H;
      inversion H; subst; discriminate Ht.
  - destruct ca; try discriminate H. inversion H; subst. discriminate Ht.
  - discriminate H.
  - discriminate H.
  - discriminate H.
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
  destruct (special_ident (proj1_sig f)) as [[t'| | | | | |]|]; cbv beta iota in H;
    [ rewrite conv_to_scalar_agg_none in H; discriminate H   (* SnType *)
    | discriminate H                                         (* SnNil *)
    | injection H as <-; reflexivity                         (* SnLen *)
    | injection H as <-; reflexivity                         (* SnCap: [cap] of PtAgg *)
    | discriminate H | discriminate H | discriminate H | discriminate H ].
Qed.
Lemma ptype_call_maplit_shape : forall f kt vt kvs p,
  ptype (ECall (EId f) (EMapLit kt vt kvs :: nil)) = Some p -> p = PtRunInt GTInt.
Proof.
  intros f kt vt kvs p H. cbn [ptype] in H.
  match type of H with
  | context [if ?b then Some PtMap else None] => destruct b
  end; cbv beta iota in H; [|discriminate H].
  destruct (special_ident (proj1_sig f)) as [[t'| | | | | |]|]; cbv beta iota in H;
    [ rewrite conv_to_scalar_map_none in H; discriminate H   (* SnType *)
    | discriminate H                                         (* SnNil *)
    | injection H as <-; reflexivity                         (* SnLen: [len] of PtMap *)
    | discriminate H                                         (* SnCap: [cap] of a map is rejected *)
    | discriminate H | discriminate H | discriminate H | discriminate H ].
Qed.
Lemma classify_gtint_name : forall s, classify s = Some GTInt -> String.eqb s "int" = true.
Proof.
  intros s H. unfold classify, special_ident in H.
  destruct (String.eqb s "int64"); [discriminate H|].
  destruct (String.eqb s "int32"); [discriminate H|].
  destruct (String.eqb s "int16"); [discriminate H|].
  destruct (String.eqb s "int8");  [discriminate H|].
  destruct (String.eqb s "int") eqn:E; [reflexivity|].
  destruct (String.eqb s "uint64");  [discriminate H|].
  destruct (String.eqb s "uint32");  [discriminate H|].
  destruct (String.eqb s "uint16");  [discriminate H|].
  destruct (String.eqb s "uint8");   [discriminate H|].
  destruct (String.eqb s "uint");    [discriminate H|].
  destruct (String.eqb s "bool");    [discriminate H|].
  destruct (String.eqb s "string");  [discriminate H|].
  destruct (String.eqb s "float64"); [discriminate H|].
  destruct (String.eqb s "float32"); [discriminate H|].
  destruct (String.eqb s "nil");     [discriminate H|].
  destruct (String.eqb s "len");     [discriminate H|].
  destruct (String.eqb s "cap");     [discriminate H|].
  destruct (String.eqb s "println"); [discriminate H|].
  destruct (String.eqb s "print");   [discriminate H|].
  destruct (String.eqb s "panic");   [discriminate H|].
  discriminate H.
Qed.
(** A [PtRunInt GTInt]-classified one-arg call with a RUNTIME-INT operand IS the [int(x)] conversion
    (the [SnLen]/[SnCap] table rows contradict the operand's class; [classify_gtint_name] pins the name) — so the sealed
    [int]-target theorem below needs NO name premise. *)
Lemma ptype_call_runint_int_name : forall f a s,
  ptype (ECall (EId f) (a :: nil)) = Some (PtRunInt GTInt) ->
  ptype a = Some (PtRunInt s) ->
  String.eqb (proj1_sig f) "int" = true.
Proof.
  intros f a s H Hpa. cbn [ptype] in H. rewrite Hpa in H. cbv beta iota in H.
  destruct (special_ident (proj1_sig f)) as [sn|] eqn:Hsn; cbv beta iota in H; [|discriminate H].
  destruct sn as [t'| | | | | |]; cbv beta iota in H.
  - assert (Ecl : classify (proj1_sig f) = Some t')
      by (unfold classify; rewrite Hsn; reflexivity).
    destruct (conv_to_scalar_runint _ _ _ H) as [-> _].
    exact (classify_gtint_name _ Ecl).
  - discriminate H.
  - destruct a; cbv beta iota in H; discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
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
    destruct (special_ident (proj1_sig f)) as [[t'| | | | | |]|]; cbv beta iota in H;
      [ rewrite conv_to_scalar_agg_none in H; discriminate H
      | discriminate H | discriminate H | discriminate H
      | discriminate H | discriminate H | discriminate H | discriminate H ].
  - (* EMapLit *)
    match type of H with
    | context [if ?b then Some PtMap else None] => destruct b
    end; cbv beta iota in H; [|discriminate H].
    destruct (special_ident (proj1_sig f)) as [[t'| | | | | |]|]; cbv beta iota in H;
      [ rewrite conv_to_scalar_map_none in H; discriminate H
      | discriminate H | discriminate H | discriminate H
      | discriminate H | discriminate H | discriminate H | discriminate H ].
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
    cbn [rexit_with rexit_tc]; fold_tc; try reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (ECall (EId f) (a :: nil))
                = Some (RAVal g')).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (ECall (EId f) (a :: nil))
                = Some (RAPanic p)).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, He. cbv beta iota.
  unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, He. cbv beta iota.
  unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, He. cbv beta iota.
  unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbn [numty_eqb negb].
    rewrite Hcond. cbv beta iota.
    unfold rconstr_vals in Hvals. rewrite Hvals. cbv beta iota.
    exact (rval_len_repr (length kvs) Hrepr). }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbn [numty_eqb negb].
    rewrite Hcond. cbv beta iota.
    unfold rconstr_vals in Hvals. rewrite Hvals. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  - (* EId *) destruct (special_ident _) as [[?| | | | | |]|];
      first [ injection Hp as <-; reflexivity | discriminate Hp ].
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
    destruct (special_ident (proj1_sig i)) as [sn|]; [|discriminate Hp].
    destruct sn as [t'| | | | | |].
    + exact (conv_to_scalar_int_ok _ _ _ Hp).                     (* SnType *)
    + discriminate Hp.                                            (* SnNil *)
    + destruct a; try destruct ca; try discriminate Hp; injection Hp as <-; reflexivity.  (* SnLen *)
    + destruct ca; try discriminate Hp. injection Hp as <-. reflexivity.                  (* SnCap *)
    + discriminate Hp.
    + discriminate Hp.
    + discriminate Hp.
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
  intros a r Hev Hr; destruct a; cbn [reval_int reval_int_tc] in Hr; fold_tc_in Hr; rewrite Hev in Hr; cbv beta iota in Hr;
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
      apply String.eqb_eq in El'. rewrite El' in Hpt. cbn in Hpt.
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
      apply String.eqb_eq in El'. rewrite El' in Hpt. cbn in Hpt.
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
    cbn [rexit_with rexit_tc] in Hg; fold_tc_in Hg; try discriminate Hg.
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
(** THE RUNTIME-FLOAT ABSENCE CLASS THEOREM (CLOSED evaluator level — [ptype]/[reval_val]; the ENV
    instance DOES evaluate a float LOCAL through the EId arm, [env_float_pins]): NO
    [PtRunFloat]-classified expression evaluates in the CLOSED instance — not the fold
    ([eval_value_runfloat_none]), not the [GTInt] engine (its [PtRunInt]
    guard), not an exit (each arm's [ptype]/[PtBool] guard).  QUANTIFIED over the class, so no
    consumer — a conversion source, a map value, a typed-unary operand — can receive a runtime-float
    value before the float arc models one. *)
Theorem reval_val_runfloat_none : forall a s,
  ptype a = Some (PtRunFloat s) -> reval_val a = None.
Proof.
  intros a s Hpt. unfold reval_val. rewrite reval_val_with_eq.
  rewrite (eval_value_runfloat_none a s Hpt).
  assert (Hri : reval_int a = None).
  { destruct a; cbn [reval_int reval_int_tc]; fold_tc;
      rewrite (eval_value_runfloat_none _ _ Hpt); cbv beta iota;
      rewrite Hpt; reflexivity. }
  rewrite Hri. cbv beta iota.
  destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
    cbn [rexit_with rexit_tc]; fold_tc; try reflexivity.
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
  intros rv t s e Hpt Hn. unfold typed_operand, typed_operand_tc. rewrite Hpt, Hn. reflexivity.
Qed.
Lemma typed_operand_typed : forall t e g,
  is_int_goty t = true ->
  (ptype e = Some (PtRunInt t)
   \/ (exists z, ptype e = Some (PtIntConst z) \/ ptype e = Some (PtTIntConst t z))) ->
  typed_operand reval_val t e = Some (RAVal g) ->
  tag_matches t g = true.
Proof.
  intros t e g Hi Hc H; unfold typed_operand, typed_operand_tc in H.
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
  intros t e z Hi Hu Hc. unfold typed_operand, typed_operand_tc.
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
  intros rv t e p H. unfold typed_operand, typed_operand_tc in H.
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
  exists z. unfold shift_count, shift_count_tc. rewrite Hpt, Hb, Hz. reflexivity.
Qed.
(** ★ CONST-count TOTALITY from the GATE ALONE — no evaluation premise, for ANY evaluator, and
    the count is EXACTLY [ptype]'s own value: the direct read makes it impossible for the count
    layer to leak a gate-admitted constant (the side-condition-leak class killed
    structurally, not per-witness). *)
Lemma shift_count_const_total : forall rv b c z,
  ptype b = Some c -> int_const_val c = Some z ->
  shift_count rv b = Some (inl z).
Proof.
  intros rv b c z Hpt Hic. unfold shift_count, shift_count_tc. rewrite Hpt.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EUn o a) = Some (RAVal g')).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EUn o a) = Some (RAPanic p)).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
    ([wrap_runint_total]).  The [PtRunFloat] complement is CLASS-absent in the CLOSED instance
    ([denote_expr_conv_float_src_absent] below, on [reval_val_runfloat_none]; supported-side witness
    [runtime_float_source_conv_absent]; the ENV conversion-absence face, payload-general, is
    [env_float_conv_class]) — the float arc, not this one. *)
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
    cbn [numty_eqb negb]. cbv beta iota.
    destruct a as [i|z0|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      cbv beta iota;
      try (rewrite Hfeq; cbv beta iota; rewrite Ha; cbv beta iota; rewrite Hz; reflexivity).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He. reflexivity.
Qed.

(** ★ THE RUNTIME-FLOAT SOURCE CLASS THEOREM (CLOSED instance) — the [PtRunFloat] half of
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
    destruct (numty_eqb t GTInt); cbn [negb]; cbv beta iota; [|reflexivity].
    destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      cbv beta iota;
      try (destruct (String.eqb (proj1_sig f) "int"); cbv beta iota;
           [rewrite Hrv; reflexivity | reflexivity]).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  rewrite reval_val_with_eq, Hev, Hri. cbv beta iota.
  cbn [rexit_with rexit_tc]; fold_tc. rewrite Hpt. cbv beta iota.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
    destruct (numty_eqb t GTInt); cbn [negb]; cbv beta iota; [|reflexivity].
    destruct a as [i|z|o a0|o l r|e0 fld|e1 e2|e1 e2 e3|fn args|e0 ty|c e0|et es|kt vt kvs|str|hx];
      cbv beta iota;
      try (destruct (String.eqb (proj1_sig f) "int"); cbv beta iota;
           [rewrite Hrv; reflexivity | reflexivity]).
    - pose proof (ptype_slicelit_shape _ _ _ Hpa) as E; discriminate E.
    - pose proof (ptype_maplit_shape _ _ _ _ Hpa) as E; discriminate E. }
  rewrite reval_val_with_eq, Hev, Hri. cbv beta iota.
  cbn [rexit_with rexit_tc]; fold_tc. rewrite Hpt. cbv beta iota.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota. rewrite Hpt. cbv beta iota.
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
    [GTUint] is the hole row ([typed_binop_uint_none], pinned in [typed_uint_hole_programs_absent]);
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some r).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some (RAPanic p)).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some (RAPanic p)).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  rewrite reval_val_with_eq, Hev, He. cbv beta iota.
  cbn [rexit_with rexit_tc]; fold_tc. rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
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
    [typed_uint_hole_programs_absent]); the [GTInt] width is the R4 engine path. *)
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAVal (anyt TBool v))).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold reval_val in Ha.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAPanic p)).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold reval_val in Ha, Hb.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAPanic p)).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  rewrite reval_val_with_eq, Hev, He. cbv beta iota.
  cbn [rexit_with rexit_tc]; fold_tc. rewrite Hpt. cbv beta iota. rewrite Hw. cbv beta iota.
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
    ([typed_shift_uint_none], pinned in [typed_uint_hole_programs_absent]); an untyped-const LEFT
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hcnt.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b) = Some r).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  unfold reval_val in Ha, Hcnt.
  assert (Hrx : rexit_with reval_int (reval_val_with reval_int) (EBn o a b)
                = Some (RAPanic p)).
  { unfold rexit_with, rexit_tc. cbv beta iota. fold_tc.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev. cbv beta iota.
    rewrite Hpt. cbv beta iota. rewrite Ht.
    cbv beta iota delta [negb]. reflexivity. }
  rewrite reval_val_with_eq, Hev, He. cbv beta iota.
  cbn [rexit_with rexit_tc]; fold_tc. rewrite Hpt. cbv beta iota. rewrite Ht. cbv beta iota.
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
Example cmp_verdict_model_rows :
  (cmp_verdict BEq = Some Fido.builtins.int_eqb)
  /\ (cmp_verdict BNe = Some (fun x y => negb (Fido.builtins.int_eqb x y)))
  /\ (cmp_verdict BLt = Some Fido.builtins.int_ltb)
  /\ (cmp_verdict BLe = Some Fido.builtins.int_leb)
  /\ (cmp_verdict BGt = Some (fun x y => Fido.builtins.int_ltb y x))
  /\ (cmp_verdict BGe = Some (fun x y => Fido.builtins.int_leb y x)).
Proof. repeat split; reflexivity. Qed.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha, Hb.
    assert (K : forall (z : bool) (pf0 : Z.eqb (intraw vb) 0 = z), z = false ->
              (match z as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
               | true  => fun _   => Some (RPanic rt_div_zero)
               | false => fun pf1 => Some (RVal (int_div va vb pf1))
               end) pf0 = Some (RVal (int_div va vb pf))).
    { intros z pf0 Hz. destruct z; [discriminate Hz|].
      unfold int_div. reflexivity. }
    exact (K _ eq_refl pf). }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha, Hb.
    assert (K : forall (z : bool) (pf0 : Z.eqb (intraw vb) 0 = z), z = false ->
              (match z as z0 return Z.eqb (intraw vb) 0 = z0 -> option RRes with
               | true  => fun _   => Some (RPanic rt_div_zero)
               | false => fun pf1 => Some (RVal (int_mod va vb pf1))
               end) pf0 = Some (RVal (int_mod va vb pf))).
    { intros z pf0 Hz. destruct z; [discriminate Hz|].
      unfold int_mod. reflexivity. }
    exact (K _ eq_refl pf). }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
Qed.
(** ---- Tier R8 sealed — the GTInt BITWISE + SHIFT rows ----
    DISPATCH AUTHORITY (gated): each live row IS, by reflexivity, the FULLY QUALIFIED model op —
    a rerouted row breaks a pin and fails the build. *)
Example int_bitop_model_rows :
  (int_bitop BAnd    = Some Fido.builtins.int_and)
  /\ (int_bitop BOr     = Some Fido.builtins.int_or)
  /\ (int_bitop BXor    = Some Fido.builtins.int_xor)
  /\ (int_bitop BAndNot = Some Fido.builtins.int_andnot).
Proof. repeat split; reflexivity. Qed.
Example int_shift_op_model_rows :
  (int_shift_op BShl = Some Fido.builtins.int_shl)
  /\ (int_shift_op BShr = Some Fido.builtins.int_shr).
Proof. split; reflexivity. Qed.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha, Hb.
    destruct o; try discriminate Hop;
      cbn [int_bitop] in Hop; injection Hop as <-; reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha, Hb. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. cbv beta iota. rewrite Hcnt.
    cbv beta iota. rewrite Hop. cbv beta iota. exact Ev. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. cbv beta iota. rewrite Hcnt.
    cbv beta iota. rewrite Hop. cbv beta iota. exact Ep. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Hs.
    cbv beta iota. rewrite Ha. cbv beta iota. rewrite Hcnt. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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
  { cbn [reval_int reval_int_tc]; fold_tc. rewrite Hev, Hpt. cbn [numty_eqb negb]. rewrite Ha. reflexivity. }
  unfold denote_expr. rewrite Hfc. cbn [negb].
  cbv beta iota delta [reval_val_with reval_val_tc]. rewrite Hev, Hr. reflexivity.
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

(** Effectful ARGUMENT sequencing, left-to-right through [denote_expr], with a terminal flag: a
    PANICKING argument short-circuits (its [CPan] is the whole command; the remaining arguments —
    which Go never evaluates — are gated by the caller's [expr_stmt_ok], not required to denote).
    All-pure arguments reduce definitionally to [(CRet vs, false)]. *)
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

(** Call SCHEDULING — a sealed two-constructor mode (an arbitrary [Cmd unit -> Cmd unit] could
    erase a panic): [CallNow] runs now; [CallDeferred] registers via [CDfr]. *)
Inductive CallMode : Type := CallNow | CallDeferred.
Definition sched (m : CallMode) (c : Cmd unit) : Cmd unit :=
  match m with CallNow => c | CallDeferred => CDfr c (CRet tt) end.

(** The ONE call-shape authority, gated on [expr_stmt_ok] for BOTH consumers ([GsExprStmt] and
    [GsDefer]) — the deferred call can never denote differently from the immediate one.
    Arguments sequence OUTSIDE [sched] (Go evaluates deferred args AT DEFER TIME); the TERMINATES
    flag is computed from argument evaluation and scheduling. *)
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

(** ONE statement to its command + TERMINATES flag (the single control-flow authority —
    [denote_body] never re-decides; the flag is not derivable: [return] and a constant
    blank-assign both give [CRet tt] but differ stop/fall-through).  Effect arms go through
    [denote_call]; the inclusion ladder is [denote_call_ok] → [denote_stmt_sound] ([stmt_ok]) →
    [denote_body_sound] ([forallb stmt_ok]) → [gosem_sound] ([supported_program]). *)
Definition denote_stmt (s : GoStmt) : option (Cmd unit * bool) :=
  match s with
  | GsReturn        => Some (CRet tt, true)    (* TERMINATES the body *)
  | GsBlankAssign e =>
      (* [_ = e] discards the VALUE, not the EFFECTS: a determined runtime panic gives its TRUE
         [CPan] with [denote_expr]'s own terminal flag; [svalue e] keeps [denote] ⊆ the closed
         fragment. *)
      if svalue e then
        match denote_expr e with
        | Some (ce, eterm) => Some (cbind ce (fun _ => CRet tt), eterm)
        | None => None
        end
      else None
  | GsReturnVal _   => None                                        (* a value return is invalid in void [main] *)
  | GsExprStmt e    => denote_call CallNow e
  | GsDefer e =>
      (* [defer <call>] via [CDfr], Go's argument timing exact: args evaluate NOW (a panicking
         arg panics AT the defer statement); only the call-on-values is deferred ([run_defers],
         LIFO). *)
      denote_call CallDeferred e
  | GsShortDecl _ _ => None  (* the expression-level env instance exists ([denote_expr_env]); THIS statement arm is ABSENT — [supported_program] admits used locals, so decl programs are supported-but-undenoted ([shortdecl_supported_undenoted]) *)
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
               be in the CLOSED supported fragment ([forallb stmt_ok rest]; on decl-free bodies the scoped
               fold agrees exactly, [GoSafe.body_okS_nil_declfree]).  Keeps [denote_body] ⊆ [supported_program]
               ([gosem_sound]) while NOT making a terminator depend on a successor slice 1 cannot yet evaluate. *)
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
  intros s H. destruct s as [e| |e0|e|e|x v]; simpl in *.
  - exact (denote_call_ok CallNow e H).                      (* GsExprStmt: gated on [expr_stmt_ok] *)
  - reflexivity.                                             (* GsReturn *)
  - congruence.                                              (* GsReturnVal: None *)
  - destruct (svalue e); [reflexivity | congruence].         (* GsBlankAssign: gated on [svalue] = stmt_ok *)
  - exact (denote_call_ok CallDeferred e H).                 (* GsDefer: the SAME [expr_stmt_ok] gate *)
  - congruence.                                              (* GsShortDecl: None (absent; the CLOSED fragment rejects it too) *)
Qed.

(** The [GsShortDecl] ABSENCE pinned at the CONSTRUCTOR, for every ident/expression (the
    CLOSED-fragment rejection pin [GoSafe.shortdecl_stmt_ok_false] is its twin —
    [supported_program] ADMITS used decls; this pair is about slice 1's scope-free fragment). *)
Example shortdecl_denote_absent : forall x e, denote_stmt (GsShortDecl x e) = None.
Proof. reflexivity. Qed.

Lemma denote_body_sound : forall b, denote_body b <> None -> forallb stmt_ok b = true.
Proof.
  induction b as [|s rest IH]; simpl; intro H.
  - reflexivity.
  - destruct (denote_stmt s) as [[c term]|] eqn:Es; [|congruence].   (* denote_stmt s = None => denote_body = None *)
    apply andb_true_intro; split.
    + apply denote_stmt_sound. congruence.             (* stmt_ok s, uniform via [Es] *)
    + destruct term.                                   (* the [denote_stmt] flag: terminator gates rest on the CLOSED fragment; else on denotability *)
      * destruct (forallb stmt_ok rest) eqn:Ef; [reflexivity | congruence].
      * destruct (denote_body rest) eqn:Er; [|congruence]. apply IH. congruence.
Qed.

Theorem gosem_sound : forall p, denote_program p <> None -> supported_program p = true.
Proof.
  intros p H. unfold denote_program in H.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main") eqn:Epkg; [|congruence].
  exact (supported_program_of_stmt_ok p Epkg (denote_body_sound _ H)).
Qed.

(** SEAM pin: [supported_program] ADMITS a used local while the statement layer does not yet
    thread the env instance — SUPPORTED yet NOT denotable.  FLIPS when the env statement layer
    lands (swap per the frontier-pin discipline). *)
Example shortdecl_supported_undenoted :
  supported_program (mkProgram (mkIdent "main" eq_refl)
    [GsShortDecl (mkIdent "x" eq_refl) (EInt 1);
     GsBlankAssign (EId (mkIdent "x" eq_refl)); GsReturn]) = true
  /\ denote_program (mkProgram (mkIdent "main" eq_refl)
       [GsShortDecl (mkIdent "x" eq_refl) (EInt 1);
        GsBlankAssign (EId (mkIdent "x" eq_refl)); GsReturn]) = None.
Proof. split; vm_compute; reflexivity. Qed.

(** The TERMINATOR dead-tail face of the seam: a used-decl tail after [return] passes
    [supported_program] yet the dead-tail check is [forallb stmt_ok], so the body does NOT
    denote — terminator tails are gated on [stmt_ok], not [supported_program]. *)
Example shortdecl_deadtail_supported_undenoted :
  supported_program (mkProgram (mkIdent "main" eq_refl)
    [GsReturn; GsShortDecl (mkIdent "x" eq_refl) (EInt 1);
     GsBlankAssign (EId (mkIdent "x" eq_refl))]) = true
  /\ denote_program (mkProgram (mkIdent "main" eq_refl)
       [GsReturn; GsShortDecl (mkIdent "x" eq_refl) (EInt 1);
        GsBlankAssign (EId (mkIdent "x" eq_refl))]) = None.
Proof. split; vm_compute; reflexivity. Qed.

(** ---- DENOTABILITY IS DECIDABLE, characterized STRUCTURALLY (converse-direction companion of [gosem_sound]).
    [denotable_body] mirrors [denote_body]: a body denotes iff its head denotes AND — at a TERMINATOR — the
    unreachable rest is merely CLOSED-supported ([forallb stmt_ok], NOT live [supported_program]: a
    live-supported decl tail still blocks denotation — [shortdecl_deadtail_supported_undenoted]), else the
    rest is itself denotable; [denote_body_dec] proves they
    AGREE.  A CHARACTERIZATION result, NOT [supported ⟹ denotes]: the [denotable_*] ⊊ [supported_*] gap
    is REPRESENTATIVELY witnessed by [undenoted_frontier] (downstream in GoSem.v; see its own comment for what it does and
    does NOT cover) — a
    [GsDefer] now denotes exactly when its deferred call does. *)
Fixpoint denotable_body (b : list GoStmt) : bool :=
  match b with
  | [] => true
  | s :: rest =>
      match denote_stmt s with
      | None            => false
      | Some (_, true)  => forallb stmt_ok rest      (* terminator: the UNREACHABLE rest need only be CLOSED-supported ([stmt_ok]) *)
      | Some (_, false) => denotable_body rest        (* continuer: the rest must itself be DENOTABLE *)
      end
  end.

Theorem denote_body_dec : forall b, denote_body b <> None <-> denotable_body b = true.
Proof.
  induction b as [|s rest IH]; simpl.
  - split; intro H; congruence.                                       (* [] : Some (CRet tt) <> None and true = true *)
  - destruct (denote_stmt s) as [[c term]|] eqn:Es.
    + destruct term.
      * destruct (forallb stmt_ok rest); split; intro H; congruence.   (* terminator: gates rest on the closed fragment *)
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
    witnesses live in [undenoted_frontier] (downstream in GoSem.v), whose Coq definition is the ONLY member list (this
    comment deliberately enumerates none of it; NON-EXHAUSTIVE — no theorem bounds the gap).
    [denotable_supported] pins denotable ⊆ supported. *)
Definition folded_arg (e : GExpr) : bool :=
  match eval_value e with Some _ => printable_arg_ok e | None => false end.

Lemma folded_arg_eval : forall e, folded_arg e = true -> eval_value e <> None.
Proof. intros e H Hn. unfold folded_arg in H. rewrite Hn in H. discriminate. Qed.

Lemma folded_arg_printable : forall e, folded_arg e = true -> printable_arg_ok e = true.
Proof. intros e H. unfold folded_arg in H. destruct (eval_value e); [exact H | discriminate]. Qed.

(** String CONCATENATION and CONVERSIONS DENOTE (the [eval_value] folds are in [eval_value_good], downstream in GoSem.v; these pin the
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
    (pr=true) / [print] (pr=false) — both callees are admitted ([stmt_call_ok]), and [print] denotes identically with
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
    denotability is pinned in [gosem_denotability_decisions], downstream in GoSem.v. *)
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
    fixture spellings; the [eval_value_good] table, the [runtime_*_runs]/[rc_*] pins, and the
    pinned witness group for the gap ([undenoted_frontier]) are all downstream in GoSem.v. *)
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
    interleaved, including a terminator followed by (closed-supported) DEAD code.  SUFFICIENT, not necessary: a
    terminator's unreachable rest need only be CLOSED-supported ([stmt_ok]).  STILL CONDITIONAL on [stmt_denotable], NOT full
    [supported_program] — the gap is representatively witnessed by [undenoted_frontier] (downstream in GoSem.v; see its comment). *)
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
  - exact (forallb_stmt_denotable_ok rest Hrest).   (* terminator: unreachable rest need only be CLOSED-supported *)
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
    and a CLOSED-supported dead tail — and DENOTES by APPLYING the general converse (not a black-box compute). *)
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
  apply String.eqb_eq in Hf. rewrite Hf.
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
  apply String.eqb_eq in Hf. rewrite Hf.
  reflexivity.
Qed.
