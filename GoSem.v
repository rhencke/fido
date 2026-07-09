(** ============================================================================
    GoSem.v — the AST's BEHAVIORAL semantics as a BRIDGE into cmd.v (ARCHITECTURE.md §GoSem).
    No second universe: [denote_program : Program -> option (Cmd unit)] translates a GoAst program into
    cmd.v's proven command tree (reusing [run_cmd]/[cbind], the GoCompile gate, the model's own value
    ctors) — single-authority, faithful.

    SLICE 1 (partial): denotes println/print/panic/return/blank-assign/defer + effectful call args,
    over the exact-or-absent [eval_value] fold, the runtime GTInt tier R1–R8 (R8 = the engine's own
    bitwise + heterogeneous-shift rows), and the typed-runtime tier T1–T5 (ONE shared evaluator,
    [reval_val_with]; [denote_expr] is a thin wrapper).
    FAITHFUL-OR-ABSENT: the right behavior or [None] ("not modeled yet", never "invalid" and never
    wrong).  [gosem_sound]: denotation ⊆ [GoCompile]; NOT the converse, NOT [BehaviorSafe].
    Absence boundaries are PINNED, not prose — [gosem_frontier_surface] is the ONE gated authority,
    and its Coq definition is the ONLY member list (this header deliberately enumerates none of it).
    Public zero-axiom surfaces (topic-split, composed, manifest-gated): [gosem_trust_surface]
    (core / float / slice-index / runtime-int / map / frontier) + [gosem_string_authority_surface].
    Physical split (ARCHITECTURE.md §3a): GoSemCore.v = the pure fold/float layer; GoSemDenote.v =
    the whole denotation layer ([eval_value] + its [Local] core, the tiers, [denote_expr]/
    [denote_program], [gosem_sound], every class theorem).  THIS file re-exports both and keeps
    the program-level fixture GROUPS / demos / frontier + the gated SURFACES (the public
    authority); grounding examples stay adjacent to their theorems upstream.
    ============================================================================ *)
From Fido Require Import GoAst GoTypes GoCompile cmd preamble.   (* [preamble] declares the extraction ML plugins only *)
From Fido Require Import GoNumeric.
From Fido Require Import GoString.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoSlice.
From Fido Require Import GoPanic.
From Fido Require Export GoSemCore.
From Fido Require Export GoSemDenote.
From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.

(** ---- SLICE-INDEX fixtures (grouped; the CLASS theorems, upstream in GoSemDenote.v, are the authorities). ----
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
                 match denote_program (println_prog e) with Some c => run_cmd c w | None => None end))
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ runidx_e
      ; EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)
      ; EIndex (ESliceLit GTInt [EInt 10; EInt 20])
               (EBn BSub (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])
                         (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1; EInt 2]])) ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 20) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (OPanic (rt_index_oob (-1) 2) w) ].
Proof. intro w. vm_compute. reflexivity. Qed.

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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ runconv_e ; runconv_trunc_e ; runconv_int_e ; runconv_uint_e ; runconv_panic_e ]
  = [ Some (ORet tt (w_log true (anyt TI64 (i64wrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 300) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TUint (uintwrap (-1)) :: nil) w))   (* uint(-1 runtime) = 2^64-1: the [uintwrap] branch exercised at a WRAPPING value *)
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.

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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ maplen_runval_e ; maplen_run2_e ; maplen_i64_e ; maplen_bool_e
      ; maplen_panic_e ; maplen_convpanic_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 2) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (OPanic rt_div_zero w)
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
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
  go_compile_check gosem_maplen_divzero_prog = true
  /\ match denote_program gosem_maplen_divzero_prog with
     | Some c => run_cmd c w | None => None end = Some (OPanic rt_div_zero w).
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
  map (fun p => match denote_program p with Some c => run_cmd c w | None => None end)
      [println_prog runlen_e; println_prog runtime_div_vals_e; println_prog panicking_elem_len_e]
  = [Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w));
     Some (ORet tt (w_log true (anyt TInt64 (intwrap 3) :: nil) w));
     Some (OPanic rt_div_zero w)].
Proof. intro w. vm_compute. reflexivity. Qed.

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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ runneg_e ; runrem_e ; runrem_neg_e ; runneg_panic_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap (-3)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap (-1)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.

(** ★ R7 pins (grouped): runtime [^] COMPLEMENT via the model's [int_not] ([^len([]int{1,2,3})]
    prints -4 — the go-run-verified [-x-1]); a PANICKING operand propagates. *)
Definition runnot_e : GExpr := EUn UXor runlen3_e.
Definition runnot_panic_e : GExpr := EUn UXor divzero_e.
Example runtime_not_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ runnot_e ; runnot_panic_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap (-4)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.

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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ runnot_i64_e ; runnot_u8_e ; runneg_i64_e ; runnot_panic_i64_e ]
  = [ Some (ORet tt (w_log true (anyt TI64 (i64_not (i64wrap 3)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8  (u8_not  (u8wrap  3)) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TI64 (i64_neg (i64wrap 3)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example typed_unary_holes_absent :
  forallb (fun e => go_compile_check (println_prog e)
                    && negb (denotable_program (println_prog e))
                    && match denote_program (println_prog e) with None => true | Some _ => false end)
          [ runnot_uint_e
          ; runneg_uint_e ; runneg_u8_e ; runneg_i8_e ; runneg_u16_e
          ; runneg_i16_e ; runneg_u32_e ; runneg_i32_e ] = true.
Proof. vm_compute. reflexivity. Qed.
(** DISPATCH AUTHORITY (gated): each live [typed_unop] branch IS the fully qualified model op; the
    holes are sealed by the COMPLETE quantified theorem [typed_unop_holes_none] below. *)
Example typed_unop_model_rows :
  (forall v, typed_unop UXor GTU8  (anyt TU8  v) = Some (anyt TU8  (Fido.GoNumeric.u8_not v)))
  /\ (forall v, typed_unop UXor GTI8  (anyt TI8  v) = Some (anyt TI8  (Fido.GoNumeric.i8_not v)))
  /\ (forall v, typed_unop UXor GTU16 (anyt TU16 v) = Some (anyt TU16 (Fido.GoNumeric.u16_not v)))
  /\ (forall v, typed_unop UXor GTI16 (anyt TI16 v) = Some (anyt TI16 (Fido.GoNumeric.i16_not v)))
  /\ (forall v, typed_unop UXor GTU32 (anyt TU32 v) = Some (anyt TU32 (Fido.GoNumeric.u32_not v)))
  /\ (forall v, typed_unop UXor GTI32 (anyt TI32 v) = Some (anyt TI32 (Fido.GoNumeric.i32_not v)))
  /\ (forall v, typed_unop UXor GTInt64 (anyt TI64 v) = Some (anyt TI64 (Fido.GoNumeric.i64_not v)))
  /\ (forall v, typed_unop UXor GTU64 (anyt TU64 v) = Some (anyt TU64 (Fido.GoNumeric.u64_not v)))
  /\ (forall v, typed_unop UNeg GTInt64 (anyt TI64 v) = Some (anyt TI64 (Fido.GoNumeric.i64_neg v)))
  /\ (forall v, typed_unop UNeg GTU64 (anyt TU64 v) = Some (anyt TU64 (Fido.GoNumeric.u64_neg v))).
Proof. repeat split; intros; repeat split; reflexivity. Qed.
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ runconv_chain_e ; runconv_chain_int_e ; runconv_chain_trunc_e ]
  = [ Some (ORet tt (w_log true (anyt TI64 (i64wrap 3) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 3) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TI8 (i8wrap 252) :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
(** The RUNTIME-FLOAT SOURCE boundary: the ABSENCE is the gated CLASS pair, CLOSED-instance only
    ([reval_val_runfloat_none] — no [PtRunFloat]-classified expression evaluates in the CLOSED
    evaluator; an ENV float LOCAL evaluates, [env_float_pins];
    [denote_expr_conv_float_src_absent] — every integer-target conversion over such a source is
    absent, [GTInt] included).  This fixture pins what the class theorems cannot: the form is
    gate-SUPPORTED (supported-but-absent, the honest frontier membership) — flips when runtime
    floats land, not here. *)
Definition runconv_float_src_e : GExpr :=
  ECall (EId (mkIdent "int64" eq_refl))
        [ECall (EId (mkIdent "float64" eq_refl)) [runlen3_e]].
Example runtime_float_source_conv_absent :
  ptype runconv_float_src_e = Some (PtRunInt GTInt64)
  /\ go_compile_check (println_prog runconv_float_src_e) = true
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      typed_mixed_cases
  = [ Some (ORet tt (w_log true (anyt TU8 (u8wrap 4) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 4) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 4) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap (-2)) :: nil) w))
    ; Some (OPanic rt_div_zero w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
(** The WIDTH seal at the operand boundary ITSELF (not caller discipline): a typed [uint8] constant
    never cross-materializes at [int64], and the outer mixed-width binop is [ptype]-REJECTED. *)
Example typed_operand_cross_width_none :
  typed_operand reval_val GTInt64 runb_u8one = None.
Proof. vm_compute. reflexivity. Qed.
Example typed_binop_cross_width_rejected :
  ptype (EBn BAdd runb_u8one runb_i64) = None
  /\ go_compile_check (println_prog (EBn BAdd runb_u8one runb_i64)) = false.
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
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
(** The [GTUint] comparison hole at program level + the cross-width comparison [ptype]-REJECTED. *)
Definition runuint_cmp_e : GExpr :=
  EBn BEq (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e])
          (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]).
Example typed_cmp_cross_width_rejected :
  ptype (EBn BEq runb_u8one runb_i64) = None
  /\ go_compile_check (println_prog (EBn BEq runb_u8one runb_i64)) = false.
Proof. split; vm_compute; reflexivity. Qed.
(** DISPATCH AUTHORITY (gated): each live [typed_cmp] row IS the fully qualified model op — one
    6-conjunct pin per width (the derived [neqb]/[gtb]/[geb] are model Definitions, pinned as such). *)
Example typed_cmp_model_rows :
  (forall a b,
  typed_cmp BEq GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.GoNumeric.u8_eqb a b)
  /\ typed_cmp BNe GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.GoNumeric.u8_neqb a b)
  /\ typed_cmp BLt GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.GoNumeric.u8_ltb a b)
  /\ typed_cmp BLe GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.GoNumeric.u8_leb a b)
  /\ typed_cmp BGt GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.GoNumeric.u8_gtb a b)
  /\ typed_cmp BGe GTU8 (anyt TU8 a) (anyt TU8 b) = Some (Fido.GoNumeric.u8_geb a b))
  /\ (forall a b,
  typed_cmp BEq GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.GoNumeric.i8_eqb a b)
  /\ typed_cmp BNe GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.GoNumeric.i8_neqb a b)
  /\ typed_cmp BLt GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.GoNumeric.i8_ltb a b)
  /\ typed_cmp BLe GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.GoNumeric.i8_leb a b)
  /\ typed_cmp BGt GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.GoNumeric.i8_gtb a b)
  /\ typed_cmp BGe GTI8 (anyt TI8 a) (anyt TI8 b) = Some (Fido.GoNumeric.i8_geb a b))
  /\ (forall a b,
  typed_cmp BEq GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.GoNumeric.u16_eqb a b)
  /\ typed_cmp BNe GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.GoNumeric.u16_neqb a b)
  /\ typed_cmp BLt GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.GoNumeric.u16_ltb a b)
  /\ typed_cmp BLe GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.GoNumeric.u16_leb a b)
  /\ typed_cmp BGt GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.GoNumeric.u16_gtb a b)
  /\ typed_cmp BGe GTU16 (anyt TU16 a) (anyt TU16 b) = Some (Fido.GoNumeric.u16_geb a b))
  /\ (forall a b,
  typed_cmp BEq GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.GoNumeric.i16_eqb a b)
  /\ typed_cmp BNe GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.GoNumeric.i16_neqb a b)
  /\ typed_cmp BLt GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.GoNumeric.i16_ltb a b)
  /\ typed_cmp BLe GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.GoNumeric.i16_leb a b)
  /\ typed_cmp BGt GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.GoNumeric.i16_gtb a b)
  /\ typed_cmp BGe GTI16 (anyt TI16 a) (anyt TI16 b) = Some (Fido.GoNumeric.i16_geb a b))
  /\ (forall a b,
  typed_cmp BEq GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.GoNumeric.u32_eqb a b)
  /\ typed_cmp BNe GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.GoNumeric.u32_neqb a b)
  /\ typed_cmp BLt GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.GoNumeric.u32_ltb a b)
  /\ typed_cmp BLe GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.GoNumeric.u32_leb a b)
  /\ typed_cmp BGt GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.GoNumeric.u32_gtb a b)
  /\ typed_cmp BGe GTU32 (anyt TU32 a) (anyt TU32 b) = Some (Fido.GoNumeric.u32_geb a b))
  /\ (forall a b,
  typed_cmp BEq GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.GoNumeric.i32_eqb a b)
  /\ typed_cmp BNe GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.GoNumeric.i32_neqb a b)
  /\ typed_cmp BLt GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.GoNumeric.i32_ltb a b)
  /\ typed_cmp BLe GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.GoNumeric.i32_leb a b)
  /\ typed_cmp BGt GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.GoNumeric.i32_gtb a b)
  /\ typed_cmp BGe GTI32 (anyt TI32 a) (anyt TI32 b) = Some (Fido.GoNumeric.i32_geb a b))
  /\ (forall a b,
  typed_cmp BEq GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.GoNumeric.i64_eqb a b)
  /\ typed_cmp BNe GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.GoNumeric.i64_neqb a b)
  /\ typed_cmp BLt GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.GoNumeric.i64_ltb a b)
  /\ typed_cmp BLe GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.GoNumeric.i64_leb a b)
  /\ typed_cmp BGt GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.GoNumeric.i64_gtb a b)
  /\ typed_cmp BGe GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (Fido.GoNumeric.i64_geb a b))
  /\ (forall a b,
  typed_cmp BEq GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.GoNumeric.u64_eqb a b)
  /\ typed_cmp BNe GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.GoNumeric.u64_neqb a b)
  /\ typed_cmp BLt GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.GoNumeric.u64_ltb a b)
  /\ typed_cmp BLe GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.GoNumeric.u64_leb a b)
  /\ typed_cmp BGt GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.GoNumeric.u64_gtb a b)
  /\ typed_cmp BGe GTU64 (anyt TU64 a) (anyt TU64 b) = Some (Fido.GoNumeric.u64_geb a b)).
Proof. repeat split; intros; repeat split; reflexivity. Qed.

(** The [GTUint] hole ROW at program level (the platform-uint carrier has NO model ops). *)
Definition runuint_binop_e : GExpr :=
  EBn BAdd (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e])
           (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]).
(** DISPATCH AUTHORITY (gated): each live [typed_binop] row IS the fully qualified model op — one
    9-conjunct pin per width; [/] and [%] pin to the [div_checked] convoy over the width's
    evidence-carrying model op. *)
Example typed_binop_model_rows :
  (forall a b,
  typed_binop BAdd GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.GoNumeric.u8_add a b)))
  /\ typed_binop BSub GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.GoNumeric.u8_sub a b)))
  /\ typed_binop BMul GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.GoNumeric.u8_mul a b)))
  /\ typed_binop BDiv GTU8 (anyt TU8 a) (anyt TU8 b) = Some (div_checked TU8 Fido.GoNumeric.u8raw Fido.GoNumeric.u8_div a b)
  /\ typed_binop BRem GTU8 (anyt TU8 a) (anyt TU8 b) = Some (div_checked TU8 Fido.GoNumeric.u8raw Fido.GoNumeric.u8_mod a b)
  /\ typed_binop BAnd GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.GoNumeric.u8_and a b)))
  /\ typed_binop BOr  GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.GoNumeric.u8_or  a b)))
  /\ typed_binop BXor GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.GoNumeric.u8_xor a b)))
  /\ typed_binop BAndNot GTU8 (anyt TU8 a) (anyt TU8 b) = Some (RAVal (anyt TU8 (Fido.GoNumeric.u8_andnot a b))))
  /\ (forall a b,
  typed_binop BAdd GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.GoNumeric.i8_add a b)))
  /\ typed_binop BSub GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.GoNumeric.i8_sub a b)))
  /\ typed_binop BMul GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.GoNumeric.i8_mul a b)))
  /\ typed_binop BDiv GTI8 (anyt TI8 a) (anyt TI8 b) = Some (div_checked TI8 Fido.GoNumeric.i8raw Fido.GoNumeric.i8_div a b)
  /\ typed_binop BRem GTI8 (anyt TI8 a) (anyt TI8 b) = Some (div_checked TI8 Fido.GoNumeric.i8raw Fido.GoNumeric.i8_mod a b)
  /\ typed_binop BAnd GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.GoNumeric.i8_and a b)))
  /\ typed_binop BOr  GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.GoNumeric.i8_or  a b)))
  /\ typed_binop BXor GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.GoNumeric.i8_xor a b)))
  /\ typed_binop BAndNot GTI8 (anyt TI8 a) (anyt TI8 b) = Some (RAVal (anyt TI8 (Fido.GoNumeric.i8_andnot a b))))
  /\ (forall a b,
  typed_binop BAdd GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.GoNumeric.u16_add a b)))
  /\ typed_binop BSub GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.GoNumeric.u16_sub a b)))
  /\ typed_binop BMul GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.GoNumeric.u16_mul a b)))
  /\ typed_binop BDiv GTU16 (anyt TU16 a) (anyt TU16 b) = Some (div_checked TU16 Fido.GoNumeric.u16raw Fido.GoNumeric.u16_div a b)
  /\ typed_binop BRem GTU16 (anyt TU16 a) (anyt TU16 b) = Some (div_checked TU16 Fido.GoNumeric.u16raw Fido.GoNumeric.u16_mod a b)
  /\ typed_binop BAnd GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.GoNumeric.u16_and a b)))
  /\ typed_binop BOr  GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.GoNumeric.u16_or  a b)))
  /\ typed_binop BXor GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.GoNumeric.u16_xor a b)))
  /\ typed_binop BAndNot GTU16 (anyt TU16 a) (anyt TU16 b) = Some (RAVal (anyt TU16 (Fido.GoNumeric.u16_andnot a b))))
  /\ (forall a b,
  typed_binop BAdd GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.GoNumeric.i16_add a b)))
  /\ typed_binop BSub GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.GoNumeric.i16_sub a b)))
  /\ typed_binop BMul GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.GoNumeric.i16_mul a b)))
  /\ typed_binop BDiv GTI16 (anyt TI16 a) (anyt TI16 b) = Some (div_checked TI16 Fido.GoNumeric.i16raw Fido.GoNumeric.i16_div a b)
  /\ typed_binop BRem GTI16 (anyt TI16 a) (anyt TI16 b) = Some (div_checked TI16 Fido.GoNumeric.i16raw Fido.GoNumeric.i16_mod a b)
  /\ typed_binop BAnd GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.GoNumeric.i16_and a b)))
  /\ typed_binop BOr  GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.GoNumeric.i16_or  a b)))
  /\ typed_binop BXor GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.GoNumeric.i16_xor a b)))
  /\ typed_binop BAndNot GTI16 (anyt TI16 a) (anyt TI16 b) = Some (RAVal (anyt TI16 (Fido.GoNumeric.i16_andnot a b))))
  /\ (forall a b,
  typed_binop BAdd GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.GoNumeric.u32_add a b)))
  /\ typed_binop BSub GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.GoNumeric.u32_sub a b)))
  /\ typed_binop BMul GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.GoNumeric.u32_mul a b)))
  /\ typed_binop BDiv GTU32 (anyt TU32 a) (anyt TU32 b) = Some (div_checked TU32 Fido.GoNumeric.u32raw Fido.GoNumeric.u32_div a b)
  /\ typed_binop BRem GTU32 (anyt TU32 a) (anyt TU32 b) = Some (div_checked TU32 Fido.GoNumeric.u32raw Fido.GoNumeric.u32_mod a b)
  /\ typed_binop BAnd GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.GoNumeric.u32_and a b)))
  /\ typed_binop BOr  GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.GoNumeric.u32_or  a b)))
  /\ typed_binop BXor GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.GoNumeric.u32_xor a b)))
  /\ typed_binop BAndNot GTU32 (anyt TU32 a) (anyt TU32 b) = Some (RAVal (anyt TU32 (Fido.GoNumeric.u32_andnot a b))))
  /\ (forall a b,
  typed_binop BAdd GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.GoNumeric.i32_add a b)))
  /\ typed_binop BSub GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.GoNumeric.i32_sub a b)))
  /\ typed_binop BMul GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.GoNumeric.i32_mul a b)))
  /\ typed_binop BDiv GTI32 (anyt TI32 a) (anyt TI32 b) = Some (div_checked TI32 Fido.GoNumeric.i32raw Fido.GoNumeric.i32_div a b)
  /\ typed_binop BRem GTI32 (anyt TI32 a) (anyt TI32 b) = Some (div_checked TI32 Fido.GoNumeric.i32raw Fido.GoNumeric.i32_mod a b)
  /\ typed_binop BAnd GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.GoNumeric.i32_and a b)))
  /\ typed_binop BOr  GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.GoNumeric.i32_or  a b)))
  /\ typed_binop BXor GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.GoNumeric.i32_xor a b)))
  /\ typed_binop BAndNot GTI32 (anyt TI32 a) (anyt TI32 b) = Some (RAVal (anyt TI32 (Fido.GoNumeric.i32_andnot a b))))
  /\ (forall a b,
  typed_binop BAdd GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.GoNumeric.i64_add a b)))
  /\ typed_binop BSub GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.GoNumeric.i64_sub a b)))
  /\ typed_binop BMul GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.GoNumeric.i64_mul a b)))
  /\ typed_binop BDiv GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (div_checked TI64 Fido.GoNumeric.i64raw Fido.GoNumeric.i64_div a b)
  /\ typed_binop BRem GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (div_checked TI64 Fido.GoNumeric.i64raw Fido.GoNumeric.i64_mod a b)
  /\ typed_binop BAnd GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.GoNumeric.i64_and a b)))
  /\ typed_binop BOr  GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.GoNumeric.i64_or  a b)))
  /\ typed_binop BXor GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.GoNumeric.i64_xor a b)))
  /\ typed_binop BAndNot GTInt64 (anyt TI64 a) (anyt TI64 b) = Some (RAVal (anyt TI64 (Fido.GoNumeric.i64_andnot a b))))
  /\ (forall a b,
  typed_binop BAdd GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.GoNumeric.u64_add a b)))
  /\ typed_binop BSub GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.GoNumeric.u64_sub a b)))
  /\ typed_binop BMul GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.GoNumeric.u64_mul a b)))
  /\ typed_binop BDiv GTU64 (anyt TU64 a) (anyt TU64 b) = Some (div_checked TU64 Fido.GoNumeric.u64raw Fido.GoNumeric.u64_div a b)
  /\ typed_binop BRem GTU64 (anyt TU64 a) (anyt TU64 b) = Some (div_checked TU64 Fido.GoNumeric.u64raw Fido.GoNumeric.u64_mod a b)
  /\ typed_binop BAnd GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.GoNumeric.u64_and a b)))
  /\ typed_binop BOr  GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.GoNumeric.u64_or  a b)))
  /\ typed_binop BXor GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.GoNumeric.u64_xor a b)))
  /\ typed_binop BAndNot GTU64 (anyt TU64 a) (anyt TU64 b) = Some (RAVal (anyt TU64 (Fido.GoNumeric.u64_andnot a b)))).
Proof. repeat split; intros; repeat split; reflexivity. Qed.

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
  /\ map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
        typed_shift_cases
     = [ Some (ORet tt (w_log true (anyt TU8 (u8wrap 6) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 1) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 6) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TI64 (i64wrap 6) :: nil) w))
       ; Some (ORet tt (w_log true (anyt TU64 (u64wrap 1) :: nil) w)) ]
  /\ forallb go_compile_check (map println_prog typed_shift_cases) = true.
Proof. intro w. repeat split; vm_compute; reflexivity. Qed.
(** The shift EDGES: a constant count, a typed-width count, a HUGE count (saturates — gc gives 0),
    and the NEGATIVE runtime count (gc's exact panic payload) — go-run-verified: 12, 24, 0, panic. *)
Definition runshift_constcnt_e : GExpr := EBn BShl runb_u8 (EInt 2).
Definition runshift_typedcnt_e : GExpr := EBn BShl runb_u8 runb_u8.
Definition runshift_hugecnt_e  : GExpr :=
  EBn BShl runb_u8 (EUn UXor (ECall (EId (mkIdent "uint64" eq_refl)) [runlen3_e])).
Definition runshift_negcnt_e   : GExpr := EBn BShl runb_u8 runb_i64n.
Example typed_shift_edge_runs : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ runshift_constcnt_e ; runshift_typedcnt_e ; runshift_hugecnt_e ; runshift_negcnt_e ]
  = [ Some (ORet tt (w_log true (anyt TU8 (u8wrap 12) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 24) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 55340232221128654848) :: nil) w))
    ; Some (OPanic rt_shift_neg w) ].
Proof. intro w. vm_compute. reflexivity. Qed.
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ gtint_and_e ; gtint_or_e ; gtint_xor_e ; gtint_andnot_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 7) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 2) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 1) :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
(** The BIG-CONST count regressions (R8 leak class): an untyped [2^31] count is
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
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
      [ gtint_shift_bigconst_e ; gtint_shr_bigconst_e ; u8_shift_bigconst_e ; gtint_shift_typedbig_e ]
  = [ Some (ORet tt (w_log true (anyt TInt64 (intwrap 55340232221128654848) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 0) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TU8 (u8wrap 55340232221128654848) :: nil) w))
    ; Some (ORet tt (w_log true (anyt TInt64 (intwrap 55340232221128654848) :: nil) w)) ].
Proof. intro w. vm_compute. reflexivity. Qed.
Example shift_bigconst_gate :
  ptype (EBn BShl runlen3_e (EInt 4294967296)) = None
  /\ ptype (EBn BShl runb_u8 (EInt 4294967296)) = None
  /\ go_compile_check (println_prog (EBn BShl runlen3_e (EInt 4294967296))) = false
  /\ go_compile_check (println_prog (EBn BShl runb_u8 (EInt 4294967296))) = false.
Proof. repeat split; vm_compute; reflexivity. Qed.
Definition runshift_uintleft_e : GExpr :=
  EBn BShl (ECall (EId (mkIdent "uint" eq_refl)) [runlen3_e]) (EInt 1).
(** the [GTUint] HOLE at program level, all three dispatch families (cmp / binop / shift):
    classified, SUPPORTED, yet undenoted and undecidable — the platform-uint carrier has NO
    model ops.  ONE grouped pin. *)
Example typed_uint_hole_programs_absent :
  (ptype runuint_cmp_e = Some PtBool
  /\ go_compile_check (println_prog runuint_cmp_e) = true
  /\ denotable_program (println_prog runuint_cmp_e) = false
  /\ denote_program (println_prog runuint_cmp_e) = None)
  /\ (ptype runuint_binop_e = Some (PtRunInt GTUint)
  /\ go_compile_check (println_prog runuint_binop_e) = true
  /\ denotable_program (println_prog runuint_binop_e) = false
  /\ denote_program (println_prog runuint_binop_e) = None)
  /\ (ptype runshift_uintleft_e = Some (PtRunInt GTUint)
  /\ go_compile_check (println_prog runshift_uintleft_e) = true
  /\ denotable_program (println_prog runshift_uintleft_e) = false
  /\ denote_program (println_prog runshift_uintleft_e) = None).
Proof. repeat split; vm_compute; reflexivity. Qed.
(** DISPATCH AUTHORITY (gated): each live [typed_shift] row IS the width's convoy over the fully
    qualified model op — one 2-conjunct pin per width. *)
Example typed_shift_model_rows :
  (forall a z,
  typed_shift BShl GTU8 (anyt TU8 a) z = shift_checked_small TU8 Fido.GoNumeric.u8_shl a z
  /\ typed_shift BShr GTU8 (anyt TU8 a) z = shift_checked_small TU8 Fido.GoNumeric.u8_shr a z)
  /\ (forall a z,
  typed_shift BShl GTI8 (anyt TI8 a) z = shift_checked_small TI8 Fido.GoNumeric.i8_shl a z
  /\ typed_shift BShr GTI8 (anyt TI8 a) z = shift_checked_small TI8 Fido.GoNumeric.i8_shr a z)
  /\ (forall a z,
  typed_shift BShl GTU16 (anyt TU16 a) z = shift_checked_small TU16 Fido.GoNumeric.u16_shl a z
  /\ typed_shift BShr GTU16 (anyt TU16 a) z = shift_checked_small TU16 Fido.GoNumeric.u16_shr a z)
  /\ (forall a z,
  typed_shift BShl GTI16 (anyt TI16 a) z = shift_checked_small TI16 Fido.GoNumeric.i16_shl a z
  /\ typed_shift BShr GTI16 (anyt TI16 a) z = shift_checked_small TI16 Fido.GoNumeric.i16_shr a z)
  /\ (forall a z,
  typed_shift BShl GTU32 (anyt TU32 a) z = shift_checked_small TU32 Fido.GoNumeric.u32_shl a z
  /\ typed_shift BShr GTU32 (anyt TU32 a) z = shift_checked_small TU32 Fido.GoNumeric.u32_shr a z)
  /\ (forall a z,
  typed_shift BShl GTI32 (anyt TI32 a) z = shift_checked_small TI32 Fido.GoNumeric.i32_shl a z
  /\ typed_shift BShr GTI32 (anyt TI32 a) z = shift_checked_small TI32 Fido.GoNumeric.i32_shr a z)
  /\ (forall a z,
  typed_shift BShl GTInt64 (anyt TI64 a) z = shift_checked_wide TI64 Fido.GoNumeric.i64_shl a z
  /\ typed_shift BShr GTInt64 (anyt TI64 a) z = shift_checked_wide TI64 Fido.GoNumeric.i64_shr a z)
  /\ (forall a z,
  typed_shift BShl GTU64 (anyt TU64 a) z = shift_checked_wide TU64 Fido.GoNumeric.u64_shl a z
  /\ typed_shift BShr GTU64 (anyt TU64 a) z = shift_checked_wide TU64 Fido.GoNumeric.u64_shr a z).
Proof. repeat split; intros; repeat split; reflexivity. Qed.
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
  /\ go_compile_check (println_prog runconv_absent_src_e) = true
  /\ denotable_program (println_prog runconv_absent_src_e) = false
  /\ denote_program (println_prog runconv_absent_src_e) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** FAIL-CLOSED pins for an INVALID NESTED map type (the INVALID-Go class of the [goty_supported]
    authority — its valid-but-out-of-core class, ptr/chan map keys, is pinned surface-by-surface in
    [GoCompile.valid_unsupported_programs]):
    [map[int]map[[]int]int]
    hides a non-comparable slice KEY inside the VALUE type, so even the EMPTY literal is invalid Go — the
    gate REJECTS it at the ROOT ([ptype = None] ⇒ unsupported, never emitted) and NO layer assigns it
    behavior ([eval_value] / [reval_int] / [denote_program] all decline) through [len],
    [println(len(..))], and the divide-by-zero shape.  GoCompile's [bad_programs_rejected] carries the same
    witnesses at the gate level. *)
Definition maplen_invalid_vt_e : GExpr :=
  ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []].
Example map_len_invalid_type_rejected :
  ptype (EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []) = None
  /\ ptype maplen_invalid_vt_e = None
  /\ eval_value maplen_invalid_vt_e = None
  /\ reval_int maplen_invalid_vt_e = None
  /\ go_compile_check (println_prog maplen_invalid_vt_e) = false
  /\ denote_program (println_prog maplen_invalid_vt_e) = None
  /\ go_compile_check (mkProgram (mkIdent "main" eq_refl)
       [GsBlankAssign (EBn BDiv (EInt 1) maplen_invalid_vt_e)]) = false
  /\ denote_program (mkProgram (mkIdent "main" eq_refl)
       [GsBlankAssign (EBn BDiv (EInt 1) maplen_invalid_vt_e)]) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** TIGHTNESS — WHERE the general converse's "sufficient, not necessary" comes from.  [stmt_terminates] just
    READS [denote_stmt]'s terminator flag (NOT a second authority).  On a TERMINATOR-FREE body the compositional
    converse is EXACT (an iff): the body denotes iff EVERY statement individually denotes.  The ONLY slack is the
    terminator escape — a terminator's UNREACHABLE rest need only be CLOSED-supported ([stmt_ok]), so a denotable
    body may carry an undenotable-but-closed-supported DEAD tail (pinned by
    [denotable_body_escapes_stmt_denotable] below). *)
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
    is a DENOTABLE body ([return] terminates; the multi-byte-rune-arg [println] is a CLOSED-supported dead tail)
    whose tail does NOT denote, so [denotable_body = true] while [forallb stmt_denotable = false].  This body
    HAS a terminator — exactly why the iff (upstream in GoSemDenote.v) does not apply to it. *)
Example denotable_body_escapes_stmt_denotable :
  denotable_body [GsReturn;
    GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb])] = true
  /\ forallb stmt_denotable [GsReturn;
       GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [runeconv_mb])] = false.
Proof. split; vm_compute; reflexivity. Qed.

(** ---- EXECUTABLE TOTALITY on the [structurally_total_cmd] fragment (every denoted command today): cmd.v's gated [run_cmd_terminates] (structural totality, no bound) proves each such
    [Cmd unit] — defers included — runs to [Some] Outcome, so a denoted program always RUNS;
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
    their CLOSED-supportedness ([stmt_ok], NOT live [go_compile_check]: a used-decl successor is
    live-supported yet gated out here — [shortdecl_deadtail_supported_undenoted], GoSemDenote.v).
    Stated for ALL [s]/[c]/[rest]: whenever [denote_stmt] marks [s] terminating
    ([Some (c, true)]), [denote_body] emits [c] and gates the rest ONLY on [forallb stmt_ok rest], NEVER on
    [denote_body rest].  A UNIVERSAL lemma (over ALL [rest]), NOT a fixture keyed to one specific
    closed-supported-but-undenotable successor — so it never erodes.  Such successors PERSIST, not vanish: a
    runtime-arg statement is closed-supported yet eval-partial; the lemma holds for EVERY [rest] regardless of
    how [eval_value] grows. *)
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

(** [print] vs [println] is OBSERVABLE in the model ([w_log]'s flag) — pinned as [rc_print]. *)
Definition gosem_print_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "print" eq_refl)) [EInt 1])].

(** A NON-panicking [_ = e] falls through — no output of its own, the successor runs — pinned
    as [rc_blank_pure]. *)
Definition gosem_blank_pure_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EInt 1);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "ok"])].

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
    are unreachable — later args are gated by the caller's [expr_stmt_ok], successor statements by
    [forallb stmt_ok] (the closed fragment, NOT [go_compile_check]); neither is required to DENOTE.  The undenoted piece
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
  map (fun p => match denote_program p with Some c => run_cmd c w | None => None end)
      arg_panic_shortcircuit_progs
  = map (fun _ => Some (OPanic rt_div_zero w)) arg_panic_shortcircuit_progs.
Proof. intro w. vm_compute. reflexivity. Qed.

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
                | Some c => run_cmd c w | None => None end) eval_value_good
  = map (fun p => Some (ORet tt (w_log true (snd p :: nil) w))) eval_value_good.
Proof. intro w. vm_compute. reflexivity. Qed.

(** REQUIRED-CATEGORY COVERAGE as a TYPED obligation.  [runs_to e v] = [println(e); return] denotes and runs
    through cmd.v's [run_cmd] to the world logging [v].  The RECORD TYPE [GoSemRequiredCategoryCoverage] fixes,
    in its FIELD TYPES (one per required behavior category), the EXACT end-to-end behaviors the model must
    exhibit — string-literal PRINTLN, int CONVERSION, exact FLOAT, numeric-compare BOOL, string CONCAT,
    string-compare-of-concat BOOL, a constant in-bounds int-slice-literal INDEX, [len] of a fully-evaluable
    literal (slice AND integer-keyed map), a non-tail RETURN that stops the body with NO output, a denoted PANIC ending in [OPanic],
    [print]'s observable flag, a pure blank-assign falling through, defer
    LIFO ordering at return, a DEFERRED panic firing at return, the determined DIVIDE-BY-ZERO panicking with
    Go's exact runtime value, a panicking ARGUMENT pre-empting its call, and a deferred call's argument
    panicking AT DEFER TIME.  [gosem_category_coverage] inhabits that type, so it can be built ONLY by
    discharging EVERY field with the stated programs+values: a category cannot be dropped without editing this
    typed STATEMENT (the record), never silently by convention.  Table-INDEPENDENT (no reference to
    [eval_value_good]). *)
Definition runs_to (e : GExpr) (v : GoAny) : Prop :=
  forall w, match denote_program (println_prog e) with
            | Some c => run_cmd c w | None => None end = Some (ORet tt (w_log true (v :: nil) w)).
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
    match denote_program gosem_return_stops_prog with Some c => run_cmd c w | None => None end
    = Some (ORet tt w);
  rc_panic : forall w,                                        (* a denoted [panic("x")] ends in [OPanic] with the model's exact value *)
    match denote_program gosem_panic_demo_prog with Some c => run_cmd c w | None => None end
    = Some (OPanic (anyt TString "x") w);
  rc_print : forall w,                                        (* [print] logs with the PRINT flag — the print/println distinction is observable *)
    match denote_program gosem_print_prog with Some c => run_cmd c w | None => None end
    = Some (ORet tt (w_log false (anyt TInt64 (intwrap 1) :: nil) w));
  rc_blank_pure : forall w,                                   (* a non-panicking [_ = e] falls through: no output of its own; the successor runs *)
    match denote_program gosem_blank_pure_prog with Some c => run_cmd c w | None => None end
    = Some (ORet tt (w_log true (anyt TString "ok" :: nil) w));
  rc_defer_lifo : forall w,                                   (* defers run at RETURN, LIFO: body "hi", then "b" (deferred LAST, runs FIRST), then "a" *)
    match denote_program gosem_defer_lifo_prog with Some c => run_cmd c w | None => None end
    = Some (ORet tt (w_log true (anyt TString "a" :: nil)
                      (w_log true (anyt TString "b" :: nil)
                        (w_log true (anyt TString "hi" :: nil) w))));
  rc_defer_panic : forall w,                                  (* a DEFERRED panic does NOT stop the body ("hi" prints) and fires at return *)
    match denote_program gosem_defer_panic_prog with Some c => run_cmd c w | None => None end
    = Some (OPanic (anyt TString "boom") (w_log true (anyt TString "hi" :: nil) w));
  rc_div_zero : forall w,                                     (* the determined divide-by-zero PANICS with Go's exact runtime value *)
    match denote_program gosem_runtime_blank_prog with Some c => run_cmd c w | None => None end
    = Some (OPanic rt_div_zero w);
  rc_arg_panic : forall w,                                    (* a PANICKING argument panics BEFORE the call — println prints NOTHING *)
    match denote_program gosem_arg_panic_prog with Some c => run_cmd c w | None => None end
    = Some (OPanic rt_div_zero w);
  rc_defer_arg_panic : forall w,                              (* a deferred call's ARGS evaluate AT DEFER TIME: the panic fires at the defer statement — the later "hi" NEVER prints *)
    match denote_program gosem_defer_arg_panic_prog with Some c => run_cmd c w | None => None end
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
    [runtime_float_source_conv_absent]), and [cap] of a slice literal [cap_slicelit_e]
    (supported + certified-emitted — GoEmit's demo prints it — yet NO denotation arm; the
    DELETION.md cap row cites this member).  Each member is pinned supported AND undenoted AND
    eval-level absent.  (SIGNED-ZERO constant folds are NOT members: the checker's authority is
    the CONSTANT-fold layer ([sf_const_binop]/[sf_const_neg] — zero-sign erasure), so
    [-(float64(0))] and the zero-binop shapes fold to [+0] and DENOTE — [negzero_const_runs] +
    [signed_zero_folds_run] below.) *)
Definition cap_slicelit_e : GExpr :=
  ECall (EId (mkIdent "cap" eq_refl)) [ESliceLit GTInt [EInt 1]].
Definition undenoted_frontier : list GExpr :=
  [ runeconv_mb
  ; runnot_uint_e
  ; runconv_float_src_e
  ; cap_slicelit_e ].
Example undenoted_frontier_pinned :
  forallb (fun e => go_compile_check (println_prog e)
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
  /\ go_compile_check (println_prog negzero_const_e) = true
  /\ denotable_program (println_prog negzero_const_e) = true
  /\ (match denote_program (println_prog negzero_const_e) with
      | Some c => run_cmd c w | None => None end)
     = Some (ORet tt (w_log true (anyt TFloat64 (S754_zero false) :: nil) w)).
Proof. intro w. repeat split; vm_compute; reflexivity. Qed.
(** the BINOP zero rows pinned end-to-end, BOTH widths: multiplication and
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
  /\ forallb go_compile_check (map println_prog
       [ zeromul_const_e ; zerodiv_const_e ; negzeromul_const_e
       ; zeromul32_const_e ; zerodiv32_const_e ; negzeromul32_const_e ]) = true
  /\ forallb denotable_program (map println_prog
       [ zeromul_const_e ; zerodiv_const_e ; negzeromul_const_e
       ; zeromul32_const_e ; zerodiv32_const_e ; negzeromul32_const_e ]) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.
Example signed_zero_folds_run : forall w,
  map (fun e => match denote_program (println_prog e) with Some c => run_cmd c w | None => None end)
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

(** every runtime/typed-tier FIXTURE program is SUPPORTED (emittable Go) — ONE grouped
    gate pin over all the per-tier fixture lists (R1–R8, T1–T5, the shift edges, the
    arg-panic short-circuits). *)
Example runtime_fixture_progs_supported :
  forallb go_compile_check
    (   ([ println_prog runidx_e
    ; println_prog (EIndex (ESliceLit GTInt [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]) (EInt 0)) ])
     ++ ([ println_prog runconv_e ; println_prog runconv_trunc_e
    ; println_prog runconv_int_e ; println_prog runconv_uint_e
    ; println_prog runconv_panic_e ])
     ++ ((map println_prog
      [ runbool_e ; runbool_ne_e ; runbool_lt_e ; runbool_le_e ; runbool_gt_e ; runbool_ge_e
      ; runbool_panic_e ]))
     ++ ((map println_prog [ maplen_runval_e ; maplen_run2_e ; maplen_i64_e ; maplen_bool_e
                      ; maplen_panic_e ; maplen_convpanic_e ; maplen_ambig_e ]))
     ++ ([println_prog runlen_e; println_prog runtime_div_vals_e; println_prog panicking_elem_len_e])
     ++ ((map println_prog [ runneg_e ; runrem_e ; runrem_neg_e ; runneg_panic_e ]))
     ++ ((map println_prog [ runnot_e ; runnot_panic_e ]))
     ++ ((map println_prog [ runnot_i64_e ; runnot_u8_e ; runneg_i64_e ; runnot_panic_i64_e ]))
     ++ ((map println_prog [ runconv_chain_e ; runconv_chain_int_e ; runconv_chain_trunc_e ]))
     ++ ((map println_prog typed_binop_cases))
     ++ ((map println_prog typed_mixed_cases))
     ++ ((map println_prog typed_cmp_cases))
     ++ ((map println_prog
    [ runshift_constcnt_e ; runshift_typedcnt_e ; runshift_hugecnt_e ; runshift_negcnt_e ]))
     ++ ((map println_prog
    [ runshift_intleft_e ; gtint_shift_wrap_e ; gtint_shift_typedcnt_e
    ; gtint_shift_huge_e ; gtint_shift_signfill_e ; gtint_shift_negcnt_e ]))
     ++ ((map println_prog
    [ gtint_shift_bigconst_e ; gtint_shr_bigconst_e ; u8_shift_bigconst_e
    ; gtint_shift_typedbig_e ]))
     ++ ((map println_prog
    [ gtint_and_e ; gtint_or_e ; gtint_xor_e ; gtint_andnot_e ]))
     ++ (arg_panic_shortcircuit_progs)) = true.
Proof. vm_compute. reflexivity. Qed.

(** All the demo programs above are SUPPORTED (each is emittable Go); grouped so the gate is pinned once. *)
Example demo_progs_supported :
  forallb go_compile_check
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
   denote_expr_pure, arg_panic_shortcircuit_runs, gosem_category_coverage,
   denote_expr_env_nil, GoCompile.tcat_mark_insensitive, env_eid_pins, env_float_pins,
   env_float_conv_class).
Definition gosem_float_surface :=
  (fsf_checked_binop_agrees, fsf_checked_neg_agrees,
   fsf_checked_conv_same_agrees, fsf_checked_conv_narrow_agrees, fsf_checked_conv_widen_agrees,
   fsf_checked_complete, floats_checked_total,
   eval_value_floats_checked, floats_checked_children_eqs,
   binary_normalize_opp, Fido.GoNumeric.binary_round_exact,
   Fido.GoNumeric.renorm_binary_round_idem,
   ptype_float_const_repr, ptype_float_payload_f64, ptype_float_payload_f32, box_float_gate,
   binary_normalize_wide_determined, add_carry_raw_wide_accepted, binary_round_of_norm_wide,
   dy_norm_value_unique, sf_render_signed_value_f64, sf_render_add_agrees_f64,
   sf_render_sub_agrees_f64, sf_render_mul_agrees_f64, sf_render_div_agrees_f64,
   sf_render_add_agrees_f32, sf_render_sub_agrees_f32, sf_render_mul_agrees_f32,
   sf_render_div_agrees_f32, sf_render_narrow_agrees_f32, sf_render_widen_agrees_f32,
   sf_render_cneg_agrees_f64, sf_render_cneg_agrees_f32,
   sf_render_neg_general_f64, sf_render_fold_neg_general_f64,
   fsf_checked_render, fsf_checked_neg_zero_total, negzero_const_runs,
   sf_const_binop_zero_erased, sf_const_neg_zero_erased,
   signed_zero_folds_eval, signed_zero_folds_run, reciprocal_sign_decisive).
Definition gosem_slice_index_surface :=
  (eval_slice_index_supported, eval_slice_index_reduces, eval_slice_index_oob_class,
   eval_slice_index_inbounds_class, eval_len_reduces, eval_len_supported,
   slice_index_supported_but_undenoted,
   denote_expr_index_in_bounds, denote_expr_index_oob,
   denote_expr_index_elem_panic, denote_expr_index_idx_panic,
   runtime_index_runs, slice_index_panics_denote).
(** SURFACE POLICY: a surface lists PUBLIC guarantees — sealed
    endpoint theorems, program-level runs/supported/absent pins, dispatch AUTHORITY pins, and
    demanded totality/boundary seals.  Internal helpers (shape splits, tag/totality/cases
    lemmas) are NOT listed: `Print Assumptions` on the endpoints pulls their whole cone, so
    they stay inside the gated trust base without noising the public contract. *)
Definition gosem_runtime_int_surface :=
  (denote_expr_div_zero, runtime_tier_runs, runtime_fixture_progs_supported,
   denote_expr_div_runs, denote_expr_rem_runs, denote_expr_neg_runs, denote_expr_neg_panic,
   denote_expr_not_runs, denote_expr_not_panic, runtime_negrem_runs, runtime_not_runs,
   denote_expr_conv_panic, denote_expr_conv_int_panic, denote_expr_conv_runs_sealed,
   denote_expr_conv_int_runs_sealed, denote_expr_conv_src_absent, typed_runtime_convchain_runs,
   denote_expr_cmp_runs, denote_expr_cmp_left_panic, denote_expr_cmp_right_panic,
   cmp_verdict_model_rows, cmp_verdict_complete, runtime_conv_runs, runtime_bool_runs,
   denote_expr_typed_unop_runs_sealed, denote_expr_typed_unop_panic, reval_val_typed,
   runtime_typed_unop_runs, typed_unop_model_rows, typed_unop_holes_none,
   denote_expr_typed_binop_runs_sealed, denote_expr_typed_binop_left_panic,
   denote_expr_typed_binop_right_panic, denote_expr_typed_binop_src_absent,
   typed_binop_nonarith_none, typed_binop_gtint_none, typed_binop_uint_none,
   typed_binop_nonint_none, typed_operand_cross_width_none, typed_binop_cross_width_rejected,
   denote_expr_typed_cmp_runs_sealed, denote_expr_typed_cmp_left_panic,
   denote_expr_typed_cmp_right_panic, denote_expr_typed_cmp_src_absent, typed_cmp_noncmp_none,
   typed_cmp_gtint_none, typed_cmp_uint_none, typed_cmp_nonint_none, runtime_typed_cmp_runs,
   typed_uint_hole_programs_absent, typed_cmp_cross_width_rejected, typed_cmp_model_rows,
   denote_expr_typed_shift_runs_sealed, denote_expr_typed_shift_count_panic,
   denote_expr_typed_shift_src_absent, typed_shift_nonshift_none, typed_shift_gtint_none,
   typed_shift_uint_none, typed_shift_nonint_none, shift_count_const_total,
   typed_runtime_shift_runs, typed_shift_edge_runs, typed_shift_model_rows,
   int_bitop_model_rows, int_shift_op_model_rows, int_bitop_complete, int_shift_op_complete,
   denote_expr_bitwise_runs, denote_expr_bitwise_left_panic, denote_expr_bitwise_right_panic,
   denote_expr_int_shift_runs, denote_expr_int_shift_neg_panic,
   denote_expr_int_shift_left_panic, denote_expr_int_shift_count_panic,
   denote_expr_int_shift_const_count_runs, denote_expr_typed_shift_const_count_runs,
   shift_bigconst_runs, shift_bigconst_gate, gtint_bitwise_runs, gtint_shift_runs,
   runtime_typed_binop_runs, typed_mixed_const_runs, typed_binop_model_rows,
   (* cross-layer int-width coherence: the type-category int-const accept-set ([int]/[uint]) lies inside the
      64-bit runtime range [in_i64]/[in_u64] — the mechanical gate for [GoTypes.int_ty_range]'s coherence doc *)
   int_const_int_subsumes_i64, int_const_uint_subsumes_u64).
Definition gosem_map_surface :=
  (eval_map_len_reduces, eval_map_len_supported, map_len_eval_absent, maplen_divzero_runs,
   map_len_invalid_type_rejected,
   denote_expr_maplen_runs, denote_expr_maplen_panic,
   runtime_maplen_runs, runtime_maplen_ambiguous_absent,
   rconstr_vals_ok_iff, rconstr_vals_panic_sound, rconstr_vals_two_panics_absent).
Definition gosem_frontier_surface :=
  (undenoted_frontier_pinned,
   typed_unary_holes_absent, reval_val_runfloat_none, denote_expr_conv_float_src_absent,
   runtime_float_source_conv_absent, runtime_conv_absent_src_pinned,
   typed_uint_hole_programs_absent).
(** The ONE composed public gate: [gosem_trust_surface] composes the topic surfaces above, and
    the topic surfaces DEFINE the current public contract (per the surface policy — endpoints
    and intentional pins; internal helpers ride the endpoints' assumption cones). *)
Definition gosem_trust_surface :=
  (gosem_core_surface, gosem_float_surface, gosem_slice_index_surface,
   gosem_runtime_int_surface, gosem_map_surface, gosem_frontier_surface).
Print Assumptions gosem_trust_surface.

(** ---- STRING-AUTHORITY PINS (gated): each of [str_cmp_op]'s six branches IS, by reflexivity, the FULLY
    QUALIFIED model constant [Fido.GoString.str_*] — so a fork that reroutes a branch breaks a pin and FAILS the
    build ([<=] = the model's [str_geb] with operands swapped).  Bundled into [gosem_string_authority_surface]
    so its [Print Assumptions] certifies the whole cone zero-axiom (the honest place for the "authority
    guarantee" claim); a fork that DIDN'T reroute a live branch would be dead code. *)
Example str_cmp_model_rows :
  (str_cmp_op BEq = Some Fido.GoString.str_eqb)
  /\ (str_cmp_op BNe = Some Fido.GoString.str_neqb)
  /\ (str_cmp_op BLt = Some Fido.GoString.str_ltb)
  /\ (str_cmp_op BLe = Some (fun s t => Fido.GoString.str_geb t s))
  /\ (str_cmp_op BGt = Some Fido.GoString.str_gtb)
  /\ (str_cmp_op BGe = Some Fido.GoString.str_geb).
Proof. repeat split; reflexivity. Qed.
Definition gosem_string_authority_surface :=
  (str_cmp_model_rows).
Print Assumptions gosem_string_authority_surface.
