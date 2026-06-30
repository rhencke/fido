(** ============================================================================
    GoSem.v — the AST's BEHAVIORAL semantics, as a BRIDGE into the existing proof-only models
    (charter Phase 5; ARCHITECTURE.md §GoSem).  GoSem does NOT fork a second semantics universe — it
    TRANSLATES a GoAst [Program] into [cmd.v]'s already-proven command tree [Cmd unit] and reuses that
    file's [denote] / [run_cmd] interpreters, the GoSafe gate ([expr_stmt_ok] / [svalue]) for which programs
    have meaning, and the MODEL's own value constructors ([anyt] / [intwrap]) for the printed values — so the
    factoring is single-authority and the modelling is faithful (a denoted [println] produces EXACTLY the
    [w_log] output the model's [println] does).

    SLICE 1 (this file, to grow): the bridge + its GATE-CONNECTION + REAL OBSERVABLE EFFECTS.
    [denote_program] translates the supported statement forms into [Cmd unit]:
      - [println(args)] -> [COut true  [eval args]]   (faithful: model [println xs = w_log true  xs])
      - [print(args)]   -> [COut false [eval args]]   (faithful: model [print   xs = w_log false xs])
      - [panic(a)]      -> [CPan (eval a)]
      - [return] / [panic] TERMINATE the body (the [denote_stmt] flag): their successors are UNREACHABLE,
                           so a non-tail `return; println(..)` / `panic(..); println(..)` faithfully runs no
                           successor.  The unreachable rest need only be SUPPORTED ([forallb stmt_ok]), NOT
                           denotable — a terminator never depends on a successor slice 1 cannot yet evaluate.
      - [_ = e]         -> [CRet tt] ONLY when [eval_value e <> None] (a constant slice 1 evaluates — no effect,
                           no panic); a RUNTIME [e] (e.g. [1/len([]int{})], which Go PANICS on) is UN-denoted
    [eval_value] (slice 1: a string LITERAL, plus any printable [ptype] that folds to an INTEGER CONSTANT —
    literals, integer CONVERSIONS [int64(3)], ARITHMETIC [1+2], complement [^x], EXCLUDING [GTUint] — boxed via
    the model's value ctors, failing closed on an out-of-range value) supplies the printed/panicked values;
    FLOAT consts, bools, non-literal strings, [GTUint], and RUNTIME values ([len(..)]/[int(x)]…) are the next
    sub-slices and [eval] to [None] there.
    ★FAITHFUL-OR-ABSENT: GoSem denotes ONLY what it models correctly — so a SUPPORTED program receives either
    its RIGHT behavior or (not yet) NO behavior ([denote_program = None]), NEVER a wrong one (the two regression
    examples below pin the [return]-stops and runtime-blank-un-denoted cases).
    SOUNDNESS is structural and clean because [denote] CONSULTS THE GATE: the effect arm fires only when
    [expr_stmt_ok] holds (and the blank arm when [svalue]), so [gosem_sound] — denotation ⊆ [SupportedProgram],
    no meaning given to invalid Go — falls out, and a PARTIAL [eval_value] can grow without ever over-accepting
    (it only narrows COMPLETENESS, never breaks soundness).  COMPLETENESS (supported ⇒ denotes) is the roadmap
    converse, reached as [eval] covers the full printable subset; together they will pin "supported ⟺ has a
    defined GoSem behavior", the foundation for [BehaviorSafe] -> [SafeProgram] -> [emit_safe].  No axioms.
    ============================================================================ *)
From Fido Require Import GoAst GoTypes GoSafe cmd preamble.   (* [preamble] re-exports [builtins]: [GoAny]/[anyt]/[intwrap]/[World]/[w_log]/[Outcome]/[ORet] *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.

(** Box an integer-constant VALUE [z] of int type [t] as the MODEL's runtime [GoAny] — or [None].  FAILS CLOSED
    at the BOUNDARY: it first checks [int_const_repr z t] (is [z] representable in [t]?), so an out-of-range [z]
    yields [None] HERE, not a silently [*wrap]-mangled value — exactness does NOT rely on a caller having gated
    (rule 4: evidence at the builder).  When in range the [*wrap] constructor is IDENTITY, so it builds EXACTLY
    the model's value (e.g. [int64(3)] -> [anyt TI64 (i64wrap 3)] = [MkI64 3], what the model's [println]
    carries).  [GTUint] stays [None] (no proof-free [GoUint] wrap yet); floats are the next sub-slice. *)
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
    | _       => None   (* [GTUint] (no proof-free wrap), non-integer [t] — next sub-slice *)
    end
  else None.

(** Evaluate a value expression to the MODEL's runtime [GoAny], or [None] if outside slice 1's bridged subset.
    FAITHFUL via [ptype] — the SINGLE constant-folding authority: [ptype] already folds an integer constant to
    its VALUE and TYPE ([PtIntConst z] = untyped, taking default [int]; [PtTIntConst t z] = a typed const, e.g.
    a conversion [int64(3)] or typed-const arithmetic), and [box_int] attaches the model value, FAILING CLOSED
    on an out-of-range [z] (so [eval_value] is self-sound, not caller-gated).  Live coverage: a string LITERAL
    ([anyt TString s], matched syntactically since [PtStr] carries no value), an untyped integer constant whose
    default-[int] value is in range, and a supported TYPED integer constant — i.e. integer literals,
    CONVERSIONS [int64(3)] (EXCLUDING [GTUint], no [GoUint] box yet), ARITHMETIC [1+2], complement [^x] — with
    NO second folding logic.  ABSENT (-> [None], the next sub-slices): float constants, bools, non-literal
    strings, [GTUint], and all RUNTIME values ([PtRunInt]/[PtRunFloat]: [len(..)], [int(x)]…).  Honestly
    absent, never wrong. *)
Definition eval_value (e : GExpr) : option GoAny :=
  match ptype e with
  | Some (PtIntConst z)    => box_int GTInt z                                                 (* untyped const -> default [int], range-checked *)
  | Some (PtTIntConst t z) => box_int t z                                                     (* typed int const (conversion / typed arith) *)
  | Some PtStr             => match e with EStr s => Some (anyt TString s) | _ => None end     (* a string LITERAL ([PtStr] carries no value) *)
  | _                      => None
  end.

Fixpoint eval_args (args : list GExpr) : option (list GoAny) :=
  match args with
  | [] => Some []
  | a :: rest =>
      match eval_value a, eval_args rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** Translate ONE statement to its command PAIRED WITH whether control TERMINATES here (i.e. its successors
    are UNREACHABLE), or [None] if outside slice 1's bridged subset.  Carrying the flag HERE makes [denote_stmt]
    the SINGLE control-flow authority — [denote_body] never re-decides which statements stop the body, so there
    is no second predicate to drift.  (The flag is ESSENTIAL, not derivable from the command: a [return] and a
    blank-assign both produce [CRet tt], yet the first STOPS the body and the second FALLS THROUGH.)
    The EFFECT arm ([GsExprStmt]) FIRES ONLY WHEN [expr_stmt_ok] holds (the gate's authority) — this is what
    makes [denote] ⊆ the gate, hence [gosem_sound], regardless of how partial [eval_value] is.  Faithful:
    [println]/[print] is a fall-through [COut] (model: [println=w_log true], [print=w_log false]); [panic] is a
    TERMINATING [CPan]; bare [return] TERMINATES with [CRet tt] (rest dropped by [denote_body]); a blank-assign
    of a LITERAL value is a fall-through, effect-free [CRet tt]. *)
Definition denote_stmt (s : GoStmt) : option (Cmd unit * bool) :=
  match s with
  | GsReturn        => Some (CRet tt, true)    (* TERMINATES the body *)
  | GsBlankAssign e =>
      (* [_ = e] discards [e]'s VALUE but NOT its runtime EFFECTS.  Denote it ONLY when slice-1 [eval_value]
         handles [e] (a scalar LITERAL — no effect, CANNOT panic), giving the faithful fall-through [CRet tt].
         A RUNTIME [e] (e.g. [1 / len([]int{})], which Go PANICS on) is left UN-denoted ([None]) until the
         evaluator models effects — GoSem must NEVER give it the WRONG (silent) behavior.  [svalue e] is still
         required so [denote] ⊆ the gate ([stmt_ok]'s blank arm IS [svalue]). *)
      if svalue e then match eval_value e with Some _ => Some (CRet tt, false) | None => None end else None
  | GsReturnVal _   => None                                        (* a value return is invalid in void [main] *)
  | GsExprStmt e =>
      if expr_stmt_ok e then
        match e with
        | ECall (EId f) args =>
            let fn := proj1_sig f in
            if String.eqb fn "panic"
            then match args with
                 | a :: nil => match eval_value a with Some v => Some (CPan v, true) | None => None end  (* TERMINATES *)
                 | _ => None
                 end
            else match eval_args args with                        (* println / print: fall through *)
                 | Some vs => Some (COut (String.eqb fn "println") vs (CRet tt), false)
                 | None => None
                 end
        | _ => None
        end
      else None
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
Lemma denote_stmt_sound : forall s, denote_stmt s <> None -> stmt_ok s = true.
Proof.
  intros s H. destruct s as [e| |e0|e]; simpl in *.
  - destruct (expr_stmt_ok e); [reflexivity | congruence].   (* GsExprStmt: gated on [expr_stmt_ok] *)
  - reflexivity.                                             (* GsReturn *)
  - congruence.                                              (* GsReturnVal: None *)
  - destruct (svalue e); [reflexivity | congruence].         (* GsBlankAssign: gated on [svalue] = stmt_ok *)
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

(** ---- A load-bearing end-to-end witness with REAL OBSERVABLE OUTPUT: a supported
    `func main(){ println("hi"); return }` denotes to a [Cmd unit] and RUNS through cmd.v's authoritative
    [run_cmd] to a World whose output trace records the `println` — FAITHFULLY, the very [w_log true ["hi"]]
    the model's own [println] produces. *)
Definition gosem_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "hi"]); GsReturn].
Example gosem_demo_supported : supported_program gosem_demo_prog = true.
Proof. reflexivity. Qed.
Example gosem_demo_denotes : denote_program gosem_demo_prog
                           = Some (COut true (anyt TString "hi" :: nil) (CRet tt)).
Proof. vm_compute. reflexivity. Qed.
Example gosem_demo_runs : forall w,
  match denote_program gosem_demo_prog with
  | Some c => run_cmd 5 c w
  | None => None
  end = Some (ORet tt (w_log true (anyt TString "hi" :: nil) w)).
Proof. intro w. vm_compute. reflexivity. Qed.

(** REGRESSION (P0, Codex 2026-06-30): [return] STOPS the body — a NON-tail return's successors do NOT run.
    `func main(){ return; println("after") }` is SUPPORTED (Go compiles it), yet prints NOTHING; GoSem denotes
    it to a no-output [CRet], NOT to running the [println].  [run_cmd] leaves the world UNCHANGED. *)
Definition gosem_return_stops_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsReturn; GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "after"])].
Example gosem_return_stops_supported : supported_program gosem_return_stops_prog = true.
Proof. reflexivity. Qed.
Example gosem_return_stops_no_output : forall w,
  match denote_program gosem_return_stops_prog with
  | Some c => run_cmd 5 c w
  | None => None
  end = Some (ORet tt w).   (* w UNCHANGED — no [w_log]; the [println] after [return] never runs *)
Proof. intro w. vm_compute. reflexivity. Qed.

(** REGRESSION (P0, Codex 2026-06-30, 2nd/3rd pass): a TERMINATOR ([return]/[panic]) must NOT depend on its
    UNREACHABLE successors DENOTING — only on them being SUPPORTED.  Witness: a SUPPORTED-but-UNDENOTABLE
    statement [println(len([]int{1}))] — [len] of a slice is a runtime [PtRunInt] (printable, so [stmt_ok] =
    true), but slice-1 [eval_value] does not model a runtime value, so [denote_stmt = None].  Pinned DIRECTLY
    (this stays undenotable as the integer-CONSTANT eval grows — it is runtime, not a constant): *)
Definition undenotable_succ : GoStmt :=
  GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                    [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]]).
Example undenotable_succ_supported   : stmt_ok undenotable_succ = true.    Proof. reflexivity. Qed.
Example undenotable_succ_undenotable : denote_stmt undenotable_succ = None. Proof. reflexivity. Qed.

(** `func main(){ return; <undenotable_succ> }` denotes (NOT [None]) to a no-output [CRet] — the [GsReturn] arm
    gates on [forallb stmt_ok rest], NOT [denote_body rest]. *)
Definition gosem_return_undenotable_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsReturn; undenotable_succ].
Example gosem_return_undenotable_supported : supported_program gosem_return_undenotable_prog = true.
Proof. reflexivity. Qed.
Example gosem_return_undenotable_no_output : forall w,
  match denote_program gosem_return_undenotable_prog with Some c => run_cmd 5 c w | None => None end
  = Some (ORet tt w).
Proof. intro w. vm_compute. reflexivity. Qed.

(** Likewise a denoted [panic] TERMINATES: `func main(){ panic("x"); <undenotable_succ> }` denotes (NOT [None])
    to a [CPan] despite the undenotable successor; [run_cmd] PANICS with [anyt TString "x"] and NO output. *)
Definition gosem_panic_terminates_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "x"]); undenotable_succ].
Example gosem_panic_terminates_supported : supported_program gosem_panic_terminates_prog = true.
Proof. reflexivity. Qed.
Example gosem_panic_terminates_runs : forall w,
  match denote_program gosem_panic_terminates_prog with Some c => run_cmd 5 c w | None => None end
  = Some (OPanic (anyt TString "x") w).
Proof. intro w. vm_compute. reflexivity. Qed.

(** REGRESSION (P0, Codex 2026-06-30): a RUNTIME blank-assign Go PANICS on — `_ = 1 / len([]int{})`
    ([len] of an empty slice = 0, a runtime divide-by-zero) — is SUPPORTED ([GoTypes] admits runtime division;
    the div-by-zero is GoSem's concern), but slice-1 [eval_value] does NOT model it, so GoSem leaves it
    UN-denoted ([denote_program = None]) rather than giving it the WRONG (silent, no-panic) behavior.  Once the
    evaluator models runtime panics this becomes a [CPan]; until then it is honestly absent, not wrong. *)
Definition gosem_runtime_blank_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EBn BDiv (EInt 1)
                              (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt []]))].
Example gosem_runtime_blank_supported : supported_program gosem_runtime_blank_prog = true.
Proof. reflexivity. Qed.
Example gosem_runtime_blank_undenoted : denote_program gosem_runtime_blank_prog = None.
Proof. reflexivity. Qed.

(** GROWTH (slice 1 -> integer conversions / arithmetic): [eval_value] now denotes any printable [ptype] folds
    to an integer constant, FAITHFULLY boxing it as the model's value.  Pinned per signedness/width + a folded
    binop; and END-TO-END, `println(int64(3))` runs to [w_log true [GoI64 3]]. *)
Example eval_int64_conv : eval_value (ECall (EId (mkIdent "int64" eq_refl)) [EInt 3])  = Some (anyt TI64 (i64wrap 3)).
Proof. vm_compute. reflexivity. Qed.
Example eval_uint8_conv : eval_value (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 5])  = Some (anyt TU8 (u8wrap 5)).
Proof. vm_compute. reflexivity. Qed.
Example eval_int8_conv  : eval_value (ECall (EId (mkIdent "int8" eq_refl)) [EInt 127]) = Some (anyt TI8 (i8wrap 127)).
Proof. vm_compute. reflexivity. Qed.
Example eval_arith_fold : eval_value (EBn BAdd (EInt 1) (EInt 2))                      = Some (anyt TInt64 (intwrap 3)).
Proof. vm_compute. reflexivity. Qed.
Definition gosem_conv_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]]); GsReturn].
Example gosem_conv_demo_supported : supported_program gosem_conv_demo_prog = true.
Proof. reflexivity. Qed.
Example gosem_conv_demo_runs : forall w,
  match denote_program gosem_conv_demo_prog with Some c => run_cmd 5 c w | None => None end
  = Some (ORet tt (w_log true (anyt TI64 (i64wrap 3) :: nil) w)).
Proof. intro w. vm_compute. reflexivity. Qed.

(** NEGATIVE (Codex 2026-06-30): the eval growth must FAIL CLOSED at the BOUNDARY, never carry a *wrap-mangled
    out-of-range value, and must NOT silently widen to [GTUint].  Pinned directly at [box_int] and end-to-end
    through [eval_value]: an out-of-range fixed-width value, an untyped const past the default-[int] range, and a
    [uint] conversion all evaluate to [None]. *)
Example box_int_oob_none    : box_int GTU8 300 = None.   (* 300 ∉ [0,255]: rejected at the builder, not [u8wrap]-mangled to 44 *)
Proof. reflexivity. Qed.
Example eval_default_oob_none : eval_value (EInt 2147483648) = None.   (* 2^31 ∉ GTInt's conservative 32-bit range *)
Proof. vm_compute. reflexivity. Qed.
Example eval_uint_absent    : eval_value (ECall (EId (mkIdent "uint" eq_refl)) [EInt 3]) = None.   (* [GTUint] intentionally absent (no proof-free [GoUint] box) *)
Proof. vm_compute. reflexivity. Qed.

(** GATE — GoSem is the (planned) behavioral trust base; keep it axiom-free.  These [Print Assumptions]
    surface in the build log so the axiom-manifest gate ([EXPECTED_ASSUMPTIONS.txt], empty) catches any axiom
    GoSem might pull in via [cmd]/[builtins]. *)
Print Assumptions gosem_sound.
Print Assumptions gosem_demo_runs.
