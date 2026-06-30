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
    [eval_value] (slice 1: a string LITERAL, plus any printable [ptype] that folds to a NUMERIC CONSTANT — an
    INTEGER constant (literals, CONVERSIONS [int64(3)], ARITHMETIC [1+2], complement [^x], EXCLUDING [GTUint])
    or an exact-integer-valued FLOAT constant ([float64(3)], [-float32(5)]) — boxed via the model's value ctors,
    failing closed on an out-of-range/out-of-interval value; plus a constant bool built from NUMERIC or
    STRING-LITERAL comparisons (string compares DELEGATED to the model's [str_*] family — no local GoSem order)
    combined by [==]/[!=]/[&&]/[||]/[!], plus the identity [bool(x)] conversion) supplies the printed/panicked
    values; a comparison with a NON-literal string operand, bools with a runtime operand, non-literal strings,
    [GTUint], fractional/runtime floats, and RUNTIME values ([len(..)]/[int(x)]…) are the next sub-slices and [eval] to
    [None] there.
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
    carries).  [GTUint] stays [None] (no proof-free [GoUint] wrap yet); floats go through [box_float] below. *)
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

(** The constant VALUE of a string operand: ONLY a string LITERAL [EStr s] (whose bytes are known); a
    non-literal string (e.g. [string(65)]) carries no recoverable value -> [None] (honestly absent). *)
Definition const_str (e : GExpr) : option string :=
  match e with EStr s => Some s | _ => None end.

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

(** Fold a CONSTANT bool expression to its [bool], or [None] if any leaf is runtime / not yet modelled.  GoSem
    is the home for bool VALUE because [ptype] keeps [PtBool] a value-less category (comparison/logical results
    are SEMANTICS, not classification).
    ★SELF-SEALED: every entry (top AND each recursive call) first demands [ptype e = Some PtBool], so [eval_bool]
    can NEVER assign a value to an expression [ptype] rejects — a direct call on a ptype-rejected (e.g.
    mixed-width [int64(1)==int32(1)]) comparison returns [None], NOT a value.  The precondition is thus
    ENFORCED here, not assumed of the caller (so [const_z]'s type-erasure can never fold an ill-typed compare).
    Inside the gate it reuses [ptype]'s numeric operand values ([const_z]) / string literals ([const_str]) and
    recurses STRUCTURALLY (terminates) over the bool forms:
      - a COMPARISON: NUMERIC (the 6 ops via [cmp_op]/[const_z]), STRING-LITERAL (the 6 ops via
        [str_cmp_op]/[const_str]), or [==]/[!=] of two bool sub-bools;
      - the LOGICAL connectives [&&]/[||] (short-circuit is irrelevant — constants have no effects) and [!];
      - the identity bool CONVERSION [bool(x)] (Go allows it only for an already-bool [x]) -> the value of [x].
    NOT folded (-> [None], honestly absent): a comparison whose string operand is NON-literal ([string(65)],
    no recoverable value) and any RUNTIME-operand leaf. *)
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
              match str_cmp_op op, const_str a, const_str b with
              | Some scmp, Some s, Some t => Some (scmp s t)               (* string-LITERAL comparison *)
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

(** Evaluate a value expression to the MODEL's runtime [GoAny], or [None] if outside slice 1's bridged subset.
    FAITHFUL via [ptype] — the SINGLE constant-folding authority: [ptype] already folds a numeric constant to
    its VALUE and TYPE ([PtIntConst z] = untyped int, taking default [int]; [PtTIntConst t z] = a typed int
    const, e.g. a conversion [int64(3)] or typed-const arithmetic; [PtFloatConst t z] = a typed float const that
    came from the EXACT integer [z]), and [box_int] / [box_float] attach the model value, FAILING CLOSED on an
    out-of-range / out-of-interval [z] (so [eval_value] is self-sound, not caller-gated).  Live coverage: a
    string LITERAL ([anyt TString s], matched syntactically since [PtStr] carries no value), an untyped integer
    constant whose default-[int] value is in range, a supported TYPED integer constant (literals, CONVERSIONS
    [int64(3)] EXCLUDING [GTUint], ARITHMETIC [1+2], complement [^x]), and a TYPED FLOAT constant of an exact
    integer value ([float64(3)], [-float32(5)]) — with NO second folding logic.  Bools: [ptype] keeps [PtBool]
    a pure CATEGORY (no value — comparison/logical VALUES are SEMANTICS, GoSem's job, not the classifier's), so
    GoSem folds a constant bool HERE via the self-sealed [eval_bool] — a bool built from NUMERIC or
    STRING-LITERAL comparisons combined by [==]/[!=]/[&&]/[||]/[!], plus the identity [bool(x)] conversion,
    reusing the operands' [ptype] values via [const_z] / [const_str].  ABSENT (-> [None], the next sub-slices):
    a comparison with a NON-literal string operand, a bool with a RUNTIME operand, non-literal strings, [GTUint],
    and all RUNTIME numeric values ([PtRunInt]/[PtRunFloat]: [len(..)], [int(x)]…).  Honestly absent, never
    wrong. *)
Definition eval_value (e : GExpr) : option GoAny :=
  match ptype e with
  | Some (PtIntConst z)     => box_int GTInt z                                                 (* untyped const -> default [int], range-checked *)
  | Some (PtTIntConst t z)  => box_int t z                                                     (* typed int const (conversion / typed arith) *)
  | Some (PtFloatConst t z) => box_float t z                                                   (* typed float const (exact int-valued: [float64(3)], [-float32(5)]) *)
  | Some PtStr              => match e with EStr s => Some (anyt TString s) | _ => None end     (* a string LITERAL ([PtStr] carries no value) *)
  | Some PtBool             => match eval_bool e with Some b => Some (anyt TBool b) | None => None end   (* a CONSTANT bool: comparison / logical fold *)
  | _                       => None
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

(** ---- DENOTABILITY IS DECIDABLE, characterized STRUCTURALLY (the converse-direction companion of
    [gosem_sound] / [denote_body_sound]).  [denotable_body] is a pure [bool] decision procedure mirroring
    [denote_body]'s discipline: a body denotes iff its head statement denotes ([denote_stmt s <> None]) AND —
    at a TERMINATOR — the unreachable rest is merely SUPPORTED ([forallb stmt_ok rest]), else the rest is
    itself denotable.  [denote_body_dec] proves the two AGREE: denotability decomposes statement-by-statement,
    with NO body-level failure mode of its own beyond [denote_stmt]'s.  This is the SCAFFOLD toward the eventual
    "supported ⟺ denotes": as [eval_value] grows toward total on the supported value forms, [denotable_*]
    converges to [supported_*]; TODAY it pins the EXACT denotable fragment as a decidable predicate.  (It is a
    CHARACTERIZATION/decidability result, NOT yet [supported_program ⟹ denotes] — [eval_value] is partial.) *)
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

(** UNIVERSAL TERMINATOR PROPERTY (consolidates the old undenotable-successor witnesses, Codex 2026-06-30):
    a TERMINATOR ([return] / a denoted [panic]) must NOT depend on its UNREACHABLE successors DENOTING — only on
    their SUPPORTEDNESS.  Stated for ALL [s]/[c]/[rest]: whenever [denote_stmt] marks [s] terminating
    ([Some (c, true)]), [denote_body] emits [c] and gates the rest ONLY on [forallb stmt_ok rest], NEVER on
    [denote_body rest].  A UNIVERSAL lemma (not a fixture) so it can never erode as [eval_value] grows — the old
    test needed a supported-but-UNDENOTABLE successor, a witness that shrinks toward nonexistent (the
    no-variable model makes every supported expr ultimately evaluable, see the eval-growth roadmap). *)
Lemma denote_body_terminator_ignores_succ : forall s c rest,
  denote_stmt s = Some (c, true) ->
  denote_body (s :: rest) = (if forallb stmt_ok rest then Some c else None).
Proof. intros s c rest H. cbn [denote_body]. rewrite H. reflexivity. Qed.

(** The two terminators the lemma covers (so it is not vacuous): bare [return] -> [CRet tt], and a denoted
    [panic("x")] -> [CPan (anyt TString "x")], each with the [true] terminates-flag. *)
Example denote_stmt_return_terminates : denote_stmt GsReturn = Some (CRet tt, true).
Proof. reflexivity. Qed.
Example denote_stmt_panic_terminates :
  denote_stmt (GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "x"]))
  = Some (CPan (anyt TString "x"), true).
Proof. vm_compute. reflexivity. Qed.

(** A denoted [panic] TERMINATES end-to-end: `func main(){ panic("x") }` denotes to a [CPan] and [run_cmd]
    PANICS with [anyt TString "x"]. *)
Definition gosem_panic_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "x"])].
Example gosem_panic_demo_supported : supported_program gosem_panic_demo_prog = true.
Proof. reflexivity. Qed.
Example gosem_panic_demo_runs : forall w,
  match denote_program gosem_panic_demo_prog with Some c => run_cmd 5 c w | None => None end
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

(** GROWTH (slice 1 -> exact-integer-valued FLOAT constants): [eval_value] now denotes a [PtFloatConst] too,
    boxing it as the model's UNIQUE canonical binary64/binary32 value (faithful — inside the contiguous-exact
    interval every integer is exact).  Pinned for [float64]/[float32]; the boundary fails closed; and
    END-TO-END `println(float64(3))` runs to [w_log true [GoFloat64 3.0]] (the canonical binary64 of 3). *)
Example eval_float64_conv : eval_value (ECall (EId (mkIdent "float64" eq_refl)) [EInt 3])
                          = Some (anyt TFloat64 (renorm 53 1024 (sf_of_Z 3))).
Proof. vm_compute. reflexivity. Qed.
Example eval_float32_conv : eval_value (ECall (EId (mkIdent "float32" eq_refl)) [EInt 5])
                          = Some (anyt TFloat32 (f32_lit (sf_of_Z 5))).
Proof. vm_compute. reflexivity. Qed.
Example box_float_oob_none : box_float GTFloat64 9007199254740993 = None.   (* 2^53+1 ∉ [-2^53,2^53] (NOT exactly representable): rejected at the builder *)
Proof. reflexivity. Qed.
Definition gosem_float_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "float64" eq_refl)) [EInt 3]]); GsReturn].
Example gosem_float_demo_supported : supported_program gosem_float_demo_prog = true.
Proof. reflexivity. Qed.
Example gosem_float_demo_runs : forall w,
  match denote_program gosem_float_demo_prog with Some c => run_cmd 5 c w | None => None end
  = Some (ORet tt (w_log true (anyt TFloat64 (renorm 53 1024 (sf_of_Z 3)) :: nil) w)).
Proof. intro w. vm_compute. reflexivity. Qed.

(** GROWTH (slice 1 -> constant bools): [eval_value] folds — via [eval_bool] — a bool built from NUMERIC
    comparisons (the 6 ops) combined by [==]/[!=]/[&&]/[||]/[!] (nested).  Pinned across the operators (incl. a
    false case, exact-float operands, a bool-equality of two numeric compares, and a NESTED `!((1==1) && (2==3))`);
    END-TO-END `println(3 < 5)` runs to [w_log true [true]].  (String-literal comparisons and the identity
    [bool(x)] conversion are folded too — see the next block.)  ABSENT (-> [None], pinned below): any bool with
    a RUNTIME operand ([len(..)==0], even under [&&]). *)
Example eval_bool_eq     : eval_value (EBn BEq (EInt 1) (EInt 1)) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_lt     : eval_value (EBn BLt (EInt 3) (EInt 5)) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_false  : eval_value (EBn BEq (EInt 1) (EInt 2)) = Some (anyt TBool false).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_float  : eval_value (EBn BEq (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2])
                                               (ECall (EId (mkIdent "float64" eq_refl)) [EInt 2]))
                         = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_and    : eval_value (EBn BLAnd (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2))) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_or     : eval_value (EBn BLOr  (EBn BEq (EInt 1) (EInt 2)) (EBn BLt (EInt 3) (EInt 5))) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_not    : eval_value (EUn UNot (EBn BEq (EInt 1) (EInt 2))) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_booleq : eval_value (EBn BEq (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2))) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_nested : eval_value (EUn UNot (EBn BLAnd (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 3)))) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_runtime_absent :   (* a comparison with a RUNTIME [len(..)] operand: honestly absent, not folded wrong *)
  eval_value (EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0)) = None.
Proof. reflexivity. Qed.
Example eval_bool_logic_runtime_absent :   (* a RUNTIME operand even UNDER [&&] makes the whole fold absent (not folded wrong) *)
  eval_value (EBn BLAnd (EBn BEq (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]) (EInt 0))
                        (EBn BEq (EInt 2) (EInt 2))) = None.
Proof. reflexivity. Qed.

(** SEAL REGRESSION (Codex 2026-06-30): [eval_bool] FAILS CLOSED on a [ptype]-rejected comparison — it does NOT
    rely on a caller having gated.  A mixed-WIDTH typed comparison [int64(1) == int32(1)] is ILL-TYPED (Go
    forbids comparing distinct int types), so [ptype = None]; a DIRECT [eval_bool] call AND [eval_value] both
    return [None], never a fabricated [true] from [const_z]'s type-erased values. *)
Definition mixed_width_cmp : GExpr :=
  EBn BEq (ECall (EId (mkIdent "int64" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "int32" eq_refl)) [EInt 1]).
Example mixed_width_ptype_none     : ptype mixed_width_cmp = None.      Proof. reflexivity. Qed.
Example mixed_width_eval_bool_none : eval_bool mixed_width_cmp = None.  Proof. reflexivity. Qed.
Example mixed_width_eval_none      : eval_value mixed_width_cmp = None. Proof. reflexivity. Qed.

(** GROWTH (slice 1 -> STRING comparisons + identity bool CONVERSION): [eval_value] now folds a comparison of
    two string LITERALS — DELEGATED to the model's byte-wise order ([str_eqb]/[str_ltb]/[str_gtb]/[str_geb]) —
    and the identity [bool(x)] conversion.  Pinned across all 6 ops [==]/[!=]/[<]/[<=]/[>]/[>=] (incl. a false
    case, the prefix case ["a" < "ab"], and a HIGH-BYTE pair confirming UNSIGNED byte order: ["\200" > "\100"]),
    and [bool(1==1)].  STILL ABSENT: a comparison whose string operand is NON-literal ([string(65)] carries no
    recoverable value). *)
Example eval_str_cmp_supported : ptype (EBn BEq (EStr "a") (EStr "a")) = Some PtBool.
Proof. reflexivity. Qed.
Example eval_str_eq     : eval_value (EBn BEq (EStr "a") (EStr "a")) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_ne     : eval_value (EBn BNe (EStr "a") (EStr "b")) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_lt     : eval_value (EBn BLt (EStr "a") (EStr "b")) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_lt_f   : eval_value (EBn BLt (EStr "b") (EStr "a")) = Some (anyt TBool false).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_le_eq  : eval_value (EBn BLe (EStr "a") (EStr "a")) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_gt     : eval_value (EBn BGt (EStr "b") (EStr "a")) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_prefix : eval_value (EBn BLt (EStr "a") (EStr "ab")) = Some (anyt TBool true).   (* "" < "b" tail: shorter prefix is less *)
Proof. vm_compute. reflexivity. Qed.
Example eval_str_ge     : eval_value (EBn BGe (EStr "b") (EStr "a")) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_ge_f   : eval_value (EBn BGe (EStr "a") (EStr "b")) = Some (anyt TBool false).
Proof. vm_compute. reflexivity. Qed.
(** HIGH-BYTE: a 1-byte string of byte 200 vs byte 100.  UNSIGNED (the model's [str_ltb], via [u8raw]) gives
    [200 > 100 = true]; a SIGNED int8 read would give [-56 < 100 = false].  Pins GoSem's fold to the model's
    unsigned-byte order. *)
Example eval_str_highbyte : eval_value (EBn BGt (EStr (String (Ascii.ascii_of_nat 200) EmptyString))
                                                (EStr (String (Ascii.ascii_of_nat 100) EmptyString)))
                          = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_bool_conv_supported : ptype (ECall (EId (mkIdent "bool" eq_refl)) [EBn BEq (EInt 1) (EInt 1)]) = Some PtBool.
Proof. reflexivity. Qed.
Example eval_bool_conv : eval_value (ECall (EId (mkIdent "bool" eq_refl)) [EBn BEq (EInt 1) (EInt 1)]) = Some (anyt TBool true).
Proof. vm_compute. reflexivity. Qed.
Example eval_str_nonlit_absent :   (* a NON-literal string operand ([string(65)]) has no recoverable value -> absent *)
  eval_value (EBn BEq (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) (EStr "A")) = None.
Proof. reflexivity. Qed.
Definition gosem_bool_demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EBn BLt (EInt 3) (EInt 5)]); GsReturn].
Example gosem_bool_demo_supported : supported_program gosem_bool_demo_prog = true.
Proof. reflexivity. Qed.
Example gosem_bool_demo_runs : forall w,
  match denote_program gosem_bool_demo_prog with Some c => run_cmd 5 c w | None => None end
  = Some (ORet tt (w_log true (anyt TBool true :: nil) w)).
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

(** DENOTABILITY-DECISION witnesses: [denotable_program] (the decidable predicate of [denote_program_dec])
    agrees with whether the program denotes — TRUE for the denoting demos (`println("hi")`, the `return`-stops
    program), FALSE for the supported-but-undenoted runtime blank-assign `_ = 1/len([]int{})`. *)
Example denotable_demo          : denotable_program gosem_demo_prog = true.            Proof. reflexivity. Qed.
Example denotable_return_stops  : denotable_program gosem_return_stops_prog = true.    Proof. reflexivity. Qed.
Example denotable_runtime_blank : denotable_program gosem_runtime_blank_prog = false.  Proof. reflexivity. Qed.

(** GATE — GoSem is the (planned) behavioral trust base; keep it axiom-free.  These [Print Assumptions]
    surface in the build log so the axiom-manifest gate ([EXPECTED_ASSUMPTIONS.txt], empty) catches any axiom
    GoSem might pull in via [cmd]/[builtins]. *)
Print Assumptions gosem_sound.
Print Assumptions denote_program_dec.
Print Assumptions gosem_demo_runs.

(** ---- DELEGATION PINS (the AUTHORITY guarantee for the live path): EVERY one of [str_cmp_op]'s SIX comparison
    branches is, by reflexivity, the FULLY QUALIFIED model constant [Fido.builtins.str_*].  Because the names are
    qualified, these proofs are SHADOW-IMMUNE — a local/nested [str_ltb] in GoSem cannot reroute the live path
    without breaking a pin (the pin's RHS is the model constant, not a re-resolvable bare name), and rerouting a
    branch to a fork makes its pin FAIL the build.  ([<=] is the model's [str_geb] with operands swapped — pinned
    in its own right.)  GoSemAuthority.v is a secondary top-level tripwire ([Fail Check Fido.GoSem.str_*]); these
    pins are what mechanically tie the executed semantics to the model order. *)
Example str_cmp_eq_model : str_cmp_op BEq = Some Fido.builtins.str_eqb.                     Proof. reflexivity. Qed.
Example str_cmp_ne_model : str_cmp_op BNe = Some Fido.builtins.str_neqb.                    Proof. reflexivity. Qed.
Example str_cmp_lt_model : str_cmp_op BLt = Some Fido.builtins.str_ltb.                     Proof. reflexivity. Qed.
Example str_cmp_le_model : str_cmp_op BLe = Some (fun s t => Fido.builtins.str_geb t s).    Proof. reflexivity. Qed.
Example str_cmp_gt_model : str_cmp_op BGt = Some Fido.builtins.str_gtb.                     Proof. reflexivity. Qed.
Example str_cmp_ge_model : str_cmp_op BGe = Some Fido.builtins.str_geb.                     Proof. reflexivity. Qed.
