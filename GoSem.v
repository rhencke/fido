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
      - [return]        -> STOPS the body ([denote_body]: the rest's commands are DROPPED, so a non-tail
                           `return; println("bad")` faithfully produces NO output).  The unreachable rest need
                           only be SUPPORTED ([forallb stmt_ok]), NOT denotable — a return never depends on a
                           successor slice 1 cannot yet evaluate.
      - [_ = e]         -> [CRet tt] ONLY when [e] is a scalar LITERAL ([eval_value e <> None] — no effect /
                           no panic); a RUNTIME [e] (e.g. [1/len([]int{})], which Go PANICS on) is UN-denoted
    [eval_value] (slice 1: string / int / hex LITERALS, boxed via the model's [anyt]/[intwrap]) supplies the
    printed/panicked values; conversions/arithmetic/etc. are the next slice and [eval] to [None] there.
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

(** Evaluate a literal value expression to the MODEL's runtime [GoAny], or [None] if outside slice 1's
    bridged subset.  Slice 1: the LITERALS — a string literal is the model string [anyt TString s]; an integer
    / hex literal takes its DEFAULT type [int] = the model's [GoInt] ([anyt TInt64 (intwrap z)]).  These are
    the exact values the model's [println]/[panic] would carry, so the denotation is FAITHFUL.  Conversions
    ([int64(x)]), arithmetic ([1+2]), [len(..)], bools (from comparisons) — all [None] here, the next slice.
    ⚠ RAW evaluator with a CALLER-SIDE precondition: it boxes any [EInt z] (the out-of-range box is [intwrap]-
    WRAPPED, not faithful), so it is sound ONLY when the caller has GATED [e] (range-checked it supported) —
    [denote_stmt] always does (via [expr_stmt_ok] / [svalue]).  It is also the slice's "can I evaluate this
    with NO runtime effect?" oracle: every literal it accepts is panic-free, so a [Some] means safe to denote. *)
Definition eval_value (e : GExpr) : option GoAny :=
  match e with
  | EStr s  => Some (anyt TString s)
  | EInt z  => Some (anyt TInt64 (intwrap z))                 (* untyped const -> default int = [GoInt] *)
  | EHex zc => Some (anyt TInt64 (intwrap (proj1_sig zc)))    (* a hex literal is a non-negative int const *)
  | _       => None
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

(** Translate ONE statement to a [Cmd unit], or [None] if outside slice 1's bridged subset.  The EFFECT arm
    ([GsExprStmt]) FIRES ONLY WHEN [expr_stmt_ok] holds (the gate's own authority) — this is what makes
    [denote] ⊆ the gate, hence [gosem_sound], regardless of how partial [eval_value] is.  [println]/[print]
    become [COut] with the faithful output bool (model: [println=w_log true], [print=w_log false]); [panic]
    becomes [CPan]; [return] / blank-assign-of-a-value are effect-free [CRet tt].  A [COut]'s continuation is a
    placeholder [CRet tt] that [denote_body]'s [cbind] threads the rest onto. *)
Definition denote_stmt (s : GoStmt) : option (Cmd unit) :=
  match s with
  | GsReturn        => Some (CRet tt)   (* a statement's LOCAL meaning; [denote_body] adds [return]'s control flow (it STOPS the body) *)
  | GsBlankAssign e =>
      (* [_ = e] discards [e]'s VALUE but NOT its runtime EFFECTS.  Denote it ONLY when slice-1 [eval_value]
         handles [e] (a scalar LITERAL — evaluation has NO effect and CANNOT panic), giving the faithful
         [CRet tt].  A RUNTIME [e] (e.g. [1 / len([]int{})], which Go PANICS on) is left UN-denoted ([None])
         until the evaluator models effects — GoSem must NEVER give it the WRONG (silent, no-panic) behavior.
         [svalue e] is still required so [denote] ⊆ the gate ([stmt_ok]'s blank arm IS [svalue]). *)
      if svalue e then match eval_value e with Some _ => Some (CRet tt) | None => None end else None
  | GsReturnVal _   => None                                        (* a value return is invalid in void [main] *)
  | GsExprStmt e =>
      if expr_stmt_ok e then
        match e with
        | ECall (EId f) args =>
            let fn := proj1_sig f in
            if String.eqb fn "panic"
            then match args with
                 | a :: nil => match eval_value a with Some v => Some (CPan v) | None => None end
                 | _ => None
                 end
            else match eval_args args with                        (* println / print *)
                 | Some vs => Some (COut (String.eqb fn "println") vs (CRet tt))
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
      | Some c =>
          match s with
          | GsReturn =>
              (* [return] STOPS the function: the command is [c] (= [CRet tt]), with the REST DROPPED.  The
                 rest is UNREACHABLE, so its DENOTABILITY is irrelevant — we require only that it be SUPPORTED
                 ([forallb stmt_ok rest], the gate), NOT that it denote.  This keeps [denote_body] ⊆ the gate
                 (for [gosem_sound]) while NOT making a [return] depend on a successor slice 1 cannot yet
                 evaluate: `return; println(int64(3))` (supported, not-yet-denotable) faithfully denotes to a
                 no-output [CRet]. *)
              if forallb stmt_ok rest then Some c else None
          | _ =>
              match denote_body rest with
              | Some k => Some (cbind c (fun _ => k))
              | None => None
              end
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
  - destruct (denote_stmt s) eqn:Es; [|congruence].   (* denote_stmt s = None => denote_body = None *)
    apply andb_true_intro; split.
    + apply denote_stmt_sound. congruence.             (* stmt_ok s, uniform via [Es] *)
    + destruct s; simpl in H.                          (* the tail: GsReturn uses the gate, others use [denote_body rest] *)
      * (* GsExprStmt *) destruct (denote_body rest) eqn:Er; [|congruence]. apply IH. congruence.
      * (* GsReturn — required [forallb stmt_ok rest] directly, NOT [denote_body rest] *)
        destruct (forallb stmt_ok rest) eqn:Ef; [reflexivity | congruence].
      * (* GsReturnVal — [denote_stmt = None] contradicts [Es] *) discriminate Es.
      * (* GsBlankAssign *) destruct (denote_body rest) eqn:Er; [|congruence]. apply IH. congruence.
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

(** REGRESSION (P0, Codex 2026-06-30, 2nd pass): a [return] must NOT depend on its UNREACHABLE successors
    DENOTING — only on them being SUPPORTED.  `func main(){ return; println(int64(3)) }` is supported, and its
    successor [println(int64(3))] is NOT yet denotable by slice 1 (no [eval_value] for conversions), yet the
    program faithfully denotes to a no-output [CRet] (the [println] never runs).  Pins that the [GsReturn] arm
    gates on [forallb stmt_ok rest], not on [denote_body rest]. *)
Definition gosem_return_undenotable_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsReturn; GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                                         [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]])].
Example gosem_return_undenotable_supported : supported_program gosem_return_undenotable_prog = true.
Proof. reflexivity. Qed.
Example gosem_return_undenotable_no_output : forall w,
  match denote_program gosem_return_undenotable_prog with
  | Some c => run_cmd 5 c w
  | None => None
  end = Some (ORet tt w).   (* denotes (NOT [None]) to a no-output [CRet], despite the un-denotable successor *)
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

(** GATE — GoSem is the (planned) behavioral trust base; keep it axiom-free.  These [Print Assumptions]
    surface in the build log so the axiom-manifest gate ([EXPECTED_ASSUMPTIONS.txt], empty) catches any axiom
    GoSem might pull in via [cmd]/[builtins]. *)
Print Assumptions gosem_sound.
Print Assumptions gosem_demo_runs.
