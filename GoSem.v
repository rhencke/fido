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
      - bare [return]   -> [CRet tt]
      - [_ = e] (svalue e) -> a pure value discarded, no effect -> [CRet tt]
    [eval_value] (slice 1: string / int / hex LITERALS, boxed via the model's [anyt]/[intwrap]) supplies the
    printed/panicked values; conversions/arithmetic/etc. are the next slice and [eval] to [None] there.
    SOUNDNESS is structural and clean because [denote] CONSULTS THE GATE: the effect arm fires only when
    [expr_stmt_ok] holds, so [gosem_sound] — denotation ⊆ [SupportedProgram], no meaning given to invalid Go —
    falls out, and a PARTIAL [eval_value] can grow without ever over-accepting (it only narrows COMPLETENESS,
    never breaks soundness).  COMPLETENESS (supported ⇒ denotes) is the roadmap converse, reached as [eval]
    covers the full printable subset; together they will pin "supported ⟺ has a defined GoSem behavior", the
    foundation for [BehaviorSafe] -> [SafeProgram] -> [emit_safe].  No axioms.
    ============================================================================ *)
From Fido Require Import GoAst GoTypes GoSafe cmd preamble.   (* [preamble] re-exports [builtins]: [GoAny]/[anyt]/[intwrap]/[World]/[w_log]/[Outcome]/[ORet] *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.

(** Evaluate a PRINTABLE value expression to the MODEL's runtime [GoAny], or [None] if outside slice 1's
    bridged subset.  Slice 1: the literals — a string literal is the model string [anyt TString s]; an integer
    / hex literal takes its DEFAULT type [int] = the model's [GoInt] ([anyt TInt64 (intwrap z)]).  These are
    the exact values the model's [println]/[panic] would carry, so the denotation is FAITHFUL.  Conversions
    ([int64(x)]), arithmetic ([1+2]), [len(..)], bools (from comparisons) — all [None] here, the next slice. *)
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
  | GsReturn        => Some (CRet tt)
  | GsBlankAssign e => if svalue e then Some (CRet tt) else None   (* pure value, discarded — no effect *)
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
      match denote_stmt s, denote_body rest with
      | Some c, Some k => Some (cbind c (fun _ => k))
      | _, _ => None
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
  - destruct (denote_stmt s) eqn:Es; [|congruence].
    destruct (denote_body rest) eqn:Er; [|congruence].
    apply andb_true_intro; split.
    + apply denote_stmt_sound. congruence.
    + apply IH. congruence.
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

(** GATE — GoSem is the (planned) behavioral trust base; keep it axiom-free.  These [Print Assumptions]
    surface in the build log so the axiom-manifest gate ([EXPECTED_ASSUMPTIONS.txt], empty) catches any axiom
    GoSem might pull in via [cmd]/[builtins]. *)
Print Assumptions gosem_sound.
Print Assumptions gosem_demo_runs.
