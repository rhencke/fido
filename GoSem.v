(** ============================================================================
    GoSem.v — the FIRST behavioral-semantics slice (Phase 5 "GoSem"; ARCHITECTURE.md
    spine GoAst -> GoPrint -> GoSem -> GoSafe -> GoEmit).

    ⚠️ HONEST SCOPE — read this before citing the file.

    This is the FIRST behavioral slice of GoSem.  It denotes ONLY the OUTPUT / panic
    behavior of the SUPPORTED statement subset — [GsExprStmt] calls to
    [println]/[print]/[panic], a bare [GsReturn], and a discarding [GsBlankAssign] —
    by BRIDGING the existing [cmd.v] semantics: a supported-subset statement list is
    mapped to a [cmd.Cmd unit], and its observable behaviour is read through builtins'
    [run_io] / [w_output].  It DEFINES NO new IO / output / outcome model (charter: do
    NOT fork a second semantics — [cmd.Cmd] / [denote] / [run_io] / [World] are reused
    verbatim).  [cmd.denote] DROPS [CDfr] (defers), but the supported subset has NO
    defers, so the bridge is exact / fuel-free here.

    It is NOT (yet), and must not be described as:
      • the full authoritative GoSem — only [println]/[print]/[panic]/[return]/[_ = e]
        statements are denoted; everything else is rejected ([None]);
      • a complete expression evaluator — [eval] covers a SMALL CORE (integer constants
        under +/-/*, the default-[int] and [int64] scalar conversions, and string
        literals), FAR less than GoSafe.ptype's supported subset.  Any other form (free
        identifiers, other conversions, slices/maps, [len]/[cap], booleans, floats, …)
        is [None] = "outside THIS slice's denotational scope", which is explicitly NOT a
        claim about Go's behaviour;
      • accompanied by an eval-vs-ptype SOUNDNESS theorem (that [eval] agrees with the
        GoSafe type/category analysis) — future work;
      • [BehaviorSafe] (the GoSafe behavioral gate) — also future work.

    So do NOT call this "the semantics" or imply completeness.  It is one small, faithful,
    zero-axiom behavioral slice that BRIDGES cmd.v.

    DESIGN — partiality (the None handling).  [denote_stmt]/[denote_body] are PARTIAL
    ([option]-valued): a statement whose argument is outside [eval]'s core yields [None],
    propagated to [None] for the whole body, surfaced as [gosem_run = None] = "this
    program is outside the current denotational scope".  This is the honest choice: it
    NEVER fabricates output, NEVER drops an output/panic event, and NEVER invents a Go
    panic for an un-modelled form (it would be unfaithful to denote an un-evaluable
    [println] as either a silent skip or a fake panic).  [GsBlankAssign e] denotes to the
    continuation [k] WITHOUT evaluating [e] — the value is discarded and the supported
    blank-assign subset is side-effect-free (e.g. [_ = []int(nil)] / [_ = []int{1}]),
    so no observable event is produced; this is faithful and avoids depending on [eval]
    covering composite literals / conversions (which it does not, yet).
    ============================================================================ *)
From Fido Require Import builtins cmd GoAst GoPrint GoSafe GoEmit.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.

(** ---- [eval_int] : the integer-CONSTANT core ---- the EXACT integer value (a [Z], Go
    untyped-constant arithmetic) of the constant subset [EInt] / [EBn BAdd|BSub|BMul].
    [None] for anything else (this is intentionally tiny — it is what [demo_prog] needs
    plus the obvious constant-arithmetic core). *)
Fixpoint eval_int (e : GExpr) : option Z :=
  match e with
  | EInt z => Some z
  | EBn BAdd l r =>
      match eval_int l, eval_int r with Some a, Some b => Some (a + b)%Z | _, _ => None end
  | EBn BSub l r =>
      match eval_int l, eval_int r with Some a, Some b => Some (a - b)%Z | _, _ => None end
  | EBn BMul l r =>
      match eval_int l, eval_int r with Some a, Some b => Some (a * b)%Z | _, _ => None end
  | _ => None
  end.

(** ---- [eval] : const-fold a SUPPORTED expression to a TAGGED Go value ([GoAny]) ----
    SCOPE (small + faithful, NOT all of ptype's subset — see the header):
      • [EStr s]                         -> the string value [s] (tag [TString]);
      • a scalar numeric conversion [t(a)] = [ECall (EId t) [a]] for [t] one of the
        numeric type keywords this slice models — [int64(a)] -> the [int64] value of
        [a] (tag [TI64], via [i64wrap]); [int(a)] -> the [int] value (tag [TInt64], via
        [intwrap]).  (Other numeric keywords are out of scope here -> [None].)
      • otherwise the integer-constant core: an evaluable [EInt]/[EBn] folds to the
        default-[int] value (tag [TInt64], via [intwrap]).
    [None] for every unevaluable / unsupported form.  This computes what Go computes:
    [1 + 2] = the int 3, [int64(3)] = the int64 3, ["hi"] = the string "hi". *)
Definition eval (e : GExpr) : option GoAny :=
  match e with
  | EStr s => Some (anyt TString s)
  | ECall (EId f) (a :: nil) =>
      match classify (proj1_sig f) with
      | Some GTInt64 =>
          match eval_int a with Some z => Some (anyt TI64 (i64wrap z)) | None => None end
      | Some GTInt =>
          match eval_int a with Some z => Some (anyt TInt64 (intwrap z)) | None => None end
      | _ => None
      end
  | _ =>
      match eval_int e with Some z => Some (anyt TInt64 (intwrap z)) | None => None end
  end.

(** Evaluate an argument list left-to-right; [Some] iff EVERY argument evaluates (an
    out-of-scope argument makes the whole call out of scope — never silently dropped). *)
Fixpoint eval_args (es : list GExpr) : option (list GoAny) :=
  match es with
  | nil => Some nil
  | e :: rest =>
      match eval e, eval_args rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** ---- [denote_stmt s k] : denote one supported statement, given continuation [k] ----
    [println(args)] -> [COut true (eval args) k]; [print(args)] -> [COut false … k];
    [panic(a)] -> [CPan (eval a)] (DROPS [k] — a panic short-circuits, as Go); a bare
    [GsReturn] -> [k] (normal fall-through); [GsBlankAssign e] -> [k] (discard, no event:
    [e] is NOT evaluated — see header).  PARTIAL: [None] if a denoted argument is outside
    [eval]'s core, or for any statement shape outside this subset ([GsReturnVal], a
    non-call / non-whitelisted expression statement). *)
Definition denote_stmt (s : GoStmt) (k : Cmd unit) : option (Cmd unit) :=
  match s with
  | GsExprStmt (ECall (EId f) args) =>
      let fn := proj1_sig f in
      if String.eqb fn "println" then option_map (fun xs => COut true xs k) (eval_args args)
      else if String.eqb fn "print" then option_map (fun xs => COut false xs k) (eval_args args)
      else if String.eqb fn "panic" then
        match args with
        | a :: nil => option_map (@CPan unit) (eval a)   (* panic ignores [k]: it short-circuits *)
        | _ => None
        end
      else None
  | GsExprStmt _    => None
  | GsReturn        => Some k
  | GsReturnVal _   => None
  | GsBlankAssign _ => Some k
  end.

(** ---- [denote_body b] : a supported statement list -> a [cmd.Cmd unit] ----
    right-fold with base [CRet tt] (normal termination); PARTIAL ([None] if any statement
    is out of scope). *)
Fixpoint denote_body (b : list GoStmt) : option (Cmd unit) :=
  match b with
  | nil => Some (CRet tt)
  | s :: rest =>
      match denote_body rest with
      | Some k => denote_stmt s k
      | None   => None
      end
  end.

(** ---- THE OBSERVABLE ---- run the denoted body through cmd.v's [denote] (Cmd -> IO) and
    builtins' [run_io] from the empty world [w_init].  [None] = out of denotational scope.
    [cmd.denote] is the bridge to the ONE existing semantics — no new model is introduced. *)
Definition gosem_run (b : list GoStmt) : option (Outcome unit) :=
  match denote_body b with
  | Some c => Some (run_io (cmd.denote c) w_init)
  | None   => None
  end.

(** ---- THE DELIVERABLE (the first behavioral theorem) ----
    [GoEmit.demo_prog]'s body runs to a NORMAL outcome ([ORet tt], NOT a panic — the
    [return] terminates normally) emitting EXACTLY the four [println] lines, in order:
      [println(1)]          -> the int    value 1   (Go prints "1")
      [println(int64(3))]   -> the int64  value 3   (Go prints "3")
      [println(1 + 2)]      -> the int    value 3   (Go prints "3")
      [println("hi")]       -> the string value "hi" (Go prints "hi")
    The two [GsBlankAssign]s ([_ = []int(nil)], [_ = []int{1}]) emit NOTHING, and the
    trailing bare [return] terminates normally.  This is the genuinely-correct Go
    behaviour of [demo_prog].

    The [match]-Prop shape pins, in one [vm_compute; reflexivity], that the result is
    (a) [Some] (the program is within denotational scope), (b) [ORet] (normal, NOT
    [OPanic]), (c) returning [tt], AND (d) the EXACT 4-event output trace.  Were it [None]
    / [OPanic] / a different trace, the goal would not reduce to [reflexivity]. *)
Theorem gosem_demo_output :
  match gosem_run (prog_body demo_prog) with
  | Some (ORet tt w') =>
      w_output w' =
        [ (true, [anyt TInt64 (intwrap 1)]);
          (true, [anyt TI64   (i64wrap 3)]);
          (true, [anyt TInt64 (intwrap 3)]);
          (true, [anyt TString "hi"]) ]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** GATE — GoSem is a (proof-only) behavioral slice; keep it axiom-free.  This [Print
    Assumptions] surfaces the trust base of the deliverable in the build log; the Docker
    prover-stage axiom-manifest gate (and [make gosem-verify]) FAIL the build on ANY axiom,
    so "Closed under the global context" here is enforced, not decorative. *)
Print Assumptions gosem_demo_output.
