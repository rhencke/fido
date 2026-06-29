(** ============================================================================
    GoSem.v — the FIRST behavioral-semantics slice (Phase 5 "GoSem"; ARCHITECTURE.md
    spine GoAst -> GoPrint -> GoSem -> GoSafe -> GoEmit).

    ⚠️ HONEST SCOPE — read this before citing the file.

    This is the FIRST behavioral slice of GoSem.  It denotes ONLY the OUTPUT / panic
    behavior of the SUPPORTED statement subset — [GsExprStmt] calls to
    [println]/[print]/[panic], a [GsReturn] (which TERMINATES — see below), and a
    [GsBlankAssign] whose RHS is in a STRUCTURALLY effect-free subset (see below) — by
    BRIDGING the existing [cmd.v] semantics: a supported-subset statement list is mapped
    to a [cmd.Cmd unit], and its observable behaviour is read through builtins' [run_io] /
    [w_output].  It DEFINES NO new IO / output / outcome model (charter: do NOT fork a
    second semantics — [cmd.Cmd] / [denote] / [run_io] / [World] are reused verbatim).
    [cmd.denote] DROPS [CDfr] (defers), but the supported subset has NO defers, so the
    bridge is exact / fuel-free here.

    LAYERING (charter spine).  Core GoSem sits BELOW GoSafe / GoEmit, so this file imports
    ONLY [GoAst] (the syntax + [classify]) and the semantic substrate it bridges ([cmd] /
    [builtins]) — NOT GoPrint / GoSafe / GoEmit.  The behavioral theorem about the certified
    [GoEmit.demo_prog] lives in the DOWNSTREAM [GoSemDemo.v] (which imports GoSem + GoEmit),
    so the dependency points the right way (GoSem does not reach up into the emission layers).

    It is NOT (yet), and must not be described as:
      • the full authoritative GoSem — only [println]/[print]/[panic] statements, a
        TERMINATING [return], and an effect-free-RHS [_ = e] are denoted; everything else
        is rejected ([None]);
      • a complete expression evaluator — [eval] covers a SMALL CORE (integer constants
        under +/-/*, the default-[int] and [int64] scalar conversions, and string
        literals), FAR less than GoSafe.ptype's supported subset.  Any other form (free
        identifiers, other conversions, slices/maps, [len]/[cap], booleans, floats, …)
        is [None] = "outside THIS slice's denotational scope", which is explicitly NOT a
        claim about Go's behaviour;
      • accompanied by an eval-vs-ptype SOUNDNESS theorem (that [eval] agrees with the
        GoSafe type/category analysis) — there is NONE; future work;
      • [BehaviorSafe] (the GoSafe behavioral gate) — also future work; the emitter's
        certificate stays [SupportedProgram], NOT a behavioral one.

    So do NOT call this "the semantics" or imply completeness.  It is one small, faithful,
    zero-axiom behavioral slice that BRIDGES cmd.v.

    DESIGN — partiality (the None handling).  [denote_stmt]/[denote_body] are PARTIAL
    ([option]-valued): a statement whose argument is outside [eval]'s core yields [None],
    propagated to [None] for the whole body, surfaced as [gosem_run = None] = "this
    program is outside the current denotational scope".  This is the honest choice: it
    NEVER fabricates output, NEVER drops an output/panic event, and NEVER invents a Go
    panic for an un-modelled form.

    DESIGN — [return] TERMINATES (it does NOT fall through).  Go's [return] STOPS the
    function: statements AFTER it do not run.  Because [denote_body] is a RIGHT-fold
    ([denote_stmt s (denote_body rest)]), [denote_stmt GsReturn] IGNORES its continuation
    and yields [CRet tt] — which DISCARDS [rest], short-circuiting exactly as Go does (so
    e.g. `func main(){ return; println(1) }`, a supported body, runs to a NORMAL outcome
    with NO output — pinned by [gosem_return_short_circuits]).

    DESIGN — [_ = e] is restricted to a STRUCTURALLY effect-free RHS.  Go EVALUATES the RHS
    of [_ = e]; the discard does NOT erase the expression unseen.  This slice does not (yet)
    give a full evaluate-with-effects semantics, so it ADMITS [_ = e] ONLY when [e] is in a
    STRUCTURALLY effect-free, total subset ([rhs_effect_free]) — expression forms that can
    produce NO observable output and CANNOT panic — and otherwise REJECTS it ([None] = out of
    this slice).  For an admitted RHS the value is total + silent BY STRUCTURE, so discarding
    it and continuing as [k] is faithful.  This is explicitly a STRUCTURAL effect-free
    RESTRICTION, NOT a full eval-with-panic semantics: a panicking/effectful RHS (a call to
    [println]/[print]/[panic] or any other function, [BDiv]/[BRem] with a zero divisor, or an
    [EIndex]/[ESlice]/[ESel]/[EAssert] that can panic) is OUT of scope, never silently erased.
    ============================================================================ *)
From Fido Require Import builtins cmd GoAst.
From Stdlib Require Import String List Bool ZArith.
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

(** ---- [rhs_effect_free e] : is [e] in the STRUCTURALLY effect-free / total RHS subset
    admitted as a [_ = e] discard? ----  This is a CONSERVATIVE structural predicate: it
    is [true] ONLY for expression forms that can produce NO observable output and CANNOT
    panic — i.e. total, silent values whose evaluation is invisible, so discarding the
    value and continuing is faithful.  It is NOT a soundness/completeness theorem against
    Go (no such proof here); it is the explicit STRUCTURAL restriction the [GsBlankAssign]
    denotation relies on (see the header DESIGN note).
    ADMITS:  [EInt] / [EStr] literals; the predeclared [nil] ([EId "nil"]); the NON-PARTIAL
      arithmetic/comparison binops ([BAdd]/[BSub]/[BMul]/[BAnd]/[BOr]/[BXor]/[BAndNot]/
      [BShl]/[BShr]/[BEq]/[BNe]/[BLt]/[BLe]/[BGt]/[BGe]) over effect-free operands; the
      unary [UNeg]/[UXor]/[UNot] over an effect-free operand; a SCALAR conversion
      [t(a)] = [ECall (EId t) [a]] with [t] a scalar type keyword ([classify t <> None])
      and [a] effect-free (a numeric/bool/string conversion cannot panic); a slice/chan/map
      type-form conversion [EConv] over an effect-free operand; and [ESliceLit]/[EMapLit]
      whose children are ALL effect-free.
    REJECTS ([false]): [BDiv]/[BRem] (a zero divisor PANICS); [BLAnd]/[BLOr] (out of this
      tiny set — conservative, not needed); [UDeref]/[UAddr]; [EIndex]/[ESlice]/[ESel]/
      [EAssert] (index / slice / deref / assert can PANIC); a free identifier other than
      [nil]; and ANY non-conversion call — [ECall (EId "println"|"print"|"panic") …] OR any
      other function call ([classify] of its name is [None]) — since a call may OUTPUT or
      PANIC. *)
Fixpoint rhs_effect_free (e : GExpr) : bool :=
  match e with
  | EInt _  => true
  | EStr _  => true
  | EId i   => String.eqb (proj1_sig i) "nil"   (* only the predeclared [nil]; every other ident is out of scope *)
  | EUn o e0 =>
      match o with
      | UNeg | UXor | UNot => rhs_effect_free e0
      | UDeref | UAddr     => false             (* deref can panic; address-of is not a value here *)
      end
  | EBn o l r =>
      match o with
      | BAdd | BSub | BMul | BAnd | BOr | BXor | BAndNot | BShl | BShr
      | BEq | BNe | BLt | BLe | BGt | BGe => rhs_effect_free l && rhs_effect_free r
      | BDiv | BRem | BLAnd | BLOr        => false   (* div/rem can panic on a zero divisor; &&/|| out of this set *)
      end
  | ECall (EId f) (a :: nil) =>
      (* a SCALAR conversion [t(a)] (cannot panic) is effect-free iff its operand is; any other
         single-arg call ([println]/[print]/[panic]/[len]/[cap]/user func) may output/panic *)
      match classify (proj1_sig f) with Some _ => rhs_effect_free a | None => false end
  | ECall _ _ => false                          (* multi-arg / non-identifier callee: a call may output/panic *)
  | EConv _ e0 => rhs_effect_free e0            (* slice/chan/map conversion: total + silent over an effect-free operand *)
  | ESliceLit _ es =>
      (fix all_ef (l : list GExpr) : bool :=
         match l with nil => true | x :: r => rhs_effect_free x && all_ef r end) es
  | EMapLit _ _ kvs =>
      (fix all_ef_kv (l : list (GExpr * GExpr)) : bool :=
         match l with
         | nil => true
         | p :: r => rhs_effect_free (fst p) && rhs_effect_free (snd p) && all_ef_kv r
         end) kvs
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => false   (* selector/index/slice/assert can panic *)
  end.

(** ---- [denote_stmt s k] : denote one supported statement, given continuation [k] ----
    [println(args)] -> [COut true (eval args) k]; [print(args)] -> [COut false … k];
    [panic(a)] -> [CPan (eval a)] (DROPS [k] — a panic short-circuits, as Go); a bare
    [GsReturn] -> [CRet tt], IGNORING [k] (Go's [return] TERMINATES — see the header DESIGN
    note: in the right-fold this discards the later statements [rest]); [GsBlankAssign e] ->
    [k] WHEN [e] is [rhs_effect_free] (its total/silent value is discarded, no event), else
    [None] (an effectful/partial RHS is out of this slice — NEVER silently erased).  PARTIAL:
    [None] if a denoted argument is outside [eval]'s core, or for any statement shape outside
    this subset ([GsReturnVal], a non-call / non-whitelisted expression statement). *)
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
  | GsReturn        => Some (CRet tt)   (* [return] TERMINATES: ignore [k]; in the right-fold this drops [rest] *)
  | GsReturnVal _   => None
  | GsBlankAssign e => if rhs_effect_free e then Some k else None   (* discard a total/silent value; reject an effectful RHS *)
  end.

(** ---- [denote_body b] : a supported statement list -> a [cmd.Cmd unit] ----
    right-fold with base [CRet tt] (normal termination); PARTIAL ([None] if any statement
    is out of scope).  Because it folds RIGHT, [denote_stmt GsReturn] returning [CRet tt]
    (ignoring its continuation) discards everything after the [return] — the short-circuit. *)
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

(** ---- REGRESSION: [return] SHORT-CIRCUITS (FIX, Codex stop-review 2026-06-29) ----
    A body `{ return; println(1) }` runs to a NORMAL outcome ([ORet tt]) with the
    UNCHANGED initial world — i.e. EMPTY [w_output] ([w_output w_init = []]): the
    [println(1)] AFTER the [return] does NOT run.  Were [return] to fall through (the bug),
    the [println] would execute and the world would be [w_log true [...] w_init <> w_init],
    so this [reflexivity] would not close.  This pins the terminating semantics of FIX 1. *)
Theorem gosem_return_short_circuits :
  gosem_run [GsReturn;
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EInt 1])]
    = Some (ORet tt w_init).
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION: the demo's blank-assign RHSs are [rhs_effect_free] ----
    [GoEmit.demo_prog]'s two [_ = e] statements ([_ = []int(nil)], [_ = []int{1}]) have
    EFFECT-FREE RHSs, so [denote_stmt (GsBlankAssign _)] admits them ([Some k], discarding
    the value).  (Reconstructed here so the property is locked in the core file, with NO
    dependency on the upper emission layers; the end-to-end demo output is in GoSemDemo.v.) *)
Example demo_blank_rhs_effect_free :
  rhs_effect_free (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl))) = true
  /\ rhs_effect_free (ESliceLit GTInt [EInt 1]) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** GATE — GoSem is a (proof-only) behavioral slice; keep it axiom-free.  These [Print
    Assumptions] surface the trust base of the deliverables in the build log; the Docker
    prover-stage axiom-manifest gate (and [make gosem-verify]) FAIL the build on ANY axiom,
    so "Closed under the global context" here is enforced, not decorative. *)
Print Assumptions gosem_return_short_circuits.
Print Assumptions demo_blank_rhs_effect_free.
