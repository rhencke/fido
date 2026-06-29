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

    DESIGN — partiality (the None handling).  [classify_stmt]/[denote_body] are PARTIAL
    ([option]-valued): a statement whose argument is outside [eval]'s core, or whose shape is
    outside this subset, classifies as [SDUnsupported], yielding [None] for the whole body,
    surfaced as [gosem_run = None] = out of the current denotational scope.  This is the honest
    choice: it NEVER fabricates output, NEVER drops an output/panic event, and NEVER invents a
    Go panic for an un-modelled form.

    DESIGN — TERMINAL statements ([return]/[panic]) short-circuit UNCONDITIONALLY.  Go's
    [return] STOPS the function and a [panic] aborts it: statements AFTER either do not run.
    [classify_stmt] tags each statement [SDTerminal]/[SDSeq]/[SDUnsupported], and [denote_body]
    folds LEFT-to-right: on an [SDTerminal] (a bare [return], or a [panic(a)]) it returns that
    [Cmd] IMMEDIATELY, WITHOUT forcing [denote_body rest] — so the suffix is discarded
    UNCONDITIONALLY, even when [rest] is itself un-denotable (e.g. [return; println(len(s))],
    where [len] is outside [eval]: the body still runs to a NORMAL outcome, the [len] suffix
    never consulted — pinned by [gosem_return_discards_undenotable_suffix]).  An [SDSeq]
    statement (an output, or an admitted blank-assign) DOES force [rest] — sequential
    statements continue — and an [SDUnsupported] statement yields [None], so an unsupported
    statement BEFORE a terminal still rejects ([gosem_unsupported_before_terminal_rejects]).

    DESIGN — [_ = e] is restricted to a STRUCTURALLY effect-free RHS.  Go EVALUATES the RHS
    of [_ = e]; the discard does NOT erase the expression unseen.  This slice does not (yet)
    give a full evaluate-with-effects semantics, so it ADMITS [_ = e] ONLY when [e] passes the
    CONSERVATIVE structural predicate [rhs_effect_free] — expression forms that produce NO
    observable output and CANNOT panic — and otherwise REJECTS it ([None] = out of this slice).
    For an admitted RHS the value is silent and non-panicking BY STRUCTURE, so discarding it and
    continuing is faithful.  This is explicitly a CONSERVATIVE STRUCTURAL effect-free check, NOT
    a full eval-with-panic semantics: it intentionally rejects a bare identifier (incl. [nil]),
    a SHIFT ([BShl]/[BShr], which can panic on a negative / oversized count), [BDiv]/[BRem]
    (a zero divisor panics), index/slice/deref/assert, and any non-conversion call — none of
    which is unconditionally silent+total, all OUT of scope, never silently erased.
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

(** ---- [rhs_effect_free e] : GoSem's STRUCTURAL effect-free + total predicate ----  the
    CONSERVATIVE behavioral check the [_ = e] discard relies on: [true] ONLY for expression
    forms that produce NO observable output AND CANNOT panic (no partial op), so the value is
    silent + non-panicking BY STRUCTURE and discarding it is faithful.  It is NOT a typing
    duplicate of GoSafe and NOT a soundness/completeness theorem against Go — it is a
    behavioral, conservative over-approximation of effect-free-and-non-panicking.  It
    INTENTIONALLY rejects bare nil, shifts, division, index/deref/assert, and arbitrary calls.
    ADMITS:  [EInt] / [EStr] literals; the unconditionally total+silent arithmetic binops
      ([BAdd]/[BSub]/[BMul]/[BAnd]/[BOr]/[BXor]/[BAndNot]) and the comparisons
      ([BEq]/[BNe]/[BLt]/[BLe]/[BGt]/[BGe]) over effect-free operands; the unary
      [UNeg]/[UXor]/[UNot] over an effect-free operand; a SCALAR conversion
      [t(a)] = [ECall (EId t) [a]] with [t] a scalar type keyword ([classify t <> None]) and
      [a] effect-free (a numeric/bool/string conversion cannot panic); a slice/chan/map
      type-form conversion [EConv] over the predeclared [nil] operand OR an effect-free operand;
      and [ESliceLit]/[EMapLit] whose children are ALL effect-free.
    REJECTS ([false]): a BARE identifier, INCLUDING [nil] ([_ = nil] is invalid Go — use of
      untyped nil); the SHIFTS [BShl]/[BShr] (a negative / oversized count panics, and the shift
      is not unconditionally total); [BDiv]/[BRem] (a zero divisor PANICS); [BLAnd]/[BLOr] (out
      of this set — conservative); [UDeref]/[UAddr]; [EIndex]/[ESlice]/[ESel]/[EAssert] (index /
      slice / deref / assert can PANIC); and ANY non-conversion call ([println]/[print]/[panic]/
      [len]/[cap]/user func — [classify] of its name is [None]), since a call may OUTPUT/PANIC. *)
Fixpoint rhs_effect_free (e : GExpr) : bool :=
  match e with
  | EInt _  => true
  | EStr _  => true
  | EId _   => false                            (* NEVER a bare identifier (incl. nil): [_ = nil] is invalid Go *)
  | EUn o e0 =>
      match o with
      | UNeg | UXor | UNot => rhs_effect_free e0
      | UDeref | UAddr     => false             (* deref can panic; address-of is not a value here *)
      end
  | EBn o l r =>
      match o with
      | BAdd | BSub | BMul | BAnd | BOr | BXor | BAndNot
      | BEq | BNe | BLt | BLe | BGt | BGe => rhs_effect_free l && rhs_effect_free r
      | BShl | BShr | BDiv | BRem | BLAnd | BLOr => false
          (* shift can panic on a neg/oversized count; div/rem on a zero divisor; &&/|| out of this set *)
      end
  | ECall (EId f) (a :: nil) =>
      (* a SCALAR conversion [t(a)] (cannot panic) is effect-free iff its operand is; any other
         single-arg call ([println]/[print]/[panic]/[len]/[cap]/user func) may output/panic *)
      match classify (proj1_sig f) with Some _ => rhs_effect_free a | None => false end
  | ECall _ _ => false                          (* multi-arg / non-identifier callee: a call may output/panic *)
  | EConv _ e0 =>
      (* slice/chan/map conversion: admit the predeclared nil operand, or an effect-free operand *)
      (match e0 with EId i => String.eqb (proj1_sig i) "nil" | _ => false end) || rhs_effect_free e0
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

(** ---- [StmtDen] : the 3-way statement classification (the FIX-2 spine) ----  every supported
    statement is one of: [SDTerminal c] — a TERMINATING statement ([return] / [panic]), whose
    meaning is the [Cmd] [c] and whose SUFFIX is discarded UNCONDITIONALLY (it does NOT depend
    on [rest]); [SDSeq f] — a SEQUENTIAL statement (an output, or an admitted blank-assign),
    a continuation TRANSFORMER applied to the denotation of [rest] (so [rest] still runs); or
    [SDUnsupported] — outside this slice, forcing [None].  This separation is what lets a
    terminal short-circuit even an un-denotable suffix (see [denote_body]). *)
Inductive StmtDen : Type :=
  | SDTerminal    : Cmd unit -> StmtDen
  | SDSeq         : (Cmd unit -> Cmd unit) -> StmtDen
  | SDUnsupported : StmtDen.

(** ---- [classify_stmt s] : classify ONE supported statement ----  [println(args)] /
    [print(args)] -> [SDSeq (COut true|false xs)] when every arg evaluates (else
    [SDUnsupported]); [panic(a)] -> [SDTerminal (CPan v)] when [a] evaluates (panic TERMINATES);
    a bare [GsReturn] -> [SDTerminal (CRet tt)] (return TERMINATES); [GsBlankAssign e] ->
    [SDSeq (fun k => k)] when [e] is [rhs_effect_free] (its silent value is discarded, no event),
    else [SDUnsupported]; every other shape ([GsReturnVal], a non-call / non-whitelisted
    expression statement) -> [SDUnsupported].  Note this NEVER consults [rest] — terminality is
    intrinsic to the statement, so [denote_body] can short-circuit without denoting the suffix. *)
Definition classify_stmt (s : GoStmt) : StmtDen :=
  match s with
  | GsExprStmt (ECall (EId f) args) =>
      let fn := proj1_sig f in
      if String.eqb fn "println" then
        match eval_args args with Some xs => SDSeq (COut true xs) | None => SDUnsupported end
      else if String.eqb fn "print" then
        match eval_args args with Some xs => SDSeq (COut false xs) | None => SDUnsupported end
      else if String.eqb fn "panic" then
        match args with
        | a :: nil => match eval a with Some v => SDTerminal (CPan v) | None => SDUnsupported end
        | _ => SDUnsupported
        end
      else SDUnsupported
  | GsExprStmt _    => SDUnsupported
  | GsReturn        => SDTerminal (CRet tt)   (* [return] TERMINATES — its [Cmd] does not depend on [rest] *)
  | GsReturnVal _   => SDUnsupported
  | GsBlankAssign e => if rhs_effect_free e then SDSeq (fun k => k) else SDUnsupported
  end.

(** ---- [denote_body b] : a supported statement list -> a [cmd.Cmd unit] ----  a LEFT-to-right
    fold via [classify_stmt]: an [SDTerminal c] returns [Some c] IMMEDIATELY — WITHOUT forcing
    [denote_body rest] — so a [return]/[panic] discards the suffix UNCONDITIONALLY (even an
    un-denotable one); an [SDSeq f] still forces [rest] ([Some (f k)] when [rest] denotes, else
    [None]); an [SDUnsupported] is [None] (so an unsupported statement BEFORE a terminal still
    rejects).  Base [CRet tt] (normal termination). *)
Fixpoint denote_body (b : list GoStmt) : option (Cmd unit) :=
  match b with
  | nil => Some (CRet tt)
  | s :: rest =>
      match classify_stmt s with
      | SDTerminal c  => Some c
      | SDSeq f       => match denote_body rest with Some k => Some (f k) | None => None end
      | SDUnsupported => None
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

(** ---- REGRESSION: [return] SHORT-CIRCUITS over a DENOTABLE suffix ----
    A body `{ return; println(1) }` runs to a NORMAL outcome ([ORet tt]) with the
    UNCHANGED initial world — i.e. EMPTY [w_output] ([w_output w_init = []]): the
    [println(1)] AFTER the [return] does NOT run.  Were [return] to fall through (the bug),
    the [println] would execute and the world would be [w_log true [...] w_init <> w_init],
    so this [reflexivity] would not close.  (The stronger [gosem_return_discards_undenotable_suffix]
    below shows the suffix is discarded even when it is itself UN-denotable.) *)
Theorem gosem_return_short_circuits :
  gosem_run [GsReturn;
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EInt 1])]
    = Some (ORet tt w_init).
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 1): a BARE identifier RHS is REJECTED ----  [_ = nil] is invalid Go
    (use of untyped nil); [rhs_effect_free (EId _) = false], so the blank-assign is out of
    scope and [gosem_run] is [None].  (nil is admitted ONLY as a conversion operand — see the
    demo's [[]int(nil)] in [demo_blank_rhs_effect_free].) *)
Theorem gosem_rejects_bare_nil :
  gosem_run [GsBlankAssign (EId (mkIdent "nil" eq_refl))] = None.
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 1): a SHIFT RHS is REJECTED ----  a shift can panic on a negative /
    oversized count (and [1 << -1] is a compile error), so it is NOT unconditionally total;
    [rhs_effect_free (EBn BShl ..) = false] and [gosem_run] is [None]. *)
Theorem gosem_rejects_shift :
  gosem_run [GsBlankAssign (EBn BShl (EInt 1) (EInt (-1)))] = None.
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 2): [return] DISCARDS an UN-denotable suffix ----  classified
    [SDTerminal], [denote_body] returns [CRet tt] IMMEDIATELY, WITHOUT forcing [denote_body
    rest] — so a suffix outside [eval]'s core (here [println(len([]int{1}))], with [len]
    outside [eval]) does NOT block the program: it runs to a NORMAL [ORet tt] with EMPTY output.
    Under the OLD right-fold this body was wrongly [None] (the unreachable [rest] failed to
    denote, dragging the whole body to [None]). *)
Theorem gosem_return_discards_undenotable_suffix :
  gosem_run [GsReturn;
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "len" eq_refl))
                                      [ESliceLit GTInt [EInt 1]]])]
    = Some (ORet tt w_init).
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 2): [panic] short-circuits and STAYS a panic ----  classified
    [SDTerminal (CPan ..)], so the un-denotable [println(len(..))] suffix is discarded and the
    outcome is the panic [OPanic <int 1>], NOT [None]. *)
Theorem gosem_panic_short_circuits :
  gosem_run [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EInt 1]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "len" eq_refl))
                                      [ESliceLit GTInt [EInt 1]]])]
    = Some (OPanic (anyt TInt64 (intwrap 1)) w_init).
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 2): an UNSUPPORTED statement BEFORE a terminal still REJECTS ----  the
    head is classified FIRST; [GsReturnVal] is [SDUnsupported] -> [None] for the whole body, even
    though a [GsReturn] follows.  Classification is per-statement and order-respecting: a
    terminal does NOT retroactively rescue an unsupported predecessor. *)
Theorem gosem_unsupported_before_terminal_rejects :
  gosem_run [GsReturnVal (EInt 1); GsReturn] = None.
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION: the demo's blank-assign RHSs are [rhs_effect_free] ----
    [GoEmit.demo_prog]'s two [_ = e] statements ([_ = []int(nil)], [_ = []int{1}]) have
    EFFECT-FREE RHSs, so [classify_stmt (GsBlankAssign _) = SDSeq (fun k => k)] admits them,
    discarding the value.  (Reconstructed here so the property is locked in the core file, with
    NO dependency on the upper emission layers; the end-to-end demo output is in GoSemDemo.v.) *)
Example demo_blank_rhs_effect_free :
  rhs_effect_free (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl))) = true
  /\ rhs_effect_free (ESliceLit GTInt [EInt 1]) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** GATE — GoSem is a (proof-only) behavioral slice; keep it axiom-free.  These [Print
    Assumptions] surface the trust base of the deliverables in the build log; the Docker
    prover-stage axiom-manifest gate (and [make gosem-verify]) FAIL the build on ANY axiom,
    so "Closed under the global context" here is enforced, not decorative. *)
Print Assumptions gosem_return_short_circuits.
Print Assumptions gosem_rejects_bare_nil.
Print Assumptions gosem_rejects_shift.
Print Assumptions gosem_return_discards_undenotable_suffix.
Print Assumptions gosem_panic_short_circuits.
Print Assumptions gosem_unsupported_before_terminal_rejects.
Print Assumptions demo_blank_rhs_effect_free.
