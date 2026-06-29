(** ============================================================================
    GoSem.v — the FIRST behavioral-semantics slice (Phase 5 "GoSem"; ARCHITECTURE.md
    spine GoAst -> GoPrint -> GoSem -> GoSafe -> GoEmit).

    ⚠️ HONEST SCOPE — read this before citing the file.

    This is the FIRST behavioral slice of GoSem.  It denotes ONLY the OUTPUT / panic
    behavior of the SUPPORTED statement subset — [GsExprStmt] calls to
    [println]/[print]/[panic], a [GsReturn] (which TERMINATES — see below), and a
    [GsBlankAssign] whose RHS is a valid VALUE by the SHARED [GoTypes.svalue] (see below) — by
    BRIDGING the existing [cmd.v] semantics: a supported-subset statement list is mapped
    to a [cmd.Cmd unit], and its observable behaviour is read through builtins' [run_io] /
    [w_output].  It DEFINES NO new IO / output / outcome model (charter: do NOT fork a
    second semantics — [cmd.Cmd] / [denote] / [run_io] / [World] are reused verbatim).
    [cmd.denote] DROPS [CDfr] (defers), but the supported subset has NO defers, so the
    bridge is exact / fuel-free here.

    LAYERING (charter spine).  Core GoSem sits BELOW GoSafe / GoEmit, so this file imports
    ONLY [GoAst] (the syntax + [classify]), the LOWER shared type-category module [GoTypes]
    (which itself imports only [GoAst] — it provides [ptype]/[svalue], the SAME blank-assign
    authority GoSafe uses), and the semantic substrate it bridges ([cmd] / [builtins]) — NOT
    GoPrint / GoSafe / GoEmit (the UPPER emission layers).  The behavioral theorem about the certified
    [GoEmit.demo_prog] lives in the DOWNSTREAM [GoSemDemo.v] (which imports GoSem + GoEmit),
    so the dependency points the right way (GoSem does not reach up into the emission layers).

    It is NOT (yet), and must not be described as:
      • the full authoritative GoSem — only [println]/[print]/[panic] statements, a
        TERMINATING [return], and a [GoTypes.svalue]-valid-RHS [_ = e] are denoted; everything else
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

    DESIGN — [_ = e] is gated by the SHARED type-category authority [GoTypes.svalue] (single source of truth).
    Go EVALUATES the RHS of [_ = e]; the discard does NOT erase the expression unseen.  This slice does not
    (yet) give a full evaluate-with-effects semantics, so it ADMITS [_ = e] ONLY when [e] is a VALID VALUE
    expression by [GoTypes.svalue] — the EXACT predicate GoSafe's [stmt_ok] uses for a blank-assign RHS —
    and otherwise REJECTS it ([None] = out of this slice).  [GoTypes.svalue] is a thin wrapper over the
    constant-aware type-category checker [GoTypes.ptype] (FACTORED into the lower shared module GoTypes so
    GoSafe and GoSem agree by CONSTRUCTION — there is no SECOND, type-blind GoSem predicate).  This closes the
    earlier type-blindness: a CLOSED-but-INVALID RHS is now REJECTED because [ptype] rejects it — not only the
    validity cases (an aggregate-to-aggregate conversion, a map literal/conversion, a slice literal with a
    bad element) but the TYPE/CONSTANT errors a structural effect-check missed ([bool(1)], [[]uint8{300}],
    [int("hi")], [!1], the bool-ordering [(1==1) < (2==2)] — each now [None], pinned below).  WHY an
    [svalue]-admitted RHS is faithfully denoted as a SILENT discard: in the no-declaration Program model a
    FREE identifier is UNDEFINED, so [ptype] REJECTS it; thus every [svalue]-valid expression is CLOSED, and
    [ptype]'s constant analysis already rejects the only closed forms that could panic (a constant-zero
    divisor, a negative/oversized constant shift count) and every partial op (index/slice/deref/assert —
    [ptype] [None]).  So an admitted RHS is valid + silent + TOTAL by structure, and discarding it and
    continuing is faithful.  Still rejected (now via [ptype], not an ad-hoc list): a bare identifier
    INCLUDING [nil] ([_ = nil] is "use of untyped nil", invalid — [svalue (EId "nil") = false] because
    [ptype] gives [PtNil] and [svalue] rejects it); a runtime/const-illegal shift or division; index / slice /
    deref / assert; and any non-conversion call ([println]/[panic]/[len]/… as a bare value), all OUT of scope.
    ============================================================================ *)
From Fido Require Import builtins cmd GoAst GoTypes.
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

(** ---- BLANK-ASSIGN VALIDITY is the SHARED [GoTypes.svalue] (no local predicate) ----  the [_ = e] discard
    is gated by [GoTypes.svalue] — the SAME value-position authority GoSafe's [stmt_ok] uses — so GoSem and
    GoSafe agree by CONSTRUCTION (one [ptype]-based source of truth, not a second type-blind GoSem check).
    The earlier hand-rolled structural predicate ([rhs_effect_free]) was DELETED: it was effect-aware but
    TYPE-BLIND, so it denoted CLOSED-INVALID Go ([_ = bool(1)], [_ = []uint8{300}], [_ = int("hi")], [_ = !1],
    [_ = (1==1) < (2==2)]) as a silent normal return.  [svalue] (= [ptype]-valid, with [PtNil] / the
    default-[int]-overflow boundary rejected) rejects all of those, AND — because a free identifier is
    [ptype]-rejected in the no-declaration model — every [svalue]-admitted RHS is CLOSED, so [ptype]'s
    constant analysis (no const-zero divisor, no negative/oversized shift count) plus its rejection of every
    partial op (index/slice/deref/assert) makes the admitted value valid + silent + TOTAL by structure;
    discarding it and continuing is faithful.  See [classify_stmt]'s blank arm below. *)

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
    [SDSeq (fun k => k)] when [e] is [GoTypes.svalue] (the SHARED value-position authority — its silent value
    is discarded, no event), else [SDUnsupported]; every other shape ([GsReturnVal], a non-call / non-whitelisted
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
  | GsBlankAssign e => if svalue e then SDSeq (fun k => k) else SDUnsupported   (* SHARED GoTypes.svalue (= ptype-valid) *)
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
    (use of untyped nil); [svalue (EId "nil") = false] ([ptype] gives [PtNil], which [svalue] rejects),
    so the blank-assign is out of scope and [gosem_run] is [None].  ★This is exactly why GoSem's gate is the
    value-position [svalue], NOT a bare [ptype e <> None]: [ptype (EId "nil") = Some PtNil], so [ptype <> None]
    would WRONGLY admit [_ = nil].  (nil is admitted ONLY as a conversion operand — see the demo's [[]int(nil)]
    in [demo_blank_svalue].) *)
Theorem gosem_rejects_bare_nil :
  gosem_run [GsBlankAssign (EId (mkIdent "nil" eq_refl))] = None.
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 1): a SHIFT RHS with a NEGATIVE constant count is REJECTED ----  [1 << -1] is a Go
    compile error (negative shift count), so [ptype] rejects it and [svalue (EBn BShl ..) = false] and
    [gosem_run] is [None].  (A VALID constant shift like [_ = 1 << 4] is now ADMITTED — [ptype] folds it, and
    in the no-declaration model there is no runtime shift count to panic at; the prior [rhs_effect_free]
    blanket-rejected ALL shifts, this is the more precise [ptype] rule.) *)
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

(** ---- REGRESSION: the demo's blank-assign RHSs are [svalue]-VALID (ptype-valid) ----
    [GoEmit.demo_prog]'s two [_ = e] statements ([_ = []int(nil)], [_ = []int{1}]) are valid VALUES by the
    shared [GoTypes.svalue] ([ptype] gives each [Some PtAgg]), so [classify_stmt (GsBlankAssign _) = SDSeq
    (fun k => k)] admits them, discarding the value.  (Reconstructed here so the property is locked in the
    core file, with NO dependency on the upper emission layers; the end-to-end demo output is in GoSemDemo.v.) *)
Example demo_blank_svalue :
  svalue (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl))) = true
  /\ svalue (ESliceLit GTInt [EInt 1]) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** ---- REGRESSION (FIX 1): an INVALID slice conversion RHS is REJECTED ----  [_ = []int([]string{})]
    is CLOSED-but-INVALID Go (a [[]string] is not convertible to [[]int]).  GoSem sits below GoSafe and
    has no convertibility evidence of its own, but it now reuses the shared [ptype], which admits a slice/chan
    conversion ONLY for the predeclared [nil] operand; a NON-nil operand (here a [[]string{}] aggregate) is
    [ptype]-REJECTED — [svalue] is [false] and [gosem_run] is [None].  GoSem must NOT denote this as a silent
    normal blank assign. *)
Theorem gosem_rejects_invalid_slice_conv :
  gosem_run [GsBlankAssign (EConv (CTSlice GTInt) (ESliceLit GTString []))] = None.
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 1): a chan conversion of a NON-nil operand is REJECTED ----  [_ = chan int([]int{1})]
    is invalid (a slice is not convertible to a channel).  Again [ptype] admits only [chan T(nil)], so the
    [[]int{1}] operand makes [svalue] [false] and [gosem_run] [None]. *)
Theorem gosem_rejects_chan_conv_of_slice :
  gosem_run [GsBlankAssign (EConv (CTChan GTInt) (ESliceLit GTInt [EInt 1]))] = None.
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 1): a map composite literal RHS is REJECTED ----  the shared [ptype] QUARANTINES map
    literals (comparable-key + value-assignability are not structurally evident), so [ptype (EMapLit ..) = None]
    and [svalue (EMapLit ..) = false] unconditionally.  Witness: a NON-comparable-key map literal
    [map[[]int]int{[]int{1}: 2}] (a slice key type is not comparable) — [gosem_run] is [None], never a
    silent normal blank assign. *)
Theorem gosem_rejects_map_literal :
  gosem_run [GsBlankAssign (EMapLit (GTSlice GTInt) GTInt
                                    [(ESliceLit GTInt [EInt 1], EInt 2)])] = None.
Proof. vm_compute. reflexivity. Qed.

(** ---- REGRESSION (FIX 1): the demo's two blank-assign RHSs are still ADMITTED end-to-end ----  the
    nil slice conversion [_ = []int(nil)] and the all-scalar slice literal [_ = []int{1}] each classify
    [SDSeq (fun k => k)] (silent discard), so a body [{ _ = e; return }] runs to a NORMAL [ORet tt] with
    the unchanged initial world.  This locks that the FIX-1 tightening did NOT regress the demo. *)
Theorem gosem_admits_demo_blank_rhs :
  gosem_run [GsBlankAssign (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl))); GsReturn]
    = Some (ORet tt w_init)
  /\ gosem_run [GsBlankAssign (ESliceLit GTInt [EInt 1]); GsReturn]
    = Some (ORet tt w_init).
Proof. split; vm_compute; reflexivity. Qed.

(** ============================================================================================
    REGRESSIONS (Codex stop-review, 2026-06-29) — TYPE-BLINDNESS CLOSED.  The deleted [rhs_effect_free] was
    effect-aware but TYPE-BLIND, so it denoted these CLOSED-but-INVALID Go forms as a SILENT normal return.
    The shared [GoTypes.svalue] (= [ptype]-valid) rejects every one — each [gosem_run] is now [None], never a
    fabricated [ORet].  (These mirror GoSafe's [bad_println_bool1] / [bad_uint8_slicelit] / [bad_println_not1]
    / [bad_bool_ord] regressions — the SAME [ptype] authority deciding both layers.)
    ============================================================================================ *)
(** [bool(1)] — an int is not convertible to bool ([conv_to_scalar (PtIntConst 1) GTBool = None]). *)
Theorem gosem_rejects_bool_conv :
  gosem_run [GsBlankAssign (ECall (EId (mkIdent "bool" eq_refl)) [EInt 1])] = None.
Proof. vm_compute. reflexivity. Qed.
(** [[]uint8{300}] — the element 300 is out of [uint8] range ([assignable_to_ty (PtIntConst 300) GTU8 = false]). *)
Theorem gosem_rejects_u8_slicelit_overflow :
  gosem_run [GsBlankAssign (ESliceLit GTU8 [EInt 300])] = None.
Proof. vm_compute. reflexivity. Qed.
(** [int("hi")] — a string is not convertible to int ([conv_to_scalar PtStr GTInt = None]). *)
Theorem gosem_rejects_int_of_string :
  gosem_run [GsBlankAssign (ECall (EId (mkIdent "int" eq_refl)) [EStr "hi"])] = None.
Proof. vm_compute. reflexivity. Qed.
(** [!1] — logical NOT needs a bool operand ([ptype]'s [UNot] arm rejects a non-bool). *)
Theorem gosem_rejects_not_of_int :
  gosem_run [GsBlankAssign (EUn UNot (EInt 1))] = None.
Proof. vm_compute. reflexivity. Qed.
(** [(1==1) < (2==2)] — ordering ([<]) needs ORDERED operands; bool is not ordered ([ord_comparable PtBool PtBool = false]). *)
Theorem gosem_rejects_bool_ordering :
  gosem_run [GsBlankAssign (EBn BLt (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)))] = None.
Proof. vm_compute. reflexivity. Qed.

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
Print Assumptions demo_blank_svalue.
Print Assumptions gosem_rejects_invalid_slice_conv.
Print Assumptions gosem_rejects_chan_conv_of_slice.
Print Assumptions gosem_rejects_map_literal.
Print Assumptions gosem_admits_demo_blank_rhs.
Print Assumptions gosem_rejects_bool_conv.
Print Assumptions gosem_rejects_u8_slicelit_overflow.
Print Assumptions gosem_rejects_int_of_string.
Print Assumptions gosem_rejects_not_of_int.
Print Assumptions gosem_rejects_bool_ordering.
