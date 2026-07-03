(** ============================================================================
    GoSafe.v — supportedness now, behavioral safety later (AST-first spine; see ARCHITECTURE.md §2/§2a).
    [SupportedProgram] is a PHASE-1 SYNTACTIC gate — a supported-subset check — NOT behavioral safety, and it
    is NAMED so deliberately (naming is a correctness claim: never call a syntactic gate "Safe").  The
    semantic [BehaviorSafe] (no nil-deref / OOB / send-on-closed / illegal-close / data-race / …, defined over
    GoSem) lands once GoSem is COMPLETE — GoSem SLICE 1 (the [cmd.v] bridge [denote_program] + [gosem_sound]:
    denotation ⊆ SupportedProgram) now EXISTS, but does not yet denote enough behavior to define BehaviorSafe
    against; [unified.v] is an existing PROOF-ONLY operational semantics, NOT the certified path's, which GoSem
    must still bridge or retire) — at which point the blessed path becomes emit_safe over a [SafeProgram]
    (= EmittableProgram + BehaviorSafe).  Until then GoEmit emits only the SUPPORTED subset via emit_supported,
    and must NOT be described as behaviorally safe.
    ============================================================================ *)
From Fido Require Import GoAst.   (* GoAst supplies the syntax AND [classify] (the keyword -> GoTy map for scalar
                                     conversions).  DELIBERATELY NOT GoPrint — the SAFETY layer must NOT depend on
                                     the printer (ARCHITECTURE.md §2: GoAst -> GoPrint and GoAst -> GoSafe are
                                     SIBLINGS off GoAst, not a chain through the printer). *)
From Fido Require Import GoTypes. (* the SHARED constant-aware type-category checker — [ptype] / [svalue] +
                                     all numeric/conversion helpers — factored into the LOWER module GoTypes
                                     (imports only GoAst) so GoSafe AND GoSem (slice 1 consults [svalue] /
                                     [expr_stmt_ok] via importing GoSafe) consult the SAME authority (single
                                     source of truth, no duplicate predicate).  GoSafe reuses [ptype]/[svalue]. *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
Open Scope string_scope.

(** ===================================================================================================
    ===== STRUCTURAL: statement-shape / supported-syntax (the [stmt_ok] / [supported_program] gate) =====
    =================================================================================================== *)

(** Is a builtin [f] valid as a standalone EXPRESSION-STATEMENT call, by NAME and ARITY only?  [println]/
    [print] are variadic in arg COUNT; [panic] takes exactly one.  This checks only name+arity — argument
    TYPES are checked SEPARATELY and per-builtin in [expr_stmt_ok] ([printable_arg_ok] for [print]/[println]
    — NOT "any type": only the guaranteed-printable SCALAR subset — and [svalue] for [panic], which takes an
    [interface{}]).  Deliberately EXACT for the current AST (no user funcs / imports yet).  Excluded on
    purpose: CONVERSIONS ([int(x)] is not a call) and VALUE-returning builtins ([len(x)]/… — "evaluated but
    not used" as a statement).  ([close]/[delete] add a channel/map arg-type constraint — deferred to GoSem.)
    Widens with user funcs / a symbol table. *)
Definition stmt_call_ok (f : string) (args : list GExpr) : bool :=
  if String.eqb f "println" then true                                  (* variadic in arg COUNT *)
  else if String.eqb f "print" then true                               (* variadic in arg COUNT *)
  else if String.eqb f "panic" then (match args with _ :: nil => true | _ => false end)  (* exactly 1 *)
  else false.

(** A [print]/[println] argument GUARANTEED-printable by the Go spec.  ★Go-spec NOTE (Bootstrapping): [print]/
    [println] are bootstrapping builtins whose implementations need NOT accept arbitrary argument types — only
    BOOLEAN, NUMERIC, and STRING are always supported.  So a printable arg is one [ptype] gives a SCALAR
    category (a numeric — [PtIntConst]/[PtTIntConst]/[PtFloatConst]/[PtRunInt]/[PtRunFloat] — or [PtBool]/
    [PtStr]).  This reuses the structural type-checker, so it INHERITS its rejection of closed type-errors —
    e.g. [len(1)] (an int is not len-able), [bool(1)], [1 && 2], [!1], [int([]int{1})], [float64(1) %
    float64(2)], [uint8(300)], [uint8(int(300))], [1/int(0)] — and of EVERY non-scalar category ([PtAgg]
    slice/chan literals and conversions AND [PtMap] map literals — both rejected by this scalar-only whitelist),
    of [nil] ([PtNil]), and of FREE identifiers (a bare [x] is undefined -> [ptype] [None]):
    emit a scalar value instead.  ([println(int64(3))] / [println(len([]int{1}))] stay admitted: a conversion of
    a constant / a [len] of an aggregate has a KNOWN scalar category.)  ★The default-[int] boundary applies: a
    bare UNTYPED int constant arg gets default type [int], so it must FIT in (conservative 32-bit) [int] —
    [println(1)] ✓, [println(<huge>)] REJECT (a TYPED constant was already range-checked at its conversion). *)
Definition printable_arg_ok (e : GExpr) : bool :=
  match ptype e with
  | Some (PtIntConst z) => int_const_repr z GTInt   (* default-[int] boundary: a bare untyped const must fit int *)
  | Some (PtTIntConst _ _) | Some (PtFloatConst _ _)
  | Some (PtRunInt _) | Some (PtRunFloat _) | Some PtBool | Some PtStr => true
  | _ => false
  end.

(** A [GExpr] legal as an EXPRESSION STATEMENT in Go.  Per the Go spec a bare expression statement must be a
    CALL (a plain value [1] / [a + b] is "evaluated but not used"), AND — crucially — a genuine function call,
    NOT a CONVERSION ([int(x)] is a conversion, also invalid as a statement).  Since no user functions exist
    yet, the statement-valid callees are EXACTLY the whitelisted builtins at their correct arity
    ([stmt_call_ok]).  ARGUMENTS are checked PER BUILTIN: [print]/[println] admit only the guaranteed-printable
    SCALAR subset ([printable_arg_ok] — NOT arbitrary [svalue], so [println(<slice/map>)] / aggregate printing
    is excluded as implementation-defined); [panic] admits any [svalue] (it takes an [interface{}]).  So
    [int64(3)] / [Foo(x)] / [1()] / [len([]int{1})] / [panic()] / [println([]int{1})] / [panic(x)] (free [x]) as
    statements are all rejected; [println(int64(3))] / [println(1 + 2)] / [panic(1)] are accepted. *)
Definition expr_stmt_ok (e : GExpr) : bool :=
  match e with
  | ECall (EId f) args =>
      let fn := proj1_sig f in
      stmt_call_ok fn args &&
      (if String.eqb fn "panic" then forallb svalue args else forallb printable_arg_ok args)
  | _                  => false
  end.

(** A statement in the SUPPORTED subset: an expression statement must be [expr_stmt_ok]; a bare [return] is
    always fine (a valid tail of a void func like [main]); a blank assign [_ = e] needs [svalue e]; a deferred
    call [defer <e>] ([GsDefer]) reuses [expr_stmt_ok] (Go requires the deferred expr be a CALL — so
    [defer 1] / [defer len(..)] / [defer panic()] / [defer println(<slice>)] are rejected exactly as the
    matching expr statements, pinned in [bad_programs]); a VALUE return [return e] ([GsReturnVal]) is REJECTED —
    the only function we emit is [main], which is VOID, so `return <value>` is invalid Go ("too many return
    values").  (It becomes supported, conditional on the enclosing function's result type, once NON-void
    functions enter the AST — a clean demonstration that GoAst represents more than the gate admits.) *)
Definition stmt_ok (s : GoStmt) : bool :=
  match s with
  | GsExprStmt e    => expr_stmt_ok e
  | GsReturn        => true
  | GsReturnVal _   => false   (* value return is invalid in the void [main] — the only function emitted today *)
  | GsBlankAssign e => svalue e  (* [_ = e] is valid iff [e] PRODUCES a value — so [_ = println(1)] (void) is rejected *)
  | GsDefer e       => expr_stmt_ok e  (* [defer <call>]: Go requires the deferred expr be a function CALL — same gate as an expr statement *)
  | GsShortDecl _ _ => false  (* [x := e] — locals rung 1: REPRESENTATION before admission; the scope-threaded gate admits it at rung 4 (plans/gosem-locals.md) *)
  end.

(** PHASE-1 supportedness — DECIDABLE (bool-reflected): the program is a runnable `package main` whose body is
    entirely in the printer/emitter's STRUCTURALLY-supported statement subset (each statement is a [return], a
    structurally-well-formed call expression statement, a blank assign of a value, or a [defer] of such a call).
    It rejects the structural absurdities Go's grammar/
    statement rules forbid: a bare-value statement `func main(){ 1 }` ("evaluated but not used") and a call of a
    non-callable `func main(){ 1() }` are both [false], so no certificate exists and [emit_supported] can never
    print them.  SCOPE OF THE CLAIM (kept honest): this is CONSERVATIVE STRUCTURAL scope + type-category
    supportedness — it REJECTS a free (undefined) identifier (the current Program has NO declarations, so a free
    [x] could never compile) and a structurally-evident type/constant error, but it is NOT full Go type-checking
    or behavioral safety (the [BehaviorSafe]/GoSem layer, later).  So it is SUPPORTEDNESS, not "guaranteed-
    compiling" and not behavioral safety.  (The package-name-ONLY check was too weak — it certified invalid Go
    — now fixed.) *)
Definition supported_program (p : Program) : bool :=
  String.eqb (proj1_sig (prog_pkg p)) "main" && forallb stmt_ok (prog_body p).
Definition SupportedProgram (p : Program) : Prop := supported_program p = true.

(** ============================================================================================
    REGRESSIONS — grouped boolean fixtures.  INVARIANT: [ptype]/[svalue] is a CONSERVATIVE supported-subset
    CLASSIFIER, not Go's typechecker; add NO new rule unless it rejects a real accepted-bad program or admits a
    needed demo.  Coverage is pinned by [forallb] over THREE ledgers with DISTINCT contracts — [bad_programs]
    (INVALID Go; each [supported_program] is [false] — the SOUNDNESS obligation), [valid_unsupported_programs]
    (VALID Go the gate STILL rejects; each [false] — bounded fail-loud INCOMPLETENESS), and [good_programs]
    (each [true]) — plus a small set of [Fail … := eq_refl] forge-attempts proving the CERTIFICATE itself cannot
    be inhabited for a rejected program.  The helpers below build the fixtures.
    ============================================================================================ *)

(** Program / expression builders shared by the lists (KEEP — they make the fixtures readable).  [pl_arg a] is
    `func main(){ println(<a>) }` (a value in a print arg); [gs_blank a] is `func main(){ _ = <a> }` (a value
    via a blank assign); the [gs_*] wrap a scalar conversion. *)
Definition pl_arg (a : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [a])].
Definition gs_blank (a : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign a].
Definition gs_defer (a : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsDefer a; GsReturn].
Definition gs_f64 (a : GExpr) : GExpr := ECall (EId (mkIdent "float64" eq_refl)) [a].
Definition gs_i64 (a : GExpr) : GExpr := ECall (EId (mkIdent "int64" eq_refl)) [a].
Definition gs_i32 (a : GExpr) : GExpr := ECall (EId (mkIdent "int32" eq_refl)) [a].
Definition gs_str (a : GExpr) : GExpr := ECall (EId (mkIdent "string" eq_refl)) [a].
Definition gs_int (a : GExpr) : GExpr := ECall (EId (mkIdent "int" eq_refl)) [a].
Definition gs_u8  (a : GExpr) : GExpr := ECall (EId (mkIdent "uint8" eq_refl)) [a].
Definition gs_i8  (a : GExpr) : GExpr := ECall (EId (mkIdent "int8" eq_refl)) [a].

(** The bare-value statement `func main(){ 1 }` — NAMED because GoEmit's certificate-forge test references it
    ([Fail Definition … := mkEmittable unsupported_value_stmt eq_refl], proving no [EmittableProgram] exists
    for an unsupported program).  It is also the first [bad_programs] / [forge_value_stmt] fixture below. *)
Definition unsupported_value_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EInt 1)].

(** REJECTED — every entry is INVALID Go the gate must refuse ([supported_program = false]): statement-shape
    errors (bare value / call-of-non-callable / assertion- or conversion- or aggregate-as-statement / value
    return in void [main] / [len] in statement context / [panic] arity), value-position errors (void call,
    conversion arity), the [ptype] CLOSED type-errors ([len]/[bool]/[&&]/[!]/int-of-slice; the FINDING 1-4
    numeric category / overflow / zero-divisor / shift / comparison / [cap]-of-string / aggregate-conversion
    cases; the transitive NUMERIC typed-constant rules — INCL. the [int8(len(<non-literal string const>)+200)] overflow
    companions that LOCK the [valid_unsupported_programs] [len] witnesses' soundness boundary; float-rounding +
    platform-[uint] complement), the INVALID [EMapLit]/[CTMap] instances (slice key / an invalid NESTED map-key type, even in an
    EMPTY literal ([goty_supported]) / key-or-value not
    representable in the element type / DUPLICATE constant keys / [cap] of a map / map as a [println] arg /
    free-ident map conversion — these LOCK the now-supported map literal's boundary), and FREE-identifier use
    (no declarations in the model).  ⚠ This
    list is the SOUNDNESS obligation — invalid Go that MUST be refused — NOT the incompleteness ledger.  A
    program Go's typechecker ACCEPTS but [ptype] still rejects (a bounded, fail-loud conservatism) belongs in
    [valid_unsupported_programs] below, NEVER here. *)
Definition bad_programs : list Program :=
  [ (* statement shape *)
    unsupported_value_stmt                                               (* bare value statement *)
  ; mkProgram (mkIdent "lib" eq_refl) [GsReturn]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EInt 1) nil)]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EAssert (EId (mkIdent "x" eq_refl)) GTInt) nil)]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "int" eq_refl)) [EId (mkIdent "x" eq_refl)])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ESliceLit GTInt [EInt 1])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EMapLit GTInt GTInt [(EInt 1, EInt 2)])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) nil)]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EInt 1; EInt 2])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EId (mkIdent "x" eq_refl)])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EStr "x")]
  ; mkProgram (mkIdent "main" eq_refl) [GsReturnVal (EInt 1)]
  ; mkProgram (mkIdent "main" eq_refl) [GsShortDecl (mkIdent "x" eq_refl) (EInt 1)]  (* [x := 1] alone — INVALID Go (declared and not used) AND locals rung 1 rejects ALL short decls (representation before admission; non-denotation is ENTAILED via [gosem_sound]'s contrapositive) *)
    (* [defer <call>] reuses [expr_stmt_ok], so it rejects the SAME non-call / value-builtin / arity / arg shapes *)
  ; gs_defer (EInt 1)                                                    (* defer of a NON-call value *)
  ; gs_defer (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])  (* defer of [len] — a value builtin, not a statement call *)
  ; gs_defer (ECall (EId (mkIdent "panic" eq_refl)) nil)                 (* defer panic() — bad arity *)
  ; gs_defer (ECall (EId (mkIdent "println" eq_refl)) [ESliceLit GTInt [EInt 1]])  (* defer println(<slice>) — non-printable arg *)
    (* value position / arg errors *)
  ; pl_arg (ECall (EId (mkIdent "println" eq_refl)) [EInt 1])            (* void call used as value *)
  ; pl_arg (ECall (EId (mkIdent "int" eq_refl)) [EInt 1; EInt 2])        (* conversion arity *)
  ; pl_arg (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))         (* println of an aggregate *)
  ; pl_arg (ESliceLit GTInt [EInt 1])                                    (* println of a slice literal *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]; ESliceLit GTInt [EInt 1]])  (* len arity *)
  ; gs_blank (ECall (EId (mkIdent "println" eq_refl)) [EInt 1])          (* _ = void call *)
    (* ptype closed type-errors *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EInt 1])
  ; pl_arg (ECall (EId (mkIdent "bool" eq_refl)) [EInt 1])
  ; pl_arg (EBn BLAnd (EInt 1) (EInt 2))
  ; pl_arg (EUn UNot (EInt 1))
  ; pl_arg (gs_int (ESliceLit GTInt [EInt 1]))
    (* FINDING 1 — numeric category / overflow / zero-divisor / shift *)
  ; pl_arg (EBn BRem (gs_f64 (EInt 1)) (gs_f64 (EInt 2)))
  ; pl_arg (EBn BShl (gs_f64 (EInt 1)) (EInt 2))
  ; pl_arg (EBn BAnd (gs_f64 (EInt 1)) (gs_f64 (EInt 2)))
  ; pl_arg (EUn UXor (gs_f64 (EInt 1)))
  ; pl_arg (gs_u8 (EInt 300))
  ; pl_arg (gs_i8 (EInt 128))
  ; gs_blank (ESliceLit GTU8 [EInt 300])
  ; pl_arg (EBn BAdd (gs_i64 (EInt 3)) (gs_i32 (EInt 2)))
  ; gs_blank (ESliceLit GTInt [gs_i64 (EInt 1)])
  ; pl_arg (EBn BDiv (EInt 1) (EInt 0))
  ; pl_arg (EBn BDiv (EInt 1) (EBn BSub (EInt 1) (EInt 1)))
  ; pl_arg (EBn BRem (EInt 1) (EInt 0))
  ; pl_arg (EBn BShl (EInt 1) (EInt (-1)))
    (* FINDING 2 — comparison split (== needs comparable, < needs ordered) *)
  ; pl_arg (EBn BEq (ESliceLit GTInt [EInt 1]) (ESliceLit GTInt [EInt 1]))
  ; pl_arg (EBn BLt (ESliceLit GTInt [EInt 1]) (ESliceLit GTInt [EInt 1]))
  ; pl_arg (EBn BLt (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)))
  ; pl_arg (EBn BEq (EInt 1) (EBn BEq (EInt 2) (EInt 2)))
    (* FINDING 3 — cap of a string *)
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [gs_str (EInt 65)])
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EStr "hi"])
    (* FINDING 4 — aggregate conversion soundness *)
  ; gs_blank (EConv (CTChan GTInt) (ESliceLit GTInt [EInt 1]))
  ; gs_blank (EConv (CTSlice GTInt) (ESliceLit GTString []))
    (* transitive NUMERIC typed-constant rules (a numeric const's value survives conversions/binops) *)
  ; pl_arg (EBn BDiv (EInt 1) (gs_int (EInt 0)))
  ; pl_arg (EBn BRem (EInt 1) (gs_int (EInt 0)))
  ; pl_arg (EBn BShl (EInt 1) (gs_int (EInt (-1))))
  ; pl_arg (gs_u8 (gs_int (EInt 300)))
  ; pl_arg (gs_u8 (gs_f64 (EInt 300)))
  ; pl_arg (EBn BAdd (gs_i8 (EInt 100)) (gs_i8 (EInt 100)))
  ; pl_arg (gs_u8 (gs_int (gs_int (EInt 300))))
  ; pl_arg (EBn BDiv (EInt 1) (EBn BSub (gs_int (EInt 1)) (gs_int (EInt 1))))
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [EStr "hi"]) (EInt 200)))  (* int8(len("hi")+200): [len] of a string LITERAL folds to 2, 2+200=202 overflows int8 -> REJECTED.  Locks the len-string-LITERAL soundness fix (a runtime-int model would WRONGLY admit this) *)
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [gs_str (EInt 65)]) (EInt 200)))  (* int8(len(string(65))+200): the NON-LITERAL companion to the [valid_unsupported_programs] witness `len(string(65))`.  string(65)="A", len folds to 1 EXACTLY, 1+200=201 overflows int8 — INVALID Go, REJECTED.  EXACT byte-length folding (the legitimate way to admit the witness) keeps THIS rejected; a sloppy [PtStr -> PtRunInt] runtime-int shortcut would make int8(runtime+200) SUPPORTED and FLIP [bad_programs_rejected] *)
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")]) (EInt 200)))  (* int8(len("a"+"b")+200): the companion to the other witness `len("a"+"b")`.  "a"+"b"="ab", len folds to 2 EXACTLY, 2+200=202 overflows int8 — same soundness lock on the concat witness *)
  ; pl_arg (EBn BAdd (EStr "a") (EInt 1))                                (* "a" + 1: string + number is INVALID Go — REJECTED ([num_binop] gives None on the non-numeric [PtStr] operand) *)
  ; pl_arg (EInt 1099511627776)                                          (* 2^40 default-int overflow *)
  ; gs_blank (EInt 1099511627776)
  ; gs_blank (ESliceLit GTU8 [gs_int (EInt 300)])
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EStr "x"))      (* []int{10,20}["x"]: a STRING index is INVALID Go — a slice index must be an integer; [ptype idx] = [PtStr] so [is_int_cat] fails -> UNSUPPORTED *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EUn UNeg (EInt 1)))  (* []int{10,20}[-1]: a NEGATIVE constant index is INVALID Go (verified gc: "index -1 must not be negative") — REJECTED by the [0 <=? k] guard.  (An OOB *positive* constant is NOT here — it is valid Go, in good_programs.) *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 9223372036854775808))  (* []int{10,20}[2^63]: 2^63 overflows int on ANY platform — INVALID Go (verified gc: "overflows int"), REJECTED by the [int_const_repr k GTInt] guard (pins the overflow arm, distinct from the negative one).  NB: that guard is CONSERVATIVE 32-bit, so it also over-rejects some indices a 64-bit gc accepts — this fixture is only the genuinely-invalid end *)
    (* float-constant rounding + platform-uint complement (the rep must not lie) *)
  ; pl_arg (gs_i64 (gs_f64 (EInt 9223372036854775807)))                  (* int64(float64(maxint64)) rounds up *)
  ; pl_arg (gs_i32 (ECall (EId (mkIdent "float32" eq_refl)) [EInt 2147483647]))
  ; gs_blank (EBn BDiv (EId (mkIdent "x" eq_refl)) (gs_f64 (EInt 0)))     (* x / float64(0) — const-zero divisor (ALSO a free-ident rejection; the CLOSED witnesses below isolate the zero-divisor rule itself) *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (gs_f64 (EInt 0)))                (* float64(1)/float64(0): CLOSED const-zero float divisor — Go compile error; FLIPS if [is_zero_const] stops seeing [PtFloatConst] *)
  ; gs_blank (EBn BDiv (ECall (EId (mkIdent "float32" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "float32" eq_refl)) [EInt 0]))  (* float32(1)/float32(0): the float32 width of the same rule *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (EBn BSub (gs_f64 (EInt 1)) (gs_f64 (EInt 1))))  (* float64(1)/(float64(1)-float64(1)): the divisor's ZERO arises by FOLDING — locks that the zero test runs on the folded dyadic *)
  ; pl_arg (ECall (EId (mkIdent "uint32" eq_refl)) [EUn UXor (ECall (EId (mkIdent "uint" eq_refl)) [EInt 0])])
    (* INVALID [EMapLit]/[CTMap] instances — now rejected by the STRUCTURAL [EMapLit] check (was a blanket
       quarantine; the supported witness `_ = map[int]int{1:2}` GRADUATED to [good_programs]).  Each LOCKS the
       supported map literal's boundary — a checker that skipped one of comparability / representability /
       distinctness / map-is-not-cap-able would wrongly admit it and FLIP [bad_programs_rejected]: a
       non-comparable slice KEY (caught by the integer-key restriction); a non-representable VALUE then KEY (300
       in [uint8] — caught by [assignable_to_ty]); DUPLICATE constant keys (caught by [nodup_z] — Go forbids
       them); an INVALID NESTED map-key type hidden in a VALUE/element/conversion type (caught by [goty_supported]
       — even an EMPTY literal, where no entry check could see it); [cap] of a map (Go forbids it — caught by
       [PtMap]≠[PtAgg], so the [cap] arm gives [None]); a map as
       a [println] arg (a map is not a printable arg); and a map CONVERSION of a FREE IDENT (an
       invalid-operand rejection — the map-conversion QUARANTINE itself is pinned on a VALID nil operand in
       [valid_unsupported_programs]) *)
  ; gs_blank (EMapLit (GTSlice GTInt) GTInt [(ESliceLit GTInt [EInt 1], EInt 2)])  (* map[[]int]int{..}: slice key not comparable *)
  ; gs_blank (EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) [])              (* map[int]map[[]int]int{}: a non-comparable slice KEY hidden in the VALUE type — invalid Go even EMPTY ([goty_supported]) *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []])  (* println(len(map[int]map[[]int]int{})): the len of an invalid-typed literal is rejected at the ROOT *)
  ; gs_blank (EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []]))  (* 1/len(map[int]map[[]int]int{}): no divide-by-zero behavior for invalid source *)
  ; gs_blank (ESliceLit (GTMap (GTSlice GTInt) GTInt) [])                  (* []map[[]int]int{}: the same invalid nested key type through a SLICE literal *)
  ; gs_blank (EConv (CTSlice (GTMap (GTSlice GTInt) GTInt)) (EId (mkIdent "nil" eq_refl)))  (* []map[[]int]int(nil): ... and through the aggregate-conversion arm *)
  ; gs_blank (EMapLit GTInt GTU8 [(EInt 1, EInt 300)])                    (* map[int]uint8{1:300}: value 300 overflows uint8 *)
  ; gs_blank (EMapLit GTU8 GTInt [(EInt 300, EInt 1)])                    (* map[uint8]int{300:1}: key 300 overflows uint8 *)
  ; gs_blank (EMapLit GTInt GTInt [(EInt 1, EInt 2); (EInt 1, EInt 3)])   (* map[int]int{1:2, 1:3}: DUPLICATE constant key 1 — a Go compile error *)
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]])  (* cap(map[int]int{1:2}): [cap] of a MAP is invalid Go — REJECTED ([PtMap] is not [cap]-able, unlike a slice) *)
  ; gs_blank (EConv (CTMap GTInt GTInt) (EId (mkIdent "x" eq_refl)))      (* map[int]int(x): a FREE-IDENT operand — undefined; the CTMap quarantine's valid-operand witness lives in [valid_unsupported_programs] *)
  ; gs_blank (EConv (CTMap (GTSlice GTInt) GTInt) (EId (mkIdent "nil" eq_refl)))  (* _ = map[[]int]int(nil): a NON-COMPARABLE key in the conversion TARGET type — INVALID Go; this pin FLIPS if CTMap is ever admitted without a target key-comparability check *)
  ; gs_blank (EConv (CTMap GTInt (GTMap (GTSlice GTInt) GTInt)) (EId (mkIdent "nil" eq_refl)))  (* _ = map[int]map[[]int]int(nil): the invalid key hidden in the target's NESTED value type — an outer-key-only CTMap admission would wrongly accept this *)
  ; gs_blank (EConv (CTMap GTInt (GTSlice (GTMap (GTSlice GTInt) GTInt))) (EId (mkIdent "nil" eq_refl)))  (* _ = map[int][]map[[]int]int(nil): the invalid key under a SLICE wrapper inside the target — a direct-map-value-only check would wrongly accept this.  These rows are WITNESSES; the CLASS gate is the ∀-theorem [ctmap_conv_unsupported_target_rejected] below *)
  ; pl_arg (EMapLit GTInt GTInt [(EInt 1, EInt 2)])                       (* println(map[int]int{1:2}): a supported map VALUE, but not a printable [println] arg *)
    (* free-identifier use — undefined in the no-declaration model *)
  ; gs_blank (EId (mkIdent "x" eq_refl))
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EId (mkIdent "x" eq_refl)])
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EId (mkIdent "x" eq_refl)])
  ; gs_blank (EConv (CTSlice GTInt) (EId (mkIdent "x" eq_refl)))
  ; pl_arg (gs_int (EId (mkIdent "x" eq_refl)))
  ].
Example bad_programs_rejected :
  forallb (fun p => negb (supported_program p)) bad_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** REJECTED-BUT-VALID — a SEPARATE contract from [bad_programs].  Go's typechecker ACCEPTS every program here,
    yet [ptype] still rejects it ([supported_program = false]): each falls outside the SOUND supported subset,
    so the gate refuses it rather than risk a plausible-but-wrong emission (rule 2 — fail loud, never
    plausible-but-wrong).  This is BOUNDED, principled INCOMPLETENESS, not a soundness obligation.  ⚠ Admitting
    a member is legitimate growth ONLY via an EXACT, soundly-STRUCTURAL rule that STILL rejects its INVALID
    companion in [bad_programs] — NEVER a sloppy widening.  ★WORKED EXAMPLE (done): the map literal
    `map[int]int{1:2}` GRADUATED from here to [good_programs] once [ptype] gained a structural
    integer-key/representability/distinctness check — and its companions `map[int]uint8{1:300}` /
    `map[uint8]int{300:1}` / `map[int]int{1:2,1:3}` STAYED in [bad_programs], exactly as this contract demands.
    Each current class's own FUTURE path (per the contract above, each names the companion that must stay
    rejected): the len-string members graduate by folding [len] of a NON-LITERAL string const to its exact
    byte length (keeping `int8(len(string(65))+200)` / `int8(len("a"+"b")+200)` rejected — a
    [PtStr -> PtRunInt] runtime-int shortcut would reopen those); the [map[int]int(nil)] CONVERSION
    graduates only when the CTMap arm consults the FULL recursive target-type gate — enforced by the GATED
    ∀-theorem [ctmap_conv_unsupported_target_rejected] below (every [goty_supported]-rejected target stays
    unsupported), which a graduating arm must RE-ESTABLISH; the [bad_programs] CTMap rows (root / nested /
    slice-wrapped) are its witnesses; the ptr/chan-key block graduates when
    [goty_key_supported] grows past scalars on a modelled ptr/chan key-equality semantics (keeping the
    slice/map-key members of [bad_programs] rejected); the float ROUNDING members ([float64(1)/float64(3)],
    the cross-width [float32(<inexact-at-32>)]) graduate only with a correctly-ROUNDING const model — the
    exact-or-reject dyadic fold refuses them today (keeping the const-ZERO-divisor [bad_programs] member
    rejected).  The two contracts must not be confused — a
    [bad_programs] regression means an UNSOUND
    emission reopened; admitting one of THESE (with its companion preserved) is the subset legitimately GROWING.
    Current members: [len] of a non-literal string CONST (byte length not folded); the valid
    [map[int]int(nil)] CONVERSION (the blanket CTMap quarantine, pinned on a VALID operand); the float
    ROUNDING cases ([float64(1)/float64(3)] and the cross-width [float32] conversion of an inexact-at-32
    const — the dyadic fold is EXACT-or-reject); and the
    CARTESIAN ptr/chan map-key block [ptrchan_key_quarantine] — each out-of-core key type × each rejecting
    surface ([goty_supported]/[is_int_goty] admit only integer keys in core; string/bool root keys are the
    same conservative int-only restriction — Go also allows string/bool/ptr/chan/comparable-struct/interface
    keys). *)
(** The valid-but-out-of-core ptr/chan MAP-KEY class, pinned STRUCTURALLY: generated as the full CARTESIAN
    product (out-of-core key type × rejecting surface), so a new key type or surface added here extends
    every pin at once — "quarantined" stays an executable per-surface claim, never a hand-picked sample.
    Surfaces: root literal (the int-only key restriction), nested map VALUE type, slice ELEMENT type
    ([goty_supported]), and the three nil-conversion arms (CTSlice / CTChan / the blanket CTMap
    quarantine).  Every generated program is VALID Go — [nil] converts to any slice/chan/map type
    (https://go.dev/ref/spec#Conversions). *)
Definition oo_core_key_tys : list GoTy := [GTPtr GTInt; GTChan GTInt].
Definition ptrchan_key_quarantine : list Program :=
  flat_map (fun k =>
    [ gs_blank (EMapLit k GTInt [])                                              (* _ = map[K]int{} — root literal *)
    ; gs_blank (EMapLit GTInt (GTMap k GTInt) [])                                (* _ = map[int]map[K]int{} — nested value type *)
    ; gs_blank (ESliceLit (GTMap k GTInt) [])                                    (* _ = []map[K]int{} — slice element type *)
    ; gs_blank (EConv (CTSlice (GTMap k GTInt)) (EId (mkIdent "nil" eq_refl)))   (* _ = []map[K]int(nil) *)
    ; gs_blank (EConv (CTChan  (GTMap k GTInt)) (EId (mkIdent "nil" eq_refl)))   (* _ = (chan map[K]int)(nil) *)
    ; gs_blank (EConv (CTMap k GTInt) (EId (mkIdent "nil" eq_refl)))             (* _ = map[K]int(nil) — the CTMap arm *)
    ]) oo_core_key_tys.
Definition valid_unsupported_programs : list Program :=
  [ pl_arg (ECall (EId (mkIdent "len" eq_refl)) [gs_str (EInt 65)])       (* println(len(string(65))): string(65)="A" (a rune-const conversion — compiles; go vet warns), len folds to 1.  A NON-LITERAL [PtStr] (not [EStr]), so [len] hits the [_, _ => None] fallback — REJECTED (fail-loud).  Pinned just below: [string_rune_const_is_supported_PtStr] + [len_of_nonliteral_PtStr_rejected] *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")])  (* println(len("a"+"b")): "a"+"b"="ab", len folds to 2.  The concat is a NON-literal [PtStr], so [len] hits the same non-literal fallback — REJECTED *)
  ; gs_blank (EConv (CTMap GTInt GTInt) (EId (mkIdent "nil" eq_refl)))    (* _ = map[int]int(nil): VALID Go (nil converts to a map type) — the blanket CTMap quarantine pinned on a VALID operand (the [bad_programs] free-ident row is an invalid-operand rejection, NOT this witness) *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (gs_f64 (EInt 3)))               (* _ = float64(1)/float64(3): VALID Go (rounds to ~0.333); the exact-or-reject dyadic fold REFUSES a non-representable quotient ([dy_div] inexact) — quarantined, never a rounded lie *)
  ; pl_arg (ECall (EId (mkIdent "float32" eq_refl)) [gs_f64 (EInt 16777217)])  (* println(float32(float64(16777217))): VALID Go (rounds to 16777216 — 2^24+1 is inexact at binary32); the cross-width const conversion is EXACT-only ([float_dyadic_repr]) — quarantined *)
  ; mkProgram (mkIdent "main" eq_refl)
      [GsShortDecl (mkIdent "x" eq_refl) (EInt 1);
       GsBlankAssign (EId (mkIdent "x" eq_refl)); GsReturn]  (* x := 1; _ = x; return — VALID Go (declared AND used); locals rung 1 keeps ALL short decls out of core (the constructor pins below isolate the rejection; the [bad_programs] `x := 1` row is the INVALID unused twin, a different contract) *)
  ] ++ ptrchan_key_quarantine.
Example valid_unsupported_rejected :
  forallb (fun p => negb (supported_program p)) valid_unsupported_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** The [GsShortDecl] rejection pinned at the CONSTRUCTOR, for EVERY ident/expression (not a sample
    row): the rung-1 arm is the constant [false], so the valid-unsupported witness above rejects for
    exactly this reason regardless of its other statements.  (The denotation-side absence pin,
    [denote_stmt (GsShortDecl _ _) = None], lives with [denote_stmt] in GoSemDenote.v.) *)
Example shortdecl_stmt_ok_false : forall x e, stmt_ok (GsShortDecl x e) = false.
Proof. reflexivity. Qed.

(** ★ THE CTMAP TARGET CLASS GATE — universal, NOT sample rows: for EVERY target type [map[k]v] the
    supported-type authority rejects ([goty_supported (GTMap k v) = false]), the nil map CONVERSION to it
    is NOT a supported program.  Today this holds because the CTMap arm fail-closes outright; if CTMap ever
    GRADUATES, re-establishing THIS gated theorem forces the new arm to consult the same recursive target
    authority — no outer-key-only or direct-map-value-only shortcut can satisfy it.  The [bad_programs]
    CTMap rows are concrete witnesses of this class, not the gate. *)
Theorem ctmap_conv_unsupported_target_rejected : forall k v,
  goty_supported (GTMap k v) = false ->
  supported_program (gs_blank (EConv (CTMap k v) (EId (mkIdent "nil" eq_refl)))) = false.
Proof. intros k v _. reflexivity. Qed.

(** The [len(string(65))] entry above ([valid_unsupported_programs]) rejects via the NON-LITERAL-[PtStr] [len]
    fallback SPECIFICALLY, not via an unsupported argument — pinned by the pair below: [string(65)] IS a
    SUPPORTED [PtStr] (a rune-const conversion), yet [len] of it is [None].  Since the arg type-checks
    ([Some PtStr]), the [len] [None] can only be the [_, _ => None] fallback — [PtStr] is neither a string
    LITERAL ([EStr], which folds) nor an aggregate ([PtAgg]/[PtMap], the other [len]-accepted cases).  This is
    what makes the [valid_unsupported_programs] entry a genuine lock on that fallback (a regression that restored
    [PtStr -> PtRunInt] would flip [len_of_nonliteral_PtStr_rejected] to [Some _]). *)
Example string_rune_const_is_supported_PtStr :
  ptype (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) = Some PtStr.
Proof. reflexivity. Qed.
Example len_of_nonliteral_PtStr_rejected :
  ptype (ECall (EId (mkIdent "len" eq_refl)) [ECall (EId (mkIdent "string" eq_refl)) [EInt 65]]) = None.
Proof. reflexivity. Qed.

(** ACCEPTED — the smaller-but-SOUND subset the gate still admits ([supported_program = true]): a conversion of
    a constant in value position, value-position aggregates (slice/chan [PtAgg] AND map [PtMap], all valid
    values) with [len] on ANY of them but [cap] on slice/chan [PtAgg] ONLY (a map is len-able, not cap-able),
    in-range / folded constants and same-width typed arithmetic, [panic]/bare-return/blank-assign/string
    literals, the EXACT float→int constant tracking ([uint8(float64(255))] is in range) + fixed-width complement,
    and an INTEGER-key map LITERAL whose value TYPE is [goty_supported], constant keys distinct + assignable
    to the key type, values assignable to the value type ([map[int]int{1:2}]). *)
Definition good_programs : list Program :=
  [ pl_arg (gs_i64 (EInt 3))                                             (* println(int64(3)) *)
  ; gs_blank (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))       (* _ = []int(nil) *)
  ; gs_blank (ESliceLit GTInt [EInt 1])                                  (* _ = []int{1} *)
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EInt 1])]
  ; mkProgram (mkIdent "main" eq_refl) [GsReturn]
  ; gs_blank (EInt 1)                                                    (* _ = 1 *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [ESliceLit GTInt [EInt 1]])
  ; pl_arg (EStr "hi")                                                   (* println("hi") *)
  ; gs_blank (EStr "x")                                                  (* _ = "x" *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EStr "hi"])             (* len of a string LITERAL folds to a CONST (2) — printable *)
  ; pl_arg (EBn BAdd (EStr "a") (EStr "b"))                             (* "a" + "b" string CONCATENATION -> a string *)
  ; pl_arg (gs_i8 (EInt 127))                                            (* int8(127) in range *)
  ; pl_arg (EBn BRem (EInt 5) (EInt 2))
  ; pl_arg (EBn BShl (EInt 1) (EInt 4))
  ; gs_blank (ESliceLit GTFloat64 [EInt 1])                             (* untyped const into a float element *)
  ; pl_arg (EBn BAdd (gs_i64 (EInt 3)) (gs_i64 (EInt 2)))               (* same-width add *)
  ; pl_arg (gs_u8 (gs_f64 (EInt 255)))                                  (* uint8(float64(255)) — exact, in range *)
  ; pl_arg (EBn BAdd (gs_i8 (EInt 100)) (gs_i8 (EInt 20)))              (* folded typed-const, in range *)
  ; pl_arg (EInt 2147483647)                                            (* 32-bit default-int boundary *)
  ; pl_arg (gs_u8 (EUn UXor (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 0])))  (* uint8(^uint8(0)) fixed width *)
  ; gs_blank (EMapLit GTInt GTInt [(EInt 1, EInt 2)])                   (* _ = map[int]int{1: 2} — integer-key map literal, const key distinct + assignable *)
  ; gs_blank (EMapLit GTInt GTInt [(EInt 1, EInt 2); (EInt 2, EInt 3)]) (* multi-element map, DISTINCT constant keys *)
  ; gs_blank (EMapLit GTInt GTString [])                               (* _ = map[int]string{} — empty (int key; value type gated only by [goty_supported]) *)
  ; gs_blank (EMapLit GTU8 GTU8 [(EInt 1, EInt 2)])                     (* map[uint8]uint8{1: 2} — typed key/value, consts in range *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]])  (* println(len(map[int]int{1:2})): [len] of a map IS valid (a runtime int) — unlike [cap] *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 1))       (* println([]int{10,20}[1]): CONSTANT in-bounds index into a slice literal — VALID Go, a RUNTIME int (supported, like [len]) *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 5))       (* []int{10,20}[5]: an OOB POSITIVE constant index is VALID Go — for a SLICE (unlike an array) gc does NOT compile-check bounds; it's a run-time PANIC.  So SUPPORTED (verified: gc builds it); its OOB-safety is BEHAVIORAL (since tier R2 GoSem DENOTES its true [rt_index_oob] panic; the behavioral gate rejects it), NOT supportedness *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]))  (* []int{10,20}[len([]int{1})]: a RUNTIME (non-constant) integer index — VALID Go, bounds are a run-time property; supported.  Locks that the rule is NOT [EInt]-only *)
  ; mkProgram (mkIdent "main" eq_refl)                                   (* defer println("bye"); return — a deferred CALL is supported (same gate as an expr statement) *)
      [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "bye"]); GsReturn]
  ].
Example good_programs_supported : forallb supported_program good_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** EXPRESSION-LEVEL direct pins — predicates not surfaced through the program lists: the [EStr] literal is a
    printable scalar / value, and the unsound platform-[uint] complement is sealed INSIDE [complement_const]
    (returns [None]) while fixed-width unsigned ([uint8]) / signed ([int]) still fold exactly. *)
Example str_printable : printable_arg_ok (EStr "hi") = true.  Proof. reflexivity. Qed.
Example str_svalue    : svalue (EStr "x") = true.            Proof. reflexivity. Qed.
Example complement_const_uint_none  : complement_const GTUint 0 = None.        Proof. reflexivity. Qed.
Example complement_const_u8_exact   : complement_const GTU8 0 = Some 255%Z.    Proof. reflexivity. Qed.
Example complement_const_int_signed : complement_const GTInt 0 = Some (-1)%Z.  Proof. reflexivity. Qed.

(** FORGE-RESISTANCE — [eq_refl] cannot inhabit [SupportedProgram <bad>] (= [false = true]); a representative
    sample (bare value statement · non-main package · free identifier · constant overflow) locks that NO
    certificate exists for a rejected program.  (The boolean lists above pin every rejection; these prove the
    certificate is unforgeable.  Note: [Fail Lemma … . Proof. … Qed.] would NOT work — [Fail] guards only the
    goal-opening vernac, which always succeeds; the [:= eq_refl] term form is what must fail to typecheck.) *)
Fail Example forge_value_stmt :
  SupportedProgram unsupported_value_stmt := eq_refl.
Fail Example forge_nonmain_pkg :
  SupportedProgram (mkProgram (mkIdent "lib" eq_refl) [GsReturn]) := eq_refl.
Fail Example forge_free_blank :
  SupportedProgram (gs_blank (EId (mkIdent "x" eq_refl))) := eq_refl.
Fail Example forge_uint8_overflow :
  SupportedProgram (pl_arg (gs_u8 (EInt 300))) := eq_refl.

(** ===================================================================================================
    ===== SEMANTIC: BehaviorSafe over GoSem (future) =====
    =================================================================================================== *)

(** Reserved for GoSem COMPLETION: the behavioral-safety GATE over the AST's denotation.  The GATE is NOT yet
    defined — GoSem's slice-1 denotation ([denote_program]) is too PARTIAL to define it against — and a
    placeholder [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the
    charter forbids (§8 Rule 4).  (FIRST proof-only PROPERTIES do exist in [GoSemSafe.v] — a NARROW DECIDABLE
    emission gate [GoSemSafe.panic_free_gate] / [emit_panic_free_gated] (end-to-end sound): accepted iff the
    program denotes to [c] with [cmd_no_panic c] — denotable panics rejected there, an ABSENT (undenoted)
    program by non-denotation — but that
    is NOT this full [BehaviorSafe] gate and does NOT gate the main output.)  When GoSem is
    complete enough: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its GoSem denotation>],
    and GoEmit gains [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions bad_programs_rejected.
Print Assumptions ctmap_conv_unsupported_target_rejected.
