(** ============================================================================
    GoEmit.v — the ONLY blessed emission path (AST-first spine; see ARCHITECTURE.md §2/§8).
    Emission REQUIRES a certificate: an [EmittableProgram] is a [Program] PLUS a [SupportedProgram] proof, and
    [emit_supported] is the sole exported way to turn a program into Go text.  There is DELIBERATELY no
    `emit : Program -> string` — a RAW program cannot reach the blessed path (charter §8 Rule 3), so the
    certificate is never decorative.
    PHASE-1: this certifies SUPPORTEDNESS (syntactic), NOT behavioral safety.  The behavioral path
    ([SafeProgram] = EmittableProgram + GoSafe.BehaviorSafe, [emit_safe]) lands once GoSem is authoritative.
    A raw printer (GoPrint.print_program) still exists for proofs/tests, but it is NOT this blessed emitter.
    ============================================================================ *)
From Fido Require Import GoAst GoPrint GoSafe.
From Stdlib Require Import String List ZArith.  (* List/ListNotations: body list; ZArith: [EInt]'s Z (Eqdep_dec/UIP no longer needed — emit_supported_program_inj is UIP-free) *)
Import ListNotations.
Open Scope string_scope.

(** A program cleared for the blessed printer: the AST + its supportedness certificate (the proof is part of
    the value, so an [EmittableProgram] cannot be built for an unsupported program). *)
Record EmittableProgram : Type := mkEmittable {
  ep_program   : Program;
  ep_supported : SupportedProgram ep_program;
}.

(** The blessed emitter: prints ONLY a certificate-carrying program.  (There is intentionally no
    [emit : Program -> string] — that would make the certificate decorative.) *)
Definition emit_supported (p : EmittableProgram) : string := print_program (ep_program p).

(** ---- THE FIRST CERTIFIED EMISSION (the AST-first seed) ----  a runnable `package main` whose `func main`
    body is seven real statements — [println(1)], [println(int64(3))] (a value-position scalar CONVERSION),
    [println(1 + 2)] (a binary-operator [EBn], exercising operator printing + gofmt spacing through the path),
    [println("hi")] (a STRING-literal [EStr], exercising [print_string_lit] through the path),
    [_ = []int(nil)] (a [GsBlankAssign] discarding a type-form [EConv] CONVERSION value), [_ = []int{1}] (a
    slice composite literal [ESliceLit]), then a bare [return] — all Go builtins / no import (rule 5), built as
    structured [GExpr]/[GoStmt]s and printed by the machine-checked [gprint] (`make emit-demo` then confirms
    the Go compiler BUILDS it).  This exercises the landed [EBn], [EStr] (`"hi"`), [EConv] (`[]int(nil)`), [ESliceLit]
    (`[]int{1}`) and [GsBlankAssign] (`_ = e`) forms END-TO-END through the BLESSED emitter to compilable Go —
    not just in isolated round-trip proofs.  Emitted ONLY through the
    proof-gated path: [demo_supported] discharges the certificate, [emit_supported] prints it, [demo_emit_bytes]
    pins the exact emitted Go source.  (A non-main package — OR a body outside the supported statement subset,
    e.g. a bare-value statement, or `_ = <void call>` — would make [SupportedProgram] FALSE, so [reflexivity]
    would not close and it could not be certified or emitted.) *)
Definition demo_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EInt 1]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [EBn BAdd (EInt 1) (EInt 2)]);
             GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "hi"]);
             GsBlankAssign (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)));
             GsBlankAssign (ESliceLit GTInt [EInt 1]);
             GsReturn].
Lemma demo_supported : SupportedProgram demo_prog.
Proof. reflexivity. Qed.
Definition demo_cert : EmittableProgram := mkEmittable demo_prog demo_supported.
Definition demo_emit : string := emit_supported demo_cert.
Example demo_emit_bytes :
  demo_emit = ("package main" ++ go_nl ++ go_nl ++ "func main() {" ++ go_nl ++
               go_tab ++ "println(1)" ++ go_nl ++ go_tab ++ "println(int64(3))" ++ go_nl ++
               go_tab ++ "println(1 + 2)" ++ go_nl ++
               go_tab ++ "println(""hi"")" ++ go_nl ++
               go_tab ++ "_ = []int(nil)" ++ go_nl ++
               go_tab ++ "_ = []int{1}" ++ go_nl ++
               go_tab ++ "return" ++ go_nl ++ "}" ++ go_nl)%string.
Proof. vm_compute; reflexivity. Qed.

(** REGRESSION (P0, external review 2026-06-28): the certificate is UNFORGEABLE for an unsupported program —
    [mkEmittable] DEMANDS a [SupportedProgram] proof, and none exists for the bare-value body
    [unsupported_value_stmt] (`func main(){ 1 }`), so [eq_refl] cannot inhabit [SupportedProgram _].  [Fail]
    locks the type-level guarantee that [emit_supported] can never print that invalid Go. *)
Fail Definition unsupported_value_cert : EmittableProgram :=
  mkEmittable unsupported_value_stmt eq_refl.

(** EMITTER FAITHFULNESS at the BLESSED boundary — [emit_supported] is INJECTIVE on the PROGRAM: two
    [EmittableProgram]s that emit the SAME Go text carry the SAME [ep_program].  This is just
    [print_program_inj] (raw-printer injectivity) lifted through [ep_program] — equal output ⇒ equal program.
    (We DO NOT lift it to whole-CERTIFICATE equality [c1 = c2]: that would need UIP on the [ep_supported]
    proofs, and certificate-proof equality is not operationally meaningful — what matters is that the emitted
    text pins the program.  Still print-injectivity, NOT Go-syntax acceptance — see [print_program_inj].) *)
Lemma emit_supported_program_inj :
  forall c1 c2, emit_supported c1 = emit_supported c2 -> ep_program c1 = ep_program c2.
Proof. intros c1 c2 H. unfold emit_supported in H. exact (print_program_inj _ _ H). Qed.

(** GATE — GoSafe/GoEmit are part of the trust base (the blessed path); keep them axiom-free. *)
Print Assumptions emit_supported.
Print Assumptions demo_emit_bytes.
Print Assumptions emit_supported_program_inj.
