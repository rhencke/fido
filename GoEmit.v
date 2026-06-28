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
From Stdlib Require Import String.
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

(** ---- THE FIRST CERTIFIED EMISSION (the AST-first seed) ----  a runnable empty `package main`, emitted
    ONLY through the proof-gated path: [demo_supported] discharges the certificate, [emit_supported] prints it,
    and [demo_emit_bytes] pins the exact emitted Go source.  (A non-main package would fail [SupportedProgram]
    — [reflexivity] would not close — so it could not be certified or emitted.) *)
Definition demo_prog : Program := mkProgram (mkIdent "main" eq_refl).
Lemma demo_supported : SupportedProgram demo_prog.
Proof. reflexivity. Qed.
Definition demo_cert : EmittableProgram := mkEmittable demo_prog demo_supported.
Definition demo_emit : string := emit_supported demo_cert.
Example demo_emit_bytes :
  demo_emit = ("package main" ++ go_nl ++ go_nl ++ "func main() {" ++ go_nl ++ "}" ++ go_nl)%string.
Proof. vm_compute; reflexivity. Qed.

(** GATE — GoSafe/GoEmit are part of the trust base (the blessed path); keep them axiom-free. *)
Print Assumptions emit_supported.
Print Assumptions demo_emit_bytes.
