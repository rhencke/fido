(** GoSemSafe.v — the first behavioral-safety PROPERTIES over GoSem's denotation (proof-only — NOT extracted;
    but the [emit_panic_free] cert below BUILDS Go source via the blessed printer, so this file is not "no Go").

    ⚠ MODULE-WIDE CAVEAT (stated ONCE; the defs below do NOT repeat it): NONE of these PROPERTIES is the
    [BehaviorSafe] gate.  The emission cert + decidable gate below ([emit_panic_free] / [panic_free_gate] /
    [emit_panic_free_gated]) ARE behavioral, but NARROW — they cover the currently DENOTED GoSem fragment,
    which has no modeled nil/pointer/channel hazards and includes the constant slice-literal-index subfragment
    (in-bounds fully-evaluable cases denote; OOB / runtime / panicking cases are DECLINED).  So the gate rejects
    BOTH an explicit [panic()] AND every currently-modeled runtime-panic case — the latter by NON-DENOTATION
    (a SUPPORTED program with a runtime-panic construct simply fails to denote; that is faithful-or-absent
    rejection, not a proof it is unsafe).  Among ACCEPTED (denoted, panic-free) programs no [OPanic] occurs.
    They do NOT gate the MAIN output (that stays the trusted plugin) and are NOT full [BehaviorSafe].  Names are
    "panic-free …", NEVER [BehaviorSafe] / [SafeProgram] / bare "safe".

    Structure (each def's exact contract is at its site; the public surface is bundled in
    [gosem_panic_free_surface], single-sourced in PROGRESS.md "Current gates"):
    - PROPERTIES: a [CPan]-free command runs (via [run_cmd], for enough fuel — defers included) to [ORet],
      never [OPanic] ([panic_free_runs_ret]; [_ustep] lifts it to [ustep] through the general bridge
      [bridge_agrees], keeping [run_cmd] the authority).
    - PREDICATE: [panic_free_denotable] = the program DENOTES and its denotation is [CPan]-free
      ([cmd_no_panic] — behavioral, one check for immediate/deferred/future-runtime panics); ONE DECIDABLE
      bool on the RAW [Program]; it ENTAILS the panic-free run ([panic_free_denotable_runs_ret][_ustep]) and
      REFINES [SupportedProgram] ([panic_free_denotable_supported]).
    - CERT + EMITTER: [PanicFreeEmittable] (program + [panic_free_denotable]) REFINES [GoEmit.EmittableProgram];
      [emit_panic_free] emits through the blessed [emit_supported] path, but its PRECONDITION is a proven
      panic-free run ([pfe_runs_ret]), not merely syntactic [SupportedProgram].
    - DECIDABLE GATE: [panic_free_gate] : [Program -> option PanicFreeEmittable] decides the predicate and
      builds-cert-or-rejects (SOUND + COMPLETE); [emit_panic_free_gated] is the end-to-end decide-then-emit
      ([emit_panic_free_gated_sound]: emit ⟹ the run guarantee + blessed bytes) — the ancestor of [emit_safe].
    Plus the cmd.v-level DEFER-FREE exact-output panic lemma ([run_cmd_panics_world]). *)

From Fido Require Import preamble cmd GoAst GoTypes GoSafe GoSem cmd_unified unified GoEmit.
From Stdlib Require Import String List Bool Sumbool ZArith.   (* ZArith registers Z's number notation so [EInt 10] type-directs to [Z] while nat fuel stays nat (as in GoSem) *)
Import ListNotations.

(** Panic-freedom is judged on the DENOTATION, by cmd.v's own authority: [cmd_no_panic c] (no [CPan] node
    anywhere — body or deferred) is a decidable [bool] over the denoted command, so the gate needs NO syntactic
    panic-site predicate.  An immediate [panic(e)] denotes [CPan], a deferred one [CDfr (CPan ..) _], and any
    FUTURE runtime-panic denotation (e.g. a determined divide-by-zero) is a [CPan] too — all rejected by this
    ONE check, with no per-construct syntax rule to keep in sync. *)

(** The PRE-TERMINAL output world of a defer-free command: [go] threads each [COut] through [w_log], stopping
    at the terminal ([CRet] or [CPan]).  A structural spec of [go]'s accumulated world, consumed by the
    [go_panics_world] exact-output panic lemma below. *)
Fixpoint cmd_out_world (c : Cmd unit) (w : World) : World :=
  match c with
  | COut b xs c' => cmd_out_world c' (w_log b xs w)
  | _ => w
  end.

(** The panic value a defer-free command ends in ([None] if it never panics). *)
Fixpoint cmd_panic_val (c : Cmd unit) : option GoAny :=
  match c with COut _ _ c' => cmd_panic_val c' | CPan v => Some v | _ => None end.

(** A defer-free command that DOES panic ([cmd_panic_val = Some v]) runs (via [go]) to [OPanic v] with the
    EXACT pre-panic output [cmd_out_world c w] — faithful: the outputs BEFORE the panic still happen, then the
    panic carries [v]. *)
Lemma go_panics_world : forall c w v,
  no_defer c = true -> cmd_panic_val c = Some v -> go c w = (OPanic v (cmd_out_world c w), nil).
Proof.
  intro c; induction c as [a | b xs c' IH | v0 | d c' IH] using Cmd_rect';
    intros w v Hnd Hpv; cbn [go no_defer cmd_panic_val cmd_out_world] in *.
  - discriminate Hpv.
  - exact (IH (w_log b xs w) v Hnd Hpv).
  - injection Hpv as ->. reflexivity.
  - discriminate Hnd.
Qed.

Lemma run_cmd_panics_world : forall c w v,
  no_defer c = true -> cmd_panic_val c = Some v -> run_cmd 1 c w = Some (OPanic v (cmd_out_world c w)).
Proof.
  intros c w v Hnd Hpv. unfold run_cmd. rewrite (go_panics_world c w v Hnd Hpv). reflexivity.
Qed.

(** The DENOTATIONAL behavioral-safety result: a program whose denotation is [CPan]-free runs to [ORet] —
    never [OPanic] — for enough fuel (defers included: a deferred [println] runs at return and cannot panic).
    Composes cmd.v's universal [run_cmd_terminates] with [run_cmd_no_panic_ret] (a completing panic-free run
    returns [ORet]). *)
Theorem panic_free_runs_ret : forall (c : Cmd unit) w,
  cmd_no_panic c = true ->
  exists fuel w', run_cmd fuel c w = Some (ORet tt w').
Proof.
  intros c w Hnp.
  destruct (run_cmd_terminates c w) as [fuel [oc Hrun]].
  destruct (run_cmd_no_panic_ret fuel c w oc Hrun Hnp) as [w' ->].
  exists fuel, w'. exact Hrun.
Qed.

(** Boundary demos: a panic-free program runs to [ORet]; a program that DOES panic runs to [OPanic] (the
    property is exactly about the [panic] primitive, not vacuous). *)
Definition panic_free_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "ok"]); GsReturn].
Example panic_free_prog_runs_ret : forall w,
  match denote_program panic_free_prog with Some c => run_cmd 1 c w | None => None end
  = Some (ORet tt (w_log true (anyt TString "ok" :: nil) w)).
Proof. intro w. vm_compute. reflexivity. Qed.

Definition panicking_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "boom"])].
Example panicking_prog_panics : forall w,
  match denote_program panicking_prog with Some c => run_cmd 1 c w | None => None end
  = Some (OPanic (anyt TString "boom") w).
Proof. intro w. vm_compute. reflexivity. Qed.

(** End-to-end APPLICATION of [run_cmd_panics_world] (not a black-box compute): `func main(){ println("x");
    panic("boom") }` DENOTES to a defer-free [COut]-then-[CPan] command, so BOTH premises hold explicitly
    ([panic_after_output_premises]: [no_defer] + [cmd_panic_val = Some boom]) and the theorem APPLIES — the
    program runs to [OPanic boom] with the pre-panic output "x" already logged. *)
Definition panic_after_output_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "x"]);
     GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "boom"])].
Definition panic_after_output_cmd : Cmd unit :=
  COut true (anyt TString "x" :: nil) (CPan (anyt TString "boom")).
Example panic_after_output_denotes :
  denote_program panic_after_output_prog = Some panic_after_output_cmd.
Proof. vm_compute. reflexivity. Qed.
Example panic_after_output_premises :
  no_defer panic_after_output_cmd = true
  /\ cmd_panic_val panic_after_output_cmd = Some (anyt TString "boom").
Proof. split; reflexivity. Qed.
Example panic_after_output_runs : forall w,
  match denote_program panic_after_output_prog with Some c => run_cmd 1 c w | None => None end
  = Some (OPanic (anyt TString "boom") (w_log true (anyt TString "x" :: nil) w)).
Proof.
  intro w.
  rewrite panic_after_output_denotes.   (* PROGRAM denotes to the defer-free command... *)
  rewrite (run_cmd_panics_world panic_after_output_cmd w (anyt TString "boom")
             (proj1 panic_after_output_premises) (proj2 panic_after_output_premises)).   (* ...run via the theorem *)
  reflexivity.
Qed.

(** ★ The panic-freedom guarantee reaches the OPERATIONAL semantics.  Composing the GENERAL cmd↔unified bridge
    [cmd_unified.bridge_agrees] (for ANY command — defers included — the [ustep] run AGREES with the
    deterministic [run_cmd]) with [run_cmd_no_panic_ret]: a [CPan]-free command runs under [ustep] — the
    calculus [unified.v]'s race-freedom / liveness are proved on — to COMPLETION ([uc_live 0 = false]) with NO
    panic ([uc_panic 0 = None]), its output equal to the [run_cmd] [ORet] run's.  cmd.v's [run_cmd] STAYS the
    authority: the conclusion CARRIES [run_cmd fuel c w = Some (ORet tt w')] and ties [uc_out] to that [w']
    (not a free observer). *)
Theorem panic_free_runs_ret_ustep : forall (c : Cmd unit) ucap w,
  cmd_no_panic c = true ->
  exists (uc : UConfig) (w' : World) (fuel : nat),
    run_cmd fuel c w = Some (ORet tt w')                    (* cmd.v's AUTHORITATIVE panic-free [ORet] run — grounds [w'] *)
    /\ usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = None
    /\ w_output w' = w_output w ++ map snd (uc_out uc).
Proof.
  intros c ucap w Hnp.
  destruct (bridge_agrees c ucap w) as [uc [oc [fuel [Hus [Hrun [Hlive [Hpan Hout]]]]]]].
  destruct (run_cmd_no_panic_ret fuel c w oc Hrun Hnp) as [w' ->].
  exists uc, w', fuel. split; [ exact Hrun | split; [ exact Hus | split; [ exact Hlive | split ] ] ].
  - rewrite Hpan. reflexivity.
  - cbn [oc_world] in Hout. exact Hout.
Qed.

(** The GATE-SHAPE predicate.  [panic_free_runs_ret] takes a command as its subject; a real gate must be
    DECIDABLE on the raw [Program].  [panic_free_denotable p] computes the denotation and checks it [CPan]-free
    with cmd.v's own [cmd_no_panic] — BEHAVIORAL by construction: any denotation containing a panic (an
    immediate [panic(e)], a deferred one, or a future runtime-panic case) is rejected by this one check.
    It ENTAILS the panic-free run to [ORet] (below).  (The module-wide caveat applies: the DECIDABLE gate
    consuming this predicate is [panic_free_gate] (below), and the narrow emission cert/emitter built on it are
    [emit_panic_free] / [emit_panic_free_gated].) *)
Definition panic_free_denotable (p : Program) : bool :=
  match denote_program p with Some c => cmd_no_panic c | None => false end.

(** The decidable [panic_free_denotable] ENTAILS the panic-free [ORet] run (for enough fuel — defers
    included): the predicate itself computes [denote_program p = Some c] with [cmd_no_panic c], and
    [panic_free_runs_ret] finishes. *)
Theorem panic_free_denotable_runs_ret : forall p w,
  panic_free_denotable p = true ->
  exists c fuel w', denote_program p = Some c /\ run_cmd fuel c w = Some (ORet tt w').
Proof.
  intros p w H. unfold panic_free_denotable in H.
  destruct (denote_program p) as [c|] eqn:Ec; [|discriminate H].
  destruct (panic_free_runs_ret c w H) as [fuel [w' Hrun]].
  exists c, fuel, w'. split; [reflexivity | exact Hrun].
Qed.

(** The same decidable-predicate guarantee at the OPERATIONAL level (via [panic_free_runs_ret_ustep]). *)
Theorem panic_free_denotable_runs_ret_ustep : forall p ucap w,
  panic_free_denotable p = true ->
  exists c uc w' fuel,
    denote_program p = Some c
    /\ run_cmd fuel c w = Some (ORet tt w')
    /\ usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = None
    /\ w_output w' = w_output w ++ map snd (uc_out uc).
Proof.
  intros p ucap w H. unfold panic_free_denotable in H.
  destruct (denote_program p) as [c|] eqn:Ec; [|discriminate H].
  destruct (panic_free_runs_ret_ustep c ucap w H)
    as [uc [w' [fuel [Hrun [Hus [Hlive [Hpan Hout]]]]]]].
  exists c, uc, w', fuel.
  split; [reflexivity | split; [exact Hrun | split; [exact Hus | split; [exact Hlive | split; [exact Hpan | exact Hout]]]]].
Qed.

(** The predicate DECIDES (non-vacuous): TRUE for [panic_free_prog], FALSE for [panicking_prog]. *)
Example panic_free_denotable_decides :
  panic_free_denotable panic_free_prog = true /\ panic_free_denotable panicking_prog = false.
Proof. split; reflexivity. Qed.

(** [panic_free_denotable] REFINES [SupportedProgram]: [panic_free_denotable p = true] implies
    [supported_program p = true], which IS [SupportedProgram p] — the [Prop] [GoEmit.EmittableProgram] carries in
    its [ep_supported] field.  So this support proof suffices to build that [ep_supported] component.  Exactly
    that implication — NOT a claim about "safe" programs in general, about a future [BehaviorSafe], or about
    [SafeProgram]. *)
Lemma panic_free_denotable_supported : forall p,
  panic_free_denotable p = true -> SupportedProgram p.
Proof.
  intros p H. unfold panic_free_denotable in H.
  destruct (denote_program p) as [c|] eqn:Ec; [|discriminate H].
  apply (denotable_supported p). apply (proj1 (denote_program_dec p)). congruence.
Qed.

(** ---- SEED of the GoSem-BACKED emission certificate (north-star: [BehaviorSafe] -> [SafeProgram] ->
    [emit_safe]).  On the DENOTED fragment "panic-free" IS the behavioral-safety condition: the fragment has no
    modeled nil/pointer/channel hazards, and its modeled runtime-panic cases (an OOB constant slice index, a
    panicking literal element, a runtime blank-assign) are DECLINED at denotation — a full [BehaviorSafe]
    (nil deref / send-on-closed / race) lands with those constructs.  So this is NAMED for what it PROVES, NOT
    [SafeProgram] / [BehaviorSafe]: a program that is EMITTABLE ([SupportedProgram], via
    [panic_free_denotable_supported]) AND carries the decidable panic-free RUN guarantee.  It is the FIRST
    certificate whose PRECONDITION is behavioral (a proven [ORet] run), not merely the syntactic
    [SupportedProgram] of [GoEmit.EmittableProgram]. *)
Record PanicFreeEmittable : Type := mkPanicFreeEmittable {
  pfe_program    : Program;
  pfe_panic_free : panic_free_denotable pfe_program = true;
}.

(** REFINEMENT: a [PanicFreeEmittable] IS an [EmittableProgram] (still emittable through the BLESSED path) —
    its behavioral precondition discharges the syntactic [ep_supported] via [panic_free_denotable_supported]. *)
Definition pfe_emittable (c : PanicFreeEmittable) : EmittableProgram :=
  mkEmittable (pfe_program c) (panic_free_denotable_supported (pfe_program c) (pfe_panic_free c)).

(** SEED of [emit_safe]: the blessed emitter on the behavioral certificate.  Goes THROUGH [emit_supported]
    (no forked emission logic — pinned by [emit_panic_free_via_blessed]); the difference from plain
    [emit_supported] is the STRONGER precondition — you cannot build a [PanicFreeEmittable] without discharging
    [panic_free_denotable], so this emitter accepts ONLY programs with a proven panic-free run. *)
Definition emit_panic_free (c : PanicFreeEmittable) : string := emit_supported (pfe_emittable c).
Lemma emit_panic_free_via_blessed : forall c, emit_panic_free c = emit_supported (pfe_emittable c).
Proof. reflexivity. Qed.

(** The behavioral guarantee TRAVELS with the certificate: a [PanicFreeEmittable]'s program DENOTES and RUNS to
    [ORet] (never [OPanic]) for enough fuel — the FIRST emission certificate carrying a GoSem-backed
    execution guarantee.  (Direct from [panic_free_denotable_runs_ret] on the carried proof.) *)
Theorem pfe_runs_ret : forall (c : PanicFreeEmittable) w,
  exists cmd fuel w', denote_program (pfe_program c) = Some cmd /\ run_cmd fuel cmd w = Some (ORet tt w').
Proof.
  intros c w. exact (panic_free_denotable_runs_ret (pfe_program c) w (pfe_panic_free c)).
Qed.

(** A concrete behavioral certificate ([panic_free_prog] = `println("ok"); return`) built + emitted through the
    behavioral path, its run guarantee discharged. *)
Definition pfe_demo : PanicFreeEmittable := mkPanicFreeEmittable panic_free_prog eq_refl.
Example pfe_demo_runs : forall w,
  exists cmd fuel w', denote_program (pfe_program pfe_demo) = Some cmd /\ run_cmd fuel cmd w = Some (ORet tt w').
Proof. intro w. exact (pfe_runs_ret pfe_demo w). Qed.

(** ---- The DECIDABLE panic-free emission GATE.  [PanicFreeEmittable] alone needs a hand proof of
    [panic_free_denotable p = true]; [panic_free_gate] builds the cert BY DECISION on ANY raw [Program] —
    either REJECT ([None]) or return the cert — so an emit-or-reject pipeline needs NO per-program proof.
    [emit_panic_free_gated] composes it end-to-end: from ANY program, reject or emit Go source CARRYING the
    panic-free run guarantee — the honest ancestor of [emit_safe] as a TOTAL decide-then-emit function. *)
Definition panic_free_gate (p : Program) : option PanicFreeEmittable :=
  match sumbool_of_bool (panic_free_denotable p) with
  | left H  => Some (mkPanicFreeEmittable p H)
  | right _ => None
  end.
Definition emit_panic_free_gated (p : Program) : option string :=
  match panic_free_gate p with Some c => Some (emit_panic_free c) | None => None end.

(** SOUND — a returned cert is FOR [p] and [p] is panic-free-denotable (so [pfe_runs_ret] applies to it). *)
Lemma panic_free_gate_sound : forall p c,
  panic_free_gate p = Some c -> panic_free_denotable p = true /\ pfe_program c = p.
Proof.
  intros p c H. unfold panic_free_gate in H.
  destruct (sumbool_of_bool (panic_free_denotable p)) as [Ht|Hf].
  - injection H as <-. cbn. split; [exact Ht | reflexivity].
  - discriminate H.
Qed.
(** COMPLETE — every panic-free-denotable program is ACCEPTED. *)
Lemma panic_free_gate_complete : forall p,
  panic_free_denotable p = true -> exists c, panic_free_gate p = Some c.
Proof.
  intros p H. unfold panic_free_gate.
  destruct (sumbool_of_bool (panic_free_denotable p)) as [Ht|Hf];
    [eexists; reflexivity | rewrite H in Hf; discriminate].
Qed.
(** The gated emitter goes THROUGH the accepted cert's blessed emission (no forked logic). *)
Lemma emit_panic_free_gated_some : forall p c,
  panic_free_gate p = Some c -> emit_panic_free_gated p = Some (emit_panic_free c).
Proof. intros p c H. unfold emit_panic_free_gated. rewrite H. reflexivity. Qed.

(** END-TO-END SOUNDNESS of the gated emitter: if it EMITS ([Some s]) then (1) the program is
    [panic_free_denotable], (2) its denotation RUNS to [ORet] for enough fuel — never [OPanic] — for every
    world, and (3) [s] is the BLESSED emission ([emit_panic_free]) of the very cert the gate accepted (emission
    goes through GoEmit's certificate path, not a fork).  So a successful [emit_panic_free_gated] carries the
    behavioral guarantee AND is byte-identical to the blessed path — the honest ancestor of [emit_safe]'s
    soundness (still no theorem to REAL Go — gap #10). *)
Theorem emit_panic_free_gated_sound : forall p s,
  emit_panic_free_gated p = Some s ->
  panic_free_denotable p = true
  /\ (forall w, exists cmd fuel w', denote_program p = Some cmd /\ run_cmd fuel cmd w = Some (ORet tt w'))
  /\ (exists c, panic_free_gate p = Some c /\ s = emit_panic_free c).
Proof.
  intros p s H. unfold emit_panic_free_gated in H.
  destruct (panic_free_gate p) as [c|] eqn:Eg; [|discriminate H]. injection H as <-.
  destruct (panic_free_gate_sound p c Eg) as [Hpf _].
  split; [exact Hpf | split].
  - intros w. exact (panic_free_denotable_runs_ret p w Hpf).
  - exists c. split; reflexivity.
Qed.

(** The gate DECIDES both ways on the boundary demos (ACCEPTS panic-free, REJECTS panicking). *)
Example panic_free_gate_decides :
  (exists c, panic_free_gate panic_free_prog = Some c) /\ panic_free_gate panicking_prog = None.
Proof. split; [apply panic_free_gate_complete; reflexivity | reflexivity]. Qed.

(** Representative emission-gate reach test for a NON-[panic()] runtime panic.  [slice_oob_prog] is VALID Go
    and [SupportedProgram] (an OOB-positive constant slice index is a run-time panic, not a compile error);
    GoSem DECLINES it, so [panic_free_gate] rejects it — by NON-denotation (faithful-or-absent), NOT a positive
    proof that OOB programs are unsafe.  The in-bounds twin is accepted and emitted.  The class-level
    denotation boundary lives in GoSem ([eval_slice_index_{reduces,inbounds_class,oob_class,supported}]). *)
Definition slice_safe_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 1)]); GsReturn].
Definition slice_oob_prog : Program :=
  mkProgram (mkIdent "main" eq_refl)
    [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 5)]); GsReturn].
Example panic_free_gate_slice :
  supported_program slice_safe_prog = true                 (* BOTH are valid Go (B1: OOB-positive const index = run-time panic) ... *)
  /\ supported_program slice_oob_prog = true
  /\ (exists c, panic_free_gate slice_safe_prog = Some c)   (* ... the in-bounds one the BEHAVIORAL gate ACCEPTS ... *)
  /\ panic_free_gate slice_oob_prog = None                  (* ... the OOB one (VALID Go!) it REJECTS behaviorally, via non-denotation *)
  /\ emit_panic_free_gated slice_safe_prog <> None
  /\ emit_panic_free_gated slice_oob_prog = None.
Proof.
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ apply panic_free_gate_complete; vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; discriminate | vm_compute; reflexivity ].
Qed.

(** DEFER reaches the gate: [gosem_defer_prog] (`defer println("bye"); return`) denotes to a [CPan]-free
    command, so the gate ACCEPTS + EMITS it — the first BEHAVIORALLY-certified defer program.
    [gosem_defer_panic_prog] (`defer panic("boom"); ...`) is SUPPORTED and DENOTABLE (valid Go that denotes —
    the rejection below is [cmd_no_panic]'s judgment on the DENOTATION, which contains [CDfr (CPan ..) _]; NOT
    non-denotation incompleteness), and the gate REJECTS it: a deferred panic still ends the run in [OPanic]
    ([GoSem.rc_defer_panic]), so admitting it would break [pfe_runs_ret]. *)
Example panic_free_gate_defer :
  supported_program gosem_defer_prog = true
  /\ (exists c, panic_free_gate gosem_defer_prog = Some c)
  /\ emit_panic_free_gated gosem_defer_prog <> None
  /\ supported_program gosem_defer_panic_prog = true
  /\ denotable_program gosem_defer_panic_prog = true
  /\ panic_free_gate gosem_defer_panic_prog = None
  /\ emit_panic_free_gated gosem_defer_panic_prog = None.
Proof.
  split; [ vm_compute; reflexivity | ].
  split; [ apply panic_free_gate_complete; vm_compute; reflexivity | ].
  split; [ vm_compute; discriminate | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

(** PUBLIC SURFACE — the module's panic-free safety results bundled into ONE constant, so a SINGLE
    [Print Assumptions] covers all their transitive cones (the Docker manifest gate FAILS on any axiom; rule 3).
    Adding a panic_free_* theorem to the certified surface = adding it HERE (else it is an internal helper,
    not advertised zero-axiom). *)
Definition gosem_panic_free_surface :=
  (panic_free_runs_ret, run_cmd_panics_world, panic_free_runs_ret_ustep,
   panic_free_denotable_runs_ret, panic_free_denotable_runs_ret_ustep,
   panic_free_denotable_supported, pfe_runs_ret, emit_panic_free_via_blessed,
   panic_free_gate_sound, panic_free_gate_complete, emit_panic_free_gated_some, emit_panic_free_gated_sound,
   panic_free_gate_slice, panic_free_gate_defer).
Print Assumptions gosem_panic_free_surface.
