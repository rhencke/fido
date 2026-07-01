(** GoSemSafe.v — the first behavioral-safety PROPERTIES over GoSem's denotation (proof-only — NOT extracted;
    but the [emit_panic_free] cert below BUILDS Go source via the blessed printer, so this file is not "no Go").

    ⚠ MODULE-WIDE CAVEAT (stated ONCE; the defs below do NOT repeat it): NONE of these PROPERTIES is the
    [BehaviorSafe] gate.  The emission cert + decidable gate below ([emit_panic_free] / [panic_free_gate] /
    [emit_panic_free_gated]) ARE behavioral, but NARROW — slice 1 denotes NO pointers / slices / channels, so
    [panic] is the ONLY unsafe runtime op; they do NOT gate the MAIN output (that stays the trusted plugin) and
    are NOT full [BehaviorSafe].  Names are "panic-free …", NEVER [BehaviorSafe] / [SafeProgram] / bare "safe".

    Structure (each def's exact contract is at its site; the public surface is bundled in
    [gosem_panic_free_surface], single-sourced in PROGRESS.md "Current gates"):
    - PROPERTIES: a program that DENOTES + is syntactically panic-free runs (via [run_cmd]) to [ORet], never
      [OPanic] ([panic_free_runs_ret]; [_output] pins the explicit output world; [_ustep] lifts it to [ustep],
      keeping [run_cmd] the authority).
    - PREDICATE: [panic_free_denotable] folds "denotes + syntactically panic-free" into ONE DECIDABLE bool on the
      RAW [Program]; it ENTAILS the panic-free run ([panic_free_denotable_runs_ret][_output][_ustep]) and REFINES
      [SupportedProgram] ([panic_free_denotable_supported]).
    - CERT + EMITTER: [PanicFreeEmittable] (program + [panic_free_denotable]) REFINES [GoEmit.EmittableProgram];
      [emit_panic_free] emits through the blessed [emit_supported] path, but its PRECONDITION is a proven
      panic-free run ([pfe_runs_ret]), not merely syntactic [SupportedProgram].
    - DECIDABLE GATE: [panic_free_gate] : [Program -> option PanicFreeEmittable] decides the predicate and
      builds-cert-or-rejects (SOUND + COMPLETE); [emit_panic_free_gated] is the end-to-end decide-then-emit
      ([emit_panic_free_gated_sound]: emit ⟹ the run guarantee + blessed bytes) — the ancestor of [emit_safe].
    Plus cmd.v-level DEFER-FREE building blocks ([run_cmd_panic_free_world] / [run_cmd_panics_world]). *)

From Fido Require Import preamble cmd GoAst GoTypes GoSafe GoSem cmd_unified unified GoSemUnified GoEmit.
From Stdlib Require Import String List Bool Sumbool.
Import ListNotations.

(** A statement is the panic primitive [panic(e)] — the only [denote_stmt] arm that yields a [CPan]. *)
Definition stmt_is_panic (s : GoStmt) : bool :=
  match s with
  | GsExprStmt (ECall (EId f) _) => String.eqb (proj1_sig f) "panic"
  | _ => false
  end.
Definition panic_free (b : list GoStmt) : bool := forallb (fun s => negb (stmt_is_panic s)) b.

(** [cmd_no_panic] (no [CPan] anywhere — cannot end in a panic Outcome) is the SINGLE authority in cmd.v (a
    [Cmd] predicate beside [no_defer]); consumed here for the panic-free safety property. *)
Lemma cbind_no_panic : forall (c : Cmd unit) (k : unit -> Cmd unit),
  cmd_no_panic c = true -> (forall u, cmd_no_panic (k u) = true) -> cmd_no_panic (cbind c k) = true.
Proof.
  intro c; induction c as [a | b xs c' IH | v | d c' IH] using Cmd_rect';
    intros k Hc Hk; cbn [cbind cmd_no_panic] in *.
  - apply Hk.
  - apply IH; [exact Hc | exact Hk].
  - discriminate Hc.
  - apply andb_true_iff in Hc as [Hd Hc']. rewrite Hd. cbn. apply IH; [exact Hc' | exact Hk].
Qed.

(** A NON-panic denoting statement emits a [CPan]-free command — panic is the only [CPan] source. *)
Lemma denote_stmt_no_panic : forall s c term,
  denote_stmt s = Some (c, term) -> stmt_is_panic s = false -> cmd_no_panic c = true.
Proof.
  intros s c term H Hnp. destruct s as [e | | ev | be | de]; cbn [denote_stmt] in H.
  - destruct (expr_stmt_ok e); [|discriminate H].
    destruct e as [ | | | | | | | fe fargs | | | | | | ]; try discriminate H.
    destruct fe as [ fi | | | | | | | | | | | | | ]; try discriminate H.
    cbn [stmt_is_panic] in Hnp. rewrite Hnp in H.
    destruct (eval_args fargs); [|discriminate H]. inversion H; subst. reflexivity.
  - inversion H; subst; reflexivity.
  - discriminate H.
  - destruct (svalue be); [|discriminate H]. destruct (eval_value be); [|discriminate H].
    inversion H; subst; reflexivity.
  - discriminate H.   (* GsDefer: [denote_stmt] = None *)
Qed.

(** A panic-free DENOTED body denotes to a [CPan]-free command. *)
Lemma denote_body_no_panic : forall b c, denote_body b = Some c -> panic_free b = true -> cmd_no_panic c = true.
Proof.
  induction b as [|s rest IH]; cbn [denote_body panic_free forallb]; intros c H Hpf.
  - inversion H; subst; reflexivity.
  - apply andb_true_iff in Hpf as [Hs Hrest]. apply negb_true_iff in Hs.
    destruct (denote_stmt s) as [[cs term]|] eqn:Es; [|discriminate H]. destruct term.
    + destruct (forallb stmt_ok rest); [|discriminate H]. inversion H; subst.
      exact (denote_stmt_no_panic s c true Es Hs).
    + destruct (denote_body rest) as [k|] eqn:Er; [|discriminate H]. inversion H; subst.
      apply cbind_no_panic; [exact (denote_stmt_no_panic s cs false Es Hs) | intro u; exact (IH k eq_refl Hrest)].
Qed.

(** The PRE-TERMINAL output world of a defer-free command: [go] threads each [COut] through [w_log], stopping
    at the terminal ([CRet] or [CPan]).  A structural spec of [go]'s accumulated world, independent of the
    [Outcome] — SHARED by both tails ([go_panic_free_world]'s [ORet] and [go_panics_world]'s [OPanic]). *)
Fixpoint cmd_out_world (c : Cmd unit) (w : World) : World :=
  match c with
  | COut b xs c' => cmd_out_world c' (w_log b xs w)
  | _ => w
  end.

(** A [CPan]-free, defer-free command runs (via [go]) to an [ORet] with output EXACTLY [cmd_out_world c w] —
    never an [OPanic], and the world is EXPLICIT (the accumulated logs), not merely existential. *)
Lemma go_panic_free_world : forall c w,
  cmd_no_panic c = true -> no_defer c = true -> go c w = (ORet tt (cmd_out_world c w), nil).
Proof.
  intro c; induction c as [a | b xs c' IH | v | d c' IH] using Cmd_rect';
    intros w Hnp Hnd; cbn [go cmd_no_panic no_defer cmd_out_world] in *.
  - destruct a. reflexivity.
  - exact (IH (w_log b xs w) Hnp Hnd).
  - discriminate Hnp.
  - discriminate Hnd.
Qed.

Lemma run_cmd_panic_free_world : forall c w,
  cmd_no_panic c = true -> no_defer c = true -> run_cmd 1 c w = Some (ORet tt (cmd_out_world c w)).
Proof.
  intros c w Hnp Hnd. unfold run_cmd. rewrite (go_panic_free_world c w Hnp Hnd). reflexivity.
Qed.

(** The DUAL, panic path: the panic value a defer-free command ends in ([None] if it never panics). *)
Fixpoint cmd_panic_val (c : Cmd unit) : option GoAny :=
  match c with COut _ _ c' => cmd_panic_val c' | CPan v => Some v | _ => None end.

(** A defer-free command that DOES panic ([cmd_panic_val = Some v]) runs (via [go]) to [OPanic v] with the
    EXACT pre-panic output [cmd_out_world c w] — faithful: the outputs BEFORE the panic still happen, then the
    panic carries [v].  The dual of [go_panic_free_world]. *)
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

(** The DENOTATIONAL behavioral-safety result, EXPLICIT-OUTPUT form: a panic-free supported program that
    DENOTES runs to [ORet] with output exactly [cmd_out_world c w] — never [OPanic].  ([no_defer] via
    [denote_body_no_defer].)  The existential [panic_free_runs_ret] below is its corollary (used by the
    operational lift). *)
Theorem panic_free_runs_ret_output : forall p c w,
  denote_program p = Some c -> panic_free (prog_body p) = true ->
  run_cmd 1 c w = Some (ORet tt (cmd_out_world c w)).
Proof.
  intros p c w Hden Hpf. unfold denote_program in Hden.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main") eqn:E; [|discriminate Hden].
  apply run_cmd_panic_free_world.
  - exact (denote_body_no_panic (prog_body p) c Hden Hpf).
  - exact (denote_body_no_defer (prog_body p) c Hden).
Qed.

Corollary panic_free_runs_ret : forall p c w,
  denote_program p = Some c -> panic_free (prog_body p) = true ->
  exists w', run_cmd 1 c w = Some (ORet tt w').
Proof.
  intros p c w Hden Hpf. exists (cmd_out_world c w). exact (panic_free_runs_ret_output p c w Hden Hpf).
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

(** ★ The panic-freedom guarantee reaches the OPERATIONAL semantics.  Composing [panic_free_runs_ret] (the
    denoted program's authoritative [run_cmd] reaches [ORet]) with the cmd↔unified bridge
    [GoSemUnified.denote_program_run_agrees] (the [unified.v] [ustep] run AGREES with the deterministic
    [run_cmd]): a syntactically panic-free supported program, once denoted, runs under [ustep] — the calculus
    [unified.v]'s race-freedom / liveness are proved on — to COMPLETION ([uc_live 0 = false]) with NO panic
    ([uc_panic 0 = None]), its output equal to the [run_cmd] [ORet] run's.  cmd.v's [run_cmd] STAYS the authority: the
    conclusion CARRIES [run_cmd 1 c w = Some (ORet tt w')] and ties [uc_out] to that [w'] (not a free observer).
    So the seed safety property is not merely denotational; it holds where the concurrency theory lives. *)
Theorem panic_free_runs_ret_ustep : forall p c ucap w,
  denote_program p = Some c -> panic_free (prog_body p) = true ->
  exists (uc : UConfig) (w' : World),
    run_cmd 1 c w = Some (ORet tt w')                       (* cmd.v's AUTHORITATIVE panic-free [ORet] run — grounds [w'] *)
    /\ usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = None
    /\ w_output w' = w_output w ++ map snd (uc_out uc).
Proof.
  intros p c ucap w Hden Hpf.
  destruct (panic_free_runs_ret p c w Hden Hpf) as [w' Hrun].
  destruct (denote_program_run_agrees p c ucap w Hden) as [uc [oc [Hus [Hrun' [Hlive [Hout Hpan]]]]]].
  assert (Hoc : oc = ORet tt w') by congruence. subst oc.
  exists uc, w'. split; [ exact Hrun | split; [ exact Hus | split; [ exact Hlive | split ] ] ].
  - rewrite Hpan. reflexivity.
  - cbn [oc_world] in Hout. exact Hout.
Qed.

(** The GATE-SHAPE predicate.  [panic_free_runs_ret] takes the denotation [denote_program p = Some c] as a
    HYPOTHESIS; a real gate must be DECIDABLE on the raw [Program].  So fold its two conditions into one boolean:
    [panic_free_denotable p] = the decidable image of "denotes" ([denotable_program], from [denote_program_dec])
    AND syntactic [panic_free] — computable from the program alone, and it ENTAILS the panic-free run to [ORet]
    (below).  (The
    module-wide caveat applies: the DECIDABLE gate consuming this predicate is [panic_free_gate] (below), and
    the narrow emission cert/emitter built on it are [emit_panic_free] / [emit_panic_free_gated].) *)
Definition panic_free_denotable (p : Program) : bool :=
  denotable_program p && panic_free (prog_body p).

(** EXPLICIT-OUTPUT form (mirrors [panic_free_runs_ret_output] for the gate-shape predicate): the decidable
    [panic_free_denotable] entails the program runs to [ORet] with output EXACTLY [cmd_out_world c w].  Composes
    [denote_program_dec] (the predicate's denotability conjunct gives the denotation) with
    [panic_free_runs_ret_output]. *)
Theorem panic_free_denotable_runs_ret_output : forall p w,
  panic_free_denotable p = true ->
  exists c, denote_program p = Some c /\ run_cmd 1 c w = Some (ORet tt (cmd_out_world c w)).
Proof.
  intros p w H. apply andb_true_iff in H as [Hden Hpf].
  destruct (denote_program p) as [c|] eqn:Ec.
  - exists c. split; [reflexivity | exact (panic_free_runs_ret_output p c w Ec Hpf)].
  - exfalso. exact (proj2 (denote_program_dec p) Hden Ec).
Qed.

Corollary panic_free_denotable_runs_ret : forall p w,
  panic_free_denotable p = true ->
  exists c w', denote_program p = Some c /\ run_cmd 1 c w = Some (ORet tt w').
Proof.
  intros p w H. destruct (panic_free_denotable_runs_ret_output p w H) as [c [Hden Hrun]].
  exists c, (cmd_out_world c w). split; [exact Hden | exact Hrun].
Qed.

(** The same decidable-predicate guarantee at the OPERATIONAL level (via [panic_free_runs_ret_ustep]). *)
Theorem panic_free_denotable_runs_ret_ustep : forall p ucap w,
  panic_free_denotable p = true ->
  exists c uc w',
    denote_program p = Some c
    /\ run_cmd 1 c w = Some (ORet tt w')
    /\ usteps ucap (ustart (cmd_to_ucmd c)) uc
    /\ uc_live uc 0 = false
    /\ uc_panic uc 0 = None
    /\ w_output w' = w_output w ++ map snd (uc_out uc).
Proof.
  intros p ucap w H. apply andb_true_iff in H as [Hden Hpf].
  destruct (denote_program p) as [c|] eqn:Ec.
  - destruct (panic_free_runs_ret_ustep p c ucap w Ec Hpf)
      as [uc [w' [Hrun [Hus [Hlive [Hpan Hout]]]]]].
    exists c, uc, w'.
    split; [reflexivity | split; [exact Hrun | split; [exact Hus | split; [exact Hlive | split; [exact Hpan | exact Hout]]]]].
  - exfalso. exact (proj2 (denote_program_dec p) Hden Ec).
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
  intros p H. apply andb_true_iff in H as [Hden _]. exact (denotable_supported p Hden).
Qed.

(** ---- SEED of the GoSem-BACKED emission certificate (north-star: [BehaviorSafe] -> [SafeProgram] ->
    [emit_safe]).  Slice 1's ONLY unsafe runtime op is [panic] (no ptrs / slices / channels denoted), so on the
    DENOTED fragment "panic-free" IS the behavioral-safety condition — a full [BehaviorSafe] (nil deref / OOB /
    send-on-closed / race) lands with those constructs.  So this is NAMED for what it PROVES, NOT [SafeProgram] /
    [BehaviorSafe]: a program that is EMITTABLE ([SupportedProgram], via [panic_free_denotable_supported]) AND
    carries the decidable panic-free RUN guarantee.  It is the FIRST certificate whose PRECONDITION is
    behavioral (a proven [ORet] run), not merely the syntactic [SupportedProgram] of [GoEmit.EmittableProgram]. *)
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
    [ORet] (never [OPanic]) under minimal fuel — the FIRST emission certificate carrying a GoSem-backed
    execution guarantee.  (Direct from [panic_free_denotable_runs_ret] on the carried proof.) *)
Theorem pfe_runs_ret : forall (c : PanicFreeEmittable) w,
  exists cmd w', denote_program (pfe_program c) = Some cmd /\ run_cmd 1 cmd w = Some (ORet tt w').
Proof.
  intros c w. exact (panic_free_denotable_runs_ret (pfe_program c) w (pfe_panic_free c)).
Qed.

(** A concrete behavioral certificate ([panic_free_prog] = `println("ok"); return`) built + emitted through the
    behavioral path, its run guarantee discharged. *)
Definition pfe_demo : PanicFreeEmittable := mkPanicFreeEmittable panic_free_prog eq_refl.
Example pfe_demo_runs : forall w,
  exists cmd w', denote_program (pfe_program pfe_demo) = Some cmd /\ run_cmd 1 cmd w = Some (ORet tt w').
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
    [panic_free_denotable], (2) its denotation RUNS to [ORet] under minimal fuel — never [OPanic] — for every
    world, and (3) [s] is the BLESSED emission ([emit_panic_free]) of the very cert the gate accepted (emission
    goes through GoEmit's certificate path, not a fork).  So a successful [emit_panic_free_gated] carries the
    behavioral guarantee AND is byte-identical to the blessed path — the honest ancestor of [emit_safe]'s
    soundness (still no theorem to REAL Go — gap #10). *)
Theorem emit_panic_free_gated_sound : forall p s,
  emit_panic_free_gated p = Some s ->
  panic_free_denotable p = true
  /\ (forall w, exists cmd w', denote_program p = Some cmd /\ run_cmd 1 cmd w = Some (ORet tt w'))
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

(** PUBLIC SURFACE — the module's panic-free safety results bundled into ONE constant, so a SINGLE
    [Print Assumptions] covers all their transitive cones (the Docker manifest gate FAILS on any axiom; rule 3).
    Adding a panic_free_* theorem to the certified surface = adding it HERE (else it is an internal helper,
    not advertised zero-axiom). *)
Definition gosem_panic_free_surface :=
  (panic_free_runs_ret, panic_free_runs_ret_output, run_cmd_panics_world, panic_free_runs_ret_ustep,
   panic_free_denotable_runs_ret_output, panic_free_denotable_runs_ret, panic_free_denotable_runs_ret_ustep,
   panic_free_denotable_supported, pfe_runs_ret, emit_panic_free_via_blessed,
   panic_free_gate_sound, panic_free_gate_complete, emit_panic_free_gated_some, emit_panic_free_gated_sound).
Print Assumptions gosem_panic_free_surface.
