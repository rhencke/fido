(** GoSemSafe.v — the FIRST behavioral-safety property over GoSem's denotation (proof-only, no Go).

    ⚠ This is NOT the [BehaviorSafe] gate, and it does NOT yet gate emission.  The charter's behavioral-safety
    TARGET (no nil-deref / OOB / send-on-closed / data race / …) concerns Go constructs the slice-1 fragment does
    NOT denote (no pointers / slices / channels reach [denote_program] yet).  In THAT fragment the ONLY unsafe
    runtime behavior is an explicit [panic], so the fragment-appropriate first "safe by construction" theorem is:
    a SYNTACTICALLY panic-free supported program provably NEVER panics at runtime ([run_cmd] yields [ORet], never
    [OPanic]).  It is the SEED of [BehaviorSafe] — the exact shape (a syntactic property ⟹ a runtime-safety
    guarantee) the eventual gate will have — kept in its own module so GoSem.v does not grow.

    Naming discipline (rule: a name is a correctness claim): this is [panic_free_runs_ret], a SPECIFIC property,
    NOT [BehaviorSafe] / [SafeProgram]. *)

From Fido Require Import preamble cmd GoAst GoTypes GoSafe GoSem cmd_unified unified GoSemUnified.
From Stdlib Require Import String List Bool.
Import ListNotations.

(** A statement is the panic primitive [panic(e)] — the only [denote_stmt] arm that yields a [CPan]. *)
Definition stmt_is_panic (s : GoStmt) : bool :=
  match s with
  | GsExprStmt (ECall (EId f) _) => String.eqb (proj1_sig f) "panic"
  | _ => false
  end.
Definition panic_free (b : list GoStmt) : bool := forallb (fun s => negb (stmt_is_panic s)) b.

(** A command with no [CPan] node — it cannot end in a panic Outcome. *)
Fixpoint cmd_no_panic (c : Cmd unit) : bool :=
  match c with
  | CRet _      => true
  | COut _ _ c' => cmd_no_panic c'
  | CPan _      => false
  | CDfr d c'   => cmd_no_panic d && cmd_no_panic c'
  end.

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
  intros s c term H Hnp. destruct s as [e | | ev | be]; cbn [denote_stmt] in H.
  - destruct (expr_stmt_ok e); [|discriminate H].
    destruct e as [ | | | | | | | fe fargs | | | | | | ]; try discriminate H.
    destruct fe as [ fi | | | | | | | | | | | | | ]; try discriminate H.
    cbn [stmt_is_panic] in Hnp. rewrite Hnp in H.
    destruct (eval_args fargs); [|discriminate H]. inversion H; subst. reflexivity.
  - inversion H; subst; reflexivity.
  - discriminate H.
  - destruct (svalue be); [|discriminate H]. destruct (eval_value be); [|discriminate H].
    inversion H; subst; reflexivity.
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

(** A [CPan]-free, defer-free command runs (via [go]) to an [ORet] — never an [OPanic]. *)
Lemma go_no_panic : forall c w,
  cmd_no_panic c = true -> no_defer c = true -> exists w', go c w = (ORet tt w', nil).
Proof.
  intro c; induction c as [a | b xs c' IH | v | d c' IH] using Cmd_rect';
    intros w Hnp Hnd; cbn [go cmd_no_panic no_defer] in *.
  - destruct a. exists w. reflexivity.
  - destruct (IH (w_log b xs w) Hnp Hnd) as [w' Hgo]. exists w'. exact Hgo.
  - discriminate Hnp.
  - discriminate Hnd.
Qed.

Lemma run_cmd_no_panic : forall c w,
  cmd_no_panic c = true -> no_defer c = true -> exists w', run_cmd 1 c w = Some (ORet tt w').
Proof.
  intros c w Hnp Hnd. destruct (go_no_panic c w Hnp Hnd) as [w' Hgo].
  exists w'. unfold run_cmd. rewrite Hgo. reflexivity.
Qed.

(** THE first behavioral-safety result: a panic-free supported program that DENOTES runs to an [ORet] —
    it provably NEVER panics at runtime.  ([no_defer] discharged via [denote_body_no_defer].) *)
Theorem panic_free_runs_ret : forall p c w,
  denote_program p = Some c -> panic_free (prog_body p) = true ->
  exists w', run_cmd 1 c w = Some (ORet tt w').
Proof.
  intros p c w Hden Hpf. unfold denote_program in Hden.
  destruct (String.eqb (proj1_sig (prog_pkg p)) "main") eqn:E; [|discriminate Hden].
  apply run_cmd_no_panic.
  - exact (denote_body_no_panic (prog_body p) c Hden Hpf).
  - exact (denote_body_no_defer (prog_body p) c Hden).
Qed.

(** Boundary demos: a panic-free program runs to [ORet]; a program that DOES panic runs to [OPanic] (the
    property is exactly about the [panic] primitive, not vacuous). *)
Definition safe_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "ok"]); GsReturn].
Example safe_prog_runs_ret : forall w,
  match denote_program safe_prog with Some c => run_cmd 1 c w | None => None end
  = Some (ORet tt (w_log true (anyt TString "ok" :: nil) w)).
Proof. intro w. vm_compute. reflexivity. Qed.

Definition panicking_prog : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EStr "boom"])].
Example panicking_prog_panics : forall w,
  match denote_program panicking_prog with Some c => run_cmd 1 c w | None => None end
  = Some (OPanic (anyt TString "boom") w).
Proof. intro w. vm_compute. reflexivity. Qed.

(** ★ The panic-freedom guarantee reaches the OPERATIONAL semantics.  Composing [panic_free_runs_ret] (the
    denoted program's authoritative [run_cmd] reaches [ORet]) with the cmd↔unified bridge
    [GoSemUnified.denote_program_run_agrees] (the [unified.v] [ustep] run AGREES with the deterministic
    [run_cmd]): a syntactically panic-free supported program, once denoted, runs under [ustep] — the calculus
    [unified.v]'s race-freedom / liveness are proved on — to COMPLETION ([uc_live 0 = false]) with NO panic
    ([uc_panic 0 = None]), its output equal to the safe run's.  cmd.v's [run_cmd] STAYS the authority: the
    conclusion CARRIES [run_cmd 1 c w = Some (ORet tt w')] and ties [uc_out] to that [w'] (not a free observer).
    So the seed safety PROPERTY is not merely denotational; it holds where the concurrency theory lives.  (Still
    a PROPERTY, NOT an emission gate.) *)
Theorem panic_free_runs_ret_ustep : forall p c ucap w,
  denote_program p = Some c -> panic_free (prog_body p) = true ->
  exists (uc : UConfig) (w' : World),
    run_cmd 1 c w = Some (ORet tt w')                       (* cmd.v's AUTHORITATIVE safe run — grounds [w'] *)
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

(** Trust surface for this module (axiom-manifest gate captures these [Print Assumptions]). *)
Print Assumptions panic_free_runs_ret.
Print Assumptions panic_free_runs_ret_ustep.
