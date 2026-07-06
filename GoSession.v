(** ==================================================================================================
    GoSession — session types over the model: [Proto] (typed send/recv protocol) + [dual] and its
    laws, and the LINEAR session layer [Sess i j A] — a forge-proof indexed monad whose only
    builders are the disciplined ops ([sret]/[sbind]/[ssend]/[srecv]/[slift]), so double-use,
    wrong order/direction/payload, and incomplete protocols are Rocq TYPE ERRORS.  [run_session]
    has NO sequential [run_io] meaning (a session run is concurrent) — its model body is a LOUD
    panic; the faithful semantics is the session calculus in concurrency.v, and the plugin lowers
    the ops BY NAME to channel-passing Go.  Mined out of the frozen builtins.v monolith
    (plans/builtins-split.md).
    ================================================================================================ *)

Require Import Coq.Strings.String.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.

(** ---- Session types ----

    [Proto] encodes a typed communication protocol as a sequence of sends
    and receives.  [dual P] flips every send↔recv, giving the complementary
    protocol for the other participant.

    [SessEndpoint P] is a channel endpoint whose *remaining* protocol is [P].
    At runtime both endpoints of a session are the same [chan any]; all type
    discipline is enforced by Rocq's type-checker at zero runtime cost.

    The key guarantee: [sess_send] only type-checks when the endpoint has
    type [SessEndpoint (PSend A P)], and [sess_recv] only when it has type
    [SessEndpoint (PRecv A P)].  Misuse (wrong order, wrong direction) is a
    Rocq compile-time error — no runtime check required. *)

Inductive Proto : Type :=
  | PSend : Type -> Proto -> Proto   (** send a value of type A, continue as P *)
  | PRecv : Type -> Proto -> Proto   (** recv a value of type A, continue as P *)
  | PEnd  : Proto.                   (** protocol complete *)

Fixpoint dual (p : Proto) : Proto :=
  match p with
  | PSend A p' => PRecv A (dual p')
  | PRecv A p' => PSend A (dual p')
  | PEnd       => PEnd
  end.

Lemma dual_involutive : forall p, dual (dual p) = p.
Proof.
  induction p as [A p' IH | A p' IH |].
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - reflexivity.
Qed.

(** Taking the dual is injective: a protocol is determined by its dual.
    Follows directly from involutivity. *)
Lemma dual_injective : forall p q, dual p = dual q -> p = q.
Proof.
  intros p q H.
  rewrite <- (dual_involutive p), <- (dual_involutive q), H.
  reflexivity.
Qed.

(** Number of communication steps in a protocol. *)
Fixpoint proto_len (p : Proto) : nat :=
  match p with
  | PSend _ p' => S (proto_len p')
  | PRecv _ p' => S (proto_len p')
  | PEnd       => O
  end.

(** Client and server perform the same number of steps: every send on one
    end is matched by a receive on the other, so the protocols have equal
    length.  This is the structural heart of the "both ends agree" guarantee. *)
Lemma dual_preserves_len : forall p, proto_len (dual p) = proto_len p.
Proof.
  induction p as [A p' IH | A p' IH |]; simpl; auto.
Qed.

(** ---- Linear sessions via an indexed monad ----

    Rocq is not substructural, so an endpoint-VALUE API cannot enforce LINEARITY
    (the original endpoint stays in scope, so a double-send would type-check).
    This indexed (parameterised) monad puts the protocol state in
    the TYPE INDEX, not in a reusable value.  [Sess i j A] is a session fragment
    that advances the protocol from state [i] to state [j], yielding [A].  There
    is no endpoint value to reuse; operations consume the head step of the index
    and [sbind] threads the state; and a *runnable* session must thread from the
    full protocol [P] all the way to [PEnd] ([Sess P PEnd unit]).  Hence
    double-use, wrong order/direction/payload, AND incomplete protocols are all
    Rocq TYPE ERRORS (see the [Fail] tests in main.v). *)

(** [Sess i j A] is the FORGE-PROOF session type: an INDUCTIVE
    whose only builders are the disciplined ops below.  There is NO [MkSess]-style
    constructor wrapping an arbitrary [IO A] at any index, so the protocol index
    CANNOT be detached from the operations — a forged "[… : Sess (PSend A P) P unit]
    that sends nothing" is UNTYPABLE (see the [Fail] tests in main.v).  The indices
    are rigid inductive indices (not a convertible [IO A] alias), so double-use,
    wrong order / direction / payload, AND incomplete protocols ([j <> PEnd]) are
    all TYPE ERRORS.  [Sess] erases in extraction — lowered by OPERATION NAME
    (channel passing), never materialised as a Go value.  Its full safety+liveness
    theory is in concurrency.v (soundness, communication safety, deadlock-freedom,
    termination / determinism, run-trace coherence) — proved DIRECTLY about THIS
    type ([PSess]/[PS…] there are aliases for [Sess]/[S…]). *)
Inductive Sess : Proto -> Proto -> Type -> Type :=
  | SRet  : forall {P : Proto} {A : Type}, A -> Sess P P A
  | SSend : forall {A : Type} {P : Proto}, A -> Sess (PSend A P) P unit
  | SRecv : forall {A : Type} {P : Proto}, GoTypeTag A -> Sess (PRecv A P) P A
  | SLift : forall {P : Proto} {A : Type}, IO A -> Sess P P A
  | SBind : forall {P Q R : Proto} {A B : Type},
              Sess P Q A -> (A -> Sess Q R B) -> Sess P R B.

(** Pure value; protocol state unchanged.  Lowers like [ret]. *)
Definition sret {P : Proto} {A : Type} (x : A) : Sess P P A := SRet x.

(** Sequence: [m] advances [i→j], then [k a] advances [j→k].  Lowers like
    [bind] (sequential Go statements). *)
Definition sbind {P Q R : Proto} {A B : Type}
  (m : Sess P Q A) (k : A -> Sess Q R B) : Sess P R B := SBind m k.

(** Send: consumes the head [PSend A] step.  No endpoint argument — the channel
    is implicit, supplied by the enclosing [run_session].
    Lowers to [_sess_ch <- any(v)]. *)
Definition ssend {A : Type} {P : Proto} (v : A) : Sess (PSend A P) P unit := SSend v.

(** Receive: consumes the head [PRecv A] step, yielding the received value.
    Lowers to [_r := <-_sess_ch; _r.(T)]. *)
Definition srecv {A : Type} {P : Proto} (tag : GoTypeTag A) : Sess (PRecv A P) P A := SRecv tag.

(** Lift an [IO] action into a session at any protocol state (consumes no
    protocol step) — e.g. to print a received value.  Lowers to the IO body. *)
Definition slift {P : Proto} {A : Type} (m : IO A) : Sess P P A := SLift m.

(** [sret]…[run_session] are already in main.v's [Extraction NoInline] list, so they
    stay named refs (NOT inlined to their constructors) and the plugin's by-operation-
    name session lowering fires exactly as before — the emitted Go is unchanged. *)

(** Session sequencing notations (the [sbind] analogues of [>>'] / [<-' ;;]):
    [>>>] discards the step's result, [<<- … ;;;] binds it.  Right-associative so
    [a >>> b >>> c] is the natural right-nested [sbind a (fun _ => sbind b …)]
    that the protocol indices and the plugin's session lowering expect. *)
Notation "m >>> k" := (sbind m (fun _ => k))
  (at level 80, right associativity).
Notation "x <<- m ;;; k" := (sbind m (fun x => k))
  (at level 80, m at level 90, right associativity).

(** Run two complementary roles concurrently: the client realises [P] to completion, the server realises
    [dual P].  Like [go_spawn], a session run is CONCURRENT — it spawns the server and runs the client
    against a shared channel — so it has NO sequential [run_io] meaning; the sequential meaning is a
    LOUD panic (any source-level proof that tries to compute a session program's [run_io] hits this
    wall).  The FAITHFUL semantics lives in the session calculus / concurrent transition system;
    extraction is unaffected — the plugin lowers [run_session] BY NAME (in main.v's [Extraction
    NoInline]) to [_sess_ch := make(chan any); go func(){ <server> }(); <client>] (body suppressed),
    so the emitted Go is genuinely concurrent. *)
Definition run_session {P : Proto}
  (client : Sess P PEnd unit) (server : Sess (dual P) PEnd unit) : IO unit :=
  fun w => OPanic (anyt TString "fido: run_session has no sequential run_io meaning — a session run is concurrent (spawns the server); the faithful semantics is the session calculus"%string) w.
