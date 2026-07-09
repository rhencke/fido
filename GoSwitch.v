(** ==================================================================================================
    GoSwitch — Go's dispatch constructs over the model: TYPE assertions ([type_assert] — panics on
    mismatch — and the safe comma-ok [type_assert_safe]) with their read-after-assert theorems,
    the TYPE switch family ([type_switch2]/[type_switch3] + the or-case forms) dispatching on a
    [GoAny]'s tag, and the EXPRESSION switches on an [int64] ([int_switch2]/[int_switch3]) and a
    [string] ([str_switch2]/[str_switch3]) scrutinee — ONE module for every switch/assert
    combinator the plugin lowers to native Go [switch]/[x.(T)].  Mined out of the frozen
    builtins.v monolith (plans/builtins-split.md).
    ================================================================================================ *)

Require Import Coq.Strings.String.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoPanic.
From Fido Require Import GoString.

(** [type_assert tag v] (Go spec "Type assertions") asserts that [v : GoAny] holds
    a value of Go type [T].  Panics (like Go's [v.(T)]) if the runtime type does not
    match.

    ESCAPE HATCH: the raw panicking form, safe only inside [catch] or when the
    runtime type is already known.  Prefer [type_assert_safe] (below), the
    safe-by-construction default.

    The tagged [GoAny] carries the value's runtime [GoTypeTag], so [tag_coerce]
    checks it against the target [tag] and recovers the value when they agree; a
    mismatch PANICS, exactly Go's [v.(T)].  Lowered by NAME to [v.(T)] (body
    suppressed). *)
Definition type_assert {T : Type} (tag : GoTypeTag T) (a : GoAny) : IO T :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce tag atag x with
      | Some t => ret t
      | None   => panic rt_assert_fail   (* runtime-type mismatch: Go panics *)
      end
  end.

(** Read-after-assert: asserting [anyt tag x] to its OWN tag returns [x] — a THEOREM,
    from [tag_coerce_refl]. *)
Theorem type_assert_ok : forall {T} (tag : GoTypeTag T) (x : T),
  type_assert tag (anyt tag x) = ret x.
Proof. intros T tag x. unfold type_assert. rewrite tag_coerce_refl. reflexivity. Qed.

(** Safe checked assertion (the safe-by-construction default for [GoAny]).
    [type_assert_safe tag a (fun v ok => body)] lowers to Go's native
    two-value form [v, ok := a.(T); body]: when the runtime tag matches [T], [ok =
    true] and [v] is the value; otherwise [ok = false] and [v = zero_val tag].
    Because the caller must handle [ok = false], it cannot panic.  CPS like [recv_ok]. *)
Definition type_assert_safe {T B : Type}
  (tag : GoTypeTag T) (a : GoAny) (k : T -> bool -> IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce tag atag x with
      | Some t => k t true
      | None   => k (zero_val tag) false
      end
  end.

(** Build-checked: a WRONG-type assertion does NOT silently return the value — the
    coercion is [None], so the result is a panic / [ok = false], never [ret x]. *)
Example type_assert_safe_ok : forall {B} (x : GoInt) (k : GoInt -> bool -> IO B),
  type_assert_safe TInt64 (anyt TInt64 x) k = k x true.
Proof. intros B x k. unfold type_assert_safe. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_assert_safe_mismatch : forall {B} (x : GoInt) (k : bool -> bool -> IO B),
  type_assert_safe TBool (anyt TInt64 x) k = k false false.
Proof. intros B x k. reflexivity. Qed.

(** ---- Type switch ----  (Go spec: "Type switches")

    Go's [switch v := x.(type) { case T1: …; case T2: …; default: … }] dispatches on
    the RUNTIME type of an interface value [x].  We model it on the SAME [tag_coerce]
    machinery as [type_assert_safe] (so it is axiom-free): try each case's tag against
    the value's tag; the first match runs that case's continuation with the recovered,
    correctly-typed value, otherwise the default runs.  Lowers to Go's native type
    switch.  N-ary (>2 cases) is the same shape with more arms. *)
Definition type_switch2 {A1 A2 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (k1 : A1 -> IO B)
  (t2 : GoTypeTag A2) (k2 : A2 -> IO B)
  (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some v1 => k1 v1
      | None =>
          match tag_coerce t2 atag x with
          | Some v2 => k2 v2
          | None => d
          end
      end
  end.

(** Build-checked dispatch: a value tagged [t1] runs the first arm with the recovered
    value (never a wrong arm or the default)… *)
Example type_switch2_first : forall {A1 A2 B} (t1 : GoTypeTag A1) (t2 : GoTypeTag A2)
    (x : A1) (k1 : A1 -> IO B) k2 d,
  type_switch2 (anyt t1 x) t1 k1 t2 k2 d = k1 x.
Proof. intros. unfold type_switch2. rewrite tag_coerce_refl. reflexivity. Qed.

(** …and a value whose type matches NEITHER case falls through to the default — the
    coercions are both [None], so no arm can fire on a type mismatch. *)
Example type_switch2_default : forall {B} (x : GoInt) k1 k2 (d : IO B),
  type_switch2 (anyt TInt64 x) TBool k1 TString k2 d = d.
Proof. intros. reflexivity. Qed.

(** N-ary type switch is the same shape with more arms — here three cases.  (The plugin
    lowers any arity through one generalised arm, so [type_switch4]… would work the same.) *)
Definition type_switch3 {A1 A2 A3 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (k1 : A1 -> IO B)
  (t2 : GoTypeTag A2) (k2 : A2 -> IO B)
  (t3 : GoTypeTag A3) (k3 : A3 -> IO B)
  (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some v1 => k1 v1
      | None =>
          match tag_coerce t2 atag x with
          | Some v2 => k2 v2
          | None =>
              match tag_coerce t3 atag x with
              | Some v3 => k3 v3
              | None => d
              end
          end
      end
  end.

(** Build-checked: the THIRD case fires for an [int64]-tagged value — the first two
    coercions miss (different tags), the third matches and runs [k3] with the value. *)
Example type_switch3_third : forall {B} (x : GoI64) k1 k2 (k3 : GoI64 -> IO B) d,
  type_switch3 (anyt TI64 x) TBool k1 TString k2 TI64 k3 d = k3 x.
Proof. intros. unfold type_switch3. rewrite tag_coerce_refl. reflexivity. Qed.

(** Multi-type case — Go's [case T1, T2:].  A single case matching EITHER of two types;
    in Go the bound value is NOT narrowed (it keeps the interface type), so the body
    commonly ignores it — we model it as a thunk [k : IO B] (no value binder), run when
    the value's type is [t1] OR [t2].  Same [tag_coerce] basis (axiom-free); lowers to
    Go's [case T1, T2:]. *)
Definition type_switch_or2 {A1 A2 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (t2 : GoTypeTag A2) (k : IO B) (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some _ => k
      | None => match tag_coerce t2 atag x with Some _ => k | None => d end
      end
  end.

(** Build-checked: the multi-type case fires for EITHER tag (here the first and the
    second), and a value matching neither falls through to the default. *)
Example type_switch_or2_first : forall {A1 A2 B} (t1 : GoTypeTag A1) (t2 : GoTypeTag A2)
    (x : A1) (k d : IO B), type_switch_or2 (anyt t1 x) t1 t2 k d = k.
Proof. intros. unfold type_switch_or2. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or2_second : forall {B} (x : GoString) (k d : IO B),
  type_switch_or2 (anyt TString x) TBool TString k d = k.
Proof. intros. unfold type_switch_or2. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or2_default : forall {B} (x : GoInt) (k d : IO B),
  type_switch_or2 (anyt TInt64 x) TBool TString k d = d.
Proof. intros. reflexivity. Qed.

(** N-type multi-case — three types here (Go's [case T1, T2, T3:]); same shape as
    [type_switch_or2], one more tag.  The plugin lowers any arity through one generalised
    arm. *)
Definition type_switch_or3 {A1 A2 A3 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (t2 : GoTypeTag A2) (t3 : GoTypeTag A3) (k : IO B) (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some _ => k
      | None => match tag_coerce t2 atag x with
                | Some _ => k
                | None => match tag_coerce t3 atag x with Some _ => k | None => d end
                end
      end
  end.
Example type_switch_or3_third : forall {B} (x : GoI64) (k d : IO B),
  type_switch_or3 (anyt TI64 x) TBool TString TI64 k d = k.
Proof. intros. unfold type_switch_or3. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or3_default : forall {B} (x : GoInt) (k d : IO B),
  type_switch_or3 (anyt TInt64 x) TBool TString TFloat64 k d = d.
Proof. intros. reflexivity. Qed.

(** Native EXPRESSION switch — Go's [switch x { case v1: …; case v2: …; default: … }]
    on an int64 scrutinee.  Semantically an equality if-chain (faithful: Go's expression
    switch compares the scrutinee to each case value with [==], first match wins) but
    lowered to the native Go [switch].  Axiom-free (built on [i64_eqb]); N-ary is the same
    shape (the plugin arm is generalised over the (value, body) pairs).

    DISTINCT CASES (Go rejects duplicate CONSTANT cases): each combinator demands a proof
    that its case VALUES are pairwise distinct ([i64_neqb]/[str_neqb]).  Because the equality
    is decided in Rocq, ANY constant case expression — a literal or a folded arithmetic
    constant like [i64_add v1 v2] — is compared by its VALUE, so a duplicate-case switch is
    UNREPRESENTABLE (no rendered-text / trusted-rendering dependency, and constant folding is
    the model's own [i64_eqb]).  A NON-constant case value cannot discharge the obligation, so
    only distinct-constant switches are representable — a proved restriction, not a fail-open. *)
Definition int_switch2 {B : Type} (x : GoI64)
  (v1 : GoI64) (k1 : IO B)
  (v2 : GoI64) (k2 : IO B)
  (Hd : i64_neqb v1 v2 = true)
  (d : IO B) : IO B :=
  if i64_eqb x v1 then k1
  else if i64_eqb x v2 then k2
  else d.

(** Build-checked dispatch: the scrutinee selects the first matching case, else default. *)
Example int_switch2_first : forall {B} (k1 k2 d : IO B),
  int_switch2 (1)%i64 (1)%i64 k1 (2)%i64 k2 eq_refl d = k1.
Proof. reflexivity. Qed.
Example int_switch2_second : forall {B} (k1 k2 d : IO B),
  int_switch2 (2)%i64 (1)%i64 k1 (2)%i64 k2 eq_refl d = k2.
Proof. reflexivity. Qed.
Example int_switch2_default : forall {B} (k1 k2 d : IO B),
  int_switch2 (9)%i64 (1)%i64 k1 (2)%i64 k2 eq_refl d = d.
Proof. reflexivity. Qed.
(** The distinctness predicates are IRREFLEXIVE — a value is never distinct from itself.  A WEAKENED
    [i64_neqb]/[str_neqb] (e.g. a constant [true]) makes these unprovable, so the build dies. *)
Lemma i64_neqb_irrefl : forall v, i64_neqb v v = false.
Proof. intro v. unfold i64_neqb. now rewrite (proj2 (i64_eqb_spec v v) (eq_refl v)). Qed.
Lemma str_neqb_irrefl : forall v, str_neqb v v = false.
Proof. intro v. unfold str_neqb. now rewrite (proj2 (str_eqb_spec v v) (eq_refl v)). Qed.

(** SEAL WITNESS (coqc-checked, non-spoofable): applying [int_switch2] to EQUAL cases [(v, v)]
    demands its obligation for [(v, v)]; that obligation IS [i64_neqb v v = true], which
    [i64_neqb_irrefl] proves FALSE — so the hypothesis is contradictory and [int_switch2] provably
    CANNOT be applied to a duplicate case.  A weakened OBLIGATION rejects the coupling and a weakened
    [i64_neqb] breaks [i64_neqb_irrefl]; either way this fails to compile.  Judges the OBSERVABLE
    duplicate-rejection, not just the obligation shape.  The ownership gate requires this witness
    (which applies [int_switch2]) for every recognized combinator. *)
Lemma int_switch2_rejects_dup : forall {B} (v : GoI64) (k1 k2 d : IO B) (Hd : i64_neqb v v = true),
  int_switch2 (0)%i64 v k1 v k2 Hd d = d -> False.
Proof. intros B v k1 k2 d Hd _. rewrite i64_neqb_irrefl in Hd. discriminate Hd. Qed.

(** N-ary expression switch — three cases here; same generalised plugin arm as
    [int_switch2] (it takes any number of (value, body) pairs). *)
Definition int_switch3 {B : Type} (x : GoI64)
  (v1 : GoI64) (k1 : IO B)
  (v2 : GoI64) (k2 : IO B)
  (v3 : GoI64) (k3 : IO B)
  (Hd : (i64_neqb v1 v2 && i64_neqb v1 v3 && i64_neqb v2 v3)%bool = true)
  (d : IO B) : IO B :=
  if i64_eqb x v1 then k1
  else if i64_eqb x v2 then k2
  else if i64_eqb x v3 then k3
  else d.
Example int_switch3_third : forall {B} (k1 k2 k3 d : IO B),
  int_switch3 (3)%i64 (1)%i64 k1 (2)%i64 k2 (3)%i64 k3 eq_refl d = k3.
Proof. reflexivity. Qed.
Example int_switch3_default : forall {B} (k1 k2 k3 d : IO B),
  int_switch3 (9)%i64 (1)%i64 k1 (2)%i64 k2 (3)%i64 k3 eq_refl d = d.
Proof. reflexivity. Qed.
(** SEAL WITNESS for [int_switch3] — see [int_switch2_rejects_dup]: applying [int_switch3] to cases
    [(v, v, v3)] (a duplicate) demands a contradictory obligation ([i64_neqb v v] is false). *)
Lemma int_switch3_rejects_dup : forall {B} (v v3 : GoI64) (k1 k2 k3 d : IO B)
  (Hd : (i64_neqb v v && i64_neqb v v3 && i64_neqb v v3)%bool = true),
  int_switch3 (0)%i64 v k1 v k2 v3 k3 Hd d = d -> False.
Proof. intros B v v3 k1 k2 k3 d Hd _. rewrite i64_neqb_irrefl in Hd. cbn in Hd. discriminate Hd. Qed.

(** Expression switch on a STRING scrutinee — Go's [switch s { case "a": …; default: … }].
    Same shape as [int_switch2] but the equality is [str_eqb] (byte equality); the plugin
    arm is SHARED (it emits the scrutinee and each case value verbatim, Go doing the [==]),
    so int64 and string scrutinees lower identically. *)
Definition str_switch2 {B : Type} (x : GoString)
  (v1 : GoString) (k1 : IO B)
  (v2 : GoString) (k2 : IO B)
  (Hd : str_neqb v1 v2 = true)
  (d : IO B) : IO B :=
  if str_eqb x v1 then k1
  else if str_eqb x v2 then k2
  else d.

Example str_switch2_first : forall {B} (k1 k2 d : IO B),
  str_switch2 "a"%string "a"%string k1 "b"%string k2 eq_refl d = k1.
Proof. reflexivity. Qed.
Example str_switch2_second : forall {B} (k1 k2 d : IO B),
  str_switch2 "b"%string "a"%string k1 "b"%string k2 eq_refl d = k2.
Proof. reflexivity. Qed.
Example str_switch2_default : forall {B} (k1 k2 d : IO B),
  str_switch2 "z"%string "a"%string k1 "b"%string k2 eq_refl d = d.
Proof. reflexivity. Qed.
(** SEAL WITNESS for [str_switch2] — see [int_switch2_rejects_dup] (Go compares string cases by
    value; [str_neqb_irrefl] is the byte-equality analogue, no escaping dependency). *)
Lemma str_switch2_rejects_dup : forall {B} (v : GoString) (k1 k2 d : IO B) (Hd : str_neqb v v = true),
  str_switch2 ""%string v k1 v k2 Hd d = d -> False.
Proof. intros B v k1 k2 d Hd _. rewrite str_neqb_irrefl in Hd. discriminate Hd. Qed.

(** N-ary string expression switch (3 cases) — same generalised plugin arm as
    [str_switch2]/[int_switch2]; completes the >2-case coverage for both scrutinee types. *)
Definition str_switch3 {B : Type} (x : GoString)
  (v1 : GoString) (k1 : IO B)
  (v2 : GoString) (k2 : IO B)
  (v3 : GoString) (k3 : IO B)
  (Hd : (str_neqb v1 v2 && str_neqb v1 v3 && str_neqb v2 v3)%bool = true)
  (d : IO B) : IO B :=
  if str_eqb x v1 then k1
  else if str_eqb x v2 then k2
  else if str_eqb x v3 then k3
  else d.
Example str_switch3_third : forall {B} (k1 k2 k3 d : IO B),
  str_switch3 "c"%string "a"%string k1 "b"%string k2 "c"%string k3 eq_refl d = k3.
Proof. reflexivity. Qed.
Example str_switch3_default : forall {B} (k1 k2 k3 d : IO B),
  str_switch3 "z"%string "a"%string k1 "b"%string k2 "c"%string k3 eq_refl d = d.
Proof. reflexivity. Qed.
(** SEAL WITNESS for [str_switch3] — see [int_switch2_rejects_dup]. *)
Lemma str_switch3_rejects_dup : forall {B} (v v3 : GoString) (k1 k2 k3 d : IO B)
  (Hd : (str_neqb v v && str_neqb v v3 && str_neqb v v3)%bool = true),
  str_switch3 ""%string v k1 v k2 v3 k3 Hd d = d -> False.
Proof. intros B v v3 k1 k2 k3 d Hd _. rewrite str_neqb_irrefl in Hd. cbn in Hd. discriminate Hd. Qed.

(** GATED SURFACE: the value-switch seal is PROOF AUTHORITY (it is what makes a duplicate-case
    expression switch unrepresentable), so its trust base is manifest-gated ZERO-AXIOM — the
    [*_rejects_dup] lemmas and the [*_neqb_irrefl] they rest on.  A NEW axiom reaching any of these
    fails the axiom-manifest gate (rule 3). *)
Definition value_switch_seal_surface :=
  (@int_switch2_rejects_dup, @int_switch3_rejects_dup,
   @str_switch2_rejects_dup, @str_switch3_rejects_dup,
   @i64_neqb_irrefl, @str_neqb_irrefl).
Print Assumptions value_switch_seal_surface.
