
(* ── §10 Declaration consumption, source-indexed ──────────────────────────── *)

(* The target and RHS sequences belong to the exact source site. *)
Parameter site_targets : forall {p}, ConsumptionSiteRef p -> list (BindingNameRef p).
Parameter site_uses : forall {p}, ConsumptionSiteRef p -> list (ExprUseRef p).

Inductive ConstAtomAt {p} {i : Input p} (ph : Phase i)
  : ResultAtomAt ph -> Prop :=
| CAUntyped : forall c, ConstAtomAt ph (RAUntyped ph c)
| CATyped   : forall t tc, ConstAtomAt ph (RATyped ph t tc).

Inductive AtomFits {p} {i : Input p} (ph : Phase i)
  : ResultAtomAt ph -> SemanticType p -> Prop :=
| FitUntyped : forall c t, Representable ph t c -> AtomFits ph (RAUntyped ph c) t
| FitTyped   : forall (s : SemanticType p) tc t, Assignable s t ->
    AtomFits ph (RATyped ph s tc) t
| FitValue   : forall (s : SemanticType p) t, Assignable s t ->
    AtomFits ph (RAValue ph s) t.

Definition atom_default_type {p} {i : Input p} {ph : Phase i}
  (a : ResultAtomAt ph) : SemanticType p :=
  match a with
  | RAUntyped _ c => default_type (constant_kind c)
  | RATyped _ t _ => t
  | RAValue _ t   => t
  end.

(* §10.1 Const spec fact, indexed by exact ConstSpecRef. *)
Inductive ConstPlan {p} {i : Input p} (ph : Phase i)
  : list (BindingNameRef p) -> list (ExprUseRef p) -> Type :=
| CPNil  : ConstPlan ph [] []
| CPUntyped : forall (n : BindingNameRef p) (rest : list (BindingNameRef p))
    (u : ExprUseRef p) (urest : list (ExprUseRef p)) (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> ConstAtomAt ph a ->
    ConstPlan ph rest urest -> ConstPlan ph (n :: rest) (u :: urest)
| CPTyped : forall (n : BindingNameRef p) (rest : list (BindingNameRef p))
    (u : ExprUseRef p) (urest : list (ExprUseRef p)) (a : ResultAtomAt ph)
    (ty : SemanticType p),
    ResultUseFactAt ph u a -> ConstAtomAt ph a -> AtomFits ph a ty ->
    ConstPlan ph rest urest -> ConstPlan ph (n :: rest) (u :: urest).

(* §10.2 Var spec fact, indexed by exact VarSpecRef. *)
Inductive VarValuesPlan {p} {i : Input p} (ph : Phase i)
  : list (BindingNameRef p) -> list (ExprUseRef p) -> Type :=
| VVNil  : VarValuesPlan ph [] []
| VVInferred : forall (n : BindingNameRef p) (rest : list (BindingNameRef p))
    (u : ExprUseRef p) (urest : list (ExprUseRef p)) (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> VarValuesPlan ph rest urest ->
    VarValuesPlan ph (n :: rest) (u :: urest)
| VVExplicit : forall (n : BindingNameRef p) (rest : list (BindingNameRef p))
    (u : ExprUseRef p) (urest : list (ExprUseRef p)) (a : ResultAtomAt ph)
    (ty : SemanticType p),
    ResultUseFactAt ph u a -> AtomFits ph a ty ->
    VarValuesPlan ph rest urest ->
    VarValuesPlan ph (n :: rest) (u :: urest).

Inductive VarPlan {p} {i : Input p} (ph : Phase i)
  : list (BindingNameRef p) -> list (ExprUseRef p) -> Type :=
(* §11 Type-only retains the exact source type-use binding and resolved type. *)
| VPTypeOnly : forall (targets : list (BindingNameRef p))
    (tu : NameUseRef p) (bf : BindingFact ph tu)
    (tm : TypeMeaning ph (bound_object ph tu bf)),
    VarPlan ph targets []
| VPValues : forall (targets : list (BindingNameRef p)) (uses : list (ExprUseRef p)),
    VarValuesPlan ph targets uses -> VarPlan ph targets uses.

(* §10.3 Short declaration fact, indexed by exact ShortDeclRef.  Each LHS occurrence carries its exact
   binder fact, and at least one nonblank name is new by construction. *)
Inductive ShortEntry {p} {i : Input p} (ph : Phase i)  : Type :=
| SEBlank : forall (k : BlankRef p)
    (u : ExprUseRef p) (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> ShortEntry ph
| SENew : forall (n : BindingNameRef p) (d : ShortDeclRef p) (sp : string) (est : ObjectEstablisher p)
    (u : ExprUseRef p) (a : ResultAtomAt ph) (ty : SemanticType p),
    short_lhs_decl n = Some d -> short_lhs_spelling n = sp ->
    ResultUseFactAt ph u a -> AtomFits ph a ty -> ShortEntry ph
| SEReuse : forall (n : BindingNameRef p) (d : ShortDeclRef p) (sp : string)
    (earlier : ObjectEstablisher p) (o : ObjectRef ph)
    (u : ExprUseRef p) (a : ResultAtomAt ph) (ty : SemanticType p),
    establisher_spelling earlier = sp ->
    source_object ph (establisher_site earlier) = o ->
    StaticVariable ph o ->
    ResultUseFactAt ph u a -> AtomFits ph a ty -> ShortEntry ph.

Definition short_entry_is_new {p} {i : Input p} {ph : Phase i}
  (e : ShortEntry ph) : bool :=
  match e with SENew _ _ _ _ _ _ _ _ _ _ _ _ => true | _ => false end.

Inductive ShortPlan {p} {i : Input p} (ph : Phase i)  : Type :=
| MkShortPlan : forall (entries : list (ShortEntry ph)),
    List.Exists (fun e => short_entry_is_new e = true) entries -> ShortPlan ph.

Definition ConsumptionFact {p} {i : Input p} (ph : Phase i)
  (c : ConsumptionSiteRef p) : Type :=
  match c with
  | ConstSite _ _ => ConstPlan ph (site_targets c) (site_uses c)
  | VarSite _ _   => VarPlan ph (site_targets c) (site_uses c)
  | ShortSite _ _ => ShortPlan ph
  end.

(* §11 Initialization units: one per exact source spec, no blank duplicates. *)
Inductive InitUnit (p : SyntaxProgram) : Type :=
| ConstEvalUnit : ConstSpecRef p -> InitUnit p
| VarInitUnit   : VarSpecRef p -> InitUnit p.

Definition RuntimeInitUnit {p} (u : InitUnit p) : bool :=
  match u with ConstEvalUnit _ _ => false | VarInitUnit _ _ => true end.
