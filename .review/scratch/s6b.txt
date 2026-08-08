(* ── §3 Scope construction and name resolution ────────────────────────────── *)
(* Source observations on object-establishing binders. *)
Parameter establisher_scope : forall {p}, ObjectEstablisher p -> ScopeId p.
Parameter establisher_context : forall {p}, ObjectEstablisher p -> DeclContext.
Parameter establisher_position : forall {p}, ObjectEstablisher p -> nat.
Parameter establisher_identifier_position : forall {p}, ObjectEstablisher p -> nat.
Parameter establisher_spec_end : forall {p}, ObjectEstablisher p -> nat.
Parameter establisher_statement_end : forall {p}, ObjectEstablisher p -> nat.

Parameter name_use_scope : forall {p}, NameUseRef p -> ScopeId p.
Parameter name_use_spelling : forall {p}, NameUseRef p -> string.
Parameter name_use_position : forall {p}, NameUseRef p -> nat.

Definition establisher_start {p} (b : ObjectEstablisher p) : ScopeStart :=
  scope_start (establisher_context b).

Definition establisher_visible_from {p} (b : ObjectEstablisher p) : nat :=
  match establisher_start b with
  | StartWholePackage | StartOutermost => 0
  | StartAtOwnIdentifier => establisher_identifier_position b
  | StartAfterSpec       => establisher_spec_end b
  | StartAfterStatement  => establisher_statement_end b
  end.

Definition VisibleAt {p} (b : ObjectEstablisher p) (u : NameUseRef p) : Prop :=
  Encloses (establisher_scope b) (name_use_scope u) /\
  (establisher_visible_from b <= name_use_position u)%nat.

Definition ScopeCloser {p} (inner outer : ScopeId p) : Prop :=
  inner <> outer /\ Encloses outer inner.

(* §3.3 A scope map indexes object-establishing binders, not all named LHS occurrences.  A short reuse
   appears in the LHS but inserts nothing into the map.  Two same-spelling object-establishing binders in
   one scope are a duplicate failure. *)
Parameter ScopeBindings : forall {p} {i : Input p}, Phase i -> ScopeId p -> Type.
Parameter scope_lookup : forall {p} {i : Input p} {ph : Phase i} {sc : ScopeId p},
  ScopeBindings ph sc -> string -> option (ObjectEstablisher p).

Definition DuplicateEstablishers {p} (earlier later : ObjectEstablisher p) : Prop :=
  establisher_spelling earlier = establisher_spelling later /\
  establisher_scope earlier = establisher_scope later /\
  (establisher_position earlier < establisher_position later)%nat.

Inductive ScopeBuildOutcome {p} {i : Input p} (ph : Phase i) (sc : ScopeId p) : Type :=
| ScopeReady  : ScopeBindings ph sc -> ScopeBuildOutcome ph sc
| ScopeFailed : forall earlier later : ObjectEstablisher p,
    DuplicateEstablishers earlier later -> establisher_scope later = sc ->
    ScopeBuildOutcome ph sc.

Parameter scope_build : forall {p} {i : Input p} (ph : Phase i) (sc : ScopeId p),
  ScopeBuildOutcome ph sc.

(* §3.4 Resolution consumes only successful scope maps.  `x := 1; x, y := 2, 3` is representable because
   the second `x` is a reuse, not an object-establishing binder, so it never enters the map and no
   duplicate is detected. *)
Inductive Resolves {p} {i : Input p} (ph : Phase i) : NameUseRef p -> ObjectRef ph -> Prop :=
| ResolvesSource : forall (u : NameUseRef p) (sc : ScopeId p) (m : ScopeBindings ph sc)
    (b : ObjectEstablisher p),
    Encloses sc (name_use_scope u) ->
    scope_build ph sc = ScopeReady ph sc m ->
    scope_lookup m (name_use_spelling u) = Some b ->
    VisibleAt b u ->
    (forall (sc' : ScopeId p) (m' : ScopeBindings ph sc') (b' : ObjectEstablisher p),
       ScopeCloser sc' sc -> Encloses sc' (name_use_scope u) ->
       scope_build ph sc' = ScopeReady ph sc' m' ->
       scope_lookup m' (name_use_spelling u) = Some b' -> ~ VisibleAt b' u) ->
    Resolves ph u (source_object ph (establisher_site b))
| ResolvesPredeclared : forall (u : NameUseRef p) (n : PredeclaredName),
    predeclared_spelling n = name_use_spelling u ->
    (forall (sc : ScopeId p) (m : ScopeBindings ph sc) (b : ObjectEstablisher p),
       Encloses sc (name_use_scope u) ->
       scope_build ph sc = ScopeReady ph sc m ->
       scope_lookup m (name_use_spelling u) = Some b -> ~ VisibleAt b u) ->
    Resolves ph u (predeclared_object ph n).

Parameter resolve_name : forall {p} {i : Input p} (ph : Phase i),
  NameUseRef p -> option (ObjectRef ph).

Record BindingFact {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) : Type := MakeBinding {
  bound_object   : ObjectRef ph;
  bound_resolves : Resolves ph u bound_object
}.

(* §3.3 Binder facts indexed by the exact BindingNameRef.  Blank establishes nothing.  A regular binder
   mints the exact object of its own establisher.  A short new mints after proving no existing same-block
   variable with the same spelling is visible.  A short reuse returns the exact earlier same-block
   static variable; it establishes no new object. *)
Inductive BinderFact {p} {i : Input p} (ph : Phase i) : BindingNameRef p -> Type :=
| BFBlank : forall (k : BlankRef p),
    BinderFact ph (blank_binding_name k)
| BFRegularNew : forall (est : ObjectEstablisher p) (c : DeclContext),
    BinderFact ph (establisher_binding_name est)
| BFShortNew : forall (n : BindingNameRef p) (d : ShortDeclRef p) (sp : string)
    (est : ObjectEstablisher p),
    short_lhs_decl n = Some d -> short_lhs_spelling n = sp ->
    (forall (e : ObjectEstablisher p),
       establisher_spelling e = sp ->
       establisher_scope e = establisher_scope est ->
       (establisher_position e < establisher_position est)%nat -> False) ->
    BinderFact ph n
(* The static-variable evidence lives in the Facts layer; here we retain the exact causal predecessor
   without the full `StaticVariable` record, which depends on type resolution. *)
| BFShortReuse : forall (n : BindingNameRef p) (d : ShortDeclRef p) (sp : string)
    (earlier : ObjectEstablisher p) (o : ObjectRef ph),
    short_lhs_decl n = Some d -> short_lhs_spelling n = sp ->
    establisher_spelling earlier = sp ->
    establisher_scope earlier = short_lhs_scope n ->
    (establisher_position earlier < short_lhs_position n)%nat ->
    source_object ph (establisher_site earlier) = o ->
    BinderFact ph n.

Parameter binder_fact : forall {p} {i : Input p} (ph : Phase i) (n : BindingNameRef p),
  BinderFact ph n.

Definition binder_object {p} {i : Input p} {ph : Phase i} {n}
  (bf : BinderFact ph n) : option (ObjectRef ph) :=
  match bf with
  | BFBlank _ _ => None
  | BFRegularNew _ est _ => Some (source_object ph (establisher_site est))
  | BFShortNew _ _ _ _ est _ _ _ => Some (source_object ph (establisher_site est))
  | BFShortReuse _ _ _ _ _ o _ _ _ _ _ _ => Some o
  end.
