
(* ── §12 Package initialization order ──────────────────────────────────────── *)
(* The nodes are the package's initialization units; the edges are name uses inside them. *)
Parameter package_init_units : forall {p}, PackageRef p -> list (InitUnit p).
Parameter init_unit_uses : forall {p}, InitUnit p -> list (NameUseRef p).
(* A const spec binds several names and a var spec is one atomic evaluation group, so a unit produces a
   list of objects.  A single optional object could not identify them. *)
Parameter init_unit_objects : forall {p} {i : Input p} (ph : Phase i),
  InitUnit p -> list (ObjectRef ph).

(* An edge IS a resolved read: it carries the exact use and the exact binding that produced it, so an edge
   cannot be posted beside the bindings it claims to summarise. *)
Inductive InitEdge {p} {i : Input p} (ph : Phase i) (k : PackageRef p)
  : InitUnit p -> InitUnit p -> Prop :=
| InitReads : forall (from to : InitUnit p) (u : NameUseRef p) (bf : BindingFact ph u),
    List.In from (package_init_units k) ->
    List.In to (package_init_units k) ->
    List.In u (init_unit_uses from) ->
    List.In (bound_object ph u bf) (init_unit_objects ph to) ->
    InitEdge ph k from to.

(* `y` initializes before `x` whenever `x` reads `y`. *)
Definition PrecedesIn {A : Type} (l : list A) (x y : A) : Prop :=
  exists before mid after, l = before ++ x :: mid ++ y :: after.

(* The ordered outcome carries its own correctness: covering, duplicate-freedom and edge respect are
   fields, not separate theorems that could be stated about a different order. *)
Parameter init_unit_position : forall {p}, InitUnit p -> nat.

Inductive InitPath {p} {i : Input p} (ph : Phase i) (k : PackageRef p)
  : InitUnit p -> InitUnit p -> Prop :=
| IPStep : forall a b, InitEdge ph k a b -> InitPath ph k a b
| IPMore : forall a b c, InitEdge ph k a b -> InitPath ph k b c -> InitPath ph k a c.

Record InitOrder {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type := MakeInitOrder {
  init_sequence  : list (InitUnit p);
  init_covers    : forall u : InitUnit p,
                     List.In u (package_init_units k) <-> List.In u init_sequence;
  init_nodup     : NoDup init_sequence;
  init_respects  : forall from to : InitUnit p,
                     InitEdge ph k from to -> PrecedesIn init_sequence to from;
  init_tiebreak  : forall a b : InitUnit p,
                     List.In a (package_init_units k) -> List.In b (package_init_units k) ->
                     ~ InitPath ph k a b -> ~ InitPath ph k b a ->
                     (init_unit_position a < init_unit_position b)%nat ->
                     PrecedesIn init_sequence a b
}.

(* A cycle witness is data: the exact unit that reaches itself, and the exact path by which it does. *)
Record InitCycle {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type := MakeInitCycle {
  init_cycle_unit : InitUnit p;
  init_cycle_path : InitPath ph k init_cycle_unit init_cycle_unit
}.

(* One decision, returning the exact witness on either side rather than a boolean to be interpreted. *)
Parameter init_order_dec : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  InitCycle ph k + InitOrder ph k.

(* Only variable work reaches the C7 runtime store; constant evaluation is compile-time. *)
Definition runtime_initialization {p} {i : Input p} {ph : Phase i} {k : PackageRef p}
  (o : InitOrder ph k) : list (InitUnit p) :=
  List.filter RuntimeInitUnit (init_sequence ph k o).

(* ── §17 The causal dependency relation ────────────────────────────────────── *)
(* Phase-indexed, because several causes are only visible once names are bound: which variable a use reads,
   and which initialization unit a use belongs to.  Type-node causality is not here — `NodeBlocked` already
   retains its exact predecessor node, edge and that predecessor's retained outcome. *)
Inductive SiteDependency {p} {i : Input p} (ph : Phase i) : Site p -> Site p -> Prop :=
| DepUseOfExpression : forall u : ExprUseRef p,
    SiteDependency ph (SExpression p (expression_of_use u)) (SUse p u)
(* A name expression depends on the binding that gave its name meaning. *)
| DepNameBinding : forall (r : ExprRef p) (u : NameUseRef p),
    r = name_use_expr u -> SiteDependency ph (SBinding p u) (SExpression p r)
(* A consumption site depends on each of its own right-hand-side uses. *)
| DepConsumptionUse : forall (c : ConsumptionSiteRef p) (u : ExprUseRef p),
    List.In u (site_uses c) -> SiteDependency ph (SUse p u) (SConsumption p c)
(* A package initialization order depends on every binding its units read. *)
| DepDependencyBinding : forall (k : PackageRef p) (unit : InitUnit p) (u : NameUseRef p),
    List.In unit (package_init_units k) -> List.In u (init_unit_uses unit) ->
    SiteDependency ph (SBinding p u) (SDependency p k)
(* A package-level declaration is elaborated after the order that decides when it runs. *)
| DepDeclarationOrder : forall (k : PackageRef p) (b : ObjectEstablisher p),
    establisher_scope b = PackageScope p k ->
    SiteDependency ph (SDependency p k) (SDeclaration p b)
(* A short reuse depends on the earlier same-block variable whose object it retains. *)
(* A declaration's meaning depends on the consumption that established it. *)
| DepMeaningConsumption : forall (c : ConsumptionSiteRef p) (n : BindingNameRef p)
    (est : ObjectEstablisher p),
    List.In n (site_targets c) ->
    n = establisher_binding_name est ->
    SiteDependency ph (SConsumption p c) (SDeclaration p est)
(* The unused-local verdict depends on the exact reads of that variable. *)
| DepLocalRead : forall (est : ObjectEstablisher p) (u : NameUseRef p) (bf : BindingFact ph u),
    bound_object ph u bf = source_object ph (establisher_site est) ->
    SiteDependency ph (SBinding p u) (SDeclaration p est).

(* ── §14 Blocked chains terminate ──────────────────────────────────────────── *)
(* A well-founded stage: every dependency strictly decreases it, so no blocked cycle exists and every
   blocked chain is finite.  This is structural termination, not a fuel bound. *)
Parameter site_stage : forall {p} {i : Input p} (ph : Phase i), Site p -> nat.
