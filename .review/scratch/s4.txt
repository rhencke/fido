
(* ── §3.1 The exact type-equation graph ────────────────────────────────────── *)

(* Nodes are exactly the source aliases and definitions. *)
Inductive TypeNode (p : SyntaxProgram) : Type :=
| AliasNode   : AliasSpecRef p -> TypeNode p
| DefinedNode : BoundDefinedTypeRef p -> TypeNode p.

Parameter equation_target : forall {p}, ResolvedTypeEquations p -> TypeNode p -> RawTypeTarget p.

(* Edges come only from the exact bound type use in a right-hand side.
   There is no constructor for a predeclared target: predeclared targets are terminal. *)
Inductive TypeEdge {p} (eqs : ResolvedTypeEquations p) : TypeNode p -> TypeNode p -> Prop :=
| EdgeToAlias   : forall n a, equation_target eqs n = RawAlias p a ->
    TypeEdge eqs n (AliasNode p a)
| EdgeToDefined : forall n d, equation_target eqs n = RawDefined p d ->
    TypeEdge eqs n (DefinedNode p d).

Inductive EdgePath {p} (eqs : ResolvedTypeEquations p) : TypeNode p -> TypeNode p -> Prop :=
| PathStep : forall n m, TypeEdge eqs n m -> EdgePath eqs n m
| PathMore : forall n m o, TypeEdge eqs n m -> EdgePath eqs m o -> EdgePath eqs n o.

(* Every C6 cycle is invalid; a cycle witness is an exact node on its own path. *)
Record TypeCycle {p} (eqs : ResolvedTypeEquations p) : Type := MakeTypeCycle {
  cycle_node : TypeNode p;
  cycle_path : EdgePath eqs cycle_node cycle_node
}.

Definition AcyclicEquations {p} (eqs : ResolvedTypeEquations p) : Prop :=
  forall n, ~ EdgePath eqs n n.

(* A cycle witness is data, so the decision is a sumor, not a sumbool. *)
Parameter acyclic_dec : forall {p} (eqs : ResolvedTypeEquations p),
  TypeCycle eqs + { AcyclicEquations eqs }.

(* ── §3.2 Semantic types need no environment ───────────────────────────────── *)
(* A type is a predeclared basic type or an exact defined-type declaration.  An environment was only ever
   needed to say what a definition's right-hand side is, and that is a per-node outcome below.  An alias has
   no constructor here, which is how it mints no identity. *)
Inductive SemanticType (p : SyntaxProgram) : Type :=
| PredeclaredType : PredeclaredBasicType -> SemanticType p
| DefinedType     : BoundDefinedTypeRef p -> SemanticType p.

Parameter defined_key : forall {p}, BoundDefinedTypeRef p -> IndexKey.

Definition type_view {p} (t : SemanticType p) : TypeView :=
  match t with
  | PredeclaredType _ b => PredeclaredView b
  | DefinedType _ d => DefinedView (defined_key d)
  end.

(* Every raw right-hand-side target a C6 node can resolve to: a predeclared named type, a predeclared
   alias, or a source definition.  A source alias target resolves through its own node. *)
(* Raw alias resolution chains through the predecessor alias node.  No global acyclicity needed here;
   the chain terminates because the graph edge structure is finite and acyclic resolution handles it. *)
Inductive ResolvedTypeTarget {p} : RawTypeTarget p -> SemanticType p -> Prop :=
| ResolvedPredeclaredType : forall n t, AdmittedPredeclaredType n t ->
    ResolvedTypeTarget (RawPredeclared p n) (PredeclaredType p t)
| ResolvedPredeclaredAlias : forall n t, AliasPredeclared n t ->
    ResolvedTypeTarget (RawPredeclared p n) (PredeclaredType p t)
| ResolvedSourceAlias : forall (a : AliasSpecRef p) (target : SemanticType p),
    ResolvedTypeTarget (RawAlias p a) target
| ResolvedDefinedType : forall d, ResolvedTypeTarget (RawDefined p d) (DefinedType p d).

(* ── §3.3 Every type node has one sealed outcome ───────────────────────────── *)
Inductive TypeNodeFailure (p : SyntaxProgram) : Type :=
| RhsUnresolved  : NameUseRef p -> TypeNodeFailure p
| RhsWrongRole   : NameUseRef p -> TypeNodeFailure p.

(* `Blocked` retains the exact predecessor node, the exact edge, and that predecessor's exact retained
   outcome — never an independently supplied outcome that merely looks equal. *)
Inductive TypeNodeOutcome {p} {i : Input p} (ph : Phase i) : TypeNode p -> Type :=
| NodeAliasSupported : forall (a : AliasSpecRef p) (u : NameUseRef p) (bf : BindingFact ph u)
    (target : SemanticType p),
    ResolvedTypeTarget (equation_target (phase_equations ph) (AliasNode p a)) target ->
    TypeNodeOutcome ph (AliasNode p a)
| NodeDefinedSupported : forall (d : BoundDefinedTypeRef p) (u : NameUseRef p) (bf : BindingFact ph u)
    (rhs : SemanticType p),
    ResolvedTypeTarget (equation_target (phase_equations ph) (DefinedNode p d)) rhs ->
    TypeNodeOutcome ph (DefinedNode p d)
| NodeFailed    : forall (n : TypeNode p), TypeNodeFailure p -> TypeNodeOutcome ph n
| NodeOutside   : forall (n : TypeNode p) (u : NameUseRef p),
    BindingFact ph u -> TypeNodeOutcome ph n
| NodeBlocked   : forall (n m : TypeNode p),
    TypeEdge (phase_equations ph) n m -> TypeNodeOutcome ph n.

(* Node outcomes are computed in dependency order, so they exist only once the graph is known acyclic.
   A cyclic phase has no node table at all. *)
Parameter node_outcome : forall {p} {i : Input p} (ph : Phase i),
  AcyclicEquations (phase_equations ph) -> forall n : TypeNode p, TypeNodeOutcome ph n.

Definition NodeIsSupported {p} {i : Input p} {ph : Phase i} {n} (o : TypeNodeOutcome ph n) : Prop :=
  match o with
  | NodeAliasSupported _ _ _ _ _ _ => True
  | NodeDefinedSupported _ _ _ _ _ _ => True
  | _ => False
  end.

(* A ready environment exists only when the graph is acyclic AND every node is supported.  `type U uintptr;
   type T U` is acyclic, yet `uintptr` has no C6 type meaning, so no environment exists for it.
   The seal is the obligation, not constructor hiding: building one requires evidence about `node_outcome`
   for every node, which only the phase's own decision produces. *)
Record TypeReady {p} {i : Input p} (ph : Phase i) : Type := MakeTypeReady {
  ready_acyclic       : AcyclicEquations (phase_equations ph);
  ready_all_supported : forall n : TypeNode p, NodeIsSupported (node_outcome ph ready_acyclic n)
}.

(* Derived from the exact node outcomes, not postulated over arbitrary acyclic graphs. *)
Definition node_rhs {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  (n : TypeNode p) : SemanticType p :=
  match node_outcome ph (ready_acyclic ph rd) n as o return NodeIsSupported o -> SemanticType p with
  | NodeAliasSupported _ _ _ _ target _ => fun _ => target
  | NodeDefinedSupported _ d _ _ _ _    => fun _ => DefinedType p d
  | NodeFailed _ _ _      => fun h => match h return SemanticType p with end
  | NodeOutside _ _ _ _   => fun h => match h return SemanticType p with end
  | NodeBlocked _ _ _ _   => fun h => match h return SemanticType p with end
  end (ready_all_supported ph rd n).

(* §6 Extract the RHS type from a single supported node, needing only its own acyclicity and support. *)
Definition node_rhs_single {p} {i : Input p} {ph : Phase i}
  (acyc : AcyclicEquations (phase_equations ph)) (n : TypeNode p)
  (sup : NodeIsSupported (node_outcome ph acyc n)) : SemanticType p :=
  match node_outcome ph acyc n as o return NodeIsSupported o -> SemanticType p with
  | NodeAliasSupported _ _ _ _ target _ => fun _ => target
  | NodeDefinedSupported _ d _ _ _ _    => fun _ => DefinedType p d
  | NodeFailed _ _ _      => fun h => match h return SemanticType p with end
  | NodeOutside _ _ _ _   => fun h => match h return SemanticType p with end
  | NodeBlocked _ _ _ _   => fun h => match h return SemanticType p with end
  end sup.


(* The underlying form is retained by the supported outcome, so it is read rather than chased through a
   relation that could self-loop.  No recursion, no fuel. *)


(* ── §3.4 Identity, underlying form and the C6 relations ───────────────────── *)
(* Identity and assignability need no environment at all: a predeclared type is its name, a defined type is
   its exact declaration. *)
Inductive Identical {p} : SemanticType p -> SemanticType p -> Prop :=
| IdenticalPredeclared : forall t, Identical (PredeclaredType p t) (PredeclaredType p t)
| IdenticalDefined     : forall d, Identical (DefinedType p d) (DefinedType p d).

Inductive Assignable {p} : SemanticType p -> SemanticType p -> Prop :=
| AssignIdentical : forall s t, Identical s t -> Assignable s t.

(* §6 Underlying needs only per-type evidence, not a global TypeReady.  A predeclared type's form is
   definitional.  A defined type's form follows the exact RHS from its own supported node outcome. *)
Inductive Underlying {p} {i : Input p} (ph : Phase i)
  : SemanticType p -> BasicType -> Prop :=
| UnderlyingPredeclared : forall t,
    Underlying ph (PredeclaredType p t) (predeclared_basic_form t)
| UnderlyingDefined : forall (d : BoundDefinedTypeRef p)
    (acyc : AcyclicEquations (phase_equations ph))
    (sup : NodeIsSupported (node_outcome ph acyc (DefinedNode p d))) b,
    Underlying ph (node_rhs_single acyc (DefinedNode p d) sup) b ->
    Underlying ph (DefinedType p d) b.

Inductive ValueConvertible {p} {i : Input p} (ph : Phase i)
  : SemanticType p -> SemanticType p -> Prop :=
| VConvIdentical : forall s t, Identical s t -> ValueConvertible ph s t
| VConvSameUnderlying : forall s t b,
    Underlying ph s b -> Underlying ph t b -> ValueConvertible ph s t
| VConvScalarNumeric : forall s t bs bt,
    Underlying ph s bs -> Underlying ph t bt ->
    ScalarNumericBasic bs -> ScalarNumericBasic bt -> ValueConvertible ph s t
| VConvComplex : forall s t bs bt,
    Underlying ph s bs -> Underlying ph t bt ->
    ComplexBasicForm bs -> ComplexBasicForm bt -> ValueConvertible ph s t.

Inductive Representable {p} {i : Input p} (ph : Phase i)
  : SemanticType p -> Constant -> Prop :=
| RepresentableAt : forall s b c, Underlying ph s b -> FitsBasic b c -> Representable ph s c.

Inductive ConstantConvertible {p} {i : Input p} (ph : Phase i)
  : SemanticType p -> Constant -> Constant -> Prop :=
| CConvExact : forall s b c c',
    Underlying ph s b -> convert_constant_to b c = Some c' -> ConstantConvertible ph s c c'.

(* A typed constant retains its exact constant value, so negation and conversion stay causally connected to
   the operand they came from. *)
Record TypedConstant {p} {i : Input p} (ph : Phase i)
  (s : SemanticType p) : Type := MakeTypedConstant {
  typed_form     : BasicType;
  typed_underlying : Underlying ph s typed_form;
  typed_value    : BasicTypedConstant typed_form
}.


(* §6 Per-semantic-type resolved fact.  A predeclared type needs nothing; a defined type needs its exact
   supported node outcome.  This replaces global `TypeReady` as the prerequisite for `Underlying` and
   downstream relations, so an independent basic expression has facts even when another type is outside. *)
Inductive TypeEvidence {p} {i : Input p} (ph : Phase i) : SemanticType p -> Type :=
| TEPredeclared : forall (t : PredeclaredBasicType), TypeEvidence ph (PredeclaredType p t)
| TEDefined : forall (d : BoundDefinedTypeRef p)
    (acyc : AcyclicEquations (phase_equations ph)),
    NodeIsSupported (node_outcome ph acyc (DefinedNode p d)) ->
    TypeEvidence ph (DefinedType p d).

(* The underlying form is now a direct consequence of Underlying, not a separate parameter. *)


(* §6 Bridge: a TypeReady projects exact TypeEvidence for every semantic type it covers. *)
Definition type_evidence_of {p} {i : Input p} {ph : Phase i} (rd : TypeReady ph)
  (t : SemanticType p) : TypeEvidence ph t :=
  match t with
  | PredeclaredType _ bt => TEPredeclared ph bt
  | DefinedType _ d => TEDefined ph d (ready_acyclic ph rd) (ready_all_supported ph rd (DefinedNode p d))
  end.

Parameter underlyingb : forall {p} {i : Input p} (ph : Phase i),
  SemanticType p -> BasicType.
Parameter identicalb assignableb : forall {p}, SemanticType p -> SemanticType p -> bool.
Parameter value_convertibleb : forall {p} {i : Input p} (ph : Phase i),
  SemanticType p -> SemanticType p -> bool.
Parameter representableb : forall {p} {i : Input p} (ph : Phase i),
  SemanticType p -> Constant -> bool.

Definition default_type {p} (k : UntypedConstantKind) : SemanticType p :=
  PredeclaredType p (default_basic k).

