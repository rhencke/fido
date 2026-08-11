# C6 — the static semantic foundation

Review: implementation

Goal: ordinary source names acquire meaning only through binding. Every predeclared spelling is a legal
source identifier and may be shadowed; `_` is a valid lexical `Names.Identifier` but not an
`OrdinaryIdentifier`, and the future `Syntax.BindingName.Blank` source form creates no binding. C6 lands the
pinned predeclared
catalog, a closed type algebra with named predeclared types, exact constants, role-indexed use facts, rules
that consume their exact operands, one result-occurrence authority, compiler-owned static variable identity,
the static package dependency object, and a three-way decision that never calls unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime`, value, place, store, environment or `Machine.T`; C7 introduces them
as one vertical and materializes package **variables** only — constants stay compile-time facts.

C6 is implemented directly in its permanent semantic owners — `Names.v` for the source-name root and the
`Compilable.*` modules for the static semantic roots owned there — following the milestone process in
`ARCHITECTURE.md` §1 "Two authorities, never two formal implementations". This document is governing prose:
it owns C6's required meaning, scope, boundaries, evidence and stop conditions. The formal-looking blocks below
(§"Remaining C6 migration inventory" and §"Theorems") are **temporary, non-authoritative migration inventory**,
not an independently elaborated specification — read their terms before using them.

**Canonical root 1 — the source-name universe** is implemented in `Names.v`: the identifier lexical predicate,
the ordinary (nonblank) identifier subtype, the complete predeclared identity catalog and its spelling,
classifier and equality. C6 requires ordinary identifiers and the full predeclared catalog; the migration
inventory below refers to those canonical names without restating them.

**Canonical root 2 — static typed constants and pre-runtime erasure** is implemented in `Float`/`Complex`
(consumed on the compilation branch by `Typing`/`Compilable`; `Render` is a sibling branch and consumes no
typed constant): a float or complex typed constant is a purely compile-time carrier retaining the exact
post-rounding rational and the exact destination-format rounded representation of one rounding, and the
premature `Float.Value`/`Complex.Value` runtime carriers and the `Safe` evaluator are deleted. C7 creates the
first runtime values. This root changes no `Syntax.Program` inhabitant, no source meaning, no decision, no
diagnostic, and no rendered byte.

**Status — Root 2 accepted; C6 Root 3 is the active frontier.** Rob accepted **C6 Root 2** at exact candidate
`aaa344121d0478540e0ebf2ce981b98a13044a8c`, disposition `C6-ROOT2-ACCEPT-AAA3441`, on two whole-system reviews
by two different models (Claude Code's post-implementation review and the primary ChatGPT review) and his
decision. The acceptance is exact and narrow: `Float.TypedConstant`, `Complex.TypedConstant`, their
format-indexed static-carrier topology, one destination-format rounding with same-result readback, exact
component composition, same-format carrier reuse, deletion of the premature runtime/value/evaluator route, and
the whole-system preservation contract at `aaa3441`. It does **not** accept C6 as a milestone, authorize C7, or
accept any later C6 root. **Root 1** remains accepted at `6c13dc0` (unchanged).

**C6 is incomplete and unaccepted; accepting one root never accepts another root or the milestone.** The sole
active implementation frontier is **C6 Root 3 — the source, occurrence, binding, and honest-outcome
foundation** (§ below). Later C6 roots, Final C6, and C7 stay frozen until Rob accepts each in turn; Rob alone
accepts. Git owns the repair and review narrative — no chronological candidate list lives here.

**Root 3 recut implemented — a semantic-root-review candidate, not an acceptance.** The recut vertical is
formalized in its canonical modules and passes the full gate (prove axiom-free + whole-tree `go build ./...` vs
goldens + byte-identical generated output): the general `Syntax` source algebra; `Index` exact source
occurrences, dependent views, and the program-level reference API; the new top-level `Bindings` module (object
identity, lexical scopes and enclosure, object-establishing sites, and ordinary-name resolution with
shadowing); the new top-level `Packages` module (the package rules, fresh-build preflight, and import path);
and `Compilable`'s site-based static phase with the permanent, sealed three-way `Compiled | Rejected |
OutsideScope` decision. The dedicated `Println`/`Convert` constructors are deleted and the accepted
println/conversion/literal fragment travels the binding-based path with byte-identical emitted output. The
qualified `Compilable.*` physical split is deferred (top-level `Bindings`/`Packages` for now); the §9 evidence
expansion and the migration-inventory prune below complete the final candidate.

**Root 3 recut (`C6-ROOT3-SOURCE-BINDING-OUTCOME-RECUT-97EA4AE`).** The earlier pure source/occurrence cut was
not dependency-closed: adding the general source forms makes pinned-Go-valid programs representable that the
current two-way (`Compiled`/`Rejected`) compiler could only false-reject, and the honest `OutsideScope` verdict
is a partial-phase fact, not a pure-syntax one (`ROOT_BOUNDARY_CONFLICT`). Rob recut Root 3 to the first honest
static vertical: source shape, exact occurrence, the scope/object/binding foundation, one retained partial static
phase, and the permanent three-way outcome form one causal unit. Root 3 lands, together:

- the general source algebra in the one `Syntax.Program` — binding names and blank, magnitude literals with
  unary-minus, ordinary type uses, `Name`/`Unary`/`Application`, and const/var/type/short/block/declaration
  shapes — deleting the superseded dedicated `Println`/`Convert` constructors once the replacement is live;
- exact `Index` occurrence and view identity for every newly live position (binding names/blanks, name uses,
  type uses, literals, unary, applications with heads and ordered arguments, decl/spec, statement/block, and
  short-declaration left/right), each refinement projecting its exact parent, no occurrence recovered by
  rescanning source;
- the binding foundation: exact lexical scopes and enclosure, object-establishing source sites (blank
  establishes none), duplicate-safe scope maps, source and predeclared object identity, ordinary-name
  resolution with shadowing and visibility, and short-declaration new/reuse at the exact left occurrence;
- one retained partial static phase built from the exact source/index/scope/binding objects, distinguishing
  established facts, definite invalidity, exact unmet requirements, and causal blocking, retaining the objects
  that established every outcome (equality to a rerun is not provenance);
- the permanent three-way `Compiled | Rejected | OutsideScope` public outcome, where an outside boundary is the
  exact earliest unmet requirement at an exact retained site (missing type/value/application/statement/unary
  meaning), never a feature flag and never a claim about Go validity; and
- migration of the accepted `println`/conversion/literal fragment through the binding-based path, byte-identical
  in branch, diagnostics and emitted output.

Deferred to later roots (not in this recut): complete type-equation solving and acyclicity; alias/defined-type
meaning; full declaration/initializer consumption; result plans and assignment; compiler-owned `StaticVariable`
formation; package const/var dependency ordering and initialization cycles; unused-local analysis; application
families beyond the accepted conversion and `println`; and any runtime value, place, store, environment,
concrete `Machine.T`, or C7 behavior. Later roots fill exact requirements inside the same sealed retained phase;
they never replace the outcome/boundary root or reinterpret an established boundary as a diagnostic. A causal
expansion beyond this recut is a `ROOT_EXPANSION_CONFLICT` stop, not autonomous widening.

**Concurrent findings (nonblocking, `STRICT-CHECKPOINT-SCOPE`).** A core semantic, provenance, theorem,
capability, behavior, or required-dependency defect blocks; a non-foundational gate, tooling, documentation,
performance, or hygiene defect is mandatory concurrent work with an exact closure point that cannot survive an
acceptance depending on it. These remain open, assigned to the Root 3 recut batch at the closure points named,
and do not reopen or weaken any accepted root:

- `TOOLCHAIN.md` Go-version truth — the immutable image digest owns the executable toolchain identity, the
  observed version is `go1.23.12`, and the stale `go1.23.2` current-state claim is to be corrected;
- Float/Complex "construction authority" wording narrowed to the proved rounding-from-exact formation
  authority for each carrier;
- the `Syntax -> Integer` retention resolved before Syntax changes — deleted if it has no retained purpose (and
  the direct-edge policy updated), or its exact consumed fact recorded;
- single-AWK layer-gate hardening — late-stream read-error detection, policy-marker order and proper closure,
  and explicit classification of actual dependency targets outside the Dune theory universe, with one policy,
  one `rocq dep` producer, and one verdict retained;
- the flat-module identity boundary — closes only if Root 3 introduces the first qualified `Compilable.*`
  physical split, otherwise assigned to the first root that does.

## Ownership and physical modules

`ARCHITECTURE.md` owns the ownership law and the physical-structure doctrine, including the `Compilable.*`
decomposition; `ROADMAP.md` owns the milestone sequence. The table below is the C6 instantiation of that
doctrine, not a competing authority.

| module | owns |
|---|---|
| `Compilable.Bindings` | `PackageRef`, scopes, object identity, binder/object sites, blank/new/reuse disposition, name binding, the predeclared outer scope and shadowing |
| `Compilable.TypeResolution` | exact type equations, the graph decision, the sealed `TypeReady` environment, object-indexed type meanings, predeclared and defined type identity through `node_rhs` and `Underlying` |
| `Compilable.Dependencies` | package const/var dependency nodes, edges, cycle/acyclic outcome, retained order, the runtime-variable projection |
| `Compilable.Facts` | expression facts, role-indexed use facts, single-result uses, unary/application rules, statement classification, object-indexed meanings, const/var/short consumption plans, binder finalization, exact `StaticVariable`, unused-local facts |
| `Compilable.Report` | site failures, diagnostics, site requirements, reflected satisfaction, boundaries, root/blocked reporting, canonical lists |
| `Compilable.v` | phase composition, whole-program preflight, `Core`, `Elaboration`, `Decision`, `Program`/`Failure`/`Outside`, `Outcome`, `elaborate`, `compile` |
| `Compilable.Evidence` | certified accepted/rejected/outside fixtures and controls; no production module imports it |

`Bindings` precedes `TypeResolution` and `Dependencies`; those three precede `Facts`; `Facts` precedes
`Report`; `Report` precedes `Compilable.v`; `Compilable.v` precedes
`Evidence`. No child imports `Compilable.v`.

## Diagnostic migration

Every current public diagnostic survives with its code, primary anchor, related anchors and erasure. Those
with one exact failing site move under `AtSiteFailure`; the package- and program-level reasons keep their own
constructors because they have no single site.

| current public constructor | C6 form |
|---|---|
| `InvalidConversion` | `AtSiteFailure (SApplication a) (FInvalidConversion …)`, retaining the exact application, operand view, target view and outer context |
| `DefaultNotRepresentable` | `AtSiteFailure (SExpression r) (FDefaultNotRepresentable …)`, retaining the exact expression, constant kind and default target |
| `MainRedeclared` | `MainRedeclared later earlier` — unchanged; both object sites retained |
| `MissingMainEntry` | `MissingMainEntry k` — unchanged; the exact `PackageRef` retained |
| `BuildOutputIsDirectory` | `BuildOutputIsDirectory k name` — unchanged |
| `AtNode`/`AtFile`/`AtPackage`/`AtProgram` | retained exactly |
| `diagnostic_code`/`diagnostic_primary`/`diagnostic_related`/`erase_diagnostic` | retained; `erase_diagnostic` is a definition over the six-field record, so the projection equations hold definitionally and carry no theorem |

C6 adds, and does not replace: unresolved name, duplicate declaration, argument, operand, not-a-statement,
result count, not-assignable, not-representable, const-initializer-not-constant, no-new-variable, unused
local, type cycle and initialization cycle.

## Sealing

The sealing below is C6 implementation-review guidance, not a public interface. Three
families are module-private and export only their projections: site outcomes, site failures and boundaries
in `Compilable.Report`, and node outcomes in `Compilable.TypeResolution`. Their constructors are freely
applicable, so a client holding them could fabricate an outcome or a boundary; production values come only
from `phase_outcome`, `node_outcome` and `core_boundaries`.

`TypeReady` is sealed differently and does not need its constructor hidden. Building one requires
acyclicity of the whole graph plus support for every node, and that evidence exists only where the phase's
own decision produced it.

## Remaining C6 migration inventory (temporary, non-authoritative)

The Rocq block below, together with the §Theorems block, is **remaining C6 migration inventory** — not a
specification and not the active surface:

- it is non-authoritative;
- it is not independently elaborated: no gate type-checks it, and it is no longer a "published surface";
- it applies only to the portions of C6 not yet canonicalized;
- the canonical `Compilable.*` implementation owns the exact topology and may prove any of it wrong;
- each later implementation commit canonicalizes one dependency-closed portion and deletes the corresponding
  inventory here in the same commit;
- no implemented declaration or theorem may keep a duplicate exact rendition in this block;
- nothing here is moved elsewhere when deleted — Git owns history;
- it must reach zero by C6 completion, leaving only C6's semantic obligations, boundaries, gates, preserved
  facts and review instructions.

```coq
(* Remaining C6 migration inventory, in dependency order.  Non-authoritative: the canonical Compilable.* *)
(* implementation owns exact topology, may prove any of this wrong, and deletes it in lockstep as it lands. *)

From Stdlib Require Import List String Ascii ZArith NArith Sorted.
Import ListNotations.

(* ── (a) existing repository public names, faithfully stubbed ──────────────── *)
Parameter SyntaxProgram SyntaxFile ModuleSpec FilePathT : Type.
Parameter PackageRef : SyntaxProgram -> Type.
Parameter package_ref_key : forall {p}, PackageRef p -> string.
Parameter Identifier : Type.
Parameter spelling : Identifier -> string.
(* Integer.Kind is closed today; stub it faithfully.  Float.Kind, Complex.Kind and their typed constants are
   the canonical owners in `Float`/`Complex`, referenced directly below. *)
Inductive IntegerKind : Type :=
| IKInt | IKInt8 | IKInt16 | IKInt32 | IKInt64
| IKUint | IKUint8 | IKUint16 | IKUint32 | IKUint64.
Parameter IntegerRepresentable : IntegerKind -> Z -> Prop.
Parameter Decimal : Type.
Parameter coefficient : Decimal -> Z.
Parameter IndexKey : Type.
Parameter Input : SyntaxProgram -> Type.
Parameter Core : SyntaxProgram -> Type.
Parameter core_input : forall {p}, Core p -> Input p.
Parameter Elaboration : SyntaxProgram -> Type.
Parameter elaboration_core : forall {p}, Elaboration p -> Core p.
Parameter elaborate : forall p, Elaboration p.
Parameter Admissible : SyntaxProgram -> Prop.

(* ── Names ─────────────────────────────────────────────────────────────────── *)
(* Canonicalized in `Names.v`: `PredeclaredName` (the 44-identity catalog), `predeclared_spelling`,
   `all_predeclared`, `classify_predeclared`, `predeclared_eqb`, and `OrdinaryIdentifier` (the nonblank
   subtype retaining its exact `Identifier`).  The names below refer to those canonical definitions; this
   inventory no longer restates them and no longer elaborates standalone. *)

(* Collections owns NonEmpty; Float owns NonNegativeDecimal. *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.
Definition ne_to_list {A} (ne : NonEmpty A) : list A := ne_first A ne :: ne_rest A ne.
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal : Decimal; nnd_nonneg : (0 <= coefficient nnd_decimal)%Z
}.

(* ── Syntax ────────────────────────────────────────────────────────────────── *)
Inductive BindingName : Type := Named (n : OrdinaryIdentifier) | Blank.
Inductive UnaryOp : Type := UnaryMinus.

(* Magnitudes only: a negative source value is exactly one `Unary UnaryMinus` over a nonnegative literal. *)
Inductive Literal : Type :=
| IntegerLiteral (n : N)
| FloatLiteral (d : NonNegativeDecimal)
| StringLiteral (s : string).

Inductive TypeExpr : Type := NamedType (n : OrdinaryIdentifier).

Inductive Expr : Type :=
| Name (n : OrdinaryIdentifier)
| LiteralExpr (l : Literal)
| Unary (op : UnaryOp) (e : Expr)
| Application (head : Expr) (args : list Expr).

Inductive ConstInitializer : Type :=
| ExplicitConstInit (ty : option TypeExpr) (values : NonEmpty Expr)
| InheritedConstInit.

Record ConstSpec : Type := MakeConstSpec {
  const_names : NonEmpty BindingName; const_init : ConstInitializer
}.

Inductive VarInitializer : Type :=
| VarTypeOnly (ty : TypeExpr)
| VarValues (ty : option TypeExpr) (values : NonEmpty Expr).

Record VarSpec : Type := MakeVarSpec {
  var_names : NonEmpty BindingName; var_init : VarInitializer
}.

(* Both alias and definition admit blank; a blank type spec creates no object and no type identity. *)
Inductive TypeSpec : Type :=
| AliasSpec (name : BindingName) (target : TypeExpr)
| DefSpec (name : BindingName) (target : TypeExpr).

(* Pinned Go accepts `const ()`, `var ()` and `type ()`, so a spec group is a list.  Name lists and explicit
   initializer expression lists stay nonempty. *)
Inductive Declaration : Type :=
| ConstDecl (specs : list ConstSpec)
| VarDecl (specs : list VarSpec)
| TypeDecl (specs : list TypeSpec).

Inductive Stmt : Type :=
| ExprStmt (e : Expr)
| DeclarationStmt (d : Declaration)
| ShortVarDecl (names : NonEmpty BindingName) (values : NonEmpty Expr).

Inductive Block : Type := MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration (d : Declaration)
| Main (body : Block).

Parameter program_files : SyntaxProgram -> list (FilePathT * SyntaxFile).
Parameter program_module : SyntaxProgram -> ModuleSpec.
(* Rendering cannot be pinned against an opaque file: these mirror the repository accessors. *)
Parameter file_decls : SyntaxFile -> list TopLevelDecl.
Parameter path_string : FilePathT -> string.
Parameter module_path : ModuleSpec -> string.
Parameter module_go_version : ModuleSpec -> string.

(* ── §2.1 The scope forest ─────────────────────────────────────────────────── *)
Parameter LexicalScopeRef : SyntaxProgram -> Type.
Parameter lexical_scope_package : forall {p}, LexicalScopeRef p -> PackageRef p.

Inductive ScopeId (p : SyntaxProgram) : Type :=
| PredeclaredScope : ScopeId p
| PackageScope     : PackageRef p -> ScopeId p
| LexicalScope     : LexicalScopeRef p -> ScopeId p.

Definition scope_parent {p} (s : ScopeId p) : option (ScopeId p) :=
  match s with
  | PredeclaredScope _ => None
  | PackageScope _ _   => Some (PredeclaredScope p)
  | LexicalScope _ b   => Some (PackageScope p (lexical_scope_package b))
  end.

Inductive Encloses {p} : ScopeId p -> ScopeId p -> Prop :=
| EnclosesSelf   : forall s, Encloses s s
| EnclosesParent : forall outer inner parent,
    scope_parent inner = Some parent -> Encloses outer parent -> Encloses outer inner.

Inductive ScopeStart : Type :=
| StartWholePackage | StartAfterSpec | StartAtOwnIdentifier | StartAfterStatement | StartOutermost.

Inductive DeclContext : Type :=
| PackageConstDecl | PackageVarDecl | PackageTypeDecl
| LocalConstDecl | LocalVarDecl | LocalTypeDecl
| ShortDecl | PredeclaredDecl.

Definition scope_start (c : DeclContext) : ScopeStart :=
  match c with
  | PackageConstDecl | PackageVarDecl | PackageTypeDecl => StartWholePackage
  | LocalConstDecl | LocalVarDecl => StartAfterSpec
  | LocalTypeDecl => StartAtOwnIdentifier
  | ShortDecl => StartAfterStatement
  | PredeclaredDecl => StartOutermost
  end.

Definition PackageInitReserved (c : DeclContext) (n : string) : Prop :=
  (c = PackageConstDecl \/ c = PackageVarDecl \/ c = PackageTypeDecl) /\ n = "init"%string.


(* ── Index: exact source occurrences ───────────────────────────────────────── *)
Inductive Role : Type :=
| RFilePackage | RDeclarationSpec | RVarSpecType
| RConstInitializerExpression | RVarInitializerExpression | RShortRightExpression
| RStatementExpression | RUnaryOperand | RApplicationHead | RApplicationArgument.

Inductive ExprChildRole : Role -> Type :=
| ECConstInitializer : ExprChildRole RConstInitializerExpression
| ECVarInitializer   : ExprChildRole RVarInitializerExpression
| ECShortRight       : ExprChildRole RShortRightExpression
| ECStatement        : ExprChildRole RStatementExpression
| ECUnaryOperand     : ExprChildRole RUnaryOperand
| ECApplicationHead  : ExprChildRole RApplicationHead
| ECApplicationArg   : ExprChildRole RApplicationArgument.

Inductive UseRole : Type := TypeNameRole | ValueNameRole | HeadNameRole.

Parameter NodeRef : SyntaxProgram -> Type.
Parameter node_key : forall {p}, NodeRef p -> IndexKey.
Parameter ExprRef ConstDeclRef ConstSpecRef BindingNameRef BlankRef : SyntaxProgram -> Type.
Parameter TypeUseRef NameUseRef UnaryRef ApplicationRef : SyntaxProgram -> Type.
Parameter ExpressionStatementRef VariableSiteRef : SyntaxProgram -> Type.
Parameter StatementRef FileRef : SyntaxProgram -> Type.
Parameter AliasSpecRef BoundDefinedTypeRef : SyntaxProgram -> Type.
Parameter VarSpecRef ShortDeclRef : SyntaxProgram -> Type.

(* ── §2 Dependent source-shape refinements ─────────────────────────────────── *)
(* Each payload projects its exact parent occurrence, so the constructor index is definitionally that
   projected occurrence and no payload can be borrowed from another. *)
Parameter LiteralRef : SyntaxProgram -> Type.
Parameter literal_expr : forall {p}, LiteralRef p -> ExprRef p.
Parameter name_use_expr : forall {p}, NameUseRef p -> ExprRef p.
Parameter unary_expr : forall {p}, UnaryRef p -> ExprRef p.
Parameter application_expr_of : forall {p}, ApplicationRef p -> ExprRef p.

Inductive ExprView {p} : ExprRef p -> Type :=
| EVLiteral     : forall (l : LiteralRef p), ExprView (literal_expr l)
| EVName        : forall (u : NameUseRef p), ExprView (name_use_expr u)
| EVUnary       : forall (n : UnaryRef p), ExprView (unary_expr n)
| EVApplication : forall (a : ApplicationRef p), ExprView (application_expr_of a).

Parameter expr_view : forall {p} (r : ExprRef p), @ExprView p r.

(* §3 Object-establishing binders are a strict subset of named occurrences. *)
Parameter ObjectEstablisher : SyntaxProgram -> Type.
Parameter establisher_spelling : forall {p}, ObjectEstablisher p -> string.

(* Each binder payload projects its exact parent BindingNameRef. *)
Parameter blank_binding_name : forall {p}, BlankRef p -> BindingNameRef p.
Parameter establisher_binding_name : forall {p}, ObjectEstablisher p -> BindingNameRef p.
Parameter short_lhs_binding_name : forall {p}, ShortDeclRef p -> BindingNameRef p -> BindingNameRef p.
Parameter short_lhs_decl : forall {p}, BindingNameRef p -> option (ShortDeclRef p).
Parameter short_lhs_spelling : forall {p}, BindingNameRef p -> string.
Parameter short_lhs_scope : forall {p}, BindingNameRef p -> ScopeId p.
Parameter short_lhs_position : forall {p}, BindingNameRef p -> nat.

Inductive BindingNameView {p} : BindingNameRef p -> Type :=
| BNBlank   : forall (k : BlankRef p), BindingNameView (blank_binding_name k)
| BNRegular : forall (est : ObjectEstablisher p) (c : DeclContext),
    BindingNameView (establisher_binding_name est)
| BNShort   : forall (d : ShortDeclRef p) (n : BindingNameRef p) (sp : string),
    short_lhs_decl n = Some d -> short_lhs_spelling n = sp ->
    BindingNameView n.

Parameter binding_name_view : forall {p} (n : BindingNameRef p), @BindingNameView p n.

(* §2 Object-site refinements — each payload projects its exact parent site. *)
Parameter ObjectSiteRef : SyntaxProgram -> Type.
Parameter object_site_key : forall {p}, ObjectSiteRef p -> IndexKey.
Parameter const_object_site : forall {p}, ConstSpecRef p -> ObjectSiteRef p.
Parameter var_object_site : forall {p}, VariableSiteRef p -> ObjectSiteRef p.
Parameter alias_object_site : forall {p}, AliasSpecRef p -> ObjectSiteRef p.
Parameter defined_object_site : forall {p}, BoundDefinedTypeRef p -> ObjectSiteRef p.
Parameter main_object_site : forall {p}, FileRef p -> ObjectSiteRef p.

Inductive ObjectSiteView {p} : ObjectSiteRef p -> Type :=
| OSConst   : forall (c : ConstSpecRef p), ObjectSiteView (const_object_site c)
| OSVar     : forall (v : VariableSiteRef p), ObjectSiteView (var_object_site v)
| OSAlias   : forall (a : AliasSpecRef p), ObjectSiteView (alias_object_site a)
| OSDefined : forall (d : BoundDefinedTypeRef p), ObjectSiteView (defined_object_site d)
| OSMain    : forall (f : FileRef p), ObjectSiteView (main_object_site f).

Parameter object_site_view : forall {p} (s : ObjectSiteRef p), @ObjectSiteView p s.
Parameter object_site_spelling : forall {p}, ObjectSiteRef p -> string.
Parameter object_site_scope : forall {p}, ObjectSiteRef p -> ScopeId p.

Parameter establisher_site : forall {p}, ObjectEstablisher p -> ObjectSiteRef p.
Parameter variable_site_establisher : forall {p}, VariableSiteRef p -> ObjectEstablisher p.

Inductive ConsumptionSiteRef (p : SyntaxProgram) : Type :=
| ConstSite : ConstSpecRef p -> ConsumptionSiteRef p
| VarSite   : VarSpecRef p -> ConsumptionSiteRef p
| ShortSite : ShortDeclRef p -> ConsumptionSiteRef p.

(* Structural source laws. *)
Parameter expr_node : forall {p}, ExprRef p -> NodeRef p.
Parameter application_expr application_head : forall {p}, ApplicationRef p -> ExprRef p.
Parameter application_key : forall {p}, ApplicationRef p -> IndexKey.
Parameter statement_expression : forall {p}, ExpressionStatementRef p -> ExprRef p.
Parameter statement_application : forall {p}, ExpressionStatementRef p -> option (ApplicationRef p).
Parameter statement_application_is_its_expression : forall {p}
  (s : ExpressionStatementRef p) (a : ApplicationRef p),
  statement_application s = Some a -> statement_expression s = application_expr a.
Parameter unary_operand : forall {p}, UnaryRef p -> ExprRef p.
Parameter OccupiesRole : forall {p}, NodeRef p -> NodeRef p -> Role -> Prop.

Parameter DirectExprUseRef : SyntaxProgram -> Type.
Parameter direct_parent : forall {p}, DirectExprUseRef p -> NodeRef p.
Parameter direct_child  : forall {p}, DirectExprUseRef p -> ExprRef p.
Parameter direct_role   : forall {p}, DirectExprUseRef p -> Role.
Parameter direct_is_expr_child : forall {p} (u : DirectExprUseRef p), ExprChildRole (direct_role u).
Parameter direct_occupies : forall {p} (u : DirectExprUseRef p),
  OccupiesRole (direct_parent u) (expr_node (direct_child u)) (direct_role u).
Parameter application_head_use : forall {p}, ApplicationRef p -> DirectExprUseRef p.
Parameter application_argument_uses : forall {p}, ApplicationRef p -> list (DirectExprUseRef p).
Parameter unary_operand_use : forall {p}, UnaryRef p -> DirectExprUseRef p.
Parameter NameAtPosition : forall {p}, ConstSpecRef p -> BindingNameRef p -> nat -> Prop.

Parameter SpecInDecl : forall {p}, ConstDeclRef p -> ConstSpecRef p -> Prop.
Parameter NearestPrecedingExplicit :
  forall {p}, ConstDeclRef p -> ConstSpecRef p -> ConstSpecRef p -> Prop.
Parameter ExprAtPosition : forall {p}, ConstSpecRef p -> ExprRef p -> nat -> Prop.
Parameter SpecTypeUse : forall {p}, ConstSpecRef p -> option (TypeUseRef p) -> Prop.
Parameter StructuralIota : forall {p}, ConstSpecRef p -> nat -> Prop.

Record InheritedConstUseRef (p : SyntaxProgram) : Type := MakeInheritedConstUse {
  ic_decl        : ConstDeclRef p;
  ic_current     : ConstSpecRef p;
  ic_predecessor : ConstSpecRef p;
  ic_name        : BindingNameRef p;
  ic_expr        : ExprRef p;
  ic_type        : option (TypeUseRef p);
  ic_position    : nat;
  ic_iota        : nat;
  ic_current_in_decl    : SpecInDecl ic_decl ic_current;
  ic_pred_in_decl       : SpecInDecl ic_decl ic_predecessor;
  ic_pred_is_nearest    : NearestPrecedingExplicit ic_decl ic_current ic_predecessor;
  ic_name_at_position   : NameAtPosition ic_current ic_name ic_position;
  ic_expr_at_position   : ExprAtPosition ic_predecessor ic_expr ic_position;
  ic_type_is_predecessors : SpecTypeUse ic_predecessor ic_type;
  ic_iota_is_structural : StructuralIota ic_current ic_iota
}.

Inductive ExprUseRef (p : SyntaxProgram) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.

Definition expression_of_use {p} (u : ExprUseRef p) : ExprRef p :=
  match u with DirectUse _ d => direct_child d | InheritedUse _ i => ic_expr p i end.

Inductive UseRefinement : Type := HeadRefinement | StatementRefinement | ResultRefinement.

Definition refinement_of_child_role {r : Role} (h : ExprChildRole r) : UseRefinement :=
  match h with
  | ECApplicationHead  => HeadRefinement
  | ECStatement        => StatementRefinement
  | ECConstInitializer | ECVarInitializer | ECShortRight | ECUnaryOperand | ECApplicationArg =>
      ResultRefinement
  end.

Definition use_refinement {p} (u : ExprUseRef p) : UseRefinement :=
  match u with
  | DirectUse _ d    => refinement_of_child_role (direct_is_expr_child d)
  | InheritedUse _ _ => ResultRefinement
  end.

(* ── Typing: named predeclared identities over a form algebra ──────────────── *)
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic (k : IntegerKind) | FloatBasic (k : Float.Kind)
| ComplexBasic (k : Complex.Kind) | StringBasic.

Inductive PredeclaredBasicType : Type :=
| TBool
| TInt | TInt8 | TInt16 | TInt32 | TInt64
| TUint | TUint8 | TUint16 | TUint32 | TUint64
| TFloat32 | TFloat64 | TComplex64 | TComplex128 | TString.

Definition predeclared_basic_form (t : PredeclaredBasicType) : BasicType :=
  match t with
  | TBool => BoolBasic
  | TInt => IntegerBasic IKInt | TInt8 => IntegerBasic IKInt8 | TInt16 => IntegerBasic IKInt16
  | TInt32 => IntegerBasic IKInt32 | TInt64 => IntegerBasic IKInt64
  | TUint => IntegerBasic IKUint | TUint8 => IntegerBasic IKUint8 | TUint16 => IntegerBasic IKUint16
  | TUint32 => IntegerBasic IKUint32 | TUint64 => IntegerBasic IKUint64
  | TFloat32 => FloatBasic F32 | TFloat64 => FloatBasic F64
  | TComplex64 => ComplexBasic C64 | TComplex128 => ComplexBasic C128
  | TString => StringBasic
  end.

Inductive ScalarNumericBasic : BasicType -> Prop :=
| SNInteger : forall k, ScalarNumericBasic (IntegerBasic k)
| SNFloat   : forall k, ScalarNumericBasic (FloatBasic k).
Inductive ComplexBasicForm : BasicType -> Prop :=
| CBComplex : forall k, ComplexBasicForm (ComplexBasic k).
Inductive FloatBasicForm : BasicType -> Prop :=
| FBFloat : forall k, FloatBasicForm (FloatBasic k).

(* §5: the complete predeclared type bridge, as one closed definition. *)
Inductive PredeclaredTypeRole : Type :=
| NamedBasic : PredeclaredBasicType -> PredeclaredTypeRole
| AliasOf    : PredeclaredBasicType -> PredeclaredTypeRole
| NoTypeMeaning : PredeclaredTypeRole.

Definition predeclared_type_role (n : PredeclaredName) : PredeclaredTypeRole :=
  match n with
  | PBool => NamedBasic TBool
  | PInt => NamedBasic TInt | PInt8 => NamedBasic TInt8 | PInt16 => NamedBasic TInt16
  | PInt32 => NamedBasic TInt32 | PInt64 => NamedBasic TInt64
  | PUint => NamedBasic TUint | PUint8 => NamedBasic TUint8 | PUint16 => NamedBasic TUint16
  | PUint32 => NamedBasic TUint32 | PUint64 => NamedBasic TUint64
  | PFloat32 => NamedBasic TFloat32 | PFloat64 => NamedBasic TFloat64
  | PComplex64 => NamedBasic TComplex64 | PComplex128 => NamedBasic TComplex128
  | PString => NamedBasic TString
  | PByte => AliasOf TUint8
  | PRune => AliasOf TInt32
  | PAny | PComparable | PError | PUintptr => NoTypeMeaning
  | PTrue | PFalse | PIota | PNil | PAppend | PCap | PClear | PClose | PComplex | PCopy
  | PDelete | PImag | PLen | PMake | PMax | PMin | PNew | PPanic | PPrint | PPrintln
  | PReal | PRecover => NoTypeMeaning
  end.

Definition AdmittedPredeclaredType (n : PredeclaredName) (t : PredeclaredBasicType) : Prop :=
  predeclared_type_role n = NamedBasic t.
Definition AliasPredeclared (n : PredeclaredName) (t : PredeclaredBasicType) : Prop :=
  predeclared_type_role n = AliasOf t.

Inductive Constant : Type :=
| BoolConstant    : bool -> Constant
| IntegerConstant : Z -> Constant
| FloatConstant   : Decimal -> Constant
| ComplexConstant : Decimal -> Decimal -> Constant
| StringConstant  : string -> Constant.

Parameter literal_constant : forall {p}, LiteralRef p -> Constant.

Inductive UntypedConstantKind : Type := UCBool | UCInteger | UCFloat | UCComplex | UCString.
Definition constant_kind (c : Constant) : UntypedConstantKind :=
  match c with
  | BoolConstant _ => UCBool | IntegerConstant _ => UCInteger | FloatConstant _ => UCFloat
  | ComplexConstant _ _ => UCComplex | StringConstant _ => UCString
  end.

Definition NumericConstantKind (k : UntypedConstantKind) : Prop :=
  k = UCInteger \/ k = UCFloat \/ k = UCComplex.

(* §5: default types, closed. *)
Definition default_basic (k : UntypedConstantKind) : PredeclaredBasicType :=
  match k with
  | UCBool => TBool | UCInteger => TInt | UCFloat => TFloat64
  | UCComplex => TComplex128 | UCString => TString
  end.

Inductive NumericBasic : BasicType -> Prop :=
| NBScalar  : forall b, ScalarNumericBasic b -> NumericBasic b
| NBComplex : forall b, ComplexBasicForm b -> NumericBasic b.

(* Float.Kind already owns the two float forms; no second carrier is minted. *)
Definition float_named_basic (f : Float.Kind) : PredeclaredBasicType :=
  match f with F32 => TFloat32 | F64 => TFloat64 end.
Definition complex_named_basic (f : Float.Kind) : PredeclaredBasicType :=
  match f with F32 => TComplex64 | F64 => TComplex128 end.

(* Exact constant arithmetic: every rule computes its result rather than being handed one. *)
Parameter negate_constant : Constant -> option Constant.
Parameter complex_of_constants : Constant -> Constant -> option Constant.

(* The one constant-conversion authority, over the destination underlying form. *)
Parameter convert_constant_to : BasicType -> Constant -> option Constant.
Definition FitsBasic (b : BasicType) (c : Constant) : Prop :=
  exists c', convert_constant_to b c = Some c'.

Inductive BasicTypedConstant : BasicType -> Type :=
| TCBool    : bool -> BasicTypedConstant BoolBasic
| TCInteger : forall k z, IntegerRepresentable k z -> BasicTypedConstant (IntegerBasic k)
| TCFloat   : forall k, Float.TypedConstant k -> BasicTypedConstant (FloatBasic k)
| TCComplex : forall k, Complex.TypedConstant k -> BasicTypedConstant (ComplexBasic k)
| TCString  : string -> BasicTypedConstant StringBasic.

Inductive TypeView : Type :=
| PredeclaredView : PredeclaredBasicType -> TypeView
| DefinedView     : IndexKey -> TypeView.

Inductive RawTypeTarget (p : SyntaxProgram) : Type :=
| RawPredeclared : PredeclaredName -> RawTypeTarget p
| RawAlias       : AliasSpecRef p -> RawTypeTarget p
| RawDefined     : BoundDefinedTypeRef p -> RawTypeTarget p.

(* The equation set is named here so the phase can carry it; the graph over it is the type layer. *)
Parameter ResolvedTypeEquations : SyntaxProgram -> Type.

(* The value a typed constant carries, so the typed computations below can be pinned to the untyped
   constant authorities rather than being free to return anything. *)
Parameter basic_typed_value : forall b : BasicType, BasicTypedConstant b -> Constant.

(* Negation and the untyped-to-typed step on the exact basic value, so a rule computes its result from its
   operand instead of accepting an unrelated one. *)
Parameter negate_basic_typed : forall b : BasicType,
  BasicTypedConstant b -> option (BasicTypedConstant b).
Parameter basic_typed_of : forall b : BasicType, Constant -> option (BasicTypedConstant b).

(* The one authority for combining two floating values of the same kind into the complex constant of the
   matching kind.  A `complex` rule computes its result through this, never accepting one. *)
Parameter complex_typed_of : forall f : Float.Kind,
  BasicTypedConstant (predeclared_basic_form (float_named_basic f)) ->
  BasicTypedConstant (predeclared_basic_form (float_named_basic f)) ->
  option (BasicTypedConstant (predeclared_basic_form (complex_named_basic f))).

(* ── The one retained static phase ─────────────────────────────────────────── *)
Parameter Phase : forall {p}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter phase_equations : forall {p} {i : Input p} (ph : Phase i), ResolvedTypeEquations p.

(* ── Objects ───────────────────────────────────────────────────────────────── *)
Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Inductive ObjectOrigin (p : SyntaxProgram) : Type :=
| Predeclared : PredeclaredName -> ObjectOrigin p
| SourceSite  : ObjectSiteRef p -> ObjectOrigin p.

Inductive ObjectKey : Type :=
| PredeclaredObjectKey : PredeclaredName -> ObjectKey
| SourceObjectKey      : IndexKey -> ObjectKey.

Definition origin_key {p} (o : ObjectOrigin p) : ObjectKey :=
  match o with
  | Predeclared _ n => PredeclaredObjectKey n
  | SourceSite _ s  => SourceObjectKey (object_site_key s)
  end.

Parameter ObjectRef : forall {p} {i : Input p}, Phase i -> Type.
Parameter object_origin : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectOrigin p.
Parameter object_eqb : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectRef ph -> bool.
Parameter predeclared_object : forall {p} {i : Input p} (ph : Phase i), PredeclaredName -> ObjectRef ph.
Parameter source_object : forall {p} {i : Input p} (ph : Phase i), ObjectSiteRef p -> ObjectRef ph.

Definition object_key {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : ObjectKey :=
  origin_key (object_origin o).

(* ObjectKind is a proof-free diagnostic view only. *)
Definition predeclared_kind (n : PredeclaredName) : ObjectKind :=
  match n with
  | PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError | PFloat32 | PFloat64
  | PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString | PUint | PUint8 | PUint16
  | PUint32 | PUint64 | PUintptr => TypeObject
  | PTrue | PFalse | PIota => ConstantObject
  | PNil => NilObject
  | PAppend | PCap | PClear | PClose | PComplex | PCopy | PDelete | PImag | PLen | PMake
  | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal | PRecover => BuiltinObject
  end.

Parameter object_kind : forall {p} {i : Input p} {ph : Phase i}, ObjectRef ph -> ObjectKind.

(* ── Erased, proof-free views ──────────────────────────────────────────────── *)
Inductive ErasedAnchor : Type :=
| EAtNode : IndexKey -> ErasedAnchor
| EAtFile : IndexKey -> ErasedAnchor
| EAtPackage : string -> ErasedAnchor
| EAtProgram : ErasedAnchor.

Inductive ContextualResult : Type := IotaResult | NilResult.

(* The exact C6 capability each predeclared name carries; every other name has an exact missing rule. *)
Inductive PredeclaredCapability : Type :=
| CapNamedType : PredeclaredBasicType -> PredeclaredCapability
| CapAliasType : PredeclaredBasicType -> PredeclaredCapability
| CapUntypedBool : bool -> PredeclaredCapability
| CapContextual : ContextualResult -> PredeclaredCapability
| CapCallable : PredeclaredCapability
| CapMissing : PredeclaredCapability.

Definition predeclared_capability (n : PredeclaredName) : PredeclaredCapability :=
  match predeclared_type_role n with
  | NamedBasic t => CapNamedType t
  | AliasOf t => CapAliasType t
  | NoTypeMeaning =>
      match n with
      | PTrue => CapUntypedBool true
      | PFalse => CapUntypedBool false
      | PIota => CapContextual IotaResult
      | PNil => CapContextual NilResult
      | PComplex | PPrintln => CapCallable
      | _ => CapMissing
      end
  end.

Inductive ErasedAtom : Type :=
| EAUntyped : UntypedConstantKind -> ErasedAtom
| EATyped   : TypeView -> ErasedAtom
| EAValue   : TypeView -> ErasedAtom.

Inductive ErasedResultForm : Type :=
| ERFixed        : list ErasedAtom -> ErasedResultForm
| ERContextual   : ContextualResult -> ErasedResultForm
| ERNoStandalone : ErasedResultForm.

Definition ErasedProfile : Type := list ErasedResultForm.

Inductive ErasedTarget : Type :=
| ETConversion    : TypeView -> ErasedTarget
| ETCallable      : PredeclaredName -> ErasedTarget
| ETNotApplicable : ErasedTarget.

(* §9: one proof-free requirement view for erasure, display, equality, order and key. *)
Inductive RequirementView : Type :=
| RVTypeMeaning  : ObjectKey -> RequirementView
| RVValueMeaning : ObjectKey -> RequirementView
| RVApplication  : ErasedTarget -> ErasedProfile -> RequirementView
| RVStatement    : ErasedTarget -> RequirementView
| RVUnary        : ErasedResultForm -> RequirementView.

Parameter requirement_view_eqb : RequirementView -> RequirementView -> bool.
Parameter requirement_view_compare : RequirementView -> RequirementView -> comparison.
Definition view_lt (a b : RequirementView) : Prop := requirement_view_compare a b = Lt.

(* ── Package identity: a compiler grouping, not a source occurrence ─────────── *)
(* A package spans files and has no single source occurrence, so its identity is the exact package-directory
   key the compiler already owns.  It is never an `Index` key. *)

(* ── The exact site universe ───────────────────────────────────────────────── *)
Inductive Site (p : SyntaxProgram) : Type :=
| SBinding     : NameUseRef p -> Site p
| SExpression  : ExprRef p -> Site p
| SUse         : ExprUseRef p -> Site p
| SStatement   : ExpressionStatementRef p -> Site p
| SConsumption : ConsumptionSiteRef p -> Site p
| SDeclaration : ObjectEstablisher p -> Site p
| SDependency  : PackageRef p -> Site p.

(* §10 Dependency causality is closed: a blocked site names exactly why it is blocked. *)


(* ── Erased payload views ──────────────────────────────────────────────────── *)
Inductive OperandResultView : Type :=
| ORUntyped : UntypedConstantKind -> OperandResultView
| ORTyped   : TypeView -> OperandResultView
| ORValue   : TypeView -> OperandResultView.

Inductive HeadView : Type :=
| HVObject : ObjectKey -> ObjectKind -> HeadView
| HVValue  : TypeView -> HeadView.

Inductive ArgumentReason : Type :=
| ArgWrongCount       : nat -> nat -> ArgumentReason
| ArgNotAssignable    : OperandResultView -> TypeView -> ArgumentReason
| ArgNotRepresentable : UntypedConstantKind -> TypeView -> ArgumentReason
| ArgProfileRejected  : ErasedProfile -> ArgumentReason.

Inductive OperandReason : Type :=
| OperandNotNumeric : OperandResultView -> OperandReason
| OperandNoResult   : ErasedResultForm -> OperandReason.

Inductive StatementReason : Type :=
| NotAnApplication        : ErasedResultForm -> StatementReason
| BuiltinNotAStatement    : PredeclaredName -> StatementReason
| ConversionNotAStatement : TypeView -> StatementReason.

(* The predeclared builtins pinned `gc` rejects in statement position.  Confirmed with nonconstant
   arguments, so the rejection is the statement-context rule and not constant folding.  Callability alone is
   not eligibility: `complex` is callable and still cannot stand as a statement. *)
Definition builtin_forbidden_as_statement (n : PredeclaredName) : bool :=
  match n with
  | PAppend | PCap | PComplex | PImag | PLen | PMake | PNew | PReal | PMin | PMax => true
  | _ => false
  end.

Inductive ConstInitReason : Type :=
| ConstInitValue      : TypeView -> ConstInitReason
| ConstInitNoResult   : ErasedResultForm -> ConstInitReason
| ConstInitWrongArity : nat -> nat -> ConstInitReason.

Inductive ContextReason : Type :=
| IotaOutsideConstSpec : ContextReason
| NilWithNoTarget      : ContextReason
| PackageInitNotAFunc  : ContextReason.

(* ── §13 Anchors and stable codes ──────────────────────────────────────────── *)
Inductive DiagnosticAnchor (p : SyntaxProgram) : Type :=
| AtNode    : NodeRef p -> DiagnosticAnchor p
| AtFile    : FileRef p -> DiagnosticAnchor p
| AtPackage : PackageRef p -> DiagnosticAnchor p
| AtProgram : DiagnosticAnchor p.

Inductive DiagnosticCode : Type :=
| CodeUnresolvedName | CodeDuplicateDeclaration | CodeUnusedLocal
| CodeArgument | CodeOperand | CodeNotAStatement | CodeResultCount
| CodeNotAssignable | CodeNotRepresentable | CodeConstInitializerNotConstant
| CodeNoNewVariable | CodeTypeCycle | CodeInitializationCycle | CodeContext
| CodeInvalidConversion | CodeDefaultNotRepresentable
| CodeMainRedeclared | CodeMissingMainEntry | CodeBuildOutputIsDirectory.
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


(* ── The retained type-phase result ────────────────────────────────────────── *)
(* Two branches, not because there are two outcomes but because acyclicity is the only question the graph
   itself answers.  An acyclic phase whose nodes fail, are outside C6 scope, or are blocked is represented
   here exactly as well as a ready one: readiness is a property of the node table, not a third branch.
   `type U uintptr; type T U` is acyclic and never ready, and this result represents it. *)
Inductive TypePhaseResult {p} {i : Input p} (ph : Phase i) : Type :=
| PhaseCyclic  : TypeCycle (phase_equations ph) -> TypePhaseResult ph
| PhaseAcyclic : AcyclicEquations (phase_equations ph) -> TypePhaseResult ph.

Definition IsTypeReady {p} {i : Input p} {ph : Phase i} (res : TypePhaseResult ph) : Prop :=
  match res with
  | PhaseCyclic _ _ => False
  | PhaseAcyclic _ acyc => forall n : TypeNode p, NodeIsSupported (node_outcome ph acyc n)
  end.

Definition ready_of {p} {i : Input p} {ph : Phase i} (res : TypePhaseResult ph)
  : IsTypeReady res -> TypeReady ph :=
  match res return IsTypeReady res -> TypeReady ph with
  | PhaseCyclic _ _ => fun h => match h return TypeReady ph with end
  | PhaseAcyclic _ acyc => fun h => @MakeTypeReady p i ph acyc h
  end.

Parameter phase_type_result : forall {p} {i : Input p} (ph : Phase i), TypePhaseResult ph.

(* ── §6 Total object descriptor ────────────────────────────────────────────── *)
Inductive SourceCategory : Type :=
| CatConst | CatVar | CatAlias | CatDefined | CatFunc.

Definition object_site_category {p} (s : ObjectSiteRef p) : SourceCategory :=
  match object_site_view s with
  | OSConst _   => CatConst
  | OSVar _     => CatVar
  | OSAlias _   => CatAlias
  | OSDefined _ => CatDefined
  | OSMain _    => CatFunc
  end.

Definition object_spelling {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : string :=
  match object_origin o with
  | Predeclared _ n => predeclared_spelling n
  | SourceSite _ s  => object_site_spelling s
  end.

Definition object_scope {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : ScopeId p :=
  match object_origin o with
  | Predeclared _ _ => PredeclaredScope p
  | SourceSite _ s  => object_site_scope s
  end.

(* ObjectKind is derived from origin/category. *)
Definition object_kind_of {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : ObjectKind :=
  match object_origin o with
  | Predeclared _ n => predeclared_kind n
  | SourceSite _ s  => match object_site_category s with
    | CatConst => ConstantObject | CatVar => VariableObject
    | CatAlias | CatDefined => TypeObject | CatFunc => FunctionObject
    end
  end.

(* ── §6 Successful semantic meaning is partial ────────────────────────────── *)
Inductive TypeMeaning {p} {i : Input p} (ph : Phase i)
  : ObjectRef ph -> Type :=
| TMPredeclared : forall n t, AdmittedPredeclaredType n t ->
    TypeMeaning ph (predeclared_object ph n)
| TMPredeclaredAlias : forall n t, AliasPredeclared n t ->
    TypeMeaning ph (predeclared_object ph n)
| TMAlias : forall (a : AliasSpecRef p) (rhs : SemanticType p),
    TypeMeaning ph (source_object ph (alias_object_site a))
| TMDefined : forall (d : BoundDefinedTypeRef p),
    TypeMeaning ph (source_object ph (defined_object_site d)).

Definition type_meaning_type {p} {i : Input p} {ph : Phase i} {o}
  (m : TypeMeaning ph o) : SemanticType p :=
  match m with
  | TMPredeclared _ _ t _      => PredeclaredType p t
  | TMPredeclaredAlias _ _ t _ => PredeclaredType p t
  | TMAlias _ _ rhs            => rhs
  | TMDefined _ d              => DefinedType p d
  end.

Inductive DeclaredConstant {p} {i : Input p} (ph : Phase i)  : Type :=
| DeclaredUntyped : Constant -> DeclaredConstant ph
| DeclaredTyped   : forall t : SemanticType p, TypedConstant ph t -> DeclaredConstant ph.

Parameter ConstantDeclarationFact : forall {p} {i : Input p} (ph : Phase i),
  ObjectEstablisher p -> Type.
Parameter constant_declared : forall {p} {i : Input p} {ph : Phase i} {s},
  ConstantDeclarationFact ph s -> DeclaredConstant ph.

Parameter VariableDeclarationFact : forall {p} {i : Input p} (ph : Phase i),
  ObjectEstablisher p -> Type.
Parameter variable_declared_type : forall {p} {i : Input p} {ph : Phase i} {s},
  VariableDeclarationFact ph s -> SemanticType p.

Inductive ConstantMeaning {p} {i : Input p} (ph : Phase i)
  : ObjectRef ph -> Type :=
| CMPredeclaredBool : forall n b, predeclared_capability n = CapUntypedBool b ->
    ConstantMeaning ph (predeclared_object ph n)
| CMDeclared : forall (c : ConstSpecRef p)
    (est : ObjectEstablisher p) (df : ConstantDeclarationFact ph est),
    ConstantMeaning ph (source_object ph (const_object_site c)).

Record StaticVariable {p} {i : Input p} (ph : Phase i)
  (o : ObjectRef ph) : Type := MakeStaticVariable {
  static_var_site    : VariableSiteRef p;
  static_est         : ObjectEstablisher p;
  static_decl        : VariableDeclarationFact ph static_est;
  static_is_its_site : object_origin o = SourceSite p (establisher_site static_est)
}.

Definition static_type {p} {i : Input p} {ph : Phase i} {o}
  (sv : StaticVariable ph o) : SemanticType p :=
  variable_declared_type (static_decl ph o sv).

Definition static_object_site {p} {i : Input p} {ph : Phase i} {o}
  (sv : StaticVariable ph o) : ObjectSiteRef p :=
  var_object_site (static_var_site ph o sv).

Inductive CallableMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| CallComplex : CallableMeaning ph (predeclared_object ph PComplex)
| CallPrintln : CallableMeaning ph (predeclared_object ph PPrintln).

Inductive IotaMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| IotaIs : IotaMeaning ph (predeclared_object ph PIota).

Inductive NilMeaning {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| NilIs : NilMeaning ph (predeclared_object ph PNil).

Inductive ObjectMeaning {p} {i : Input p} (ph : Phase i)
  (o : ObjectRef ph) : Type :=
| MeaningType     : TypeMeaning ph o -> ObjectMeaning ph o
| MeaningConstant : ConstantMeaning ph o -> ObjectMeaning ph o
| MeaningVariable : StaticVariable ph o -> ObjectMeaning ph o
| MeaningCallable : CallableMeaning ph o -> ObjectMeaning ph o
| MeaningIota     : IotaMeaning ph o -> ObjectMeaning ph o
| MeaningNil      : NilMeaning ph o -> ObjectMeaning ph o.

(* §7 Exact role decisions over the object descriptor and the use role.  Wrong role is a definite error,
   not a capability bucket.  A type used as a value is wrong-role, not "value capable".  A callable alone
   has no standalone value.  `iota` and `nil` are contextual, not ordinary values. *)
Inductive TypeRoleResult {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| TypeRoleAdmitted : forall o, TypeRoleResult ph o
| TypeRoleMissing  : forall o, TypeRoleResult ph o
| TypeRoleWrong    : forall o, TypeRoleResult ph o.

Inductive ValueRoleResult {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| ValueRoleConstant    : forall o, ValueRoleResult ph o
| ValueRoleVariable    : forall o, ValueRoleResult ph o
| ValueRoleContextual  : forall o, ValueRoleResult ph o
| ValueRoleMissing     : forall o, ValueRoleResult ph o
| ValueRoleWrong       : forall o, ValueRoleResult ph o.

Inductive HeadRoleResult {p} {i : Input p} (ph : Phase i) : ObjectRef ph -> Type :=
| HeadRoleType     : forall o, HeadRoleResult ph o
| HeadRoleCallable : forall o, HeadRoleResult ph o
| HeadRoleMissing  : forall o, HeadRoleResult ph o
| HeadRoleWrong    : forall o, HeadRoleResult ph o.

Parameter type_role_decision : forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph),
  TypeRoleResult ph o.
Parameter value_role_decision : forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph),
  ValueRoleResult ph o.
Parameter head_role_decision : forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph),
  HeadRoleResult ph o.

(* Backward compatibility: the requirements still reference these until §13 rewrites them. *)
Definition HasTypeCapability {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : Prop :=
  match type_role_decision ph o with TypeRoleAdmitted _ _ => True | _ => False end.

Definition HasValueCapability {p} {i : Input p} {ph : Phase i} (o : ObjectRef ph) : Prop :=
  match value_role_decision ph o with
  | ValueRoleConstant _ _ | ValueRoleVariable _ _ | ValueRoleContextual _ _ => True
  | _ => False
  end.

(* ── §5 The expression-fact algebra ────────────────────────────────────────── *)
(* One sealed dependent judgment. A failed, outside or blocked expression has no `ExprFact` at all — it has
  the corresponding exact site outcome. Every family below is indexed by the exact result it computes, so
  the result is never a field a constructor could be handed. *)

(* Result atoms over the retained phase, so every rule can compute its own vector. *)
Inductive ResultAtomAt {p} {i : Input p} (ph : Phase i)
  : Type :=
| RAUntyped : Constant -> ResultAtomAt ph
| RATyped  : forall t : SemanticType p, TypedConstant ph t -> ResultAtomAt ph
| RAValue  : SemanticType p -> ResultAtomAt ph.

Inductive ResultFormAt {p} {i : Input p} (ph : Phase i)
  : Type :=
| RFFixed    : list (ResultAtomAt ph) -> ResultFormAt ph
| RFContextual  : ContextualResult -> ResultFormAt ph
| RFNoStandalone : ResultFormAt ph.

(* The result a bound name yields is decided by its one exact meaning, not supplied beside it. A type or
  callable name has no standalone result; `iota` and `nil` are contextual and resolved at the exact use. *)
Definition name_result {p} {i : Input p} {ph : Phase i} {o}
 (m : ObjectMeaning ph o) : ResultFormAt ph :=
 match m with
 | MeaningConstant _ _ cm =>
   match cm with
   | CMPredeclaredBool _ _ b _ => RFFixed ph [RAUntyped ph (BoolConstant b)]
   | CMDeclared _ _ _ df =>
     match constant_declared df with
     | DeclaredUntyped _ k => RFFixed ph [RAUntyped ph k]
     | DeclaredTyped _ t tc => RFFixed ph [RATyped ph t tc]
     end
   end
 | MeaningVariable _ _ sv => RFFixed ph [RAValue ph (static_type sv)]
 | MeaningIota _ _ _ => RFContextual ph IotaResult
 | MeaningNil _ _ _ => RFContextual ph NilResult
 | MeaningType _ _ _ => RFNoStandalone ph
 | MeaningCallable _ _ _ => RFNoStandalone ph
 end.

(* Atom builders, so the `complex` cases below read as rules rather than as record plumbing. *)
Definition float_atom_typed {p} {i : Input p} {ph : Phase i}
 (t : SemanticType p) (f : Float.Kind)
 (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
 (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
 : ResultAtomAt ph :=
 RATyped ph t (@MakeTypedConstant p i ph t _ hu v).

Definition complex_atom_typed {p} {i : Input p} {ph : Phase i} (f : Float.Kind)
 (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f)))
 : ResultAtomAt ph :=
 RATyped ph (PredeclaredType p (complex_named_basic f))
  (@MakeTypedConstant p i ph (PredeclaredType p (complex_named_basic f)) _
   (UnderlyingPredeclared ph (complex_named_basic f)) vr).

Definition complex_atom_value {p} {i : Input p} {ph : Phase i} (f : Float.Kind)
 : ResultAtomAt ph :=
 RAValue ph (PredeclaredType p (complex_named_basic f)).

(* ── The rule-coverage relations ───────────────────────────────────────────── *)
(* These are the one authority for "C6 has a rule for operands of this exact shape". The rule families
  below carry a coverage witness rather than restating its premises, and a requirement's satisfaction is
  stated over these — never over whether the successful fact happens to be inhabited. *)
Inductive UnaryRuleCovers {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> Prop :=
| URUntyped : forall c, NumericConstantKind (constant_kind c) ->
  UnaryRuleCovers (RAUntyped ph c)
| URTyped : forall t tc b, Underlying ph t b -> NumericBasic b ->
  UnaryRuleCovers (RATyped ph t tc)
| URValue : forall t b, Underlying ph t b -> NumericBasic b ->
  UnaryRuleCovers (RAValue ph t).

(* `println` admits an argument whose underlying form exists; an untyped constant is defaulted first. *)
Inductive PrintlnArg {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> Prop :=
| PAUntyped : forall c, Representable ph (default_type (constant_kind c)) c ->
  PrintlnArg (RAUntyped ph c)
| PATyped  : forall t tc b, Underlying ph t b -> PrintlnArg (RATyped ph t tc)
| PAValue  : forall t b, Underlying ph t b -> PrintlnArg (RAValue ph t).

Definition PrintlnRuleCovers {p} {i : Input p} {ph : Phase i}
 (args : list (ResultAtomAt ph)) : Prop := List.Forall (PrintlnArg ) args.

Inductive ConvRuleCovers {p} {i : Input p} {ph : Phase i}
 : SemanticType p -> ResultAtomAt ph -> Prop :=
| CCConstant : forall dst b c, Underlying ph dst b ->
  (exists c', convert_constant_to b c = Some c') ->
  ConvRuleCovers dst (RAUntyped ph c)
| CCTypedConstant : forall dst src (tc : TypedConstant ph src),
    ValueConvertible ph src dst -> ConvRuleCovers dst (RATyped ph src tc)
| CCValue : forall dst src, ValueConvertible ph src dst ->
  ConvRuleCovers dst (RAValue ph src).

(* A floating operand of an exact kind, constant or not: what the `complex` combinations quantify over. *)
Inductive FloatOperand {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> Float.Kind -> Prop :=
| FOTyped : forall t tc f, Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  FloatOperand (RATyped ph t tc) f
| FOValue : forall t f, Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  FloatOperand (RAValue ph t) f.

Inductive ComplexRuleCovers {p} {i : Input p} {ph : Phase i}
 : ResultAtomAt ph -> ResultAtomAt ph -> Prop :=
| CxCBothUntyped : forall c1 c2,
  NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
  ComplexRuleCovers (RAUntyped ph c1) (RAUntyped ph c2)
| CxCUntypedLeft : forall c y f, NumericConstantKind (constant_kind c) -> FloatOperand y f ->
  ComplexRuleCovers (RAUntyped ph c) y
| CxCUntypedRight : forall x c f, FloatOperand x f -> NumericConstantKind (constant_kind c) ->
  ComplexRuleCovers x (RAUntyped ph c)
| CxCBothKinded : forall x y f, FloatOperand x f -> FloatOperand y f ->
  ComplexRuleCovers x y.

(* The application target, derived from the exact head rather than guessed from the argument count. *)
Inductive ApplicationTarget {p} {i : Input p} (ph : Phase i) : Type :=
| ConversionTarget : SemanticType p -> ApplicationTarget ph
| BuiltinTarget  : forall o : ObjectRef ph, CallableMeaning ph o -> ApplicationTarget ph
| NotApplicable  : HeadView -> ApplicationTarget ph.

(* Coverage is asked of the exact target, never of the arity alone. *)
Definition ApplicationRuleCovers {p} {i : Input p} {ph : Phase i}
 (tgt : ApplicationTarget ph) (args : list (ResultAtomAt ph)) : Prop :=
 match tgt with
 | ConversionTarget _ dst => exists a1, args = [a1] /\ ConvRuleCovers dst a1
 | BuiltinTarget _ o _ =>
   (o = predeclared_object ph PComplex /\
    exists a1 a2, args = [a1; a2] /\ ComplexRuleCovers a1 a2) \/
   (o = predeclared_object ph PPrintln /\ PrintlnRuleCovers args)
 | NotApplicable _ _ => False
 end.

(* Statement eligibility is `println` and nothing else: `complex` is callable and still cannot stand as a
  statement, which is why callability alone was never the right question. *)
Definition StatementRuleCovers {p} {i : Input p} (ph : Phase i) (a : ApplicationRef p) : Prop :=
 exists (hu : NameUseRef p) (bf : BindingFact ph hu),
  application_head a = name_use_expr hu /\
  bound_object ph hu bf = predeclared_object ph PPrintln.

(* A contextual expression is resolved at the exact use. `iota` takes the index of its own const spec.
  There is deliberately no `nil` constructor: pinned `gc` rejects `nil` in every C6-representable context,
  so a `nil` use produces its exact requirement or diagnostic and never a resolved atom. *)
Inductive ContextResolvesAt {p} {i : Input p} (ph : Phase i)
 : ExprUseRef p -> ContextualResult -> ResultAtomAt ph -> Prop :=
| IotaResolves : forall (ih : InheritedConstUseRef p),
  ContextResolvesAt ph (InheritedUse p ih) IotaResult
   (RAUntyped ph (IntegerConstant (Z.of_nat (ic_iota p ih)))).

Inductive ExprFact {p} {i : Input p} (ph : Phase i)
  : ExprRef p -> ResultFormAt ph -> Type :=
| EFLiteral : forall (l : LiteralRef p),
  ExprFact ph (literal_expr l) (RFFixed ph [RAUntyped ph (literal_constant l)])
| EFName : forall (u : NameUseRef p)
  (bf : BindingFact ph u) (m : ObjectMeaning ph (bound_object ph u bf)),
  ExprFact ph (name_use_expr u) (name_result m)
| EFUnary : forall (n : UnaryRef p)
  (opa : ResultAtomAt ph) (res : list (ResultAtomAt ph)),
  ResultUseFactAt ph (DirectUse p (unary_operand_use n)) opa ->
  UnaryFact ph n opa res ->
  ExprFact ph (unary_expr n) (RFFixed ph res)
| EFApplication : forall (a : ApplicationRef p)
  (hf : ResultFormAt ph) (res : list (ResultAtomAt ph)),
  ExprFact ph (application_head a) hf -> AppFact ph a res ->
  ExprFact ph (application_expr_of a) (RFFixed ph res)

(* §10 A result use selects exactly one atom BY CONSTRUCTION. A head or statement use cannot inhabit it,
  and neither can an expression whose form is contextual-unresolved or no-standalone. *)
with ResultUseFactAt {p} {i : Input p} (ph : Phase i)
  : ExprUseRef p -> ResultAtomAt ph -> Type :=
| RUFFixed : forall (u : ExprUseRef p) (a : ResultAtomAt ph),
  use_refinement u = ResultRefinement ->
  ExprFact ph (expression_of_use u) (RFFixed ph [a]) ->
  ResultUseFactAt ph u a
| RUFContextual : forall (u : ExprUseRef p) (cr : ContextualResult) (a : ResultAtomAt ph),
  use_refinement u = ResultRefinement ->
  ExprFact ph (expression_of_use u) (RFContextual ph cr) ->
  ContextResolvesAt ph u cr a ->
  ResultUseFactAt ph u a

(* §7.1 Argument facts are indexed by the EXACT ordered source use list and the exact ordered atoms they
  consume, so there is one fact per source argument, in source order, with no duplicate and no omission. *)
with ArgFacts {p} {i : Input p} (ph : Phase i)
  : list (DirectExprUseRef p) -> list (ResultAtomAt ph) -> Type :=
| ArgsNil : ArgFacts ph [] []
| ArgsCons : forall (u : DirectExprUseRef p) (rest : list (DirectExprUseRef p))
  (a : ResultAtomAt ph) (arest : list (ResultAtomAt ph)),
  ResultUseFactAt ph (DirectUse p u) a -> ArgFacts ph rest arest ->
  ArgFacts ph (u :: rest) (a :: arest)

(* §11 The unary rule is indexed by the exact operand atom and computes its result from it. There is no
  free input constant and no unrelated output typed constant. *)
with UnaryFact {p} {i : Input p} (ph : Phase i)
  : UnaryRef p -> ResultAtomAt ph -> list (ResultAtomAt ph) -> Type :=
| UFUntyped : forall (n : UnaryRef p) (c c' : Constant),
  UnaryRuleCovers (RAUntyped ph c) -> negate_constant c = Some c' ->
  UnaryFact ph n (RAUntyped ph c) [RAUntyped ph c']
| UFTypedConstant : forall (n : UnaryRef p) (t : SemanticType p) (b : BasicType)
  (hu : Underlying ph t b) (v v' : BasicTypedConstant b),
  UnaryRuleCovers (RATyped ph t (@MakeTypedConstant p i ph t b hu v)) ->
  negate_basic_typed b v = Some v' ->
  UnaryFact ph n
   (RATyped ph t (@MakeTypedConstant p i ph t b hu v))
   [RATyped ph t (@MakeTypedConstant p i ph t b hu v')]
| UFValue : forall (n : UnaryRef p) (t : SemanticType p),
  UnaryRuleCovers (RAValue ph t) ->
  UnaryFact ph n (RAValue ph t) [RAValue ph t]

(* Arity is a constructor constraint, not a separate theorem: a conversion demands a one-element source
  argument list and `complex` a two-element one, so a wrong-arity application cannot build a fact. *)
with AppFact {p} {i : Input p} (ph : Phase i)
  : ApplicationRef p -> list (ResultAtomAt ph) -> Type :=
(* The destination is the head's own type meaning, not a free type beside it. *)
| AFConversion : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
  (tm : TypeMeaning ph (bound_object ph hu bf))
  (u : DirectExprUseRef p) (arg : ResultAtomAt ph) (res : list (ResultAtomAt ph)),
  application_head a = name_use_expr hu ->
  application_argument_uses a = [u] ->
  ArgFacts ph [u] [arg] ->
  ConvRule ph a (type_meaning_type tm) arg res -> AppFact ph a res
| AFComplex : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
  (u1 u2 : DirectExprUseRef p) (a1 a2 : ResultAtomAt ph)
  (res : list (ResultAtomAt ph)),
  application_head a = name_use_expr hu ->
  bound_object ph hu bf = predeclared_object ph PComplex ->
  application_argument_uses a = [u1; u2] ->
  ArgFacts ph [u1; u2] [a1; a2] -> ComplexRuleF ph a a1 a2 res -> AppFact ph a res
| AFPrintln : forall (a : ApplicationRef p) (hu : NameUseRef p) (bf : BindingFact ph hu)
  (args : list (ResultAtomAt ph)),
  application_head a = name_use_expr hu ->
  bound_object ph hu bf = predeclared_object ph PPrintln ->
  ArgFacts ph (application_argument_uses a) args ->
  PrintlnRuleF ph a args -> AppFact ph a []

(* §12.2 The conversion consumes the one exact argument atom and computes the exact result atom. *)
with ConvRule {p} {i : Input p} (ph : Phase i)

 : ApplicationRef p -> SemanticType p -> ResultAtomAt ph -> list (ResultAtomAt ph) -> Type :=
| CRConstant : forall (a : ApplicationRef p) (dst : SemanticType p) (b : BasicType)
  (hu : Underlying ph dst b) (c c' : Constant) (v : BasicTypedConstant b),
  convert_constant_to b c = Some c' -> basic_typed_of b c' = Some v ->
  ConvRule ph a dst (RAUntyped ph c) [RATyped ph dst (@MakeTypedConstant p i ph dst b hu v)]
| CRTypedConstant : forall (a : ApplicationRef p) (dst src : SemanticType p)
    (b_dst : BasicType) (hu_dst : Underlying ph dst b_dst)
    (tc : TypedConstant ph src) (tc' : TypedConstant ph dst),
    ValueConvertible ph src dst ->
    ConvRule ph a dst (RATyped ph src tc) [RATyped ph dst tc']
| CRValue : forall (a : ApplicationRef p) (dst src : SemanticType p),
    ValueConvertible ph src dst ->
    ConvRule ph a dst (RAValue ph src) [RAValue ph dst]

(* §12.3 `complex` consumes its two exact argument atoms. The result's constantness follows the operands'
  and its kind follows the exact floating kind they share. *)
with ComplexRuleF {p} {i : Input p} (ph : Phase i)

 : ApplicationRef p -> ResultAtomAt ph -> ResultAtomAt ph ->
  list (ResultAtomAt ph) -> Type :=
(* Two untyped numeric constants give an untyped complex constant. *)
| CxUntypedUntyped : forall (a : ApplicationRef p) (c1 c2 cr : Constant),
  NumericConstantKind (constant_kind c1) -> NumericConstantKind (constant_kind c2) ->
  complex_of_constants c1 c2 = Some cr ->
  ComplexRuleF ph a (RAUntyped ph c1) (RAUntyped ph c2) [RAUntyped ph cr]
(* One untyped constant with one typed floating constant: the untyped operand converts to the typed
  operand's exact kind, and the result is a typed complex constant of the matching kind. *)
| CxUntypedTypedL : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : Float.Kind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v vc : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
  NumericConstantKind (constant_kind c) ->
  basic_typed_of (predeclared_basic_form (float_named_basic f)) c = Some vc ->
  complex_typed_of f vc v = Some vr ->
  ComplexRuleF ph a (RAUntyped ph c) (float_atom_typed t f hu v)
   [complex_atom_typed f vr]
| CxUntypedTypedR : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : Float.Kind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v vc : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
  NumericConstantKind (constant_kind c) ->
  basic_typed_of (predeclared_basic_form (float_named_basic f)) c = Some vc ->
  complex_typed_of f v vc = Some vr ->
  ComplexRuleF ph a (float_atom_typed t f hu v) (RAUntyped ph c)
   [complex_atom_typed f vr]
(* One untyped constant with one floating value: the result is a value, not a constant. *)
| CxUntypedValueL : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : Float.Kind),
  NumericConstantKind (constant_kind c) ->
  Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  ComplexRuleF ph a (RAUntyped ph c) (RAValue ph t) [complex_atom_value f]
| CxUntypedValueR : forall (a : ApplicationRef p) (c : Constant) (t : SemanticType p) (f : Float.Kind),
  NumericConstantKind (constant_kind c) ->
  Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  ComplexRuleF ph a (RAValue ph t) (RAUntyped ph c) [complex_atom_value f]
(* Two typed floating constants of one identical type give a typed complex constant. *)
| CxTypedTyped : forall (a : ApplicationRef p) (t : SemanticType p) (f : Float.Kind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v1 v2 : BasicTypedConstant (predeclared_basic_form (float_named_basic f)))
  (vr : BasicTypedConstant (predeclared_basic_form (complex_named_basic f))),
  complex_typed_of f v1 v2 = Some vr ->
  ComplexRuleF ph a (float_atom_typed t f hu v1) (float_atom_typed t f hu v2)
   [complex_atom_typed f vr]
(* A typed floating constant with a floating value of the same type gives a value. *)
| CxTypedValueL : forall (a : ApplicationRef p) (t : SemanticType p) (f : Float.Kind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f))),
  ComplexRuleF ph a (float_atom_typed t f hu v) (RAValue ph t) [complex_atom_value f]
| CxTypedValueR : forall (a : ApplicationRef p) (t : SemanticType p) (f : Float.Kind)
  (hu : Underlying ph t (predeclared_basic_form (float_named_basic f)))
  (v : BasicTypedConstant (predeclared_basic_form (float_named_basic f))),
  ComplexRuleF ph a (RAValue ph t) (float_atom_typed t f hu v) [complex_atom_value f]
(* Two floating values of one identical type give a value. *)
| CxValues : forall (a : ApplicationRef p) (t : SemanticType p) (f : Float.Kind),
  Underlying ph t (predeclared_basic_form (float_named_basic f)) ->
  ComplexRuleF ph a (RAValue ph t) (RAValue ph t) [complex_atom_value f]

with PrintlnRuleF {p} {i : Input p} (ph : Phase i)
  : ApplicationRef p -> list (ResultAtomAt ph) -> Type :=
| PrFAdmitted : forall (a : ApplicationRef p) (args : list (ResultAtomAt ph)),
  PrintlnRuleCovers args -> PrintlnRuleF ph a args.

(* ── §5 The one remaining projection ───────────────────────────────────────── *)
(* `result_form` is now the index itself, so there is nothing left to project. Only the referenced object
  is a genuine view of the fact. *)
Definition expr_referenced_object {p} {i : Input p} {ph : Phase i} {r} {form}
 (f : ExprFact ph r form) : option (ObjectRef ph) :=
 match f with
 | EFName _ u bf _ => Some (bound_object ph u bf)
 | _ => None
 end.

(* ── §8 A statement fact exists only for an eligible statement ─────────────── *)
Definition IsPrintlnApp {p} {i : Input p} {ph : Phase i} {a} {res}
 (f : AppFact ph a res) : Prop :=
 match f with AFPrintln _ _ _ _ _ _ _ _ _ => True | _ => False end.

Definition IsConversionApp {p} {i : Input p} {ph : Phase i} {a} {res}
 (f : AppFact ph a res) : Prop :=
 match f with AFConversion _ _ _ _ _ _ _ _ _ _ _ _ => True | _ => False end.

Definition IsComplexApp {p} {i : Input p} {ph : Phase i} {a} {res}
 (f : AppFact ph a res) : Prop :=
 match f with AFComplex _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True | _ => False end.

Inductive StmtFact {p} {i : Input p} (ph : Phase i)
  : ExpressionStatementRef p -> Type :=
| SFPrintln : forall (s : ExpressionStatementRef p) (a : ApplicationRef p)
  (res : list (ResultAtomAt ph)) (f : AppFact ph a res),
  statement_application s = Some a -> IsPrintlnApp f -> StmtFact ph s.

Definition statement_application_of {p} {i : Input p} {ph : Phase i} {s}
 (f : StmtFact ph s) : ApplicationRef p :=
 match f with SFPrintln _ _ a _ _ _ _ => a end.

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

(* ── §9 Requirements are exact missing facts ───────────────────────────────── *)
(* Each constructor retains the exact partial facts already established at that site, so a requirement
   cannot pair an arbitrary use with an arbitrary object, and satisfaction never asks whether the outcome
   is already supported. *)
(* No environment index: a requirement is reportable for an arbitrary core.  Each constructor carries the
   exact readiness the partial facts it retains were established at. *)
Inductive SiteRequirement {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
(* The requirement retains the exact use, its exact binding, and thereby the exact bound object's total
   descriptor.  It does not retain a successful meaning: that is precisely what it reports as missing. *)
| NeedTypeMeaning : forall (u : NameUseRef p) (bf : BindingFact ph u),
    SiteRequirement ph (SBinding p u)
| NeedValueMeaning : forall (u : NameUseRef p) (bf : BindingFact ph u),
    SiteRequirement ph (SBinding p u)
(* §15 A missing application rule retains the exact head fact, the exact target derived from it, the exact
   ordered argument facts and the exact derived profile. *)
| NeedApplication : forall  (a : ApplicationRef p)
    (hf : ResultFormAt ph) (tgt : ApplicationTarget ph)
    (args : list (ResultAtomAt ph)),
    ExprFact ph (application_head a) hf ->
    ArgFacts ph (application_argument_uses a) args ->
    ErasedProfile -> SiteRequirement ph (SExpression p (application_expr_of a))
| NeedStatement : forall  (s : ExpressionStatementRef p) (a : ApplicationRef p)
    (hf : ResultFormAt ph),
    statement_application s = Some a ->
    ExprFact ph (application_head a) hf -> SiteRequirement ph (SStatement p s)
| NeedUnary : forall  (n : UnaryRef p) (opa : ResultAtomAt ph),
    ResultUseFactAt ph (DirectUse p (unary_operand_use n)) opa ->
    SiteRequirement ph (SExpression p (unary_expr n)).

(* Satisfaction is a question about the fact families, not about the site table. *)
(* Every case is a positive semantic relation over the exact facts the requirement retains.  None asks
   whether the successful site fact happens to be inhabited: that would decide whether a requirement is met
   by checking for the very thing the requirement reports as missing. *)
Definition RequirementSatisfied {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s) : Prop :=
  match r with
  | NeedTypeMeaning _ u bf =>
      match type_role_decision ph (bound_object ph u bf) with
      | TypeRoleAdmitted _ _ => True | _ => False end
  | NeedValueMeaning _ u bf =>
      match value_role_decision ph (bound_object ph u bf) with
      | ValueRoleConstant _ _ | ValueRoleVariable _ _ | ValueRoleContextual _ _ => True
      | _ => False end
  | NeedApplication _ _ _ tgt args _ _ _ => ApplicationRuleCovers tgt args
  | NeedStatement _ _ a _ _ _ => StatementRuleCovers ph a
  | NeedUnary _ _ opa _ => UnaryRuleCovers opa
  end.

Parameter requirement_dec : forall {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.

(* The exact bound object a name requirement is about is read off its binding fact, never supplied. *)
Definition requirement_object {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s) : option (ObjectRef ph) :=
  match r with
  | NeedTypeMeaning _ u bf => Some (bound_object ph u bf)
  | NeedValueMeaning _ u bf => Some (bound_object ph u bf)
  | _ => None
  end.

Parameter requirement_view : forall {p} {i : Input p} {ph : Phase i} {s},
  SiteRequirement ph s -> RequirementView.

(* ── §10 Site failures retain their exact causes ───────────────────────────── *)
(* The source witnesses a diagnostic must consume.  These are facts about the source and its bindings, not
   claims that Go rejects the program: two binders sharing a spelling in one scope IS the duplication, and a
   package-level declaration spelled `init` IS the reservation. *)
Definition ShortHasNoNewName {p} {i : Input p} (ph : Phase i) (d : ShortDeclRef p) : Prop :=
  forall (n : BindingNameRef p) (sp : string),
    short_lhs_decl n = Some d -> short_lhs_spelling n = sp ->
    match binder_fact ph n with
    | BFShortNew _ _ _ _ _ _ _ _ => False
    | _ => True
    end.

Definition NoReadOf {p} {i : Input p} (ph : Phase i) (v : VariableSiteRef p) : Prop :=
  forall (u : NameUseRef p) (bf : BindingFact ph u),
    bound_object ph u bf
      <> source_object ph (establisher_site (variable_site_establisher v)).

(* A duplicate declaration is a failure at the declaration site, not at some unrelated name use; an argument
   failure retains the exact argument use, not a free index; a consumption failure retains the exact
   occurrence, not a free position. *)
(* No environment index: a failed or cyclic core must be able to report why no environment exists.  The
   three cases that genuinely resolved a type carry the exact readiness they used. *)
Inductive SiteFailure {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
(* Unresolved consumes the complete decision: resolve_name returned None for this exact use. *)
| FUnresolvedName : forall (u : NameUseRef p),
    resolve_name ph u = None -> SiteFailure ph (SBinding p u)
(* A name bound to an object that cannot carry the role its use demands. *)
| FWrongRole : forall (u : NameUseRef p) (bf : BindingFact ph u),
    ~ HasValueCapability (bound_object ph u bf) ->
    ~ HasTypeCapability (bound_object ph u bf) ->
    SiteFailure ph (SBinding p u)
| FDuplicateDeclaration : forall earlier later : ObjectEstablisher p,
    DuplicateEstablishers earlier later -> SiteFailure ph (SDeclaration p later)
| FPackageInitReserved : forall b : ObjectEstablisher p,
    PackageInitReserved (establisher_context b) (establisher_spelling b) ->
    SiteFailure ph (SDeclaration p b)
| FNotAStatement : forall t : ExpressionStatementRef p, StatementReason ->
    SiteFailure ph (SStatement p t)
| FResultCountWrong : forall c : ConsumptionSiteRef p, nat -> nat ->
    SiteFailure ph (SConsumption p c)
| FNotAssignableAt : forall (c : ConsumptionSiteRef p)  (u : ExprUseRef p)
    (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> SemanticType p -> SiteFailure ph (SConsumption p c)
| FNotRepresentableAt : forall (c : ConsumptionSiteRef p)  (u : ExprUseRef p)
    (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> SemanticType p -> SiteFailure ph (SConsumption p c)
| FConstInitNotConstant : forall (c : ConsumptionSiteRef p)  (u : ExprUseRef p)
    (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> ConstInitReason -> SiteFailure ph (SConsumption p c)
| FNoNewVariable : forall d : ShortDeclRef p,
    ShortHasNoNewName ph d -> SiteFailure ph (SConsumption p (ShortSite p d))
(* A short reuse whose right-hand side does not fit the reused variable's exact type. *)
| FShortReuseMismatch : forall (d : ShortDeclRef p)  (o : ObjectRef ph)
    (sv : StaticVariable ph o) (u : ExprUseRef p) (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> ~ AtomFits ph a (static_type sv) ->
    SiteFailure ph (SConsumption p (ShortSite p d))
| FContext : forall r : ExprRef p, ContextReason -> SiteFailure ph (SExpression p r)
| FDefaultNotRepresentable : forall r : ExprRef p,
    UntypedConstantKind -> TypeView -> SiteFailure ph (SExpression p r)
| FUnusedLocal : forall (est : ObjectEstablisher p) (v : VariableSiteRef p),
    StaticVariable ph (source_object ph (establisher_site est)) ->
    NoReadOf ph v -> SiteFailure ph (SDeclaration p est)
| FInitializationCycle : forall k : PackageRef p, InitCycle ph k -> SiteFailure ph (SDependency p k).

(* ── The fact a supported site carries ─────────────────────────────────────── *)
Parameter DeclarationFact : forall {p} {i : Input p} (ph : Phase i), ObjectEstablisher p -> Type.
(* A supported dependency site is exactly a valid initialization order for that package. *)
Definition DependencyFact {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type :=
  InitOrder ph k.

(* No global readiness index: each case names only the predecessor it actually needs.  A binding fact needs
   no type environment at all; the cases that resolve types retain the exact readiness they used. *)
(* §6 No global readiness wrapper: every fact carries only the exact type evidence it needs.  An
   independent `println(1)` has facts even when `type U uintptr` is outside scope. *)
Definition SiteFact {p} {i : Input p} (ph : Phase i) (s : Site p) : Type :=
  match s with
  | SBinding _ u     => BindingFact ph u
  | SDeclaration _ b => DeclarationFact ph b
  | SDependency _ k  => DependencyFact ph k
  | SExpression _ r  => { form : ResultFormAt ph & ExprFact ph r form }
  | SUse _ u         => match use_refinement u with
                        | ResultRefinement =>
                            { a : ResultAtomAt ph & ResultUseFactAt ph u a }
                        | _ => { form : ResultFormAt ph &
                                 ExprFact ph (expression_of_use u) form }
                        end
  | SStatement _ t   => StmtFact ph t
  | SConsumption _ c => ConsumptionFact ph c
  end.

(* ── §10 One outcome per site ──────────────────────────────────────────────── *)
(* The topology below is migration inventory for a module-private type.  `Compilable.Report` exports
   `phase_outcome` and the projections; it does not export these constructors, because they are freely
   applicable and a client holding them could fabricate an outcome claiming a site failed. *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| Supported       : forall s : Site p, SiteFact ph s -> SiteOutcome ph s
| DefiniteFailure : forall s, SiteFailure ph s -> SiteOutcome ph s
| Outside         : forall s, SiteRequirement ph s -> SiteOutcome ph s
(* Blocked retains the exact predecessor site and the exact dependency edge, and nothing more: the
   predecessor's outcome is `phase_outcome ph pred`, which is unique, so no equal-looking substitute can be
   supplied alongside it. *)
| Blocked         : forall s pred, SiteDependency ph pred s -> SiteOutcome ph s.

Definition IsSupported {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with Supported _ _ _ => True | _ => False end.

Definition supported_fact {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : IsSupported o -> SiteFact ph s :=
  match o in SiteOutcome _ s0 return IsSupported o -> SiteFact ph s0 with
  | Supported _ _ f => fun _ => f
  | DefiniteFailure _ _ _ => fun h => match h return SiteFact ph _ with end
  | Outside _ _ _ => fun h => match h return SiteFact ph _ with end
  | Blocked _ _ _ _ => fun h => match h return SiteFact ph _ with end
  end.

Definition IsDefiniteFailure {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with DefiniteFailure _ _ _ => True | _ => False end.

Definition IsRootOutside {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with Outside _ _ _ => True | _ => False end.

Definition root_requirement {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : IsRootOutside o -> SiteRequirement ph s :=
  match o in SiteOutcome _ s0 return IsRootOutside o -> SiteRequirement ph s0 with
  | Outside _ _ r => fun _ => r
  | Supported _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | DefiniteFailure _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | Blocked _ _ _ _ => fun h => match h return SiteRequirement ph _ with end
  end.

(* Every site has an outcome for an arbitrary core, with no global environment in sight. *)
Parameter phase_outcome : forall {p} {i : Input p} (ph : Phase i) (s : Site p), SiteOutcome ph s.


(* ── §14 One closed root-cause authority ───────────────────────────────────── *)
(* A diagnostic is a sealed view of one exact root cause.  Every cause is a constructor of this sum,
   so completeness and soundness are constructive rather than asserted. *)
Inductive RootCause {p} {i : Input p} (ph : Phase i) : Type :=
| RCSiteFailure : forall s : Site p, SiteFailure ph s -> RootCause ph
| RCTypeCycle   : TypeCycle (phase_equations ph) -> RootCause ph
| RCMainRedeclared : forall later earlier : ObjectSiteRef p, RootCause ph
| RCMissingMain : PackageRef p -> RootCause ph
| RCBuildOutputDir : PackageRef p -> string -> RootCause ph.

Definition site_failure_code {p} {i : Input p} {ph : Phase i} {s}
  (f : SiteFailure ph s) : DiagnosticCode :=
  match f with
  | FUnresolvedName _ _ _ => CodeUnresolvedName
  | FWrongRole _ _ _ _ _ => CodeUnresolvedName
  | FDuplicateDeclaration _ _ _ _ => CodeDuplicateDeclaration
  | FPackageInitReserved _ _ _ => CodeContext
  | FNotAStatement _ _ _ => CodeNotAStatement
  | FResultCountWrong _ _ _ _ => CodeResultCount
  | FNotAssignableAt _ _ _ _ _ _ => CodeNotAssignable
  | FNotRepresentableAt _ _ _ _ _ _ => CodeNotRepresentable
  | FConstInitNotConstant _ _ _ _ _ _ => CodeConstInitializerNotConstant
  | FNoNewVariable _ _ _ => CodeNoNewVariable
  | FShortReuseMismatch _ _ _ _ _ _ _ _ => CodeNotAssignable
  | FContext _ _ _ => CodeContext
  | FDefaultNotRepresentable _ _ _ _ => CodeDefaultNotRepresentable
  | FUnusedLocal _ _ _ _ _ => CodeUnusedLocal
  | FInitializationCycle _ _ _ => CodeInitializationCycle
  end.

Definition root_cause_code {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : DiagnosticCode :=
  match rc with
  | RCSiteFailure _ _ f     => site_failure_code f
  | RCTypeCycle _ _         => CodeTypeCycle
  | RCMainRedeclared _ _ _  => CodeMainRedeclared
  | RCMissingMain _ _       => CodeMissingMainEntry
  | RCBuildOutputDir _ _ _  => CodeBuildOutputIsDirectory
  end.

Record ErasedDiagnostic : Type := MakeErasedDiagnostic {
  erased_code   : DiagnosticCode;
  erased_primary : ErasedAnchor;
  erased_related : list ErasedAnchor;
  erased_target  : option TypeView;
  erased_output  : option string;
  erased_source_target : option TypeExpr
}.

Parameter diagnostic_primary : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> DiagnosticAnchor p.
Parameter diagnostic_related : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> list (DiagnosticAnchor p).
Parameter erase_anchor : forall {p}, DiagnosticAnchor p -> ErasedAnchor.
Parameter diagnostic_compare : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> RootCause ph -> comparison.

Definition diagnostic_target {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : option TypeView :=
  match rc with
  | RCSiteFailure _ _ f =>
      match f with
      | FDefaultNotRepresentable _ _ _ t => Some t
      | FNotAssignableAt _ _ _ _ _ t => Some (type_view t)
      | FNotRepresentableAt _ _ _ _ _ t => Some (type_view t)
      | _ => None
      end
  | _ => None
  end.

Definition diagnostic_output {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : option string :=
  match rc with RCBuildOutputDir _ _ nm => Some nm | _ => None end.

Parameter diagnostic_source_target : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> option TypeExpr.

Definition erase_diagnostic {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : ErasedDiagnostic :=
  MakeErasedDiagnostic (root_cause_code rc) (erase_anchor (diagnostic_primary rc))
    (List.map erase_anchor (diagnostic_related rc))
    (diagnostic_target rc) (diagnostic_output rc) (diagnostic_source_target rc).

(* ── §14 Boundaries, the report, and the outcome ───────────────────────────── *)
(* No environment index: an outside-scope core is precisely one with no ready environment, so a boundary
   that needed one could never be reported. *)
Record PackedBoundary {p} {i : Input p} (ph : Phase i) : Type := MakeBoundary {
  boundary_site : Site p;
  boundary_requirement : SiteRequirement ph boundary_site;
  boundary_is_root : IsRootOutside (phase_outcome ph boundary_site)
}.

Definition boundary_view {p} {i : Input p} {ph : Phase i}
  (b : PackedBoundary ph) : RequirementView :=
  requirement_view (boundary_requirement ph b).

(* The site table is the authority; the report lists are its canonical projections, not peer lists.
   `Core`, `Elaboration` and `phase` are the existing repository names, stubbed once above. *)
Parameter core_diagnostics : forall {p} (c : Core p), list (RootCause (phase c)).
Parameter core_boundaries : forall {p} (c : Core p), list (PackedBoundary (phase c)).

Inductive Decision {p} (c : Core p) : Type :=
| DecisionAccepted : core_diagnostics c = [] -> core_boundaries c = [] -> Decision c
| DecisionRejected : core_diagnostics c <> [] -> Decision c
| DecisionOutside  : core_diagnostics c = [] -> core_boundaries c <> [] -> Decision c.

Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).

Parameter Program : Type.
Parameter source : Program -> SyntaxProgram.
Parameter core : forall cp : Program, Core (source cp).
Parameter accepted : forall cp : Program, core_diagnostics (core cp) = [].
Parameter in_scope : forall cp : Program, core_boundaries (core cp) = [].

Parameter Failure : SyntaxProgram -> Type.
Parameter failure_core : forall {p}, Failure p -> Core p.
Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> [].
Parameter Outside_ : SyntaxProgram -> Type.
Parameter outside_core : forall {p}, Outside_ p -> Core p.
Parameter outside_clean : forall {p} (o : Outside_ p), core_diagnostics (outside_core o) = [].
Parameter outside_blocked : forall {p} (o : Outside_ p), core_boundaries (outside_core o) <> [].

Inductive Outcome (p : SyntaxProgram) : Type :=
| Compiled : forall cp : Program, source cp = p -> Outcome p
| Rejected : Failure p -> Outcome p
| OutsideScope : Outside_ p -> Outcome p.

Parameter compile : forall p : SyntaxProgram, Outcome p.
Definition InScope (p : SyntaxProgram) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = [].

(* ── Accepted facts are projections of the one retained phase ──────────────── *)
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
(* The one readiness authority is the retained phase result; there is no second `core_ready` beside it. *)
Parameter accepted_is_ready : forall cp : Program,
  IsTypeReady (phase_type_result (accepted_phase cp)).
Definition accepted_ready (cp : Program) : TypeReady (accepted_phase cp) :=
  ready_of (phase_type_result (accepted_phase cp)) (accepted_is_ready cp).
Definition accepted_outcome (cp : Program) (s : Site (source cp))
  : SiteOutcome (accepted_phase cp) s :=
  phase_outcome (accepted_phase cp) s.

(* Derived, not postulated.  An accepted core has no diagnostic and no boundary; the report lists are
   complete over root failures and root outside requirements; and every blocked chain reaches one of those
   roots.  Together those force every site to be supported, so this is a consequence rather than a second
   authority sitting beside the report. *)
Lemma accepted_supported : forall (cp : Program) (s : Site (source cp)),
  IsSupported (accepted_outcome cp s).
Proof. Admitted.

Definition accepted_fact (cp : Program) (s : Site (source cp))
  : SiteFact (accepted_phase cp) s :=
  supported_fact (accepted_outcome cp s) (accepted_supported cp s).

Definition AcceptedType (cp : Program) : Type := SemanticType (source cp).
Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition ExpressionFact (cp : Program) (r : ExprRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SExpression (source cp) r).
Definition expression_fact (cp : Program) (r : ExprRef (source cp)) : ExpressionFact cp r :=
  accepted_fact cp (SExpression (source cp) r).
(* Application and statement facts are now accessed through the expression site, since SApplication
   and SUnary are no longer independent sites. *)
Definition ApplicationFact (cp : Program) (a : ApplicationRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SExpression (source cp) (application_expr_of a)).
Definition application_fact (cp : Program) (a : ApplicationRef (source cp))
  : ApplicationFact cp a := accepted_fact cp (SExpression (source cp) (application_expr_of a)).
Definition StatementFact (cp : Program) (t : ExpressionStatementRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SStatement (source cp) t).
Definition statement_fact (cp : Program) (t : ExpressionStatementRef (source cp))
  : StatementFact cp t := accepted_fact cp (SStatement (source cp) t).
Definition ConsumptionAt (cp : Program) (c : ConsumptionSiteRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SConsumption (source cp) c).
Definition consumption_at (cp : Program) (c : ConsumptionSiteRef (source cp))
  : ConsumptionAt cp c := accepted_fact cp (SConsumption (source cp) c).

(* ── §15 Rendering: contexts, exact equations, real whitespace properties ──── *)
Inductive RenderContext : Type :=
| TopContext | UnaryOperandContext | ApplicationHeadContext | ApplicationArgumentContext.

(* Canonical grouping is decided by the spec count: exactly one renders ungrouped, zero or two-or-more
   render grouped.  Pinned `gc` accepts the empty group, so both forms are reachable. *)
Definition renders_grouped {A : Type} (specs : list A) : bool :=
  match specs with [_] => false | _ => true end.

Parameter needs_parens : RenderContext -> Expr -> bool.
Parameter render_in : RenderContext -> Expr -> string.
Parameter render_expr : Expr -> string.
Parameter render_literal : Literal -> string.
(* The three literal emission authorities: canonical decimal for magnitudes, canonical Go escaping for
   strings.  Nothing else may spell a literal. *)
Parameter decimal_of_magnitude : N -> string.
Parameter decimal_of_float : NonNegativeDecimal -> string.
Parameter escape_go_string : string -> string.
Parameter render_type_expr : TypeExpr -> string.
Parameter render_binding_name : BindingName -> string.
(* §16 Depth-aware rendering: a grouped local declaration has internal newlines and cannot be correctly
   indented by prepending one tab to the finished string.  These are the permanent structural roots. *)
Parameter render_declaration_at : nat -> Declaration -> string.
Parameter render_stmt_at : nat -> Stmt -> string.
Parameter render_block_at : nat -> Block -> string.
Parameter render_top_decl : TopLevelDecl -> string.

Definition render_declaration : Declaration -> string := render_declaration_at 0.
Definition render_stmt : Stmt -> string := render_stmt_at 0.
Definition render_block : Block -> string := render_block_at 0.
Parameter render_file : SyntaxFile -> string.
Parameter render_const_spec : ConstSpec -> string.
Parameter render_var_spec : VarSpec -> string.
Parameter render_type_spec : TypeSpec -> string.
Parameter render_program : SyntaxProgram -> list (string * string).
Parameter render_gomod : ModuleSpec -> string.

Fixpoint InString (c : ascii) (s : string) : Prop :=
  match s with EmptyString => False | String c' rest => c = c' \/ InString c rest end.

Definition first_char (s : string) : option ascii :=
  match s with EmptyString => None | String c _ => Some c end.

Fixpoint last_char (s : string) : option ascii :=
  match s with
  | EmptyString => None
  | String c EmptyString => Some c
  | String _ rest => last_char rest
  end.

(* Exactly two adjacent bytes: a token-boundary property, not a scan of arbitrary contents. *)
Fixpoint HasAdjacent (a b : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c rest => (c = a /\ first_char rest = Some b) \/ HasAdjacent a b rest
  end.

Definition NewlineChar : ascii := ascii_of_nat 10.
Definition SpaceChar : ascii := ascii_of_nat 32.
Definition TabChar : ascii := ascii_of_nat 9.

Definition StartsWithMinus (s : string) : Prop := first_char s = Some "-"%char.
Definition AsciiOnly (s : string) : Prop := forall c, InString c s -> (nat_of_ascii c < 128)%nat.
Definition Parenthesized (s : string) : Prop := exists inner, s = ("(" ++ inner ++ ")")%string.

(* No line ends in a space or a tab, and the final byte is a newline. *)
Definition NoTrailingBlank (s : string) : Prop :=
  ~ HasAdjacent SpaceChar NewlineChar s /\
  ~ HasAdjacent TabChar NewlineChar s /\
  last_char s = Some NewlineChar.
```

## Theorems

These theorem statements are part of the migration inventory above: non-authoritative, and the canonical
implementation owns their exact statements and proofs.

```coq
(* ── §17 Theorem surface ───────────────────────────────────────────────────── *)

(* §17.1 Names/index/source — canonicalized in `Names.v`, which proves catalog completeness and NoDup,
   spelling injectivity, classifier round-trip and soundness, reflected equality, and the ordinary-identifier
   iff (nonblank in both directions).  Not restated here. *)

(* §17.2 Binding *)
Theorem resolve_name_reflects :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o : ObjectRef ph),
  resolve_name ph u = Some o <-> Resolves ph u o.
Proof. Admitted.
Theorem resolution_is_same_spelling :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o : ObjectRef ph),
  Resolves ph u o -> object_spelling o = name_use_spelling u.
Proof. Admitted.
Theorem resolution_is_unique :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o1 o2 : ObjectRef ph),
  Resolves ph u o1 -> Resolves ph u o2 -> o1 = o2.
Proof. Admitted.
Theorem source_binding_shadows_predeclared :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (sc : ScopeId p)
    (m : ScopeBindings ph sc) (b : ObjectEstablisher p) (n : PredeclaredName),
  Encloses sc (name_use_scope u) ->
  scope_build ph sc = ScopeReady ph sc m ->
  scope_lookup m (name_use_spelling u) = Some b -> VisibleAt b u ->
  ~ Resolves ph u (predeclared_object ph n).
Proof. Admitted.
Theorem duplicate_scope_fails :
  forall {p} {i : Input p} (ph : Phase i) (sc : ScopeId p) (e l : ObjectEstablisher p),
  DuplicateEstablishers e l -> establisher_scope l = sc ->
  forall m : ScopeBindings ph sc, scope_build ph sc <> ScopeReady ph sc m.
Proof. Admitted.

(* §17.3 Type resolution *)
Theorem byte_is_uint8 : AliasPredeclared PByte TUint8.
Proof. Admitted.
Theorem rune_is_int32 : AliasPredeclared PRune TInt32.
Proof. Admitted.
Theorem every_basic_type_has_a_name : forall t : PredeclaredBasicType,
  exists n, AdmittedPredeclaredType n t.
Proof. Admitted.
Theorem default_types_exact :
  default_basic UCBool = TBool /\ default_basic UCInteger = TInt /\
  default_basic UCFloat = TFloat64 /\ default_basic UCComplex = TComplex128 /\
  default_basic UCString = TString.
Proof. Admitted.
Theorem identicalb_reflect : forall {p} (s t : SemanticType p),
  identicalb s t = true <-> Identical s t.
Proof. Admitted.
Theorem assignableb_reflect : forall {p} (s t : SemanticType p),
  assignableb s t = true <-> Assignable s t.
Proof. Admitted.
Theorem value_convertibleb_reflect :
  forall {p} {i : Input p} {ph : Phase i}  (s t : SemanticType p),
  value_convertibleb ph s t = true <-> ValueConvertible ph s t.
Proof. Admitted.
Theorem representableb_reflect :
  forall {p} {i : Input p} {ph : Phase i}  (s : SemanticType p) (c : Constant),
  representableb ph s c = true <-> Representable ph s c.
Proof. Admitted.

(* §17.4 Objects *)
Theorem source_object_origin_is_its_site :
  forall {p} {i : Input p} (ph : Phase i) (s : ObjectSiteRef p),
  object_origin (source_object ph s) = SourceSite p s.
Proof. Admitted.
Theorem object_origin_injective :
  forall {p} {i : Input p} {ph : Phase i} (o1 o2 : ObjectRef ph),
  object_origin o1 = object_origin o2 -> o1 = o2.
Proof. Admitted.

(* §17.5 Reports *)
Theorem view_lt_irrefl : forall a : RequirementView, ~ view_lt a a.
Proof. Admitted.
Theorem view_lt_transitive : forall a b c : RequirementView,
  view_lt a b -> view_lt b c -> view_lt a c.
Proof. Admitted.
Theorem view_lt_total : forall a b : RequirementView, view_lt a b \/ a = b \/ view_lt b a.
Proof. Admitted.

Definition StrictlyIncreasingBy {A : Type} (lt : A -> A -> Prop) : list A -> Prop :=
  fix go l := match l with
  | [] => True
  | a :: rest => match rest with [] => True | b :: _ => lt a b /\ go rest end
  end.

Theorem boundary_order_canonical : forall {p} (c : Core p),
  StrictlyIncreasingBy view_lt (List.map (fun b => boundary_view b) (core_boundaries c)).
Proof. Admitted.
Theorem boundary_views_nodup : forall {p} (c : Core p),
  NoDup (List.map (fun b => boundary_view b) (core_boundaries c)).
Proof. Admitted.
Theorem root_boundary_complete : forall {p} (c : Core p) (s : Site p),
  IsRootOutside (phase_outcome (phase c) s) ->
  exists b, List.In b (core_boundaries c) /\ boundary_site (phase c) b = s.
Proof. Admitted.

(* §17.6 Outcome *)
Definition elaborated (p : SyntaxProgram) : Core p := elaboration_core (elaborate p).
Definition IsCompiled {p} (o : Outcome p) : Prop :=
  match o with Compiled _ _ _ => True | _ => False end.
Definition IsRejected {p} (o : Outcome p) : Prop :=
  match o with Rejected _ _ => True | _ => False end.
Definition IsOutsideScope {p} (o : Outcome p) : Prop :=
  match o with OutsideScope _ _ => True | _ => False end.

Theorem compiled_iff : forall p : SyntaxProgram,
  IsCompiled (compile p) <->
  core_diagnostics (elaborated p) = [] /\ core_boundaries (elaborated p) = [].
Proof. Admitted.
Theorem rejected_iff : forall p : SyntaxProgram,
  IsRejected (compile p) <-> core_diagnostics (elaborated p) <> [].
Proof. Admitted.
Theorem outside_scope_iff : forall p : SyntaxProgram,
  IsOutsideScope (compile p) <->
  core_diagnostics (elaborated p) = [] /\ core_boundaries (elaborated p) <> [].
Proof. Admitted.

Theorem compiled_retains_core : forall (p : SyntaxProgram) (cp : Program) (e : source cp = p),
  compile p = Compiled p cp e ->
  eq_rect (source cp) Core (core cp) p e = elaborated p.
Proof. Admitted.
Theorem rejected_retains_core : forall (p : SyntaxProgram) (f : Failure p),
  compile p = Rejected p f -> failure_core f = elaborated p.
Proof. Admitted.
Theorem outside_retains_core : forall (p : SyntaxProgram) (o : Outside_ p),
  compile p = OutsideScope p o -> outside_core o = elaborated p.
Proof. Admitted.

Theorem compile_sound : forall (p : SyntaxProgram) (cp : Program) (e : source cp = p),
  compile p = Compiled p cp e -> Admissible p.
Proof. Admitted.
Theorem compile_complete_in_scope : forall p : SyntaxProgram,
  Admissible p -> InScope p -> exists (cp : Program) (e : source cp = p), compile p = Compiled p cp e.
Proof. Admitted.
Theorem rejected_not_admissible : forall (p : SyntaxProgram) (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.
Proof. Admitted.

(* §17.7 Empty reports force every site supported — this is how `accepted_supported` is derived. *)
Theorem empty_report_implies_all_supported : forall {p} (c : Core p) (s : Site p),
  core_diagnostics c = [] -> core_boundaries c = [] ->
  IsSupported (phase_outcome (phase c) s).
Proof. Admitted.

(* §17.8 Dependencies *)
Theorem init_units_nodup : forall {p} (k : PackageRef p), NoDup (package_init_units k).
Proof. Admitted.
Theorem runtime_projection_excludes_constants :
  forall {p} {i : Input p} {ph : Phase i} {k : PackageRef p} (o : InitOrder ph k),
  List.Forall (fun u => RuntimeInitUnit u = true) (runtime_initialization o).
Proof. Admitted.


(* §14 Blocked causality *)
Theorem dependency_decreases_stage :
  forall {p} {i : Input p} (ph : Phase i) (pred s : Site p),
  SiteDependency ph pred s -> (site_stage ph pred < site_stage ph s)%nat.
Proof. Admitted.

(* §16 Additional theorem obligations *)
Theorem node_blocked_cause_not_supported :
  forall {p} {i : Input p} (ph : Phase i)
    (acyc : AcyclicEquations (phase_equations ph)) (n m : TypeNode p)
    (e : TypeEdge (phase_equations ph) n m),
  node_outcome ph acyc n = NodeBlocked ph n m e ->
  ~ NodeIsSupported (node_outcome ph acyc m).
Proof. Admitted.

Theorem type_ready_iff_all_supported :
  forall {p} {i : Input p} (ph : Phase i)
    (acyc : AcyclicEquations (phase_equations ph)),
  (forall n, NodeIsSupported (node_outcome ph acyc n)) ->
  TypeReady ph.
Proof. Admitted.

Theorem static_variable_identity :
  forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph) (sv : StaticVariable ph o),
  object_origin o = SourceSite p (establisher_site (static_est ph o sv)).
Proof. Admitted.
```

## Implementation review boundaries

**Per-root review rule.**

> C6 advances only at a whole-repository-green exact `HEAD` that closes one named dependency-closed semantic
> root in its permanent owners, deletes every authority and migration-inventory statement it supersedes, and
> makes every affected document true. That exact `HEAD` receives the two-different-model whole-system reviews
> and Rob acceptance required by `ARCHITECTURE.md` §1 "Review and acceptance" before any dependent C6 root
> begins. Acceptance applies
> only to the named root; it is neither C6 semantic-root closure nor C6 acceptance.

**C6 semantic-root closure review** stops only when the repository is green, the `Compilable.*` modules exist with no
old path beside a new one, and the tree contains: an ordinary identifier that excludes blank and nothing
else, with every predeclared spelling shadowable; blank only as a `BindingName`; nonnegative literal
magnitudes with negation only through `Unary UnaryMinus`; declaration spec groups as lists; one sealed
exhaustive view per expression, binding-name and object-site occurrence, so no occurrence carries two
classifications; a scope build that fails on same-scope duplicates, with resolution consuming ready maps
only; a phase type result that represents a cyclic phase, an acyclic phase whose nodes fail, are outside
scope or are blocked, and a ready one; per-node outcomes retaining the exact right-hand side that produced
them, with `underlying` read from the node rather than chased; a `TypeReady` whose seal is its obligation —
acyclicity plus support for every node — rather than a hidden constructor; site facts naming only the
predecessor each actually needs, and failures, requirements, outcomes and boundaries needing no global
environment at all; `Blocked` retaining its exact predecessor site and edge, with the cause being
`phase_outcome` itself; a stage that strictly decreases along every dependency, so blocked chains are finite
and reach a root; capabilities reading their values from declaration facts rather than carrying supplied
constants or types; a conversion whose destination is the head's own type meaning; all nine `complex`
operand combinations computing their results; a statement judgment only a `println` application can inhabit;
consumption plans indexed by their own site's target list and use list in lockstep; a short reuse that must
name an existing static variable in its own block; initialization units producing lists of objects, edges
citing an object the destination unit produces, and a tie-break over the transitive relation rather than
direct-edge absence; requirements stated over the total descriptor, never over the meaning they report
missing; the complete diagnostic migration above; exact core provenance for `Compiled`, `Rejected` and
`Outside`; nontrivial render predicates; and prior generated bytes unchanged.

**Final C6 review** then completes exhaustive differential/e2e evidence, C6 fixtures, `LAT-077`,
generated-artifact evidence, and final document and ledger truth. It may not introduce or reinterpret
declaration behaviour, shadowing, boundary topology, application meaning, result consumption, static-variable
identity, or rendering semantics.

C7 is forbidden until Rob accepts C6.

## Pinned-gc observations

Adversarial observations of what pinned Go 1.23 (`gc`) accepts and rejects, gathered with `make go-probe`.
They are implementation-review evidence: the C6 implementation must agree with every one, and none is a
language-semantics authority — a finite probe set is evidence, never a global theorem.

**Source root.** Every predeclared spelling is a legal ordinary source identifier: `int`,
`int32` and `any` as type names, `true`, `iota`, `nil`, `len`, `println` and `complex` as ordinary bindings,
at package level and locally. `_` is rejected as a value and as a type, so blank is exclusively a
`BindingName`. `type _ = int`, `type _ int`, `const _ = 1` and `var _ = 1` all accept. `const ()`, `var ()`
and `type ()` accept at package level and inside a function. `- 1` and `-1` both accept, so a negative value
is a unary application over a magnitude, not a literal.

**Arity and operands.** `int64()` and `int64(1, 2)` rejected; `complex(1)` and `complex(1, 2, 3)` rejected;
`complex(true, 1)` and `complex("a", 1)` rejected; two nonconstant `int` operands rejected. Accepted: two
untyped numeric constants; typed `float32` constant with an untyped operand giving `complex64`; a `float32`
value with an untyped operand; a typed `float64` constant with a `float64` value giving `complex128`; two
operands of one defined type over `float64`. Two distinct defined types over the same form rejected; mixed
`float32`/`float64` rejected.

**Unary rendering.** `-(-x)` and `- -x` both accept, so pinned `gc` does not force the choice; the
contract renders the parenthesized form because it makes the `--` token boundary unreachable by
construction rather than by a scan. `-int(x)` and `println(-x)` accept.

**Type chains, `complex` profiles and cycles.** `type U uintptr; type T U` accepts, so a predeclared name
with no C6 type meaning is a boundary and never a rejection. All six `complex` operand combinations accept
with the kind the contract assigns — two untyped giving `complex128`, and any `float32` operand giving
`complex64`; mixed `float32`/`float64` rejects, so both operands share one kind. A package-level forward
reference accepts while `var a = b; var b = a` and the same pair as constants both reject, so dependency
decides initialization order and cycles are definite failures.

**Short declarations.** `x := 1; x, y := 2, 3` accepts and `x := 1; x := 2` rejects, so at least one nonblank
left-hand name must be new. `x := 1; x, y := "s", 3` rejects, so a reuse carries exact type compatibility.

**Short reuse, conversion and defaulting.** `c, y := 2, 3` after `const c = 1` rejects, and the same with a
local type name rejects, so a short reuse must name an existing variable. `type A = int; type B A` accepts,
so a definition resolves through a source alias. `const a float32 = 2.0; const b = int(a)` accepts while
`1.5` rejects, so typed-constant conversion carries representability. `println(1)` accepts and
`println(1 << 200)` rejects, so an untyped argument must be representable in its exact default type.
`complex(1e400, 0)` rejects. `var a = c; var b = 1; var c = b` accepts, so ordering follows the transitive
chain where no direct edge exists.

**Const initializers.** `var x = 1; const y = x` rejected; `const y = println(1)` rejected; `const x = 1;
const y = x`, `const y = int64(x)` and `const y = complex(1.0, 2.0)` accepted.

**Statement position.** Rejected: `append`, `cap`, `complex`, `imag`, `len`, `make`, `new`, `real`, `min`,
`max`, a conversion, a bare identifier, a bare literal, a unary expression. Accepted: `clear`, `close`,
`copy`, `delete`, `panic`, `print`, `println`, `recover`, and an ordinary function call. `min` and `max` were
confirmed with nonconstant arguments, so their rejection is the statement-context rule and not constant
folding; pinned `gc` rejects them although the Go 1.23 spec text does not enumerate them.

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations independent of file order; two packages sharing a spelling without collision;
duplicate package names rejected; `byte`/`uint8` and `rune`/`int32` interchangeable; `int` assignable to
neither `int32` nor `int64`; an unshadowed `len`, a `var x uintptr` and a recursive `main()` each giving a
boundary with the exact unmet requirement and no diagnostic; every currently accepted program rendering
byte-identically after migration.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; `Integer.Kind`, `Float.Kind` and `Complex.Kind` as the only kind carriers;
`Float.TypedConstant` and `Complex.TypedConstant` as the static constant carriers; `Compilable.PackageRef` as
the package-directory key with its proved injectivity; every current public diagnostic constructor, code,
anchor and erasure; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

An ordinary identifier must exclude a predeclared spelling, or must admit blank; a negative value needs a
second source form; a declaration group must be nonempty; the use refinement needs a fallback case; a source
occurrence must carry two classifications, or a view must be split back into independent option
projections; name resolution must go through a scope whose own construction failed; a phase type result
cannot represent an acyclic phase that is not ready; a `TypeReady` must exist without support for every
node; a node outcome cannot retain the right-hand side that produced it; `underlying` must chase a relation
that can self-loop; a site failure, requirement, outcome or boundary must be indexed by a global
environment; a requirement decision cannot run before a `Program` exists; a requirement must retain the very
meaning it reports as missing; a blocked chain cannot be shown finite without fuel, or cannot be shown to
reach a root; a conversion destination cannot be derived from its own application head; a `complex`
combination cannot be stated exactly; a short-declaration reuse cannot be pinned to an existing static
variable in its own block; an initialization unit cannot produce more than one object, or an edge cannot
cite an object its destination unit produces, or the tie-break must use direct-edge absence rather than the
transitive relation; a current public diagnostic cannot be migrated without loss; `compiled_retains_core`
cannot be stated exactly; a render predicate cannot be made nontrivial; the pinned toolchain rejects the
qualified namespace; a real semantic cycle appears between the frozen child modules; implementation needs a
placeholder, compatibility path, trusted shortcut, fuel, bound or premature future state.
