# C6 — Names, types, slots, places, and the first concrete machine

Baseline: 57b913af9c15deee46df5b117839c2b9528d6b1a
Review: contract

Goal:
C6 lands exact binding and use roles, the one type algebra, the predeclared universe, static slots, dynamic
places, basic closed runtime values, the first scalar-cell object-store slice, and the expression-fact/use
boundary needed by declarations and variables.

C6 is the first consumer of `Machine.T`. It defines **one** concrete machine slice over the already accepted
fragment plus C6 declarations. It defines no peer evaluator and no second run relation. Future milestones
extend the same machine internals; they never replace C6's machine with another one.

`Safe.Property` stays `True` while the represented fragment has no unsafe behaviour. Operational meaning
belongs to the one machine; no false safety claim is invented to make `Property` nontrivial.

## Rows and gates

66 closure rows and 22 latitude rows carry `milestone` `C6`. Counts are derived from the ledgers, never
written by hand. `LAT-077` is C6's only acceptance gate.

Reassigned by this review: `SPEC-045` (Label scopes) to C8; `LAT-X004` to C7 beside its owner `SPEC-096`;
acceptance gate `LAT-019` to C7, whose shift fixtures need C7 constant-expression syntax; `GRAM-104`
(`OperandName`) to C6, admitting only its unqualified-identifier branch, with `GRAM-105` staying at C11.
`GRAM-050` (`TypeLit`) is sum-production evidence only and authorises no C6 constructor.

## Contract slices

C6 consumes only these, and claims no later slice of any cumulative contract:

- **SC-02** predeclared constants, constant declarations, `iota`, C6 constant initializers, defaulting and
  representability for admitted forms;
- **SC-03** package and local scopes, declarations, binding facts, static slots, blank uses, uniqueness,
  export classification, predeclared shadowing;
- **SC-04** one type algebra over basic, alias and defined types, with no structural or generic case;
- **SC-05** context-free facts and exact C6 use edges, including ordinary name expressions;
- **SC-08** scalar cells, places, allocation identity and typed lookup only;
- **SC-14** C6 zero values and the current closed-command start only;
- **SC-21** minimal exact public roots, disposable internals, every proof helper `Local`;
- **SC-22** `LAT-077` only.

## The cost this contract commits to

A defined type's identity is its exact source declaration reference. The only such reference is
`Index`-indexed by the program. Therefore **`Typing.SemanticType` becomes program-indexed**, and every
current signature mentioning it — in `Typing`, `Compilable`, `Safe` and `Render` — gains that index. This is
the single largest mechanical cost in C6 and it is deliberate: the alternative is a string, numeric `TypeId`,
registry or tag as type identity, which is forbidden.

## Exact public source surface

`Names` loses its closed sixteen-name class. `Names.TypeName`, `Names.SupportedType`, `Names.classify`,
`Names.supported_of` and every projection over them are **deleted**, not wrapped.

```coq
(* Syntax: an ordinary identifier is the only way to name a type or an object. *)
Inductive TypeExpr : Type :=
| NamedType : Names.Identifier -> TypeExpr.

Inductive NameOrBlank : Type :=
| DeclaredName : Names.Identifier -> NameOrBlank
| BlankName    : NameOrBlank.

Inductive Expr : Type :=
| Name                 : Names.Identifier -> Expr
| IntegerLiteral       : N -> Expr
| NegatedIntegerLiteral : N -> Expr
| StringLiteral        : string -> Expr
| FloatLiteral         : Float.Decimal -> Expr
| ComplexLiteral       : Complex.Decimal -> Expr
| Convert              : TypeExpr -> Expr -> Expr.
```

`Syntax.BoolLiteral` is **deleted**. `true` and `false` are predeclared constants reached through `Name`.

Declarations and statements are mutually inductive, because a block holds statements and a statement may hold
a local declaration:

```coq
Inductive ConstSpec : Type :=
| MakeConstSpec : list NameOrBlank -> option TypeExpr -> list Expr -> ConstSpec
with VarSpec : Type :=
| MakeVarSpec   : list NameOrBlank -> option TypeExpr -> list Expr -> VarSpec
with TypeSpec : Type :=
| AliasSpec : Names.Identifier -> TypeExpr -> TypeSpec
| DefSpec   : Names.Identifier -> TypeExpr -> TypeSpec
with Decl : Type :=
| ConstDecl : list ConstSpec -> Decl
| VarDecl   : list VarSpec   -> Decl
| TypeDecl  : list TypeSpec  -> Decl
| Main      : Block -> Decl
with Stmt : Type :=
| Println      : list Expr -> Stmt
| DeclStmt     : Decl -> Stmt
| ShortVarDecl : list NameOrBlank -> list Expr -> Stmt
with Block : Type :=
| MakeBlock : list Stmt -> Block.
```

`Main` now carries a real `Block`. `DeclStmt` admits only `ConstDecl`, `VarDecl` and `TypeDecl`; a nested
`Main` is rejected by `Admissible`, not by constructor absence, because the constructor is shared.

`Syntax.File` keeps its shape; `TopLevelDecl := Decl` continues to name the same type.

## Exact type algebra

```coq
Inductive SemanticType (p : Syntax.Program) : Type :=
| BoolType    : SemanticType p
| IntegerType : Integer.Kind -> SemanticType p
| FloatType   : Float.Kind   -> SemanticType p
| ComplexType : Complex.Kind -> SemanticType p
| StringType  : SemanticType p
| DefinedType : Index.TypeSpecRef p -> SemanticType p.
```

An alias has **no constructor**: it resolves to the type its right-hand side denotes. A defined type carries
its declaration reference and nothing else. These are separate relations over the one algebra:

```coq
Parameter underlying : forall {p}, SemanticType p -> SemanticType p.
Parameter core_type  : forall {p}, SemanticType p -> option (SemanticType p).
Parameter Identical  : forall {p}, SemanticType p -> SemanticType p -> Prop.
Parameter Assignable : forall {p}, SemanticType p -> SemanticType p -> Prop.
Parameter ConvertibleTo : forall {p}, SemanticType p -> SemanticType p -> Prop.
Parameter zero_value : forall {p}, SemanticType p -> Value p.

Theorem identical_defined_iff_same_decl : forall p (a b : Index.TypeSpecRef p),
  Identical (DefinedType p a) (DefinedType p b) <-> a = b.
Theorem underlying_defined_not_defined : forall p (r : Index.TypeSpecRef p),
  forall r', underlying (DefinedType p r) <> DefinedType p r'.
Theorem alias_preserves_identity : forall p (d : Index.TypeSpecRef p) (t : SemanticType p),
  AliasDenotes p d t -> Identical t (alias_target p d).
```

No second runtime type enum, `TypeId`, registry, tag or string-keyed identity exists anywhere.

## Exact index additions

```coq
Inductive Kind := FileKind | PackageClauseKind | DeclarationKind | StatementKind | ExpressionKind
                | TypeNameKind | BlockKind | SpecKind | DeclaredNameKind | BlankKind.

(* Roles gained by C6; existing roles keep their meaning and argument order. *)
| DeclarationSpec  (n : nat)
| SpecName         (n : nat)
| SpecType
| SpecValue        (n : nat)
| BlockStatement   (n : nat)
| ShortDeclName    (n : nat)
| ShortDeclValue   (n : nat)
```

Refined references C6 adds, each `NodeRefOf p k`:

```coq
Definition BlockRef        (p : Syntax.Program) := NodeRefOf p BlockKind.
Definition SpecRef         (p : Syntax.Program) := NodeRefOf p SpecKind.
Definition TypeSpecRef     (p : Syntax.Program) := { r : SpecRef p | spec_is_type r = true }.
Definition DeclaredNameRef (p : Syntax.Program) := NodeRefOf p DeclaredNameKind.
Definition BlankRef        (p : Syntax.Program) := NodeRefOf p BlankKind.
```

A reference belongs to the exact `Syntax.Program` and the exact source occurrence. No source name, string,
list position or rebuilt equal occurrence is identity.

## Exact fact surface

Facts are retained before any runtime state exists. A consumer reads the retained child fact and never
re-reads the raw child to rediscover binding or type meaning.

```coq
Inductive Binding (p : Syntax.Program) : Type :=
| PredeclaredBinding : PredeclaredObject -> Binding p
| DeclaredBinding    : DeclaredNameRef p -> Binding p.

Record BindingFact (p : Syntax.Program) : Type := MakeBindingFact {
  binding_use    : ExprRef p;
  binding_target : Binding p
}.

Record TypeUseFact (p : Syntax.Program) : Type := MakeTypeUseFact {
  type_use     : TypeNameRef p;
  type_denoted : SemanticType p
}.

Record SlotFact (p : Syntax.Program) : Type := MakeSlotFact {
  slot_name : DeclaredNameRef p;
  slot_type : SemanticType p
}.

Record BlankUseFact (p : Syntax.Program) : Type := MakeBlankUseFact {
  blank_use     : BlankRef p;
  blank_operand : option (ExprRef p)
}.

Theorem blank_never_binds : forall p (b : BlankRef p) (f : BindingFact p),
  binding_use f <> blank_expr b.
Theorem slot_unique_per_name : forall p (a b : SlotFact p),
  slot_name a = slot_name b -> a = b.
Theorem binding_total_on_names : forall p (idx : Index.Program p) (e : ExprRef p),
  name_expr e = true -> exists f, BindingOf idx e f.
```

`PredeclaredObject` is the closed universe: the eighteen predeclared type names, `true`, `false`, `iota`,
`nil`. `Compilable.predeclared_type` and its ten fixing notations are **deleted**; every predeclared name
resolves through `BindingFact` like any other.

## Exact store, place and value surface

```coq
Parameter ObjectId : Type.                       (* private; only allocation mints one *)
Inductive Place (p : Syntax.Program) : Type :=
| ScalarCell : ObjectId -> Place p.

Inductive Value (p : Syntax.Program) : Type :=
| BoolValue    : bool -> Value p
| IntegerValue : Integer.Kind -> Z -> Value p
| FloatValue   : forall ft, Float.Value ft -> Value p
| ComplexValue : forall ct, Complex.Value ct -> Value p
| StringValue  : string -> Value p.

Parameter Store : Syntax.Program -> Type.
Parameter allocate : forall {p}, Store p -> SemanticType p -> Value p -> Store p * Place p.
Parameter load  : forall {p}, Store p -> Place p -> option (Value p).
Parameter Env   : Syntax.Program -> Type.
Parameter lookup_slot : forall {p}, Env p -> DeclaredNameRef p -> option (Place p).

Theorem allocate_fresh : forall p (s : Store p) t v s' pl,
  allocate s t v = (s', pl) -> load s pl = None /\ load s' pl = Some v.
Theorem allocate_never_reuses : forall p (s : Store p) t v s' pl pl' w,
  allocate s t v = (s', pl) -> load s pl' = Some w -> pl <> pl'.
Theorem reachable_lookup_total : forall p (st : GoState p),
  Reachable st -> forall sl, SlotDeclared st sl -> exists pl, lookup_slot (env st) sl = Some pl.
```

Runtime object identities are private, come only from allocation, never derive from a declaration reference
or a name, and are never reused. Constants and types create no place. The current unindexed `Safe.Value`
path is **replaced**, not retained beside this one.

## Exact machine surface

```coq
Parameter GoState  : Syntax.Program -> Type.
Parameter GoStart  : Syntax.Program -> Type.
Parameter GoLabel  : Syntax.Program -> Type.
Inductive GoResult : Type := NormalExit.

Parameter go_machine : forall (sp : Safe.Program), Machine.T.
Parameter go_initial : forall {p}, GoStart p -> GoState p.
Parameter go_step    : forall {p}, GoState p -> GoLabel p -> GoState p -> Prop.
Parameter go_final   : forall {p}, GoState p -> GoResult -> Prop.

Theorem go_machine_state  : forall sp, Machine.State  (go_machine sp) = GoState (Safe.source sp).
Theorem go_machine_step   : forall sp, Machine.step   (go_machine sp) = go_step.
Theorem go_machine_final  : forall sp, Machine.final  (go_machine sp) = go_final.
Theorem go_final_absorbing : forall sp, Machine.FinalAbsorbing (go_machine sp).
Theorem go_initial_wf   : forall p (s : GoStart p), WellFormed (go_initial s).
Theorem go_step_preserves_wf : forall p (a : GoState p) l b,
  WellFormed a -> go_step a l b -> WellFormed b.
Theorem go_start_accepts_current_fragment : forall sp,
  exists s : GoStart (Safe.source sp), True.
```

`GoState`, `GoStart`, `GoLabel`, `Place`, `ObjectId` and `Store` are **sealed**. `WellFormed` is hidden; only
its preservation is public. C6 provides **no** `Machine.EnabledDecision` inhabitant unless a C6 proof
genuinely needs and earns one. No empty future state field and no future action constructor is added.

C6 gives operational meaning to exactly: entering the current command start; the `main` block; constant,
type, variable and short-variable declarations; zero initialization; constant initialization; identifier
reads; blank discard in C6 contexts; the existing conversion and `println` forms; normal completion.

C6 adds no operator, general call, user function, loop, label, panic, concurrency, composite object, import
or package initialization. C7 generalises expression evaluation, output, order and panic **on this same
machine**. C8 adds control.

## Scope rules that must not be generalised into one vague algorithm

- the predeclared universe is the outer scope;
- the package block is built across all files before package declarations are resolved, so package-level
  order and file order do not choose meaning;
- duplicate package names are rejected exactly;
- the existing `main` declaration participates in package-block uniqueness;
- local blocks are sequential: a declaration enters scope at the exact point the Go specification gives it;
- local names may shadow package and predeclared names where Go permits;
- short declarations are local only and require at least one new nonblank name in the current block;
- `_` never creates a binding or slot;
- `init` creates no ordinary package binding and may not name a C6 const, type or variable declaration;
- `byte` and `rune` keep their source binding and spelling and create no identity distinct from `uint8` and
  `int32`;
- `nil` is in the universe, but C6 has no nilable type form, so a source occurrence may resolve to the
  predeclared object and still fail every available value context;
- `iota` is the ordinary predeclared identifier in its exact const-spec context, never a global numeric value.

## Deletions — no aliases, wrappers or compatibility constructors

- `Syntax.BoolLiteral`;
- `Names.TypeName`, `Names.SupportedType`, `Names.classify`, `Names.supported_of`, `Names.all_type_names`
  and every projection over them;
- `Syntax.TypeName` (`Unqualified`) and the `type_expr_*` helpers built on `Names.SupportedType`;
- `Compilable.predeclared_type`, `predeclared_type_of_name`, and the ten `Local Notation`s fixing it;
- the unindexed `Safe.Value` and `Safe.eval_expr` path, once the indexed value authority lands.

Current programs migrate through the ordinary-name path first; the competing path is then deleted in the
same milestone. Nothing is kept for compatibility.

## Two implementation review points

C6 is one milestone with two dependency-ordered reviews. There is no review stop between individual
constructors or files.

1. **Semantic-root review** — exact source constructor topology; block, declaration, binding, slot,
   name-use, type-use, expression-use and blank-use references; one type algebra and one predeclared
   universe; package and local scope construction; universal invariants and reflected decisions; migration of
   the existing fragment; deletion of every competing name and type authority.
2. **Final vertical review** — basic closed runtime values; slots, places and the first scalar-cell store;
   the concrete machine slice; declaration initialization, zero values, name reads, blank discard and the
   current `main`/`println` path; diagnostics, rendering, fixtures, generated artifacts and pinned-Go
   evidence.

## Required fixtures

Positive and negative, at minimum:

- package `const`/`type`/`var` declarations accepted;
- local `const`/`type`/`var` declarations accepted;
- a local variable used by the existing `println` path accepted;
- an unused local rejected with `FIDO-E-UNUSED-LOCAL`;
- cross-file package declarations resolve independent of file order;
- duplicate package names rejected;
- local shadowing of package and predeclared names accepted where Go permits;
- a short declaration with no new nonblank name rejected;
- blank declarations create no binding and no slot;
- `true`, `false`, the predeclared type names, `byte` and `rune` resolve through ordinary binding facts;
- shadowing those names changes resolution exactly;
- an alias preserves identity;
- two distinct defined declarations have distinct identity even with equal underlying types;
- every C6 type-declaration cycle rejected;
- zero values materialize for every admitted basic and defined type;
- every currently accepted program renders **byte-identically** after migration to the ordinary-name path;
- generated C6 programs pass the pinned Go build with their exact expected runtime observation.

The `LAT-019` shift-precision fixtures are **not** C6's; they belong to C7.

## Preserve

- `Syntax.Program` as the sole source authority, and the AST as the one IR;
- the exact retained `Compilable.Program`, `Failure` and whole-elaboration cores, and their sealing;
- `Machine.T` exactly as C5 froze it;
- direct rendering and the one `Emit.Mint.issue` authority;
- certified-module coverage, the whole-theory audit, and controls A-E;
- every sealed-capability, mint, transport and positive client control;
- working-tree and staged-index separation, and no-host-Python;
- `life.md`.

## Done

- every C6 closure and latitude row is discharged or explicitly repriced under review;
- `LAT-077` discharges with its exact diagnostic and fixture;
- no structural type, loop, closure, user function, label, panic, concurrency, composite object or package
  initialization appears;
- exactly one machine exists, and no second run relation or peer evaluator;
- every deleted authority is gone, with no wrapper or compatibility constructor;
- `make prove`, `make check`, `make audit-fresh`, `make regenerate`, `make regen-guard` pass;
- generated bytes change only where a newly admitted construct is actually rendered, with goldens updated in
  the same commit and the differential evidence to justify them;
- both implementation reviews pass, then Rob accepts C6.

## Stop

- the program-indexed `SemanticType` migration cannot be completed without weakening an existing theorem;
- a C6 row needs a construct assigned to a later milestone;
- a new AST constructor cannot land complete, with its `Admissible` rule, machine meaning, rendering proofs
  and differential evidence together;
- `LAT-077` needs a diagnostic the elaboration cannot produce from the retained object;
- the concrete machine would need a second run relation, a peer evaluator, or an empty future field;
- implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound, or premature future
  state.
