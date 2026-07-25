# Fido FCB Architecture Charter

> **Derived reference, not authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document** — its version is the Git blob; its history is the commit log. · **Last updated:** `2026-07-25`  
> **Source repository basis:** `rhencke/fido@ece4c1dd0797eff6e9ebdd5d77a0e59f1c9e76e0`  
> **Amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


This charter carries forward the terminal spec-closure architecture body and all contracts `SC-00` through `SC-22`. It retains the authorized closure of `LAT-X004` with option (ii), the rounding-invariant-domain policy, and incorporates accepted Amendment A001: opaque static capabilities and failure results retain the exact whole compiler object that established their result.

**Source plan SHA-256:** `48ba54aa7d91123c07a3152d75a2f8133599238a2e3e584bf07c4182be5660aa`  
**Pinned Go specification:** `go1.23`, SHA-256 `c47fb4b5b795b9732cbae0250dcb84f791df78bb98695b30fb3f7788d1c9b389`  
**Pinned memory model:** SHA-256 `366b995adeee8b57bd23547feea8252a7ee619baec91cb22cfb21b12208da2c6`

---

## 0. Claim, Closure Rule, and Asymmetric Vow

The claim sought by this plan is **spec-closure**, not age, elegance, confidence, or a model-assigned score.

> The public base is closed under the pinned Go 1.23 language specification and the pinned memory-model obligations used by Fido’s safety claims.

Closure has an exact meaning. The Spec-Closure Ledger walks the pinned specification exhaustively. Every construct has one disposition:

- **IN:** the construct is paper-elaborated through this architecture; each part of its meaning has one named owner; at least one named §25 contract covers it; and inclusion demands no new public source, compiler, type, execution, trace, scheduler, safety, or rendering authority.
- **OUT:** the construct is absent by construction or rejected before `CompilableProgram`; the exact loss is stated; and the full price of any future inclusion is written before implementation. No exclusion may live only in prose, code comments, tests, or custom knowledge. Reflection is explicitly OUT rather than inherited by silence.

The ledger’s closure invariants are:

```text
all pinned spec headings covered
all pinned EBNF productions covered
all reserved keywords and operator/punctuation tokens covered
all predeclared identifiers covered
all grouped constructs split when dispositions differ
all mechanically extracted latitude candidates dispositioned
all named supplemental latitude cases dispositioned
all module/toolchain boundary rows covered
IN => exact representation + one owner chain + named §25 contract
OUT => exact unrepresentability + written inclusion price
no row => no implementation
no new public authority for any row
```

The plan’s vow is deliberately asymmetric:

1. **The public base is frozen.** A future supported construct that requires changing it is evidence that this architecture failed.
2. **The internals are disposable.** §25.22 requires redesign or deletion when proof cost, equality transport, duplication, or a better root appears. Preserving an internal form because work has accumulated around it is failure.
3. **Exclusions are priced, never silent.** A construct cannot enter by incidental syntax, a host helper, or a library call.
4. **Wrong theorem statements are bounded by human review.** When found, the statement, cause, repair, and prevention rule are banked in the project’s lessons and review record. No model may convert its own confidence into acceptance.

### 0.1 Fixed points during revision

The following are fixed. A repair that weakens one is a regression:

1. §1’s deletion and generalization standard.
2. §2’s minimal `Machine` base and the rule that no Go feature defines another run relation.
3. §3’s one-owner-per-meaning table.
4. §5’s fact/use split and the rule that the use builder does not inspect the raw child again.
5. §6’s single type algebra with `RuntimeType := SemanticType Empty_set`, alias non-identity, and declaration-reference recursion.
6. §11’s static-slot/dynamic-place distinction.
7. §13’s stack-only panic/defer/recover design and nested-panic replacement semantics.
8. §15’s resource-local origins with proof-connected provenance.
9. §17’s finite bad-prefix safety with liveness separate.
10. §19’s rejection of vacuous library safety from an empty start set.
11. §24’s Do-Not-Do-Early list, verbatim.
12. §26’s stance that this is a candidate, not an assertion.

### 0.2 Latitude closure rule

The pinned language and memory-model documents are mechanically scanned for the terms listed in the frozen Latitude Manifest. Every candidate sentence has one exact Latitude Ledger disposition:

- **STEP-NONDET:** `step` admits every specification-permitted choice. The choice gains no new label kind; it is visible only through the ordinary Actions produced by the chosen execution.
- **ADEQUACY-DEMOTION:** the observation is not used as a portable specification theorem and is claimed only under the pinned external adequacy contract.
- **PROVED-REFINEMENT:** the model fixes one permitted behavior only after Rob records approval and a named theorem proves accepted programs insensitive to the discarded choices.
- **NOT-LATITUDE:** the sentence is a source permission, prohibition, lower bound, example, or deterministic rule rather than semantic latitude for one accepted program.
- **OUT-COVERED:** the latitude lies wholly inside one named `OUT` row and can enter only after that row’s price is paid.

No candidate may remain implicit. The mechanically extracted set is supplemented by named observable cases whose governing sentence does not contain an extraction trigger, including append growth, ready-case selection, and general goroutine scheduling.

---

## 1. Standard

The architecture must be as simple as possible, but no simpler.

A part remains only when it:

1. prevents a real invalid state;
2. owns a fact that no other part owns;
3. supports a required operation or proof;
4. cannot merge with another part without losing a real distinction;
5. cannot generalize further without becoming weaker or less exact.

No placeholder cases, empty future fields, compatibility paths, trusted semantic shortcuts, fuel, copied authorities, or parallel behavior models may survive.

The lasting design must remain valid after panic, defer, recover, pointers, aliases, recursive types, closures, loops, divergence, channels, scheduling, races, shadowing, constants, methods, interfaces, generics, exact rendering, multi-command modules, and every other `IN` row in the frozen Spec-Closure Ledger are added.

Every proposed field, type, relation, theorem export, module, cache, or helper must answer:

```text
What exact invalid state, operation, or proof fails if this is removed?
Why can its meaning not be owned by an existing part?
Why is this form more basic than every alternative considered?
```

An unclear answer requires deletion.

---

## 2. Permanent Public Semantic Base

Define one general labelled transition machine:

```coq
Record Machine : Type := {
  State  : Type;
  Start  : Type;
  Label  : Type;
  Result : Type;

  initial :
    Start -> State;

  step :
    State -> Label -> State -> Prop;

  final :
    State -> Result -> Prop
}.
```

Fido provides exactly one machine for each accepted program:

```coq
GoMachine :
  CompilableProgram ->
  Machine.
```

All general behavior notions derive from `Machine`:

```coq
FiniteRun
InfiniteRun
Reachable
Stuck
Deadlocked
Trace
FairRun
```

No Go feature defines another run relation.

### 2.1 Why each field remains

| Field | Exact need |
|---|---|
| `State` | Current live execution state |
| `Start` | One exact closed execution start |
| `Label` | Runtime choices, effects, and trace facts that final state cannot recover |
| `Result` | Valid terminal outcomes |
| `initial` | Builds one process from one start |
| `step` | Sole behavior authority |
| `final` | Separates valid terminal states from stuck and deadlocked states |

Nothing else belongs in the permanent public machine base.

### 2.2 Final states are absorbing

For every Fido machine:

```coq
final_states_have_no_steps :
  forall cp s r,
    final (GoMachine cp) s r ->
    forall l s',
      ~ step (GoMachine cp) s l s'.
```

`step` has a global nonfinal side condition. A main-returned state is final even when other goroutines remain. Those goroutines cannot take ghost steps. Fatal process termination is also final and absorbing.

This theorem is part of the permanent machine law, not a property reconstructed by `GoSafe`.

---

## 3. Complete Authority Chain

```text
GoProgram
  -> SyntaxIndex
  -> exact retained whole elaboration
  -> projected total compiler facts
  -> CompilableProgram
  -> GoMachine
  -> runs and safety
  -> SafeProgram
  -> direct rendering of the original GoProgram
  -> DirectoryImage
```

Each kind of meaning has one owner:

| Meaning | Sole authority |
|---|---|
| Source | `GoProgram` |
| Source occurrence identity | `SyntaxIndex` and sealed references |
| Static compilation provenance | The exact retained whole-elaboration object hidden inside the accepted or rejected compiler result |
| Binding, type, use, control, package, initialization, method, layout, and build-plan decisions | Total projections from that retained whole elaboration |
| Runtime behavior and nondeterministic choice | `GoMachine cp` and its `step` relation |
| Runtime history | Labels from runs of that machine |
| Resource provenance needed by later steps | Resource-local state linked by proofs to prior labels |
| Safety | A property over runs of that machine |
| Output source | Direct rendering of the original AST |
| Published bytes | `DirectoryImage` |
| Spec inclusion and exclusion | Frozen Spec-Closure Ledger |

A derived fact table, diagnostic list, layout, or build plan is a projection of the retained whole elaboration. It cannot replace that elaboration as provenance and cannot be independently paired with a foreign causal history.

There is no typed AST, command AST, target AST, executable CFG, runtime type mirror, scheduler program, trace reconstruction pass, parser in the production path, generic host-call escape, or second library semantics.

Derived views are allowed only when they are proved projections of the authority above and cannot mint facts, replace provenance, or choose behavior.

---

## 4. `CompilableProgram` Is the Static Capability

`CompilableProgram` is an abstract static capability minted only by the one production elaborator.

Its hidden representation retains, by construction, the exact successful whole-elaboration object that made the program admissible. That retained object includes the exact source index and retained compilation input, the exact compiler phase objects, the causal outcome history, retained compiler facts, package facts, root layout, build plan, diagnostic projection, and the success evidence over that same object.

The raw constructor and internal records remain private. Internal work, phase, map, trace, and diagnostic forms are not public Go semantics, but they are not discarded. They remain the hidden provenance from which the public total queries are projected.

The public interface exposes the original source, exact source/index references, total compiler-fact queries, accepted root-layout and build-plan queries, and the exact success theorem surfaces required by later layers. Its public shape includes total queries equivalent to:

```coq
source :
  CompilableProgram -> GoProgram

index :
  forall cp,
  SyntaxIndex (source cp)

expr_fact :
  forall cp (r : ExprRef cp),
  ExprFact cp r

expr_use_fact :
  forall cp (r : ExprUseRef cp),
  ExprUseFact cp r

binding_fact :
  forall cp (r : IdentifierUseRef cp),
  BindingFact cp r

blank_use_fact :
  forall cp (r : BlankUseRef cp),
  BlankUseFact cp r

control_fact :
  forall cp (r : ControlUseRef cp),
  ControlFact cp r

method_fact :
  forall cp (r : MethodUseRef cp),
  MethodFact cp r

root_layout :
  forall cp,
  RootLayoutFact cp

build_plan :
  forall cp,
  BuildPlanFact cp

accepted_success :
  forall cp,
  AcceptedSuccessEvidence cp
```

The declarations above freeze the total-query and theorem surface, not a particular internal Rocq record layout.

A successful query does not return `option`. Compilation has already proved that the exact role has one fact.

A public query never reruns elaboration, rediscovers a domain, remints a source reference, reconstructs an equal phase, or obtains provenance from an equality to recomputation.

Equality between the retained result and a canonical rerun may be proved separately as a specification or determinism theorem. That equality is not the capability's retained provenance and is not required to recover any retained object.

A rejected elaboration retains its exact failed whole-elaboration object behind an opaque failure interface. Rejected programs cannot mint `CompilableProgram`, `SafeProgram`, or `DirectoryImage`.

### 4.1 Blank identifier

`IdentifierUseRef` excludes `_` by construction. A blank occurrence has type `BlankUseRef`, binds nothing, and has an exact use fact for its context. For example, `_ = f()` evaluates `f` exactly once and creates no binding.

No `BindingFact` may contain a fake blank target.

### 4.2 Internal compiler forms

Internal compiler objects do not become a second public semantics. One exact object is built at each stage and passed to the next stage. The exact objects that justify an accepted or rejected result remain retained behind the opaque capability or failure boundary.

Opacity restricts access; it never authorizes discarding an object and later rebuilding an extensionally equal replacement. A consumer may receive total projections and theorem surfaces, but no consumer may rediscover a domain, remint a source reference, rebuild a compiler phase, or use specification equality as object identity.

### 4.3 `IndexedProgram`

The current one-field `IndexedProgram` wrapper does not pass the deletion test yet. It must either:

1. gain a real invariant or capability not present in `SyntaxIndex`; or
2. be deleted, with the retained whole elaboration carrying `SyntaxIndex` directly.

This remains an open later foundation decision. Repair 14 may provide new evidence, but neither preservation nor deletion is authorized by this documentation amendment. Any deletion still requires explicit review and authorization.

---

## 5. Facts Depend on Exact Source Roles

Do not use one broad expression record with inactive or optional fields.

Use:

```coq
ExprFact :
  forall cp,
  ExprRef cp ->
  Type

ExprUseFact :
  forall cp,
  ExprUseRef cp ->
  Type
```

An `ExprUseRef` is a proved reference to one child occurrence in one parent role. It is not another syntax node.

`ExprFact` owns context-free facts:

- exact untyped constant kind and value;
- exact typed constant and semantic type;
- exact typed nonconstant result;
- intrinsic operation, call, selector, index, receive, assertion, or instantiation form;
- intrinsic result count and result types.

`ExprUseFact` owns context. The following list is exemplary at plan level and **closed per checkpoint**:

- defaulting;
- assignment and initialization;
- return matching;
- call argument matching;
- conversion operand handling;
- send element handling;
- map key and element handling;
- operator operand selection;
- shift rules;
- comma-ok result selection;
- builtin eligibility;
- interface packing;
- range-clause key and element typing;
- composite-literal key and element matching;
- variadic `...` argument spreading;
- untyped-nil context handling.

Each frozen checkpoint contract enumerates every `ExprUseRef` constructor it introduces. A use kind absent from every accepted contract is unrepresentable. Adding a use kind requires its exact fact, diagnostics, consumers, and §25 fixture in the same checkpoint.

The use builder consumes the exact retained child `ExprFact`. It does not inspect the raw child again.

---

## 6. One Type Algebra

Use one type algebra parameterized by free type variables:

```coq
SemanticType
  (cp : CompilableProgram)
  (V  : Type) :
  Type.
```

Its lasting forms are:

```text
basic type
defined type declaration plus type arguments
type variable
pointer
array
slice
struct
map
channel
function
interface
```

Current non-generic code uses no type-variable case. Generic compiler facts use exact type-parameter references as `V`.

Runtime types are closed:

```coq
Definition RuntimeType cp :=
  SemanticType cp Empty_set.
```

Rules:

- Defined identity comes from the exact declaration reference.
- Generic named identity also includes exact type arguments.
- An alias creates no new identity.
- Recursive named types stay finite through declaration references.
- Unnamed types use structural identity.
- Function results use typed sequences, not a fake tuple type.
- Underlying type, core type, assignability, convertibility, representability, comparability, nilability, method sets, and interface implementation remain separate compiler relations over this one algebra.
- Compiler facts, runtime values, store objects, channels, methods, interfaces, and behavior use this exact algebra.
- Open generic facts close through an exact substitution; runtime values contain only closed types.

There is no numeric `TypeId` registry and no `GoTypeTag`.

### 6.1 Pinned target and `uintptr`

The current target remains direct rather than threaded through every theorem. This invokes `.review/decisions/ADR-0001-PINNED-64-BIT-TARGET.md`, which remains **PROPOSED** and is not accepted by this plan.

`uintptr` is OUT in the Spec-Closure Ledger until Rob accepts ADR-0001 or a replacement target decision and the inclusion price is paid. Ordinary `uintptr` support and `unsafe.Pointer` support are separate decisions.

No broad `TargetConfig` is added until more than one proved target exists or a live proof need earns it.

### 6.2 Floating-point implementation latitude

Floating-point latitude remains inside the one type algebra and one `step` relation:

- division by zero admits every result or structured runtime panic permitted by the pinned specification and IEEE 754 boundary;
- an eligible expression admits both separately rounded and specification-permitted fused evaluation;
- intermediate values admit every precision the specification permits until an explicit conversion or other required rounding point;
- each chosen value flows through the ordinary typed `Value`, panic, read, write, call, and output rules.

No floating-latitude tag, alternate evaluator, or target-specific machine exists. The pinned `go1.23.2 linux/amd64` observation that ordinary `x*y+z` is not fused by default is adequacy evidence only. It does not narrow the specification theorem, and a target change requires revision of the target and Latitude Ledger rows.

---

## 7. Constants and Runtime Values Stay Distinct

```coq
UntypedConstant

TypedConstant :
  forall cp,
  RuntimeType cp ->
  Type

Value :
  forall cp,
  RuntimeType cp ->
  Type

Values :
  forall cp,
  list (RuntimeType cp) ->
  Type
```

Materialization is total:

```coq
materialize_constant :
  forall cp t,
  TypedConstant cp t ->
  Value cp t.
```

A variable read always produces a runtime value. It does not recover the constant status of its initializer.

A hidden dynamic value is only:

```coq
Definition DynamicValue cp :=
  { t : RuntimeType cp & Value cp t }.
```

Nil is a value constructor for nilable forms. Nil is never a failed lookup.

A nil interface remains distinct from an interface containing a typed nil pointer.

Multiple values are a typed sequence, not a tuple type. A function signature, call continuation, assignment, and return fact each state the exact result sequence they consume.

---

## 8. Use Only Three Classes of Dependent Index

Keep dependent indices only where they prevent a direct semantic error:

1. **Source snapshot and exact owner**  
   A reference belongs to one source snapshot, function, declaration, or source-use role.

2. **Semantic type**  
   A value, place, channel entry, argument list, or result list has one exact type.

3. **Static control owner**  
   A slot or control reference belongs to one exact function.

Do not index whole configurations by:

- start;
- trace;
- schedule;
- store generation;
- panic state;
- result;
- fairness policy.

Those facts belong in hidden invariants or derived judgments.

An index stays only when removing it admits an actual invalid state. If it mainly creates equality transport, move the claim into the hidden state invariant or an exported theorem.

---

## 9. Opaque Runtime State and Its Theorem Surface

Do not expose:

```coq
{ raw : RawConfig cp & ConfigWF cp raw }
```

as the public form.

Use an abstract:

```coq
Config cp : Type
```

Only `initial` and `step` create public configurations.

Internally prove:

```coq
initial_well_formed
step_preserves_well_formedness
```

The abstraction boundary includes a permanent theorem surface. At minimum it exports:

```coq
reachable_well_formed
reachable_lookup_total
identity_fresh_monotone
reachable_control_total
```

Their required meanings are:

- `reachable_well_formed`: every state reachable from an accepted start satisfies the full hidden invariant;
- `reachable_lookup_total`: every reachable typed place, slot, live channel entry, and retained resource origin resolves to the expected kind and type;
- `identity_fresh_monotone`: allocation identities and goroutine identities are never reused and freshness advances monotonically along runs;
- `reachable_control_total`: every reachable focus and continuation consumes retained compiler facts and has a valid next-rule domain.

Later clients may receive more theorems only when a §25 contract proves the need. They never receive raw fields or constructors merely to make a proof convenient.

The live state contains only what live features need:

```text
typed object store
scope and slot environments
finite goroutine map
fresh runtime object supply
fresh goroutine supply
resource-local counters required by live operations
```

It does not store:

- the source or compiler result again;
- selected start;
- copied syntax;
- trace or output log;
- global event counter;
- scheduler queue;
- runnable or waiting sets;
- process status;
- deadlock or divergence flags;
- model-fault values.

---

## 10. One Runtime Object Store

All mutable runtime objects come from one private allocation authority.

The minimum lasting object forms are:

```text
typed addressable cell
typed map state
typed channel state
```

A backing array is an addressable array cell, not a separate permanent object kind.

Conceptually:

```coq
Object cp :=
| CellObject :
    forall t,
    Value cp t ->
    Object cp

| MapObject :
    forall k v,
    MapState cp k v ->
    Object cp

| ChannelObject :
    forall t,
    ChannelState cp t ->
    Object cp.
```

The store is one mature finite map from a private object identity to a packed object.

Runtime identities:

- have private constructors;
- can be created only by allocation;
- never repeat;
- retain allocation origin;
- cannot be made from source names, declaration references, natural numbers, trace positions, or type tags.

### 10.1 Places

```coq
Place cp t
```

A place identifies one root cell and one proved projection through arrays or structs to a result of type `t`.

A place may identify:

- a whole variable;
- a struct field;
- an array element;
- a slice backing element;
- a nested addressable subobject.

A map entry is not a place because Go map entries are not addressable.

Pointer values contain nil or one typed place. Nil is not failed lookup.

### 10.2 Strings and string/slice conversion

Strings are values, not mutable objects. Their byte contents do not gain object identity merely because they exist.

`string([]byte)` and `[]byte(string)` allocate fresh backing storage as required. No alias may expose later mutation across the conversion. §25.9 includes named two-way freshness fixtures.

### 10.3 `append` growth and aliasing

`append` has one owner in `step` and the typed store:

- when the current backing capacity is sufficient, the existing backing array is reused;
- when it is insufficient, `step` allocates a fresh backing array and chooses any capacity at least the required new length;
- the returned slice, `cap`, later element writes, and aliases through the old slice observe the selected backing object and capacity;
- the selected capacity is ordinary state, not a new Action or external adequacy choice.

This models the full specification latitude. The pinned allocator growth result is evidence for one permitted branch only.

---

## 11. Static Bindings and Dynamic Cells Are Different

A source declaration can create many runtime variable instances through:

- recursion;
- loop re-entry;
- per-iteration variables;
- closures;
- repeated block entry;
- backward jumps that re-execute a declaration.

Therefore:

- `BindingFact` points to a static object or slot.
- A live scope maps that slot to a dynamic place.
- Re-executing a declaration can allocate a new place.
- A closure captures the old place.
- The active scope can later map the same static slot to a new place.

A source declaration reference never acts as a runtime object identity.

Use one typed environment abstraction parameterized by a compiler-owned slot domain. Package, function, and closure environments use that same base without merging their scope rules.

---

## 12. Source-Indexed Activation Machine

Each goroutine contains a stack of packed activations:

```coq
{ f : FunctionRef cp &
  Activation cp f }
```

An activation contains:

```text
closed type substitution
slot-to-place environment
defer stack
control state
```

The function identity is an index, not a second field that can disagree.

The control state has only:

```coq
Control cp f :=
| Running :
    Focus cp f ->
    Continuation cp f ->
    Control cp f

| Finishing :
    FinishReason cp ->
    Control cp f.
```

No separate cases exist for:

- pending;
- awaiting call;
- runnable;
- waiting;
- caller ID;
- return link;
- process status.

A call leaves a continuation in the caller and pushes an activation.

A blocked source operation remains the current `Focus`. When it is not ready, no transition applies to that goroutine.

Return and panic enter `Finishing`.

### 12.1 Continuation is a source zipper

The continuation contains only:

- exact parent and child-use references;
- values already computed;
- source children still to run;
- the next continuation.

It contains no copied source tree and no compiler decision.

### 12.2 Jumps consume retained target continuations

`break`, `continue`, and `goto` consume retained `ControlFact` values. A jump fact contains both:

```text
exact target source focus
exact target continuation skeleton
```

The machine never constructs a target continuation from a raw source position. No production function of shape:

```coq
continuation_at :
  SourcePosition -> Continuation
```

may exist.

This prevents runtime canonical recomputation from replacing compiler-owned control facts. A backward `goto` that re-executes `:=` allocates fresh dynamic cells while closures retain earlier cells.

A CFG may be derived as a proved view of the same control facts. It cannot own execution or jump construction.

### 12.3 Range over integer and iterator function

All Go 1.23 range domains are owned by the same source zipper and `step`: array, pointer-to-array, slice, string, map, channel, integer, and iterator function.

Integer range uses retained use facts for the iteration value type and produces `0` through `n-1` without a new iterator authority. String range consumes exact bytes and yields byte indices plus decoded runes, including one-byte advance with `U+FFFD` for invalid UTF-8.

Range over function creates one private machine-internal callable value:

```coq
RangeYieldCallable cp range_ref continuation
```

It is not a source declaration, host closure, command, or new public machine field. Its identity and behavior are fixed by the exact range source reference and current source continuation. Invoking it is a `step` rule that:

- checks the iterator function’s retained signature fact;
- transfers zero, one, or two yielded values into fresh per-iteration variables;
- executes the loop body through the same source zipper;
- returns `true` after a continuing iteration;
- returns `false` when the loop body terminates the range;
- records that the yield callable is closed after returning `false` or after the range ends;
- raises the exact structured runtime panic if the iterator calls yield again after it returned `false` or after the loop has ended.

No general “machine-generated function” escape is allowed. `RangeYieldCallable` is the one exact internal callable justified by the pinned range-function rule and is gated by §25.7.

### 12.4 Order-of-evaluation latitude

Fido adopts **Route A: Step nondeterminism**.

Where the pinned specification leaves relative evaluation order unspecified, the source zipper exposes the independent ready subcomputations and `step` admits every permitted next choice. The choice is not recorded by a new label constructor. It becomes observable only through the ordinary Actions caused by that choice: calls, method calls, receives, reads, writes, panics, and output.

Where the specification fixes order, the zipper remains deterministic. In particular, the lexical left-to-right order of function calls, method calls, and receive operations is a named obligation, as are the specified assignment and return evaluation/assignment phases.

A deterministic canonical traversal of unspecified siblings is forbidden because it would under-approximate the pinned specification and make `GoSafe` blind to allowed executions. A proved refinement may replace this nondeterminism only after Rob approves the `PROVED-REFINEMENT` Latitude Ledger disposition and the named insensitivity theorem is proved.

---

## 13. Panic, Defer, and Recover

```coq
FinishReason cp :=
| Returning
| Panicking : PanicValue cp -> FinishReason cp.
```

A finishing activation retains its named result places and remaining defer stack.

A captured defer stores:

- the evaluated function value;
- evaluated argument values;
- the exact defer source reference.

To invoke it, the machine pushes an ordinary function activation directly above the finishing activation.

### 13.1 Load-bearing machine invariant

The invariant is named:

```coq
finishing_pushes_only_deferred_activations
```

It states that the only activation a `Finishing` activation can directly push is one created from its captured defer stack. Ordinary calls are pushed only by `Running` activations. Runtime panic reporting, package finalization, diagnostics, and future helpers cannot add another push rule from `Finishing`.

The derived lemma is named:

```coq
above_finishing_iff_deferred_call
```

It states that a running activation directly above a finishing activation exists exactly because the lower activation invoked that captured deferred call. This lemma is the sole justification for omitting recover provenance fields.

A hypothetical non-defer push from `Finishing` is unrepresentable by constructor absence, not merely unused.

### 13.2 Direct `recover`

`recover` succeeds exactly when:

- the current running activation is directly above a finishing activation;
- the lower activation is panicking;
- the current activation is the captured deferred call identified by `above_finishing_iff_deferred_call`.

A helper call adds another activation, so it cannot recover.

A bare `defer recover()` does not create the required deferred function activation and cannot recover.

No recover token, permission flag, invocation-kind field, caller ID, or global panic context exists.

### 13.3 Nested panic

The activation stack retains nested panic context.

A deferred activation may panic with a newer value while the older finishing activation remains below it. If the newer panic is recovered, the older panic remains. If the newer panic escapes, it replaces the older active panic at the lower finishing activation. A later `recover` observes only the current active panic.

A separate diagnostic panic-report chain may be added only if Fido claims exact fatal report text. It must not become source-observable recover state.

### 13.4 Panic value

```coq
PanicValue cp :=
| UserPanic
    (DynamicValue cp)
| RuntimePanic
    (RuntimeError cp).
```

Runtime panic is not a string. `panic(nil)` follows the pinned Go 1.23 rule.

Model failure is never a panic value.

---

## 14. Goroutines, Scheduler Choice, and Map Iteration

A goroutine contains either:

```text
active activation stack
returned
unrecovered top-level panic
```

No stored runnable or waiting flag exists.

A goroutine is enabled when a `step` rule applies.

A blocked send, receive, select, or nil-channel operation has no local step until the full state permits one.

The global relation chooses any enabled transition. There is no semantic:

- ready queue;
- waiter registry;
- scheduler policy field;
- scheduler stutter step.

A queue or waiter index may exist only as a proved cache derived from the same state.

Fairness is a predicate over infinite runs. It is not part of state or `step`.

### 14.1 Map iteration order has one owner

Range over a map is `step` nondeterminism over the map’s current unvisited key set. The chosen next key, range source reference, map identity, and iteration instance are recorded in the transition’s `Action`.

There is no hidden host-map iterator and no fixed canonical order. A concrete pinned-Go run is checked as membership in one model run with the same observed key order.

Programs with concurrent conflicting map access are excluded by `DataRace` in `BadPrefix`. The implementation-specific runtime fatal throw such as “concurrent map writes” is OUT and is not modeled as a recoverable panic.

---

## 15. One Structured Label per Transition

```coq
Label cp :=
| Silent
| Visible : Action cp -> Label cp.
```

An action has one exact kind, such as:

```text
output
memory read
memory write
allocation
goroutine spawn
map-range choice
channel communication
channel close
```

Do not return an arbitrary list of events from one transition. Evaluation order, scheduling, map iteration, select, floating evaluation, append growth, and initialization latitude do not add a generic `Choice` label. Their selected branch is witnessed only by the ordinary exact Actions and state changes it performs.

An unbuffered rendezvous is one transition. Its action records:

- sender and receiver source references;
- sender and receiver goroutine identities;
- channel identity;
- selected cases where relevant;
- exact value;
- communication token;
- required phase points.

The memory-model view derives phase nodes from that action.

### 15.1 Resource-local origins

No global event log or global fresh event counter belongs in state.

Trace position plus event-specific phase identifies dynamic trace events. Live state retains resource-local origins when future steps need them:

- channel send sequence and channel identity;
- close origin;
- child goroutine identity;
- future lock or atomic epochs only after their package contracts are IN.

A proof connects each retained resource origin to one prior event in the same run.

A buffered channel entry carries its exact send origin. A closed channel carries its unique close origin. A receive that returns zero because of closure names the close origin, never a synthetic zero event.

---

## 16. Derived Behavior, Absorbing Exit, and Decidable Enabledness

From the same `step`, define:

```text
FiniteRun
InfiniteRun
NormalExit
FatalPanic
Deadlocked
```

Meanings:

- **Normal exit:** the main goroutine returned.
- **Fatal panic:** a goroutine reached the top with an unrecovered panic and the process terminated.
- **Deadlock:** main has not returned, the state is not otherwise final, unfinished work exists, and no transition applies.
- **Divergence:** an infinite sequence of real steps.

Main return ends the process even when other goroutines remain. `final_states_have_no_steps` rules out all post-return ghost execution.

There is no fuel.

Blocking is not a result.

Deadlock and divergence are not state fields or ordinary result constructors.

### 16.1 Enabledness decision

Constructive deadlock, select-with-default, negative premises, and run membership require a named decision procedure on reachable states:

```coq
enabled_dec :
  forall cp (s : State (GoMachine cp)),
    Reachable (GoMachine cp) s ->
    ({ l : Label (GoMachine cp) &
       { s' : State (GoMachine cp) &
         step (GoMachine cp) s l s' } })
    +
    (forall l s',
      ~ step (GoMachine cp) s l s').
```

The hard cases include nil channels, buffered readiness, rendezvous, select case readiness, select-with-default, closed channels, and final absorbing states.

`enabled_dec` is a decision procedure for the relational `step`; it does not define another execution semantics. §25.18’s evidence checker and §25.19’s deadlock proof consume this one result.

---

## 17. Safety Is a Finite Bad-Prefix Property

Termination is not baseline safety.

Define exact constructors only:

```coq
BadPrefix :
  forall cp,
  Start (GoMachine cp) ->
  Trace (GoMachine cp) ->
  State (GoMachine cp) ->
  Prop.
```

The live cases are introduced by named constructors. The architecture currently names:

```text
unrecovered fatal panic
global deadlock
data race
```

The external-boundary case set is presently empty inside `GoMachine`. Output materialization, filesystem errors, and pinned tool invocation remain outside language behavior and fail at their named external boundary.

A future external boundary adds one exact `BadPrefix` constructor per represented failure at the checkpoint that introduces that boundary, with a named fixture per constructor. A broad constructor such as “external boundary failed” is forbidden.

Then:

```coq
Definition GoSafe (cp : CompilableProgram) : Prop :=
  forall start trace state,
    FiniteRun
      (GoMachine cp)
      (initial (GoMachine cp) start)
      trace
      state ->
    ~ BadPrefix cp start trace state.
```

This covers every finite reachable prefix under every legal scheduler choice and every accepted start.

It allows:

- recovered panic;
- temporary blocking;
- safe infinite execution;
- scheduler nondeterminism;
- map-order nondeterminism.

Liveness remains separate:

```text
may terminate
terminates under every legal run
terminates under every fair run
may diverge
cannot diverge
```

Finite and infinite behavior use the same `step`.

---

## 18. Model Faults Stay Outside Go Behavior

A wrong lookup, wrong object kind, wrong type, missing compiler fact, malformed continuation, forged origin, or impossible dispatch is not:

- panic;
- nil;
- zero;
- block;
- normal exit;
- deadlock;
- unknown.

It has no machine step.

The core proof chain is:

```coq
initial_is_well_formed
step_preserves_well_formedness
reachable_well_formed
reachable_lookup_total
well_formed_progress_or_final_or_deadlock
enabled_dec
```

An open diagnostic interpreter may report an internal model defect during development. That report stays outside `GoMachine` and cannot be observed by source code.

---

## 19. Starts

`Start (GoMachine cp)` is the general form.

For current closed executable programs, a start selects:

- an exact command package;
- its exact `main`;
- its package dependency closure;
- its proof-carrying package initialization plan.

A module can have several starts.

Safety covers all starts.

A module without a command package has no closed command start. Open-world library safety requires an explicit call contract and must not follow from an empty start set.

Later closed test harnesses can add exact start forms only through a frozen contract. They cannot invoke arbitrary source declarations without static call facts and a closed environment.

---

## 20. Package Initialization

The compiler retains an exact initialization dependency object:

```text
package dependency order
package-variable dependency partial order
initializer source references
init function source references
main source reference
proof that every required edge is present
proof that the dependency graph is acyclic
```

An initialization cycle cannot inhabit `ProgramFacts` or `CompilableProgram`; elaboration rejects it with an exact diagnostic.

The initial goroutine performs initialization through the same activation machine and the same `step` relation. At each point, `step` may select any initializer ready under the retained partial order when the pinned specification leaves its order relative to another initializer unspecified. Specified dependency and file/declaration-order edges remain deterministic obligations.

The selected order is visible only through the initializers’ ordinary calls, reads, writes, spawns, panics, and outputs. There is no package-initialization evaluator, precomputed total order, or hidden scheduling authority beside the function machine.

---

## 21. Methods, Interfaces, and Closing Substitution

The compiler owns:

- receiver binding;
- method sets;
- selector resolution;
- promotion and ambiguity;
- interface requirements;
- structural implementation;
- receiver adjustment;
- exact dispatch target.

A runtime interface value is nil or contains:

```text
closed dynamic non-interface type
value of that type
proof that the type implements the static interface
```

Interface-to-interface assignment preserves the same dynamic type and value. It does not wrap one interface value inside another.

Dispatch consumes the same retained method facts that proved implementation.

The load-bearing generic lemma is named:

```coq
implements_closed_substitution
```

It proves that an implementation fact established with open type variables is preserved by a valid closing substitution. Interface packing of an instantiated generic value, dispatch, and assertion consume the substituted retained fact. They do not re-run conformance and do not consult a runtime registry.

There is no source dictionary, copied vtable, runtime type tag, rendered-name lookup, or plugin method choice.

---

## 22. Rendering, External Adequacy, and Nondeterministic Membership

The renderer consumes only the original source AST.

It does not consume:

- runtime values;
- frames;
- objects;
- traces;
- CFGs;
- lowered commands;
- method tables.

Cross-layer theorems belong in a theorem-only module that imports compiler facts, behavior, and rendering. `GoRender` should not import runtime behavior merely to hold those theorems.

The parser never enters the production path.

`DirectoryImage` remains because it pins the exact byte snapshot used by validation and publication. Its constructor is private.

The Go compiler and runtime remain a named pinned external trust boundary. Fido proves the accepted source, its model, and exact bytes. Differential tests check the external toolchain.

### 22.1 Claim (B) under nondeterminism

For deterministic observations, the existing byte-equality differential remains.

For scheduling, select, map iteration, and other nondeterministic behavior, “matches” means **membership**:

> The concrete pinned-Go observable sequence must be certified as the projection of at least one run of `GoMachine cp` from the same start.

A proved evidence checker consumes:

- a well-formed state;
- a proposed label/choice witness;
- the concrete observation;
- `enabled_dec` and the decision procedure for the relevant `step` instance.

It returns evidence of the relational `step` or rejects the witness. It is not a semantic authority and cannot create a transition that the relation does not admit. Its correctness and completeness against `step` are gated theorems.

Instrumentation may expose scheduler, select, or map-order choices needed for membership evidence. Instrumentation is test-only and cannot change the generated program’s semantics.

### 22.2 Emitted module and pinned executor

The emitted `go.mod` contains exactly:

```text
module <the accepted ModulePath>

go 1.23
```

The module directive consumes the one accepted `ModulePath` authority. The `go` directive equals the language version of this ledger. The frozen module parser source proves those directives are read as exact `module` and `go` statements, and the frozen `gc.go` source proves the selected module Go version is passed to the compiler as `-lang=go1.23`. Changing either directive or either governing source is a ledger-revision event under human review, not a renderer detail.

Validate-then-publish invokes the exact pinned `/usr/local/go/bin/go` binary whose hash is recorded above, with at least:

```text
GOTOOLCHAIN=local
GOENV=off
GOWORK=off
```

and verifies `go version go1.23.2 linux/amd64` before the build. `GOTOOLCHAIN=local` forecloses automatic toolchain switching; `GOENV=off` forecloses a user-written Go environment file; `GOWORK=off` forecloses ambient workspace selection. A `toolchain` directive is not emitted. This invocation contract is external adequacy, not GoMachine state.

Executor identity is derived from one complete Go distribution, not from a standalone front-end hash. Confirmed evidence requires the verified official `go1.23.2.linux-amd64.tar.gz`; pending evidence copies the local Go distribution into the closed sandbox, records a complete path/type/mode/symlink/hash manifest, and marks every affected pin and observation `PROVENANCE-PENDING`. The current evidence target is `go1.23.2 linux/amd64`; the platform target set remains under pending ADR-0004, and no other platform claim is made here.

### 22.3 Terminal observation tuple

The one external observation tuple is:

```text
(stdout bytes, stderr projection, exit status)
```

The stderr projection is exact by case:

1. **Ordinary model output:** an `Output` Action names its stream. Under the current pinned built-in contract, `print` and `println` map to stderr; no bytes from them map to stdout.
2. **Normal exit:** exit status is `0`; stdout and stderr consist only of bytes justified by model Output Actions.
3. **Fatal panic adequacy:** exit status is `2`; stdout is matched by model Output Actions; the first stderr line must equal the pinned rendering `panic: <panic value>`. The remaining traceback bytes are retained as evidence but are not a language-spec theorem and are ignored by the formal membership projection.
4. **Runtime noise:** stderr bytes not justified by an Output Action or the stated fatal-panic projection are outside the current adequacy contract. Their exclusion is explicit and owned by `BOUND-X009`; they are never silently discarded.

Deterministic equality and nondeterministic membership both compare this same tuple. A future package contract that writes to a stream must add an exact Output Action and observation rule at its checkpoint.

---

### 22.4 Acceptance alignment

Pinned-gc acceptance is part of the external adequacy boundary. It does not own language meaning, and probe evidence does not prove the global subset theorem.

The standing obligation is:

```text
fido_accepts_subset_pinned_gc
```

It is split into three exact claims:

1. **Formal:** every `CompilableProgram` satisfies each accepted implementation-restriction row. Each implementing checkpoint discharges its own restriction with an elaboration rule and exact diagnostic.
2. **External:** a publishable `DirectoryImage` passes the pinned-gc preflight under the one closed probe environment.
3. **Evidence:** this documentary bundle records pinned-gc observations and freezes the future Fido fixtures. A finite probe set is evidence for the selected profile, not a proof of the formal theorem.

The Latitude Ledger disposition `ACCEPTANCE-ALIGNMENT` owns these restrictions. Each row has an individual justification, one pinned-gc fixture observation, one frozen future-Fido diagnostic obligation, one owning contract, and one implementing checkpoint. Until that checkpoint runs both halves, the Fido half remains `PENDING-IMPLEMENTATION`.

Constant-expression **value** latitude is separate. `LAT-X004` is owned by closure row `SPEC-096`, intrinsic `ExprFact`, and `SC-05-EXPR-FACT-USE-EVAL`. `SC-22` owns only admission into `CompilableProgram`. FCB v3 retains option (ii), the proved rounding-invariant accepted-domain policy. `ExprFact` retains the unique exact value of every accepted constant expression; expressions outside the proved domain must be rejected with the acceptance-gate diagnostic. Ownership remains `SPEC-096` / `ExprFact` / `SC-05`.

---

## 23. Deletion Is Individually Gated

Delete when complete replacements exist:

- one-field `IndexedProgram`, unless it gains a real invariant;
- `ExprFact.ef_use_resolved`;
- production raw `eval_expr`, `eval_stmt`, `eval_decl`, and `eval_file`;
- unconditional `certify` once a real violation is representable;
- `EConvert`, `SPrintln`, and `DMain` after complete general forms replace them;
- source-name comparisons used as semantic identity;
- optional lookup after accepted compilation;
- raw numeric runtime references;
- runtime type tags;
- trace reconstruction;
- global event log or event counter;
- scheduler authority beside `step`;
- fuel, gas, step budgets, or renamed bounds;
- compatibility paths that preserve special and general forms together;
- peer command, CFG, target, or typed-source execution models.

Each deletion is its own gated commit. The commit includes:

1. the fixture or theorem proving the replacement covers the old behavior;
2. the deletion itself;
3. a full-tree search showing no compatibility path remains;
4. where possible, a `Fail Definition` or constructor-absence proof showing the old form is unrepresentable.

Bulk deletion commits are forbidden because they hide surviving paths.

---

## 24. Current Repository Reconciliation

### Keep

- `GoProgram` as sole source authority.
- `SyntaxIndex` and sealed references.
- C4 `CompilationInput` and `ExprWorkForest` as internal one-domain construction.
- exact phase object identity.
- `ElaborationFacts`.
- full `CompilableProgram` provenance.
- exact constants and `TypedConst`.
- direct source rendering.
- `DirectoryImage`.
- transport-only extraction and materialization boundary.

### Change at approved checkpoints

- make `CompilableProgram` opaque;
- split expression facts from use facts;
- expose total fact-backed behavior queries;
- replace production raw source evaluation with retained fact consumption;
- move cross-layer semantic theorems out of `GoRender`;
- seal `DirectoryImage` construction;
- replace unindexed runtime values at the first nonconstant runtime feature;
- add only the source constructors, facts, rules, and tests named by the accepted checkpoint’s Spec-Closure rows.

### Whole-result retention

- Every proof-carrying compiler phase built by the production path must survive any later capability or result boundary when later proofs depend on its identities, predecessors, or causal history.
- Selected projections plus equality to rebuilding the compiler result do not satisfy this obligation.
- Accepted and rejected compilation both retain the exact whole-elaboration object.
- `SafeProgram` refines the same exact accepted capability.
- Rendering continues to project the original `GoProgram` and does not evaluate elaboration.

This is the active C4 blocking obligation introduced by A001. The repair-13 candidate does not yet satisfy it; repair 14 must establish it before C4 can return for human review.

### Do Not Do Early

- do not add runtime state before the compiler fact/use boundary is complete;
- do not add functions through a special evaluator;
- do not add concurrency through a command language;
- do not add empty future modules or state fields;
- do not retain old demo paths after the general path exists.

The current C4 source forest, exact work index, and causal outcome trace follow the one-construction rule inside the compiler. They must remain internal compiler forms, and A001 now requires their exact accepted or rejected whole elaboration to survive the final capability boundary rather than be rebuilt later.

---

## 25. Frozen Spec-Closure Proof Contracts

Every contract below is frozen in its own `.review` file with a SHA-256 **before** implementation begins. A test cannot be softened after proof cost appears. A redesign changes the internal candidate and reruns the unchanged contract. Changing a contract is a separate human review act.

Every `IN` row in the Spec-Closure Ledger names at least one contract below. An `IN` row without a frozen contract is not eligible for implementation.


### 25.0 Contract map

This table is generated from and must remain a byte-for-byte projection of the contract headings below.

| Contract | Plan section |
|---|---:|
| `SC-00` | §25.1 |
| `SC-01` | §25.2 |
| `SC-02` | §25.3 |
| `SC-03` | §25.4 |
| `SC-04` | §25.5 |
| `SC-05` | §25.6 |
| `SC-06` | §25.7 |
| `SC-07` | §25.8 |
| `SC-08` | §25.9 |
| `SC-09` | §25.10 |
| `SC-10` | §25.11 |
| `SC-11` | §25.12 |
| `SC-12` | §25.13 |
| `SC-13` | §25.14 |
| `SC-14` | §25.15 |
| `SC-15` | §25.16 |
| `SC-16` | §25.17 |
| `SC-17` | §25.18 |
| `SC-18` | §25.19 |
| `SC-19` | §25.20 |
| `SC-20` | §25.21 |
| `SC-21` | §25.22 |
| `SC-22` | §25.23 |

### 25.1 `SC-00-PIN-LEDGER-CLOSURE`

Prove and audit:

- the pinned spec, memory-model, cmd/go documentation, toolchain-selection source, and executor hashes;
- every pinned heading appears in the heading manifest;
- every pinned EBNF production appears in the grammar manifest;
- every reserved keyword and operator/punctuation token appears in the token manifest;
- every predeclared identifier appears in the predeclared-identifier manifest;
- every mechanically extracted latitude sentence appears in the Latitude Manifest and has one Latitude Ledger disposition;
- every required supplemental latitude case appears in the Latitude Ledger;
- every module/toolchain BOUND row is present;
- every finite-domain entry has at least one ledger row;
- every row is `IN` or `OUT`;
- every `IN` row has one owner chain and a named §25 contract;
- every `OUT` row has constructor-level unrepresentability and a written future price;
- every row states no change to the §2 public base;
- a future spec/toolchain version requires a new pin and full ledger walk.

### 25.2 `SC-01-SOURCE-LEXICAL-RENDER`

Cover source representation, Unicode validity, identifiers, tokens, semicolon insertion, keywords, operators, punctuation, canonical literal spelling, and source-file organization.

Prove the renderer’s admitted source forms encode exact source values and that excluded comments, raw-string spelling, raw-source parsing, build constraints, and directives have no constructors.

### 25.3 `SC-02-CONSTANTS-LITERALS`

Cover integer, floating-point, imaginary, rune, interpreted string, boolean, exact untyped constants, typed constants, `iota`, constant expressions, representability, defaulting, overflow, and materialization.

No fixture bound may replace a spec bound. Any current DecimalFloat restriction must receive its own human disposition before the full floating-literal row can become implemented.

### 25.4 `SC-03-BINDINGS-DECLARATIONS-BLANK`

Cover blocks, scopes, labels, exported and unique identifiers, predeclared shadowing, declarations, short declarations, per-iteration variables, closure capture, static slots, dynamic places, and blank uses.

Required blank fixture:

```go
_ = f()
```

`f` evaluates exactly once and no binding is created.

### 25.5 `SC-04-TYPES-PROPERTIES-GENERICS`

Cover the one type algebra; underlying/core type; identity; assignability; conversion; representability; comparability; nilability; arrays, slices, structs, pointers, maps, channels, functions, interfaces; aliases; defined types; type parameters; constraints; instantiation; inference; and type unification.

Required recursive-type fixture and open-to-closed generic substitution fixture must pass without another type identity system.

Required struct-tag fixtures:

- tags participate in struct type identity;
- conversion between otherwise identical struct types ignores tags exactly where the pinned rule permits it.

### 25.6 `SC-05-EXPR-FACT-USE-EVAL`

Cover one context-free fact per expression, one exact fact per use edge, operands, qualified identifiers, composite literals, primary expressions, selectors, indexing, slicing, assertions, calls, variadics, operators, conversions, short-circuiting, multiple results, comma-ok selection, and specified evaluation order.

The production path performs no raw re-analysis. Every use kind introduced by the contract is enumerated; absent use kinds are unrepresentable.

Latitude fixtures:

- one expression where two specification-permitted sibling orders produce different ordinary Action sequences, with both certified as runs;
- one expression proving function calls, method calls, and receives keep their specified lexical left-to-right order;
- one floating expression with distinct fused and separately rounded results, with both model branches admitted;
- pinned-toolchain evidence records that ordinary `x*y+z` follows the unfused branch under `go1.23.2 linux/amd64`, without turning that evidence into a specification theorem;
- one division-by-zero fixture covers every admitted result/panic branch;
- one retained-extra-precision fixture proves explicit conversion forces the required rounding point.

### 25.7 `SC-06-SOURCE-ZIPPER-CONTROL`

Implement calls, multiple results, statements, loops, switches, labels, `break`, `continue`, `goto`, `fallthrough`, return, short-circuit control, and blocking with only:

```text
Running focus continuation
Finishing reason
```

Required theorems and gates:

- jump targets consume retained `ControlFact` continuation skeletons;
- no production `continuation_at : SourcePosition -> Continuation` exists;
- no runtime source walk constructs a jump continuation;
- a backward `goto` over `:=` allocates a fresh place on re-execution;
- a closure captured before the jump retains the old cell;
- range over arrays, slices, strings, maps, channels, integers, and iterator functions uses the same zipper;
- string range handles invalid UTF-8 with `U+FFFD` and one-byte advance;
- integer range closes the untyped/defaulted iteration type through retained use facts;
- iterator-function range uses only `RangeYieldCallable`, fresh per-iteration variables, and the same `step`;
- calling yield after it returned `false` or after the range ended produces the pinned structured runtime panic.

No command language, host callback semantics, broad statement-completion result, or general machine-generated function escape may appear.

### 25.8 `SC-07-FUNCTIONS-CLOSURES-MULTIRESULT`

Cover function declarations and literals, methods as callable declarations, parameters, named and unnamed results, variadics, closures, recursion, method expressions, method values, argument/result typed sequences, and exact call/return continuations.

### 25.9 `SC-08-STORE-PLACES-CONVERSIONS`

Implement variables, arrays, structs, pointers, slices, maps, aliases, allocation, addressability, indexing, slicing, append, copy, clear, delete, `make`, `new`, numeric conversions, string conversions, and slice-to-array conversions.

Prove:

- no forged identity;
- no identity reuse;
- total typed lookup on reachable states through `reachable_lookup_total`;
- exact subobject overlap;
- closure retention of old dynamic cells;
- map entries are non-addressable;
- strings are values, not mutable objects;
- `string([]byte)` allocates fresh bytes and later source-slice mutation cannot change the string;
- `[]byte(string)` allocates fresh bytes and later result mutation cannot change the string;
- proof transport does not dominate ordinary rules;
- when append has sufficient capacity, the returned slice aliases the existing backing array;
- when append requires allocation, at least two permitted fresh capacities are valid model branches and writes through the old slice cannot change the new backing array;
- comparison of distinct zero-size variables admits both specification-permitted equality results without merging their object identities.

### 25.10 `SC-09-PANIC-DEFER-RECOVER`

Implement named results, defer registration, mutation, panic, nested deferred panic, direct recovery, helper recovery failure, repeated recovery, result update, and normal return.

Gated theorems:

```coq
finishing_pushes_only_deferred_activations
above_finishing_iff_deferred_call
```

Required negative proof: a non-defer push from `Finishing` is unrepresentable by constructor absence.

Required fixtures:

- a deferred function directly recovers;
- a helper called by that deferred function cannot recover;
- bare `defer recover()` cannot recover;
- a newer recovered panic leaves the older panic active;
- an escaping newer panic replaces the older active panic.

No recover token, panic monad, global panic state, or second panic evaluator may appear.

### 25.11 `SC-10-GOROUTINES-CHANNELS-SELECT`

Implement goroutine creation, buffered and unbuffered channels, nil channels, send, receive, close, range over channels, select, default, closed-drained receive, blocking continuation retention, and scheduler nondeterminism.

`enabled_dec` is a prerequisite. No ready queue, waiter registry, or second scheduler authority may decide behavior.

Required latitude fixtures:

- two ready select cases both produce valid Step branches;
- default is selected only when no communication can proceed;
- two enabled goroutines can produce both permitted schedules, with fairness tested only as a run predicate.

### 25.12 `SC-11-MAP-ITERATION-NONDET`

Use a map with at least two keys.

Prove:

- each valid next-key choice is a `step` branch;
- both key orders are valid runs;
- the chosen order appears in `Action` labels;
- no host map order or canonical sort chooses semantics;
- the pinned-Go observed order can be checked as membership in a model run;
- concurrent conflicting map access reaches `DataRace` and does not require modeling the runtime fatal throw.

### 25.13 `SC-12-HB-RACE-CHANNEL-EDGES`

The channel edge set is exhaustive and named. The contract must prove all four:

1. **send-to-receive-completion:** the `k`-th send happens before completion of the `k`-th receive from that channel;
2. **capacity edge:** for capacity `C`, the `k`-th receive happens before completion of the `(k+C)`-th send;
3. **close-to-zero-receive:** close happens before a receive that returns zero because the channel is closed;
4. **unbuffered receive-to-send-completion:** on an unbuffered channel, the receive happens before the corresponding send completes.

Each edge has:

- one positive fixture showing the edge derives from labels;
- one negative fixture whose race result changes if that edge is missing.

Also cover spawn and package-initialization edges. Trace events come only from `step`; no trace reconstruction or synthetic origin is allowed.

### 25.14 `SC-13-INTERFACE-GENERIC-CLOSURE`

Implement value and pointer receivers, method sets, promoted selectors, typed nil, nil interface, interface assignment, dispatch, method values, assertion, type switches, interface comparison, and generic named types with methods.

Gated lemma:

```coq
implements_closed_substitution
```

Joint fixture:

- define a generic named type with a method;
- prove open implementation against an interface;
- instantiate at a closed type;
- pack it into the interface;
- dispatch through the interface;
- assert it back out;
- prove dispatch consumes the substituted retained fact;
- show no runtime type registry or re-derived conformance appears.

### 25.15 `SC-14-PACKAGES-INIT-STARTS-EXIT`

Cover package clauses, imports including aliases/blank/dot forms, import cycles, package scopes, dependency closure, zero values, package variable initialization, `init`, program initialization, multiple command roots, main execution, and main return.

Required fixtures and theorems:

- two command packages produce two exact starts and independent initial states;
- the emitted `go.mod` contains exactly the accepted module path and `go 1.23`;
- no `toolchain` directive is emitted;
- the pinned invocation cannot switch away from the hashed `go1.23.2` executor;
- initialization follows every required dependency edge;
- two initializers left unordered by hidden dependencies can execute in both specification-permitted orders;
- a two-variable initialization cycle is rejected and cannot mint `CompilableProgram`;
- an acyclic variant initializes in dependency order rather than source order;
- main returns while another goroutine is blocked mid-send;
- the result is `NormalExit`, not `Deadlocked`;
- no post-main step exists;
- `final_states_have_no_steps` is gated.

### 25.16 `SC-15-BUILTINS`

Cover every predeclared built-in admitted by the ledger: append, cap, clear, close, complex, copy, delete, imag, len, make, max, min, new, panic, print, println, real, and recover.

Each built-in resolves through normal binding facts, receives exact use facts, and executes through `step`. `print`/`println` output formatting is a pinned-toolchain adequacy claim, not a portable language theorem.

Required fixtures:

- append capacity and aliasing follow §10.3 and expose every specification-permitted growth branch;
- a NaN-keyed map entry is insertable, contributes to `len`, cannot be retrieved by lookup, cannot be removed by `delete`, and is removed by `clear`;
- `println` evaluates operands once and emits its pinned observation to stderr.

### 25.17 `SC-16-ERRORS-UNREPRESENTABILITY`

Cover exact static diagnostics, invalid program rejection, runtime panic constructors, and every `OUT` boundary’s constructor absence.

No rejected program can mint `CompilableProgram`, `SafeProgram`, or `DirectoryImage`.

Static acceptance and rejection are decided over one exact retained whole-elaboration object. Every represented static error projects from the exact rejected object which produced it. The public failure interface may hide the object, but it retains it. A diagnostic list copied out of a discarded failed phase is insufficient.

Required gates include exact accepted-core retention, exact rejected-core retention, and direct failure-cause queries that perform no compiler rerun.

No broad “unsupported” catch-all constructor is allowed where the ledger names distinct exclusions.

### 25.18 `SC-17-RENDER-ADEQUACY-MEMBERSHIP`

Prove direct rendering covers every admitted source constructor, preserves exact literal values and grouping, has no raw-text escape, and yields the one `DirectoryImage` publication path.

For deterministic programs, pinned-Go observations match by the exact terminal tuple `(stdout bytes, stderr projection, exit status)`.

For nondeterministic programs, a concrete pinned-Go observation is accepted only by a proved membership checker against `GoMachine` runs. The checker is sound and complete for the evidence form it accepts and consumes `enabled_dec`; it does not define semantics.

Required adequacy fixtures:

- `println` produces zero stdout bytes, its exact pinned text on stderr, and exit status `0`;
- an unrecovered `panic("fido-panic")` produces exit status `2` and first stderr line `panic: fido-panic`; traceback remainder is evidence-only under §22.3;
- stderr noise outside Output Actions or the fatal-panic projection is rejected as outside the current contract;
- the emitted `go` directive is exactly `1.23`, and the exact pinned executor remains selected under the stated environment.

### 25.19 `SC-18-ENABLEDNESS-DECISION`

Gate:

```coq
enabled_dec
```

Cover:

- nil-channel send and receive;
- buffered full/empty readiness;
- unbuffered rendezvous;
- close and closed receive;
- select with several ready cases;
- select with no ready case and default;
- select with no ready case and no default;
- final absorbing states;
- deadlock classification.

The constructive decision must agree exactly with relational `step` on reachable well-formed states.

### 25.20 `SC-19-OUT-BOUNDARIES`

For every `OUT` row, freeze:

- exact missing source/fact/runtime constructor;
- valid Go programs or environments lost;
- reason for exclusion;
- future-inclusion price;
- proof that no host helper or generic fallback can introduce the behavior.

The contract explicitly covers comments, raw source parsing, raw strings, `uintptr`, package `unsafe`, size/alignment, prior language modes, implementation-specific system behavior, reflection, uncontracted standard-library packages, cgo, assembly, directives, build constraints, finalizers, plugins, dynamic loading, platform resource limits, hostile local-verifier tampering, and all uncontracted compiler/runtime behavior.

### 25.21 `SC-20-EVAL-ORDER-LATITUDE`

Freeze the complete Latitude Ledger and prove every `STEP-NONDET` row is owned by the one relational `step` without a generic choice authority.

Required cross-contract fixtures:

- unspecified expression sibling order admits both visible Action sequences;
- specified lexical left-to-right calls, methods, and receives admit one order;
- fused and separately rounded floating evaluation are both runs where permitted;
- append allocation admits multiple sufficient capacities while sufficient existing capacity forces reuse;
- ready select cases, map keys, enabled goroutines, and unordered initializers each expose every permitted branch;
- distinct zero-size pointer equality admits both permitted results;
- memory-model composite/word decomposition emits the actual sub-access order;
- every `ADEQUACY-DEMOTION`, `NOT-LATITUDE`, and `OUT-COVERED` row is checked against its stated owner and cannot mint a Step branch by fallback.

No latitude row may add a public Machine field, a second evaluator, a scheduler object, a generic `Choice` Action, or an unreviewed refinement theorem.

### 25.22 `SC-21-PROOF-COST-INTERNALS`

The public base is fixed. Internal forms remain candidates.

Measure and attack:

- source-indexed continuation cost;
- heterogeneous store and typed place cost;
- resource-local provenance and phase proof cost;
- open static types closed for runtime;
- stack-only panic/defer/recover;
- decision procedure extraction and proof cost.

Keep an internal type or index only when removing it admits a real invalid state. If equality transport, proof duplication, or compensating lemmas dominate normal semantics, replace or delete the internal form. Do not soften another §25 contract to save an internal design.

Internal forms remain disposable only when their replacement preserves the exact public guarantees and the exact causal objects required by later layers. “Internal” or “opaque” never means “safe to discard and reconstruct.”

At every publish boundary, inspect constructor topology: if a later capability or failure result retains only copied fields plus equality to recomputation, the internal design has failed even when extensional theorems pass.

Clinging to an internal form because it is implemented is a contract failure.

---

### 25.23 `SC-22-ACCEPTANCE-ALIGNMENT`

Freeze and discharge `fido_accepts_subset_pinned_gc` without making pinned gc a language-semantics authority.

The contract requires:

- every implementation-restriction latitude candidate is classified exactly once as `ACCEPTANCE-ALIGNMENT`, `OUT-COVERED`, or `NOT-LATITUDE`;
- every `ACCEPTANCE-ALIGNMENT` row has a unique justification, a pinned-toolchain observation, a future Fido elaboration obligation, an exact diagnostic ID and text-or-shape, and an implementing checkpoint;
- pinned observations run under the closed `PROBE_ENVIRONMENT.tsv` profile and retain raw stdout, stderr, exit status, exact command, effective `go env`, and distribution provenance;
- a finite probe set never claims to prove the global subset theorem;
- the publication path rejects any `DirectoryImage` the pinned toolchain rejects;
- the formal subset theorem is discharged incrementally by the checkpoint that makes each restriction representable;
- `LAT-X004` is closed by a proved rounding-invariant accepted domain; ownership remains `ExprFact`, closure row `SPEC-096`, and `SC-05`; no acceptance row may own or silently select a constant value;
- the first frozen future-Fido fixtures cover the pinned constant limit, general-interface union restriction, unused local, empty-type-set operand, duplicate constant switch case, shadowed-result naked return, and unsupported `print`/`println` argument type.

`CompilableProgram` is minted from the exact retained accepted whole elaboration. `CompileFailure` retains the exact rejected whole elaboration. Acceptance-alignment fixtures and publication checks consume projections from those retained objects; they do not rerun elaboration to reconstruct acceptance evidence.

The global subset theorem may compare the retained result with pinned-toolchain acceptance, but no such comparison becomes the compiler's retained provenance.

A future change to the pinned language version, Go distribution, probe environment, or acceptance policy is a ledger revision under human review.

---

## 26. Acceptance and Freeze Rule

The architecture becomes eligible for citation by a checkpoint contract only when all of the following hold against the same frozen commit:

1. every BLOCKING and REQUIRED external-review or repair finding has a model-recorded `APPLIED` disposition with an empty-or-completed Rob countersign field, or a human-approved `REJECTED` ADR rationale; citation requires Rob’s countersign for every applicable row;
2. every RECOMMENDED and EDITORIAL finding has a recorded disposition before citation;
3. the plan, Spec-Closure Ledger, Latitude Manifest and Ledger, all finite-domain manifests, disposition ledgers, scripts, pinned documents, and freeze record have exact SHA-256 values;
4. the shipped audit reports every pinned heading, EBNF production, reserved keyword, operator/punctuation token, predeclared identifier, module/toolchain boundary, and latitude candidate covered; no blank disposition; every `IN` row owned and tested; every `OUT` row priced; and every retained template row explicitly flagged lexical-only;
5. all applicable frozen §25 contracts pass without a second public authority;
6. each internal redesign preserves the public base and leaves no compatibility path;
7. the current scope ledger agrees with every implemented IN/OUT frontier;
8. actual generated Go passes the pinned build and deterministic equality or nondeterministic run-membership method, as applicable;
9. `make prove`, `make e2e`, `make check`, and `make regenerate` are green on the exact frozen commit;
10. wrong theorem statements found during review are repaired and banked in the project’s lessons with a prevention rule.

**Each condition’s satisfaction is a human review act by Rob, recorded in `.review`. No model may declare any condition met. Conditions 1–10 are evaluated only against frozen commits with green `make prove`, `make e2e`, `make check`, and `make regenerate`.**

Rob owns every countersign and the decision that a frozen artifact may be cited by a checkpoint contract. Model-authored `APPLIED` records prove only that text was changed; they do not prove that a finding is resolved.

A change to the §2 public base after acceptance is architecture failure and requires a new architecture review, not a checkpoint amendment.

A change to an internal form under §25.22 is normal and required when it simplifies proofs or removes duplication.

This document remains a candidate until Rob records acceptance. It is not self-executing.

---

## 27. Attributed Confidence and Open Proof-Cost Reserves

**Authoring model confidence statement:** The public base appears complete for the pinned closure ledger and no known `IN` row requires another public authority. This statement is advisory, unscored, and excluded from all acceptance reasoning.

The unresolved risk is proof cost, not an identified missing public category. Real Rocq work may still replace internal forms in:

- source-indexed continuations and retained jump skeletons;
- typed places and heterogeneous storage;
- resource-local origins and event phases;
- open generic types and closing substitutions;
- stack-only panic, defer, and recover;
- enabledness and step-membership decision procedures;
- exhaustive implementation-latitude branching without proof duplication.

Sub-value and machine-word access granularity is deliberate proof cost that affects condemned runs, not reachable safe-run behavior; it may be narrowed only by a future countersigned ledger disposition.

The response to failure is asymmetric:

- do not change the public base to save an internal form;
- do not weaken a frozen §25 contract;
- replace or delete the internal form;
- record the failure and lesson;
- rerun the same contract.

No numerical score appears in this document. Any acceptance or score belongs to Rob and has no force unless recorded under §26.

---

## 28. Governance Boundary

This plan and its companion ledgers are development-discussion artifacts only until accepted under §26.

They do not:

- accept C4;
- authorize C5;
- modify `.review/C4_IMPLEMENTATION_REPAIR_6.md`;
- supersede `.review/NEXT_STEPS.md` as the active authority pointer;
- resolve ADR-0001 or ADR-0002;
- authorize any implementation of an `IN` row;
- weaken any current unrepresentability frontier.

The main review thread remains authoritative for C4 acceptance. The latest repair directive remains the active implementation authority.
