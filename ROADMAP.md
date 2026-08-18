# Roadmap

What is left to build, in dependency order. `.review/NEXT.md` owns the active task; this file owns the
sequence.

Governing prose owns each milestone's semantic contract and evidence obligations; the exact formalization is
developed directly in that milestone's canonical implementation, never as a separate formal surface that must
converge first. A milestone may begin only when every milestone it depends on is accepted, and a falsified
lower layer triggers the targeted causal dependency retreat in `ARCHITECTURE.md` §1 — repair the affected
accepted contract, reopen only its real causal dependents, negative closure for the rest.

**A milestone closes when its contract, its required evidence, a whole-system review, and Rob's acceptance
all pass.** That rule is the same for every row below and is not repeated in them.

## Frontier

`C5` is historically accepted: `Machine.T`, the one labelled-transition base every later runtime milestone
shares — opaque `State`/`Start`/`Label`/`Result`, `initial`, a relational `step`, `final`, and the runs,
reachability and absorbing-final results derived from it. It fixes no Go feature, no module imports it, and
this repository defines no concrete `Machine.T` value (`ARCHITECTURE.md` §3).

The `C4` static-authority cutover is **`IMPLEMENTED_NOT_ACCEPTED`** — one atomic replacement of the whole C4
topology: the direct shallow `Index` (finite file→position→cell maps) and its position selectors, exact
package/binding/scope identity with the fixed-spelling `func main()` carried as `Compilable.Bindings.MainDeclRef
s pr` — a real package function establishment with `MainOne`/`MainMultiple` multiplicity — one
`Compilable.Analysis` fact and issue authority (`Facts` and `Packages` deleted) with the canonical issue table,
the applicability + complete 5-way disposition algebra, and the selected-package preflight, projection-only
`Report`, the sealed `C4_PUBLIC` surface (`compile`/`inspect`/`compiled_prog`, opaque `Prog`, no public
elaborator), and the exact theorems and evidence. `.review/NEXT.md` owns the candidate. C4 stays
implemented-not-accepted until Rob separately accepts it; the C6 roots that depend on it stay frozen and resume
only after acceptance.

## Ahead

`scope` is the exact row set a milestone must discharge: every row of `.review/closure.csv` and
`.review/latitude.tsv` whose `milestone` column holds that milestone's id. **The ledger rows own the
assignment**; the counts in parentheses are diagnostic, and no row list is restated here. Rows carrying
`milestone=OUT` are priced exclusions belonging to no milestone. `evidence` names what must exist beyond the
common exit rule; an acceptance gate is a `.review/acceptance.tsv` row and may fire before the milestone that
owns the latitude row it gates.

**The SC contracts are cumulative.** When one ID appears against several milestones, each proves only the
slice frozen in its own active contract, and the last milestone listed against it closes the full obligation.
An earlier milestone may not claim cases assigned to a later one.

Milestones are ordered by **semantic dependency**, not by Go feature name. A feature family whose members
have different prerequisites is split across the milestones that can actually carry them, and the row that
names the family closes when its last member lands.

| id | depends_on | goal | public_result | scope | evidence |
|---|---|---|---|---|---|
| C6 | C5 | **Static semantic foundation.** Ordinary names and shadowing, scopes, semantic objects, the complete predeclared identity catalog, binding, one type algebra and environment, exact constants, expression/use/application facts, result-consumption plans, compiler-owned static variable identity, the type and package dependency objects, diagnostics and exact scope boundaries. **No runtime module, no value, no place, no store, no environment, no machine.** C6 also decomposes the current `Compilable.v` monolith into qualified `Compilable.*` modules owning its permanent static-semantic roots, while retaining one `Compilable` semantic authority. | One retained static authority every runtime milestone consumes, and a three-way decision that never calls unmodelled Go a rejection. | `milestone=C6` (70 + 9) | SC-01 literal magnitude and the unary-minus source and rendering slice; SC-02 predeclared constants, constant declarations, `iota` and C6 initializers; SC-03 scopes, declarations, binding facts, static variable identity, blank and uniqueness; SC-04 one type algebra over basic, alias and defined types; SC-05 context-free facts, C6 use edges and the one application root; SC-14 the retained package dependency object only; SC-16 the three-way decision; SC-19; SC-21; SC-22 exact acceptance over the no-boundary domain. Gate LAT-077 |
| C7 | C6 | **Scalar runtime foundation and execution.** Introduce `Runtime` — values, the permanent object store, dynamic places, dynamic environments and zero values — and the **first concrete `Machine.T`**. Execute C6's scalar expressions and declarations, conversions, `complex`, `println`, scalar operators, and closed no-import package initialization over C6's exact runtime projection, which materializes package **variables** in the store; constants stay compile-time facts and never enter it. Output and scalar runtime faults land here too. | One machine and one runtime root, both of which every later milestone extends rather than replaces. | `milestone=C7` (66 + 43) | SC-01…SC-03, SC-05, SC-08, SC-13, SC-14 closed no-import initialization and the first machine start, SC-15, SC-17, SC-20, SC-21, SC-22; gates LAT-019, LAT-177 |
| C8 | C7 | **Control and continuations.** Assignment, `if`, switches, loops, labels, `break`/`continue`/`goto`, nested blocks, the permanent focus and continuation root; the range control root with its integer and string domains. | One source-zipper control authority with no CFG lowering. | `milestone=C8` (45 + 17) | SC-03, SC-05, SC-06, SC-18, SC-21, SC-22; gate LAT-148 |
| C9 | C8 | **Functions and activations.** Function types, declarations and literals, callable expression heads, parameters and results, multi-results, calls and returns, closures, activation environments, `defer`/`panic`/`recover`; the iterator-function range domain. | One activation and call authority extending the same application and control roots. | `milestone=C9` (24 + 16) | SC-03…SC-07, SC-09, SC-15…SC-17, SC-20…SC-22; gate LAT-171 |
| C10 | C9 | **Aggregate and addressable data.** Arrays, structs, pointers, slices, maps, composite literals, indexing and slicing, addressability, aliasing, `append`/`copy`/`clear` and map operations; the array, slice and map range domains. | Aggregate objects extend the C7 store rather than replacing it. | `milestone=C10` (49 + 29) | SC-03…SC-05, SC-08, SC-10, SC-11, SC-15, SC-20, SC-21 |
| C11 | C10 | **Package orchestration.** Imports, qualified identifiers, the package graph, `init`, generalized package initialization order, command starts and module execution. | C6's dependency object and C7's initialization path generalize to closed multi-package programs, with no peer graph. | `milestone=C11` (19 + 14) | SC-02, SC-05…SC-07, SC-10, SC-14, SC-16, SC-17, SC-20, SC-21 |
| C12 | C11 | **Methods and interfaces.** Methods, selectors, method values and expressions, interface types and values, conformance, assertions, type switches and dynamic dispatch through the same application path. | One method and interface closure with no runtime type registry. | `milestone=C12` (28 + 23) | SC-03…SC-07, SC-13, SC-21, SC-22 |
| C13 | C12 | **Generics.** Type parameters, constraints, inference, unification, core types, instantiation and closing substitution. | Parametric typing extends the same type and interface roots. | `milestone=C13` (24 + 23) | SC-03…SC-05, SC-13, SC-21, SC-22; gates LAT-049, LAT-085 |
| C14 | C13 | **Concurrency, and family closure.** Goroutines, channel types and objects, send, receive, close, `select`, the channel range domain, and enabledness for concurrency. Channels are the last type form and the last builtin argument kind, so C14 also **closes** the umbrella rows whose families end there — expressions, operands, operators and precedence, built-in functions, length and capacity, making slices/maps/channels, type identity and assignability, zero values, and program execution including the no-post-main-ghost-step property. Its row count is large for that reason, not because concurrency grew. | The same machine and store gain concurrent behaviour, and every family whose last member is a channel closes here. | `milestone=C14` (45 + 11) | SC-03…SC-06, SC-08, SC-10, SC-15, SC-18, SC-20, SC-21 |
| C15 | C14 | **Memory model and whole-runtime safety.** Actions, happens-before, races, deadlock, complete enabledness agreement, finite bad-prefix safety. | Global safety theorems over the C14 machine. | `milestone=C15` (12 + 11) | SC-12, SC-16, SC-18, SC-20, SC-21 |
| C16 | C15 | **External adequacy, platform closure and final confirmation.** The target-matrix decision, pinned-Go correspondence, the terminal observation, and every remaining external boundary — plus final **confirmation** that the continuously enforced one-authority and deletion law still holds. Cleanup is never postponed to here; every earlier milestone already discharges it. | A closed external claim, and one authority per fact confirmed rather than belatedly imposed. | `milestone=C16` (1 + 0) | SC-00, SC-17, SC-19, SC-21 |

## How the language grows

A constructor lands with every source, acceptance, fact, rendering, fixture and proof obligation assigned to
**its** milestone: exact whole-program `Admissible` rules matching `go build ./...`, renderer support with
its value and syntax proofs, and — where observable — a differential fixture and an e2e witness. Runtime
stepping lands at the first mandatory runtime milestone the roadmap names for it. No earlier milestone may
claim a run theorem for a constructor, and no alternate evaluator may be added meanwhile. **Shrink the
representable language before weakening `Admissible`** — and where a construct is representable but its
meaning is not yet modelled, report the exact scope boundary rather than a rejection.

The type universe grows in one reviewed order, each root landing complete before the next begins. Integers,
floats, complex, and the predeclared source aliases are **done**. C6 adds named types over exactly those
roots: an **alias creates no new type identity**, and a **defined type's identity is its exact source
declaration reference** — never a string, a numeric `TypeId`, a registry entry or a tag. C6 resolves aliases
and definitions through predeclared types and other C6 named types, and rejects **every** type-declaration
cycle. Unnamed structural types are not a prerequisite for either.

Each type form lands with the semantics that give it meaning, and there is no general "all structural types"
event: function types at C9, array, struct, pointer, slice and map types at C10, interfaces at C12, generic
forms at C13, channels at C14. Valid recursive named types arrive with the first type-literal form that makes
recursion legal. `uintptr` and exact rune constants remain separately priced scope changes, and neither
blocks C6. Each root adds STATIC facts only and never resurrects a fake operational value to assert a static
type exists.

Imports stay unrepresentable until the closed-world resolver lands with its proof. See `.review/scope.tsv`.
