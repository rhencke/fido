# Roadmap

What is left to build, in dependency order. `.review/NEXT.md` owns the active task; this file owns the
sequence.

**A milestone closes when its contract, its required evidence, a whole-system review, and Rob's acceptance
all pass.** That rule is the same for every row below and is not repeated in them.

A milestone may begin only when every milestone it depends on is accepted.

## Done

`C4` (opaque static capability retaining the exact elaboration object) is accepted, and with it the current
fragment: `println` of primitive literals plus one source-shaped explicit conversion. The mechanical M-series
that followed it — source diet, performance snapshot, tool and build audit — is closed.

`DOC-RESET` is accepted. The documentation and review-process subsystem is now the minimal corpus, and it
superseded what remained of the M-series. Git history owns every one of those contracts and its evidence.

`ASSUM-GATE` is accepted. The hand-maintained assumption-surface list is deleted, and the build-time
zero-project-axiom claim is owned by one chain — certified-module coverage, then the whole-theory
`Fido Audit Assumptions`, then adversarial controls A-E — of which no part is sufficient alone.
`DECISIONS.md` owns the decision; Git owns the accepted implementation.

`C5` is accepted. `Machine.T` is the one labelled-transition base every later runtime milestone shares —
opaque `State`, `Start`, `Label` and `Result`, plus `initial`, a relational `step`, and `final` — with finite
and infinite runs, reachability, enabledness and absorbing-final results derived from it. It fixes no Go
feature, no module imports it, and this repository defines no concrete `Machine.T` value; the first complete
runtime vertical feature is what consumes it. `ARCHITECTURE.md` §3 describes it.

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

| id | depends_on | goal | public_result | scope | evidence |
|---|---|---|---|---|---|
| C6 | C5 | Exact binding and use roles, the one type algebra, the predeclared universe, static slots, dynamic places, typed closed runtime values, the first scalar-cell store slice, and the expression-fact/use boundary that declarations and variables need. C6 **instantiates no machine**: it builds the facts and store roots a runtime consumes. | Package and local declarations with exact roles; named types whose identity is their declaration; variables with slots, typed places and zero values. | `milestone=C6` (66 + 22) | **slices only**: SC-02 predeclared constants, constant declarations, `iota` and C6 initializers; SC-03 package and local scope, declarations, binding facts, slots, blank uses, uniqueness, package-only export and predeclared shadowing; SC-04 one type algebra over basic, alias and defined types, no structural or generic case; SC-05 context-free facts and C6 use edges including ordinary name expressions; SC-08 typed scalar cells, typed places, allocation identity and typed lookup only; SC-14 C6 zero values and closed-command start **facts** only; SC-21; SC-22 via `LAT-077`. Gate LAT-077 |
| C7 | C6 | Runtime expressions, evaluation order, output, and fatal panic. C7 builds the **first concrete `Machine.T`** for a `Safe.Program`, consuming C6's retained facts and store roots and giving the existing expression and `println` fragment one run relation. | Observable output and exit status under the pinned target, on the one machine every later milestone extends. | `milestone=C7` (72 + 43) | SC-01…SC-03, SC-05, SC-08, SC-13, SC-14 the first concrete machine start, SC-15, SC-17, SC-20, SC-21, SC-22; gate LAT-177 |
| C8 | C7 | Control flow with retained jump continuations. | Structured control with no CFG lowering. | `milestone=C8` (42 + 16) | SC-03, SC-06, SC-18, SC-21, SC-22; gate LAT-148 |
| C9 | C8 | Functions, closures, multi-results, defer, panic, recover. | Stack-only panic/defer/recover. | `milestone=C9` (24 + 15) | SC-03…SC-07, SC-09, SC-15…SC-17, SC-20…SC-22; gate LAT-171 |
| C10 | C9 | Composite data and typed mutable objects. | One runtime object store. | `milestone=C10` (49 + 28) | SC-03…SC-05, SC-08, SC-10, SC-11, SC-15, SC-20, SC-21 |
| C11 | C10 | Packages, initialization, starts, and range. | Package init order and program starts. | `milestone=C11` (26 + 13) | SC-02, SC-05…SC-07, SC-10, SC-11, SC-14, SC-16, SC-17, SC-20, SC-21 |
| C12 | C11 | Methods and interfaces. | Method sets and non-generic value interfaces. | `milestone=C12` (28 + 20) | SC-03…SC-07, SC-13, SC-21, SC-22 |
| C13 | C12 | Generics and closing substitution. | Type parameters with closed instantiation. | `milestone=C13` (17 + 20) | SC-03…SC-05, SC-13, SC-21, SC-22; gates LAT-049, LAT-085 |
| C14 | C13 | Goroutines, channels, select, and enabledness. | Concurrency with a decidable enabledness relation. | `milestone=C14` (16 + 8) | SC-03…SC-06, SC-08, SC-10, SC-15, SC-18, SC-20, SC-21 |
| C15 | C14 | Happens-before, races, and deadlock. | A race and deadlock account tied to the memory model. | `milestone=C15` (12 + 11) | SC-12, SC-16, SC-18, SC-20, SC-21 |
| C16 | C15 | Platform matrix and target model. | More than one validated target; ADR-0004 decided. | `milestone=C16` (1 + 0) | SC-00, SC-17, SC-19, SC-21 |
| C17 | C16 | Ruthless trim and final authority audit. | One authority per fact across the whole system. | none — C17 discharges no ledger row | SC-19, SC-21 |

## How the language grows

A constructor lands with every source, acceptance, fact, rendering, fixture and proof obligation assigned to
**its** milestone: exact whole-program `Admissible` rules matching `go build ./...`, renderer support with
its value and syntax proofs, and — where observable — a differential fixture and an e2e witness. Runtime
stepping lands at the first mandatory runtime milestone the roadmap names for it. No earlier milestone may
claim a run theorem for a constructor, and no alternate evaluator may be added meanwhile. **Shrink the
representable language before weakening `Admissible`.**

The type universe grows in one reviewed order, each root landing complete before the next begins. Integers,
floats, complex, and the predeclared source aliases are **done**. C6 adds named types over exactly those
roots: an **alias creates no new type identity**, and a **defined type's identity is its exact source
declaration reference** — never a string, a numeric `TypeId`, a registry entry or a tag. C6 resolves aliases
and definitions through predeclared types and other C6 named types, and rejects **every** type-declaration
cycle. Unnamed structural types are not a prerequisite for either.

After C6: valid recursive named types arrive with the later type-literal forms that make recursion legal;
composite structural types with the composite-data milestone; function types with functions; interfaces with
interfaces; generics with generics. `uintptr` and exact rune constants remain separately priced scope
changes, and neither blocks C6. Each root adds STATIC facts only and never resurrects a fake operational
value to assert a static type exists.

Imports stay unrepresentable until the closed-world resolver lands with its proof. See `.review/scope.tsv`.
