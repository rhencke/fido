# C5 — Machine base

Baseline: 187af467f0de356b3fee9b58c7f3bd819702b0d2
Review: implementation

Goal:
Add the smallest public labelled-transition base that all later runtime milestones share. C5 defines no Go
feature semantics and no concrete Go machine.

Scope — C5 may:
- add `Machine.v`;
- place `Machine` after `Compilable` and before `Safe` in `dune`;
- audit the exact closure and latitude rows whose `milestone` is `C5`;
- update `ARCHITECTURE.md`, `ROADMAP.md` and this file to state the current accepted result.

Scope — C5 may not add:
- a parser, token layer, second source form, typed AST, target IR, or command language;
- a concrete Go state, start, label, result, evaluator, scheduler, store, runtime value, panic state, or
  goroutine state;
- a second step relation or an `EnabledDecision` inhabitant;
- deadlock, fairness, safety, liveness, output, panic, function, object-store, channel, or scheduler
  semantics;
- a compatibility layer, placeholder, trusted shortcut, fuel, bound, or premature future state;
- any change to `Safe.Property`, generated output, or runtime behavior.

Exact public API — `Machine.v` adds these declarations and no others:

```coq
Record T : Type := Make {
  State  : Type;  Start  : Type;  Label  : Type;  Result : Type;
  initial : Start -> State;
  step    : State -> Label -> State -> Prop;
  final   : State -> Result -> Prop
}.

Trace, FiniteRun (FiniteRefl, FiniteStep), InfiniteRun (InfiniteStep), Reachable,
Enabled, Disabled, EnabledDecision, FinalAbsorbing, Stuck

finite_run_app, initial_reachable, reachable_step,
final_absorbing_no_step, finite_run_from_absorbing_final, infinite_run_from_absorbing_final
```

Every proof helper is `Local`. No alias, notation, alternate constructor, convenience lemma, decidable
equality, classical principle, instance, or second run representation. Direct structural induction and
coinductive inversion only — no axiom, parameter, admitted fact, fuel, arbitrary bound, or classical
shortcut.

Contract slices — C5 consumes only these slices of the cumulative SC contracts:
- SC-00 audit the C5 ledger and pinned-vocabulary foundation; add no manifest machinery;
- SC-01 preserve and audit only the source, identifier and rendering forms currently admitted;
- SC-16 preserve the current accepted/rejected static capability and constructor-level unrepresentability;
- SC-18 freeze only `EnabledDecision`, `FinalAbsorbing` and `Stuck` over abstract `Machine.T`; provide no
  inhabitant;
- SC-21 keep the public base exact and minimal; every proof helper remains local.

`Machine` is deliberately imported by nothing. C5's product is the public base itself; the first complete
runtime vertical feature consumes it.

Preserve:
- `Syntax.Program` as the sole source authority;
- the exact retained `Compilable.Program`, `Failure` and whole-elaboration cores;
- the existing `Safe.Property` and `Safe.Program`;
- direct rendering and the one `Emit.Mint.issue` authority;
- certified-module coverage, the whole-theory audit, and controls A-E;
- emit-time assumption-closure provenance rejection;
- every sealed-capability, mint, transport and positive client control;
- working-tree and staged-index separation, and no-host-Python;
- generated `go.mod` and `.go` bytes, and runtime stdout, stderr and exit status;
- `life.md`.

Done:
- the public base and theorem surface exist exactly, with no additional public declaration;
- no second run relation, concrete machine, or feature-specific state exists;
- all C5 ledger rows name an owner that actually exists;
- `make prove`, `make check`, `make audit-fresh`, `make regenerate`, `make regen-guard` pass;
- generated Go and runtime goldens are unchanged;
- one whole-system implementation review passes, then Rob accepts C5.

Stop:
- the exact public API needs another field, constructor, definition, or theorem;
- one of the theorem statements is false or needs a concrete Go feature;
- a C5 ledger row needs the accepted source/static/render foundation changed;
- implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound, or premature future
  state;
- any existing public theorem statement or generated/runtime artifact would change.
