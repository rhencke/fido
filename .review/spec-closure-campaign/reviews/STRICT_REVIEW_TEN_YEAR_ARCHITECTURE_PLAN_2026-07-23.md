# STRICT REVIEW — Fido Ten-Year Architecture Plan

**Reviewed document:** `FIDO_TEN_YEAR_ARCHITECTURE_PLAN_2026-07-23.md`
**Reviewed-document SHA-256:** `f373b9c3ef376366f9519b79b118c114167299389ff79dfec7a6f96d27a9b752`
**Review date:** 2026-07-23
**Reviewer:** Claude (external, advisory)
**Authority:** ADVISORY ONLY. This review does not accept the plan, does not accept C4, does not authorize C5, and does not modify any active repair directive. Every disposition below is Rob's to make. Per project governance, a model must not certify its own trade-offs; the same rule binds this review — it identifies conditions, it does not award scores.

---

## 0. The 10/10 Rule

The plan currently self-assigns 9.5/10. That number is void (see F-8). The path to 10/10 is defined here as a closed checklist, not a judgment call:

> The plan is **eligible** for 10/10 when every BLOCKING and REQUIRED finding below has a recorded human disposition (FIXED, or REJECTED with rationale in an ADR), and the plan text has been re-frozen with a new SHA. The score itself is then **assigned by Rob or by the §26 acceptance rule — never by the document, and never by a model.**

RECOMMENDED and EDITORIAL findings do not block eligibility but must receive dispositions before the plan is cited as authority by any checkpoint contract.

---

## 1. Verdict Summary

The plan is architecturally sound as a candidate. Its public base (one source, one retained compiler result, one machine, one step relation, one bad-prefix safety rule, one renderer) is the correct minimal surface, and its §1 deletion standard, §17 safety formulation, §15 provenance design, and §24 do-not-do-early list are direct, correct generalizations of the repository's paid-for lessons. Nothing in the findings below requires a new public authority. Every finding is either an unstated load-bearing lemma, an unassigned meaning, an under-specified contract, or a governance defect.

| ID | Severity | Section(s) | One-line defect |
|----|----------|-----------|-----------------|
| F-1 | BLOCKING | §13, §25.5 | Recover's no-token claim rests on an unstated machine invariant |
| F-2 | BLOCKING | §12, §25.2 | Jump-target continuations risk reintroducing canonical recomputation |
| F-3 | BLOCKING | §14, §15 | Map iteration order is a meaning with no owner |
| F-4 | BLOCKING | §2, §16, §17 | Main-return does not disable `step`; safety quantifies over ghost steps |
| F-5 | REQUIRED | §25.6 | Channel happens-before edge set is again a partial list |
| F-6 | REQUIRED | §22, §26.8 | Claim (B) has no stated method once runs are nondeterministic |
| F-7 | REQUIRED | §16, §18 | Progress trichotomy hides an enabledness-decidability obligation |
| F-8 | REQUIRED | §27 | Self-assigned score violates the self-certification prohibition |
| F-9 | REQUIRED | §25.4, §25.7 | Generic/interface closing-substitution lemma untested by either test alone |
| F-10 | REQUIRED | §9 | Opaque `Config` names no exported theorem surface |
| F-11 | REQUIRED | §4 | Blank identifier breaks totality of `binding_fact` as written |
| F-12 | REQUIRED | §26 | Acceptance rule names no disposition owner |
| F-13 | REQUIRED | §17 | "Represented external-boundary failure" is not an exact case |
| F-14 | REQUIRED | §5 | The use-fact list has no closure rule |
| F-15 | REQUIRED | §20 | Initialization-cycle rejection is not required to be unrepresentable |
| F-16 | RECOMMENDED | §10, §25.3 | String↔slice conversion allocation needs a named fixture |
| F-17 | RECOMMENDED | §23 | Deletions should be individually gated commits |
| F-18 | RECOMMENDED | §25 | Each mandatory proof test should be a frozen contract with a SHA |
| F-19 | EDITORIAL | §6 | Cross-reference ADR-0001 where the pinned target is invoked |

---

## 2. Findings

### F-1 — BLOCKING — The recover mechanism's load-bearing lemma is unstated (§13, §25.5)

**Defect.** §13 claims recover needs "no recover token, permission flag, invocation-kind field, caller ID, or global panic context" because structural position suffices: the current running activation is directly above a finishing activation. That claim is true **only** because of an invariant the plan never states: *an activation in `Finishing` pushes only deferred-call activations; ordinary calls are pushed only by `Running` activations.* "Directly above Finishing" implies "defer-invoked" solely via this invariant. If any future rule ever permits a Finishing activation to push anything else — a runtime-panic report formatter, a package-finalization edge, anything — recover becomes silently wrong and **no gate fails**, because the invariant that broke was never written down.

**Required change.**
1. State the invariant in §13 by name, e.g. `finishing_pushes_only_deferred_activations`, as a machine invariant of `GoMachine`.
2. State the derived lemma by name, e.g. `above_finishing_iff_deferred_call`, and identify it as the sole justification for the absence of provenance fields.
3. Add both to §25.5 as gated proof obligations with a negative fixture: a hypothetical non-defer push from Finishing must be unrepresentable (constructor absence), not merely unused.

**Verification.** `make prove` includes both named theorems; §25.5 fixture demonstrates a helper called *by* a deferred function (Running→Running push) cannot recover, while the deferred function itself (Finishing→Running push) can.

---

### F-2 — BLOCKING — Goto must consume retained continuations, not recompute them (§12, §25.2)

**Defect.** §12 says resolved `break`, `continue`, and `goto` "select their retained exact target." Selecting the target is the easy half. Constructing the **continuation at that target** is the hard half, and the plan is silent on who owns it. If the machine's jump rule computes the target continuation by a canonical function over source position, the architecture reintroduces — inside the runtime — the exact canonical-recomputation root that C4 repairs 6 and 7 just eliminated from the static side (`prog_forest` re-evaluated by every consumer, proofs discarded and re-derived).

**Why it is cheap to do right.** The Go specification forbids jumping into a block and over variable declarations into their scope. Consequently the continuation skeleton at every label is a pure function of source structure: no value context crosses a jump, and expression progress is always discarded (goto is a statement). The skeleton can therefore be computed **once, at elaboration**, and retained as a `ControlFact`.

**Required change.**
1. Amend §12: jump-target continuations are retained compiler facts; the machine's jump rule *consumes* the retained continuation and never constructs one.
2. Amend §25.2 to require it, and to forbid any production function of shape `continuation_at : source position → Continuation`.
3. Add the interaction fixture with §11: a **backward goto over a `:=` inside a loop body**. The jump must allocate a fresh place for the re-executed declaration while a closure captured before the jump observably retains the old cell. This is the fixture that catches slot-place reuse.

**Verification.** §25.2 fixtures pass; grep-level gate (in the style of the existing `as_expr` prohibition) confirms no production continuation constructor takes a raw source position.

---

### F-3 — BLOCKING — Map iteration order is a meaning without an owner (§14, §15)

**Defect.** Range-over-map is nondeterministic by the Go specification. The plan assigns this meaning to nobody: §14's "the global relation chooses any enabled transition" governs *which goroutine* steps, not *which permutation* a single range-over-map step observes; §15's action list has no case for it. §3 forbids exactly this: a meaning with no owner.

**Required change.** Decide and record (an ADR is appropriate):
1. Iteration order is **step nondeterminism**: the range construct's step relation admits any permutation of the map's current keys, and
2. The **chosen permutation (or the chosen next key) is recorded in the Label's action**, so that (a) happens-before and race analysis see the reads in their true order, and (b) claim-(B) membership checking (F-6) can match a concrete Go run's observed order to a model run.
3. State explicitly that programs with concurrent map access races require no modeled fatal-throw behavior, because every such program is already excluded by `GoSafe` (data race is a BadPrefix); the Go runtime's "concurrent map writes" throw therefore stays outside the model with a one-sentence justification, not by silence.

**Verification.** §25.6 (or a new §25 test) includes a two-key map range fixture with both orders demonstrated as valid runs and reflected in labels.

---

### F-4 — BLOCKING — Main-return must disable `step`, or safety quantifies over ghost executions (§2, §16, §17)

**Defect.** §16 says "main return ends the process even when other goroutines remain." The Machine has no rule enforcing this: as written, nothing prevents `step` from continuing to fire on remaining goroutines after the main goroutine has returned. `GoSafe` quantifies over **all** finite runs; if post-main ghost steps exist, then (a) a BadPrefix occurring only in ghost steps wrongly condemns a program whose real process already exited, and (b) the Deadlocked category can misfire on a goroutine blocked forever after main returned — which in real Go is a normal exit, not a deadlock. This is a soundness defect in the safety definition itself, in whichever direction it resolves by accident.

**Required change.**
1. Make main-returned states **absorbing**: a global side condition on `step` (no transition applies when the main goroutine has returned), or equivalently fold main-return into `final` with a proved theorem `final_states_have_no_steps`.
2. Redefine Deadlocked (§16) to require **main not returned**: nonterminal unfinished work exists, main has not returned, and no step applies.
3. Add the fixture: main returns while another goroutine is blocked mid-send; the run is NormalExit, not Deadlocked, and no post-return step exists.

**Verification.** `final_states_have_no_steps` is a gated theorem; the fixture above is in the §25 suite.

---

### F-5 — REQUIRED — Enumerate the full channel happens-before edge set by name (§25.6)

**Defect.** Dig 05's central failure was an incomplete event vocabulary: the capacity rule and the receive-side rendezvous edge were silently dropped between the abstract theory and the final trace model, and nothing failed. §25.6 currently lists "write-before-send and read-after-receive" — again a partial list, again inviting the same silent omission.

**Required change.** §25.6 must enumerate the Go memory model's channel edges exhaustively and by name, as contract items whose absence is a contract violation:
1. The *k*-th send on a channel happens before the *k*-th receive from that channel completes.
2. For a channel with capacity *C*, the *k*-th receive happens before the (*k*+*C*)-th send completes (this is the capacity rule Dig 05 lost).
3. The close of a channel happens before a receive that returns the zero value because the channel is closed.
4. For an unbuffered channel, the receive happens before the send completes (the receive-side edge Dig 05 lost).

Each edge gets a positive fixture (edge derivable from labels) and a negative fixture (a race detectable only if that edge is present is in fact detected).

**Verification.** Four named edges, eight fixtures, all gated.

---

### F-6 — REQUIRED — Claim (B) needs a stated method for nondeterministic programs (§22, §26.8)

**Defect.** Today claim (B) is byte-differential: generated output equals pinned-toolchain behavior. Once the machine is nondeterministic (scheduling, select, map order), a single concrete Go execution is one resolution of the model's nondeterminism, and "outputs match" is no longer a well-posed check. §26.8 ("actual generated Go compiles and matches the formal observations") is silent on what *matches* means under nondeterminism.

**Required change.** State the method: differential testing becomes **membership** — the concrete run's observable sequence must be certified as a run of `GoMachine cp`. This requires an executable step-checker (an evidence tool, not a semantic authority — it decides `step` instances, it does not define them) whose verdicts are themselves gated against the relational `step`. Note explicitly that select-with-default and other negative-premise rules make this checker's correctness depend on F-7's decidability results. Amend §26.8 to define "matches" as membership plus, where the observation is deterministic (single-goroutine, no map iteration), byte equality as today.

**Verification.** The checker exists as a proved-decidable evaluator for `step` on well-formed states; a concurrent fixture's real `cmd/go` run is machine-checked as a model run.

---

### F-7 — REQUIRED — Name the enabledness-decidability obligation (§16, §18, §27)

**Defect.** Deadlock is a negative property ("no step applies"), and §18's `well_formed_progress_or_final_or_deadlock` is a trichotomy whose constructive proof requires **deciding enabledness** per reachable state. This is true but nontrivial for select over nil channels, rendezvous readiness, and select-with-default (whose enabledness is itself a negative premise). The plan's §27 reserve list omits it.

**Required change.** Add to §27's reserves: `enabled_dec : forall config, {l & {config' & step config l config'}} + (forall l config', ~ step config l config')` on well-formed states, with select/default and nil-channel operations named as the hard cases. Note that F-6's checker consumes this same decision procedure — one authority, two consumers.

**Verification.** `enabled_dec` is a gated theorem before any §25.6 fixture is accepted.

---

### F-8 — REQUIRED — Strike the self-assigned score (§27)

**Defect.** "Architecture satisfaction: 9.5/10" is a model certifying its own trade-offs. The repository's governance forbids this in exactly these words, and the plan itself is otherwise scrupulous about authority (§26 correctly makes acceptance conditional and lists conditions). A number the author assigns to the author's own architecture has no standing and, worse, anchors future readers.

**Required change.** Delete the score. Retitle §27 "Open Proof-Cost Reserves" and keep only the (genuinely valuable) list of the five areas where real Rocq cost could force internal redesign. If a confidence statement is wanted, it must be labeled as author's confidence, carry no number, and be excluded from any acceptance reasoning. The only score-bearing instrument is §26, and its verdicts belong to Rob (see F-12).

**Verification.** Textual; re-freeze with new SHA.

---

### F-9 — REQUIRED — Test the generic/interface closing-substitution lemma jointly (§25.4, §25.7)

**Defect.** §25.4 proves the one type algebra serves open static facts and closed runtime values. §25.7 proves conformance, packing, dispatch, assertion, and equality use the same facts. Neither test, alone, exercises the known crux of Go generics formalization: **interface implementation proved with open type variables must be preserved under closing substitution**, so that a runtime interface value holding an instantiated generic type carries an implementation proof derived from the open fact plus the activation's closed substitution — not re-derived, not tag-mediated.

**Required change.** Add a joint mandatory fixture spanning both tests: a generic named type with a method set, instantiated at a closed type, packed into an interface value, dispatched through it, and asserted out of it — with the gated lemma `implements_closed_substitution` named in the contract, and with dispatch proved to consume the substituted retained fact.

**Verification.** The named lemma and fixture are gated; no auxiliary runtime registry appears in the diff.

---

### F-10 — REQUIRED — Name the exported theorem surface of the opaque `Config` (§9)

**Defect.** §9 makes `Config cp` abstract and proves well-formedness internally. Clients — the safety layer, the HB derivation, the §25 fixtures, the F-6 checker — need *some* facts about reachable states (well-formedness, typed-lookup totality on reachable states, identity freshness). If the exported surface is unnamed, clients will either be unable to proceed or will pressure the abstraction open.

**Required change.** §9 must list the exported theorem surface by name, minimally: `reachable_well_formed`, `reachable_lookup_total`, `identity_fresh_monotone`, plus whatever §25.3 requires ("total typed lookup on reachable states" is already promised there — connect the promise to the export list). The rule: the abstraction boundary is defined by its exports, and the exports are part of the permanent public base, so they belong in the plan.

**Verification.** Textual now; each export becomes a gated theorem at its checkpoint.

---

### F-11 — REQUIRED — The blank identifier breaks `binding_fact` totality as written (§4)

**Defect.** §4 promises `binding_fact : forall cp (r : IdentifierUseRef cp), BindingFact cp r` with no `option`. The blank identifier `_` is an identifier use with **no binding** (it denotes nothing, is not declared, and each use is distinct). As written, either the query is partial (forbidden) or `BindingFact` must lie.

**Required change.** Choose and record one of the two honest designs: (a) `IdentifierUseRef` excludes blanks **by construction** — a blank use is a different reference kind, unrepresentable as an `IdentifierUseRef`, with its own exact facts where the spec gives it semantics (assignment discard, receiver, parameter); or (b) `BindingFact` gains an exact `Blank` case whose downstream consumers are total. Option (a) is more in the spirit of §1. Either way, add the fixture: `_ = f()` evaluates `f` exactly once and binds nothing.

**Verification.** The chosen design is in the plan text; the fixture is in §25.1's suite.

---

### F-12 — REQUIRED — The acceptance rule needs a disposition owner (§26)

**Defect.** §26 lists eight conditions but never says who judges them. Under this project's governance the answer is singular and load-bearing: Rob. Without the sentence, a future reader (human or model) can read §26 as self-executing — precisely the failure mode the `.review` ledger exists to prevent.

**Required change.** Append to §26: "Each condition's satisfaction is a human review act by Rob, recorded in `.review`. No model may declare any condition met. Conditions 1–8 are evaluated only against frozen commits with green `make prove`, `make e2e`, `make check`, and `make regenerate`."

**Verification.** Textual; consistent with `NEXT_STEPS.md` authority language.

---

### F-13 — REQUIRED — "Represented external-boundary failure" must become exact cases (§17)

**Defect.** Every other live BadPrefix case is exact (unrecovered fatal panic, global deadlock, data race). "Represented external-boundary failure" is a category, not a constructor, and categories in safety definitions rot into judgment calls.

**Required change.** Replace with the rule rather than the placeholder: *BadPrefix admits only exact constructors; each new external boundary (output, OS interaction, future FFI) adds its failure cases by named constructor at the checkpoint that introduces the boundary, with a fixture per constructor.* If the current fragment has exactly one boundary (output), name its failure cases now or state that the set is presently empty.

**Verification.** Textual; enforced by the F-18 per-test contracts.

---

### F-14 — REQUIRED — Close the use-fact list (§5)

**Defect.** §5's `ExprUseFact` responsibilities list is flat and unmarked. It omits at least: range-clause key/element typing, composite-literal element and key matching, variadic `...` argument spreading, and untyped-nil contexts. An unmarked list will be read as exhaustive by one implementer and as exemplary by the next; both readings have already cost this project repairs.

**Required change.** Mark the list explicitly: it is **exemplary here and closed per checkpoint** — each checkpoint's frozen contract enumerates the exact use kinds it introduces, and a use kind absent from every accepted contract is unrepresentable (`ExprUseRef` has no constructor for it). Add the four omissions above to the plan's list now so the exemplar is not misleading.

**Verification.** Textual; the per-checkpoint closure is then enforced by F-18.

---

### F-15 — REQUIRED — Initialization cycles must be unrepresentable (§20)

**Defect.** §20 retains an initialization plan (dependency order, initializer references, init functions, main) as a compiler fact, but does not require that **initialization cycles are an elaboration failure**. Go rejects initialization cycles at compile time; a plan that could represent one would be a fact with no meaning — §1's own prohibition.

**Required change.** State it: the retained plan's dependency order is a proof-carrying topological order; a cyclic dependency is unrepresentable in `CompilableProgram` (elaboration rejects, with an exact diagnostic). Fixture: a two-variable initialization cycle is rejected; the acyclic variant initializes in dependency order, not source order, observed via output.

**Verification.** Both fixtures gated at the checkpoint that lands §20.

---

### F-16 — RECOMMENDED — String↔slice conversion allocation fixture (§10, §25.3)

`string([]byte)` and `[]byte(string)` allocate fresh backing; the results never alias the operand. This is a classic differential trap (mutation of the source slice after conversion must not be observable through the string, and vice versa). Add one named fixture to §25.3. Strings themselves are values, not objects — worth one sentence in §10 so nobody gives them cells.

### F-17 — RECOMMENDED — Gate each deletion in §23 individually

"Delete when complete replacements exist" should inherit the repository's existing discipline: each §23 deletion is its own commit, paired with the fixture flip that proves the replacement covers it, and where applicable a `Fail Definition` demonstrating the deleted form is now unrepresentable. A bulk deletion commit is how a compatibility path survives unnoticed.

### F-18 — RECOMMENDED — Freeze each §25 test as a contract with a SHA

The nine mandatory proof tests are where this plan's claims become falsifiable. Give each the C4 treatment: its own contract file, frozen with a SHA-256 **before** implementation begins, so §25.9's redesign trigger has teeth — a test that can be softened after contact with proof cost is not a test. The plan itself should be re-frozen (new SHA) after F-dispositions, and the new SHA recorded in `.review`.

### F-19 — EDITORIAL — Cross-reference ADR-0001 (§6)

Where §6 says "the current pinned target remains direct," cite ADR-0001 (PROPOSED) explicitly so the plan and the ledger cannot drift on what "pinned" means. Note ADR-0001's own disposition remains open and is not resolved by this plan.

---

## 3. What Must Not Change

A strict review owes the same exactness to strengths. The following are correct as written and should be treated as fixed points during F-disposition edits — a repair that weakens any of these is a regression, not a fix:

1. **§1's deletion and generalization standard** — the five retention tests and the prohibition list.
2. **§2's minimal Machine base** and the rule that no Go feature defines another run relation.
3. **§3's one-owner-per-meaning table.**
4. **§5's fact/use split** and "the use builder does not inspect the raw child again."
5. **§6's single type algebra** with `RuntimeType := SemanticType Empty_set`, alias non-identity, and declaration-reference recursion.
6. **§11's static-slot/dynamic-place distinction** — this is what makes F-2's goto fixture and closures correct for free.
7. **§13's stack-only panic/defer/recover** (pending F-1's lemma being named) and nested-panic replacement semantics.
8. **§15's resource-local origins with proof-connected provenance** — the closure, by construction, of Dig 05's forged-origin hole.
9. **§17's finite bad-prefix safety** with liveness held separate.
10. **§19's rejection of vacuous library safety** from an empty start set.
11. **§24's Do-Not-Do-Early list**, verbatim.
12. **§26's stance** that this is a candidate, not an assertion (pending F-12's ownership sentence).

---

## 4. Disposition Ledger (to be completed by Rob)

| ID | Disposition (FIXED / REJECTED+ADR) | Commit / ADR | Date |
|----|------------------------------------|--------------|------|
| F-1 | | | |
| F-2 | | | |
| F-3 | | | |
| F-4 | | | |
| F-5 | | | |
| F-6 | | | |
| F-7 | | | |
| F-8 | | | |
| F-9 | | | |
| F-10 | | | |
| F-11 | | | |
| F-12 | | | |
| F-13 | | | |
| F-14 | | | |
| F-15 | | | |
| F-16 | | | |
| F-17 | | | |
| F-18 | | | |
| F-19 | | | |

**Eligibility gate:** all BLOCKING and REQUIRED rows dispositioned → plan re-frozen with new SHA → 10/10 becomes assignable, by Rob, under §26. Not before, and not by anyone else.

---

*End of review. This document is advisory input to the human review and carries no acceptance authority of its own.*
