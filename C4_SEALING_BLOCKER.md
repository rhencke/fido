# C4 correction — sealing vs. reducible witnesses: a decision for the reviewer

**Status:** `BLOCKED_FOR_ROB` at dependency-order step 2 (public topology) of the C4 correction contract
(`ebf80c34-WORK_CONTRACT.md`). No canonical code was changed to reach this conclusion; five throwaway spikes were
built, observed, and deleted. The candidate content is exactly the entry state (commit
`1306aa190fc1a21fd8c1bc94dde56c10f8054409`, tree `b39729a19afb1ef429652c5ac4fcd53ae71e04ba`); the only commit on
the branch is this write-up.

This file exists only to hand the decision to the reviewer, and should be deleted once the approach is chosen.

---

## Bottom line

The contract requires **all** of the following, and in this Rocq toolchain they cannot hold together:

1. **Sound, type-level sealing** (§2, §10): `Decision`/`Compilation`/payloads abstract outside the owner;
   constructors absent from the client namespace; hostile controls fail when a client *names* a raw constructor
   or pattern-matches `Decision` directly; "impossible states … established by Rocq module/type topology"
   (§Required-validation-2, line 818).
2. **Reducible, Rocq-computed certified witnesses** (§Preservation, §12): `make emit`/`e2e` materialize the
   certified image to the preserved bytes/goldens, via `Fido Materialize` (which normalizes with
   `Reductionops.nf_all`).
3. **`inspect` as the sole payload route** (§2, §10, line 597): no `*_of_nilb`, no mint-from-report-equality, no
   second decision authority (e.g. a parallel boolean `check`).

These are mutually exclusive. The chain of forced implications:

- (2) requires `inspect (compile p)` to **reduce** in client code (to extract the payload the witness feeds to
  `Safe.certify`; the source bytes are then a primitive projection). Proven: under opaque ascription the match is
  stuck and materialization fails.
- reduction requires `Decision`/`compile`/`inspect` **transparent**.
- a **transparent** type is **forgeable**: a client can write out a canonical-looking value and close any
  equality guard with `eq_refl` (Coq *conversion* evaluates even an un-nameable `Local` composer). So a hostile
  client can fabricate a `Compilation` with empty reports, prove `Admissible`, apply `DCompiled`, and mint a
  `Prog`/`Image` — i.e. **sound sealing fails** under transparency.
- the only escape valves for (2) that would allow opacity — a reducible boolean `check` proved equivalent to
  `compile`, or minting the payload from `diagnostics = []` — are exactly what (3) forbids.

So: **sound seal ⇔ opacity ⇔ no client reduction ⇔ no computable witness**, and the sanctioned witness route is
mandatory. The requirement set has no implementation in this Rocq. The reviewer must relax one axis.

---

## Why materialization needs client-side reduction

The witness is `Emit.of_safe (Safe.certify demo_program (compile demo_program) c cp _)`, where `c`, `cp` come from
`match inspect (compile demo_program) with IsCompiled c cp => …`. `Safe` uses primitive projections, so
`Safe.source` reduces to the source **without** forcing the phases — but the enclosing `match` on
`inspect (compile demo_program)` must first reduce to `IsCompiled c cp`, or the whole term is stuck and
`Fido Materialize` (via `Reductionops.nf_all`, `plugin/materialize.mlg:213`, which does not unfold opaque
constants) cannot decode `(go.mod, entries)`. Proving *any* fact about a concrete program's compilation has the
same requirement. Hence `compile`/`inspect` must be transparent.

## Why a transparent surface cannot be soundly sealed

A transparent inductive/record's values are constructible by writing them out. An equality guard
(`DCompiled : forall c, c = elaborate p -> … -> Decision p` with `elaborate` a `Local Definition`) does **not**
help: the `Local` keyword hides the *name* but conversion still evaluates the *body*, so a client closes the guard
with `eq_refl` by supplying a value convertible to `elaborate p`. Spike E below demonstrates a client building the
"sealed" constructor directly. The same defeats a sealed-sigma field
(`Compilation p := { facts | facts = analysis p }`): supply the canonical `facts` value + `eq_refl`. For any one
concrete target program these canonical values are specific closed terms an adversary can, in principle, write —
so the seal is not proof-level. Only an **abstract** (opaque) type makes values un-constructible, and that removes
reduction.

## Mechanisms measured (five throwaway spikes, all deleted)

| # | Mechanism | Hides constructor (name + direct-match + apply)? | `inspect (compile p)` reduces in a client file? |
|---|---|---|---|
| A | `Local Module` / `Local Inductive` | — | **rejected**: "does not support this attribute: local" |
| B | `#[private(matching)] Inductive` | **no** (client names, matches, applies freely) | yes |
| C | `Module M : SIG := Impl` (opaque) | **yes** | **no** — `vm_compute (inspect (compile 0))` stuck |
| D | `Module M <: SIG := Impl` (transparent) | **no** (full interface, ctor nameable) | yes |
| E | transparent inductive + `Local Definition` equality guard | **no** — client forges `DC v eq_refl` (conversion) | yes |

Opaque and transparent ascriptions bracket the needed middle point without hitting it. This is contract
**stop-condition 5** ("cannot implement the sealed API without exposing a raw constructor"); the public
acquisition topology is Rob-reserved (line 1015).

---

## The relaxations the reviewer can choose among

### R1 — accept practical (not proof-level) sealing; keep everything working *(least disruptive)*

Keep `Decision`/`Compilation`/payloads **transparent** (witnesses/goldens unchanged). Fix the *real* finding-#1
defects soundly: delete every `*_of_nilb`; make `inspect` the sole payload route in all witnesses; make the whole
canonical composer chain (`index`/`surface`/`bindings`/`analysis`/the top composer) `Local Definition`
(un-nameable), and make `mk_compilation`/`DCompiled` unreachable by any **named/ordinary** route. Hostile controls
then prove a client cannot forge via any named constructor, composer, `nilb`, or report-equality route. The
acknowledged residual: a determined adversary could hand-reconstruct a target program's exact canonical value and
close the guard with `eq_refl` — impractical, but **not** a type-level impossibility.

This is the most defensible fit for the accepted **cooperating-developer** threat boundary (scope row SR-005), but
it **contradicts §Required-validation-2 line 818** ("impossible states must be established by Rocq type
topology"). Choosing R1 means relaxing that sentence to "no forgery via any named/ordinary route," and rewording
the §10 controls to target *ordinary construction/forgery* rather than *naming*.

### R2 — keep proof-level sealing; change the witness/provenance architecture

Make `Decision` opaque (every §10 control passes literally). Since no concrete program can then be reduced or
proved to compile through the sealed API, the certified-emit link must be re-founded: e.g. move the
compile-certification into a **trusted** materialization step, or expose a reducible decision that the contract
currently forbids. This is a substantial redesign that likely conflicts with §Preservation (`Emit.of_safe` sole
route; preserved certified bytes) and with (3) above. I do not recommend it without a concrete alternative
provenance design from the reviewer.

### R3 — a Rocq technique I have not found

If the reviewer knows an idiom for a **reducible-yet-abstract** sum type, or a materialization route that survives
opacity without a forbidden second authority, please point me to it and I will implement §2/§10 literally.

---

## What I need decided

1. **R1**, **R2**, or **R3**.
2. If **R1**: confirmation that the §10 controls may target *forgery via named/ordinary routes* (not constructor
   *naming*), and that this "no ordinary forgery" property is the accepted meaning of "genuinely sealed" for C4
   under the cooperating-developer threat model — i.e. line 818 is relaxed accordingly. I then proceed through the
   full dependency order and deliver one candidate.
3. If **R2**: the alternative provenance/materialization design.
4. If **R3**: the technique or reference.

Everything downstream (shallow-cell `Index`, applicability-first `Analysis.Result`, coexisting issue rows,
complete import-path preflight, projection-only `Report`) is independent of this choice **except** how the
payloads/result are exposed — which is why the dependency order puts the public topology first and why I have not
begun the lower layers.

---

## Appendix — the two decisive spikes (reproducible)

**Spike C (opacity kills reduction).**
```coq
(* SpikeSealed.v *)  Module Type DEC_SIG.
  Parameter Dec : nat -> Type.  Parameter compile : forall p, Dec p.
  Inductive Case (p:nat)(d:Dec p):Type := IsC:p=0->Case p d | IsR:p<>0->Case p d.
  Parameter inspect : forall p (d:Dec p), Case p d.  End DEC_SIG.
Module DecImpl <: DEC_SIG.
  Inductive Dec_(p:nat):Type := DC:p=0->Dec_ p | DR:p<>0->Dec_ p.  Definition Dec := Dec_.
  Definition compile p : Dec p := match Nat.eq_dec p 0 with left h=>DC p h|right h=>DR p h end.
  Inductive Case (p:nat)(d:Dec p):Type := IsC:p=0->Case p d | IsR:p<>0->Case p d.
  Definition inspect p (d:Dec p):Case p d := match d with DC _ h=>IsC p d h|DR _ h=>IsR p d h end.
End DecImpl.  Module Dec : DEC_SIG := DecImpl.
(* SpikeClient.v *)  From Fido Require Import SpikeSealed.
Example e : (match SpikeSealed.Dec.inspect 0 (SpikeSealed.Dec.compile 0) with
             SpikeSealed.Dec.IsC _ _ _ => true | SpikeSealed.Dec.IsR _ _ _ => false end) = true.
Proof. vm_compute. reflexivity. Qed.   (* FAILS: "Unable to unify true with <stuck>" *)
```

**Spike E (a transparent `Local`-guard is forgeable).**
```coq
(* SpikeSealed.v *)  From Stdlib Require Import Arith.
Local Definition elaborate (p:nat) : nat := p + 7.
Inductive Dec (p:nat):Type := DC : forall c:nat, c = elaborate p -> Dec p | DR : Dec p.
Definition compile p : Dec p := DC p (elaborate p) eq_refl.
(* SpikeClient.v *)  From Fido Require Import SpikeSealed.
Fail Definition hostile_forge : SpikeSealed.Dec 3 := SpikeSealed.DC 3 10 eq_refl.
(* "The command has not failed!" — the forge TYPECHECKS: conversion reduces elaborate 3 to 10,
   so eq_refl : 10 = 10 closes the guard c = elaborate 3, even though `elaborate` is un-nameable. *)
```
