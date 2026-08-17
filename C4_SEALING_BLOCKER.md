# C4 correction — sealing vs. reducible witnesses: a design decision for the reviewer

**Status:** `BLOCKED_FOR_ROB` at dependency-order step 2 (public topology) of the C4 correction contract
(`ebf80c34-WORK_CONTRACT.md`). No code was changed to reach this conclusion; the working tree is exactly the
entry state (commit `1306aa190fc1a21fd8c1bc94dde56c10f8054409`, tree `b39729a19afb1ef429652c5ac4fcd53ae71e04ba`,
clean). Four throwaway spikes were built, observed, and deleted.

This file exists only to hand the decision to the reviewer. It is not part of the governing corpus and should be
deleted once the sealing approach is chosen.

---

## The ask, in one paragraph

Contract finding #1 requires a **genuinely sealed** public surface: `Compilation`, `Decision`, the branch
payloads, and the compiled capability must be **abstract outside the sealed owner**, with their constructors
**absent from the client namespace**, and §10 requires hostile-client controls that fail when a client tries to
**name** a raw constructor or **pattern-match the Decision directly**. Separately, §Preservation and §12 require
the certified witnesses to keep **materializing to bytes** (`make emit`/`e2e`, preserved goldens). In this Rocq
toolchain those two requirements are **mutually exclusive**: making `Decision` abstract forces `compile`/`inspect`
to be non-reducing in client code, and the materializer cannot then compute the witness image. I need the reviewer
to choose which requirement gives, or to supply a Rocq technique that satisfies both. My recommendation is
**Resolution A** below.

---

## Why the two requirements collide

### Materialization requires client-side reduction of `compile`/`inspect`

The witness image is produced by the `Fido Materialize` plugin, which normalizes the transport term with
`Reductionops.nf_all` (`plugin/materialize.mlg:213`). `nf_all` does **not** unfold opaque constants. The witness is

```coq
demo_safe  := Safe.certify demo_program (compile demo_program) c cp _   (* c, cp from inspect *)
demo_image := Emit.of_safe demo_safe
```

`Safe` uses primitive projections, so `Safe.source demo_safe` reduces to `demo_program` **without** forcing the
heavy phases — good. But obtaining `c` and `cp` still requires eliminating the decision:

```coq
match Compilable.inspect (Compilable.compile demo_program) with
| IsCompiled c cp => Safe.certify demo_program (compile demo_program) c cp _
| _ => (* no image exists for a non-compiling program *)
end
```

For this to reduce to a concrete `Safe.certify …` (so `Safe.source` can then project the source), the scrutinee
`inspect (compile demo_program)` must reduce to `IsCompiled c cp`. That requires `compile` and `inspect` to be
**delta-reducible in the client**. The same is true for proving *any* fact about a concrete program's compilation
(e.g. `compiles demo_program`): the proof reduces `compile`, which requires transparency.

### Abstracting `Decision` forces `compile`/`inspect` opaque

Hiding a constructor's **name** from clients (so `Fail Definition x := Compilable.DCompiled` actually fails, per
§10) requires the type to be **abstract** — i.e. exposed through an opaque module signature. Under an opaque
ascription, the module's operations become opaque constants, and `nf_all`/`vm_compute` leave
`inspect (compile p)` **stuck**. So the witness image cannot be computed, and no concrete program can even be
*proved* to compile.

There is no ascription in this Rocq that yields *reducing operations* **and** *un-nameable constructors*.

---

## Mechanisms tried (all four spikes deleted; each was a `make prove-errors` observation)

| Mechanism | Hides the constructor name? | `inspect (compile p)` reduces in a **separate client file**? |
|---|---|---|
| `Local Module` / `Local Inductive` | — | **rejected**: "This command does not support this attribute: local" |
| `#[private(matching)] Inductive` | **no** — the client both names the constructor and matches `Decision` directly | yes |
| `Module M : SIG := Impl` (opaque) | **yes** | **no** — `vm_compute (inspect (compile 0))` is stuck; `reflexivity` fails to unify |
| `Module M <: SIG := Impl` (transparent) | **no** — the full interface (incl. constructors) is exposed | yes |

The opaque and transparent ascriptions are the two endpoints Rocq offers; neither is the needed middle point.

This is precisely contract **stop-condition 5**: *"The sealed public API cannot be implemented without exposing …
a raw constructor …."* To keep the required reducing witnesses, the raw `Decision` constructor must remain
nameable. Because the public acquisition topology is Rob-reserved (contract line 1015), I stopped here rather than
pick a resolution myself — especially since the previous candidate's sealing was found to be only cosmetic.

---

## Resolution options

### Resolution A — provenance sealing (recommended)

Keep `Decision`/`Compilation`/payloads **transparent** (so the witnesses still materialize), and make **forgery
impossible** rather than making the constructor un-nameable:

- The private composer is a `Local Definition elaborate` (Rocq **does** support `Local Definition`, unlike
  `Local Module`/`Local Inductive`), so `elaborate` is **un-nameable** by any client.
- `DCompiled` carries a witness tying its compilation to the private composer, e.g.
  `DCompiled : forall c, c = elaborate p -> Admissible c -> Decision p`. A client cannot write `elaborate p`
  (un-nameable), so **cannot construct the required equality**, so **cannot apply `DCompiled`** to mint a decision
  from fabricated data.
- `CompiledPayload` is **abstract**, obtained only from `inspect`; a client cannot extract the composer-equality
  from a payload to route around the guard.
- All `*_of_nilb` helpers are **deleted**; `inspect` is the sole eliminator; `compiled_prog` (already an opaque
  capability, whose bytes are avoided via `Safe.source`) stays the sole capability maker.

**What this achieves (the security intent of finding #1):** no client can forge a `Decision`, a `CompiledPayload`,
a `Prog` capability, or an `Emit.Image` for a program that did not actually compile — including via the previously
abused `*_of_nilb` list-equality route or a `DCompiled` applied with a provable `Admissible`. `compile` is the sole
first source of a *valid* decision; `inspect` the sole source of a payload; `compiled_prog` the sole source of the
capability. The witnesses keep materializing unchanged; goldens are preserved.

**What it does not achieve (the residual, versus the literal §2/§10 wording):** the raw constructor **name**
(`Compilable.DCompiled`) is technically still in the client namespace, though inert — it cannot be applied to forge.
A client can also `match` a `Decision` directly, but that only yields an already-legitimate compilation (the same
one `inspect` would give) and a reusable equality — it forges nothing. The §10 hostile controls would therefore
target **application/forgery** (constructing a valid decision/payload/capability/image from fabricated data — must
fail) instead of **naming**.

**One confirming spike still owed:** whether a public constructor whose *type* mentions a `Local Definition`
(`c = elaborate p`) exports cleanly and genuinely blocks client application. This is a ~one-build check I will run
first if A is chosen.

### Resolution B — fully opaque `Decision`

Seal `Decision` through an opaque signature so every §10 hostile test passes **literally** (naming and direct-match
both fail). This forbids client-side reduction, so the certified witnesses can no longer be Rocq-computed to bytes.
It requires **replacing the certified-emit/materialize architecture** (how a concrete program is shown to compile
and how its bytes are produced) and very likely conflicts with §Preservation (`Emit.of_safe` as the sole image
route; preserved paths/bytes/modes/goldens). This is a large, high-risk redesign and I do not recommend it without
a concrete alternative materialization design.

### Resolution C — a Rocq technique I have not found

If the reviewer knows an idiom for a **reducible-yet-abstract** sum type (client reduction of `inspect ∘ compile`
while the constructors are un-nameable), or a materialization route that survives opacity, please point me to it and
I will implement the literal §2/§10 seal as written. My four spikes did not find one, and the module system's
opaque/transparent endpoints appear to bracket the needed behavior without hitting it.

---

## What I need decided

1. **Which resolution** (A recommended / B / C).
2. If **A**: confirmation that the §10 hostile controls may target **forgery/application** rather than
   **constructor-naming**, and that the "provenance sealing" guarantee above is the accepted meaning of "genuinely
   sealed" for C4. I will then run the one confirming spike and proceed through the full dependency order (Index →
   PackageIdentity → Bindings → Analysis → Report → Compilable → Safe/Emit → controls → docs), delivering one
   candidate.
3. If **C**: the technique or reference.

Everything downstream (Index shallow-cell rewrite, applicability-first `Analysis.Result`, coexisting issue rows,
complete import-path preflight, projection-only `Report`) is unaffected by this choice **except** that whether
`CompiledPayload` is abstract (A) or the surface is fully opaque (B) changes how `Analysis.Result` and the payloads
are exposed — which is why the contract's own dependency order puts the public topology first, and why I did not
begin the lower layers before this is settled.

---

## Appendix — decisive spike (reproducible)

The opaque-ascription spike that proves reduction is lost (the others are analogous):

```coq
(* SpikeSealed.v *)
From Stdlib Require Import Arith.
Module Type DEC_SIG.
  Parameter Dec : nat -> Type.
  Parameter compile : forall p, Dec p.
  Inductive Case (p : nat) (d : Dec p) : Type := IsC : p = 0 -> Case p d | IsR : p <> 0 -> Case p d.
  Parameter inspect : forall p (d : Dec p), Case p d.
End DEC_SIG.
Module DecImpl <: DEC_SIG.
  Inductive Dec_ (p : nat) : Type := DC : p = 0 -> Dec_ p | DR : p <> 0 -> Dec_ p.
  Definition Dec := Dec_.
  Definition compile (p : nat) : Dec p := match Nat.eq_dec p 0 with left h => DC p h | right h => DR p h end.
  Inductive Case (p : nat) (d : Dec p) : Type := IsC : p = 0 -> Case p d | IsR : p <> 0 -> Case p d.
  Definition inspect (p : nat) (d : Dec p) : Case p d := match d with DC _ h => IsC p d h | DR _ h => IsR p d h end.
End DecImpl.
Module Dec : DEC_SIG := DecImpl.

(* SpikeClient.v — separate compilation unit *)
From Fido Require Import SpikeSealed.
Example client_reduces :
  (match SpikeSealed.Dec.inspect 0 (SpikeSealed.Dec.compile 0) with
   | SpikeSealed.Dec.IsC _ _ _ => true | SpikeSealed.Dec.IsR _ _ _ => false end) = true.
Proof. vm_compute. reflexivity. Qed.   (* FAILS: "Unable to unify true with <stuck term>" *)
```

Observed: the client `Example` fails — opaque ascription blocks the reduction the materializer needs. With `<:`
(transparent) the same `Example` succeeds, but then `Fail Definition x := SpikeSealed.Dec.DC 0 h` does **not**
fail (the constructor is nameable), i.e. the seal is cosmetic.
