# Problem statement — the §19 branch-carried reader will not `vm_compute`

Contract `bd41f0a8` (C4 Exact Retained Analysis Fact-Row). The exact-fact-row main root is implemented and
vm-safe. The one blocker is §19's concurrent closeout: the concrete e2e reader must acquire the retained Analysis
`Result` from `Compilable.compile p`'s branch object (not a fresh `Analysis.analyze p`), and that reader does not
reduce under `vm_compute` within budget. Rob authorized making the branch object's stored emptiness/nonemptiness
witness proof-insensitive (opaque). That change was implemented and **did not** remove the cliff. This document is
the full problem statement, with the exact definitions, the exact evidence, what was tried, and the candidate
mechanisms — including one unresolved inconsistency that a single further experiment would settle.

---

## 1. What the reader must be, and why it must reduce

§19 requires `e2e/WitnessReject.v` to stop reading `Analysis.analyze p` directly and instead project the retained
`Result` out of the branch object `compile` produces:

```coq
Definition result_of_compile (p : Syntax.Program) : AN.Result p :=
  match Compilable.disposition p as k return Compilable.OutcomeAt p k -> AN.Result p with
  | Compilable.Compiled     => Compilable.program_result
  | Compilable.Rejected     => Compilable.rejection_result
  | Compilable.OutsideScope => Compilable.outside_result
  end (Compilable.compile p).
Definition rres (p : Syntax.Program) : AN.Result p := result_of_compile p.
```

`result_of_compile p = AN.analyze p` is provable by the kernel (`result_of_compile_canonical`, via each branch's
`*_result_canonical`). But the concrete e2e controls read `rres p` under `vm_compute` — e.g.

```coq
RP.result_cause_views (rres (prog [ println(iota) ])) = [ RP.CvInvalidIdentity Names.PIota ].  (* vm_compute; reflexivity *)
```

so `result_of_compile p` must *reduce* cheaply, not merely be provably equal to `analyze p`. §19 forbids acquiring
the value through the equality (`rewrite result_of_compile_canonical; vm_compute` — a "fresh analyze route"), and
§29.7 names exactly that as the block condition.

---

## 2. The relevant definitions (verbatim shapes)

### 2.1 `Compilable.v` — the branch decider and the sealed mint

```coq
Local Definition c_result (p : Syntax.Program) : AN.Result p := AN.analyze p.   (* transparent *)

Inductive Disposition := Compiled | Rejected | OutsideScope.

Definition disposition (p : Syntax.Program) : Disposition :=
  let c := c_result p in
  match nil_dec (RP.diagnostics (AN.res_facts c) (AN.res_pkg c)) with
  | left _ => match nil_dec (RP.boundaries (AN.res_facts c)) with left _ => Compiled | right _ => OutsideScope end
  | right _ => Rejected
  end.
```

`disposition` reduces `nil_dec (diagnostics …)` only to WHNF (nil vs cons) and **discards** the proof (`left _` /
`right _`). It is cheap under `vm_compute` (see §3, `probe_disp`).

### 2.2 The seal — everything the reader traverses is a `Parameter`

```coq
Module Type C4_PUBLIC.
  Parameter Compilation : Syntax.Program -> Type.
  Parameter Program   : Syntax.Program -> Type.
  Parameter Rejection : Syntax.Program -> Type.
  Parameter Outside   : Syntax.Program -> Type.
  Definition OutcomeAt (p) (k : Disposition) : Type :=
    match k with Compiled => Program p | Rejected => Rejection p | OutsideScope => Outside p end.  (* transparent *)
  Parameter compile : forall p, OutcomeAt p (disposition p).
  Parameter program_compilation   : forall {p}, Program p -> Compilation p.
  Parameter rejection_compilation : forall {p}, Rejection p -> Compilation p.
  Parameter outside_compilation   : forall {p}, Outside p -> Compilation p.
  Parameter compilation_result : forall {p}, Compilation p -> AN.Result p.
  Parameter compilation_result_canonical : forall {p} (c : Compilation p), compilation_result c = AN.analyze p.
  ... (Diagnostic/Boundary/diagnostics/boundaries/Admissible/… also Parameters) ...
End C4_PUBLIC.

Module Sealed : C4_PUBLIC.        (* opaque signature ascription ':' *)
  Record CompilationR p := mkComp { c_res : AN.Result p ; c_prov : c_res = AN.analyze p }.
  Definition elaborate (p) : Compilation p := mkComp (AN.analyze p) eq_refl.   (* the sole composer, PRIVATE *)
  Definition compilation_result {p} (c) : AN.Result p := c_res c.
  Record ProgramR   p := mkProg { pr_comp ; pr_adm  : Admissible pr_comp }.
  Record RejectionR p := mkRej  { rj_comp ; rj_diag : diagnostics rj_comp <> [] }.
  Record OutsideR   p := mkOut  { ou_comp ; ou_diag : diagnostics ou_comp = [] ; ou_bnd : boundaries ou_comp <> [] }.
  Definition compile (p) : OutcomeAt p (disposition p).
  Proof.
    unfold OutcomeAt, disposition. cbv zeta. set (c := c_result p).
    destruct (nil_dec (RP.diagnostics (AN.res_facts c) (AN.res_pkg c))) as [Hd|Hd].
    - destruct (nil_dec (RP.boundaries (AN.res_facts c))) as [Hb|Hb].
      + exact (mkProg (mkComp c eq_refl) (conj Hd Hb)).
      + exact (mkOut  (mkComp c eq_refl) Hd Hb).
    - exact (mkRej  (mkComp c eq_refl) Hd).
  Defined.
  ...
End Sealed.

(* outside the module — thin re-exports of the SEALED (Parameter) components *)
Definition compile := Sealed.compile.
Definition compilation_result   {p} := @Sealed.compilation_result p.
Definition program_compilation  {p} := @Sealed.program_compilation p.
Definition rejection_compilation {p} := @Sealed.rejection_compilation p.
Definition program_result   {p} (cp : Program p)  : AN.Result p := compilation_result (program_compilation cp).
Definition rejection_result {p} (r  : Rejection p) : AN.Result p := compilation_result (rejection_compilation r).
Definition outside_result   {p} (o  : Outside p)   : AN.Result p := compilation_result (outside_compilation o).
```

`compile`, `program_compilation`, `rejection_compilation`, `compilation_result` are all `Parameter`s in the sealing
signature. `program_result`/`rejection_result`/`outside_result` are `compilation_result (…_compilation …)` — i.e.
the whole reader path is `compilation_result (rejection_compilation (compile p))` for a rejected program.

### 2.3 The `Result` and its subset-typed components

```coq
Record Result (p) := mk_result { res_index : Index.ProgramIndex p ; res_surface ; res_bind_data ; res_binds ;
                                 res_facts : FactPhase res_binds ; res_pkg : PackageFacts res_binds }.
Definition analyze (p) := mk_result (index_program p) … (facts b) (package_facts b).

(* Index.v *)          Definition ProgramIndex p := { m : Collections.FileMap.t FileInfo | m = raw_index p }.
                       Definition index_program p := exist _ (raw_index p) eq_refl.        (* a SIG value *)
(* Analysis.v *)       Definition FactPhase := { m : list (OccFact bp) | m = raw_facts }.
                       Definition facts := exist _ raw_facts eq_refl.                       (* a SIG value *)
                       Definition fact_list (fp) := proj1_sig fp.
```

So `res_index (analyze p) = exist _ (raw_index p) eq_refl` — this is the `exist (fun x => x = {| … |})` that shows
up in the `res_index` probe error below. `res_facts (analyze p) = facts = exist _ raw_facts eq_refl`.

### 2.4 Why the issue lists are expensive on the vm path (the whole point of this candidate)

The main root re-indexed every occurrence diagnostic to carry an exact `FactRowRef` (an ordinal + retained row +
`nth_error` membership) over the canonical `FactPhase`. Reading/forcing a fact-row diagnostic's **cause** on the
concrete `vm_compute` path is the cliff the candidate is built to avoid — every concrete control reads bp-free
views computed directly from `fact_list`, and the exact fact-row refs are checked only in abstract-`bp` kernel
laws. `RP.diagnostics` (which `disposition`, `compile`, and the branch records all reference) is exactly this
expensive-to-fully-force list.

---

## 3. The evidence (exact probe outcomes)

All probes are in `e2e/WitnessReject.v`, compiled by `make emit` (which builds the theory, then compiles
WitnessReject after "evidence DAG OK"). `probe_prog := prog [ println(iota) ]` — one tiny rejected program.

| Probe | Term (LHS) | `vm_compute` outcome |
|---|---|---|
| `probe_disp` | `Compilable.disposition probe_prog = Rejected` | **cheap, passes** |
| baseline | `RP.result_cause_views (analyze probe_prog)` and all `rres:=analyze` controls | **cheap**; `make emit` = 28 s |
| `r_iota_cause` | `RP.result_cause_views (result_of_compile probe_prog) = [CvInvalidIdentity]` | **Timeout 40 s** |
| `probe_reader_len` | `length (fact_list (res_facts (result_of_compile probe_prog))) = length (… (analyze …))` | **Timeout 30 s** |
| `probe_reader_index` | `res_index (result_of_compile probe_prog) = res_index (analyze probe_prog)` | **fast fail**: `Error: Unable to unify` `"exist (fun x => x = {| … |})"` … (NOT a timeout) |

Whole-`make emit` with `rres := result_of_compile`: hangs after "evidence DAG OK", killed at 300 s.
Whole-`make emit` with `rres := analyze`: 28 s, generated bytes byte-identical, all controls green.

So: `disposition` and every `analyze`-based read are cheap; every `result_of_compile`-based read is not, and the
cost is *entirely* in reducing `result_of_compile p` — nothing downstream.

---

## 4. What was tried (Rob-authorized) and why it did not work

**Attempt: make the stored branch witness opaque (proof-insensitive for reduction).** First-block hypothesis was:
`compile`'s transparent `destruct (nil_dec …)` binds `Hd : diagnostics <> []` and *stores* it in the branch record
(`rj_diag` etc.); reducing `compile p` to WHNF forces `Hd`, which forces the expensive `diagnostics`. `disposition`
stays cheap because it *discards* the same proof.

I replaced `compile` with: select the branch by the sole computational decider `disposition`, and fill each branch
record's proof field with an **opaque `Qed` lemma** about the exact already-elaborated Result:

```coq
Lemma rejected_diag (p) (H : disposition p = Rejected) : diagnostics (elaborate p) <> [].  (* Qed, by inverting disposition *)
Definition compile (p) : OutcomeAt p (disposition p) :=
  match disposition p as k return disposition p = k -> OutcomeAt p k with
  | Compiled     => fun H => mkProg (elaborate p) (compiled_admissible p H)
  | Rejected     => fun H => mkRej  (elaborate p) (rejected_diag p H)
  | OutsideScope => fun H => mkOut  (elaborate p) (outside_diag_empty p H) (outside_bnd_nonempty p H)
  end eq_refl.
```

This is strictly nicer — the branch witness is now logical evidence (opaque), and it removes `compile`'s *second*
`nil_dec` decider in favour of the single `disposition` decider. The four inversion lemmas are kernel-checked and
assumption-free; the theory built green. **But `probe_reader_len` still timed out at 30 s** — the reader is still
not vm-reducible. So opacity of the branch witness alone does not remove the cliff. (Per Rob's fallback, the
`compile` change was then reverted, since the spike did not succeed.)

---

## 5. Candidate mechanisms — and the one unresolved inconsistency

Two mechanisms are each consistent with *part* of the evidence, and they conflict on the `res_index` vs
`res_facts` probes. Resolving which is true is the crux.

### (A) Opaque sealed-projection barrier
`compilation_result`, `compile`, `rejection_compilation` are `Parameter`s under `Module Sealed : C4_PUBLIC`
(opaque ascription). If they are opaque to `vm_compute`, then
`result_of_compile p = compilation_result (rejection_compilation (compile p))` is **stuck** at the seal and never
reaches the `mk_result` structure. This **explains `probe_reader_index`'s fast fail**: `res_index` cannot match a
stuck `compilation_result (…)`, so the LHS stays stuck while the RHS reduces to `exist _ (raw_index p) eq_refl`, and
`reflexivity` reports "Unable to unify … exist(…)". Under (A) the branch-witness opacity is irrelevant, because the
barrier is the sealed *Result projection*, not the witness — and un-sealing `compilation_result` for reduction is a
change to the public branch topology / trust boundary, which is out of scope.

**But (A) predicts `probe_reader_len` should also fast-fail** (a stuck LHS compared to a concrete nat), not time
out. It timed out. So (A) alone is incomplete.

### (B) Transparent-but-expensive reduction
If the sealed components are in fact delta-reducible (transparent ascription behaviour), then reducing
`result_of_compile p` fully forces `compile p`, whose branch record forces the expensive fact-row `diagnostics`.
This **explains the `probe_reader_len` / `r_iota_cause` timeouts**. Under (B) the opaque branch witness *should*
have helped (it moves the diagnostics-forcing proof off the value path) — but it did not, which is itself evidence
against a naive version of (B).

**And (B) does not obviously explain `probe_reader_index`'s fast fail** — if `result_of_compile p` reduces (even
expensively) to the same `Result` as `analyze p`, `res_index` of both should be the identical `exist _ (raw_index
p) eq_refl` and `reflexivity` should *succeed*. It failed with "Unable to unify". That means either the LHS is
stuck (→ mechanism A), or the two reductions reach `exist`s with **different proof components** (a proof-relevance
/ UIP-style mismatch through the two paths) even though the carried data (`raw_index p`) is equal.

### (C) What the `res_index` residual actually shows — partial reduction leaving a proof-bearing residual
The full `probe_reader_index` unification error resolves the A/B conflict toward a third, more precise picture. The
two sides being unified are:

- **RHS** (`res_index (analyze p)`): the clean, fully-reduced `exist (fun x => x = {| FileMap.this := … concrete
  raw_index of println(iota) … |}) … eq_refl` — i.e. `index_program p` computed to a ground value.
- **LHS** (`res_index (result_of_compile p)`): a **large residual term riddled with nested stuck matches** —
  `match x1 with … match x6 with … match x4 with …` over bound variables `x1 … x13`, wrapping the same cell data.

So `result_of_compile p` is **neither** a clean opaque-stuck `compilation_result (…)` head (pure A) **nor** a clean
`mk_result …` equal to `analyze p` (pure B). It reduces *partway* — through the sealed re-exports and `compile`'s
dependent `match disposition p as k return OutcomeAt p k` + `destruct (nil_dec …)` machinery — and gets **stuck on
proof-bearing sub-terms** (the `nil_dec` disequality witnesses are functions `fun H => … match … end`; the
dependent-outcome convoy leaves motive matches), yielding a big residual instead of the ground `Result`.

That single picture explains all three failing probes:
- `res_index` threads through the residual and lands on a stuck-`match` term ≠ the ground `exist` → **fast unify
  fail** (the residual is big but finite).
- `res_facts` → `fact_list` → `length` threads through the *same* residual but now also over the fact-row issue
  lists, so building/forcing it explodes → **timeout**.
- `result_cause_views (result_of_compile …)` is the `res_facts` path plus the view fold → **timeout**.

It also explains why the opaque branch witness did not help: opacifying `rj_diag`/`pr_adm` removes one source of
`match`-under-`fun` residual, but the **dependent-outcome convoy** (`match disposition p as k return OutcomeAt p k
-> …`) and the sealed re-export wrapping still leave a stuck residual that never collapses to the ground `Result`.

### The decisive experiment (still worth running to fully pin the residual's origin)
```coq
Set Printing All.  Eval vm_compute in (result_of_compile (prog [ println(iota) ])).
```
Read the head and the first stuck `match`: is the residual rooted at `Sealed.compilation_result`/a `Parameter`
(seal barrier — un-sealing needed), or at `compile`'s own `match … return OutcomeAt …`/`nil_dec` convoy
(reducible-but-non-collapsing — a `compile` reformulation whose branch object reduces to a ground `Result` is
needed)? The residual shape above points at the latter, but the head confirms which.

---

## 6. Constraints (must hold for any fix)

- Branch choice and the retained `Result` are **computational data**; the proof certifying the branch choice is
  **logical evidence, opaque, not computational authority**. Its statement must be about the exact already-computed
  Result/branch, and it must stay kernel-checked and assumption-free — never an unchecked cache or a second
  semantic authority.
- Preserve the exact branch type, exact `Result`, exact `disposition`, and theorem strength.
- No second decider, boolean classifier, report recomputation, equality-to-rerun acquisition path, or alternate
  capability mint.
- Do not change the public branch topology / trust boundary of the sealed `Compilable` mint beyond the narrow,
  authorized proof-shape repair.
- The concrete e2e controls read `rres p = result_of_compile p` under `vm_compute`; acquisition must be through
  `compile`, never through `result_of_compile_canonical`.
- Budget: warmed complete-path `make check` ≤ 120 s.

---

## 7. State of the tree

- Main root (exact fact-row identity) implemented; `make prove` + `make emit` green with `rres := analyze`;
  generated Go byte-identical. Uncommitted.
- `result_of_compile` + `result_of_compile_canonical` retained as the §19 reader + its `= analyze` theorem
  (kernel-checked). `rres := analyze` (green) pending resolution of this cliff.
- The opaque-branch-witness `compile` change was implemented, shown insufficient, and reverted.
- Nothing committed or pushed.
