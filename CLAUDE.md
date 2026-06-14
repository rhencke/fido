# Fido

Formally verified Go programs. Theorems are proved in Rocq; the Go is a
proof artifact, not something written by hand. Nothing in `*.go` is ever
edited directly — it is always extracted from `*.v`.

## The goal

Be **safer than Go's compiler can prove** — type, memory, and concurrency
safety lifted to compile time — while still lowering into ordinary Go for the
primitives we like (channels, goroutines, maps, slices). Those primitives are
good at runtime but weak *statically*. Go doesn't *prevent* memory errors so
much as *contain* them: a nil deref or out-of-bounds access is a real
violation that Go traps into a panic rather than ruling out. And the
containment is conditional — under a data race Go isn't memory-safe at all (a
torn interface or slice header is type confusion, i.e. genuine corruption, not
a panic), which is why races get a *runtime* detector instead of a static
check. Fido instead proves these cannot happen — nil deref, use-after-close,
out-of-bounds, send-on-closed, data races — all ruled out at compile time
before any Go is emitted. Rocq supplies the compile-time guarantees; Go
supplies the runtime and the primitives.

We add these guarantees incrementally, as needed. The target is concurrent
programs (channels, goroutines) where the interesting properties are:

- **Protocol compliance** — session types on channels; both ends follow
  the same send/receive sequence, enforced by Rocq's type checker
- **Race freedom** — ownership tracking through channel operations
- **Deadlock freedom** — eventually, via liveness proofs
- **Panic freedom (logical)** — no nil deref, out-of-bounds, failed type
  assertion, send-on-closed, etc.  These already live in `IO`; the plan is to
  discharge each as a Hoare precondition so Rocq propagates the obligation to
  every call site (a partiality discipline, like the session `Fail` tests).
  Requires extending `run_io` to expose panic as an *outcome* rather than
  conflating it with divergence (so `hoare_panic` need no longer be admitted).
  Explicitly **modulo resources**: OOM and stack overflow are Go *fatal
  errors*, not panics — the heap is modelled as unbounded and they are out of
  scope.  The claim is "panic-free given sufficient resources", never "never
  crashes".
- **Overflow freedom (provable)** — integer overflow in Go is *silent*
  wraparound at runtime (unchecked), and only *constant* overflow is caught,
  by the compiler.  Fido makes "this arithmetic does not overflow" a Rocq
  theorem: a no-overflow precondition implies the result equals the exact
  mathematical value.  Intentional wrap stays available as an opt-in.  We do
  **not** lean on `go build` or Go's silent runtime wrap — overflow checking is
  usefully provable in Rocq, which is the whole point.

These concurrency properties rest on a substrate we must model explicitly: the
**happens-before** relation as documented by the Go memory model
(go.dev/ref/mem).  Race freedom is *defined* by it — a race is two conflicting
accesses, at least one a write, unordered by happens-before — and it is what
actually justifies the channel ordering laws (a send happens-before the
matching receive completes; a receive from an unbuffered channel happens-before
its send completes; the kth receive on a capacity-C channel happens-before the
(k+C)th send).  Today those laws (`send_recv`, …) lean on bind-sequencing
intuition; happens-before is the honest foundation, and the cross-goroutine
proofs cannot even be *stated* without it.

We don't need all of this now. The architecture supports adding each layer
without redesigning what came before.

**Principle: small scope, but correct within that scope.** When we model
something, model it honestly — wrong type mappings, hand-waving over
tricky semantics, or silent overflow are not acceptable even in early
stages. It's fine to leave things unmodeled; it's not fine to model them
wrong.

**Principle: completeness is the thesis — model *all* of Go, faithfully.** We
add primitives incrementally (small scope), but the goal is that Go can be
*fully* modelled in Rocq, and no primitive we model may be left with *partial*
semantics.  The only acceptable deviations are **principled and bounded** — a
deliberate safety guarantee (e.g. nil dereference made unrepresentable) or an
unavoidable limit of the substrate (e.g. one bit of int precision lost to
Rocq's 63-bit primitive).  Difficulty is **never** a licence for partiality: a
hard primitive like `goto` must be modelled fully (a labeled-block / CFG
model), not approximated to a convenient subset.  "It's hard" means "do the
work", not "model less".

**Principle: partial operations are safe-by-construction or proof-gated.**
The unsafe primitives — nil deref, out-of-bounds, divide-by-zero,
send-on-closed, failed type assertion — must be *modelled* (we don't pretend Go
lacks them), but modelled so their unsafe use is forbidden by default or
rejected. Prefer a total, **evidence-carrying** API: one that demands a proof
of safety (`i < len xs`, `d <> 0`, pointer non-nil) and extracts to the raw Go
op unguarded, because the proof discharged the guard. Where safety depends on
runtime values, force a **check-and-branch** that yields the evidence (the
comma-ok / `option` shape, as with `map_get_opt`) so the failure case cannot be
ignored. The raw panicking form survives only as an explicitly-marked escape
hatch (in `IO`, recoverable via `catch`); reaching for it is opting out of the
guarantee, and the panic-freedom proofs flag it. You should never be able to
*accidentally* write a Rocq program that needs a nil deref or an out-of-bounds
to work.

## Wish list

Further-out proofs that **closed-world reasoning** unlocks once the primitive
layer is complete — i.e. once a value's whole lifecycle can stay inside the
modelled fragment ("we control every method and module it passes through").
Each extends a guarantee we already have rather than inventing a new kind.
All gated on structs / methods / interfaces, and on *closure being
enforceable* — no escape via `any`/reflection, unsynchronised sharing, or
unmodelled callbacks.

- **Behavioral interface satisfaction** — not just "T has method M" (a local
  check in the dictionary model) but "M obeys a contract, preserved everywhere
  the value flows". The preservation is what needs the closed world.
- **Typestate** — a value advancing through states (File: Open→Readable→Closed;
  Conn: New→Authed→Active→Closed), every method call a provably legal
  transition. Session types for values instead of channels.
- **Representation invariants** — a struct invariant (sorted, balanced, indices
  in range) preserved by every method.
- **Information flow / taint** — "this secret never reaches a sink", "input is
  sanitised before the query". Whole-program properties, meaningless open-world.
- **Value-level ownership** — extend channel-endpoint ownership (race freedom)
  to heap values: no aliasing, no use-after-close.

Interdependence to remember: closed-world for a *shared* value presupposes the
ownership / race-freedom discipline (another goroutine could mutate it out from
under the invariant), so these and the concurrency proofs are one web, not
separate tracks.

## Incremental ladder

1. **Builtins** (done) — `println`, `print`, `panic`, `any`, primitive types,
   `GoSlice`, `GoString`, `GoMap`, `type_assert`. Add to `builtins.v` + plugin match
2. **IO monad** (done) — `bind` lowers to sequential Go; world token erases;
   `panic : GoAny -> IO A` is consistent and short-circuits via `bind_panic_l`;
   `catch`/`with_defer` for panic recovery
3. **Hoare logic** (done) — `run_io` denotational semantics (proof-only);
   monad laws are provable lemmas; `{{ P }} m {{ Q }}` Hoare triple defined;
   `hoare_ret`, `hoare_bind`, `hoare_consequence`, `hoare_seq` proved
4. **Channel axioms** (done) — `make_chan`/`make_chan_buf`, `send`, `recv`,
   `recv_ok`, `close_chan`. Lower to `make(chan T)`, `ch <- x`, `<-ch`,
   `x, ok := <-ch`, `close(ch)`
5. **Goroutines** (done) — `go_spawn`. Ownership of channel endpoints
   transfers to the spawned goroutine at spawn time
6. **Session types** (done) — `Proto`/`dual`, `SessEndpoint`, `sess_send`/
   `sess_recv`/`sess_close`. Protocol compliance enforced by Rocq's type
   checker; violations are compile-time errors (the `Fail` tests in `main.v`
   are build-checked negative tests). Pure Rocq guarantee, zero runtime cost
7. **Control flow** — branching and case analysis. Nothing branches today:
   the plugin has no `MLcase` arm, so `if` (sugar for `match` on `bool`) and
   every `match` extract to `nil /* TODO */`. This is a correctness hole, not
   just a missing feature — it compiles wrong instead of failing loudly. Build
   it in two stages, **statements before expressions**.

   **a. Statements first** — `MLcase` in IO / statement position:
   - `if`/`else` (match on `bool`) → `if c { … } else { … }` — the core case
   - `switch` (match on a simple inductive) → Go `switch`/if-chain on the
     constructor; also unblocks `option`, so `map_get_opt` can finally lower
   - type switch (`switch v := x.(type)`) — a separate combinator dispatching
     on a `GoAny`'s runtime type, built on the existing `GoTypeTag` /
     `type_assert` machinery, *not* on `MLcase`
   - design point: an IO-valued branch `bind (match …) k` must thread the
     continuation `k` through every arm — emit each arm's statements then `k`
     in that branch (duplicate, or hoist the result into a var), never a value

   **b. Expressions second** — `MLcase` in value position. Go has no
   conditional expression, so pure `if`/`match` lowers via hoisting or an
   IIFE. *(Still pending — no demo triggers a value-position match yet.)*
   The **operator-precedence printer is done**: `binop_of` gives each inlined
   arithmetic/comparison op a Go precedence (`* / %` = 5, `+ -` = 4, comparisons
   = 3), and `pp_prec ctx e` parenthesises a sub-operand only when its operator
   binds looser than the context requires (left operand at the op's level, right
   at `+1` for left-associativity) — instead of `pp_atom`'s conservative
   "parenthesise every non-atom". `Prec_demo` shows `a*b + c` (no parens) and
   `(a+b) * c` (parens only where needed); existing output is unchanged (those
   operands were already atoms).
8. **`select`** — non-deterministic choice between ready channels. Needed for
   services/multiplexing/timeouts. Significantly harder semantics than linear
   send/recv; wants control flow (each case is a branch) in place first.

## Known gaps

Audit (2026-06-13 sweep) of the partial/unsafe primitives against the
safe-by-construction principle. Tracked until closed.

1. **Integer div/mod by zero** — *resolved; evidence-carrying `div_nz`/`mod_nz`*.
   Rocq's `Uint63`/`nat` division is total (`x/0 = 0`), Go's panics, so a raw
   `/` is silently unsound.  Fix: the plugin emits no *bare* integer `/`/`%`; the
   only way to divide is `div_nz`/`mod_nz`, which **demand a proof the divisor is
   non-zero** (`(d =? 0) = false`, discharged by `eq_refl` for a literal) and
   only then extract to the unguarded `n / d` / `n % d` — the proof discharged
   the panic guard (safe-by-construction, same shape as `slice_at_ok`).
   Underneath they are `PrimInt63.divs`/`mods`, the signed primitives that
   truncate toward zero exactly like Go's int64 (machine-checked
   `div_nz_trunc_neg`: `-7/2 = -3`, `mod_nz_trunc_neg`: `-7%2 = -1` — not the
   flooring `-4`/`1`).  Raw `PrimInt63.divs` stays the escape hatch (Go panics on
   a zero divisor, mirroring raw `send`/`slice_get`).  Float `/` is kept — IEEE,
   no panic.  *Open:* a runtime check-and-branch form (comma-ok) for a
   divisor whose non-zeroness is only known at runtime.
2. **Integer model** — *resolved; ±2⁶² accepted*. `int` is interpreted with
   SIGNED Sint63 semantics matching Go's int64: `+`/`-`/`*` are two's-complement
   (shared with the unsigned primitive), comparison is signed (`ltsb`/`lesb` →
   Go `<`/`<=`), and `2 - 5` is `-3` (machine-checked `sub_signed_matches_go`;
   extracted Go prints `-3`). Overflow is **provable**: `add_no_overflow_exact`
   proves no-overflow → the result is the exact mathematical sum (main.v).
   Accepted limitation (user signed off): Rocq's primitive int is 63-bit, so the
   model is faithful within `[-2^62, 2^62)` — one bit short of int64, fine. No
   Z-model rewrite planned; the `add_wraps_at_boundary` example documents where
   the model wraps.
3. **`slice_get`** — *checked form added*. `slice_at_ok` (CPS, bounds-checked,
   forces handling the OOB case) is now the safe-by-construction default;
   `slice_get` is the escape hatch. Still open: the proof-carrying
   `slice_at xs i (i < len xs)` → `xs[i]` unguarded form, which needs the int
   model (#2).
4. **`type_assert`** — *checked form added*. `type_assert_safe` (CPS, Go's
   native `v, ok := x.(T)`) is the safe-by-construction default; `type_assert`
   is the escape hatch.
5. **Untyped constants** — *open, not yet modelled*. Go integer/float literals
   are *untyped* and arbitrary-precision: constant arithmetic is exact and a
   constant gets a type (with a compile-time representability check) only at the
   point of use. We model literals as already-typed fixed-width values
   (`int` = Sint63, `float64` = IEEE double), conflating the two layers:
   - integer: a constant overflowing its target type is a *compile error* in Go,
     not a runtime wrap; and large constants (`1 << 70`) aren't representable in
     63-bit `int` at all.
   - float: Go does constant float arithmetic at arbitrary precision and rounds
     once at the typed boundary (`const 0.1 + 0.2` = `0.3`), whereas runtime
     `float64` rounds each step (`0.30000000000000004`). Modelling literals as
     IEEE doubles matches the *runtime* answer, not the constant one.
   No impact yet (no large/narrow/constant-arithmetic cases). Accurate model:
   untyped int constants as `Z`, untyped float constants as exact rationals; a
   constant acquires a type only at use, where representability is a proof
   obligation (Go's compile-time check → safe-by-construction). Ties to #2 (the
   Z int model) and to string literals.
6. **Function-scoped `defer`** — *done*. `defer_call f` is Go's `defer`
   keyword — function-scoped, LIFO, runs at function return on both normal and
   panic exit; it lowers to `defer func(){ f }()` (Go provides the scoping,
   ordering, and run-at-return), mirroring `go_spawn`. Distinct from the
   **block**-scoped `with_defer` (an IIFE + `defer`, cleanup at end of the
   wrapped computation). The two now coexist: `defer_call` in a loop accumulates
   and all run at function exit (faithful to Go's `for { defer f() }`);
   `with_defer` runs per scope.
7. **`goto` / unified control-flow model** — *the architecture for all control
   flow* (a primitive — completeness principle; no partial punt). The semantics
   is a **goto-CFG**: every function body is a control-flow graph of basic blocks
   joined by gotos. That is trivially complete — any Go control flow, structured
   or irreducible, is just a CFG, and `goto` is the native edge; the
   non-terminating paths live in IO. The extraction is then a **structuring
   pretty-printer** (Relooper / Stackifier / decompiler-style): it walks the CFG
   and *lifts* it back to idiomatic `if`/`for`/`break`/`continue` where the graph
   is reducible, emitting raw Go labels + `goto` only where it is not.
   **Completeness lives in the model; niceness lives in the printer.** The
   structured combinators we already have (`if`, `for_each`, `slice_fold`) become
   *patterns the structurer recognises*, not the foundation. This supersedes the
   shallow embedding for control flow (a Rocq `if`/Fixpoint *is* the Go
   construct), which cannot express jumps. Biggest build to date; do it
   minimal-faithful-slice first (CFG IR → Go labels+goto), then add the lifting.
   *Status:* CFG IR (`run_blocks`/`Jump`/`Done`) and raw labels+goto are done,
   and a **unified structurer (relooper)** lifts the goto-CFG back to idiomatic
   Go — loops *and* branching, arbitrarily nested. It computes dominators and
   post-dominators (iterative fixpoints, valid with cycles), finds natural loops
   (back-edge = a jump to a dominator), then recurses:
   - a **loop header** → `for { <body> }` then the exit region. A `loopctx`
     (enclosing `(header, exit)` pairs, innermost first) plus a `tail` flag turn
     each terminator into the right thing: a back-edge to the header is the
     loop-around (fall-through when it is the body's natural tail, else an
     explicit `continue`); a jump to the single exit is `break`.
   - a **conditional** → `if`/`else` whose arms run up to their *merge* — the
     immediate (closest) common post-dominator, not min-index, which is wrong
     under cycles — emitted once after the `if`, so no block is duplicated. A
     merge that is the loop-around or loop exit means there is no in-loop merge
     (the arms `break`/`continue`/fall through). Empty arms collapse to a
     one-armed `if`, inverted to `if !c` when the *then* arm jumps to the merge.
   A jump that escapes **more than the innermost loop** is Go's labeled
   break/continue: `handle_edge` scans the whole `loopctx` (not just the top), so
   a jump to an enclosing loop's header is `continue L`, to its primary exit
   `break L`; the loop gets an `L<h>:` label, emitted only when some nested-loop
   edge actually targets it (`needs_label`, so no unused labels). Multi-exit
   loops are fine as long as ≤1 exit is *primary* (emitted after the `for`) — the
   rest must be these labeled escapes (`primary_exits` = exits minus enclosing
   loops' headers/exits). The merge-vs-escape test likewise scans all of
   `loopctx`, so a branch whose post-dominator is an outer exit becomes a
   (labeled) break rather than an inlined block.
   Demos: `Count_demo`/`Defer_loop_demo` → `for { … break }`; `Cond_goto_demo` →
   `if !early { … }`; `Diamond_demo` → `if b { … } else { … }`; `Loopif_demo` →
   a `for` with a nested `if`; `Nested_loop_demo` → two nested `for`s;
   `Early_return_demo` → an in-loop `return` plus post-loop tail;
   `Labeled_break_demo` → an inner loop with `break L0` escaping the outer.
   Two lowering invariants the relooper respects: every block is re-emitted in
   the **call-site de Bruijn env** (a block's free `Ref`s are relative to
   `run_blocks`, not to whatever block jumped to it); and same-named hoists from
   distinct blocks (Rocq reuses a binder name across closed terms) collapse to
   **one** `var`, since they become one reused, assign-before-read Go variable.
   The structurer is gated on `structurable` (entry 0, **reducible**, ≤1 primary
   exit per loop, loops properly nested); anything else falls back to raw
   labels+goto — always correct, just un-prettified. Reducibility (back-edges
   removed ⇒ a DAG) is required because an irreducible CFG has a cycle with no
   dominating back-edge, hence no loop header to stop `emit_region`'s recursion;
   `Irreducible_demo` (a two-entry loop) exercises this fallback and locks the
   raw-goto path in the golden. Golden-guarded: structuring changes the source,
   never the behaviour. Remaining nicety (not coverage): n-ary `switch`/type-
   switch blocks decompose to chained bool `if`s in the goto model rather than a
   Go `switch`.

   **Lowering correctness — the unifying principle.** The goto approach trades
   a single uniform primitive for some subtle correctness obligations; they all
   collapse to one rule: *preserve each model variable's identity under every
   way it escapes.* Each variable is either an **immutable binding**
   (`bind`/`fun x =>` — a value, fresh per evaluation/iteration) or a **`Ref`**
   (one shared cell). It escapes by **read**, **capture**, or **address**:
   - immutable value: read → its value; captured → **by value** (`func(x T){…}(x)`,
     so each iteration's closure fixes its value); address → n/a (not addressable).
   - `Ref` cell: read → the cell; captured → **by reference** (shared var);
     address → `&` the cell (future pointers).
   Our lowering follows this exactly — `block_hoists` collects the immutable
   temps (hoisted + captured by value) and leaves `Ref`s as shared vars (captured
   by reference). Plus the two scope clauses below (dominance + no shadowing).
   This is precisely the statement a lowering-correctness proof discharges: the
   generated Go denotes the same as the model.

   **Scoping-correctness obligation** for the CFG lowering: every variable's
   declaration must *dominate* all its uses (and not be jumped over). With
   unique names (Rocq alpha-renames — one decl per name) this is a clean,
   provable dominance condition (referenced-points ⊆ in-scope-points).
   Structured lowering gets it by construction (de Bruijn = scope; continuations
   pushed into branches with `ast_lift`). The CFG needs an explicit
   **variable-placement** pass: hoist each cross-block/loop-carried var's
   `var x T` to the dominator of its uses and assign with `=` (avoids `:=`
   re-declaration on loop re-entry and Go's goto-over-declaration rule).
   `ref_set` already emits `=`, not `:=`.
   *Block scope is a gate, not a transform (for the structurer):* introduce a
   structured block scope (if/for body) only when every variable defined inside
   is used **only** inside — no outer access. A variable whose live range
   *crosses* the block boundary cannot be block-scoped, and **hoisting it to the
   enclosing scope is not a fix**: a `:=` inside a block (or once per loop
   iteration) is a *fresh* variable per entry, while an outer `var x T` is one
   *shared* cell — and the difference is observable under closure capture
   (goroutine/`defer`) or address-of (Go's loop-variable semantics). So when a
   variable crosses the boundary, lower that region as `goto` — the complete
   fallback, which loses nothing, just stays un-prettified. When variables nest
   cleanly, structure it: `Count_demo` now lifts to a `for { … break }`. (The
   loop temp `iv` is still hoisted to a function-level `var iv` and assigned with
   `=` — correct, since it dominates and is rewritten before each read; sinking
   it to a loop-local `iv := i` inside the `for` body is a pending idiomatic
   tidy, not a correctness gap.)
   *Capture is handled:* a `defer`/`go` closure inside a loop block captures the
   hoisted temps **by value** — `kw func(iv T){ body }(iv)` — so each closure
   fixes its iteration's value (verified: `defer` in a goto-loop prints 2,1,0,
   not 2,2,2). This is the goto form of Go's loop-variable capture; the
   structured `for` lowering gets it free on Go 1.22+. *Residual:* taking the
   *address* of a hoisted temp (`&iv`) across iterations would still alias the
   shared cell — rare, not yet handled. (The closures currently pass *all*
   hoisted temps; refining to only-captured via free-var analysis is a tidy.)
   **No shadowing (by design).** Go permits shadowing — `i := …` nested inside
   `i := …` is a *distinct* variable with its own memory — but we never emit it:
   Rocq alpha-renames binders to unique names, so each name is exactly one
   variable. This loses no completeness (shadowing is alpha-equivalent to
   unique-naming; we generate the unique-name form of any behaviour) and is
   precisely what keeps "declaration dominates use" unambiguous. Shadowing only
   resurfaces when *importing* existing Go (alpha-rename on import) — a deferred
   libraries-frontier concern, never a generation one.
8. **Minor** — `map_empty` is a likely-nil map; `map_set` on it would panic
   (use `map_make`/`map_make_typed`, which are non-nil). Raw `send`/`close_chan`
   panic on closed/nil channels — sessions are the safe layer; the raw forms
   are labelled escape hatches.

Pedantic-review findings (2026-06-14), separating *theorem* (machine-checked)
from *axiom* (assumed) from *tested* (golden) from *asserted* (prose):

9. **`run_io` totality collapsed the semantic layer** — *FIXED*. The old
   `run_io : IO A -> World -> A * World` was **total**, so the law "panic
   satisfies every postcondition" (`hoare_panic`) could only be satisfied by
   making `World` empty.  Machine-checked: from `hoare_panic` one proves
   `World -> False`, hence (via `run_io_inj`, whose hypothesis becomes vacuous)
   *every* `m m' : IO A` are equal — `println [any 1] = println [any 2]` was a
   theorem — and *every* Hoare triple was vacuously true.  Not *inconsistent*
   (model `World:=∅, IO A:=unit`), but **degenerate**: the denotational layer
   that justifies the lowering certified nothing.  Pure-data theorems (overflow,
   `dual_*`, signed-int) were unaffected (they never touch `World`).  *Fix:*
   `run_io` now returns an **`Outcome A = ORet A World | OPanic GoAny World`**;
   `bind`/`catch`/`panic` get outcome-aware `run_*` axioms; `hoare` is partial
   correctness over the *normal* (`ORet`) outcome (panic ⇒ `True`, honestly,
   *not* `False`).  `World` is no longer collapsible (non-degenerate model:
   `World:=unit`, `IO A:=World->Outcome A`), and `bind_panic_l`, `catch_ret`,
   `catch_panic`, **`hoare_panic`** are now *proved lemmas*, not axioms.
   Divergence stays idealised away (total `run_io` ⇒ all IO terminates), like
   OOM — documented, not modelled.
10. **The Rocq→Go translator is unverified and in the TCB** — *open, structural*.
   "Formally verified Go" = *Go emitted by an unverified ~1500-line OCaml
   pretty-printer (`plugin/go.ml`, incl. the relooper) from Rocq terms checked
   against the axioms.*  The theorems constrain the **Rocq term**; no
   lowering-correctness theorem relates the emitted **Go** to it (this doc
   repeatedly says "precisely what a lowering-correctness proof discharges" — no
   such proof exists).  The relooper is justified only by **golden tests**, which
   exercise finitely many fixed trajectories and cannot witness a CFG-shape bug
   that does not surface on the chosen inputs.  A real fix needs a Go semantics
   in Rocq + a simulation proof — out of scope for now; stated here so the
   guarantee is not overclaimed.  *Down-payment:* keep the model honest and the
   raw-goto fallback total, so the unverified surface is the *prettifier*, not
   the *meaning*.
11. **Session types enforce ordering, not linearity** — *FIXED via indexed
   monad*.  The old CPS API `sess_send : SessEndpoint (PSend A P) -> A ->
   (SessEndpoint P -> IO B) -> IO B` left the *original* endpoint in scope in the
   continuation; Rocq is not substructural, so a **double-send** (or silent
   abandonment) type-checked — machine-checked with a `fido_double_send` that
   compiled.  Ordering/direction/payload *were* enforced; exactly-once use was
   not.  *Fix:* a **parameterised (indexed) session monad** `Sess (i j : Proto)
   A` carrying the protocol state in the *type index*, not in a reusable value:
   `sess_send : A -> Sess (PSend A P) P unit`, `sess_recv : tag -> Sess
   (PRecv A P) P A`, `sess_bind : Sess i j A -> (A -> Sess j k B) -> Sess i k B`.
   There is no endpoint value to reuse, and a runnable session must thread from
   the full protocol to `PEnd`, so double-use and mid-protocol drop are now
   **type errors** (build-checked `Fail` tests).  The plugin lowers the indexed
   monad to channel-passing Go (`run_session` → `make(chan any)` + spawn server +
   run client; `ssend`/`srecv` on the implicit `_sess_ch`); behaviour is
   unchanged (sessions still print 42).  *Tidy left:* the old plugin session
   lowering (`make_sess`, `sess_send`, …) is now dead code — the `named
   "sess_send"` recognizers match nothing since those axioms are gone — harmless,
   pending removal.

Verification methodology used for #9/#11 (kept honest, not just asserted):
`Print Assumptions` to read each result's exact axiom base, plus adversarial
"this must now FAIL to compile" lemmas. Confirmed: the `World -> False` attack no
longer type-checks; `hoare_panic` depends only on `{run_io, run_panic, World}`;
`bind_panic_l`/`with_defer_panic` add `{run_bind, run_io_inj(, run_catch)}`; and
`add_no_overflow_exact` depends on **none** of the IO/session axioms (only Coq's
primitive-integer kernel axioms), so the overflow result is independent of the
whole Go-axiom trust base. The `Fail`-test build gate proves the negative cases
(e.g. `bad_double_send`) genuinely do not type-check.

## Correctness debt — MUST close before module import

A library inherits every subtlety of the primitives it is built on, so each item
below has to be *correct*, not just present, before we type any imported package.
"Punt until later" is fine — but it lives here, tracked, until closed.  Audited
2026-06-14 against the actual code (not from memory).  Ordered by how foundational
the gap is.  Tiers 1–3 are **modelled-but-wrong / ungrounded** (real *now*); tiers
4–5 are **unmodelled** (fine under small-scope until a program/library uses them).

### Tier 1 — the model itself is incomplete or ungrounded
1. **Concurrency has no denotational model.**  `run_io` has equations for
   `ret`/`bind`/`panic`/`catch` ONLY — there is no `run_io` for `send`/`recv`/
   `close`/`go_spawn`/sessions.  The channel laws (`send_recv`, `send_recv_ok`,
   `send_closed_panics`, `double_close_panics`) are free-standing equational
   axioms asserted on bind-sequencing intuition, NOT derived from a semantics.
   Consequences: the Hoare logic cannot reason about channels at all; goroutine
   interleaving is absent; race-freedom and deadlock-freedom are unstated; and
   the channel laws' consistency with `run_io` is unverified.  *Fix:* a concurrent
   denotational model — a world carrying heap + channel state + a **happens-before
   relation** (per go.dev/ref/mem) — give `send`/`recv`/`go_spawn` real `run_io`
   equations, and DERIVE the channel laws instead of asserting them.  This is the
   substrate the entire concurrency thesis rests on; it is the single biggest gap.
2. **Joint consistency of the ~70 axioms is unproven.**  The pure-IO fragment has
   a model (`World:=unit`, `IO A:=World->Outcome A`), but the channel / session /
   map / slice / `zero_val` axioms are not shown consistent with it.  If the set
   is inconsistent, every theorem is vacuous.  *Fix:* exhibit one model that
   validates all axioms at once (or, better, replace axioms with definitions where
   possible so consistency is by construction).
3. **Lowering correctness is unproven (the plugin is trusted).**  ~1500 lines of
   OCaml (incl. the relooper) translate Rocq→Go with NO theorem relating the
   emitted Go to the source term; golden tests cover only finitely many
   trajectories.  (See Known gaps #10.)  *Fix:* an operational semantics for the
   Go fragment in Rocq + a simulation/refinement proof — start with straight-line
   IO, then control flow, then channels.

### Tier 2 — numeric correctness within the int/float parameters
4. **`int` is ±2⁶², not full int64.**  One bit short of the int64 parameter; the
   wrap boundary differs from Go's.  Earlier accepted, but strictly incorrect for
   int64.  (Known gaps #2.)  *Fix:* a full-width model (Z-based, or a paired
   63-bit representation) so the range and overflow point match int64 exactly.
5. **Arithmetic is not overflow-safe by construction.**  `add`/`sub`/`mul` emit
   `+`/`-`/`*` that silently wrap; overflow is *provable* (`add_no_overflow_exact`)
   but not *enforced* — the inverse of the safe-by-construction discipline, which
   wants a proof-carrying `add`/`sub`/`mul` (no-overflow precondition) as the
   DEFAULT and raw wrap as a labelled opt-in.  `div_nz`/`mod_nz` already show the
   shape.  *Fix:* guarded `add_nz`/`sub_nz`/`mul_nz` (proof the exact result is in
   range) and/or a checked form; keep raw `add` as the opt-in wrap.
6. **Untyped constants modelled wrong.**  Literals are modelled as already-typed
   fixed-width/IEEE values; Go's *untyped* constants are arbitrary precision and
   acquire a type (with a representability check) only at use.  So `const 0.1+0.2`
   should be `0.3` (we give the runtime `0.30000000000000004`), large int
   constants (`1<<70`) are unrepresentable in 63-bit `int`, and constant overflow
   is a compile error not a wrap.  (Known gaps #5.)  *Fix:* untyped int constants
   as `Z`, untyped float as exact rationals; type + representability proof at use.

### Tier 3 — modelled types that are faithful only in a sub-regime
7. **Strings conflate byte and rune indexing.**  `GoString := list GoRune` maps to
   Go `string`, but Go `s[i]` yields a *byte* and `len(s)` is the *byte* count,
   while `range s` yields runes.  The list-of-rune model is the rune view only;
   byte-level indexing/len would be wrong, and no string ops (index, len, concat,
   slice, `string`↔`[]byte`/`[]rune`) are modelled.  *Fix:* model strings as byte
   sequences with a rune-decoding view (or restrict to the rune view and forbid
   byte indexing), then add the operations.
8. **Reference-type aliasing (maps, slices).**  Maps and slices are Go reference
   types; the functional model (`append`→new list, map-as-value) is correct ONLY
   for single-goroutine, non-aliasing use.  Sub-slicing (`s[a:b]` shares the
   backing array), append-may-mutate-in-place, and any aliased or concurrent
   access are not modelled.  *Fix:* move mutating ops fully into `IO` under an
   ownership/aliasing discipline (ties to Tier 1's concurrency model).
9. **Operator coverage is partial.**  Only `==`, `<`, `<=` are emitted; `>`, `>=`,
   `!=`, `&&`, `||` are not in the op tables (must currently be encoded via
   swapped operands / negation).  *Fix:* add them and verify faithfulness — in
   particular that `&&`/`||` short-circuit is unobservable here (true only while
   operands are pure; revisit if a bool operand can have effects).

### Tier 4 — unmodelled operations on (some) modelled types
10. **Narrow integer types** (`int8/16/32`, `uint`, `uint8/16/32/64`): opaque
    axioms with no arithmetic and no overflow semantics — and unsigned wrap
    differs from signed.  Needed before any library does sized/unsigned math.
11. **Float gaps:** `float32` is an opaque axiom (no native Rocq f32); float
    comparison (`<`/`<=`/`==`, and NaN's unordered behaviour) is not emitted; and
    int↔float / float↔float conversions are absent.
12. **Bit operations** (`<<`, `>>`, `&`, `|`, `^`, `&^`, including negative-shift /
    over-width-shift behaviour) — entirely unmodelled.
13. **Conversions** in general: int↔float, integer narrowing (truncation/wrap),
    `string`↔`[]byte`/`[]rune`, interface conversions beyond `type_assert`.

### Tier 5 — semantic edge cases
14. **Divergence / non-termination.**  `run_io` is total, so the model assumes
    every computation terminates; infinite loops and deadlocks have no denotation.
    Liveness and deadlock-freedom proofs need a model that admits non-termination
    (step-indexed or coinductive).  (Tied to Tier 1.)
15. **Goroutine panic semantics.**  An unrecovered panic in ANY goroutine crashes
    the whole program, and `main`'s `recover` cannot catch another goroutine's
    panic — the current single-thread `catch`/`panic` model does not capture this
    cross-goroutine crash.
16. **nil / closed edges, uniformly.**  nil-channel send/recv blocks forever;
    `close(nil)`, double-close, and send-on-closed panic; `map_set` on a nil
    (`map_empty`) map panics.  Some are axiomatised, some only made safe by a
    higher layer (sessions), some are raw escape hatches — the enforcement story
    should be uniform and each unsafe raw form clearly labelled.

## Architecture

- `*.v` and `*.go` are both committed; `*.go` is always re-derivable from `*.v`
- `plugin/go.ml` + `plugin/g_go_extraction.mlg` — the Rocq→Go extraction plugin
- `builtins.v` — Go builtins (always in scope, loaded via `preamble.v`)
- `preamble.v` — shared preamble; every theory starts with `From Fido Require Import preamble`
- `dune` / `dune-project` — builds plugin + theories together inside Docker
- Pre-commit hook (`.githooks/pre-commit`; activate once via `make
  install-hooks`): when any `.v` or `plugin/` file is staged, it re-extracts
  and auto-stages the generated Go, so committed `*.go` can never drift from
  prover output (a broken proof aborts the commit); also enforces gofmt. Still
  the anti-tampering gate — fresh prover output always overwrites `*.go`.

## Key commands

```
make build        # full Docker build → static binary
make run          # run the image
make extract      # pull generated Go into the repo
make run-local    # extract + go run (no Docker)
make check        # golden check: run program, diff output vs expected_output.txt
make golden       # update expected_output.txt after an intended behaviour change
make install-hooks  # activate pre-commit hook (run once after clone)
```

`expected_output.txt` is the golden runtime output — a cheap end-to-end check
that a Rocq/plugin change did not alter observable behaviour *anywhere*. After
an intended behaviour change, `make golden` and commit the new baseline.
