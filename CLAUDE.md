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
   IIFE. This stage also adds precedence/associativity to the expression
   printer: today `pp_atom` parenthesises conservatively (correct but noisy);
   clean nested arithmetic/boolean output needs real operator levels. Trickier
   than (a) — hence second.
8. **`select`** — non-deterministic choice between ready channels. Needed for
   services/multiplexing/timeouts. Significantly harder semantics than linear
   send/recv; wants control flow (each case is a branch) in place first.

## Known gaps

Audit (2026-06-13 sweep) of the partial/unsafe primitives against the
safe-by-construction principle. Tracked until closed.

1. **Integer div/mod by zero** — *neutralised, real fix pending*. Rocq's
   `Uint63`/`nat` division is total (`x/0 = 0`), Go's panics, and the plugin
   used to emit a raw `/` — silently unsound. The plugin no longer emits
   integer `/` or `%`, so the path can't be reached (any use extracts to an
   undefined identifier). Proper fix: a guarded `div` (proof `d <> 0`, or a
   checked form). Float `/` is kept — IEEE, no panic.
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
   *Status:* CFG IR (`run_blocks`/`Jump`/`Done`) and raw labels+goto are done;
   the structuring pass has its **first pattern** — `as_while_loop` lifts a
   two-block reducible loop (header jumps only to itself or the single exit) to
   `for { … break }` with no labels/goto (`Count_demo`, `Defer_loop_demo`).
   The emitter is parameterised by a *terminator handler* (`raw_term` →
   `goto`/`return`; `loop_term h x` → fall-through/`break`), so one `emit_block`
   prints raw or structured form; non-matching CFGs (`Cond_goto_demo`) stay raw
   goto. Golden-guarded: structuring changes the generated source, never the
   behaviour. Next patterns: forward if-diamond (`cond_goto`), then general
   reducible reloop.

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
