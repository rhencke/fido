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
  *First demonstrated (2026-06-15, `typestate_demo` in main.v):* a value carries
  its FSM state in a PHANTOM type index (`Light c`, `c : LightColor` in **`Prop`**
  so extraction erases it — `Light CRed` and `Light CGreen` stay DISTINCT types yet
  both lower to one `type Light struct`). Each transition's type names the legal
  from/to states (`go_green : Light CRed -> Light CGreen`), so an illegal transition
  is a Rocq TYPE ERROR — build-gated by `Fail Definition bad_double_green` /
  `bad_red_on_fresh`. At runtime it is a plain struct + value-receiver methods (the
  index is compile-time only), so the emitted Go is ALWAYS a legal trace. This is
  the "an FSM can't compile to a broken transition" property, concretely. *Still
  open:* the index must be `Prop` AND the record needs ≥2 fields (Coq unboxes a
  1-field record); generalising to single-field/`Type`-indexed handles needs the
  phantom-index erasure + curried-return work tracked under ladder 9c.
- **Representation invariants** — a struct invariant (sorted, balanced, indices
  in range) preserved by every method.
  *First demonstrated (2026-06-15, `repinv_demo` in main.v):* a struct carries a
  PROOF of its invariant as an ERASED (`Prop`) field, so the SMART CONSTRUCTOR
  demands the invariant and an out-of-invariant value is unrepresentable. `Sorted2`
  bundles two ints with a proof `Sint63.leb s_a s_b = true`; the proof field erases,
  so it lowers to a plain `struct { S_a, S_b int64 }` (zero runtime cost) yet the
  invariant is usable — `max_of` returns `s_b` as the maximum with NO runtime
  comparison, justified by the proof (`max_ge_min` machine-checks
  `leb (min_of p) (max_of p) = true`). Build-gated negative: `bad_unsorted`
  (`MkSorted2 7 3 eq_refl`) does not type-check. Same erased-`Prop` mechanism as
  typestate, but the index is a *proof about the fields* rather than a phantom state.
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
   `GoSlice`, `GoString`, `GoMap`, `type_assert`, plus the import-free predeclared
   set: `len`/`cap`/`append`/`delete`/`close`/`recover`, `make` (chan/map/slice
   `make([]T,n)`), and Go 1.21 `min`/`max`/`clear`. Add to `builtins.v` + plugin
   match.  *Deferred (non-import prereqs):* `new` (pointers), `copy`/slice-`clear`/
   `make([]T,len,cap)` (slice-aliasing model), `complex`/`real`/`imag` (no complex
   type).
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
   - **Inline-`if` continuation duplication — *fixed for the discard case*.**
     `bind (if c then a else b) k` used to emit `k` *inside both arms*, so N
     chained inline `if`s in one `bind` blew up **exponentially** (2^(N-1) copies
     of the tail). Now, when `k` **discards** the matched result (`fun _ => rest`,
     bound var unused — the overwhelmingly common sequential-effects case), the
     arms are emitted with no continuation and `rest` is emitted **once** after
     the `if`/`else` (both arms fall through to it). `Inline_if_demo` (three
     chained inline `if`s) lowers to three flat sequential `if/else`s, golden-
     locked. *Still threaded (duplicated) when the result is USED* — that needs
     the "hoist the result into a `var`" path (`var x T; if c { … x = v0 } else
     { … x = v1 }; rest`), which requires the arm's value type; deferred, and rare
     (a value-producing `if` whose result feeds the continuation). The detection
     is `db1_free` of the continuation body (de Bruijn index 1 unused).

   **b. Expressions second** — `MLcase` in value position. Go has no
   conditional expression, so pure `if`/`match` lowers via hoisting or an
   IIFE. *(Still pending — no demo triggers a value-position match yet. But it
   is no longer a SILENT hole: a value-position match now **fails loudly at
   extraction** via `unsupported` — see "Fail-loud policy" below — rather than
   emitting a plausible-but-wrong `nil`.  So the gap is honest, not a footgun.)*
   **Boolean operators are done**: `andb`/`orb`/`negb` lower to Go's `&&`/`||`/`!`
   (`Bool_op_demo`).  Faithful because the operands are pure, total `bool` values
   (no effects, no divergence), so Go's short-circuit evaluation is
   observationally identical to Coq's strict `andb`/`orb`.  Precedence: `||` = 1,
   `&&` = 2 (in `binop_of`), so `(a || b) && c` parenthesises the looser `||`;
   `negb` is unary (`!`, binds tighter than any binary op).  The dead standalone
   `andb`/`orb`/`negb` definitions are suppressed in `is_inlined_ref` (every use
   is inlined at the call site).
   The **operator-precedence printer (parens) is done**: `binop_of` gives each
   inlined arithmetic/comparison op a Go precedence (`* / %` = 5, `+ -` = 4,
   comparisons = 3), and `pp_prec ctx e` parenthesises a sub-operand only when its
   operator binds looser than the context requires — instead of `pp_atom`'s
   conservative "parenthesise every non-atom".  `Prec_demo` shows `a*b + c` (no
   parens) and `(a+b) * c` (parens only where needed).  **gofmt SPACING is solved
   by canonicalising on extract:** `make extract` runs `gofmt -w` on the output,
   so the plugin emits valid Go and gofmt tightens the operator spacing (`a * b`
   → `a*b`) — its depth/operand heuristic is not worth replicating in the plugin.
   gofmt does not touch parens, so the printer still owns those.  (The pre-commit
   hook also now runs `gofmt -l` via Docker when the host lacks it, instead of
   silently skipping — a missing host `gofmt` had let non-canonical output
   through.)
8. **`select`** — non-deterministic choice between ready channels. *Lowering done*
   (`select_recv2` = two recv cases; `select_recv_default` = recv + `default`, the
   non-blocking form) → faithful Go `select { case x := <-ch: … }`, CPS like
   `recv_ok`. `select_demo` prints 42 (ready case), `select_default_demo` prints 99
   (default); golden-locked. *Frontier:* the denotational CHOICE semantics (which
   ready case runs, pseudo-random fairness, blocking when none ready) is idealised
   away like `recv`'s blocking (Tier 5 #14, needs the scheduler/non-terminating
   model); and send-cases / N-ary (>2) cases are the same lowering with more arms.
9. **Structs / methods / interfaces** — the gateway to the closed-world wishlist
   (typestate, representation invariants, behavioral satisfaction, and the
   prerequisite for typing libraries). Built in three stages.

   **a. Structs (value-structs from Rocq Records)** — *done*. A Rocq `Record` is a
   single-constructor inductive with projections and value/copy semantics — exactly
   a Go value-`struct`. The plugin gathers each record's projections + constructor
   in a `collect_records` pre-pass (so uses anywhere lower correctly), then: the
   type → `type T struct { Field Type … }` (`Dind`'s `Record` arm, fields via the
   general `pp_type`, so not hardcoded — `int`→`int64`, `bool`→`bool`); the
   constructor → a struct literal `T{…}` (`MLcons` when `is_record_ctor`); each
   projection → field access `x.Field` (`MLglob` app when `is_record_proj`); the
   projection *definitions* are suppressed. The numint-wrapper records (`GoU8`…)
   are excluded by an `is_numint_typename` guard so they keep their int64-erasure.
   Struct invariants are provable in Rocq directly (`point_proj_px`:
   `px (MkPoint a b) = a` by `reflexivity`). Demos: `point_demo`
   (`Point{3,4}` → `3/4/7`), `labeled_demo` (mixed `Flag bool`/`Qty int64` →
   `true/5`); golden-locked. *Not yet:* embedded fields/promotion, struct tags,
   field-wise `==`.

   **b. Methods (value receiver)** — *done*. A top-level function whose FIRST
   visible parameter is a record (struct) is lowered as a Go value-receiver method:
   the decl → `func (recv T) M(rest…) ret { … }` (`pp_function` pulls the first
   param out as the receiver; the body keeps the SAME de Bruijn env, only the
   signature changes), and a call `m recv a…` → `recv.M(a…)` (the call-site arm in
   `pp_expr`, before the general-call fallback). Detection is type-directed
   (`first_param_type` is a registered `record_typename`), so it is automatic and
   faithful — `recv.M(a)` denotes the same as `M(recv, a)` — and idiomatic;
   projections and inlined refs are excluded. Both pure and IO-returning methods
   work (`describe` → `func (p Point) Describe() { … }` through `pp_io_body`).
   Method behaviour is provable in Rocq (`shifted_px`: `px (shifted p d) =
   add (px p) d` by `reflexivity`). Demos: `method_demo` (`Sum_coords`/`Shifted`
   → `7/13/14/27`), `io_method_demo` (`p.Describe()` → `8/9`). The method↔type
   association (the method SET of `T` = every such function) is what (c) checks.
   *Not yet:* pointer receivers (need the pointer/aliasing model), method values /
   expressions (`recv.M` as a first-class closure, `T.M`), method-name namespacing
   via Rocq `Module`s (so two types can share a basename like `Area`).

   **c. Interfaces (dictionary model)** — *≥2-method done; 1-method (unboxed) pending*.
   An interface is modelled as a Rocq `Record` whose fields are the methods, each a
   closure ALREADY CLOSED OVER the underlying value — so the concrete type is hidden
   inside the closures, which is exactly Go's "method dictionary, existential at
   runtime" ([[go-interfaces-as-dictionaries]]). It lowers to a Go struct of function
   fields (a vtable): the type → `type I struct { M func(A) R; … }`; constructing
   the dictionary → a struct literal of TYPED closures (`pp_typed_closure` uses the
   field types from `record_ctor_ftypes`, so a method entry is `func(s int64) int64`,
   not the generic `func(any) any`); the concrete value is captured by the closures
   (existential — a `Shape` can't be turned back into the rect it came from); a method
   call `m d a…` → dynamic dispatch `d.M(a…)` (the projection-application arm). The
   projection defs are suppressed. Satisfaction is checked in Rocq — building the
   dictionary DEMANDS real `int -> int` methods — and dispatch is provable
   (`dispatch_area`: `area (mk_rect w h) s = …` by `reflexivity`). Demo: `Shape`
   with `Area`/`Perim`, two carriers (`mk_rect`/`mk_square`), `show_shape` dispatching
   `sh.Area(0)`/`sh.Perim(1000)` → `14/1007/20/1010`; golden-locked.
   *Pending:* a SINGLE-method interface — Coq UNBOXES a one-field record (`{m}` ≡ `m`),
   so it erases to a bare function and the lowering must emit a curried-return
   (`func F(p T) func(A)R { return func(a A)R{…} }`) instead of leaking the inner
   lambda into `F`'s params; tracked. Also pending: nullary (unit-thunk) methods
   (need unit-arg erasure), and a true Go `interface{…}` keyword form (the vtable
   struct is the same semantics — Go's interface IS a vtable + erased value).
   This is the gateway to typestate / "an FSM can't compile to a broken transition"
   and behavioral-satisfaction proofs.

## Known gaps

Audit (2026-06-13 sweep) of the partial/unsafe primitives against the
safe-by-construction principle. Tracked until closed.

**Fail-loud policy (the meta-invariant).** No unmodeled construct may extract to
plausible-but-wrong Go. The plugin's `unsupported what` helper raises a
`CErrors.user_err` (aborting `make extract`) for every case it cannot lower —
the catch-all in `pp_expr`/`pp_atom`, an unhandled `MLcase` shape in statement
position, a non-literal `print`/`println` arg list, an unmodeled constructor
(`MLcons` that is not nat/bool/list), and a `map_get_opt` result not immediately
matched. Previously these emitted `nil /* TODO */` / `panic("unhandled match")`,
which *compiles and runs wrong* — the one thing the project forbids. Now an
unmodeled construct either gets implemented or gets suppressed in
`is_inlined_ref` (if the offending definition is dead, as the `andb`/`negb`
bodies were); it is never papered over. Verified: a value-position match probe
aborts extraction with `fido: cannot extract this expression …`. This is what
makes every "still pending" gap below *honest* rather than a silent footgun.

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
   **Coq `nat` (≠ `int`) is mapped to Go `uint`**, used mainly for compile-time
   indices (e.g. `run_blocks` block labels); runtime integer math is `int`
   (Sint63). `Nat.add`/`mul`/`eqb`/`ltb`/`leb` lower to the Go operators and are
   faithful within the representable range (a `nat ≥ 2^64` is unrepresentable in
   `uint` either way). But **`Nat.sub` is excluded** (`classify_nat_op`): Coq's
   `Nat.sub` is *truncated monus* (`3 - 5 = 0`) while Go `uint` `-` *wraps*
   (`3 - 5 = 2^64-2`) — they disagree even on small values, so it would be
   silently wrong. Using it now **fails loud** (`unsupported`), like the omitted
   `Nat.div`/`mod`/`pred`. *Open:* a `b <= a`-guarded monus (`a - b` exact when no
   truncation) or an `if a>=b` form, mirroring `div_nz`. `PrimInt63.sub` (the
   `int` path, two's-complement) is faithful and unaffected.
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
1. **Concurrency denotational model — *Phase 1 done (channel state); HB partial
   order + cross-goroutine pending*.**  The channel laws are no longer
   free-standing axioms asserted on bind-sequencing intuition: `send`/`recv`/
   `recv_ok`/`close` now have real `run_io` equations over CHANNEL STATE in the
   world — a per-channel FIFO `chan_buf` + a `chan_closed` flag, with updates
   `chan_send_upd`/`chan_recv_upd`/`chan_close_upd` and heap-interface laws, the
   exact shape of the map heap model (a standard FIFO+flag, hence satisfiable /
   consistent).  `send_recv`, `send_recv_ok`, `send_closed_panics`,
   `double_close_panics` are now **THEOREMS** derived from that interface
   (properly conditioned — `send_recv` needs the channel open AND the buffer
   empty, the honesty the old unconditional axiom hid), and `recv_ok_closed_empty`
   (receive-from-closed-empty → `(zero,false)`) is now stateable (it was
   inconsistent as an unconditional axiom).  Blocking is idealised away like
   divergence: a `recv` equation is given only for a non-empty buffer (or a closed
   channel); recv on a permanently-empty open channel is a deadlock, no
   denotation.  **Phase 2 done — the happens-before partial order** (per
   go.dev/ref/mem) is now modelled, AXIOM-FREE (`Print Assumptions hb_irrefl` =
   *Closed under the global context*).  Events are the start/completion of the
   n-th send / n-th receive on a capacity-`cap` channel (`ChEvent`); `hb cap` is
   the transitive closure of exactly the real edges — program order + "send ⤳
   corresponding receive completes" (`hbe_send_recv`) + "kth receive ⤳ (k+cap)th
   send completes" (`hbe_recv_send`; `cap = 0` is the unbuffered rendezvous,
   which needs the start/completion distinction not to cycle).  It is a proven
   STRICT PARTIAL ORDER: irreflexive via a concrete timestamp `ev_ts` that is a
   linear extension of every edge (`hb_ts_increasing`), transitive by
   construction.  Crucially it adds NO spurious order — `ev_credit` (a receive at
   `k` authorises sends to `k+cap`) is weakly monotone along `hb`, proving
   concurrent events stay unordered (`buffered_sender_runs_ahead`:
   `~ hb 2 (RecvStart 0) (SendDone 1)`), which is what keeps it sound for race
   freedom.  **Phase 3 done — data races are now DEFINED and the channel guarantee
   is PROVEN, axiom-free** (`Print Assumptions mp_no_race` = *Closed under the
   global context*).  A `data_race hb acc e1 e2` is conflicting accesses (`conflict`
   = same location, ≥1 write) UNORDERED by `hb`; the generic `hb_ordered_no_race`
   proves happens-before ordering is the whole defence.  The canonical
   message-passing instance (`mp_hb`: A writes `x` then sends; B receives then
   reads `x`) shows the write/read pair `mp_conflict`-s yet is `hb`-ordered through
   the `mp_sync` (= `hbe_send_recv`) edge — `mp_no_race`: it does NOT race.  **Phase 4a
   adds the 4th go-mem channel rule** (close⤳receive-returning-zero): the finite
   model `hbc cap nsent` (sender sends `nsent` then closes), `hbc_close_before_zero_
   recv` orders close ⤳ `CRecvDone n` for `n ≥ nsent` ONLY — `close_not_before_value_
   recv` proves it does NOT order close before the value-receives (via the conserved
   `ev_credit_c`, so no over-ordering; irreflexive via `ev_ts_c`).  **Phase 4b adds
   the goroutine FORK edge** (`fork_hb` + `fork_program_race_free`: parent writes `x`,
   spawns a child reading `x` with no channel — race-free by the fork edge alone).
   Both axiom-free.  **Phase 5 (`concurrency.v`) ties happens-before to ACTUAL
   EXECUTION TRACES** — a list of events from interleaving goroutines, synchronisation
   recorded by BACK-POINTERS (a receive carries its matched send's trace position; a
   goroutine's first step carries its spawn position).  `hbt_irrefl` (axiom-free): for
   ANY well-formed trace, happens-before is a strict partial order, because the TRACE
   POSITION is a linear extension (`hbt_forward` — no synchronising with the future).
   This GENERALISES the bespoke `ev_ts` to arbitrary executions and ANY topology (no
   longer one-sender/one-receiver); race freedom generic (`trace_ordered_no_race`) +
   concrete (`mp_trace_race_free`).  **Phase 6 (same file) — well-formed traces are
   GENERATED, not assumed:** a concurrent small-step operational semantics (`step`: a
   DYNAMIC goroutine pool over FIFO channels — spawn via `PSpawn`/`cfg_live`, only
   spawned goroutines run; each step appends an event, a send records its trace
   position in the channel buffer, a receive pulls the front as its back-pointer),
   with invariant `BufOk` preserved by every step
   (`step_preserves_inv`).  So `reachable_wf`: EVERY reachable trace is well-formed —
   `WfTrace` is now a THEOREM about execution; and `reachable_hb_strict`: the
   happens-before of ANY real execution is a strict partial order, EARNED by running.
   All axiom-free.  *Still pending:* tie this calculus (`PAct`/`step`) to the actual
   `run_io`/`World` IO model (extracted IO programs realise it); the FIFO refinement
   (kth recv ↔ kth send); deadlock-freedom (liveness, needs a non-terminating/
   scheduler model — Tier 5 #14).  Net: Phase 1 grounds the channel
   laws, Phase 2 the ordering, Phase 3 the race-freedom guarantee — all three
   axiom-free or interface-grounded, replacing the old asserted-on-intuition
   axioms.
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
5. **Overflow-safe arithmetic — DONE (the guarded forms now exist).**
   `add_nz`/`sub_nz`/`mul_nz` are evidence-carrying: each demands a proof that the
   exact result is in range (`no_overflow_{add,sub,mul}`, discharged by `now
   vm_compute` for concrete operands), then extracts to the raw machine op — which
   the proof has shown does not wrap, so the result equals the exact value
   (`{add,sub,mul}_no_overflow_exact` theorems, machine-checked).  Raw `add`/`sub`/
   `mul` (and `PrimInt63.*`) remain the opt-in WRAPPING forms — same shape as
   `div_nz` vs the raw divide.  `overflow_safe_demo` prints `3000000000000
   1000000` (proven no wrap).  *Open:* a runtime check-and-branch (comma-ok) form
   for operands whose range is only known at runtime; and a *boolean*-guard
   variant so the obligation discharges by `eq_refl` like `div_nz`.
6. **Untyped constants modelled wrong.**  Literals are modelled as already-typed
   fixed-width/IEEE values; Go's *untyped* constants are arbitrary precision and
   acquire a type (with a representability check) only at use.  So `const 0.1+0.2`
   should be `0.3` (we give the runtime `0.30000000000000004`), large int
   constants (`1<<70`) are unrepresentable in 63-bit `int`, and constant overflow
   is a compile error not a wrap.  (Known gaps #5.)  *Fix:* untyped int constants
   as `Z`, untyped float as exact rationals; type + representability proof at use.

### Tier 3 — modelled types that are faithful only in a sub-regime
7. **Strings — byte model DONE; rune view deferred.**  `GoString := string` (Coq's
   `Strings.String`, a genuine **byte** sequence) → Go `string`, replacing the old
   `list GoRune` (the rune view, which mismodelled `s[i]`/`len`).  Now modelled, all
   faithful: `str_len` = **byte** count (→ `int64(len(s))`; `str_len "Go" = 2` is a
   *theorem*), `str_at_ok` = the **safe** byte index (CPS/comma-ok like
   `slice_at_ok` — forces the OOB branch, cannot panic; `s[i]` widened to the int64
   carrier), `str_concat` = Go `+` (a *theorem*: `"Go"+"!" = "Go!"`); a string is
   its own type (`str_no_implicit` `Fail`); literals decode `String`/`Ascii`/
   `EmptyString` → byte-faithful Go string literal (printable verbatim, else
   `\xNN`).  *Deferred (unmodeled, fails loud — NOT silently wrong):* the **rune
   view** (`range s` UTF-8 decode and `string`↔`[]rune`/`[]byte`, Conversions), and
   byte mutation (Go forbids it — strings immutable).
8. **Reference-type state (maps, slices, refs).**
   (b) *get-after-write — FIXED for maps via a heap in the world.*  Map reads are
   now in `IO` (`map_get_opt : ... -> IO (option V)`, `map_get_or`, `map_len`);
   the contents live in the world via an abstract heap interface (`map_sel` /
   `map_upd` / `map_rem` / `map_size`) with `run_io` equations, and the
   get-after-write laws (`map_get_set_same`, `map_get_delete_same`,
   `map_get_set_diff`, `map_get_empty`, `map_get_or_hit/miss`) are now **derived
   THEOREMS**, not a degenerate axiom — `map_set` returns normally, no degeneracy.
   The plugin lowers the IO reads to the same comma-ok Go (golden unchanged).
   **Refs get the same treatment** (`ref_sel`/`ref_upd`/`run_ref_get`/
   `run_ref_set`/`ref_sel_upd_same`), and `ref_get_set_same` (read-after-write)
   is a THEOREM — no extraction change, since `ref_get`/`ref_set` were already IO.
   *Remaining:* the heap interface is still AXIOMATIC (its consistency relies on a
   concrete heap model that is not yet exhibited — ties to #2); extend to slices;
   and `ref_new`/`map_make` allocation semantics (fresh location) are not modelled.
   (a) *aliasing — still open.*  Maps/slices are Go reference types; the model is
   correct only for single-goroutine, non-aliasing use; sub-slicing (`s[a:b]`
   shares the backing array), in-place append, and aliased/concurrent access are
   unmodelled (ties to Tier 1's concurrency model).
9. **Operator coverage — *boolean + float comparison now done; `>`/`>=`/`!=`
   still via encoding*.**  Integer `==`/`<`/`<=` for `int` go through the SIGNED
   primitives `eqb`/`ltsb`/`lesb` (→ Go signed `==`/`<`/`<=`); the user-facing
   `Sint63.ltb`/`leb` reduce to those.  The UNSIGNED `PrimInt63.ltb`/`leb` are
   **excluded** (own `int63_op_names`, no ltb/leb) — they would mis-map to Go's
   signed `<`/`<=` and disagree on high-bit values (`ltb (-1) 0` is `false`
   unsigned, `-1 < 0` is `true` signed), so a raw use now **fails loud** until an
   unsigned-int model exists.  Now also **`&&`/`||`/`!`** (`andb`/`orb`/`negb`)
   and **float `<`/`<=`/`==`** (`PrimFloat.ltb`/`leb`/`eqb`) are emitted.  `&&`/`||`
   short-circuit is unobservable because the operands are pure, total `bool`
   values (no effects, no divergence) — revisit only if a bool operand could ever
   have effects.  Float comparison is faithful on IEEE corner cases, not just
   ordinary values: machine-checked `nan_eqb_false`/`nan_ltb_false` (NaN is
   unordered) plus the `float_nan_demo` golden show Coq and Go agree.  *Still
   open:* `>`/`>=` (encode by swapping operands) and `!=` (encode as
   `negb (eqb …)` → `!(a == b)`) have no *direct* operator — low priority, since
   they are losslessly expressible, but a direct `gtb`/`geb`/`neqb` mapping would
   be tidier.

### Tier 4 — operations to model on the remaining types
**(There is no "acceptably unmodeled" — decided 2026-06-14.  The point of the
builtin layer is that it is *precisely modelled*; until a primitive has faithful
semantics we cannot reason about anything built on it safely.  A type that exists
only as a type tag with no operations is a hole, tracked here until closed, not a
resting state.)**

10. **Narrow integer types** — *`uint8` modelled; the rest pending the same
    template*.  The model: a `uintN` value is an `int` (PrimInt63) kept reduced
    mod 2^N by masking (`land .. (2^N-1)`) after every op — exactly Go's uintN
    wrap.  It is a **Definition, not an axiom** (computable: `vm_compute`
    discharges the wrap; consistency by construction), and the plugin lowers each
    op to int64 with the explicit mask (`u8_add a b` → `((a + b) & 0xff)`),
    observationally identical to Go's `uint8` for the in-range values these ops
    produce.  Done for `uint8`: `u8_lit`/`add`/`sub`/`mul`/`eqb`/`ltb`/`leb`, with
    machine-checked `u8_add_wraps`/`u8_mul_wraps`/`u8_sub_wraps` and the `u8_demo`
    golden (`44 / 1 / 255 / true`; note `u8_sub 0 1 = 255` — uint8 *does* wrap,
    unlike the rejected truncating `Nat.sub`).  **Signed `int8` done too** (proves
    the template handles two's-complement): mask to 8 bits then SIGN-EXTEND
    (`(m ^ 0x80) - 0x80`), comparison via signed `Sint63.ltb`; plugin emits the
    explicit int64 form `((((a + b) & 0xff) ^ 0x80) - 0x80)`.  Machine-checked
    `i8_add_wraps` (`100+50 = -106`), `i8_sub_wraps` (`-128-1 = 127`); `i8_demo`
    golden `-106 / 127 / -100 / true`.  **`uint16`/`int16` AND `uint32`/`int32` done**
    (same template, masks `0xffff` / `0xffffffff`) — add/sub, comparison, bitwise,
    shift, div/mod, conversions, all machine-checked (`spec_u32_add_wrap` 4e9+1e9→
    705032704, `spec_i32_add_wrap` 2e9+2e9→-294967296).  **`div`/`mod` done for every
    width** — evidence-carrying non-zero divisor (`div_nz` pattern; `u8_div_zero`
    `Fail`), signed wraps the `-2^(N-1)/-1` overflow via `norm`.  *Still ✗:*
    **`u32_mul`/`i32_mul`** ((2³²−1)² ≈ 2⁶⁴ > 2⁶² carrier — OMITTED, fails loud, needs
    the wider model), and **`uint64`/`uint`/`int` full width** (64-bit exceeds the
    63-bit carrier — needs the Z-based int model, like `int64`'s ±2⁶² limit).
    *Cosmetic:* `u8_lit`/`i8_lit` of an in-range literal emits the full
    mask/sign-extend expression instead of just the literal — correct, just verbose.
    **TYPE DISTINCTNESS — DONE (airtight, Go spec "Numeric types").**  Each
    `uint8`/`int8`/`uint16`/`int16` is its OWN Rocq type — a single-field record
    `GoU8`/`GoI8`/… `{ u8raw : int }` over the carrier — so Rocq REJECTS mixing a
    `uint8` with an `int` (no implicit conversion; the only implicit path is the
    untyped-constant `u8_lit`, per the spec).  Build-checked by the `*_no_implicit`
    + `u8_u16_no_mix` `Fail` tests.  The wrapper is ERASED in the LOWERING (not by
    a gate): the plugin recognises `GoU<N>`/`GoI<N>` (→ int64), `MkU<N>` and
    `<u|i><N>raw` (→ identity, like `existT`/`any`), so a well-typed distinct-type
    term compiles BY CONSTRUCTION — same int64+mask Go, no wrapper leak.  Principle:
    a *bad program* is unrepresentable in Rocq (type checker + `Fail` tests);
    *uncompilable Go* is prevented by a correct lowering, not caught after the fact.
    *Pending:* wrap `int` itself as a distinct record (tied to the Z-width model);
    explicit numeric CONVERSIONS (`int(x)`, `uint8(y)`) — now load-bearing, since
    distinct types can't mix without them (the Conversions spec section).
11. **Float gaps — *comparison + unary negation now done; float32 + conversions +
    abs/sqrt still open*.**  Float `<`/`<=`/`==` (incl. NaN's unordered behaviour)
    and unary `opp` → `-x` (IEEE sign-flip, makes `-0.0`; machine-checked
    `opp_zero_is_neg` + runtime `float_opp_sign_demo`) are now emitted and proven
    faithful (see #9).  *Still open:* `float32` is an opaque axiom (no native Rocq
    f32); int↔float / float↔float conversions are absent; and `abs`/`sqrt` are
    **deferred** because they need `math.Abs`/`math.Sqrt` — and **package imports
    are on hold by decision until every no-import builtin is locked down perfect**
    (an inline `abs` would mishandle `-0.0`, so it must wait for the real
    `math.Abs`, not a hand-rolled one).
12. **Bit operations.**  *Bitwise `& | ^ &^` and unary `^` (complement): DONE for
    fixed-width `uintN`/`intN`* (`u8_and`/`or`/`xor`/`andnot`/`not`, `i8_*`,
    `u16_*`, `i16_*`; machine-checked `spec_u8_and`…`spec_i8_andnot`; `bitwise_demo`
    prints 48 252 204 / 192 15 / -6 -6).  Faithful: `uintN` results stay in range
    (no mask); `intN` operands are sign-extended so the raw int64 op is correct;
    AND-NOT/complement flip within the width; unary `^x` is wrapped back to the
    width (Go's int64 `^240` is -241, not the uint8 15).  *Still ✗:* bitwise on
    `int` (Sint63) — the 63-vs-64-bit carrier exposes the sign bit, so negative-`int`
    bitwise would differ from int64 (blocked on the Z model, Tier 2 #4).  *Shifts
    `<< >>`: DONE for fixed-width* (`uN_shl`/`shr`, `iN_shl`/`shr`) — EVIDENCE-CARRYING
    like `div_nz` (count proven ≥0, so the negative-count panic is unreachable;
    `u8_shl_neg` `Fail`).  Machine-checked `spec_u8_shl`…`spec_i8_shr_neg`:
    over-width `1<<8=0` (no upper limit), signed `64<<1=-128` (wrap), `>>` arithmetic
    for signed via `PrimInt63.asr` (`-3>>1=-2` toward −∞, NOT `-3/2=-1`; `-1>>3=-1`),
    logical for unsigned via `lsr`.  `shift_demo` prints 8 0 15 / -128 -2.  *`int`
    (Sint63) shifts still ✗* (same carrier issue as `int` bitwise).
13. **Conversions.**  *Integer↔integer among `{int,uint8,int8,uint16,int16}`: DONE.*
    Routed through the `int` carrier — `int_of_FW` widens (value preserved → lowers
    to identity), `FW_of_int` narrows (truncate: `land` for `uintN`, mask+sign-extend
    for `intN` — Go's `uint8(x)`/`int8(x)`, no representability proof since it
    truncates).  Cross-width by composition.  These also make the distinct numeric
    types mixable (implicit mixing rejected — `u8_of_i16_direct` `Fail`).
    Machine-checked `spec_u8_of_int_trunc`…`spec_i16_of_u8_cross`; `convert_demo`
    prints 200 232 / 1200.  *Still ✗:* int↔float / float↔float (float gaps, no f32);
    `string`↔`[]byte`/`[]rune` (rune view); `int`/64-bit conversions (Z-width model);
    interface conversions beyond `type_assert`.

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

## Concurrency research plan — the road to real race-freedom

Where the concurrency proofs stand (`builtins.v` Phases 1–4, `concurrency.v` Phases
5–6) and the three steps that turn "an abstract calculus has sound happens-before"
into "**Fido's extracted programs are race-free**".  Done so far, all axiom-free: the
4 go-mem channel rules + the fork edge as a strict partial order that does not
over-order; happens-before for ARBITRARY execution traces (`hbt_irrefl` — the trace
position is a linear extension); and a concurrent operational semantics whose every
reachable trace is provably well-formed (`reachable_wf` → `reachable_hb_strict`).
The honest gaps, IN ORDER, each taken one at a time with careful up-front planning:

1. **Keystone — refine `run_io` to the operational calculus.**  The race-soundness
   lives on the abstract `PAct`/`step` calculus (`concurrency.v`), DISCONNECTED from
   the `run_io`/`World` model we actually extract from.  No theorem links `send`/
   `recv`/`go_spawn` to `step`, so the guarantee does not yet *apply* to a real
   program.  CORE DIFFICULTY: `run_io` is SEQUENTIAL (no interleaving) and `IO` is
   axiomatic/opaque, so we can't compile it structurally — the keystone needs a
   *concurrent* operational semantics for the IO ops, connected both ways.  Sub-steps:
   **(1.1 — DONE)** goroutine SPAWN added to `step` (`PSpawn`/`step_spawn`, DYNAMIC pool
   via `cfg_live` — only spawned goroutines run, initially just `main`);
   `reachable_wf`/`reachable_hb_strict` re-established, axiom-free.  *Fork EDGE
   (`KStart` back-pointer) deferred* — a two-event step, already proven abstractly by
   `fork_hb`; until then cross-goroutine ordering flows through channels.
   **(1.2 — DONE)** the RICH calculus (`Cmd`/`RConfig`/`rstep` in concurrency.v):
   per-goroutine programs are a command TREE (`CRet`/`CSend`/`CRecv`/`CWrite`/`CRead`/
   `CSpawn`) with value-binding continuations (`nat -> Cmd`) — i.e. `bind`, control
   branches on received/read VALUES.  Channels carry `(value, send-position)`; the
   HEAP is real (`rc_heap`).  REUSES the proven infrastructure, so `RInv` is preserved
   (`rstep_preserves_inv`) and the safety theorems are INHERITED: `reachable_wf_r` →
   `reachable_hb_strict_r`, `reachable_owned_safe_r`.  `rich_recv_binds`/
   `rich_read_binds` demo the value flow; `rheap_read_after_write` the real memory.
   **(1.3 — channel/heap-state refinement DONE; channel + heap term-level bridge DONE;
   multi-channel/composition open)**
   `rchan` (the channel value-FIFO) evolves EXACTLY as the `run_io` axioms specify —
   `rchan_send_law` = `chan_buf_send` (enqueue value), `rchan_recv_law` =
   `chan_buf_recv` (dequeue head).  So the calculus soundly models Fido's IO channels.
   **The TERM-LEVEL bridge is now built** (`Section Keystone` in concurrency.v): `Cmd`
   IS the deep embedding of an IO program, and `Denotes c m` is the deep↔shallow
   correspondence — a RELATION, because `CRecv`'s continuation is a Coq function
   (`nat -> Cmd`) so a denotation *function* can't structurally recurse.  Then
   `denote_sim_send` / `denote_sim_recv` prove that ONE `rstep` channel action
   run-reduces the IO denotation EXACTLY as `run_io` specifies (`run_bind` +
   `run_send`/`run_recv`), with the channel buffer staying matched (`WMatch1`) —
   mirroring `rstep_send`/`rstep_recv`.  This ties the abstract `rstep` (where
   race-freedom is proven) to the `run_io`/`World` model we extract from.  Trust base
   (verified by `Print Assumptions`): exactly `run_bind`/`run_send`/`chan_buf_send`
   (send) and `run_bind`/`run_recv`/`chan_buf_recv` (recv) — no degenerate axioms;
   the faithful-coding round-trip `Hret` is a DISCHARGED hypothesis, not an axiom.
   Carrier is `int`/`TInt64` because `GoTypeTag nat` is provably empty; values are
   coded `nat`↔`int` (realizable on the bounded ±2⁶² regime the int model already
   assumes).  **`go_spawn` is deliberately ABSENT from the bridge — it has NO `run_io`
   law because `run_io` is SEQUENTIAL and cannot express interleaving; that is exactly
   why the calculus is the model for concurrency.**  The HEAP fragment is bridged too
   (`denote_sim_write`/`denote_sim_read`: `CWrite`/`CRead` → `ref_set`/`ref_get` via
   `run_ref_set`/`run_ref_get` + `ref_sel_upd_same`, with a one-location heap match
   `WHMatch1`) — so the bridge now covers the full sequential channel + MEMORY fragment
   (memory accesses being exactly what races are about).  *Still open:* multi-channel /
   multi-location matching (needs a channel/ref-separation/frame law), composing the
   per-step lemmas into a whole-execution simulation, and the plugin lowering side
   (`Cmd` ↔ extracted Go).
2. **General race-freedom under the ownership / session discipline — DONE (core
   theorem).**  `owned_race_free` (concurrency.v, axiom-free): a trace satisfying the
   ownership discipline `Owned` — accesses to each location form an hb-CHAIN (any two
   same-location accesses are directly hb-ordered or separated by an intermediate
   same-location access, the trace shadow of "only the owner touches it, ownership
   transfers only via synchronisation") — is `TraceRaceFree`.  Proof: `Owned` lifts
   locally-ordered accesses to a global hb-chain (`owned_orders_same_loc`, strong
   induction), so no conflicting pair is unordered.  `mp_trace_owned` shows the
   message-passing trace satisfies it, so `owned_race_free` re-derives its
   race-freedom from the GENERAL theorem (subsuming the hand-built
   `mp_trace_race_free`).  *Remaining:* tie `Owned` to a SYNTACTIC discipline a
   program can be checked against (channel-endpoint ownership transfer / session
   linearity ⇒ `Owned`), so it is established by typing rather than as a hypothesis.
3. **Model completeness — exact FIFO (done), liveness, real memory.**  *Exact FIFO —
   DONE:* `reachable_sorted` (concurrency.v, axiom-free) — every reachable channel
   buffer is STRICTLY INCREASING in send position (`BufSorted`, via `step_preserves_
   sorted`).  Since `step_recv` pulls the buffer FRONT (the minimum = oldest
   unreceived send), receives consume sends oldest-first — the exact kth-recv ↔
   kth-send pairing, established by the semantics + the invariant.  (An explicit
   trace-level `from(j1) < from(j2)` theorem would additionally need a recv-event ↔
   producing-step relationship — a nicety on top.)  *Still open:* deadlock-freedom /
   progress (representable today, freedom unproven — needs a typing/session
   discipline + a non-terminating model); and a real heap behind `KWrite`/`KRead`
   (currently abstract events).

**Combined (steps 1+2):** `reachable_owned_safe` — a REACHABLE execution respecting
the ownership discipline has a strict-partial-order happens-before AND is race-free.
**Deadlock representability:** unlike the (total, sequential) `run_io`, the
operational semantics REPRESENTS deadlock — `block_stuck`: a config that cannot step
yet has a live goroutine with work left (`Stuck`).  Proving deadlock-FREEDOM is the
open liveness frontier; this is its honest foundation.  All axiom-free.

(Supersedes / extends the open items under "Correctness debt" Tier 1 #1.)

## Architecture

- **Package imports are on hold (decided 2026-06-14).** The plugin emits
  `package main` with **no** `import` block, and we will not add the import
  machinery (nor any builtin that needs it — `math.Abs`/`math.Sqrt`,
  `fmt`/`strings`/stdlib, etc.) **until every no-import builtin is locked down
  perfect**. Rationale: imports are a frontier of their own (when to emit, dedup,
  Go's unused-import error); finishing the primitive layer first keeps the trust
  base small. A builtin that *needs* an import is deferred, not approximated — no
  hand-rolled `abs` that mishandles `-0.0`.
- `SPEC_CONFORMANCE.md` — the Go-spec conformance ledger: each spec section we
  model, the rule (cited), our behavior, status (✓ conforms / ⚠ bounded deviation
  / ✗ fails loud), and the machine-checked witness. Verify the spec **one section
  at a time**; when code implements a rule, it cites the section in a comment. A
  primitive is "done" only when its section is honored there.
- `*.v` and `*.go` are both committed; `*.go` is always re-derivable from `*.v`
- `plugin/go.ml` + `plugin/g_go_extraction.mlg` — the Rocq→Go extraction plugin
- `builtins.v` — Go builtins (always in scope, loaded via `preamble.v`)
- `concurrency.v` — proof-only theory (emits no Go): trace-based happens-before for
  arbitrary executions (`hbt_irrefl`), the bridge from the abstract go-mem rules to
  actual execution traces.  Listed in `dune` `(modules …)`
- `preamble.v` — shared preamble; every theory starts with `From Fido Require Import preamble`
- `dune` / `dune-project` — builds plugin + theories together inside Docker
- **Extraction-driver recompile (build correctness).** The generated `*.go` are a
  SIDE EFFECT of compiling the extraction-driver theory (`main.v`'s `Go Main
  Extraction` vernac); dune does NOT track them as build outputs.  A warm `_build`
  cache breaks this BOTH ways, so the `Dockerfile` counters both before `dune build`:
  (1) *removal* — a deleted/renamed driver's stale `*.go` orphan would linger in the
  cached `_build` (and ship), so nuke ALL generated `*.go` up front; only still-
  existing drivers recreate theirs; (2) *staleness* — dune skips recompiling an
  unchanged driver, so force every current driver's `.vo` out (drivers auto-detected
  via `grep -l 'Go Main Extraction'`) to make it re-extract afresh, with the heavy
  proof libraries staying cached.  A `test -n` guard then fails the build LOUD if no
  `*.go` was produced.  (Host side: `make extract` does `rm -f *.go` first, same
  removal hygiene.)  The principle: keep generated outputs in sync by removing ALL
  stale outputs AND forcing regeneration of the current ones — neither half alone
  suffices (just removing `*.go` won't regenerate an untracked side-effect; just
  forcing recompile leaves orphans when a source is deleted).  Do not "fix" a
  missing-`.go` build by touching `main.v` — that masks the real cause.
- Pre-commit hook (`.githooks/pre-commit`; activate once via `make
  install-hooks`): when any `.v` or `plugin/` file is staged, it re-extracts
  and auto-stages the generated Go, so committed `*.go` can never drift from
  prover output (a broken proof aborts the commit); also enforces gofmt. Still
  the anti-tampering gate — fresh prover output always overwrites `*.go`.
- **`gofmt` is load-bearing, by design.** The plugin emits valid Go but does NOT
  match gofmt's whitespace (operator spacing is an operand-sensitive
  depth/cutoff rule; alignment is `text/tabwriter`'s two-pass elastic tabstops).
  gofmt *is* Go's only definition of canonical surface form — there is no spec to
  implement independently — so `make extract` runs `gofmt -w` to canonicalise,
  rather than vendoring a second copy of `go/printer`+`tabwriter`. **Do not remove
  the `gofmt -w` step**; the hook's `gofmt -l` is only a backstop confirming it
  ran. (Decided 2026-06-14: a from-scratch canonical emitter would mean
  maintaining a gofmt clone byte-for-byte forever — the worse trade for cosmetics.)

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
