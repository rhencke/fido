# Fido — progress, design & status

Detailed companion to `CLAUDE.md` (which is kept short: the rules, commands, and architecture). This is the living reference — the full project vision and principles, the incremental ladder (what is modelled, feature by feature), the correctness-debt tiers, known gaps, the wish list, and the concurrency research plan. **Update the ladder here when a feature lands.** Not auto-loaded into context; read on demand.

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

**Principle: minimize and track the trust base (axiom discipline).** A theorem is
only as strong as its weakest assumption.  An **axiom** is a fact Rocq *believes
without proof* — and one inconsistent axiom is catastrophic: from a contradiction
you can prove *anything*, so every theorem silently becomes vacuous while still
compiling.  This is not hypothetical here — a plausible totality axiom on `run_io`
once entailed `World -> False`, making `println [1] = println [2]` a "theorem" and
every Hoare triple vacuously true; nothing *looked* broken (Known gaps #9).  So:
(1) **prefer proving to assuming** — the strongest results are **axiom-free**
("`Print Assumptions` = *Closed under the global context*"), resting only on the
kernel; the doc is full of "this was an axiom, now it's a derived theorem", and
each such move shrinks what we trust.  (2) Axioms are not evil — they are how we
*model reality* (channels, IO, the heap can't be proved from pure logic); but each
is a load-bearing **promise** that our model matches Go, hence a place the proof
can be right about the model yet the model wrong about Go.  Keep them **few**, and
prefer ones validated by an exhibited model (separation/heap laws) over free-
standing assertions.  (3) **Always know the base**: run `Print Assumptions` after a
significant result and state its trust base honestly — never overclaim a guarantee
whose axioms aren't named.

**CURRENT TRUST BASE (re-verified 2026-06-19, `Print Assumptions main_effect`): ZERO Fido
axioms** — confirmed AFTER this session's additions (custom enums, user/mutual recursion,
generics over functions & types, struct embedding, IO-value methods, defined types over
every underlying).  `main.v` now keeps a standing `Print Assumptions main_effect.` before the
`Go Main Extraction`, so EVERY build re-confirms the base (continuous verification; it prints
to the build log and does not affect the runtime golden).  The printed base is EXACTLY Rocq's
machine primitives — `int : Set`, `float : Set`, `PrimInt63.*`, `PrimFloat.*`, and
`of_uint63` — with no `chan_*`/`map_*`/`ref_*`/`wrap*` or any other Fido name.  `builtins.v`,
`main.v`, `concurrency.v` declare NO `Axiom`/`Parameter`/`Admitted`; the IO /
heap / channel / session model is `Definition`s over a concrete `World`/`Outcome`, and
every law (`run_bind`, channel & heap get-after-put, `ref_sel_upd_same`, …) is a DERIVED
THEOREM.  The extracted program rests on EXACTLY Rocq's own machine primitives — `int :
Set`, `float : Set`, and the `PrimInt63.*` / `PrimFloat.*` operations — and nothing else.
The only assumptions anywhere are two `concurrency.v` SECTION hypotheses (the abstract-
calculus ↔ IO coding round-trip) — proof-only, parameterised (discharged at section
close), emit no Go, NOT in the extracted program's trust base.  So the old "~70 axioms /
joint consistency unproven" debt is CLOSED: there is no Fido axiom set to be jointly
consistent.  The discipline now is to PRESERVE this — add no `Axiom` for any new builtin
(model it as a `Definition`, even hard cases like a soft-float `float32`).

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
- **The "make a Go expert faint" demo (NORTH-STAR, user-requested 2026-06-21)** — one
  deliberately HORRIFYING but PROVABLY-CORRECT Go program: goroutines and channels nested
  in slices in structs, `select` over channels of structs-containing-channels, channels
  that send *themselves*, and assorted nonsense — that compiles, runs, and is machine-
  checked to never race, deadlock, send-on-closed, or panic. The point is VISCERAL: it
  looks unsafe to an expert, yet Rocq has ruled out every failure mode. *Pieces:* FINITE
  nesting is mostly ASSEMBLY today — `TChan`/`TSlice`/`TProd`/`TPtr`/`TMap` already compose
  (a `[]chan *Foo` field in a struct shuttled between goroutines is taggable now). Two
  genuine frontiers gate the FULL horror: (1) RECURSIVE / self-referential types. Valid Go
  recurses through INDIRECTION (pointer/channel/slice/map/func); only direct `type X X` /
  `struct{x X}` is rejected. FIRST TARGET = **`type X *X`** (valid Go, the minimal recursive
  self-type). Because `Ptr` is a TAG-FREE phantom handle, the VALUE side is BENIGN — model
  `Inductive X := mkX (Ptr X)`: a value is just a location, recursion erased at runtime (like
  phantom typestate). So the research nut is NARROW: the recursive TYPE TAG, not the value rep —
  deref/sending X needs `GoTypeTag X`, but the finite-inductive `GoTypeTag` can't hold the cyclic
  `tagX = TPtr tagX` (the universe wall that forced `GoChan`/`Ptr` tag-free, builtins.v:161).
  Need a named-type tag / tag fixpoint; `type X *X` cracks it cleanest (pointer keeps values
  trivial), `type C chan C` is the same tag problem + payload semantics. (2) VERIFIED SAFETY on
  the cursed program (race/deadlock-freedom on the TYPED program) = limit #2 (in progress) + the
  deadlock/session theory. The safety half is what makes it LAND — without it the demo merely
  compiles; with it, an expert learns the self-sending-channel soup is *proven* clean. *Ordering
  (user 2026-06-21): QUEUED after the current loop priorities (limit #2 etc.) — a to-do, not now.*

Interdependence to remember: closed-world for a *shared* value presupposes the
ownership / race-freedom discipline (another goroutine could mutate it out from
under the invariant), so these and the concurrency proofs are one web, not
separate tracks.

## Incremental ladder

1. **Builtins** (done) — `println`, `print`, `panic`, `any`, primitive types,
   `GoSlice`, `GoString`, `GoMap`, `type_assert`, plus the import-free predeclared
   `make([]T,n)`), and Go 1.21 `min`/`max`/`clear`. `min`/`max` cover `int`
   (`go_min`/`go_max`), the canonical `int64`/`uint64` (`i64_min`/`i64_max` signed,
   `u64_min`/`u64_max` unsigned), AND `float` (`f64_min`/`f64_max` — faithful on the
   NaN-propagation and signed-zero corners) → Go `min(a,b)`/`max(a,b)`
   (`minmax64_demo` → `-2 1 18446744073709551615`; `fminmax_demo` floats). Add to
   `builtins.v` + plugin
   match.  `new` (pointers), `copy`/slice-`clear`/`make([]T,len,cap)` (slice aliasing),
   and `complex`/`real`/`imag` are all now DONE (the last 2026-06-18: `GoComplex128` is a
   2-field float record rendered as native `complex128`, with `go_complex`/`go_real`/
   `go_imag` → `complex(re,im)`/`real(c)`/`imag(c)`; struct decl/ctor/projections
   suppressed, recognised by name; axiom-free, `complex_demo` golden-locked).  **Complex
   ARITHMETIC is also done (2026-06-18):** `+`/`-` (component-wise), `*` (gc's naive
   cross-product — faithful since gc inlines naive, no Annex G), unary `-` (sign-flip),
   `==`/`!=` (component-wise float `==`, faithful incl. the NaN corner), and **`/` (DONE
   2026-06-18: Smith's scaling algorithm = gc's `runtime.complex128div`, faithful for FINITE
   divisors; the degenerate Inf/NaN/zero-denominator Annex-G recovery applies at runtime via
   the native lowering but is a documented Coq-model gap; branch test uses the squared-
   magnitude form to dodge the `PrimFloat.abs` extraction-axiom)** — all lower to the native
   Go operators, axiom-free, golden-locked.  **Complex arithmetic is now COMPLETE.**
   **MILESTONE (2026-06-18): every Go PREDECLARED BUILTIN FUNCTION is now modeled** —
   append, cap, clear, close, complex, copy, delete, imag, len, make, max, min, new, panic,
   print, println, real, recover.  The remaining no-import work is all LANGUAGE FEATURES;
   **method values (`p.M`), method expressions (`T.M`), and MULTIPLE RETURN VALUES are now
   done too** (2026-06-18) — a pair-returning function lowers to a Go multi-value return
   `(A, B)` / `return a, b` and the caller's destructuring `let '(x,y) :=` to `x, y := f(…)`
   (`multiret_demo` → `4 3`, axiom-free, golden-locked).  **USER VARIADIC FUNCTIONS DONE
   (2026-06-19):** `func f(xs ...T)` — a param of type `Variadic T` renders `...T` (not `[]T`),
   and a `vararg xs` call argument spreads to `xs...`; inside the func `va_slice` recovers the
   slice.  `Variadic T` is a 2-FIELD record (a `bool` phantom) so Coq does NOT unbox the single
   slice field — that is what keeps the param type distinguishable from a plain `[]T`; the
   single-field-unbox blocker (which sinks the 1-method interface / GoI64-2-field) does NOT
   apply here because a variadic param needs no `Comparable`/equality, so the phantom is free.
   `variadic_demo`: `Sum_print(xs ...int64)` called `Sum_print(xs...)` → `7 / 8 / 9`, axiom-free,
   golden-locked.  **GO GENERICS (type parameters) DONE (2026-06-19):** Rocq's parametric
   polymorphism maps directly to a Go generic — a function's distinct type VARIABLES (kept by
   extraction as `Tvar`, rendered `T<i>`) become a `func F[T1 any, …]` type-parameter list
   (`pp_function` collects them via `collect_tvars`; constraint `any` because parametric
   polymorphism imposes no operations on the type).  Call sites need NO change — Go infers the
   type args (`Gid("go")`, `Glen(make([]int64,3))`).  Emitted only for FUNCTIONS, not methods (Go
   forbids a method introducing its own type params — that needs a generic receiver/struct, not yet
   modeled).  `generics_demo`: `Gid[T1 any](x T1) T1`, `Glen[T1 any](xs []T1) int` reused at
   `[]int64` AND `[]string`, `Gfirst[T1 any, T2 any]` → `go / 3 / 2 / first`, axiom-free,
   golden-locked.  Faithfulness caveat: a BARE untyped-int literal arg (`gid 7`) has Go infer `int`
   not our `int64` (the untyped-constant gap, Tier 2 #6); typed operands (string lits / typed slices)
   pin the arg, so the demo is faithful.  **GENERIC STRUCTS/TYPES DONE (2026-06-19):** a
   PARAMETERIZED Rocq `Record` → a Go generic struct `type Box[T1 any] struct {…}` (the struct-decl
   arm collects the field types' `Tvar`s into a type-param list).  Go does NOT infer type args for a
   composite LITERAL, so the constructor emits them explicitly — `Box[T1]{…}` inside a generic
   function, `Box[int64]{…}` at a concrete use — taken from the `MLcons` constructed-type field
   `Tglob(Box, instanceargs)` (non-generic records have no args → no brackets, so existing `Point{…}`
   etc. are unchanged).  A method's receiver carries the params (`func (b Box[T1]) Box_get() T1` — the
   already-existing `pp_type`/`is_record_tglob` handle the parameterised receiver) and call sites
   infer (`(Make_box("hi")).Box_get()`).  `Box` needs ≥2 fields (1-field records unbox).  `gstruct_demo`
   reuses one `Box` at `string` AND `bool` → `hi / true / 1`, golden-locked, axiom-free.  *Still
   pending:* constraints beyond `any` (`comparable`/interface — would map a Coq typeclass dict to a Go
   constraint); generic struct used as a map value/key; an unused non-erased value param mis-names
   (the `_:B` → duplicate-name artifact, a latent dummy-binder bug, sidestepped by naming params).
   *Cross-project status (this list was STALE — reconciled 2026-06-19, each verified in the
   committed Go):* **DONE** — single-method + nullary interfaces (NOT blocked: the `gr_self`/
   `sg_self` second field makes a 2-field record modelling Go's (vtable, value) pair, which both
   sidesteps Coq's 1-field unboxing AND is more faithful — `Greeter{Greet: func(x int64) int64 {
   return base + x }, Gr_self: base}`, dispatch `g.Greet(10)`; closures capturing locals lower
   too); the rune/UTF-8 string view; `float32` soft-float (full: arith / compare / all
   conversions); the int↔float and narrow↔64 conversions (the whole width-typed integer matrix +
   `float64`↔`int64`); complex `/` (Smith's); N-field struct pointers (`StructRep3`).  **Still
   open** — exact-rational / untyped float constants only.  Tracked in the ladder + Tiers.
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
   - **CUSTOM ENUMS DONE (2026-06-19), the first real `switch` emission.** A nullary-
     constructor user `Inductive` (≥2 ctors, all 0-arg; `bool` excluded as a builtin,
     nat/list/option auto-excluded by their non-nullary ctors) → Go's iota-enum idiom:
     `type Direction int` + a `const ( North Direction = iota; South; East; West )` block
     (Dind arm), each constructor emits its const name (`MLcons` nullary arm), and an
     N-arm match in STATEMENT position → a Go `switch d { case North: … }` (a new
     `emit_case` arm, checked before the 2-arm shapes so a 2-value enum switches too).
     `pp_type` accepts the enum typename; registered in `collect_decls` pass 1.
     `enum_demo` (`dir_io East`) → `2`, golden-locked, axiom-free.  **VALUE-position enum
     match DONE too (2026-06-19):** a `pp_pure_tail` enum-switch arm emits `func (d Direction)
     String() string { switch d { case North: return "N"; … } }`.  Go does NOT treat a
     `default`-less switch as exhaustive (→ "missing return"), so the LAST arm (the last
     constructor, in constructor order) is emitted as `default:` — faithful, since the match is
     total and the others are matched above, so `default` catches exactly the last constructor.
     `dir_name` needs `NoInline` (keep the match in tail position); `enum_value_demo` → `W`.
     A source `_` WILDCARD arm needs no special handling (confirmed 2026-06-19): Coq EXPANDS
     it into the missing constructors (so `North => 1 | _ => 0` lowers to the all-cases
     switch), so it never reaches the plugin as a `Pwild` for a finite enum; `enum_default_demo`
     → `1 / 0`.  *Still pending:* enum values as map keys / `==` comparison.
   - **`nat` match (`O` / `S k`) → `if n == 0 { … } else { k := n - 1; … }` — DONE
     (2026-06-19), enabling USER RECURSION** (a Coq `Fixpoint` → a self-calling Go
     func).  The probe was the lesson: "recursion" was never the wall — a `Fixpoint`
     extracts fine; the blocker was the `nat` STRUCTURAL match (`O`/`S k`) being
     unmodeled in statement position.  Modeled as a mirror of the list nil/cons case
     (`O` = the zero test, `S k` binds the predecessor `k := n - 1`, reachable only when
     `n != 0` so the `uint` subtraction never underflows).  `countdown (n : nat) (v : GoI64)`
     (nat fuel + a `GoI64` accumulator) → `func Countdown(n uint, v int64) { if n == 0 {} else
     { k := n - 1; println(v); Countdown(k, v-1) } }`, `recursion_demo` → `3 / 2 / 1`, golden-
     locked, axiom-free.  **VALUE-position `nat` match DONE too (2026-06-19):** `pp_pure_tail`
     is now nat-aware (the same mirror, in tail position — `if n == 0 { return a } else { k :=
     n - 1; return b }`), so PURE value-returning recursion lowers: `Fixpoint pow2 (n : nat) :
     GoI64` → `func Pow2(n uint) int64 { if n == 0 { return 1 } else { k := n - 1; return 2 *
     Pow2(k) } }`, the self-call `Pow2(k)` in expression position; `pure_rec_demo` → `16`.  So
     recursion is complete in BOTH IO (statement) and pure (value) positions.  **MUTUAL
     RECURSION works too (2026-06-19), no plugin change:** a mutual `Dfix` already emits each
     function via `pp_function` and a cross-call is an ordinary call, so `Fixpoint is_even … with
     is_odd …` → two cross-calling `func Is_even(n uint) bool` / `func Is_odd(n uint) bool`;
     `mutual_rec_demo` → `true / false`.  *Still pending:* a GENERAL value-position match on
     richer inductives / >2 arms (the nat & bool tail cases are special-cased; an arbitrary
     value-position match still needs the IIFE/hoist work).
   - type switch (`switch v := x.(type)`) — *DONE (2026-06-18)*. `type_switch2` is a
     combinator dispatching on a `GoAny`'s runtime type, built on the existing
     `tag_coerce`/`GoTypeTag` machinery (*not* `MLcase`) — so it is **axiom-free** (the
     same basis as `type_assert_safe`). Each case tries its tag via `tag_coerce`; the
     first match runs that arm's continuation with the recovered, correctly-typed value,
     else the default. Machine-checked dispatch (`type_switch2_first` runs the matching
     arm with the value; `type_switch2_default` falls through on a type matching neither).
     Lowers to Go's native `switch _tsv := a.(type) { case T: v := _tsv; … default: … }`
     — each arm rebinds the case-typed value from the shared guard `_tsv` (distinct
     binder names need no env renaming); the guard is omitted if no arm uses its value.
     Two general plugin fixes it needed: `any v` (existT) now erases to its payload in
     *general* value position (e.g. a direct func arg), not only inside the `type_assert`
     arms; and the `GoAny` Definition-alias renders as Go `any` as a signature type.
     `tsw_demo` → `true 1` / `go 2` / `9` (bool/string/default), golden-locked.  **N-ary
     DONE (2026-06-18):** `type_switch3` (and any `type_switchN`) lowers through one
     GENERALISED plugin arm — it matches `type_switch` by name prefix and treats the args
     after the scrutinee as (tag, continuation) PAIRS then the default, so higher arities
     need no new plugin code.  `tsw3_demo` → `true 1` / `hi 2` / `5 3` (bool/string/int64;
     the int64 case driven by a typed func return so it boxes as `int64`, a faithful
     int-vs-int64 distinction).  **Multi-type `case T1, T2:` DONE (2026-06-18):**
     `type_switch_or2` — one arm matching EITHER of two tags; in Go the value is not
     narrowed (keeps the interface type) so it's a value-less thunk `k : IO B`, run when
     the type is `t1` OR `t2`; machine-checked first/second/default; lowers to native
     `case bool, string:`.  `tsw_or_demo` → `1` / `1` / `0`.  **Type switches are now
     complete** (2-case, N-ary, multi-type).
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
   IIFE. *The TAIL case is now DONE (2026-06-18):* when the `if`/`match` is the
   whole pure-function BODY (tail position), `pp_pure_tail` lowers it to a Go
   `if`/`else` whose arms each `return` — the idiomatic form — recursing so
   nested `if`s chain. Only a 2-arm **bool** match is modeled; a non-bool / non-
   tail value-position match still **fails loudly at extraction** via
   `unsupported` (the `return` fallback routes it to `pp_expr`'s catch-all —
   see "Fail-loud policy" below — rather than emitting a plausible-but-wrong
   `nil`). Demo: `i64_abs` (Go has no integer `abs` builtin, so it is written
   with exactly such an `if`) lowers to `func I64_abs(a int64) int64 { if a < 0
   { return 0 - a } else { return a } }`; faithful across the full int64 range
   incl. the `MININT` corner (`0 - a` wraps, so `|MININT| = MININT` — machine-
   checked `i64_abs_minint`), golden-locked (`7 7 -9223372036854775808`). The
   callee must be `NoInline` so the `if` stays in tail position rather than
   being inlined into a call-site value slot. *Still pending:* the general
   value-position match as a SUBexpression (IIFE / hoist-to-var, needs the arm's
   value type).
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
   (default); golden-locked. The denotational CHOICE semantics (which ready case
   runs, pseudo-random fairness, blocking when none ready) is idealised away in the
   *sequential* `IO` model — but the AUTHORITATIVE choice semantics now lives in
   `concurrency.v`'s relational `rstep_select` (nondeterministic, per-case
   continuations), and the typed `select_recv2` is proven a SOUND scheduler of it
   (`det_select_sound`), INCOMPLETE in general (`det_select_incomplete`: ≥2 ready ⇒ it
   misses a successor), yet COMPLETE precisely when ONE case is ready
   (`det_select_complete_unique` / `det_select_exact_unique`, 2026-06-21, axiom-free) —
   so the deterministic model's exact faithfulness boundary is now a theorem. *Frontier:*
   send-cases / N-ary (>2) cases are the same lowering with more arms; and a single
   composed `select_recv2`(World)→`rstep_select` theorem (today argued in prose).
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
   `true/5`); golden-locked. **Struct COMPARABILITY done (2026-06-18):** Go's struct
   `==` is FIELD-WISE, so `point_eqb a b := (a.Px==b.Px) && (a.Py==b.Py)` (via the
   existing `&&`/`==`/projection ops — no value-position `if`, no new lowering) is
   faithful to `p == q`; `point_eqb_spec` PROVES it decides `Point` equality (the
   comparability guarantee, from `comparable_TI64` + record injectivity).  It lowers as
   a value-receiver method `func (a Point) Point_eqb(b Point) bool { return a.Px ==
   b.Px && a.Py == b.Py }`; `struct_eq_demo` → `true false`, golden-locked.  **NESTED
   struct fields done (2026-06-18):** a struct with a struct-typed field composes — `Wrap
   { w_inner : Inner ; wz }` lowers to `type Wrap struct { W_inner Inner; Wz int64 }`, the
   nested literal `MkWrap (MkInner 5 1) 9` → `Wrap{Inner{5, 1}, 9}`, and the chained
   projection `iv (w_inner o)` → `(o.W_inner).Iv` — compiles; `nested_struct_demo` → `5 9`,
   golden-locked.  **single-field-record gap — now FAIL-LOUD (fixed 2026-06-18):** a 1-field
   user record (`Inner { iv }`) is UNBOXED by Coq (`Inner ≡ GoI64`, no `Dind`/struct decl
   emitted), so a `W_inner Inner` field would reference a now-nonexistent type → previously
   UNCOMPILABLE Go (`undefined: Inner`), a meta-invariant violation.  Now the plugin's
   generic `Tglob` type arm REFUSES any type that is not a registered (emitted) record:
   `cannot extract type 'Inner' (no struct decl emitted — a single-field Record is unboxed
   by Coq; give it >= 2 fields)`, aborting `make extract` instead of emitting dangling Go
   (verified both directions: 2-field extracts; 1-field aborts).  Workaround stays ≥2 fields
   (the demo does); proper single-field support needs the curried/erasure work (ladder 9c).
   **STRUCT EMBEDDING DONE (2026-06-19)** — Go's `type Dog struct { Animal; Breed string }`
   (composition with field/method PROMOTION).  Modeled as a record field whose exported name
   EQUALS its (record) type's name (`animal : Animal`); the plugin emits it as an ANONYMOUS
   embedded field (the `field` helper checks `fname = go_export typename && is_record_typename`),
   so the Go struct genuinely embeds `Animal` and Go promotes its method set.  The embedded type
   needs ≥2 fields (a 1-field record is unboxed).  Access is through the embedded field —
   `species (animal d)` → `(d.Animal).Species`, promoted method `speak (animal d)` →
   `(d.Animal).Speak()` (both valid/faithful; Rocq has no implicit subtyping, so the explicit
   projection is how a well-typed term reaches the embedded member).  The PROMOTED SHORTHAND is
   emitted too: a member access through an embedded field `member (animal d)` lowers to the
   idiomatic `d.Species` / `d.Speak()` (a `peel_embedded` peephole strips the `.Animal` hop in
   the projection + method-call arms) — which compiles ONLY because Go promotes through the
   embedded field, so it genuinely exercises promotion.  Safe with no shadowing check: Coq
   projection names are globally unique, so `d.Member` is unambiguous; non-embedded nested access
   (`(o.W_inner).Iv`) is left explicit (the peephole is selective).  `embed_demo` → `canine /
   canine`, golden-locked, axiom-free.  *Not yet:* embedding a non-struct/pointer type; struct
   tags; the single-field-struct distinctness (ladder 9c), the IDIOMATIC direct `p == q` (tidiness).

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
   **Pointer-RECEIVER methods DONE (B2, 2026-06-18)**, on the struct-pointer substrate
   (**Bs.2**): a heap-backed `SPtr R` → Go `*R` with mutation through the pointer
   (`sptr_new`→`&R{…}`, `sptr_set_field`→`p.Field = v`, `sptr_get_field`→`p.Field`),
   backed by field-cell read-after-write + aliasing THEOREMS (`sptr_field_get_set`/
   `sptr_field_alias`, axiom-free over the heap), sidestepping the `GoTypeTag` struct-tag
   wall via a data-only `StructRep`.  A method whose first param is `SPtr (record)` lowers
   to `func (p *T) M(…)` (the SAME detection/signature path as the value-receiver method,
   since `pp_type (SPtr R) = *R`), and a call `m p …` → `p.M(…)`; the method MUTATES its
   receiver, observed by the caller.  `cell_incx` → `func (p *Cell) Cell_incx() { a := p.Cx;
   p.Cx = a + 1 }`; `ptr_method_demo` mutates a `*Cell` via the method and prints `11`
   (`sptr_demo` → `7 4`).  **METHOD VALUES DONE (2026-06-18):** `recv.M` as a first-class
   closure — a value-receiver method applied to ONLY its receiver (`shifted p`) is the
   under-application Go writes `p.M` for.  The plugin records each method's visible arity at
   registration (`method_arity`); a call site applying fewer than that many args emits the
   bare `p.Shifted` (a method value) instead of a call, full-arity calls unchanged (no
   regression).  `method_value_demo` passes `p.Shifted` to a HOF `call_shift10(f func(int64)
   Point)` (func-typed param via the `Tarr` arm) → `11 12`; faithful (Go's `p.M` binds the
   value receiver at evaluation = the partial application).  **METHOD EXPRESSIONS `T.M` DONE
   (2026-06-18):** a value-receiver method referenced UNBOUND (a bare method glob, 0 args) is
   Go's method expression — a `func(T, …) …` whose first arg is the receiver.  The plugin
   records the receiver type name (`method_recvtype`) and emits `Point.Sum_coords` for the
   bare glob; `method_expr_demo` passes it to a HOF `apply_pt(f func(Point) GoI64, p Point)`
   → `11`.  **N-FIELD pointer receiver DONE (2026-06-19):** `StructRep3`/`SPtr3` generalise the
   2-field substrate to a 3-field `*Cell3` (same GENERIC `hfield_cell`/`hfield_get_set_same`
   heap, so `sptr3_field_get_set` reuses the 2-field proof); the plugin recognizers
   (`is_sptr_type`/`is_sptr_*_ref`/`is_erased_record_typename`) match `SPtr3`/`StructRep3` too,
   so `cell3_inc_z (p : SPtr3 Cell3)` → `func (p *Cell3) Cell3_inc_z()` mutating `p.C3z`;
   `nfield_ptr_demo` → `31`, golden-locked, axiom-free (`Print Assumptions main_effect`
   unchanged).  **HETEROGENEOUS field types DONE (2026-06-19):** `StructRep2H`/`SPtrH R A B`
   carry per-field types + tags, so a `*Pair{ N int64; B bool }` mutates through the pointer
   (`pair_bump` → `func (p *Pair) Pair_bump()` bumps the int64 field, bool preserved); the
   field-cell heap was already generic over the field type, so `sptrh_field_get_set` is again
   the `hfield_get_set_same` proof verbatim.  The only plugin change: the record-type
   extractors take the FIRST type arg of the 3-arg `SPtrH R A B` (`arg :: _` vs `SPtr R`'s
   `[arg]`).  `het_ptr_demo` → `11 true`, golden-locked, axiom-free.  *Not yet:* the same
   template at arbitrary N (4+, mechanical); pointer-receiver method expressions `(*T).M`;
   method-name namespacing via Rocq `Module`s (so two types can share a basename like `Area`).
   **DEFINED TYPES over a primitive with methods DONE (2026-06-19)** — Go's `type MyI64 int64`
   (a distinct named type with the primitive's representation, carrying methods).  Modeled as a
   2-field record whose 2nd field is a `GoTypeTag` PHANTOM: extraction KEEPS that field, so Coq does
   NOT unbox the single value field, keeping the type a distinct method-receiver — the recurring
   single-field-unboxing wall beaten again (free here because a defined type needs no `Comparable`,
   same trick as the variadic wrapper).  The plugin registers a record whose 2nd field is a
   `GoTypeTag` as a defined-primitive-type and emits `type MyI64 int64` (NOT a struct — the phantom
   never renders), the ctor as the cast `MyI64(v)`, the value projection as `int64(x)`; methods are
   detected as usual (`func (m MyI64) Myi64_double() MyI64`).  The underlying is GENERIC (`pp_type` of
   the value field), so it works over a **string** too (`type Greeting string`, casts `Greeting(s)`/
   `string(x)`, `deftype_str_demo` → `Hi, fido`), and a defined type can **satisfy an INTERFACE**
   (`type Celsius int64`'s method `Reading` wired into a `Measurable` dictionary whose closure
   dispatches `c.Reading()` — behavioral satisfaction for a defined type; `deftype_iface_demo` → `120`).
   `deftype_demo` → `42`; all golden-locked, axiom-free.  **NAMED FUNC TYPES DONE (2026-06-19)** —
   `type Handler func(int64) int64` (the `http.HandlerFunc` idiom), a defined type whose underlying is
   a FUNC.  Needed a `TArrow` `GoTypeTag` constructor (for the phantom) — added with its `goarrow_cong`
   + arms in `tag_eq`/`zero_val`/`key_eqb` (two arrows equal iff domain+codomain tags agree; func zero
   is Go `nil`; funcs not comparable → `false` sentinel like slices), all axiom-free.  Plugin: the
   projection cast PARENTHESISES a composite (func) underlying and CALLS THROUGH it when applied —
   `func (h Handler) Handler_run(x int64) int64 { return (func(int64) int64)(h)(x) }` — so a method on
   the named func type calls the wrapped func; `mk_handler` → `Handler(f)`, `named_func_demo` → `42`.
   **SLICE underlyings DONE (2026-06-19)** — `type IntList []int64` (the `sort.Interface` `type ByLen
   []T` idiom): the underlying tag is the existing `TSlice`, no call-through, and a slice conversion
   `[]int64(l)` is valid Go WITHOUT parens (only `*`/`<-`/`func` need them), so `pp_cast_type` leaves it
   bare; the one fix was teaching `pp_type` to recognise the `GoSlice` NAME (a Fido `Definition := list`
   that a record field keeps unexpanded — parallel to `GoMap`/`GoChan`).  `func (l IntList) Il_len() int
   { return len([]int64(l)) }`, `deftype_slice_demo` → `3`.  *Not yet:* defined types as map KEYS (the
   phantom breaks equality), `Module`-namespaced method names.  **MAP underlyings DONE
   (2026-06-19)** — `type Counts map[string]int64`: `GoMap` is already name-recognised in `pp_type`
   (so no `GoSlice`-style fix needed), the ctor is `Counts(m)`, the projection cast `map[string]
   int64(c)` (valid Go without parens, like a slice).  `co_size` is an IO-VALUE-returning METHOD
   (`func (c Counts) Co_size() int { return len(map[string]int64(c)) }`) — it lowers now that
   `pp_io_body` `return`s a value-returning IO tail (see below); `gmap_deftype_demo` → `2`.  *Still
   pending:* defined types over a STRUCT underlying (mechanical).

   **IO-VALUE-returning methods/functions (`func … V`, V ≠ unit) — single-tail case DONE
   (2026-06-19):** `pp_io_body` emits IO as VOID statements (right for `IO unit`), so a value-
   returning IO function used to drop its `return` (uncompilable, caught by go build).  Now
   `pp_function`'s IO arm passes `~ret_val` (true iff the inner type ≠ unit) and `pp_io_body`
   `return`s the COMMON single-expression tail — `ret v` → `return v`, a clean value-read
   (`map_len`/`len`/`cap`) → `return <expr>`.  Zero-regression: only fires for value-returning IO
   functions (which were broken before); void IO funcs (`Describe()`) stay void-bodied.
   **BIND-CHAIN tail DONE (2026-06-19), no threading needed:** the key insight — the `pp_stmts`
   `ret` case is only ever reached at a TAIL (an intermediate `ret` is the action of a `bind`,
   emitted via `emit_m`), and a tail's `ret` argument is `tt` (unit) IFF the enclosing scope is
   void.  So `ret tt` → no statement (void func/goroutine), `ret <non-unit>` → `return v` (a
   value-returning IO function's tail) — the VALUE distinguishes the two, so no `ret_val` thread
   through the ~50 sites is required.  `co_sum` (two `map_get_or` comma-ok reads then
   `ret (i64_add a b)`) → `…; return a + b`; `gmap_deftype_demo` → `2 / 3`, golden-locked, void
   funcs unchanged.  *Still pending:* a bare value-OP tail INSIDE a bind chain (not wrapped in
   `ret`, e.g. `bind a (λ_. map_len m)` — rare; only the whole-body single-op tail is caught), and
   value returns through the run_blocks/goto structurer (exotic; bare `return`, loud-broken).

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
   **SINGLE-method interface DONE (2026-06-18)** — Coq UNBOXES a one-field record (`{m}` ≡
   `m`), erasing the struct.  Rather than the curried-return, we keep it a real dictionary
   by carrying the underlying value as an explicit SECOND field (`gr_self : GoAny`) — which
   sidesteps the unboxing AND is more faithful (a Go interface value IS a (method-table,
   value) pair, and it's consistent with our multi-method dictionary model).  `Greeter
   { greet : GoI64→GoI64 ; gr_self : GoAny }`, `mk_adder base` → method adds `base` +
   stashes it; dispatch `greet g x` → `(g).Greet(x)`; `single_iface_demo` → `15`.  No
   NoInline / extraction quirk (mirrors the `Shape` demo).  **NULLARY methods DONE
   (2026-06-19):** a `unit -> R` dictionary method (Go's `String() string`) lowers to the
   idiomatic nullary `func() R` — `pp_type` renders `unit -> R` as `func() R` and
   `pp_typed_closure` drops `unit`-typed params from the closure signature (the dispatch call
   already dropped the `unit` arg); `nullary_iface_demo` → `Stringer{ Sg_str func() string;
   … }`, `(Mk_namer("fido")).Sg_str()` → `fido`, `dispatch_str` machine-checked.  *Still
   pending:* a true 1-FIELD model (the curried-return work); and a true Go `interface{…}`
   keyword form (the vtable struct is the same semantics — Go's interface IS a vtable +
   erased value).
   This is the gateway to typestate / "an FSM can't compile to a broken transition"
   and behavioral-satisfaction proofs.

## Known gaps

### ⛔ RELEASE-BLOCKING soundness breaks (external review, 2026-06-21) — verified against source

**VERDICT (own it, do not let it drift): these proofs do NOT currently verify the generated Go.**
There are valuable verified COMPONENTS, but the bridge from those components to actual Go behaviour
has multiple independent soundness breaks.  The accurate headline is "verified components over
honestly-modelled Go primitives, bridge status documented per item" — NOT "verified Go".  Every break
below was CONFIRMED verbatim in the source (not taken on faith).  Close these in the order given before
any "verified" claim.

**Genuine soundness BREAKS (model ≠ Go, or an impossible premise — could let a false claim through):**
1. **The Keystone coding hypothesis is uninstantiable.** `Variable inj : nat -> GoI64; Variable prj :
   GoI64 -> nat; Hypothesis Hret : forall n, prj (inj n) = n` — but `GoI64 = {i64raw:Z; Squash(in_i64…)}`
   is FINITE, so `Hret` forces an injection from infinite `nat` into a finite type: NONE EXISTS.  So
   `denote_adequate`/`denote_adequate_mem` are conditional on a premise no implementation can meet (true
   implications, useless end-to-end); `mp_g0_denotes`/`mp_handoff_delivers` are quantified over `inj`/`prj`
   without `Hret`, so true even for nonsense codings → pin down no faithfulness.  THE TYPED↔OPERATIONAL
   BRIDGE DOES NOT CONNECT THE CALCULUS TO THE EMITTED GO.  Fix: finite domains (`Fin n`, or injectivity
   only over one execution's finite support).  (This is the "weak seam" of the architectural review, now
   shown to rest on an impossible hypothesis — strong evidence for refounding the bridge or path (b).)
2. **`map_size := 0` but Go `len` returns the real length.** `map_len` returns `map_size` (constant 0);
   plugin lowers `map_len`→Go `len(m)`; `map_demo` prints `3`.  Direct model/extraction disagreement.
3. **Session discipline forgeable.** `Record Sess (i j) A := MkSess { run_sess : IO A }` with public
   `MkSess` — `MkSess (ret tt) : Sess P PEnd unit` typechecks for ANY `P`.  Linearity is not enforced.
   Fix: seal `Sess` behind a module signature, or make constructors embody the protocol transitions.
4. **Evidence-carrying equality APIs carry NO evidence.** `ComparableW := {cw_eqb : K->K->bool}` and
   `struct_eqb (eqb) a b := eqb a b` — public constructors, no `forall x y, eqb x y = true <-> x = y`,
   both erase to native `==`.  `struct_eqb (fun _ _ => false) p p` = `false` in Rocq, `true` in Go.
   Fix: add the decidability field (SProp/erased) + seal the constructor.
5. **Allocation freshness asserted, never established.** Allocators use `w_next` with NO `ValidWorld`
   invariant (nonzero, > all live locs, no wrap).  "fresh"/"nonzero"/"disjoint" are comments, false as
   theorem-level claims over arbitrary `World`.  Fix: a `ValidWorld` invariant, loc 0 reserved.
6. **Nil aliases location 0; raw nil ops fabricate objects.** Nil chan/map/ptr = loc 0; send/close on
   nil chan, assign to nil map, write through nil ptr all "succeed" (Go blocks/panics), and all nils of
   a kind alias loc 0 (one bad write corrupts all).  (Nil-DEREF panic is in the excluded "nil/div"
   scope; nil-chan-block and nil-map-panic are NOT, and the aliasing is a representational break.)
7. **Runtime tag identity ≠ Go type identity.** `TInt64` tags Rocq `int`, `TI64` tags `GoI64`; both
   lower to Go `int64`, but `tag_eq` distinguishes them → a `TInt64`-boxed value asserted at `TI64`
   fails/panics in the model while Go's `int64` assertion succeeds.  Fix: one canonical runtime tag per
   emitted Go type, separate from proof-side carriers.
8. **`WfTrace` accepts malformed sync edges.** A `KStart` only needs its back-pointer to hit SOME
   `KSpawn c`; it never requires the started thread = the spawned child `c`.  So `[t0: KSpawn 1; t99:
   KStart 0]` is well-formed → a forged sync edge that can "prove" a race absent.  `sync` inspects only
   the target event's number, not the source.  Fix: make source-kind/channel/child intrinsic to `sync`.
9. **`complex_div` wrong on finite values.** Replaces Go's `abs(re)>=abs(im)` with a SQUARED-magnitude
   compare → overflow/underflow.  Counterexample `1+2i / 1e307+1e308i`: Go ≈ `2.08e-308 - 7.9e-309i`,
   model `0 - 0i`.  The "faithful for all finite" claim is false.
10. **UTF-8 model is not a decoder.** `str_to_runes` picks width from the first byte and masks the rest
    with no validation (continuation prefixes, overlong, surrogates, >MaxRune, invalid leads).  `0x80
    0x41` → one 2-byte seq → `U+0001`; Go → `U+FFFD` then `A`.  `rune_bytes` emits surrogates/out-of-range
    directly (Go substitutes `U+FFFD`).  Golden tests only exercise VALID input.

**Overclaimed labels on true theorems (re-scope the words, the proofs are fine):**
- "full/whole state refinement" — `WMatchC` compares only buffers (not closed-state/cap/nil); on close
  the World is unchanged, so a closed operational channel "refines" an open World channel.
- "the Go happens-before relation" — `hbt` omits the unbuffered recv→send-completion edge and the
  cap-based k-th-recv→(k+cap)-th-send edge.  It is a CONSERVATIVE SUBSET (so `hbt`-race-free ⇒ Go-race-free
  for race-freedom, sound-but-incomplete), but it is NOT the Go hb and cannot do exact bounded-channel claims.
- "deadlock-freedom for Go" — the main `rstep` is UNBOUNDED-ASYNC (`rstep_send` always appends, no cap, no
  full-buffer/rendezvous block); results are about that calculus, not Go's bounded/rendezvous channels.
- `RStuck` conflates PANIC and DEADLOCK (both = can't-step ∧ not-done); `rpanicking` is post-hoc, there is
  no panic transition/terminal.  Fix: explicit `Done`/`Panicked v`/`Running`.
- The `∃ cfg, rsteps … ∧ TraceRaceFree` examples (`fork_exec`, `chan_pub_exec`, the old `mp_exec`) prove ONE
  safe schedule, not program race-freedom.  *(`mp_all_interleavings_race_free` / `mp_reachable_owned`
  (2026-06-21) now give the ∀-over-reachable + Owned-INVARIANT version FOR mp — but only mp, still over the
  unbounded calculus, still unbridged to Go.)*

**Documented idealizations that nonetheless must NOT slide into a "correctness" theorem:** unbounded
channels; `defer_call` no-op; `go_spawn` sequential, discards child panics; `run_blocks` 1000-step cutoff;
panic-value-as-`unit` (so `catch` can distinguish it from Go's runtime panic value); `zero_val TArrow` is a
callable function (Go's zero func is nil, panics); `GoArray` erases length (different-length arrays
comparable); `SliceH` public ctors with no `off≤len≤cap` invariant (raw indexing reads arbitrary heap);
append-realloc fixes `cap=len+1` (Go may pick larger); `FConst` permits zero denominator (Go: compile error);
`key_eqb` treats maps as comparable by location (Go maps comparable only vs nil).

**Genuinely good (per the reviewer):** `Outcome` instead of arbitrary postcondition; the monad laws from the
concrete `IO`; the fixed-width integer arithmetic + boundary witnesses; `hbt` irreflexivity under `WfTrace`;
the rich nondeterministic `select`; closed-and-drained receive; the bounded-channel fragment (right direction,
honestly flags the main calculus's limit); the emitted Go builds/vets/runs cleanly under Go 1.23.

**REPAIR ORDER (do not extend the bridge until these close):** (1) seal `Sess`/`ComparableW`/`struct_eqb`/
handle constructors + every invariant-carrying ctor; (2) `ValidWorld` invariant (loc 0 reserved, genuine
freshness, no wrap/collision); (3) real nil blocking/panic; (4) canonical runtime tag per Go type; (5)
finite domains for the Keystone coding; (6) integrate cap/closed/nil/panic into the authoritative state;
(7) strengthen `sync` validity + prove safety UNIVERSALLY over reachable executions; (8) full-state
refinement; (9) **differential-test every primitive vs Go on adversarial edges** (malformed UTF-8, extreme
complex, NaN map keys, slice bounds, panic/recover) — the missing discipline (golden tests only hit valid input).

### Architectural seams & the strategic fork (external review, 2026-06-21)

A global-altitude review (vs. the slice-local loop view) named the real seams.  Most are tracked
piecewise below / in SPEC_CONFORMANCE / under limit #2; the value here is the UNIFYING diagnosis +
the strategic fork.  Recorded so they steer work rather than live in chat.

1. **TWO SEMANTICS, ONE WEAK SEAM — the root.**  `run_io : World -> Outcome` is TOTAL (blocking /
   divergence / OOM idealized away: a recv on an empty-open channel returns zero, `go_spawn` runs
   sequentially) BECAUSE it is the EXTRACTION target — a deterministic `World->Outcome` that lowers to
   sequential Go the runtime then schedules.  Blocking can't be a *value* in a total function, so ALL
   liveness is exiled to the operational calculus (`rstep`, blocking = no-step = `RStuck`).  The split
   is the idealization made architectural.  CONSEQUENCE: the concurrent end-to-end guarantee is
   PROSE-GLUED — `denote_adequate` is single-goroutine / single-channel / frame-free; multi-goroutine
   adequacy is the deferred capstone (limit #2 slice 2c).

2. **The trust base mirrors the model split — "axiom-free" must not drift.**  Honest headline = ZERO
   *Fido* axioms; external trust base = `PrimInt63`/`PrimFloat` (computational primitives) +
   `functional_extensionality` (logical holdout #1).  funext lives almost entirely in the IO/World
   layer (`run_io_inj` IS funext); the operational-calculus proofs (`mp_exec`, `det_select_*`, `le1`,
   the `MpReach` bricks…) are genuinely "Closed under the global context" — no axioms, not even funext.
   So: calculus = axiom-free but proof-only; IO model = extracts but needs funext.  The weakest link
   (the bridge) is exactly where the two regimes meet.  DISCIPLINE: per-theorem claims stay precise
   (verify via `Print Assumptions`); the AGGREGATE headline is "axiom-minimal, funext holdout #1".

3. **Bespoke-ness — root cause is no GENERIC RECORD REFLECTION.**  `StructRep2/3/2H` are symptoms of
   hand-rolling per-arity / per-representation isos because Coq gives no "for any Record, its product /
   Go-struct view" generically.  Principled fix = datatype-generic deriving (a real research lift; Coq
   record reflection is weak).  Same shape: the two slice models don't unify — `SliceH` (heap) is the
   faithful Go-reference-type one, `GoSlice = list` the convenient pure view, no subsumption theorem.
   Multiplies as coverage grows (StructRep4, 5…) until reflection collapses it.

4. **Select is the microcosm — its gap = the capstone gap.**  The composed `select_recv2`(World) →
   `rstep_select`(operational) theorem is argued, not a lemma — AND it is literally a SPECIAL CASE of
   multi-goroutine adequacy.  So the select cross-model gap and the adequacy capstone are ONE gap, seen
   through the most-used construct.  (Select's INTERNAL story is well-closed — soundness bug found+fixed,
   sound/incomplete/complete-under-uniqueness — because that lives inside ONE model.)

5. **THE STRATEGIC FORK (sit with this before committing).**  The IO/World model earns its keep ONLY as
   the extraction target.  Two routes to one closed end-to-end concurrent theorem:
   - **(a) Bridge the split** (current path): keep two models, build multi-goroutine adequacy (limit #2
     2c).  Incremental; skeleton exists (`Denotes`, `reachable_refines`); preserves working extraction.
     Bet: the bridge is closable.
   - **(b) Eliminate the split** (the DEEP limit #2 = "carry typed values IN the calculus"): make the
     TYPED `Cmd`/`rstep` calculus the SINGLE model AND extraction source.  `Cmd` is already a program AST
     whose ops extract (`CSend`→`ch<-v`, `CRecv`→`<-ch`, `CSpawn`→`go`, `CSelect`→`select`); Go's runtime
     IS the resolver of its nondeterminism (faithful — Go `select` IS nondeterministic).  `run_io`
     demotes to a DERIVED single-schedule denotation; likely funext-free.  Massive refactor (retarget
     extraction), bets the extraction story.
   TRIGGER: stay on (a) for now.  The capstone is the TEST — if multi-goroutine serialization closes
   cleanly, the split was fine; if it fights back, the split WAS the problem and (b) is the answer.  Do
   NOT start (b) without an explicit decision.

### Construct-layer completeness assessment (2026-06-19, grounded survey)

A direct survey of the committed code (NOT the drifted "still pending" notes, which had
mislabelled ~6 done features — see ladder item 1) finds the **Go language-construct layer
essentially complete**.  Verified present + extracting:

- **Numerics — COMPLETE.** Every type (`uintN`/`intN` N≤32, `int64`, `uint64`, `float64`,
  `float32`, `complex128`); all arithmetic / bitwise / shift / comparison; the full conversion
  matrix incl. both `float↔int64` and `float↔uint64`; `min`/`max` (Go 1.21).
- **Composite + nominal types — COMPLETE.** Slices, maps, arrays, strings (byte + rune view),
  value/heap structs (2/3-field, heterogeneous, nested, embedding/promotion), defined types.
- **Methods + interfaces — COMPLETE.** Value/pointer receivers, method values/expressions,
  IO methods; interfaces of ALL arities (single via `gr_self`, nullary, ≥2-method), dynamic
  dispatch, `any`/`interface{}`, type switch/assertion, closures capturing locals.
- **Concurrency CONSTRUCTS — present + extracting.** Buffered channels, `go_spawn` → real
  `go func(){…}()`, `select` → Go `select{…}`.  (The deep race/deadlock GUARANTEE — tying
  happens-before to the operational semantics — is the open research layer, not a construct gap.)
- **Generics — present** with `any` constraint (generic funcs + structs, multi-instantiation).
- Control flow / IO monad / panic-recover / defer / typestate — done.

**The genuine remaining frontier (no-import):**
1. *Generic `comparable` constraint* — **DONE (2026-06-19).**  The witness-erasure mechanism
   shipped: `ComparableW K` (a record carrying `cw_eqb`, distinct from the ambiguous `GoTypeTag`)
   is computational in Rocq (so `ceq_i64`/`ceq_str` witnesses `vm_compute`) but the plugin ERASES
   it — `collect_decls` pass 3 records each function's `ComparableW (Tvar)` param indices, which
   are dropped at the declaration (`render_pairs` filter) AND every call site (the
   `comparable_witness` drop arm), the type var is emitted `[K comparable]` (not `any`), and
   `cw_eqb w a b` lowers to native `a == b`.  Result: `func Ceqb[T1 comparable](a, b T1) bool {
   return a == b }`, instantiated at `int64` AND `string` (`Ceq_i64`/`Ceq_str` drop the witness,
   Go infers K); golden-locked, axiom-free, no witness struct leaks.  **Generalised (2026-06-19):**
   the witness-instance suppression is now a `collect_decls` registry (any `ComparableW`-typed def
   is auto-suppressed — no per-instance plugin edit), and `ceqb` is exercised over EVERY Go
   comparable kind — `int64`, `uint64`, `string`, and a STRUCT (`Point`, field-wise `==`) — all
   lowering to the one `Ceqb[K comparable]`; `comparable_demo` → `true true false true`.
   *(Interface-typed constraints — a generic over `K` bounded by a method set — would reuse the
   same erasure with the dictionary record in place of `ComparableW`; the open subtlety is name
   alignment between the dict field, the emitted `interface` method, and the concrete method.)*
2. *Untyped constants* (Go's arbitrary-precision, default-typed literal system) — foundational.
3. *Enum `==` / enums as map keys* — idiomatic `==` needs plugin recognition (enums are Rocq
   inductives, no int projection); a nested-match `eqb` is faithful but non-idiomatic.
4. *Reference-type aliasing* (maps/slices share backing state) — heap-model depth.
5. *The concurrency guarantee* (happens-before ⇒ race/deadlock freedom over the real step
   relation) — the research north-star, multi-tick proof work.

Net: the project is far closer to "complete sans imports" than the loop framing implied — the
bulk of remaining work is these named corners plus the concurrency proof, not missing builtins.

### Channel-payload faithfulness — what composes vs. the two real limits (2026-06-20)

Probing (a code-review thread) how faithfully channels compose as first-class values.
**What WORKS — channels are first-class values (handles), so they compose freely:**
- *Channels of channels of channels …* (any depth): `TChan : GoTypeTag A → GoTypeTag (GoChan A)`
  is recursive, `send`/`recv`/`select_recv2`/`chan_buf` are `{A}`-polymorphic, and the channel
  cell stores its element type existentially (`existT E (etag,(buf,cl))`) with a tag-checked read —
  so `GoChan (GoChan (GoChan A))` is typed and sound; `tag_eq`/`zero_val` already recurse through
  `TChan`.
- *Channels captured in a lambda / goroutine closure*: a `GoChan A` is a value, captured like any
  other; `go_spawn (send ta ch v)` → `go func(){ ch <- v }()` (main.v:1016), and `go`/`defer`
  closures capture by VALUE (sidestepping Go's loop-variable gotcha).
- *Channels in struct fields, returned, passed/aliased*: fine — a struct with a `GoChan` field is
  an ordinary value; a returned/shared channel handle is the same handle (reference semantics).

**Limit #1 — RESOLVED for BOTH structs and pointers (2026-06-21).**
- *Structs:* DONE via `TProd` — a struct rides a channel / `any` / map as its canonical PRODUCT
  backing (marshalled by its `StructRep` iso, extracts to the native named Go struct).
- *Pointers:* DONE via **`TPtr`** (2026-06-21) — `Ptr A` was REDESIGNED tag-free (a phantom
  `{p_loc:int}` handle beside `GoChan`/`GoMap`; the pointee tag lives in the world `RefCell`, and the
  deref ops `ptr_get`/`ptr_set`/`ptr_as_ref` take the `GoTypeTag` explicitly).  That breaks the
  universe cycle (a tag-CARRYING `Ptr` made `GoTypeTag (Ptr A)` inconsistent), so `GoTypeTag` gains
  `TPtr : GoTypeTag A -> GoTypeTag (Ptr A)`, with `tag_eq`/`tag_coerce`/`zero_val`/`key_eqb`/`Tagged_ptr`
  cases and the plugin rendering `*T` (by type, like `chan T`).  Now a `*T` is a first-class channel
  payload / `any` box / map element: witness `ptr_chan_demo` — `p := new(int64)←7`, `ch <- p`,
  `q := <-ch` (aliases p), `*q = 7` — emits idiomatic `make(chan *int64,1)` / `ch <- p` / `<-ch`,
  prints `7`.  Axiom-free (trust base only), golden-stable.  *Still ✗ (niche):* embedding a non-struct
  type, and `*T` to a struct whose `GoTypeTag` is product-backed only.
2. **The rich typed channel values and the now-correct concurrent select live in DIFFERENT
   layers.**  The typed sequential `IO`/`World` model carries arbitrary typed payloads (nested
   channels, struct fields, closure captures, aliasing `Ptr A` pointers via `ptr_get`/`ptr_set`);
   the operational `step`/`rstep` calculus — where nondeterministic choice + blocking-as-`Stuck`
   were just proven (`select_nondeterministic` / `sel_block_stuck`, 2026-06-20) — carries UNTYPED
   `nat` values/locations.  So there is no *end-to-end* "concurrent select over a channel of
   structs / nested channels", nor a typed "pointer sent over a channel, pointee mutated,
   race-freedom guaranteed".  *The bones exist on the operational side:* shared-memory
   `KWrite`/`KRead`, `TraceRace` (cross-goroutine conflicting accesses unordered by happens-before),
   and `owned_race_free : Owned t → TraceRaceFree t` — the worked `mp_trace` is exactly
   "write a location, hand off over a channel, read it": the send→recv orders the accesses, so it is
   PROVEN race-free, and dropping the sync makes it a representable `TraceRace`.  What is missing is
   the bridge: the race model is over untyped `nat` locations, not the typed `Ptr A` / `GoChan`.
   *Fix:* carry typed values/locations in the operational calculus (or a refinement relating the
   two) — the same typed-sequential ↔ operational bridge the goto-substrate unification (ladder
   item, ref. Known gaps #10) targets.
   **SLICE 1 DONE (2026-06-21) — typed pointers ARE the calculus's locations.** `concurrency.v`
   `Section KeystonePtr`: the operational memory steps `rstep_write`/`rstep_read` are simulated by the
   EXTRACTABLE Go-pointer derefs `ptr_set`/`ptr_get` (what the plugin emits as `*p = v` / `*p`), so a
   calculus `nat` location `l` is a genuine runnable `*T` cell — the pointer `ptrenv l`. The deref ops
   are DEFINITIONALLY the Keystone's ref-accesses at `ptr_as_ref` (`ptr_set_is_ref`/`ptr_get_is_ref`),
   so read-after-write + aliasing transfer with no new heap/axiom; `ptr_write_sim` (IO world advances
   as `upd h l v`, cell-match preserved), `ptr_read_sim` (reads the coded heap value), `ptr_write_read`
   (typed cell coherent). Substrate base only (PrimInt63/PrimFloat, no funext, no Fido axiom),
   proof-only ⇒ golden-stable. So `mp_trace_race_free`'s guarantee is now known to concern a real `*T`,
   not an abstract `nat`. **SLICE 2a DONE (2026-06-21) — `mp_trace` is GENERATED by a real execution.**
   `mp_exec_trace`: the two-goroutine pointer-handoff program (g0 writes loc 0 then sends ch 0; g1 recvs
   then reads loc 0, both pre-live) STEPS to exactly `mp_trace` (`rsteps (mp_init v0 v1) cfg /\ rc_trace
   cfg = mp_trace`); `mp_exec_race_free` ⇒ that run is `TraceRaceFree`. So slice-1's identified location
   is grounded in an actual program run, not a hand-written literal. Both Closed-under-global-context
   (fully axiom-free). **SLICE 2b DONE (2026-06-21) — mp_prog's goroutines DENOTE a typed program.**
   `Section MpTyped`: each goroutine of `mp_prog` (slice 2a's race-free program) is the Keystone-
   denotation of an EXTRACTABLE typed IO program — `mp_g0_io = *p=v0; ch<-v1`, `mp_g1_io = <-ch; _:=*p`
   (`mp_g0_denotes`/`mp_g1_denotes`), the memory ops being the genuine `ptr_set`/`ptr_get` (pointer-
   backed `locenv`, slice 1). So the race-free execution is the operational image of real typed pointer-
   over-channel code. Substrate base, proof-only. **VALUE-CORRECTNESS companion (2026-06-21):**
   `mp_handoff_delivers` — the extractable typed program run in `run_io` DELIVERS exactly `(inj v1, inj v0)`
   (g1 receives v1 over the channel AND reads v0 back through the pointer; pointee survives send+recv via
   the channel/heap World frames). So the program is not only race-free (2a) but COMPUTES the right values
   end-to-end. **CROSS-MODEL AGREEMENT (2026-06-21):** `mp_exec_state` — the operational handoff outcome
   (`rc_heap cfg 0 = v0`: g0's value survived the handoff and g1 read it; channel drained) MIRRORS the
   typed `mp_handoff_delivers` (`inj v0`): both models compute the same outcome `v0`/`inj v0`, axiom-free.
   **MEMORY ADEQUACY (2026-06-21):** `denote_adequate_mem` — the Keystone's `denote_adequate` was
   channel-only; added its HEAP analogue (`OnLoc`/`SimInvMem`/`WHMatch1`, reusing `denote_sim_write`/
   `_read`): a single-goroutine write/read program run to `CRet` has its `run_io` denotation complete at
   a world whose cell matches the calculus heap. Both single-goroutine adequacy halves now exist
   (channel + heap), substrate-base, proof-only. *Slice 2c (DEFERRED — multi-tick):* the COMBINED
   multi-goroutine ADEQUACY = a proven SIMULATION between the interleaved `rstep` execution and the
   typed `run_io` (combine channel+heap with cross-frames, then generalise to N goroutines) — the ONE
   closed end-to-end theorem. Assessed
   hard: SimInv is fundamentally single-goroutine (its sequential `run_io` invariant has no analogue for an
   interleaving without a serialization argument); a dedicated effort, not a clean tick. The per-model
   facts (safety, denotation, value-correctness, cross-model agreement) already tell the story side-by-side.
   *N-generality
   (user asked 2026-06-21):* the GUARANTEE already generalizes — `reachable_owned_safe_r` quantifies over
   arbitrary programs (N goroutines via spawn) and all interleavings; these witnesses are concrete
   instances, and the open seam for full N is program-structure-discipline ⇒ race-free with dynamic spawn.

---

Audit (2026-06-13 sweep) of the partial/unsafe primitives against the
safe-by-construction principle. Tracked until closed.

**Fail-loud policy (the meta-invariant).** No unmodeled construct may extract to
plausible-but-wrong Go. The plugin's `unsupported what` helper raises a
`CErrors.user_err` (aborting `make extract`) for every case it cannot lower —
the catch-all in `pp_expr`/`pp_atom`, an unhandled `MLcase` shape in statement
position, a non-literal `print`/`println` arg list, an unmodeled constructor
(`MLcons` that is not nat/bool/list), a `map_get_opt` result not immediately
matched, and a `Tglob` type that is not a registered record (no struct decl
emitted — the single-field-record-unboxing dangling reference, 2026-06-18).
Previously these emitted `nil /* TODO */` / `panic("unhandled match")`,
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
2. **Integer model** — *RESOLVED: migrated to full-width `GoI64` (A4.3, 2026-06-17)*.
   The canonical Go `int64`/`uint64` are now `GoI64`/`GoU64` (`Z`-carried, faithful
   across the whole 64-bit range, wrapping at the true 2⁶³); `2 - 5 = -3` is
   `neg_demo` (`i64_sub`), overflow-freedom is the THEOREM `i64_add_no_overflow_exact`
   (no-overflow → exact, axiom-free), and the evidence-carrying `i64_add_nz`/`sub_nz`/
   `mul_nz` are the guarded forms.  ALL int64 VALUE arithmetic + value/payload/struct
   demos use `GoI64`; the old Sint63 VALUE-overflow theory (`add_nz`/`no_overflow_*`/
   `*_no_overflow_exact`/`sub_signed_matches_go`/`add_wraps_at_boundary`) was REMOVED.
   The primitive `Sint63` `int` survives ONLY as **index arithmetic** — loop counters
   and computed slice indices (`sub 0 1`), the Go `int` index type — with its signed
   `+`/`-`/comparison (`Sint63.ltb` → Go `<`; `ltb_signed_neg_true` still justifies it).
   **Coq `nat` (≠ `int`) is mapped to Go `uint`**, used mainly for compile-time
   indices (e.g. `run_blocks` block labels); runtime integer math is `int`
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
5. **Untyped constants** — *integer VALUES DONE + exhibited (2026-06-19); constant
   EXPRESSIONS and the float side open.*  Go literals are untyped + arbitrary-precision; a
   constant gets a type — with a compile-time REPRESENTABILITY check — only at use.  Fido's
   typed-literal-with-fit-proof IS that model: the literal's argument is an exact `Z`/`uint63`
   VALUE and the `eq_refl` fit-proof is Go's representability check.  `uconst_demo` (main.v)
   exhibits it: a >32-bit value at `int64`; the SAME `100` typed at both `int64` AND `uint8`
   (one constant, many types); and overflow REJECTED at compile time — `in_i64 (2^63) = false`
   and `300 <? 256 = false`, so the literal cannot be built and the unsafe Go never extracts
   (`uc_i64_overflow`/`uc_u8_overflow`).
   - *Constant EXPRESSIONS — DONE (2026-06-19).*  The plugin's `z_eval` folds a closed `Z`
     expression — `Z.add`/`sub`/`mul`/`opp`/`shiftl`/`land`/`lor`/`lxor` of constants — to its
     int64 value, so `i64_lit (Z.shiftl 1 40 + 5)` / `(1<<20)-1` / `10^6 * 10^6` now extract
     (`uc_bignum`/`uc_mask`/`uc_product` → `1099511627781 1048575 1000000000000`).  Faithful to
     Go's ARBITRARY-PRECISION constant fold via checked int64: every op detects overflow and
     fails LOUD (an intermediate exceeding int64 — e.g. `(1<<62)+(1<<62)-(1<<62)` = 2^62, fits,
     but the `+` overflows — is rejected, never silently wrapped).  *(A bignum folder would also
     ACCEPT such over-int64-intermediate constants; the checked-int64 form instead bounds them
     fail-loud, which is faithful-or-fail, not wrong.)*  `u64_lit` expressions fold too (2026-06-19,
     `zu_eval` — same ops with UNSIGNED overflow checks via `Int64.unsigned_*`; `uc_u64_hi` = `1<<63`
     = 9223372036854775808, beyond int64 max, and `(1<<32)-1`).  So INTEGER constant expressions are
     complete for both signed and unsigned int64.  Remaining: float-side below.
   - *Float side — MODEL DONE (2026-06-19), lowering deferred.*  Go does constant float arithmetic
     at arbitrary precision, rounding ONCE at the typed boundary (`const 0.1 + 0.2 = 0.3`), whereas
     runtime `float64` rounds each step (`0.30000000000000004`).  Modeled: `FConst` = an exact
     rational `num/den`; `fc_add`/`fc_sub`/`fc_mul`/`fc_div` are EXACT (cross-multiply, no rounding);
     `f64_of_fconst` rounds to `float64` exactly once (IEEE divide of the two integer endpoints,
     correctly-rounded while `|num|,den < 2^53`).  Machine-checked: `fconst_exact`
     (`(1/10)+(2/10) → 0.3`), `fconst_runtime` (runtime `0.1+0.2 ≠ 0.3`), `fconst_mul`
     (`(3/2)·(1/4) = 0.375`).  **LOWERED (2026-06-19):** the plugin's `fc_eval` folds the FConst
     expression to its `(num, den)` (checked int64, overflow + `≥2^53`-endpoint = fail-loud) and
     emits `(float64(num) / float64(den))`, which Go RE-FOLDS at compile time to the same
     correctly-rounded constant; `fconst_demo` → `(float64(30)/float64(100))`,
     `(float64(3)/float64(8))` → `+3.000000e-001 +3.750000e-001` (0.3, 0.375), golden-locked.  So
     untyped float constants are now done model + proof + lowering — the last real faithfulness gap
     closed end-to-end.  (A decimal `Number Notation` so `0.1` parses straight to `1#10` is the
     only polish left — currently the rational is written `mkFC 1 10`.)
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
`i64_add_no_overflow_exact` depends on **none** of the IO/session axioms (it is
axiom-free — only `Z` inductives + `lia`), so the overflow result is independent of
the whole Go-axiom trust base. The `Fail`-test build gate proves the negative cases
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
2. **Joint consistency — CLOSED (2026-06-18): there is no Fido axiom set.**  The
   "better" fix the original entry called for ("replace axioms with definitions where
   possible so consistency is by construction") is DONE across the board.  The whole
   IO / channel / session / map / slice / `zero_val` model is now `Definition`s over a
   concrete `World` (`{ w_refs ; w_chans ; w_maps ; w_next }`) and `Outcome`, so every
   law is a derived theorem — vacuity is impossible without inconsistency in Rocq's own
   kernel.  Verified by `Print Assumptions main_effect`: the trust base is EXACTLY Rocq's
   `int`/`float` primitives, zero Fido axioms (see "axiom discipline" above).  *Residual,
   narrower:* the two `concurrency.v` section hypotheses (the calculus↔IO coding round-
   trip) — proof-only, parameterised, not in any extracted program; discharging them with
   a concrete coding is the remaining bridge nicety (Tier 1 #1's keystone), not a
   consistency risk.
3. **Lowering correctness is unproven (the plugin is trusted).**  ~1500 lines of
   OCaml (incl. the relooper) translate Rocq→Go with NO theorem relating the
   emitted Go to the source term; golden tests cover only finitely many
   trajectories.  (See Known gaps #10.)  *Fix:* an operational semantics for the
   Go fragment in Rocq + a simulation/refinement proof — start with straight-line
   IO, then control flow, then channels.  **FIRST SLICE LANDED (2026-06-21,
   `relooper.v`, proof-only):** the CONTROL-FLOW core — a CFG (basic blocks +
   conditional gotos) with a big-step operational semantics `cfg_halts`, a
   structured target (if/seq + `LLoop`/`LBreak`) with its semantics, and TWO
   semantics-preservation theorems: `diamond_realized` (acyclic — the if-diamond
   lowered via compositional `Realizes` combinators) and `while_realized` (CYCLIC
   — the canonical while-loop CFG with a back-edge lowered to `loop { … break }`,
   proved by induction on the `cfg_halts` derivation / loop-iteration count).
   Plus the GENERAL ACYCLIC case, NO-duplication: a run-to-a-LABEL semantics
   `runs_to` and the key `runs_to_halts` (region-reaches-join ∘ join-reaches-HALT
   is UNCONDITIONAL — the second leg is terminal, dodging the join-revisit hazard
   that makes naive join-to-join composition unsound), giving compositional
   combinators (`realize_seq`/`realizeTo_goto`/`realizeTo_if`) and `diamond_general`
   (the diamond re-lowered with the join emitted ONCE) — the per-step soundness an
   arbitrary acyclic relooper is built from.  All axiom-free.  It is a REFERENCE
   model (does NOT verify the OCaml plugin — that needs reflecting the OCaml), but
   it proves the transformation CAN be verified, supplies the method, and is a spec
   to check the plugin against.  The acyclic relooper now also exists as an
   ALGORITHM: `reloop fuel g l` (fuel-bounded ⇒ total without a well-founded order;
   `None` on a cycle/out-of-fuel, `Some S` otherwise) with SOUNDNESS `reloop_correct`
   (every `Some S` realizes the CFG), exercised end-to-end by `diamond_reloop_correct`
   (the function COMPUTES the diamond's lowering, certified correct).  And
   COMPLETENESS (`reloop_complete`/`reloop_total_correct`): a `Ranked g rank` witness
   (a measure that strictly drops along every edge = acyclicity) gives fuel
   `rank l + 1` that SUCCEEDS — so on any acyclic CFG `reloop` is TOTAL ∧ SOUND ∧
   COMPLETE (`diamond_reloops` instantiates it).  Still open: folding LOOPS into the
   function (the loop CORE is proved separately as `while_realized`), and connecting
   to the emitted Go AST.

   **DEFERRED ARCHITECTURE — "verified relooper, extracted, plugged in" (PUNTED below
   built-ins/imports; the golden file is sufficient for now).**  The eventual way to
   turn `relooper.v` from a *reference* model into an actual guarantee, decided
   2026-06-21: do NOT try to verify the existing OCaml (that needs reflecting ~3000
   lines).  Instead, CompCert-style — (1) PORT the lowering (relooper + term→Go-AST)
   into Rocq, transcribing the existing OCaml as the reference; (2) PROVE it
   semantics-preserving (relooper.v is the control-flow seed); (3) EXTRACT the Rocq
   lowering back to OCaml via Rocq's own (trusted) OCaml extractor and have the plugin
   CALL it; (4) LEAVE the Go-AST→text printer as trusted OCaml — the irreducible
   print/parse boundary every verified compiler keeps axiomatic (CompCert trusts its
   asm printer).  During the port the existing OCaml lowering pulls double duty: the
   spec to transcribe AND a DIFFERENTIAL-TESTING oracle (run both, diff the emitted Go
   over the whole golden suite; any mismatch is a transcription bug).  Per *Reflections
   on Trusting Trust*: this MINIMISES the trusted base, never eliminates it — after the
   work you still trust Rocq's term→MiniML extraction, the MiniML→Rocq-mirror glue,
   Rocq's OCaml extraction, and the printer.  What you buy: the relooper (the most
   intricate, golden-only-sampled transform) becomes a THEOREM.  Scope when picked up:
   "verified relooper, extracted, plugged in" then STOP — porting the straight-line
   cases is low-risk tedium; leave the rest of `go.ml` trusted-but-golden-tested.
   Smallest non-throwaway first step: pin the Go-AST type in Rocq + a `Stmt → GoStmt`
   print-to-AST function, connecting `relooper.v`'s `Stmt` to what the printer consumes
   (the seam between reference model and extractable lowering).  ORDER: only after the
   no-import built-in layer (and then imports) lands; this is a multi-week build, not a
   loop tick.

### Tier 2 — numeric correctness within the int/float parameters
4. **`int` is ±2⁶², not full int64 — *RESOLVED: `GoI64`/`GoU64` are the canonical
   full-width int64/uint64; primitive `int` kept as a bounded convenience*.**  The
   63-bit primitive `int` (Sint63) is one bit short of int64, so its wrap boundary
   differs from Go's.  *Fix delivered for signed int64:* `GoI64`, a distinct record
   carried by **`Z`** (not `int`),
   normalised mod 2⁶⁴ into the signed range after every op (`wrap64`).  Faithful
   across the WHOLE int64 range and wrapping at the true 2⁶³ — `spec_i64_add_wrap`
   (2⁶³−1+1→−2⁶³), `spec_i64_beyond62` (a sum unrepresentable in the old ±2⁶²
   model), `i64_add_no_overflow_exact` — all **axiom-free** (`Print Assumptions` =
   *Closed under the global context*).  Erases to a Go `int64` (wraps natively at
   2⁶⁴, so the emitted op is bare `a + b`, no mask); the `Z` arithmetic helpers
   extraction drags in (`Z.modulo`/`CompOpp`/…) are proof-only and suppressed by
   module, never emitted.  *Bounded caveat:* a CONSTANT `MAX+1` in extracted Go hits
   Go's untyped-constant compile-time overflow check (a compile error), not the
   runtime wrap `i64_add` models — that is Tier 2 #6 (untyped constants), and the
   wrap is faithful for runtime operands / witness-proven.  **`GoU64` — unsigned
   full-width uint64 — DONE (A3, 2026-06-17):** same Z template, unsigned mod-2⁶⁴ wrap
   (`wrapU64`), all ops (arith/compare/div/mod/bitwise/shifts/not); plugin emits
   `uint64` type (exception to the `int64`-default numint erasure) and unsigned decimal
   literals; witnesses `spec_u64_add_wrap`/`sub_wrap`/`not`/`shr`/`beyond63` all
   axiom-free.  **A4 (default-int migration) DONE (2026-06-17) — `GoI64`/`GoU64` are
   now THE canonical Go `int64`/`uint64`:** (A4.1) the concurrency.v bridge value
   carrier migrated `int`/`TInt64` → `GoI64`/`TI64` (mechanical — the bridge uses only
   polymorphic IO laws; axiom-free preserved, `Print Assumptions` unchanged), so the
   modeled channel/heap values are full-width; (A4.2a) `Notation int64 := GoI64` /
   `uint64 := GoU64` + range-checked `Number Notation` (`42%i64`/`42%u64`, out-of-range
   numeral REJECTED at parse = Go's untyped-constant overflow; `i64_lit_oob`/
   `u64_lit_oob` `Fail`) + scoped arithmetic (`(a+b)%i64`); (A4.2b) `comparable_TI64`/
   `comparable_TU64` (int64/uint64 map keys) + end-to-end pipelines flowing int64 and a
   `≥2^63` uint64 through a typed channel AND map (`i64_pipeline_demo`/
   `u64_pipeline_demo`, golden-locked).  The plugin renders an erased full-width
   literal sign-aware (a `Zpos` whose 64-bit pattern is negative-as-`Int64` is a
   `uint64 ≥ 2^63` → `%Lu`; else signed) and pins bare literals in typed slots via the
   value tag (`pp_typed_lit_tagged`).  **A4.3 (2026-06-17) completed the migration:**
   ALL int64 VALUE demos (channels, maps, sessions, conditionals, structs/methods/
   interfaces/typestate/repinv, slices, arithmetic) were converted to `GoI64`/`%i64`,
   and the Sint63 VALUE-overflow theory removed.  The primitive `Sint63` `int` now
   survives ONLY as **index arithmetic** — loop counters and computed slice indices
   (the Go `int` index type) — plus `nat`-coding and `go_min`/`go_max` (the min/max
   builtin demo).  All conversions were golden-IDENTICAL (`GoI64` and `int` both lower
   to Go `int64`).
5. **Overflow-safe arithmetic — DONE, at the FULL int64 width (`GoI64`, A4.3).**
   `i64_add_nz`/`i64_sub_nz`/`i64_mul_nz` are evidence-carrying: each demands a proof
   the exact result is representable (`i64_no_overflow_{add,sub,mul}` = `in_i64
   (exact) = true`, discharged by `eq_refl` for concrete operands — a decidable bool
   equation, cleaner than the old `now vm_compute`), then extracts to the raw machine
   op, exact by `i64_{add,sub,mul}_no_overflow_exact` (axiom-free).  Raw `i64_add`/
   `sub`/`mul` remain the opt-in WRAPPING forms.  `overflow_safe_demo` prints
   `3000000000000 1000000` (proven no wrap).  The bounded Sint63 `add_nz`/`no_overflow_*`
   were REMOVED in the int-model migration.  *Open:* a runtime check-and-branch
   (comma-ok) form for operands whose range is only known at runtime.
6. **Untyped constants — *INTEGER side DONE (A5, 2026-06-17); float side open*.**
   Go's *untyped* constants are arbitrary precision and acquire a type (with a
   representability check) only at use; a constant that does not fit is a *compile
   error*, not a runtime wrap.  *Integer fix delivered:* an untyped int constant is
   modelled as `Z`, constant arithmetic is `Z` arithmetic (exact), and the type-at-use
   conversion is the `i64c`/`u64c` notations — each `vm_compute`-evaluates the closed
   `Z` expression at ELABORATION (real bignums, so an INTERMEDIATE may exceed the
   target, e.g. `1<<70`) then converts via `i64_lit`/`u64_lit` demanding `in_i64`/
   `in_u64`.  An out-of-range constant FAILS to elaborate (the representability proof
   cannot be built) = Go's untyped-constant overflow.  No plugin change — the
   arbitrary precision lives in `vm_compute`; the resulting literal lowers via the
   existing fold.  Witnesses (axiom-free): `const_intermediate_exceeds` (`(1<<70)>>8
   = 2^62`), `const_exact_arith` (`10^12`), `const_u64_upper` (`2^63` fits uint64 not
   int64), `const_oob_i64`/`const_oob_u64` `Fail`; `const_demo` golden-locked.  *Still
   open (float side):* `const 0.1+0.2` should be `0.3` (we give the runtime
   `0.30000000000000004`) — untyped FLOAT constants as exact rationals (`Q`), tied to
   the float work (Phase D).

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
   `\xNN`).  **Comparison DONE (2026-06-18):** `str_eqb` = Go `==` (byte equality,
   `String.eqb`), `str_ltb` = Go `<` (LEXICOGRAPHIC by byte value — byte-by-byte,
   proper prefix `<` longer, first difference decides; reuses the suppressed
   `ascii_byte` decoder, no `nat_of_ascii` drag) — both *theorems*
   (`spec_str_eq_*`/`spec_str_lt_*`); `str_cmp_demo` → `true false true false`,
   golden-locked.  **`string`↔`[]byte` DONE (2026-06-18)** and **`string`↔`[]rune` DONE
   (2026-06-19): the rune/UTF-8 view** — `str_to_runes`/`runes_to_str` lower to native
   `[]rune(s)`/`string(rs)` (runtime does the real UTF-8); the Coq bodies are a full 1–4
   byte UTF-8 codec (suppressed), VERIFIED by round-trip examples for ASCII and a 3-byte CJK
   point (`rune_roundtrip_ascii`/`_cjk`, 中=U+4E2D).  `rune_demo` → `Go`, golden-locked.
   **`range s` (the ITERATING form) DONE (2026-06-19):** `str_range s (fun i r => …)` lowers
   to the native two-variable `for i, r := range s { … }` — `i` the BYTE offset of each
   code point, `r` the rune (`GoI32`).  Faithful byte offsets: the proof-only model is
   `runes_with_offsets` (running prefix sums of `rune_width`, the per-rune UTF-8 byte length)
   over `str_to_runes`, recognized-by-name so the emitted Go is the idiomatic range loop, NOT
   a `[]rune` materialisation.  The offsets MATCH Go's (machine-checked `str_range_offsets`:
   `A 中 B` → `0 1 4`; `str_range_demo` runs `H € !` → `0 72 / 1 8364 / 4 33`, golden-locked,
   axiom-free).  *Still deferred:* byte mutation (Go forbids it — strings immutable).
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
   (a) *aliasing — SINGLE-GOROUTINE aliasing now DONE (note was stale; reconciled 2026-06-19).*
   Reference-type sharing is modelled on the concrete heap and PROVEN + EXHIBITED: sub-slicing
   (`s[a:b]` shares the backing array) — `subslice_alias` THEOREM + `slice_alias_demo`
   (`s[1:3][0]=99` seen through `s[1]`); in-place append aliases / realloc-on-full —
   `slice_append_incap_aliases` THEOREM + `append_demo`; pointer aliasing — `ptr_alias` THEOREM +
   `ptr_alias_demo`; and MAP reference semantics across a function boundary —
   `map_alias_demo` (a callee's `m[7]=77` observed by the caller; rests on `map_get_set_same`).
   *Still open:* CONCURRENT aliased access (cross-goroutine visibility of a shared map/slice
   write) — that is the happens-before GUARANTEE (Tier 1 concurrency), not a construct gap.
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
   unordered) plus the `float_nan_demo` golden show Coq and Go agree.
   **Direct `>`/`>=`/`!=` DONE for int64/uint64/string/float (2026-06-18):**
   `i64_gtb`/`i64_geb`/`i64_neqb`, `u64_gtb`/…, `str_gtb`/`str_geb`/`str_neqb`,
   `f64_gtb`/`f64_geb`/`f64_neqb` (defined as the swapped `</<=` and `negb(==)`, but
   recognized by name and lowered to the DIRECT Go operator, so the emitted Go matches
   the source — `cmp_ops_demo`/`scmp_demo`/`fcmp_demo` → `true …`).  **Float `>=` is the
   SWAPPED `leb b a`, NOT `¬(<)`** — with a NaN operand `a >= b` is FALSE but `¬(a<b)`
   would be TRUE (machine-checked `f64_geb_nan = false`, `f64_neqb_nan = true`).
   Strings have a total order, so `str_geb = ¬(<)` is fine.  **Narrow fixed widths DONE
   too (2026-06-18):** `u8`/`i8`/`u16`/`i16`/`u32`/`i32` all have `_gtb`/`_geb`/`_neqb`
   (the plugin's `fw_is` + `parse_fixed_width` recognize the op on EVERY width);
   `fw_cmp_demo` → `true true true true`.  So all six comparison operators now emit
   DIRECTLY for EVERY integer / string / float type — the comparison surface is COMPLETE.

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
    `Fail`), signed wraps the `-2^(N-1)/-1` overflow via `norm`.  **`u32_mul`/`i32_mul`
    DONE** (mask-after-multiply): the product can reach `(2³²−1)² ≈ 2⁶⁴ > 2⁶³` carrier,
    but the masked LOW 32 bits are EXACT — `PrimInt63.mul` is mod 2⁶³ and `2³²∣2⁶³`, so
    `(a*b mod 2⁶³) mod 2³² = a*b mod 2³²` (losing the carrier's high bits never disturbs
    the low `w<63` bits the mask keeps); machine-checked `spec_u32_mul_wrap` (100000²→
    1410065408), `spec_i32_mul_wrap` (46341²→-2147479015).  The earlier omission was
    over-conservative — only a **≥63-bit-WIDE** product genuinely needs the wider model.
    *Still ✗:* **`uint64`/`uint`/`int` full width** (64-bit exceeds the 63-bit carrier —
    needs the Z-based int model, like `int64`'s ±2⁶² limit).
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
11. **Float gaps — *comparison + unary negation + min/max + float32 (sound) + conversions
    now done; abs/sqrt still open (need imports)*.**  Float `<`/`<=`/`==` (incl. NaN's unordered
    behaviour) and unary `opp` → `-x` (IEEE sign-flip, makes `-0.0`; machine-checked
    `opp_zero_is_neg` + runtime `float_opp_sign_demo`) are now emitted and proven
    faithful (see #9).  **`min`/`max` on float DONE (2026-06-18):** `f64_min`/`f64_max`
    → Go `min(a,b)`/`max(a,b)`, faithful on the two IEEE corners Go's builtin handles —
    NaN PROPAGATION (a NaN arg → NaN result) and SIGNED ZERO (`min(-0,+0)=-0`,
    `max(-0,+0)=+0`), which a naive `if a<b` gets wrong; machine-checked
    `f64_min_nan`/`f64_max_nan_b`/`f64_min_negzero`/`f64_max_poszero`, `fminmax_demo`.
    **`int` → `float64` DONE (2026-06-19):** `f64_of_int` → native `float64(i)` — modeled by
    the Rocq primitive `PrimFloat.of_uint63` (unsigned magnitude) + a sign-split, recognized
    by name → cast with the body suppressed (machine-checked `f64_of_int_pos`/`_neg`;
    `f64_of_int_demo` → `+5.000000e+000 -3.000000e+000`).  It SUCCEEDS where the narrow→int64
    widening fails for one reason: `f64_of_int` returns `float` (a primitive, NOT a single-
    field record), so there is no unbox-η-collapse to a renaming — it stays a NAMED call the
    recognizer fires on.  Adds `PrimFloat.of_uint63` to the trust base — a Rocq `float`
    PRIMITIVE (like `PrimFloat.add`), NOT a Fido axiom.  **`GoI64` → `float64` DONE too
    (2026-06-19):** `f64_of_i64` → native `float64(i)`, same recognize-and-suppress; its `Z`
    carrier additionally drags the Z→int63 helpers `of_Z`/`of_pos`/`of_pos_rec`, suppressed
    alongside the already-suppressed `Z`/`positive` arithmetic (`f64_of_i64_demo` →
    `+7.000000e+000 -3.000000e+000`).  **FLOAT32 ARITHMETIC MODELED (2026-06-19) — the
    "soft-float is intractable" wall dissolved by a probe.**  `SpecFloat` (already imported for
    `Prim2SF`) provides PRECISION-PARAMETERIZED arithmetic, so `f32_add a b := SF2Prim (SFadd
    24 128 (Prim2SF a) (Prim2SF b))` (binary32 = prec 24, emax 128) is a FAITHFUL float32 add —
    the SpecFloat round-to-nearest-even at binary32 is the SAME rounding Go's hardware does, NOT
    a float64 idealisation (so no hand-rolled soft-float, the thing I'd wrongly assumed was
    required).  `f32_add`/`f32_sub`/`f32_mul`/`f32_div` all modeled; machine-checked: the
    decisive `f32_add_rounds` (`2^24 + 1` rounds back to `2^24` in binary32) contrasted with
    `f32_f64_differ` (float64 KEEPS `16777217`) PROVES it really rounds at binary32; exact cases
    `f32_add_exact`/`f32_mul_exact` confirm ordinary results.  *Lowering deferred (proof-only,
    like `i64_of_f64`):* the body's `SFadd`/`Prim2SF` drag the SpecFloat definitional tree into
    extraction, so the native lowering (`GoFloat32` → `float32`, `f32_add` → Go `+`, recognized-
    and-suppressed) needs that tree suppressed — a follow-on; the MODEL (the hard part) is done.
    **Lowering SCOPED (2026-06-19, `Recursive Extraction f32_add`):** the drag closure is BOUNDED
    (~15 decls) — `SFadd`/`SFsub`/`SFmul`/`SFdiv`, `Prim2SF`/`SF2Prim`, and the SpecFloat rounding
    machinery `binary_round`/`binary_round_aux`/`round_nearest_even`/`shr`/`shr_m`/`shr_r`/`shr_s`/
    `shr_fexp`/`shr_record`/`shr_record_of_loc`/`fexp`/`emin`/`digits2_pos`/`cond_Zopp`, plus the
    `spec_float` TYPE.  An attempted lowering confirmed they drag (the abort is the generic
    "unmodeled node in value position" — it does NOT name the decl, so the closure had to be found
    via `Recursive Extraction`, not the error).  So the lowering is a concrete multi-piece job, not
    intractable: (1) suppress those ~15 value decls (`is_inlined_ref`) + the `spec_float` type
    (Dtype/Dind arm); (2) recognise `f32_add`/… → the native operator (`classify_f32_op` →
    `binop_of`); (3) avoid the float32 LITERAL-typing issue by demoing through a typed-param
    function (`f32_sum (a b : GoFloat32)` → `func F32_sum(a, b float32) float32`, so the call-site
    consts pin to `float32`); (4) `println`/`any` of a `GoFloat32` (needs a `Tagged GoFloat32`
    check).  **float32 LOWERING DONE (2026-06-19) — by MODULE suppression.**  Two earlier
    approaches failed: suppress-the-tree BY BASENAME (the SpecFloat drag reaches PrimFloat
    primitives that emit as `panic("axiom: …")` stubs, AND its parity `is_even` collides with the
    user mutual-recursion `is_even`), and `Extract Constant` (the `Go Main Extraction` driver still
    pulls a realized constant's body-deps in).  The clean fix was already in the plugin for `Z`:
    `is_zarith_helper` suppresses proof-only stdlib decls BY MODULE.  Extending it with
    `SpecFloat`/`FloatOps`/`FloatLemmas`/`PrimFloat`/`Sint63`/`Int63`/`Cyclic` drops the ENTIRE
    rounding closure at the source — and being module-qualified it drops SpecFloat's `is_even`
    while KEEPING the user's (collision gone).  One stdlib RECORD type (`shr_record`) is suppressed
    by name in the Dind arm (types don't collide).  Then `classify_f32_op` recognises `f32_add`/… →
    Go `+`/`-`/`*`/`/`, demoed through a typed-param function (`f32_combine (a b c : GoFloat32)` →
    `func F32_combine(a, b, c float32) float32 { return (a+b)*c }`) so call-site consts pin to
    `float32`.  `f32_demo` → `+7.500000e+000` (= (1.5+2.25)*2 in float32), golden-locked,
    **trust base still ZERO Fido axioms** (the SpecFloat machinery in `main_effect`'s proof base is
    only Rocq's `PrimFloat.*` primitives).  So float32 is a COMPLETE Go type: faithful binary32
    model + native lowering.  The same `is_zarith_helper` module suppression then unblocked the
    first proof-only conversion: **`float64` → `int64` TRUNCATION LOWERED (2026-06-19)** —
    `i64_of_f64` → native Go `int64(f)` (truncates toward zero).  Its `Prim2SF`-match body
    `f64_trunc_Z` is suppressed by name (a Fido proof-only helper) and the `Prim2SF` closure by
    module; `i64_of_f64` recognised → the cast.  Through a typed-param wrapper (`trunc64 (x :
    GoFloat64) → func Trunc64(x float64) int64 { return int64(x) }`) because Go rejects
    `int64(3.7)` on a CONSTANT (truncation error) — the wrapper makes the operand a variable.
    `i64_of_f64_demo` → `3 -2` (= `int64(3.7)`, `int64(-2.9)`), golden-locked, axiom-free.
    **narrow → int64 WIDENING LOWERED too (2026-06-19):** the probe corrected the force-inline
    fear — `i64_of_u8` is NOT force-inlined; it extracts to a real decl `func I64_of_u8(a int64)
    int64 { return To_Z(a) }`.  Since the widen is value-preserving and the narrow already erases
    to a Go `int64`, it lowers to IDENTITY — `i64_of_u8`…`i64_of_i32` recognised → the operand,
    and `To_Z`'s value-position-match body is dropped by the `Sint63`/`Int63` module suppression.
    `i64_of_narrow_demo` → `200 -5 60000` (u8/i8-signed/u16 widened), golden-locked, axiom-free.
    So ALL the previously-drag-blocked conversions now lower: float32 arith, `float64`→`int64`
    truncation, narrow→`int64` widening.  **float32 ↔ float64 LOWERED too (2026-06-19):**
    `f64_of_f32` (widen, EXACT — a binary32 value is exactly a binary64) → `float64(x)`, identity
    model; `f32_of_f64` (narrow, ROUNDS to binary32) → `float32(x)`, modelled `SF2Prim (SFmul 24
    128 (Prim2SF a) (Prim2SF 1))` — NOTE `SFadd …(Prim2SF 0)` does NOT round (SpecFloat special-
    cases a zero operand and returns it unrounded, assuming operands are already at the format),
    so rounding-by-`+0` is wrong; multiply-by-1 rounds the product.  Machine-checked
    `f32_of_f64_rounds`: `2^24 + 1` → `2^24` in binary32; `floatconv_demo` → `+1.677722e+007`
    (16777216 as float32) `/ +7.500000e+000` (round-trip 7.5).  **COMPARISON DONE (2026-06-19):**
    `f32_ltb`/`leb`/`eqb`/`gtb`/`geb`/`neqb` → native Go `float32` `<`/`<=`/`==`/`>`/`>=`/`!=`
    (operands are `float32`).  Faithful: a `GoFloat32` holds a binary32-representable value and a
    comparison does NO rounding, so binary32 and binary64 ordering agree on representable operands —
    hence `PrimFloat.ltb`/`leb`/`eqb` on the carrier ARE the float32 comparisons (recognized → the
    direct operator, decls suppressed via `is_f32_cmp_ref`, mirroring the f64 set).  NaN corner
    machine-checked: `f32_geb` is the SWAPPED `leb` so `x >= NaN` is FALSE (`f32_geb_nan`),
    matching Go — `¬(x < NaN)` would wrongly be true; `f32_cmp_demo` → `true true true`,
    golden-locked, axiom-free (the `PrimFloat` compares were already in the trust base).  *Still
    open:* float32 literals beyond the demo.

    **SOUNDNESS FIX (2026-06-20, code review) — `GoFloat32` made ABSTRACT.**  The model above
    had `GoFloat32 := float` (a transparent alias), so the type system let a NON-binary32-
    representable `float` literal flow straight into a `GoFloat32` position with no rounding:
    `f64_of_f32 16777217 = 16777217` in Rocq, but Go rounds `float32(16777217)` to `16777216` —
    a Rocq/Go DISAGREEMENT that licenses unsound proofs (the emitted Go was already `float32`-
    correct; the hole was purely at the Rocq level).  Fix: `GoFloat32` is now an ABSTRACT record
    `mkF32 { f32val : float ; f32ok : exists a, f32val = f32_round a }` — the proof field
    WITNESSES that the carrier is in the image of `f32_round` (binary32-representable).
    `mkF32 16777217 _` is unconstructable (its obligation `exists a, 16777217 = f32_round a` is
    false), so every inhabitant enters through a rounding smart constructor (`f32_of_f64` /
    `f32_lit` / the arith ops, which route their `SpecFloat` result back through `f32_of_f64`).
    Widening `f64_of_f32 := f32val` (identity) is now SOUND by construction.  **Zero new axioms:**
    the provenance proofs are `eq_refl` (the carrier is *literally* `f32_round a`); `Print
    Assumptions` = Rocq's own float/int primitives only — no Flocq, no `Admitted` (the hard
    `binary_round_aux` idempotence proof is SIDESTEPPED by carrying provenance instead of the
    fixpoint equation).  **Extraction unchanged:** `GoFloat32` erases to native `float32` and
    `mkF32`/`f32val`/`f32_round` to identity (suppressed; they only appear inside by-name-lowered
    ops) — same `GoU8`-style wrapper erasure — so the Go and the golden output are byte-identical.
    Machine-checked regression `f32_widen_sound`: `widen64 (f32_lit 16777217) = 16777216`,
    matching Go; the raw injection `f64_of_f32 16777217` no longer typechecks.  float32 literals
    now enter via `f32_lit` (rounds at the Rocq boundary), closing the "literals beyond the demo"
    item.

    **int64 → narrow TRUNCATION DONE (2026-06-19):** `u8_of_i64`/`i8_of_i64`/`u16`/`i16`/`u32`/
    `i32_of_i64` → the SAME native mask / sign-extend the `uN_of_int` narrows already emit
    (`(x & 0xFF)` for `uN`; `((x & 0xFF) ^ 0x80) - 0x80` for `iN`), because `GoI64` and the narrow
    types share the int64 carrier — so the lowering arm is literally the existing `of_int` arm
    plus an `of_i64` alias (`parse_fixed_width` op-list + one `||` at the lowering site; the decl
    is auto-suppressed by `fixed_width_op`).  The model crosses `GoI64`'s `Z` carrier into the
    int63 carrier via `Uint63.of_Z` then masks — faithful for `W < 63` since `2^W | 2^63`, so the
    low `W` bits agree — and the `of_Z`-match body never reaches the emitted Go (the op stays a
    NAMED call the recognizer fires on; `of_Z` is already module-suppressed).  **The feared
    carrier-crossing wall was false** (same lesson as float32): no force-inline, no `to_Z`/`of_Z`
    leak, no carrier-in-Z refactor needed.  Machine-checked `i64_to_u8_trunc`/`i64_to_i8_signed`/
    `i64_to_u8_neg` (`uint8(-1)=255`) / `i64_to_i32_wide`; `i64_to_narrow_demo` →
    `52 -56 4464 705032704`, golden-locked, axiom-free.

    **narrow ↔ uint64 CLOSED via the int64 HUB (2026-06-19), zero new ops.**  Every integer
    conversion factors through `GoI64`: narrow→uint64 = `u64_of_i64 ∘ i64_of_narrow` (widen
    identity, then the `uint64(x)` reinterpret); uint64→narrow = `<narrow>_of_i64 ∘ i64_of_u64`
    (`int64(x)` reinterpret, then the mask/sign-extend just landed).  Each leg already lowers,
    and the NAMED hub functions `U64_of_i64`/`I64_of_u64` apply the cast to a VARIABLE — so the
    signed corners a bare cast would reject (Go forbids `uint64(-1)` on a *constant*) emit valid
    Go.  Machine-checked: `u64_of_u8_widen` (value preserved), `u64_of_i8_reinterp`
    (`uint64(int8 -1) = 2^64-1`), `u8_of_u64_trunc` (`uint8(uint64 511) = 255`), `i8_of_u64_signed`
    (`int8(uint64 255) = -1`); `narrow_u64_demo` → `200 18446744073709551615 255 -1`, golden-
    locked.  **With this the WIDTH-TYPED integer-conversion matrix {uintN/intN (N≤32), int64,
    uint64} is complete** — all pairs route through the int64 hub, each leg faithful + lowering.
    (Go's machine `int`/`uint` ARE `GoI64`/`GoU64` here; the `Sint63` "int" is internal index
    plumbing that connects only to the narrows via `uN_of_int`/`int_of_uN`, not a user-facing
    width.)  A bare cast would need a different rule per signedness/constness; the hub funnels
    them to one place.

    **float ↔ uint64 DONE (2026-06-19) — the numeric layer is now COMPLETE.**  `u64_of_f64` →
    native `uint64(f)` (truncate toward zero; exact parallel of `i64_of_f64`, reusing the verified
    `f64_trunc_Z`).  `f64_of_u64` → native `float64(v)`, correctly rounded: since `of_uint63` is
    63-bit, the `≥2^63` range uses the round-to-odd trick — halve (`v>>1`, now <2^63), OR the lost
    bit back as STICKY (`| v&1`), round to binary64, then double (exact power-of-two scale) — which
    reproduces round-nearest-even on the full value.  Both bodies suppressed; the casts apply to a
    variable (typed wrappers) so neither hits Go's constant-cast rejection.  Machine-checked
    `f64_of_u64_lo` (255 exact), `f64_of_u64_max` (uint64 MAX rounds to exactly `2^64` — the trick
    is off-by-nothing), `u64_of_f64_big` (`float64 2^63 → uint64`, which `int64` would overflow);
    `u64conv_demo` → `+1.844674e+019 13835058055282163712` (uint64 max is a large POSITIVE double,
    and 1.5·2^63 round-trips exactly).  Axiom-free.

    Note: `abs`/`sqrt` are
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
    width (Go's int64 `^240` is -241, not the uint8 15).  **Full-width signed int64
    bitwise DONE via `GoI64`** (`i64_and`/`or`/`xor`/`andnot`/`not`): the `Z` carrier
    has the real 64-bit sign bit, so `Z.land`/`lor`/`lxor`/`lnot` agree with Go int64
    `& | ^ &^ ^` on negatives (`spec_i64_and` `-1 & 255 = 255`, `spec_i64_not`
    `^5 = -6`); axiom-free.  *Still ✗:* bitwise on the LEGACY `int` (Sint63) — the
    63-vs-64-bit carrier exposes the sign bit (use `GoI64` instead; legacy-`int`
    migration is Tier 2 #4 / PRE_IMPORT_PLAN A4).  *Shifts `<< >>`: DONE for
    fixed-width* (`uN_shl`/`shr`, `iN_shl`/`shr`) — EVIDENCE-CARRYING like `div_nz`
    (count proven ≥0, so the negative-count panic is unreachable; `u8_shl_neg`
    `Fail`).  Machine-checked `spec_u8_shl`…`spec_i8_shr_neg`: over-width `1<<8=0` (no
    upper limit), signed `64<<1=-128` (wrap), `>>` arithmetic for signed via
    `PrimInt63.asr` (`-3>>1=-2` toward −∞, NOT `-3/2=-1`; `-1>>3=-1`), logical for
    unsigned via `lsr`.  `shift_demo` prints 8 0 15 / -128 -2.  **Full-width int64
    shifts DONE via `GoI64`** (`i64_shl`/`shr`, evidence-carrying ≥0 count;
    `spec_i64_shl_wrap` `1<<63 = MININT`, `spec_i64_shr_arith` `-8>>1 = -4`).
    **Full-width uint64 shifts also DONE via `GoU64`** (`u64_shl`/`shr`;
    `>>` is logical for unsigned — `Z.shiftr` on non-negative values; `spec_u64_shr`
    `8>>1=4`). *Legacy `int` (Sint63) shifts still ✗* (same carrier issue — use `GoI64`).
13. **Conversions.**  *Integer↔integer among `{int,uint8,int8,uint16,int16}`: DONE.*
    Routed through the `int` carrier — `int_of_FW` widens (value preserved → lowers
    to identity), `FW_of_int` narrows (truncate: `land` for `uintN`, mask+sign-extend
    for `intN` — Go's `uint8(x)`/`int8(x)`, no representability proof since it
    truncates).  Cross-width by composition.  These also make the distinct numeric
    types mixable (implicit mixing rejected — `u8_of_i16_direct` `Fail`).
    Machine-checked `spec_u8_of_int_trunc`…`spec_i16_of_u8_cross`; `convert_demo`
    prints 200 232 / 1200.  **Full-width `int64`↔`uint64` DONE (2026-06-18):**
    `u64_of_i64`/`i64_of_u64` are Go's `uint64(x)`/`int64(x)` — a two's-complement
    REINTERPRET, EXACT (no rounding, unlike int↔float): the Z carrier re-normalises mod
    2⁶⁴ (`MkU64 (wrapU64 (i64raw a))` / `MkI64 (wrap64 (u64raw a))`), faithful by
    `wrap64_wrapU64` (the two normalisers agree mod 2⁶⁴, axiom-free).  Distinct from the
    narrow widths (which erase to int64, so a widen is identity) because `GoU64` lowers
    to a real Go `uint64`.  Emitted as a small NAMED function `func U64_of_i64(a int64)
    uint64 { return uint64(a) }` (pp_function special-case) — NOT inlined — so the cast
    applies to the parameter VARIABLE, sidestepping Go's rejection of `uint64(-1)` on an
    untyped CONSTANT.  Machine-checked `conv_u64_of_neg1` (`-1 → 2⁶⁴-1`)/`conv_i64_of_max`
    (`2⁶⁴-1 → -1`)/`conv_roundtrip`; `conv64_demo` → `18446744073709551615 -1 255`,
    golden-locked.  **Narrow → `int64` widening MODELED, lowering deferred (proof-only,
    2026-06-18):** `i64_of_u8`…`i64_of_i32` are value-preserving widens (a byte/short
    fits int64), machine-checked (`widen_u8`/`widen_i8`/`widen_u16`/`widen_u32`/
    `widen_i32`).  The lowering WOULD be identity (the narrow already erases to a Go
    int64 holding the value), but the faithful body crosses the PrimInt63→`Z` carrier
    via `Sint63.to_Z`, whose stdlib chain (`Sint63Axioms.to_Z` → the deliberately-
    REJECTED unsigned `Uint63.ltb`, Tier 3 #9) fights clean extraction-suppression — so
    kept proof-only (not reachable from `main_effect`, not extracted), like `f64_of_i64`.
    A runtime form needs an int63→`Z` that drags no match-bodied stdlib decls (or a
    narrow-stored-in-`Z` model).  **int↔float: int→`float64` DONE both ways** (`f64_of_int`/
    `f64_of_i64` → native `float64(x)`, 2026-06-19) — they return `float` (a PRIMITIVE), so
    recognize-and-suppress works.  **`float64`→`int64` truncation: MODELED + machine-checked,
    lowering deferred** (`i64_of_f64` via verified `Prim2SF`, 2026-06-19).  `string`↔`[]byte`/
    `[]rune` DONE (rune view).  *Still ✗:* `float↔float` / `float32` (no native f32); narrow →
    `uint64` and `int64`→narrow; interface conversions beyond `type_assert`.

    **THE VALUE-POSITION MATCH BLOCKER (shared; the GoI64-2-field "fix" was TRIED and FAILED —
    2026-06-19).** Two proven-but-unextracted conversions — the narrow→`int64` widening
    (`i64_of_u8`…, body `MkI64 (Sint63.to_Z (u8raw a))`) and the `float64`→`int64` truncation
    (`i64_of_f64`, body via `Prim2SF`/`wrap64`) — fail to LOWER because their faithful body
    contains a MATCH (`Sint63.to_Z`'s sign `if`; `Prim2SF`/`wrap64`'s branches) that Coq's
    extraction optimizer (NOT gated by `NoInline`) inlines + pushes the surrounding `MkI64` ctor
    INTO, leaving a `match` in VALUE position — so the conversion never stays a NAMED call the
    plugin can recognize → cast.  (The int→float casts lower because their body's leaf is a
    PRIMITIVE `of_uint63`, no match.)  *Hypothesis tried and REJECTED (this date):* "give
    `GoI64`/`GoU64` a 2nd field so Coq doesn't unbox, then the ctor app is non-renaming."  Built
    it end-to-end (2-field record + `Notation MkI64 z := (MkI64c z tt)`, plugin `z_value`
    see-through, `comparable_TI64` proof fixed) — the existing i64 layer stayed GREEN (golden
    unchanged), but the widening STILL leaked `to_Z`'s match into value position.  Root causes:
    (a) a `unit` phantom is ERASED by extraction → the record unboxes anyway; (b) a `bool` phantom
    is kept but makes `GoI64` NON-`Comparable` (two values, equal `i64raw`, differ in the bool —
    `key_eqb` would lie), losing the int64/uint64 map-KEY types; and (c) MORE FUNDAMENTALLY, the
    blocker is the `to_Z`/`Prim2SF` MATCH inlining, which unboxing-prevention does NOT touch.  *The
    real unblocks:* for the widening, the **narrow-stored-in-`Z`** carrier refactor (re-base
    `GoU8`… on `Z`, so `i64_of_u8 a = MkI64 (u8raw a)` is pure identity — NO `to_Z`, no match);
    for `float64`→`int64`, a value-position-match lowering (IIFE/hoist) OR a primitive-only
    truncation path.  Both proven faithful TODAY (machine-checked); only the extraction is gated.

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
   (`KStart` back-pointer) — now GROUNDED IN EXECUTION in the RICH calculus (see 1.2):
   `rstep_spawn` is a TWO-event step that emits the parent's `KSpawn cid` AND the
   child's `KStart (length tr)` (back-pointer = the just-laid `KSpawn`), so the fork
   `sync` edge is produced by running a program, not asserted on a literal.
   `fork_exec_trace` EXECUTES `write 7; go (read 7)` and proves the resulting trace
   EQUALS the once-hand-built `fork_handoff_trace`; `fork_exec_race_free` then derives
   race-freedom + hb-irreflexivity from `reachable_owned_safe_r`.  (The simple `step`
   calculus still emits `KSpawn` only — it has no heap/race story; the rich `rstep` is
   the authoritative model and supersedes it here.)*  The CHANNEL handoff edge is grounded
   the SAME way (`chan_pub_exec_trace`/`chan_pub_exec_race_free`): a real 2-goroutine
   program that SPAWNS the child, THEN writes loc 7 and sends — the write happens AFTER the
   spawn, so the fork edge canNOT publish it and the cross-goroutine ordering MUST flow
   through the channel send/recv (`transfer_orders` over the `KSend`/`KRecv` pair).  BOTH
   go-mem synchronisation edges (fork AND channel) are now consequences of EXECUTION, not
   assertions on literals.  All axiom-free.
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
   (memory accesses being exactly what races are about).  **The per-step lemmas COMPOSE
   into a whole-program theorem** (`denote_adequate`): for a single-channel,
   single-goroutine program, running it in the calculus to `CRet` means `run_io` of its
   DENOTATION also completes (`ORet tt`) at a world whose channel buffer matches — so
   the calculus execution and the extracted program's `run_io` meaning AGREE on the
   WHOLE run, not just per step.  Proved by a simulation invariant `SimInv` (carrying
   `OnChan` single-channel well-formedness, the single-goroutine live-set, `Denotes`,
   the buffer match, channel-open, and the `run_io` equation) preserved across `rsteps`
   (`siminv_step`/`siminv_steps`), read off at `CRet`.  Trust base: the per-step bases +
   `run_ret` + `chan_closed_send`/`chan_closed_recv` (channel-open frame) — nothing
   degenerate.  **MULTI-GOROUTINE state refinement is now done** (`Section KeystoneMulti`,
   via a CHANNEL SEPARATION/frame law): since `run_io` is SEQUENTIAL it cannot sequence
   concurrent goroutines, so the honest multi-goroutine connection is a STATE refinement
   — the calculus's full channel state stays matched to the `run_io` `World` under
   ARBITRARY interleaving.  `WMatchC` is the MULTI-channel match (no single-channel
   restriction); `wmatchc_step` proves EVERY `rstep` (any goroutine, any channel)
   preserves it — the new `chan_buf_send_frame`/`chan_buf_recv_frame` axioms (separation:
   an op on one channel leaves the others' buffers untouched) handle the untouched
   channels, and write/read/spawn don't touch buffers (so the world is unchanged there),
   so NO `Denotes`/`prj`/`Hret` is needed.  `reachable_refines`: every reachable state of
   a concurrent multi-channel execution is realized by a `run_io` world;
   `reachable_refines_and_safe` bundles it with the proven race-freedom
   (`reachable_owned_safe_r`) on the SAME reachable execution — so the guarantee now
   applies to genuinely concurrent programs at the state level.  Cost: 2 new axioms in
   builtins.v (the channel-frame laws), validated by the same per-channel FIFO-map heap
   model as `chan_buf_send`; trust base verified by `Print Assumptions` (exactly the
   channel laws + the 2 frame axioms; `chenv_inj` is a discharged hypothesis).
   **The HEAP analogue is now DONE (2026-06-21, `Section KeystoneHeap`):** `WHMatchC` matches
   every location's `run_io` ref value (`ref_sel (locenv l) w`) to the operational `rc_heap`;
   `whmatchc_step` proves EVERY `rstep` (any goroutine, any location) preserves it — only
   `rstep_write` advances the heap world (by `ref_upd`), the ref SEPARATION law
   `ref_sel_upd_diff` handling the untouched locations, every other step leaving `rc_heap`
   unchanged so the same world matches.  `reachable_refines_heap`: every reachable state's
   MEMORY is realized by a `run_io` world, across all interleavings; `reachable_refines_heap_and_safe`
   bundles it with the proven race-freedom — so the guarantee now covers the MEMORY STATE that
   races are actually about, not just channels.  Trust base (`Print Assumptions`): only
   `PrimInt63`/`PrimFloat` — no `functional_extensionality`, NO frame axioms (`ref_sel_upd_diff`
   is a derived lemma; `locenv_loc_inj` a discharged hypothesis), cleaner than the channel side.
   **The SINGLE-world COMBINED state match is now DONE too (2026-06-21, `Section KeystoneState`):**
   `WState w cfg := WMatchC chenv inj w cfg /\ WHMatchC locenv inj w cfg`; `wstate_step` shows EVERY
   `rstep` preserves it in ONE world — each step advances at most one component (`chan_*_upd` for a
   channel op, `ref_upd` for a write) and the `World`'s ref- and channel-heaps are INDEPENDENT, so the
   untouched component stays matched in the SAME advanced world (the new builtins cross-frames
   `ref_sel_chan_send_upd`/`ref_sel_chan_recv_upd`/`chan_buf_ref_upd_frame`, all one-line: the two
   sub-heaps are distinct `mkWorld` fields).  `reachable_refines_state` / `reachable_refines_state_and_safe`:
   every reachable concurrent state — channels AND memory — is realized by ONE `run_io` world AND (under
   ownership) race-free.  Trust base: only `PrimInt63`/`PrimFloat`.  *Still open:* a term-level account
   of cross-goroutine value flow beyond state, and the plugin lowering side (`Cmd` ↔ extracted Go).
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
   `mp_trace_race_free`).  **A CHECKABLE discipline now DISCHARGES `Owned` (2026-06-21):**
   `LocPrivate` — every memory location is touched by a SINGLE goroutine (any two
   same-location accesses share a tid) — IMPLIES `Owned` (`locprivate_owned`), because
   same-location accesses then lie in ONE goroutine's PROGRAM ORDER and `po ⊆ hbt`; hence
   `locprivate_race_free` and `reachable_locprivate_safe` (a reachable location-private
   execution is race-free + strict-hb) earn race-freedom from a STRUCTURAL condition with
   NO `Owned` hypothesis — all fully axiom-free.  Witnesses: `disjoint_race_free` (two
   goroutines on disjoint locations) and `shared_not_locprivate` (the discipline bites: two
   goroutines on the SAME location is rejected).  This is the no-sharing BASE.
   **The TRANSFER case is now a GENERAL theorem (2026-06-21):** `transfer_orders` — if access [a] is
   program-before a SEND and the matching RECV is program-before access [b], then [a] →hb→ [b]
   (`po`·`sync`·`po`); so ownership can MOVE between goroutines through a channel and the handed-off
   location stays race-free.  Witness `handoff_race_free`: goroutine 0 writes loc 7, hands off via a
   send, goroutine 1 receives and ALSO writes loc 7 — a genuine WRITE/WRITE conflict, yet race-free
   because the transfer orders the two writes (`handoff_owned` via `transfer_orders`).  `LocPrivate`
   REJECTS this (two goroutines on 7); the transfer discipline ACCEPTS it — the idiomatic Go "pass
   ownership over a channel".  Axiom-free.  **The closed-form DISCIPLINE is now DONE (2026-06-21):**
   `HandoffDisciplined t` — EVERY conflicting (same-location) pair `i<j` is a `Handoff`: same
   goroutine (program order) OR a single `po`·`sync`·`po` handoff.  `handoff_disciplined_owned`:
   this one CHECKABLE structural condition ⇒ `Owned` ⇒ `handoff_disciplined_race_free`.  It UNIFIES
   the two bases — `locprivate_handoff_disciplined` (no sharing ⇒ same-goroutine disjunct) and
   `handoff_trace_disciplined` (the channel handoff ⇒ the `po·sync·po` disjunct, re-deriving
   `handoff_race_free` through the discipline).  Axiom-free.  Future programs earn race-freedom by
   exhibiting the STRUCTURE, not a hand-built `Owned` proof.  **MULTI-HOP now DONE (2026-06-21):**
   `syncpath t i j` = the transitive `po`·(`sync`·`po`)* — an access, then any number of (program-step
   to a send/spawn, hand off to the matching recv/start, program-step on) hops; `syncpath_hbt` (each
   hop = two `hbt` edges) ⇒ `sync_disciplined_owned`/`_race_free`.  STRICTLY generalises the single
   handoff (`handoff_disciplined_sync`: one hop is a path); witness `two_hop_race_free` — ownership
   passes g0⇝g1⇝g2 across TWO channels before the final read, race-free via the 2-hop chain (a single
   handoff cannot reach).  Axiom-free.  *Still open:* a PROGRAM-level (`Cmd`) discipline ⇒ the
   reachable traces are `SyncDisciplined` (subtle: dynamic `CSpawn`).
3. **Model completeness — exact FIFO (done), liveness, real memory.**  *Exact FIFO —
   DONE:* `reachable_sorted` (concurrency.v, axiom-free) — every reachable channel
   buffer is STRICTLY INCREASING in send position (`BufSorted`, via `step_preserves_
   sorted`).  Since `step_recv` pulls the buffer FRONT (the minimum = oldest
   unreceived send), receives consume sends oldest-first — the exact kth-recv ↔
   kth-send pairing, established by the semantics + the invariant.  (An explicit
   trace-level `from(j1) < from(j2)` theorem would additionally need a recv-event ↔
   producing-step relationship — a nicety on top.)  **Deadlock-freedom — characterized
   + a real class proven (all axiom-free).**  In the rich calculus, every head is
   ENABLED except `CRecv` on an empty buffer (and `CSpawn` needs a fresh id, always
   available — `LiveFin` is a reachable invariant), so `ready_can_step` proves any live
   goroutine that is neither finished nor blocked CAN step.  Hence the exact DEADLOCK
   CHARACTERIZATION `rstuck_blocked`: a stuck config has someone unfinished, yet EVERY
   live goroutine is finished (`CRet`) or blocked receiving on an empty channel ("all
   waiting to receive, no one sending"); `rblock_stuck` is a concrete rich deadlock.
   And a genuine deadlock-FREEDOM theorem for a real class: `reachable_recvfree_progress`
   — a RECEIVE-FREE program (sends/writes/reads/spawns, i.e. real concurrency, but no
   receive) NEVER deadlocks; in any reachable state every live unfinished goroutine can
   step (`RecvFree`/`LiveFin` preserved across `rsteps`).  And a RECEIVING program is
   shown deadlock-free too (`sr_never_stuck`): `sr_prog` sends then receives on one
   channel — it performs a receive yet never deadlocks, because the UNBOUNDED BUFFER
   lets the send precede the matching receive (proved by exhibiting the reachable shapes
   `SRShape` and showing each is done-or-can-step).  **BIDIRECTIONAL exchange under
   GENUINE INTERLEAVING — DONE (2026-06-21):** `ex_never_stuck` — TWO distinct goroutines
   that each BOTH send and receive across two channels (`g0: send c0; recv c1` ‖
   `g1: send c1; recv c0`).  Both opening sends are concurrently enabled, so the
   reachable-state space BRANCHES (a 7-shape lattice with a diamond `4→{5,6}`, not the
   linear chain `sr` had) — yet it never deadlocks, because each goroutine sends BEFORE
   it blocks on a receive.  `EXShape` enumerates the 7 reachable shapes; `ex_step_shape`
   shows `rstep` stays inside them (the send/recv transitions walk the lattice; the other
   7 rstep rules are impossible); `ex_shape_progress` shows each is done-or-can-step.
   Contrast `ex_recvfirst_stuck`: the SAME goroutines RECEIVE-first deadlock immediately
   (the classic circular wait — the model faithfully represents it).  This shows the
   manual reachable-shape method SURVIVES real interleaving (with real bookkeeping, no
   blowup).  Axiom-free.  *Still open:* GENERAL deadlock-freedom for receiving programs
   (a session/ownership discipline ⇒ "every blocked receive has a guaranteed future send",
   i.e. no circular wait); and a real heap behind `KWrite`/`KRead` (currently abstract).

   **UNBUFFERED-channel FORCING — operational, DONE (2026-06-21, `Section BoundedChannels`).**
   The rich `rstep` uses UNBOUNDED buffers; Go's `make(chan T)` (capacity 0) FORBIDS buffering
   and a send must RENDEZVOUS (blocking until a receiver).  `rendezvous_via_buffer` DERIVED the
   handoff but did not FORCE it.  A self-contained capacity-parameterised channel calculus
   (`Variable cap`, `cstep`) adds the forcing: `cstep_send` is GUARDED by `length (buf c) < cap c`
   (unsatisfiable for cap 0), plus a synchronous `cstep_sync` rendezvous (guarded `buf c = []`, so
   FIFO stays honest).  Proven: a cap-0 channel's buffer is empty in EVERY reachable state
   (`cstep_cap0_buf` / `csteps_cap0_buf`) — buffering is impossible; an all-senders config in an
   unbuffered world is STUCK (`all_senders_stuck` / `ublock_stuck`) — the blocking the buffered
   model cannot express; and the rendezvous fires when a receiver is present (`urv_can_sync`).
   The capacity sub-model is now COMPLETE: SAFETY — the buffer never exceeds capacity on any run
   (`cstep_cap_respected` / `csteps_cap_respected` / `csteps_from_empty_cap_respected`, no overflow);
   LIVENESS — a buffered send with room never blocks (`buffered_send_progresses`), the dual of
   `all_senders_stuck`, so BOTH halves of Go's channel blocking (cap>len ⇒ progress, cap 0 ⇒ block)
   are captured.  Axiom-free.  Scope is bounded to the channel fragment ([CSend]/[CRecv]); integrating
   `cap` into the full `rstep` (an `rc_cap` field at ~42 `mkRCfg` sites) is the remaining cascade — the
   missing SEMANTICS (unbuffered = synchronous-only + blocking) is now proven.

**Combined (steps 1+2):** `reachable_owned_safe` — a REACHABLE execution respecting
the ownership discipline has a strict-partial-order happens-before AND is race-free.
**Deadlock representability + freedom:** unlike the (total, sequential) `run_io`, the
operational semantics REPRESENTS deadlock — `block_stuck`/`rblock_stuck`: a config that
cannot step yet has a live goroutine with work left (`Stuck`/`RStuck`).  Deadlock is now
also CHARACTERIZED (`rstuck_blocked`: stuck ⇒ all live goroutines finished or
empty-channel-recv-blocked) and deadlock-FREEDOM is PROVEN for receive-free programs
(`reachable_recvfree_progress`).  Disciplined deadlock-freedom for receiving programs is
the remaining liveness frontier.  All axiom-free.

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
make run-local    # extract + go run (no Docker; needs a host Go)
make run-extracted # extract + run (Dockerised) — guarded ad-hoc run, no diff
make check        # extract + run + diff output vs expected_output.txt (the verify step)
make golden       # extract + SHOW the delta (committed → new) + bless expected_output.txt
make install-hooks  # activate pre-commit hook (run once after clone)
```

`expected_output.txt` is the golden runtime output — a cheap end-to-end check
that a Rocq/plugin change did not alter observable behaviour *anywhere*.

**Run/verify ONLY through these targets — never a bare `go run` / `docker run …
go run`** (that bypasses extraction and can validate stale Go).  `check`, `golden`,
`run-local`, and `run-extracted` ALL declare `extract` as a prerequisite, so the
program you run/diff always reflects current `*.v`/plugin source.  Verify-then-bless
workflow after an intended change: **`make check`** (re-extracts, runs, prints the
diff vs the golden — review that the delta is exactly what you intended) → **`make
golden`** (re-extracts, *re-shows* the delta, then blesses) → commit.  The diff
check lives in the Makefile (both `check` and `golden` surface it); do not diff by
hand.
