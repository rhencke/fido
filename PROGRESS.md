# Fido — progress, design & status

Detailed companion to `CLAUDE.md` (which is kept short: the rules, commands, and architecture). This is the living reference — the full project vision and principles, the incremental ladder (what is modelled, feature by feature), the correctness-debt tiers, known gaps, the wish list, and the concurrency research plan. **Update the ladder here when a feature lands.** Not auto-loaded into context; read on demand.

**STATUS — the MODELLING scope is comprehensively complete; the active front is the PRINTER / TCB-shrink (gap #10), which is still RED — see the PRINTER ledger below.** What "complete" does and does not mean: every construct is *modelled in Rocq and lowered by the TRUSTED OCaml plugin* — it is NOT "verified Go", because the plugin (and the live expression printer) remain trusted.
- **Go CONSTRUCT (MODEL) LAYER is complete** — every Go construct in the no-import scope is modelled in Rocq and extracted (via the trusted plugin), with NO remaining fail-closed construct gap. (Interfaces are method-dictionary records: behaviourally correct dispatch, just not the native `interface{}` *keyword* — an idiomatic-output difference, not a correctness gap.) This is the MODEL surface; it does not make the emitted Go verified — that is the printer/gap-#10 work below.
- **BACKEND hardened + GATED** — the fail-closed sweep (4 external reviews' defect classes) is complete, and a gate trio now *enforces* it on every build: `go vet` + the axiom-manifest (trust base == `EXPECTED_ASSUMPTIONS.txt`) + the non-bypassable negtest harness (`negtests/`), plus the hook anti-tampering fix.
- **CONCURRENCY theory complete** — the abstract dynamic-ownership invariant (`region_inv_f_race_free`, all three transfer mechanisms) + the full session safety/liveness theory, axiom-free + funext-free.
- **PRINTER (status ledger).** The `SRaw` verified-expression-printer overlay was deleted (postmortem in `LESSONS.md`; do not revive it). Current state:
  - **GREEN** — the Go **type/literal** printers (`print_ty`/`print_Z`/`print_string_lit`/`print_hex`/`print_float_hex`/`print_sep`) are EXTRACTED to `plugin/printer.ml` and USED by the plugin, each with a zero-axiom round-trip (`print_ty_inj`, `parse_print_ty`, `print_parse_Z`/`_hex`/`_float_hex`, `esc_string_roundtrip`). The from-scratch Wirth **`Module Front`** (lexer + recursive-descent/precedence-climbing parser + clean `GExpr` AST, NO raw constructor) has a zero-axiom round-trip `parse_print_roundtrip : ∀ e, parse_str (gprint 0 e) = Some (e, [])` (+ `gprint_inj`) over the binop/unary/atom core + the five postfix forms (selector/index/slice/call/type-assertion) + the M5 token-level type layer. **★Stage B slice 1 (LIVE):** `Front.gprint` is now EXTRACTED and CALLED by the plugin for the first expression class — a binary operator over two runtime locals (`MLrel OP MLrel`): `go.ml`'s `goexpr_bridge_binop` builds the `Front.GExpr` directly (never by parsing a string) via the go_ident-checked `mk_goexpr_id` smart constructor, and prints it with the machine-checked `Printer.Front.gprint`. Liveness is demonstrated (a `+`→`BSub` perturbation of the operator map flips exactly the `var OP var` sites in the emitted Go, at five real locations).
  - **RED** — `Front` prints only the `var OP var` binop class so far; **every other expression shape still uses the trusted OCaml `pp_prec`/`pp_expr`** (the bulk of expression printing). That `var OP var` slice is restricted so the typed-arith IIFE provably cannot fire, making the Front output byte-identical to `pp_prec` (golden unchanged besides the new demo). `gofmt` remains a trusted post-processor (whitespace normaliser, outside the proof claim). No source→emitted-Go correctness theorem (gap #10). `Front.lex` is a *printer-grammar* lexer (self-consistency `parse(gprint(ast))=ast`), NOT a general Go-subset lexer.
  - **NEXT** — grow the LIVE Front class: bridge binops with literal / nested-binop operands (replicating or, better, subsuming `pp_prec`'s force-wrapper decision so the duplicate precedence authority eventually dies), then atoms / calls / conversions — shrinking the `pp_prec` fallback toward retirement. Each step: construct `Front.GExpr` directly, never via string parsing; keep golden byte-identical (or bless an intended delta).
- ⚠️ **Still NOT "formally verified Go."** The plugin stays trusted/unverified (gap #10 — no source→emitted-Go theorem; golden + negtests are the only end-to-end check). The proven safety reaches the modelled fragment, not arbitrary emitted Go.
- **PRINCIPLED current restriction — ASCII-only identifiers** (review #4 item 5). `is_idstart`/`is_idc` (goprint.v) accept only `[_A-Za-z][_A-Za-z0-9]*`; Go identifiers may be Unicode (any letter/digit per the spec's `unicode.IsLetter`/`IsDigit`). This is NOT a soundness hole — it only narrows the *representable* identifier set (an over-restriction: everything `go_ident` accepts IS a valid Go identifier) — it is a deliberate, bounded "Go-with-proofs" expressiveness gap, to be widened to full Unicode when warranted, NOT a permanent accidental limit.
- **Clean tractable wins ON DECK (review 2026-06-28):** wire ONE `Front` expression form into the live plugin path (Stage B, the headline item); make `gofmt` check-only (`gofmt -l` → fail if it would rewrite) to pull it out of the trusted path; collapse the duplicate type parsers (prove the type round-trip through `Front.parse_gty`, then retire the string-level `parse_ty`). These are real, bounded wins — not "frontier."
- **Deeper frontier — foundational / gated / substrate-bound:** native `interface{}` keyword (idiomatic paradigm change; dict lowering already correct), defined-type map KEYS (heterogeneous-heap rework, niche), the full source→Go RECOGNITION / correctness theorem (gap #10 — to be built on `Module Front`, NOT `SRaw`), the concurrency IO-LIFT (spawn fragment; `go_spawn` has no `run_io` law — user-gated option b), CI (gh token lacks Actions perms), and `int` bitwise/shifts (63-bit Rocq-`int` substrate limit) / assert-to-`any` (`GoTypeTag GoAny` universe-inconsistent) — both genuine `✗` that cannot be closed under the current substrate.

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

The memory model now also answers **which write a read observes** (review #6 #19).
The read is sequentially consistent — it returns `rc_heap l`, the value of the
last write to `l` in the linearised order — so the observed writer is, by
construction, the trace-last write before the read (`last_write_before` =
`W(r)`).  Under the ownership discipline (`Owned`, which every reachable
race-free execution satisfies) this `W(r)` is proved the *unique hb-maximal
write that happens-before the read* (`visible_write_hb_maximal`), and no write to
`l` is ever concurrent with the read (`read_write_hb_ordered`).  So a read's value
is happens-before-determined, not interleaving-dependent — the DRF visible-write
condition, proved constructively (no classical reasoning; it rests on
`owned_orders_same_loc`'s positive ordering).

**THE UNIFIED SEMANTICS (`unified.v`) — the 2026-06-24 review's decisive ask.**
That review's verdict (RED) found several disconnected semantic systems (the shallow
`IO`/`World`, the `cmd.v` effect evaluator, `rstep`, `rstepC`, the session reductions)
but no single authoritative operational configuration covering an *ordinary program*
combining goroutines + channels + heap + panic + defer + output.  `unified.v` is that
configuration: ONE command language `UCmd` with every admitted effect, ONE config
`UConfig`, ONE step relation `ustep`.  The defer/panic interaction is faithful (a
panicking goroutine still runs its remaining defers — the cmd.v P0 fix, now operational
and concurrent).  The ownership/race and liveness results are PORTED onto it, reusing
concurrency.v's trace theory verbatim (it is calculus-agnostic): `uprivate_disc_step` +
`uprivate_disc_reachable_race_free` (RACE-FREEDOM for every interleaving of an all-effects
program), `uready_can_step` (PROGRESS) + `ustuck_blocked` (the DEADLOCK characterization —
a stuck config is a genuine wait-for-sender, since send/close-on-closed now panic-step and
recv-on-closed returns zero).  Concrete all-effects executions are machine-checked
(`unified_panic_runs_defer`, `unified_heap_write_read`, `unified_chan_send_recv`,
`unified_output_ordered`).  `unified.v` is the authoritative semantics; the older systems
are now provably narrower FRAGMENTS of it: the rich value-carrying calculus `rstep` (the most
expressive prior system — goroutines + channels + heap + select + closed-channel semantics) is
EMBEDDED into `ustep` by a structure-preserving translation `embed_cmd`/`embed_cfg`, and
`rstep_embeds` proves a rule-for-rule FORWARD SIMULATION (`rstep cfg cfg' -> ustep (embed_cfg cfg)
(embed_cfg cfg')`), lifted to runs (`rsteps_embeds`).  Because the embedding is the IDENTITY on the
trace (`embed_cfg_trace`), every trace-based safety result already proved over `rstep` runs (WfTrace,
happens-before, the ownership/race discipline) is — verbatim — a statement about `ustep` runs
(`rsteps_trace_embeds`).  So `ustep` is not a competing semantics: the rich calculus is literally
`ustep` restricted to the panic/defer/output-free sub-language, and `ustep` only ADDS the missing
effects.  This is the formal close of the architectural finding ("no single authoritative semantics").
*Trust note:* `rstep_embeds` commutes `embed_cmd` with the program-map `upd` via
`functional_extensionality` — already part of the END-TO-END TRUST BASE (builtins.v `run_io_inj`),
and NOT in `main_effect`'s cone, so `EXPECTED_ASSUMPTIONS.txt` stays empty and the axiom gate is
unaffected.

SESSIONS are now ported onto `ustep` too (review finding #10 — they had been "primarily about
protocol SYNTAX": `PEmits`/`psess_emits_proto` read the send/recv sequence off a session TERM but
never tied it to an execution).  `proto_ucmd` compiles a `Proto` to a `UCmd` (send on an open channel
`cs`, recv on a pre-CLOSED+drained `cr` — Go's "partner finished and closed", so every recv is ready
and yields zero), and `proto_ucmd_realizes` proves its `ustep` run RUNS TO COMPLETION emitting a trace
whose send/recv polarity sequence is EXACTLY the protocol's (`proto_polarity`).  `psess_realized_
operationally` composes this with the syntactic `psess_full_emits_proto`: a COMPLETE session-typed term
(`PSess i PEnd A`, the forge-proof extracted `Sess`) has its `PEmits` behavioural spec realized,
step-for-step, by a concrete execution of the unified semantics — the indices are no longer just
syntax.  Still open: retiring the old systems now that they are provably fragments, and a multi-
goroutine session rendezvous (the realization runs the client against a closed-channel environment,
which suffices for the polarity-sequence guarantee; a two-party `ustep` handoff is the natural next
extension).

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
to the build log and does not affect the runtime golden).  As of commit 445aca3 the printed base
is **EMPTY — `Print Assumptions main_effect` = "Closed under the global context" (ZERO axioms)**.
The former `PrimInt63.*` / `PrimFloat.*` substrate (`int : Set`, `float : Set`, `of_uint63`, …)
is GONE: integers are `Z` (`GoI64`/`GoU64`/`GoInt`/the narrows are Z-carried records), heap
locations are `nat`, and floats are `SpecFloat.spec_float` (the axiom-free Z-based IEEE-754
inductive — every float op is a computable `SF*` / `binary_normalize` definition).  `builtins.v`,
`main.v`, `concurrency.v` declare NO `Axiom`/`Parameter`/`Admitted` AND use no kernel primitive;
the IO / heap / channel / session / numeric model is `Definition`s over concrete Rocq data, and
every law (`run_bind`, channel & heap get-after-put, `ref_sel_upd_same`, float `SFadd`/… specs, …)
is a DERIVED THEOREM.  The extracted program's `main_effect` rests on NOTHING beyond Rocq's kernel
*at the Rocq-model level* (this is the AXIOM base of `main_effect` — now empty; it is NOT the
end-to-end trust base of the emitted bytes, which still includes the trusted plugin — see
**END-TO-END TRUST BASE** below).
The only *Fido-declared* assumptions anywhere are two `concurrency.v` SECTION hypotheses
(the abstract-calculus ↔ IO coding round-trip) — proof-only, parameterised (discharged at
section close via the concrete keystone coding), emit no Go, NOT in the extracted program's
trust base.  (One EXTERNAL Coq-stdlib axiom is in scope for the IO-EQUATIONAL results:
`funext`, used via `run_io_inj` — holdout #1; absent from `main_effect`, present in the
`denote_*` adequacy chain.)  So the old "~70 axioms / joint consistency unproven" debt is
CLOSED: there is no Fido axiom set to be jointly consistent.  The discipline now is to
PRESERVE this — add no `Axiom` for any new builtin (model it as a `Definition`, even hard
cases like a soft-float `float32`).

**END-TO-END TRUST BASE — the whole picture (external review, 2026-06-23; be exact).**
"ZERO Fido axioms" above is the **Rocq-model** base.  It is NOT the trust base of the bytes
`go build` compiles — that is strictly larger, and the optimistic parts must not be assembled
into "verified race-free Go."  FOUR unverified bridges sit between the proofs and the bytes:
- **The extraction plugin** (`plugin/go.ml`, ~4300 lines OCaml) — TRUSTED and UNVERIFIED; no
  theorem relates emitted Go to the source term (Known gap #10).  Every "emits `[]T{…}`" /
  "body suppressed" in these proofs is a claim about THIS translator, and a faithfulness bug
  would live here.  It is the real TCB's largest, least-guarded component.
- **funext** (Coq-stdlib `functional_extensionality`, EXTERNAL) — pulled in by the IO-equational
  results through `run_io_inj` (builtins.v), including the `denote_adequate`/`_mem` chain.  Those
  results are "no *project-declared* axiom," with funext a standing holdout (ZERO_AXIOMS_PLAN.md
  #1) — so the project is NOT globally axiom-free.  (`main_effect` does not use it.)
- **The `Denotes` relation + the source→`Cmd`→denotation map.**  `denote_adequate` proves "IF a
  program denotes this IO term, its `run_io` agrees" — but the map from real Go to `Cmd` to `IO`
  is by-hand/plugin, so a `Denotes` that mis-models Go makes the theorem reassure *vacuously*.
  The machine-checked non-vacuity keystone (`keystone_roundtrip`) covers the VALUE CODING, not
  the denotation relation itself.
- **The `gofmt` postprocessor** (Go's formatter, EXTERNAL) — `make extract` runs `gofmt -w` on the
  plugin's output, so the COMMITTED `*.go` bytes are `gofmt(plugin output)`, NOT the plugin's own
  bytes.  Go EXPRESSIONS are printed by the TRUSTED OCaml `pp_expr` (the `SRaw` verified-expression-printer was
  DELETED — see the PRINTER status), and the surviving verified TYPE/LITERAL printers' round-trips
  (`print_ty_inj` / `print_parse_Z` etc.) prove properties of the *Rocq printer's* bytes — which then
  pass through gofmt anyway, so the committed bytes are gofmt's, not the producer's: gofmt is an
  explicitly-TRUSTED (unverified) rewrite.  **DECISION (external review #4 item 4): gofmt is TRUSTED,
  not "temporary-until-proven."**  gofmt is Go's ONLY definition of canonical surface form (no spec to
  implement independently), so making the printers emit gofmt-canonical bytes directly (committed ==
  produced) is a future close, not a quick win.  The honest claim is **"plugin output, then
  trusted-gofmt-formatted,"** NOT "verified committed bytes."  (gofmt rewrites only operator/operand
  whitespace, never parens.)

**Where the safety guarantee actually reaches.**  Race-freedom lives on `rstep`/the calculus and
is bridged to `run_io` only for the **single-channel, single-goroutine, spawn-free, non-blocking**
fragment (`denote_adequate`/`_mem`); `go_spawn` has no `run_io` law BY DESIGN, so the genuinely
concurrent / possibly-blocking programs — exactly the safety-critical ones — are carried by the
calculus ALONE, tied to emitted Go only through the plugin/prose.  Generality is also thinner than
the line count: the one **arbitrary-N** race-freedom result (`PureLocal`/`PrivateDisc`) is the
**no-transfer, memory-free-children** fragment.  *(UPDATE 2026-06-23 — the ownership-TRANSFER gap is
now closed for the pointer-handoff fragment: `region_inv_race_free` proves EVERY reachable interleaving
of ANY (no-spawn) pointer-handoff program is race-free, via an ABSTRACT ownership invariant — not the
old per-program phase enumeration (`MpReach`/`XferReach`/…).  The chain: `owned_snoc`/`owned_step_snoc`
(incremental `Owned` — per-step preservation reduces to "the new access is hb-after the location's
previous access") ← `AcqConn`/`acqconn_hbt_new` (a dynamic OWNER discharges that obligation: same-owner
⇒ program order, transferred-owner ⇒ the send→recv sync edge) ← `WT` (a LINEAR region-threading typing —
send RELEASES the sent pointer, recv ACQUIRES it; `OnlyAcc` is non-linear so cannot express transfer) ←
`RegionInv` (the config invariant: single-valued ghost `own : Owner` ⇒ disjointness free; channel buffer
carries each in-transit pointer with its sender's hb-support) + `BufLin` (buffer linearity, so a recv pop
leaves no duplicate) ← `region_inv_step` (every `rstep` preserves both; spawn/select/close vacuous by
`WT`-inversion, closed-recv by `NoClose`) ← `region_inv_steps`/`region_inv_race_free`.  Witnessed
non-vacuously (`witness_all_interleavings_race_free`: a genuine cross-goroutine write/WRITE on one cell,
handed off over a channel, race-free for ALL interleavings).  ENTIRELY funext-free — `WT`'s region is a
hypothesis position and own-updates are pointwise, so `wt_region_ext` re-types continuations with no
axiom.  SPAWN-transfer now ALSO covered (2026-06-23): `WT_spawn` splits the region on `CSpawn` (child
takes `Rc ⊆ R`, parent keeps the rest), `region_inv_spawn` proves the split preserves the invariant —
the transferred cell's `AcqConn` is forged through the `KSpawn`→`KStart` fork edge — so
`region_inv_race_free` now covers BOTH channel-handoff AND ownership-split-on-spawn (witnessed by a
fork-handoff program whose child writes a cell the parent handed it, race-free for all interleavings).
SIGNAL-handoff (pattern B) now ALSO covered (2026-06-23): `WTf flp` parameterises the typing by a footprint
map `flp c v` = the location a send of value `v` on channel `c` transfers (pattern A = `flp c v = v`; signal
handoff = a channel-fixed footprint), and `region_inv_f_race_free` proves race-freedom for it — so the
canonical `mp_prog` idiom (write a shared cell, send a SIGNAL, recv, read the cell), which pattern-A `WT`
could not type, is now race-free via the general theorem (witnessed by `sig_*`).  So all THREE Go
ownership-transfer mechanisms — pointer-handoff, spawn-split, signal-handoff — have general abstract
race-freedom, now UNIFIED into ONE theorem: `WTf_spawn` folds the region-split spawn into the `flp`
typing, so `region_inv_f_race_free` alone covers all three for arbitrary programs (witnessed by `fcombo`:
a cell going g0 →spawn→ child →signal-channel→ g1, both mechanisms in one program, race-free for all
interleavings).  Still open: lifting from the `rstep` calculus to the EXTRACTABLE typed IO layer.  The
discipline `Owned ⇒ race-free` was always general; what is NEW is *earning* `Owned` for an arbitrary
transfer program (channel/spawn/signal) by an abstract `rstep` induction, not a hand-built per-shape proof.)*
  (And `GoInt`'s past-2⁶² deviation is *documented
unreachable in practice*, not *proved* unreachable; mitigated by the faithful `GoI64`/`GoU64`.)
None of this is new breakage — it is the same scope the RED reviews, gap #10, and the "Overclaimed
labels on true theorems" section already record, consolidated here so the words stay exact.

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
  genuine frontiers gate the FULL horror: (1) RECURSIVE / self-referential types — **CRACKED
  (2026-06-22) for a concrete recursive type, axiom-free, end-to-end to Go.** Valid Go recurses
  through INDIRECTION (pointer/channel/slice/map/func); only direct `type X X` / `struct{x X}` is
  rejected. The VALUE side is benign — `Inductive ListNode := MkListNode { ln_val ; ln_next : Ptr
  ListNode }` (`Inductive`, not the recursion-forbidding `Record` keyword; recursion through the
  TAG-FREE phantom `Ptr` ⇒ vacuously positive, accepted by Rocq). The supposed TYPE-TAG wall — that
  a finite `GoTypeTag` can't hold a cyclic `tagX = TPtr tagX` — was a **MISDIAGNOSIS**: a NULLARY
  nominal tag `TListNode : GoTypeTag ListNode` does NOT structurally contain itself (it's a base case
  exactly like `TBool`); the `ln_next : *ListNode` field's tag is the FINITE term `TPtr TListNode`.
  So the recursive TYPE gets a finite tag that round-trips through `tag_eq` (`tlistnode_tag_refl` /
  `tlistnode_selfptr_refl`, both `reflexivity`, assumptions = just `int : Set`), `*ListNode` cells
  live in the typed heap, and `linked_list_demo` heap-allocates + pointer-chains + TRAVERSES a real
  3-node singly-linked list → `1 2 3`. The SAME crack extends through a CHANNEL (2026-06-22):
  `Inductive ChanBox := MkChanBox { cb_id ; cb_chan : GoChan ChanBox }` = `type ChanBox struct { Id
  int64; Ch chan ChanBox }` with nullary tag `TChanBox` (the channel-of-itself tag is the finite
  `TChan TChanBox`) — so `chanbox_demo` makes a `chan ChanBox`, a goroutine sends `ChanBox{42, c}`
  whose `Ch` field IS `c`, main receives it → `42`. **"A CHANNEL THAT SENDS ITSELF", realized,
  axiom-free** (the explicitly-named north-star horror; `tchanbox_*_refl` rest on `int : Set`).
  REMAINING gap (genericity): each named recursive type needs its own nullary tag constructor in
  builtins.v (Rocq inductives are closed — main.v can't extend `GoTypeTag`); a user-defined recursive
  struct getting a tag automatically needs a named-type registry / plugin pass (deferred).
  (2) VERIFIED SAFETY on
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
   match.  `new` (pointers), `&x` (address-of-a-local, 2026-06-23 — `ref_as_ptr` →
   Go `&x`, the inverse of `ptr_as_ref`; provably never-nil + read/write aliasing
   theorems on the substrate base; fail-closed to addressable operands; `addr_of_demo`
   golden-locked), `copy`/slice-`clear`/`make([]T,len,cap)` (slice aliasing),
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
   the `hfield_get_set_same` proof verbatim.  `het_ptr_demo` → `11 true`, golden-locked, axiom-free.
   **GENERIC ARITY-FREE STRUCT REP DONE (2026-06-25, review #8/#9):** `StructRep2`/`StructRep3`/
   `StructRep2H` were arity-monomorphised copies (not a generalisation — `StructRep47` is the reductio).
   They are now REPLACED + DELETED in favour of ONE `StructRep R ts`: a struct is the heterogeneous
   NESTED PRODUCT `Tup ts` over its field-type list, a field is a TYPED de Bruijn index `Mem ts t`
   (`MHere`/`MNext` = Peano `FZ`/`FS`), and `GSPtr R` → `*R`.  This ALSO closes the #8/#9 defect class BY
   CONSTRUCTION: the old field API took a numeric slot AND a separate projection, tied by an erasable
   coherence a swapped dictionary could satisfy with a MISMATCHED pairing (wrong Go); here a field is the
   SINGLE index `m`, the projection is the COHERENCE-PINNED name (`gfield_coh m proj := proj = mem_get m
   ∘ sr_to`, erased), so slot and name CANNOT disagree.  Lowers to native Go (`&T{…}`, `*p`, `p.F = v`,
   `p.F`, `a == b`).  Stress-tested by `big64_demo`: a **64-field** heterogeneous struct (cycling
   `int64`/`bool`/`float64`/`string`) extracts a real 64-field Go struct and runs (`0 true x 999 x true
   false` — read at depths 0/1/3/4/63, mutate-through-pointer, structural `==`); all earlier demos
   (`Cell`/`Cell3`/`Pair` + pointer-receiver methods + `Node` embedding) migrated onto it, output
   byte-identical.  API is receiver-first (`p` before the index).  Residual: full canonicity of the rep
   vs the Go field order remains the trusted-plugin bridge (gap #10).  *Not yet:* pointer-receiver method
   expressions `(*T).M`; method-name namespacing via Rocq `Module`s (so two types can share `Area`).
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

### RELEASE REVIEW #4 (2026-06-23) — resolution: defect CLASSES closed, overclaims re-scoped

Verdict was RED (head c8400932). Central critique CONFIRMED firsthand: prior fixes repaired the OBSERVED
demo instance but docs promoted each to "whole defect CLASS closed" — false; the source language still
admitted invalid-Go / silent-wrong programs outside the curated demos. Each finding is now closed by
FAILING-CLOSED the class (fail-loud `unsupported`) or making it genuinely correct, with a NEGATIVE source
test (a `Fail`/abort) or a runtime golden lock that the un-demoed instances also hold:

- **P0 #1 — platform-int distinctness (CLOSED, commit 60a71b6).** `GoUint`/`GoIntN`/`GoUintN` were
  transparent `:= int` aliases rendered as DISTINCT Go types (invalid Go like `func(x int) uint`; `any`
  mis-tagged). `GoUint` is now a genuinely distinct record (`Tagged_GoUint := TUint`, unique); the 7 dead
  bare-int placeholders RETIRED; `GoRune` re-pointed to the faithful `GoI32`. Negative `Fail` tests +
  runtime `uint_lock_demo`. So "DISTINCTNESS airtight" / the INJECTIVE tag→Go-type map are now ACCURATE
  (were the hole P0 #1 named).
- **P0 #2 — CPS continuation-loss (CLOSED, commit 6d4b3d8).** The comma-ok intrinsics
  (`slice_at_ok`/`ptr_get_ok`/…/`type_assert_safe`, select-recv) kept `recv_ok`'s old fail-open
  `|_->k_body`; now one shared `unsupported` for a non-inline handler. Permanent named-handler neg-fixtures.
- **P1 #3 — raw-CFG nonzero-entry (CLOSED, commit 72a489c).** `run_blocks` with a nonzero entry emitted
  `goto blockN` with no label; now validates the entry + every jump target in range (else `unsupported`)
  and labels the nonzero entry. So "raw goto fallback always correct" is now ACCURATE (validated).
- **P1 #4 — destination-typed narrow conversions (CLOSED, commits a4e715d, 31ca614, 6926948, 2eb8aac,
  ac8250b, 69dd071, 8993a8d).** The typed-lowering crux. A wide int64-carried value into a NARROW
  destination was emitted bare (invalid Go) at EVERY boundary the review listed; now cast via the unified
  `narrow_dest_conv`/`narrow_go_name`/`pp_narrow_or`/`func_param_types` helpers at: narrow→wide widening,
  struct fields, slice/array elements, pointer/channel payloads, map keys+values, and function args. So
  R4(d) "every position" is now genuinely true (method-arg + erased-arg/generics×narrow residuals also
  CLOSED — commits a134f7d, aeb8ae1). Each boundary has a runtime golden lock. **The last narrow-destination
  residual — narrow `Ref` type-identity — is now CLOSED too (2026-06-23).** A `Ref GoU8` was lowering to the
  `int64` carrier (a latent type-identity gap: model `GoU8` vs Go `int64`, observable only via box+assert —
  the P0 #1 class), because `ref_new` emitted the cell's init bare. FIX (go.ml): `ref_new` now casts the init
  via its tag (`pp_payload_at_tag`, like `ptr_new`), so the Go cell is `uint8`; `ref_set` casts the value via
  `value_narrow_conv` (the value's OWN narrow Go type — `ref_set` carries no tag, but the value has the same
  source type `A` as the ref, so it supplies the cast). COMPLETE, no fail-open residual: an already-`uint8`-typed
  value (param / let-var / narrow-returning call) needs no cast (`uint8 = uint8`); only the int64-carrier narrow
  OP results do, and `value_narrow_conv` detects exactly those. Non-narrow refs (`TInt64`/…) byte-identical
  (`pp_payload_at_tag`/`value_narrow_conv` decline). Runtime lock `narrow_ref_demo` → `true false` (a `Ref GoU8`
  asserts to `uint8` not `int64`; was `false true`). Turned out NOT to need the feared ref-var tracking.
- **P1 #5 — session "full safety+liveness" (RE-SCOPED, not a code bug).** Restated above (search "review #4
  P1 #5"): forge-proof discipline + conditional successful-trace soundness PROVED; unconditional
  liveness/termination NOT (SLift admits `panic`; emits theorems conditional on `PEmits`). PARTIAL.
- **P1 #6 — generated-name injectivity (CLOSED, commit 43b2703).** `Dtype` aliases now registered; each
  record's exported field names scanned for a collision (`x'`/`x_` → `X_`) → `unsupported`. So R7's
  injectivity claim now covers type aliases + struct fields too.

The broader trust-base exactness (the plugin TCB, funext, the `Denotes` map, where the safety guarantee
reaches) was consolidated separately — see **END-TO-END TRUST BASE** above. Still open from review #4: the
R10 GATES (a permanent negtest harness, a `Print Assumptions` manifest, a `go vet`/build gate, CI) — the
automation that would have caught these classes before a human review.

### ⛔⛔ RELEASE REVIEW (2026-06-22) — BACKEND FAILS *OPEN*: extraction emits plausible-but-wrong Go

**Verdict: RED. Do NOT call current `main` "formally verified Go", and do NOT extend the feature set
before fixing the backend.** A second external review (2026-06-22) found that the *extraction backend*
(`plugin/go.ml`) repeatedly substitutes plausible Go — `nil`, `any`, `return`, block-zero, a comment —
when it cannot preserve the source semantics. That is a direct violation of CLAUDE.md **rule 2**
("faithful or fail-loud; the plugin's `unsupported` ABORTS extraction for anything it can't lower
correctly — the meta-invariant"). These are **source-visible silent miscompilations**, independent of
the 2026-06-21 model/bridge breaks below (those were the *model*; this is the *compiler*). **The "9 of 10
breaks closed" status below is MODEL-LAYER only — it does NOT make the backend sound.** Findings that were
CONFIRMED VERBATIM in `plugin/go.ml` this session are marked ✓verified.

**P0 (release-blocking) — each is a fail-OPEN site that must become fail-LOUD (`unsupported`) or be lowered correctly:**
1. **Full-width int ops use constant, not runtime, semantics. ✓verified** (`go.ml` ~1015–1043): `i64_*`/`u64_*`
   lower to BARE Go operators (`x - y`, `-x`), no IIFE. But on *literal* operands Go evaluates them as
   arbitrary-precision UNTYPED constants. `u64_neg 1` (Rocq: `= 18446744073709551615`) would print `-1`
   (silent wrong); `u64_sub 0 1`, `u64_not 1`, `i64_add MAXINT 1`, `i64_div MININT (-1)` go wrong or fail
   `go build`. **Fix:** wrap in a runtime-typed IIFE `func(x,y uint64) uint64 { return x-y }(…)` — exactly
   the technique already used for float constants (`f32`/`f64`). Tier-2 numeric carrier note relates but the
   *constant-folding* bug is independent.
2. **Rocq types lost at local / interface boundaries. ✓CONFIRMED — REPRODUCED 2026-06-22** (narrow widths
   render `uint8`/`int8`/`int32`, but the expr printer assumes int64-carried; emits `:=` locals so Go RE-INFERS
   a type; the boxing repair inspects only the syntactic HEAD (`payload_head`/`fw_value_type`) so a
   `let`/projection/helper-call defeats it). **Exact reproduction:** `let xrepro := u8_of_i64 (i64_lit 4660) in
   println [any xrepro; …]` emits `xrepro := ((4660) & 0xff)` (Go infers `int`) and boxes `xrepro` BARE — vs the
   direct sibling `any (u8_of_i64 …)` which correctly boxes `uint8(((4660) & 0xff))`. So `any xrepro` has dynamic
   type `int`; `.(uint8)` FAILS though the model says `GoU8`, and `.(int)` SUCCEEDS — the exact model/runtime
   contradiction. Also: `i8_add` emits `& 0xff` (Go rejects 255 on `int8`); `i64_of_u8` emitted as identity
   (returns the narrow type where `int64` required); `str_at_ok` declares its byte result `int64`; a literal
   `GoI64`/`GoU64` boxed as `GoAny` defaults to Go `int`.
   **DEEP ROOT — the sub-issues are COUPLED by the int64-carrier representation:** narrow types are carried as
   int64 for arithmetic (so masked ops constant-fold; native `uint8(200)+uint8(100)` is a Go const-overflow
   error) but rendered as the REAL narrow Go type only at var-decls/boxing. Making narrows CONSISTENTLY their
   real type (so a let-bound `uint8` boxes itself) would then require fixing every op that assumed int64-carrier
   (`i64_of_u8` identity → `int64(x)` cast, masked arith → native arith on runtime narrow operands, …) — i.e. a
   type-DIRECTED emission (native op on a runtime narrow-typed operand, masked int64 op on a constant). This is
   the same runtime-vs-constant split as P0 #1's forcing, but per-type.
   **Semantics change by adding a `let` — fatal for an extractor. Fix (typed IR / expr-type environment):** emit
   every local, return, field init, interface box, channel send, and argument from the SOURCE Go type, never
   AST-inferred; the `GoAny` payload's tracked TYPE drives interface conversion (not `payload_head`).
   **PLANNED IMPLEMENTATION (least-invasive first slice, preserves the int64-carrier model):** record narrow-
   typed let-bound vars and apply the `uint8(…)` conversion at the box site — either (a) extend the `env`
   (currently an `MLident list`, threaded ~20 sites) to `(MLident * goType option) list`, or (b) a per-function
   `state` table `var-name ↦ narrow-Go-type` populated at the narrow `MLletin` (2 sites: pp_expr IIFE ~2050 +
   the pp_stmts `:=`) and consulted at the box (`pp_pa` ~1747, which has `env`), reset per function in
   pp_function (Coq names are function-locally unique). LATENT today (the golden demos box narrow values DIRECTLY,
   head visible) — so the fix is golden-byte-identical + re-verified by the repro boxing as `uint8(xrepro)`.
3. **Unsupported type tags silently become `any`. ✓verified** (`go_type_of_tag` ~552 `| _ -> "any"`, ~543
   `None -> "any"`; `zero_of_tag` ~563 → `any(0)`). For `TUnit`/`TArrow`/`TProd` the emitted `x.(any)` assertion
   SUCCEEDS for any non-nil iface, but Rocq `tag_eq` says `TUnit ≠ TI64` → `type_assert_safe TUnit` on an int64
   is `false` in model, `true` in Go: a clean silent contradiction. **Fix:** `go_type_of_tag` returns an ERROR
   (→ `unsupported`) for any unrenderable tag; only explicit `GoAny` maps to `any`; exhaustive over `GoTypeTag`.
4. **`slice_of_list` replaces runtime data with `nil`. ✓verified** (`go.ml` ~1500: non-literal spine → `[]T(nil)`).
   `fun xs => slice_of_list tag xs` returns `nil` for EVERY runtime `xs`. **Fix:** emit the runtime list
   expression if Coq-list/Go-slice share a rep, else `unsupported`. (Also ~1581 `(*T)(nil)` ptr case — audit.)
5. **CFG backend invents control flow. ✓verified** (`go.ml`: ~2613 non-literal `Jump`/start → `goto block0`/
   zero; unrecognized terminator → `return`; ~2924 non-literal block list → comment-only). A runtime-computed
   jump mapped to block 0 runs a DIFFERENT program; an unfamiliar branch → `return` truncates effects. The
   "raw goto is an always-correct fallback" claim is FALSE without first validating every start/target/
   terminator/block shape. **Fix:** every such default → `unsupported`; validate literal targets+bounds BEFORE
   the relooper runs. (This is gap #10's backend face; the verified `relooper.v` reference model does NOT
   excuse the emitter's fail-open defaults.)
6. **Builtins not identified by exact identity. ✓verified** (`from_builtins` ~173 scans for the SUBSTRING
   "builtins" anywhere in the dirpath → `mybuiltins` passes; `named` = basename + that scan; `catch`,
   string/rune convs, complex ops, struct-ptr ops, type-switch helpers, `fst`/`snd` suppressions all match on
   BASENAME). Innocent user code can be suppressed or rewritten as an intrinsic; name mangling (capitalize,
   `'`→`_`) has no collision handling and drops the source module namespace. **Fix:** register/compare exact
   `GlobRef` identities; fully-qualified registry keys; deterministic namespace mangling + collision detection.
7. **`Sess` is forgeable. — ✅ FULLY RESOLVED (model + EXTRACTED layer, 2026-06-22).** `MkSess` public → a term
   claims any protocol while wrapping `ret tt`; backend recognizes session ops by name, so a forged session
   emits no communication. The user chose the DEEPER fix over sealing (no Module-Type `Parameter`): a
   protocol-indexed INDUCTIVE session `PSess` (concurrency.v) whose only builders are the disciplined
   combinators, with soundness `psess_emits_proto`/`psess_full_emits_proto` proving its communication trace is
   EXACTLY `proto_steps i` — and `psess_send_nonempty` showing the `MkSess (ret tt)` forgery has no `PSess`
   counterpart. Axiom-clean (PrimInt63/PrimFloat only; no funext/Eqdep). **Brick 2 (2026-06-22): session
   DUALITY / communication safety** — `proto_steps_dual` (`proto_steps (dual p) = map flip_step (proto_steps p)`,
   fully Closed-under-global-context) + `psess_pair_complementary` (a client realising `P` and a server realising
   `dual P` emit exact mirror-image traces: each side receives precisely what the other sends, same types same
   order — no mismatch, no orphaned message; the classical session-types safety property). **Brick 3 (2026-06-22):
   session PROGRESS / deadlock-freedom** — a synchronized `pair_step` on the two endpoints' remaining protocols
   (matched `PSend A`/`PRecv A` cancel), `dual_pair_progress` (a dual pair is both-finished OR can take a matched
   step, and the stepped pair stays dual = PRESERVATION+PROGRESS) + `dual_pair_stuck_iff_done` (the ONLY stuck dual
   pair is `(PEnd,PEnd)` = DEADLOCK-FREEDOM). Both fully Closed-under-global-context (axiom-free). So the protocol-
   safety theory is complete. **Brick 4 (2026-06-22): session LIVENESS** — `pair_steps` (RTC of `pair_step`),
   `dual_pair_terminates` (every dual pair runs to completion at `(PEnd,PEnd)` — no infinite communication, no
   premature stop) + `dual_pair_step_deterministic` (the run is deterministic, no divergent choice). Both fully
   Closed-under-global-context. Plus a concrete bidirectional `pingpong` witness (`PSend GoI64 (PRecv GoI64 PEnd)`)
   exercising `PSRecv`: its client's trace = the protocol, and the pair terminates. **So the model-layer session
   theory is COMPLETE: soundness (1) + communication safety (2) + progress/deadlock-freedom (3) + termination/
   determinism (4)**. **Brick 5 (2026-06-22): run–trace coherence** — `pair_step_tr`/`pair_steps_tr` (the
   synchronized run recording each communicated `StepKind`) + `dual_pair_run_trace` (the run from `(P, dual P)` to
   `(PEnd,PEnd)` emits EXACTLY `proto_steps P`) + `pair_steps_tr_forget` (a traced run is a `pair_step` run). So the
   THREE trace notions coincide — protocol SPEC (`proto_steps`), session TERM (`PEmits`, brick 1), synchronized RUN
   — the terminating deterministic run carries precisely the protocol's messages. All Closed-under-global-context.
   FINDING (foundation): a FAITHFUL real-channel Rocq denotation (`PSess` → `IO` over a `GoChan`) stays BLOCKED — a
   heterogeneous session channel needs `GoChan GoAny` but `GoTypeTag GoAny` is universe-inconsistent (builtins.v:489),
   the SAME idealisation that forces `run_sess = ret tt`; so the extracted `run` remains plugin-lowered/idealised.
   **✅ MIGRATION DONE (2026-06-22, commit 2721403, golden BYTE-IDENTICAL):** the extracted `Sess` in builtins.v is
   now an INDUCTIVE (`SRet`/`SSend`/`SRecv`/`SLift`/`SBind`) replacing the record; `MkSess`/`run_sess` removed; the
   combinators `sret`…`slift` are thin wrappers, already in main.v's `Extraction NoInline` list so they stay named
   refs and the plugin's by-operation-name lowering fires UNCHANGED (emitted Go identical). `Sess` erases by name so
   the inductive erases like the record. **No plugin change needed.** Regression lock `Fail Definition bad_forge :
   Sess PingPong PEnd unit := MkSess (ret tt)` (main.v) — `MkSess` no longer exists ⇒ the forgery is UNTYPABLE (the
   build passing proves the `Fail` succeeds). **✅ UNIFIED (commit c2108b2, golden byte-identical):** the redundant
   `PSess` inductive in concurrency.v is gone — `PSess`/`PS…` are now ABBREVIATIONS for `builtins.Sess`/`S…`, so
   bricks 1–5 are proved DIRECTLY about the extracted type (no isomorphic-but-separate gap). **R9 is FULLY CLOSED:
   the emitted `Sess` is forge-proof and its successful-trace soundness is proved about that very type — PARTIAL/
CONDITIONAL correctness, NOT unconditional "full safety+liveness" (review #4 P1 #5: `SLift` embeds arbitrary `IO`
incl. `panic` at ANY index, and the emits theorems are conditional on a `PEmits` derivation an aborting/`Void`
computation lacks, so they apply only to NORMALLY-RETURNING terms; unconditional liveness/termination is NOT
proved — see the RELEASE REVIEW #4 resolution below).** The
   only residual is the documented idealisation (the channel `run` stays plugin-lowered, `GoTypeTag GoAny` universe
   block) — principled, not a hole.

**P1:**
8. **Headline overclaims.** Keep the public claim at **"verified model components with a trusted (currently
   fail-open) extraction backend"** until a compiler-correctness theorem connects MiniML/source semantics to
   emitted Go. The concurrent model is still NOT proven to BE the emitted semantics — the
   multi-goroutine→Go bridge is prose, not an end-to-end adequacy theorem (gap #10). (The specific
   model-faithfulness gaps the 2026-06-23 review #6 flagged here are CLOSED at the model level: channels
   are now BOUNDED — the capacity-guarded `rstepC` with a cap-0 rendezvous + a send-block-aware deadlock
   theory `rstuckC_blocked`/`send_block_rstuckC`, now completed to the SINGLE biconditional
   `rstuckC_iff_blocked` (a config is `RStuckC` iff every live goroutine is done/blocked/panicking) over
   ALL bounded programs — buffered AND unbuffered — via the general-cap progress converse
   `ready_can_stepC_general` (its cap-0 rendezvous decided by a bounded `find_partner` search) and
   `rstepC_stepper_ready`, #2; `go_spawn` and `defer_call` FAIL LOUD in the
   sequential `run_io` rather than sequentializing / discarding a child panic / dropping the deferred —
   the faithful semantics are `rstep_spawn` and `run_cmd`'s `CDfr`, #5/#12; `run_blocks` exhaustion is a
   LOUD distinct panic, never a silent success, #6; the function zero is a non-callable `NilFunc`, #8.)
   Wording: "**no project-declared Fido axioms**" is accurate; "**axiom-free**" is NOT (depends on
   `functional_extensionality` in places) — fix that phrasing in SPEC_CONFORMANCE.md / docs.
9. **Gates weaker than claimed.** `make check` runs ONE demo and diffs text output — numeric output cannot
   distinguish `int`/`uint8`/`int64`/`uint64`, so it systematically MASKS the type-identity bugs (#1, #2). The
   pre-commit hook only re-extracts when a `.v`/`plugin/` file is staged → a gofmt-clean hand-edit to `main.go`
   ALONE bypasses re-extraction (and the hook is opt-in). An `MLaxiom` is emitted as a runtime
   `panic("axiom: …")` rather than aborting extraction (a latent axiom compiles if its path isn't run). No CI
   status on the reviewed head.

**REPAIR ORDER (supersedes the feature/relooper roadmap until P0s are closed — this IS the "no punting on
correctness" mandate):**
1. **Fail closed:** remove EVERY `nil` / `any` / block-zero / comment-only / `return` fallback → `unsupported`.
   Incremental & loop-friendly: one fallback → `unsupported` per tick, each with a NEGATIVE fixture (a `.v`
   that must fail at EXTRACTION), verifying the golden's legitimate paths still extract. Do this FIRST — it
   converts every silent miscompilation into an honest abort, immediately restoring rule 2.
2. **Real expression typing:** typed locals/casts/interface-boxing/returns/sends/stores/closures from the
   SOURCE type (a typed IR or expr-type env). Closes #1's typing half and #2.
3. **Constant/runtime boundary:** full-width int ops → runtime-typed IIFE (#1).
4. **Exhaustive, identity-based** tag + intrinsic lowering (#3, #6).
5. ~~**Seal `Sess`** (#7 / break #3).~~ ✅ DONE at the model layer the DEEPER way (2026-06-22): forge-proof
   inductive `PSess` + soundness in concurrency.v (no seal, no `Parameter`). Remaining: migrate extracted `Sess`.
6. **Differential + metamorphic tests:** direct vs let-bound, literal vs runtime var, local vs global, inline
   vs helper, full type-tag-assertion matrix (#9). A golden that masks type identity is not a gate.
7. **CI clean-extraction gate:** rebuild from Rocq, re-extract, require ZERO generated diff, compile positive
   fixtures, require negative fixtures to fail AT EXTRACTION (#9).
8. **Hold the headline** at the honest wording until a compiler-correctness theorem exists (#8).

This review does not invalidate the verified model/proof work — it bounds the *claim*. The model components are
real; the *backend that lowers them to Go is the unverified, currently-fail-open frontier*, and closing it
(fail-closed first, then typed lowering) is now the top priority.

**STATUS (2026-06-22, after the fail-closed + typed-lowering loop arc) — most P0s CLOSED:**
- **#1 (full-width int constant semantics) — ✅ FIXED.** Unary (`u64_neg`/`i64_neg`/`*_not`, commit 19162e0) and
  binary (`add`/`sub`/`mul`/`div`/`mod`/bitwise/shift, 4fd96a9) full-width int ops now force constant operands
  through a typed IIFE (comparisons exempt); `u64_neg 1` emits `18446744073709551615`, not `-1`. golden-identical.
- **#3 (unknown tag → `any`) — ✅ FIXED** (b7a23e5): `go_type_of_tag`/`zero_of_tag` abort on an unrenderable tag.
- **#4 (`slice_of_list` → `nil`) — ✅ FIXED** (51ceed5): non-literal list aborts.
- **#5 (CFG invents control flow) — ✅ NOW FULLY FIXED (structured + raw)** (8fefdbc + 72b1617 + 30619aa +
  **R1 below**): the *structured* `walk` emitter (`go.ml` ~2950–3003) and `raw_term` (~1520–1528) were fixed
  earlier; an overclaim ("#5 FIXED") was corrected when **review #3 R1** found the RAW block-body emitter
  `emit_block` STILL failed open (non-bool 2-branch match → bare `return`; non-1/2-branch → bare `return`;
  unrecognized block → bare `pp_expr`, reachable via defer/go closures + the raw `run_blocks` fallback). **R1
  closed that** — see the RELEASE REVIEW #3 section; all three `emit_block` fallbacks now `unsupported`
  (2462 context-aware: a void closure body still emits, a run_blocks block fails loud).
- **#6 (identity-based recognition) — ✅ FOUNDATIONAL + bulk done** (868aa39 exact-component `from_builtins`;
  86b2124/9b68589/ea2b36f/02eb5db gate ~66 recognizers on it). Remaining tail (GoTypeTag-ctor machinery,
  suppression list, stdlib basename-fallback drops) is LOW-marginal (requires a user to name a def exactly like a
  Fido intrinsic in a non-builtins module).
- **#2 (types lost at boundaries) — ◑ slice 1 (let-boundary) FIXED** (34318ad): a narrow value through a `let`
  now boxes as its real Go type (`uint8(x)`), so `.(uint8)` succeeds. Remaining (deeper, coupled, LATENT):
  narrow values at projection/param/field boundaries (the full type-directed emission — native op on a runtime
  narrow operand vs masked int64 on a constant). **PRECISE DIAGNOSIS (2026-06-22, firsthand):** the narrow
  CARRIER is Go `int` (a narrow literal `u8_lit 200` emits `(200 & 0xff)`, an untyped-constant expression →
  `int`; narrow op results are masked-int expressions). The mismatch bites only for RUNTIME narrow values
  (params/fields), NOT constants (untyped constants are assignable to any numeric type). `pp_param` (go.ml
  ~3753) renders a narrow param `x:GoU8` as `uint8` via `go_prim_type_table`, so the body's carrier
  arithmetic `(x+x) & 0xff` makes `0xff` (255) overflow `int8` → a Go BUILD error (loud, not silent — so
  NOT a soundness hole, but an ungraceful feature gap). The same carrier-vs-declared mismatch hits the
  RETURN (`return x` with `x:int` carrier against a declared `int8`/`int64`) and struct FIELDS — they are
  COUPLED (one coherent fix, not three). Two design options, the SECOND preferred for faithfulness: (A)
  uniform-carrier — render every narrow type as `int` in signatures/fields, re-cast `uint8(x)` only at
  boxing/assertion (simplest, but Go signatures show `int` not `uint8`, and broad surface area: structs,
  map keys, channel payloads with narrow fields); (B) FAITHFUL — keep `uint8` signatures, INSERT a carrier
  conversion at each boundary crossing (widen `int(x)` at param entry, `int8(expr)` at return/field-write).
  (B) is the type-directed conversion-insertion refactor — genuinely multi-tick (every narrow boundary),
  the documented next backend frontier. Boxing-ONLY narrow params already emit correct Go (the declared
  narrow type matches the model), so a blanket fail-closed abort would over-reject; a precise guard needs
  body use-analysis. Deferred WITH this scoping, not punted.
- **#7 (`Sess` forgeable) — ✅ RESOLVED at the model layer (2026-06-22; user took the rule-3 policy call).**
  Decision: the DEEPER fix, NOT sealing — sealing needs opaque module ascription (a Module-Type `Parameter`,
  which brushes rule 3) whereas the deeper fix needs none. Brick 1 landed: a protocol-indexed inductive `PSess`
  (concurrency.v) + soundness `psess_emits_proto` (its trace is EXACTLY `proto_steps i`) + `psess_send_nonempty`
  (the `MkSess (ret tt)` forgery has no counterpart). Axiom-clean. Remaining bricks: denote `PSess` into the
  channel `IO`, then migrate the extracted `Sess` onto `PSess` (retiring `MkSess`).
- **#8 headline / #9 gates — partially addressed** (CLAUDE.md headline corrected; the `|| true` gate was already
  fixed pre-review). Full differential/CI harness (repair steps 6–7) still open.
Net (⚠️ CORRECTED by review #3, 2026-06-22): the FIRST review's enumerated fail-OPEN sites are closed, but that
review was NOT exhaustive — **review #3 (below) found MORE silent-miscompile sites the first sweep missed**
(`emit_block` raw block-body, `recv_ok` continuation-drop). So "the backend's silent-miscompile sites are CLOSED"
was itself an overclaim. The accurate status: a SUBSET of fail-OPEN sites is closed; closing the rest (review #3
R1/R2 first) is the live fail-closed work, ahead of the deeper typed-lowering (#2 param/field) and the
verified-compiler theorem (#8).

### ⛔⛔ RELEASE REVIEW #3 (2026-06-22, independent) — MORE silent miscompiles + invalid-Go + model gaps

**VERDICT: RED — "Do not release Fido as a correctness-preserving or 'verified Go' compiler."** A THIRD
independent review (reviewed commit 031c133, plugin blob 57b7fa51; Go 1.23.2 linux/amd64 probes of emitted
fragments; not a full extraction build). It found (a) backend silent-miscompile paths the earlier sweeps MISSED
— including one that **falsifies our "#5 FIXED" claim**, (b) several constructs that emit INVALID or falsely-typed
Go, and (c) model-to-runtime semantic gaps. Findings I CONFIRMED verbatim in `plugin/go.ml` this session are
marked ✓verified. **This review SUPERSEDES the "most P0s CLOSED" status above for release purposes.**

**P0 — fail-OPEN silent miscompiles (must become `unsupported`; the TOP fail-closed work):**
- **R1. Raw CFG emitter `emit_block` silently truncates. ✅ FIXED (this session, golden byte-identical).**
  ✓verified (`go.ml` ~2455–2461): a non-bool 2-branch match → bare `return`; a non-1/2-branch match → bare
  `return`; an unrecognized block → bare `pp_expr` with NO control terminator. Reachable via **defer/go closure
  bodies** (`emit_closure` ~2406, which goes through `emit_action` from BOTH the raw and structured emitters)
  and the raw `run_blocks` fallback (`emit_raw`). **This is why "#5 FIXED" was wrong** (only the structured
  `walk` was fixed). FIX: threaded a `terminating` flag through `emit_block`; the two bare-`return` arms now
  `unsupported` ALWAYS (silent truncation in both contexts); the bare-expression arm `unsupported` in the
  TERMINATING (run_blocks-block) context but still emits a valid void single-action body in a NON-terminating
  (defer/go closure) context. Golden byte-identical (the fallbacks were dead for current demos). NEGATIVE
  FIXTURE proved the guard FIRES: a non-bool 2-branch `match` in `defer_loop_demo`'s defer body (a run_blocks
  closure) now aborts extraction ("a non-bool match would silently become a bare `return`, truncating the
  block's control flow") — pre-fix it silently emitted a bare `return`.
- **R2. `recv_ok` drops its continuation. ✅ FIXED (this session, golden byte-identical).** ✓verified (`go.ml`
  3050–3051 stmt, 1706–1707 expr): the statement lowering assumed the continuation is an inline 2-arg `MLlam`;
  for ANY other shape (a named/separately-extracted handler, eta-reduced, etc.) it emitted `_, _ = <-ch` and
  NEVER emitted the continuation body. The expression position emitted only `<-ch`, discarding `_kont` entirely.
  So a non-inline continuation was silently dropped (the recv still happens; subsequent effects vanish). FIX:
  both the non-`[x;ok]` statement branch and the expression-position fallback → `unsupported`. Golden
  byte-identical (all demos use inline `fun x ok => …` continuations in statement position). NEGATIVE FIXTURE
  proved the guard FIRES: `recv_ok TI64 ch recv_neg_handler` with a NAMED handler (extraction did NOT inline it)
  aborts extraction ("its body cannot be lowered inline; emitting `_, _ = <-ch` would silently DISCARD it") —
  pre-fix it emitted `_, _ = <-ch`, dropping the handler.

**P1 — emits INVALID or falsely-typed Go (should be negative extraction tests):**
- **R3. Value-position lets/lambdas forcibly typed `any`** — ✅ **the value-position LET is FIXED** (this session,
  verified end-to-end); the `any`-lambda + `Tdummy…→any` remain (latent, deeper). CONFIRMED in source: a
  value-position `let` emitted `(func() any { x := e1; return e2 })()` (go.ml MLletin arm) — `any` in a typed
  context (e.g. inside int64 arithmetic → `int64(any)`) does NOT compile. **FIX:** an expression-position `let`
  is PURE (referentially transparent), so it is now INLINED via `ast_subst e1 e2` (`e2[Rel 1 := e1]`) — no IIFE,
  no `any`; the surrounding context types the result. Verified: new demo `vlet (x z : GoI64) := i64_add (let y :=
  i64_add x x in i64_add y y) z` COMPILES and computes `21` (was `int64((func() any {…})())` → build error);
  model `Example vlet_val = 21`. Golden `+21`. REMAINING (latent — golden has ZERO `func() any`/`any) any`):
  the untyped LAMBDA `func(x any) any` (go.ml MLlam arm ~2142) is wrong where a concrete `func(T)R` is expected —
  needs the EXPECTED function type (expected-type threading, the deeper #2/R3 work); and `Tdummy`/`Tunknown`/
  `Taxiom`/`Tmeta` → `any` in `pp_type`. Both effectively dead today (Fido HOFs are interface/method-dict typed),
  but the deeper typed lowering is the remaining R3.
- **R4. Several constructs emit invalid/falsely-typed Go:** (a) `map_make` → `make(map[any]any)` — not assignable
  to a typed `map[K]V` (probe failed); (b) `map_make_typed` accepts non-comparable key tags (slice/map/func) — Go
  rejects non-comparable map keys; (c) **non-empty list literal fallback → `append(nil, v1, v2)`** — Go rejects
  (`first argument to append must be a slice; have untyped nil`); (d) **signed narrow arithmetic on a narrow
  PARAM** — `int8` param + `(((x+1)&0xff)^0x80)-0x80` → `0xff` overflows `int8` (this is the #2 param-boundary;
  the narrow boundary — RETURN, PARAM, and consumption — is COMPLETE this session, see R4(d) below).
  **R4(c) ✅ FIXED (this session, golden byte-identical).** `go.ml` ~2192: the non-empty list-literal value-position
  fallback emitted `append(nil, v1, …)` (always-invalid Go — `append`'s first arg must be a TYPED slice, not
  untyped `nil`; the element type is erased so we cannot synthesize `[]T{…}` here). Now `unsupported`, directing
  to `slice_of_list <tag> [v1; …]` (which carries the element type → a typed `[]T{…}`). Golden byte-identical
  (the path was DEAD — `append(nil` appears nowhere in the committed Go). The fix is UNCONDITIONALLY correct (it
  only ever replaces provably-invalid Go with a loud abort). A standalone negative fixture proved IMPRACTICAL:
  reaching ~2192 needs a bare `list` value in value position, but Fido's list handlers (`print`/`println`/
  `slice_of_list`/`vararg`) intercept every reachable list use and the type system routes slice-typed values
  through `slice_of_list` — so 2192 is a generic fallback unreachable from well-typed demo code (exactly why it
  was a latent invalid-Go hole — review R10).
  **R4(a) ✅ FIXED (this session, golden byte-identical).** `go.ml` ~1731 (applied) + ~2080 (bare value): untyped
  `map_make` → `make(map[any]any)` lost K/V (the resulting `map[any]any` is the WRONG Go type — reads yield
  `any`, not the typed value, and it is not assignable to a typed `map[K]V`). Both sites now `unsupported`,
  directing to `map_make_typed`. Golden byte-identical (`map_make` is unused — every demo map uses
  `map_make_typed`). NEG-FIXTURE fired: `bind map_make (fun m => map_set TI64 TI64 … m)` aborts ("a bare map
  constructor — make(map[any]any) loses the key/value types").
  **R4(b) ✅ FIXED (this session, golden byte-identical).** `go.ml` ~1715: `map_make_typed kt vt` rendered ANY
  key tag, including the NON-COMPARABLE `TSlice`/`TMap` (→ `make(map[[]T]V)`, which Go rejects: "invalid map
  key type"). Added `tag_comparable_key` (rejects `TSlice`/`TMap`; `TArrow`/`TProd` already fail in
  `go_type_of_tag`); a non-comparable key now `unsupported`s. Golden byte-identical (all demo keys are
  int64/uint64/string — comparable). NEG-FIXTURE fired: `map_make_typed (TSlice TI64) TI64` aborts
  ("NON-COMPARABLE key type"). *Known deeper sub-case (noted, not yet closed):* a comparable check on a STRUCT
  key requires field-comparability analysis (a struct with a slice/map field would still slip through) — part
  of the typed-lowering phase.
  **R4(d) — narrow-boundary.** (HONEST HISTORY: this entry ORIGINALLY claimed "EVERY position" while only
  RETURN / PARAM / CONSUMED-by-arithmetic were covered — review #4 P1 #4 correctly falsified that. NOW genuinely
  complete across ALL destination boundaries via the P1 #4 slices: narrow→wide widening, struct fields,
  slice/array elements, pointer/channel payloads, map keys+values, and function args — see the RELEASE REVIEW #4
  resolution. Residuals DECLINE the cast rather than mis-cast: narrow params of methods / erased-arg functions,
  `ref_set`.) The original RETURN / PARAM / arithmetic fixes (golden `52 -56 201 -55`), two coordinated
  `go.ml` changes:
  - **RETURN:** a narrow return casts its int-carrier result to the declared Go type — `func lowbyte(x int64)
    uint8 { return uint8((x & 0xff)) }` (pre-fix: `return (x & 0xff)`, an `int64` against a `uint8` signature →
    build error). `narrow_prim_type` (parses the short `GoU8`→`uint8` name via `is_numint_type`, width ≤ 32) +
    a per-fn `narrow_ret_type` ref set in `pp_function`, consulted in `pp_pure_tail`'s `return`.
  - **ARITHMETIC widening:** every MASKED narrow op (`not`, `add`/`sub`/`mul`, `shl`, signed `div`/`mod`) now
    widens each operand to the int carrier (`int(x)`) BEFORE the `& mask`. So a narrow-typed operand — a `uint8`
    PARAM (`func inc8(x uint8) uint8 { return uint8(((int(x)+int(1))&0xff)) }`), or a signed-narrow CALL-RESULT
    consumed in signed arith (`consume_i8 = i8_add (lowbyte_i8 x) 1` → `int(Lowbyte_i8(x))`, which previously
    overflowed `int8 & 0xff`) — computes in `int` then masks. `int(…)` is a no-op on a constant/int carrier and
    a widen on a narrow type, so it is correct for ANY operand; signatures stay faithful (`uint8` params).
  Verified end-to-end: `lowbyte`/`lowbyte_i8`/`inc8`/`consume_i8` COMPILE and RUN correctly (`52 -56 201 -55`),
  with model-level `Example`s (`inc8 200 = 201`, `consume_i8 200 = -55`). Narrow struct FIELDS would follow the
  same widening if a demo needs them (no current demo has one).
- **R7. Generated identifiers not injective — ✅ collision now caught AT EXTRACTION (this session, golden
  byte-identical).** Two fixes (`go.ml`): (1) **`go_export` now `go_safe`s first** — a Coq name with `'`
  (e.g. `foo'`) previously emitted the INVALID Go identifier `Foo'` (or, if some sites `go_safe`d and others
  didn't, an inconsistent name); now every emitted identifier (decl AND call site — both route through
  `go_export`) is a valid Go name, consistently (`foo'` → `Foo_`). (2) **An explicit collision registry**
  (`register_emitted_name`): each emitted package-level Go identifier is claimed by its source identity
  (functions/vars by `global_path`, so CROSS-MODULE basename collisions are caught; types/enum-consts too); a
  second DIFFERENT claimant `unsupported`s — so `foo'`/`foo_`→`Foo_`, `foo`/`Foo`→`Foo`, and a type-vs-function
  clash abort at EXTRACTION, NOT via a Go `redeclared` error (which would be TOO LATE — the plugin must emit
  valid Go or fail loud itself). Plus `collect_decls` guards: two records/enums with the same typename, or two
  records with the same ctor name, abort (the silent metadata-OVERWRITE the review flagged). Golden byte-identical
  (no current name has `'`; no current collision). NEGATIVE FIXTURE fired: `Definition foo'`/`Definition foo_`
  both → `Foo_` aborts ("two distinct declarations both mangle to the Go identifier `Foo_`"). REMAINING R7
  sub-item (separate surface, not a decl-name collision): builtin RECOGNITION keys on any path component named
  `builtins` rather than the canonical `builtins.v` GlobRef — the backend #6 deep tail (low-marginal; a user
  must name a module `builtins` AND shadow a Fido intrinsic).

**P2 — model-to-runtime faithfulness gaps (the bridge, gap #10 / limit #2):**
- **R5. Plain `GoSlice` capacity — ✅ functional `cap` FIXED (this session, golden byte-identical).** CONFIRMED
  real: the model has `cap xs = len xs`, but the plugin emitted Go's native `cap(s)` (verified: `cap` reaches the
  plugin, is NOT inlined to `len`), and Go's capacity after `append` is IMPLEMENTATION-DEFINED (append may
  over-allocate), so the model's `cap = len` disagrees with the generated Go at runtime — a value `go build`
  accepts but that is WRONG (the "too late" failure mode). FIX: the plugin emits `unsupported` for `cap` on a
  functional `GoSlice` (golden byte-identical — `cap(` appears nowhere in the committed Go), directing
  capacity-aware code to the heap-backed `SliceH` (explicit `sh_cap` field); the model `cap` Definition is
  re-commented "proof-only; NOT Go's cap". NEGATIVE FIXTURE fired: `cap (slice_of_list TI64 [1;2;3])` aborts
  ("cap of a functional GoSlice — Go's capacity after `append` is implementation-defined …"). The functional
  `append` itself stays faithful (a functional slice has `cap = len`, no spare, so Go `append` always reallocs →
  fresh value, no aliasing — matching the value model). **DISCOVERED related `SliceH` bug (next):** `SliceH`'s
  `slice_append` realloc sets `sh_cap = len+1` but emits Go's native `append` (impl-defined realloc cap), so a
  SECOND append after a realloc can ALIAS differently (model: disjoint fresh backing; Go: maybe in-place into the
  over-allocated spare). No demo asserted post-realloc cap, so latent — but a real faithfulness gap. **✅ FIXED
  (this session):** `slice_append` now emits a manual realloc IIFE — in-place via Go's `append` when `len < cap`
  (faithful: cap unchanged), else `make([]T, len+1, len+1); copy(r, s); r[len] = v` — FORCING `cap = len+1` to
  match the model. New demo `slice_realloc_alias_demo` LOCKS the subsequent-append faithfulness: two appends
  (the 2nd hits the forced-cap realloc) → the slices are DISJOINT, so writing `s3[0]=99` is NOT seen through
  `s2[0]` (prints `0`, the model's disjoint value; pre-fix Go would over-allocate and alias → `99`). Existing
  slice demos (`9`, `77`) preserved; golden gains `0`. So the whole slice-capacity story is now honest: the
  functional value-slice `cap` fails loud (use `SliceH`), and `SliceH`'s capacity + aliasing are faithful.
- **R6. `PrimInt63.int` → platform `int`, divergent overflow — ✅ HONESTLY SCOPED (this session); a SUBSTRATE
  LIMIT, not a backend bug.** Go's `int` is, BY SPEC, 32-OR-64-bit (implementation-specific), so NO deterministic
  model is faithful on every platform — un-modelability is inherent to `int`. `GoInt := int` (Rocq `PrimInt63`,
  63-bit, Sint63-signed) is the chosen substrate carrier (it renders to Go `int`, idiomatic for `len`/`cap`/
  indexing — rendering as `int64` would force a cast at every such interop). Faithful to a 64-bit Go `int` in
  [−2^62, 2^62) (and [−2^31, 2^31) on 32-bit Go); an op whose result reaches ±2^62 wraps in the model where
  64-bit Go would not — but 2^62 ≈ 4.6e18 is far above any realistic index/length/size, so the divergence is
  UNREACHABLE in the index/size use case (no demo/theorem touches the boundary). This is exactly the
  "principled and bounded … substrate limit like Rocq's 63-bit primitive int" CLAUDE.md rule 2 PERMITS.
  **Correction landed:** a stale comment claimed `GoInt64` was the 63-bit `PrimInt63` — but `GoI64`/`GoU64` are
  now FAITHFUL full-64-bit RECORDS (Z-carried, wrap exactly at 2^64); they ARE the faithful path for code needing
  the guaranteed range. The remaining question — a per-op in-range proof to ENFORCE the bound — is deliberately
  NOT added: it is invasive for an unreachable case, and the faithful 64-bit alternative (`GoI64`) already exists.
  Docs sharpened in builtins.v (the `GoInt` block) + here; golden byte-identical (docs-only).
  **⚠ SUPERSEDED — being FIXED, not accepted (review #6 #13, user directive "ALL ints/uints → Z, no documented
  shortcomings"):** the "principled substrate-limit deviation" framing above is being RETIRED for the platform
  types — each is re-carriered onto `Z` (faithful full width, the `GoI64`/`GoU64` shape), so there is no residual
  63-bit wrap deviation to permit. **Platform `uint` (`GoUint`): DONE (commit 796281f)** — distinct `Z`-carried
  record, faithful `[0, 2^64)`, golden byte-identical. **Platform `int` (`GoInt`): NEXT** (atomic big-bang — `GoInt`
  is a pervasive type; the index/loop/len machinery already emits Go-native so it stays byte-identical, only the
  literal renderers migrate to the `Z`-literal path). The ONLY residual platform assumption then is the 64-bit
  *width* choice (Go's `int` is 32-or-64 by spec; we model 64), which is NOT a carrier deviation. Once `GoInt`
  lands, the line-10 "`int` bitwise/shifts — 63-bit substrate ✗ that cannot be closed" and the §2453 "uint64/uint/
  int full width ✗" entries also flip to ✓ and must be updated.
- **R8. Proof IO semantics ≠ emitted-Go semantics** (known two-models gap, itemized): buffered-channel alloc
  ignores capacity; recv from an empty OPEN channel returns a fabricated zero instead of blocking; `go_spawn` runs
  the child sequentially to completion in the denotational model; `defer_call` is a proof-side no-op while the
  backend emits a real Go `defer`. No compiler-correctness/refinement theorem connects source ↔ backend ↔ Go run.
  Accurate claim: "verified model components + a tested trusted backend," not "verified generated Go."
- **R9. `Sess` forgeable** (= backend #7 / 2026-06-21 break #3, still open): `MkSess` is exposed, so a value can
  claim any protocol while wrapping an unrelated `IO`. Seal the constructor or tie indices to operational
  semantics.
- **R10. Gates too weak** (= backend #9): `make check` compares golden OUTPUT only (misses
  type/interface/blocking/aliasing/overflow changes that preserve printed numbers); the pre-commit hook
  re-extracts only when selected files are staged (a standalone `.go` edit bypasses it); the axiom grep covers a
  subset. **AXIOM-GREP COVERAGE ✅ widened (this session):** the pre-commit `Axiom`/`Parameter`/`Conjecture`/
  `Admitted` check ran on builtins.v + main.v only; it now covers ALL FIVE theory files (+ concurrency.v,
  relooper.v, preamble.v) — an `Admitted`/`Axiom` in a proof-only theory previously slipped the gate. The
  Section-local `Hypothesis`/`Variable` the proof-only theories legitimately use are still allowed there (only
  the EXTRACTED files forbid top-level `Hypothesis`/`Variable`); `Print Assumptions` remains the definitive
  catch for a mis-discharged one. Verified: a temp `Admitted` in relooper.v now aborts the commit (it did not
  before); golden byte-identical. **AXIOM-MANIFEST GATE DONE (2026-06-23):** the Dockerfile's prover stage now
  captures the live `Print Assumptions main_effect` (re-run on every fresh build, since the driver `.vo` is
  forced out) and asserts the axiom NAME set EXACTLY equals the committed `EXPECTED_ASSUMPTIONS.txt` (42 names,
  the PrimInt63/PrimFloat substrate) via `LC_ALL=C sort -u` + `diff`; ANY drift — a new transitive/imported
  axiom (funext/Classical via a stray `Require`), an `Admitted` the grep missed — FAILS the build, not silently
  in a `Print Assumptions` nobody reads. Complements the pre-commit DECLARED-axiom grep (this catches TRANSITIVE
  ones). Verified both ways: passes on the real base; a deliberate mismatch (a sort-order delta during dev) fired
  the `AXIOM-MANIFEST DRIFT` abort exactly. **NEGATIVE-FIXTURE HARNESS DONE (2026-06-23, `make negtest`):** the
  permanent fail-closed regression gate the reviews wanted. `negtests/*.v` are programs that hit a fail-CLOSED
  backend site; each declares `(* EXPECT: <substring> *)` (the `unsupported` message it must abort with), and
  `negtests/run.sh` compiles each (standalone `rocq compile -R _build/default Fido`, OCAMLPATH at the built
  plugin) asserting the abort — a fixture that EXTRACTS instead = a reopened fail-closed site (the defect class
  the golden can't see). Locks 4 sites: `&x` non-addressable operand, `recv_ok` in expression position (R2),
  `slice_of_list` of a non-literal (P0 #4), non-comparable map key (R4(b)). Verified both ways: passes on the real plugin; a temp valid fixture
  (extracts fine) makes the harness FAIL exit 1. KEY: the in-`main.v` `Fail Go File Extraction` approach is dead
  (`Fail` doesn't catch the extraction `unsupported`; File Extraction hits an enum-collision) — a SEPARATE-build
  compile (its own fresh compilation unit) sidesteps both. **NON-BYPASSABLE (2026-06-23): `negtests/run.sh` now
  runs in the Docker prover stage on EVERY build (after the axiom gate), so a reopened fail-closed site fails
  `make check` itself; also `make negtest` locally.** The fixtures live OUTSIDE the theory's module list so
  `dune build` never compiles them as modules (the harness compiles each explicitly). FOLLOW-UP: more fixtures.
  **HOOK ANTI-TAMPERING HOLE CLOSED (2026-06-23):** the pre-commit hook re-extracted only on a staged
  `.v`/`plugin/` change, so a hand-edited `.go` with NO source change slipped through (contradicting its own
  "a hand-edit of *.go cannot survive a commit" claim). The trigger now also fires on a staged `.go`
  (`grep -qE '\.v$|^plugin/|\.go$'`) → re-extract overwrites the hand-edit with fresh prover output and the
  bare tampering commit aborts ("nothing to commit"). Docs-only commits still skip re-extraction (fast).
  **STILL OPEN (deeper R10 slices):** runtime DIFFERENTIAL tests beyond the type-identity matrix (now
  comprehensive); CI running `make check` (the token lacks Actions-policy permission here — can't verify-run,
  so deferred rather than ship an unverifiable workflow).
  **RUNTIME DIFFERENTIAL TEST ✅ started + caught a real bug (2026-06-22, commit 5cb8611):** `type_identity_lock_demo`
  (main.v) boxes each scalar and `type_assert_safe`s it against its OWN Go type (→true) and a sibling it must NOT
  alias (→false), turning type identity into observable output. On its FIRST run it caught a latent type-identity
  bug — a standalone `GoI64` literal emitted as a BARE decimal (`i64v := 9` ⇒ Go infers `int` not `int64`), so
  `any(GoI64).(int64)` returned FALSE, diverging from the `TI64` tag. **FIXED** (go.ml: `i64_lit`→`int64(N)`,
  `u64_lit`→`uint64(N)`); output golden unchanged for existing demos (`int64(9)` prints `9`). The runtime companion
  to the model-side `tag_runtime_agrees` lock (R6/#7d). The matrix should be EXTENDED to narrow struct fields / map
  values / channel payloads (likely more latent boxing bugs there).

**REPAIR ORDER (review #3) — fail-closed FIRST, in this order:**
1. **R1** (`emit_block` 3 fallbacks → `unsupported`) — the worst silent truncation, reachable via defer/go. ✅ DONE.
2. **R2** (`recv_ok` continuation-drop → `unsupported`/residual call). ✅ DONE.
3. **R4 negative tests** (`append(nil,…)`, `map[any]any`, non-comparable map keys, narrow-param arith → each
   `unsupported` with a negative fixture) + finish the narrow boundary (RETURN slice in-progress, then PARAM). ← NEXT.
4. **R3** typed lowering (the typed target IR / expected-type threading — the deep #2 refactor).
5. **R7** deterministic full-GlobRef mangling + collision check; exact-GlobRef builtin identity.
6. **R5/R6** model-faithfulness (slice cap; int63 range proof or honest scoping).
7. **R9** seal `Sess`; **R10** real differential/negative/from-scratch gate harness.
8. **R8** the refinement theorem (source ↔ backend ↔ Go) — the long-horizon capstone; until then, headline stays
   "verified model components + tested trusted backend," NOT "verified Go".
Until R1–R4 close, do NOT headline "verified Go" and do NOT extend the feature set (CLAUDE.md rule 2 + the
project's own fail-loud meta-invariant).

### ⛔ RELEASE-BLOCKING soundness breaks (external review, 2026-06-21) — verified against source

**VERDICT (own it, do not let it drift): these proofs do NOT currently verify the generated Go.**
There are valuable verified COMPONENTS, but the bridge from those components to actual Go behaviour
has multiple independent soundness breaks.  The accurate headline is "verified components over
honestly-modelled Go primitives, bridge status documented per item" — NOT "verified Go".  Every break
below was CONFIRMED verbatim in the source (not taken on faith).  Close these in the order given before
any "verified" claim.

**STATUS (2026-06-22): 9 OF 10 RESOLVED — #1, #2, #4, #5, #6, #7, #8, #9, #10 all closed (machine-checked,
golden byte-identical).**  ⚠️ **SCOPE: these ten are MODEL-LAYER / typed↔operational-bridge breaks. They are
NOT the backend. The 2026-06-22 review above found an INDEPENDENT set of backend fail-open miscompilations —
"9/10 closed" here does NOT mean release-ready; the backend P0s gate the "verified Go" claim too.**  Only
**#3 (Sess)** remains, DECISION-BLOCKED on a rule-3 policy call (a discharged
module-`Parameter` seal that adds no `Print Assumptions` axiom but uses the keyword rule 3 forbids, vs. keeping
it foundation-blocked pending a real session-IO semantics).  See each item below for its resolution commit.

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
   **→ SLICE 1 DONE (2026-06-22): the REALIZABLE coding + its honest BOUNDED round-trip are now PROVED**
   (`builtins.v`): `keystone_inj n := i64wrap (Z.of_nat n)`, `keystone_prj g := Z.to_nat (i64raw g)`, and
   `keystone_roundtrip : forall n, Z.of_nat n < 2^63 -> keystone_prj (keystone_inj n) = n` (machine-checked).
   This is the foundation the unbounded `Hret` falsely claimed for ALL `n` — it holds only on REPRESENTABLE
   values (which is every real Go int64).  The `concurrency.v` Keystone doc is corrected to state this
   honestly (the unbounded form is impossible; do NOT claim it).
   **→ SLICE 2 DONE (2026-06-22): the bridge is REFOUNDED on the bounded round-trip — the impossible
   `Hret` is GONE.**  The section now carries `Variable Vrep : nat -> Prop` + a REALIZABLE
   `Hypothesis Hret : forall n, Vrep n -> prj (inj n) = n` + `Vrep0 : Vrep 0` (instead of the impossible
   `forall n, prj (inj n) = n`).  Representability is threaded through the WHOLE single-goroutine bridge:
   `OnChan`/`OnLoc` require `Vrep` on sent/written values and restrict recv/read continuations to
   representable inputs; `SimInv` carries `Forall Vrep (rchan cfg c)` (buffer values representable),
   `SimInvMem` carries `Vrep (rc_heap cfg l)`; `siminv_step`/`siminvmem_step` preserve it; `denote_sim_recv`/
   `denote_sim_read` use the bounded `Hret`; `denote_adequate`/`denote_adequate_mem` go through unchanged.
   The section is now INSTANTIABLE — `Vrep := fun n => Z.of_nat n < 2^63`, `inj/prj := keystone_inj/prj`,
   `Hret := keystone_roundtrip`, `Vrep0` trivial — so the bridge is no longer vacuous: it genuinely
   connects the calculus to the emitted Go for representable (= real int64) values.  Builds; golden
   byte-identical (concurrency.v emits no Go); axiom base unchanged.
   **→ SLICE 2c DONE (2026-06-22): non-vacuity EXHIBITED.**  `denote_adequate_keystone` /
   `denote_adequate_mem_keystone` (concurrency.v) instantiate the bridge with the concrete keystone coding
   (`inj/prj := keystone_inj/prj`, `Vrep := Vrep64 := Z.of_nat n < 2^63`), DISCHARGING the section
   hypotheses (`keystone_roundtrip` is exactly `Hret`, `Vrep64_0` is `Vrep0`).  So the adequacy theorems
   hold for a REAL coding — the bridge is no longer a vacuous implication.  **BREAK #1 RESOLVED**
   (single-goroutine channel + heap fragment): the typed↔operational bridge connects the calculus to the
   emitted Go for representable int64 values, on a realizable, instantiated coding.  (Multi-goroutine
   adequacy / spawn remains future work — `go_spawn` has no `run_io` law, by design; that is the separate
   limit-#2 frontier, not break #1.)
2. **`map_size := 0` but Go `len` returns the real length.** `map_len` returns `map_size` (constant 0);
   plugin lowers `map_len`→Go `len(m)`; `map_demo` prints `3`.  Direct model/extraction disagreement.
   **→ RESOLVED (2026-06-22, proof-only, golden byte-identical).**  The map's `MapCell` now carries an
   `int` SIZE (live-key count) ahead of the existT — `map_size m w` reads it (was the constant-0 stub), so
   the model AGREES with the native `len(m)` the plugin emits.  `map_upd` does +1 only on a genuinely-new
   key (unchanged on overwrite), `map_rem` −1 only on a present key (unchanged if absent); `map_make_typed`
   / `map_clear` init it to 0.  Size sits OUTSIDE the existT (type-independent), so the value accessor
   `map_get_fn` and ALL value laws (`map_sel_upd_same`/`_diff`/`map_sel_rem`/`map_sel_clear`/`map_get_set_*`/
   `map_get_delete_*`) are UNCHANGED (the size threads as an extra `match` arg that `map_get_fn_write_same`
   ignores) — re-proved with no edits.  Witness `map_len_counts` machine-checks len = 2 after insert 1,2 +
   overwrite 1, then 1 after deleting 2.  Bodies suppressed (plugin emits `len(m)`), so golden unaffected;
   PrimInt63 base.
3. **Session discipline forgeable.** `Record Sess (i j) A := MkSess { run_sess : IO A }` with public
   `MkSess` — `MkSess (ret tt) : Sess P PEnd unit` typechecks for ANY `P`.  Linearity is not enforced.
   Fix: seal `Sess` behind a module signature, or make constructors embody the protocol transitions.
   **→ ANALYSIS (2026-06-21, scoped — NOT a break-#4-style cheap seal).**  Confirmed REAL wrong-Go: the
   plugin lowers sessions by recognizing `ssend`/`srecv`/`sbind`/`sret`/`slift` BY NAME (`go.ml` ~3399-3428);
   a forged bare `MkSess (ret tt)` falls through `pp_sess_stmts`' `| _ ->` arm to `pp_expr` and emits a
   no-op, so `run_session (MkSess (ret tt)) (MkSess (ret tt))` at e.g. `P := PSend nat PEnd` allocates a
   channel but NEVER communicates — the type claims a send/recv protocol, the Go skips it (runtime desync).
   **Why no erased-evidence (Squash) seal works here, unlike #4:** `run_sess` is IDEALIZED (`ssend := MkSess
   (ret tt)`; the channel effect is injected by the plugin by op-name, absent from the proof model), so there
   is NO protocol-realization relation over the idealized `IO` for a `cw_ok`-style field to prove.  **Two real
   paths:** (a) **module-ascription seal** — wrap the API in `Module S : SESS := SessImpl` whose signature
   omits `MkSess`, forcing every `Sess` through the protocol-correct combinators; tractable and needs no new
   foundation, but a SUBSTANTIAL refactor (Sess + 6 combinators + notations + main.v demos/`Fail` tests) with
   golden risk (must keep `S.Sess` extracting as unboxed `IO`, basenames `ssend`/… still recognized; opaque
   ascription introduces NO axiom).  (b) **real session-IO semantics** — make `run_sess` actually perform the
   send/recv so the indices are a provable consequence; this is limit-#2 foundation (the typed↔operational
   bridge).
   **→ ATTEMPTED & BLOCKED (2026-06-21).**  Tried the cheapest version of (a): an SProp CAPABILITY-TOKEN
   field on `MkSess` whose constructor is `Local` (so only `builtins.v` can mint it; SProp ⇒ erased ⇒
   golden-stable).  Rocq 9.2 REJECTS it: both `#[local] Inductive` and `Local Inductive` give "This command
   does not support this attribute: local," and `Private Inductive` restricts *matching*, not *construction*.
   So there is NO way to hide an inductive constructor short of opaque module ascription, which forces a
   Module-Type `Parameter`.  **This converts break #3 into a POLICY DECISION for the user:** permit a
   *discharged* Module-Type `Parameter` (verified to add no `Print Assumptions` axiom — honoring rule 3's
   PURPOSE while brushing its LETTER) to enable the module seal (a), OR treat #3 as foundation-blocked
   pending the session-IO semantics (b).  Until decided, the `Sess` doc now states the hole HONESTLY (the
   `Fail` discipline binds combinator-built sessions; `MkSess` remains forgeable).  No code seal landed;
   loop pivots to break #5 (`ValidWorld`, proof-only, no blockers) next.
4. **Evidence-carrying equality APIs carry NO evidence.** `ComparableW := {cw_eqb : K->K->bool}` and
   `struct_eqb (eqb) a b := eqb a b` — public constructors, no `forall x y, eqb x y = true <-> x = y`,
   both erase to native `==`.  `struct_eqb (fun _ _ => false) p p` = `false` in Rocq, `true` in Go.
   Fix: add the decidability field (SProp/erased) + seal the constructor.
   **→ FULLY RESOLVED (2026-06-21, both halves, golden-stable, no plugin change).**
   *ComparableW:* now carries `cw_ok : Squash (forall x y, cw_eqb x y = true <-> x = y)` (SProp-erased — the
   plugin drops the whole witness regardless of arity).  Decidability proved for all 4 instances
   (`i64_eqb_spec`/`u64_eqb_spec`/`str_eqb_spec`/the existing `point_eqb_spec`); `bogus_eqb_undecidable`
   machine-checks the always-`false` witness is unconstructable.
   *struct_eqb:* now takes `pf : Squash (forall x y, eqb x y = true <-> x = y)` between `eqb` and `a,b`.
   The KEY: an SProp argument is ERASED by Coq's extraction, so `struct_eqb eqb pf a b` extracts to the same
   3-arg MiniML the plugin already lowers to `a == b` (`[_eqb; a; b]`) — byte-identical Go, zero plugin
   change.  The forge `struct_eqb (fun _ _ => false) ? a b` is now unconstructable (`?` is unprovable).
   Net: both erasures to native `==` are SOUND, not forgeable.  Base: PrimInt63 only (no funext/irrelevance/
   Fido axiom).  **TECHNIQUE (reusable for the remaining seals): a `Squash (…spec…)` proof field/param is
   free at runtime (SProp-erased) yet structurally blocks every bogus constructor — the cheapest possible
   way to retrofit safe-by-construction onto an already-extracting, golden-locked API.**
5. **Allocation freshness asserted, never established.** Allocators use `w_next` with NO `ValidWorld`
   invariant (nonzero, > all live locs, no wrap).  "fresh"/"nonzero"/"disjoint" are comments, false as
   theorem-level claims over arbitrary `World`.  Fix: a `ValidWorld` invariant, loc 0 reserved.
   **→ RESOLVED (2026-06-21, commit pending, proof-only, golden byte-identical).**  `ValidWorld w :=
   (0 <? w_next w) ∧ (∀ l, w_next w <=? l → all three heaps None at l)` — allocator pointer positive (loc 0
   RESERVED for `nil`) and bounding the live region.  Two payoffs follow from the invariant ALONE:
   `valid_fresh_nonzero` (the minted loc `w_next w` is nonzero ⇒ a fresh ptr/chan/map is never nil) and
   `valid_fresh_disjoint` (it is None in all three heaps ⇒ the install overwrites nothing — no aliasing).
   `valid_w_init` (empty heaps, `w_next = 1`) is the base; `valid_run_ref_new`/`valid_run_make_chan`/
   `valid_run_map_typed`/`valid_run_map_make` prove EACH allocator (by name, via `run_io … = ORet r w'`)
   carries `ValidWorld` to its output world — so every world reachable by a finite allocation sequence is
   valid.  Preservation needs `HasRoom w := to_Z(w_next w)+1 < wB` (no wrap); exhausting 2^63 locations is
   the documented PrimInt63 substrate limit (same finiteness as `GoI64`), NOT a soundness gap.  Base:
   PrimInt63 only (`Uint63Axioms.*`), no funext / proof-irrelevance / Fido axiom.  Freshness is now a
   THEOREM, not a comment.  (Feeds break #6: loc 0 reserved is the hook for real nil blocking/panic.)
6. **Nil aliases location 0; raw nil ops fabricate objects.** Nil chan/map/ptr = loc 0; send/close on
   nil chan, assign to nil map, write through nil ptr all "succeed" (Go blocks/panics), and all nils of
   a kind alias loc 0 (one bad write corrupts all).  (Nil-DEREF panic is in the excluded "nil/div"
   scope; nil-chan-block and nil-map-panic are NOT, and the aliasing is a representational break.)
   **→ POINTERS DONE (2026-06-21, golden byte-identical).**  Raw `ptr_get`/`ptr_set` now PANIC on a nil
   pointer (`if eqb (p_loc p) 0 then OPanic … else …`), faithful to Go's `*nil` (which the plugin already
   emits as `*p`, panicking natively) — closing the "fabricate a zero / silently write loc 0" gap.
   `ptr_get_nil`/`ptr_set_nil` machine-check the panic; `ptr_get_set_same` re-proved UNCONDITIONALLY (on
   nil both sides panic at the `ptr_set` step, so they still agree).  Break #5 justifies the `eqb … 0`
   guard exactly separating live cell from nil (loc 0 reserved).  The Keystone/MpTyped bridge gained a
   `ptrenv_live` hypothesis (its pointers are allocated ⇒ non-nil) so the raw derefs coincide with the
   bridge ref-accesses.  Lowered by name ⇒ golden unchanged; demos deref only live pointers.  Base:
   PrimInt63 + the pre-existing funext holdout (`run_io_inj` for IO equality), no NEW axiom.
   **→ MAPS DONE (2026-06-21, golden byte-identical).**  `map_set` on a nil map (`MkMap 0`) now PANICS
   (`if eqb (gm_loc m) 0 then OPanic … else …`) — Go's "assignment to entry in nil map" — instead of
   fabricating a cell at loc 0.  `map_set_nil` machine-checks it; `map_get_set_same` re-proved
   unconditionally (nil ⇒ both sides panic at `map_set`), `map_get_set_diff` gained a non-nil hypothesis
   (its post-state is only `map_upd` on a live map).  Nil-map READ already returns zero (`map_get_empty`,
   Go-faithful) and `delete`/`clear` on nil are no-ops (no guard added) — only assignment panics.  Lowered
   by name ⇒ golden unchanged; demos write only allocated maps.
   **CLOSED-WORLD SAFETY (the point — modeling the panic is only half).**  The modeled nil panic plays
   TWO roles: (1) COMPLETENESS (faithful to Go), and (2) DEFENCE — a cheap RUNTIME guard for the future
   OPEN WORLD (imports), where proofs rest on axioms about external code that could be WRONG; the check
   turns "an import handed back nil" into a loud panic, not silent heap corruption.  But in the CLOSED
   WORLD the "oops" must NEVER fire, and now it provably can't: `ptr_new_nonzero` / `map_make_typed_nonzero`
   (from break #5's `valid_fresh_nonzero`) prove an allocated handle is non-nil, and `ptr_set_nonnil` /
   `ptr_get_nonnil` / `map_set_nonnil` show the panic branch is then DEAD — capped by `ptr_alloc_assign_no_panic`
   / `map_alloc_set_no_panic` (*allocate then use ⇒ provably no panic*).  The OPEN-WORLD boundary (an
   ARBITRARY handle) still guards via `ptr_get_ok` / `ptr_is_nil`.  **Aspiration (recorded as the bar): NO
   panic class — nil, div-by-zero, OOB, send-on-closed, failed assert — reachable in a well-formed
   closed-world program; the evidence-carrying APIs (`div_nz`, `slice_at`, these) are the bricks, and the
   eventual capstone is a global progress/"no-stuck" theorem (cf. break #7, universal safety).**
   **→ CHANNELS: close DONE (2026-06-21, golden byte-identical).**  `close_chan` on a nil channel
   (`MkChan 0`) now PANICS ("close of nil channel") via an `eqb (ch_loc ch) 0` guard before the
   double-close guard; `close_chan_nil` machine-checks it.  `run_close` gained a non-nil hypothesis,
   `run_close_closed` stays unconditional (nil OR closed ⇒ panic), `send_closed_panics`/`double_close_panics`
   gained the non-nil hypothesis (a nil channel panics at the *first* close).  Closed-world safety:
   `make_chan_nonzero` (allocated channel is non-nil, from break #5) ⇒ `chan_alloc_close_no_panic`
   (allocate-then-close ⇒ provably no nil panic).  No concurrency-bridge ripple (close isn't used there).
   **STILL OPEN: nil-CHAN send/recv BLOCK FOREVER** — Go deadlocks; NOT expressible as a returning
   `Outcome` (`run_io` total), and a fail-loud `OPanic` over-approximation would ripple through the ENTIRE
   channel concurrency bridge (D_send/D_recv, mp_handoff, MpReach).  Faithful modeling needs a
   divergence/"stuck" outcome (foundation) — deferred honestly; UNREACHABLE in the closed world anyway
   (`make_chan_nonzero`), and it is the same "blocking idealised away" limitation already documented for
   `recv` on an empty-open channel.  The **aliasing** point (all nils share loc 0) is now benign for ptr,
   map, AND chan-close.  OPEN-WORLD WRITE guards (`ptr_set_ok`/`map_set_ok` comma-ok, parallel to
   `ptr_get_ok`) remain a follow-up — they need plugin lowering.
7. **Runtime tag identity ≠ Go type identity.** `TInt64` tags Rocq `int`, `TI64` tags `GoI64`; both
   lower to Go `int64`, but `tag_eq` distinguishes them → a `TInt64`-boxed value asserted at `TI64`
   fails/panics in the model while Go's `int64` assertion succeeds.  Fix: one canonical runtime tag per
   emitted Go type, separate from proof-side carriers.
   **→ SCOPED (2026-06-21, deep investigation — LARGER & subtler than the one-liner; needs a representation
   decision before coding).**  The real structure: `GoTypeTag` has TWO numeric families over the SAME
   carrier `int`/`Z`.  (A) **Squash-sealed, range-enforced**: `GoU8`/`GoI8`/…/`GoU32`/`GoI32`/`GoI64`/`GoU64`
   (tags `TU8`/`TI8`/…/`TI64`/`TU64`) — sound *values*, USED.  (B) **bare-int aliases** (`GoInt8`/`GoUint8`/
   …/`GoUint64` = `int`, tags `TInt8`/…/`TUint64`) — emit the REAL narrow Go types (`int8`/`uint8`/…) but
   carry NO range invariant, and are UNUSED in demos.  THE ROOT (worse than TInt64/TI64): the plugin lowers
   EVERY family-A small-width type to Go **int64** (go.ml ~1069: `GoU64→uint64`, else `int64`), so `TU8`,
   `TI8`, `TI16`, … AND `TI64` ALL emit Go `int64` and ALL collide under `tag_eq` — a family-A value boxed
   as `any` has Go runtime identity `int64`, not its nominal `uint8`.  So break #7 is really *the int64-
   backing of narrow types*, not just the TInt64/TI64 pair.  Reachable-collision census: TInt64(int)≡TI64,
   plus every family-A narrow tag ≡ TI64 (all int64); TUint64(unused)≡TU64.  **Two finds:** (i) the 37
   `TInt64` uses are all RELOOPER/control-flow loop counters — `int`-backed with int arithmetic, merely
   MISLABELLED as Go int64; re-tagging them `TInt` (Go `int`) is mechanical (same `int` backing, identical
   logic), retires `TInt64`, and closes the *cited* collision — but changes the emitted Go (`int64`→`int`
   for counters; runtime output identical, so `expected_output.txt` stable).  (ii) the deeper fix —
   family-A narrow types emitting their REAL Go type (`uint8`…) so their `any`-identity matches Go — is a
   PLUGIN + representation change (give family-A the family-B Go-type names, keep the Squash range proof).
   **DECISION NEEDED (surfaced):** retire-TInt64 only (cheap, closes the cited example, leaves narrow-backing)
   vs. the full narrow-type representation fix (closes it properly, bigger).
   **→ "retire-TInt64" ATTEMPTED & REVERTED (2026-06-21) — it is NOT a cheap re-tag; it is PLUGIN-ENTANGLED.**
   Re-tagged the 37 counters `TInt64`→`TInt` and pointed `Tagged_int := TInt`.  Coq extraction SUCCEEDED but
   the GENERATED GO DID NOT COMPILE: `cannot use iv (variable of type int) as int64 value in argument to Add`.
   Root: the plugin lowers Rocq `int` ARITHMETIC (`PrimInt63.add`, …) to **int64** Go ops (the `Add` helper
   is int64-typed — `int` was *always* int64 via `TInt64`), so re-tagging the VARIABLES to Go `int`
   desyncs variable types from operation types.  CONCLUSION: break #7 cannot be fixed by re-tagging at all —
   the `int`-as-int64 conflation lives in the PLUGIN's numeric lowering, so BOTH sub-fixes (retire-TInt64 AND
   narrow-type representation) require plugin work to lower each numeric type's ops consistently with its Go
   type.  Reverted to HEAD (surgical edits — `git checkout` is boundaried; golden restored, tree clean).  No
   incremental .v-only fix exists; this is a plugin-representation task.  Break is LATENT (no demo
   cross-asserts) so the closed world is sound today.
   **→ SLICE 7a DONE (commit 26ea15e, 2026-06-22, golden BYTE-IDENTICAL, .v-only).** Retired the 7 DEAD
   family-B fixed-width tags (`TInt8`/`TInt16`/`TInt32`/`TUint8`/`TUint16`/`TUint32`/`TUint64`) from the
   `GoTypeTag` inductive + the `tag_eq`/`zero_val`/`key_eqb` arms.  They had no `Tagged` instance and no
   value was ever boxed with them (provably dead — full build re-extracted byte-identical), and
   `TUint64`/`TU64` both→`uint64` was exactly such an unreachable collision.  Kept platform-width
   `TInt`/`TUint` (`cap`/`len` return `GoInt`).  This is the NECESSARY PRECURSOR to the real fix: with the
   family-B fixed-width duplicates gone, the canonical Squash family `TI8`/`TU8`/… can claim their REAL Go
   types (`int8`/`uint8`/…) without re-colliding with a family-B alias.  (Carrier aliases `GoInt8`/… left
   inert — `GoInt32`←`GoRune` dep; harmless, no tag ⇒ unboxable.  Plugin `go_type_tag_map` still lists the
   removed tags — dead, never matched — cleaned during 7b's plugin work.)
   **→ SLICE 7b DONE (commits 082e0b7 + b6af16d, 2026-06-22, golden BYTE-IDENTICAL).**  *Faithful narrow
   interface identity* — but NOT via native narrow types (the obvious "approach B"), which is WRONG for Go:
   `uint8(200)+uint8(100)` is a Go CONSTANT-overflow compile error (Go never wraps constant arithmetic), and
   the int64+mask model exists precisely so narrow arithmetic constant-folds.  So keep int64+mask arithmetic
   UNTOUCHED and convert to the real narrow Go type ONLY at the `any` box, where the value is in range:
   `uint8(((200&0xff)+(100&0xff))&0xff)` = `uint8(44)`.  The crux: an `any x` tag resolves through the
   single-field `Tagged` class and its type index is ERASED in extraction (the `existT` payload is
   `Obj.magic`-wrapped, the tag is `the_tag _` with the type gone) — unrecoverable from the term.  So the
   width is read from the PAYLOAD's head op: a value built by a fixed-width VALUE op (`u8_add`/`u8_lit`/
   `u8_of_i64`/…, NOT the bool predicates `ltb`/`leb`/`eqb`/`gtb`/`geb`/`neqb`) IS that narrow type
   (`fw_value_type` + magic-peeling `payload_head` + `any_narrow_conv`, at both boxing sites).  7b-ii:
   `pp_type` renders each numint as its real Go type (`GoU8`→`uint8`…`GoI32`→`int32`, `GoI64`→`int64`,
   `GoU64`→`uint64`), so the one emitted narrow ANNOTATION (`uc_100_u8 : GoU8` → `var uint8`) boxes faithfully
   — no widening cascade (the narrow OPS emit untyped int64+mask EXPRESSIONS that no annotation types).
   `go_type_tag_map` gains `TU8`→uint8…`TI32`→int32 (so a `type_assert TU8` emits `v.(uint8)`) and drops the
   dead 7a entries.  RESULT: every boxed `GoU8`…`GoI32` value carries its real Go interface identity; 6 of the
   8 int64-cluster tags DE-COLLIDED.  **→ REMAINING:** *(7c)* retire `TInt64` → migrate ALL `int`-boxing to
   `GoI64` (pervasive: `any (n:int)`, `len`/`cap`/`str_len` return `int` tagged `TInt64`) — leaves `TI64` the
   sole `int64` tag, closing the last `{TInt64,TI64}` collision.  *(7d)* THE FORCING THEOREM: a Rocq
   `go_runtime_name {A} (t:GoTypeTag A) : string` mirroring the plugin + `tag_runtime_agrees : tag_eq ta tb =
   None -> go_runtime_name ta <> go_runtime_name tb` — UNPROVABLE while any collision survives, so it is the
   permanent anti-regression lock once 7c lands.
   **→ SLICE 7c DONE (commit 3bc9627, 2026-06-22, golden BYTE-IDENTICAL) — last collision closed.**  The fix
   was the OPPOSITE of "retire TInt64 → migrate to GoI64": render Rocq `int` (PrimInt63) as Go's platform
   `int`, DISTINCT from the Z-carried `GoI64`=int64.  More faithful (loop counters, `len`/`cap`, indices ARE
   Go int) AND it resolves `{TInt64,TI64}` (`v.(int)` ≠ `v.(int64)` now agrees with `tag_eq`).  This is what
   the reverted b5c11ee couldn't do — its blocker was the plugin lowering int ARITHMETIC to int64 ops; fixed
   at the source (`pp_type(uint63)→"int"`, so the `Add`/`Sub` helpers + counter vars retype together).
   Int↔int64 boundaries patched (each surfaced by a make-check Go compile error): `str_len`→`len(s)`, the
   typed int-literal wrapper `int(…)`, the slice/string index bounds-checks `i < len(xs)` (were
   `int64(len(…))`).  Rocq int and `GoI64` never mix in demos ⇒ no conversion sites; `GoI64` (chan int64,
   map[int64], i64 ops) stays int64 (228→188 int64 in main.go).  Making `TInt64`→"int" exposed a latent
   SECOND Go-int tag — `TInt` (`GoTypeTag GoInt`, `GoInt:=int`), no `Tagged` instance, never boxed (`GoInt`
   values box via `Tagged_int`=`TInt64`; `len`/`cap` use the TYPE not the tag) — DEAD, so RETIRED (inductive +
   the 3 fixpoint arms + `go_type_tag_map`).  **Break #7's scalar tag→Go-type map is now INJECTIVE — one tag
   per Go type across 7a (dead bare tags) + 7b (narrows→real types) + 7c (int vs int64); ALL collisions
   closed.**  **→ SLICE 7d DONE (commit 7ab3d5b, 2026-06-22, golden BYTE-IDENTICAL, proof-only) — BREAK #7
   CLOSED.**  `go_runtime_name {A} (t:GoTypeTag A) : option string` mirrors the plugin's `go_type_tag_map`
   for the scalar tags; `tag_runtime_agrees : tag_eq ta tb = None -> go_runtime_name ta = Some sa ->
   go_runtime_name tb = Some sb -> sa <> sb` PROVES the model never distinguishes (`tag_eq`) two tags Go
   cannot (`v.(T)`).  One-line proof (`destruct ta, tb; cbn in *; congruence` over ~441 ctor pairs), zero new
   axioms (the extraction's Print Assumptions base is unchanged — exactly the PrimInt63/PrimFloat primitives).
   It is the permanent machine-checked LOCK: UNPROVABLE if any two named tags ever share a Go name again.
   (Scope: composites reduce to this via recursion; `TUnit`/`TArrow` assert to Go `any` — the documented
   `GoAny` limit.)  **The `GoTypeTag` → runtime-Go-type map is now INJECTIVE — `tag_eq` agrees with Go's
   runtime type identity.**
8. **`WfTrace` accepts malformed sync edges.** A `KStart` only needs its back-pointer to hit SOME
   `KSpawn c`; it never requires the started thread = the spawned child `c`.  So `[t0: KSpawn 1; t99:
   KStart 0]` is well-formed → a forged sync edge that can "prove" a race absent.  `sync` inspects only
   the target event's number, not the source.  Fix: make source-kind/channel/child intrinsic to `sync`.
   **→ RESOLVED (2026-06-22, proof-only, golden byte-identical).**  `WfTrace`'s `KStart parent` clause now
   requires `e_kind e' = KSpawn (e_tid e)` (the spawn's `child` = THIS start's own goroutine id), not
   `KSpawn ch` for some unrelated `ch`.  So a `KStart` can only synchronise with the `go` that spawned
   IT — the forged-edge trace `[KSpawn 1; t99:KStart 0]` is now rejected (`forged_start_rejected`, a
   machine-checked `~ WfTrace`).  No consumer broke (`sync_forward`/`hbt_forward`/`hbt_irrefl` use only the
   `parent < i` conjunct); all producers re-proved unchanged — the operational `rstep` spawn step and the
   abstract traces already emit `mkEv cid (KStart …)` pointing at `mkEv tid (KSpawn cid)`, so child = tid
   holds by construction.  (The `KRecv` back-pointer was already channel-matched, `KSend c`/`KClose c`.)
   Axiom-free (constructive list/nat reasoning); the downstream race-freedom theorems stay closed.
9. **`complex_div` wrong on finite values.** Replaces Go's `abs(re)>=abs(im)` with a SQUARED-magnitude
   compare → overflow/underflow.  Counterexample `1+2i / 1e307+1e308i`: Go ≈ `2.08e-308 - 7.9e-309i`,
   model `0 - 0i`.  The "faithful for all finite" claim is false.
   **→ RESOLVED (2026-06-21, golden byte-identical).**  The branch condition is now `PrimFloat.leb
   (abs mi) (abs mr)` (i.e. `|mi| <= |mr|`) — exactly Go's `|mr| >= |mi|` — instead of `mi² <= mr²`.
   `abs` never overflows, so the right Smith branch is chosen for ALL finite divisors (the squared form
   reduced to `Inf <= Inf = true` for |mi|,|mr| ≳ 1e154, picking the |mr|-branch even when |mi| > |mr|).
   Sound to use `PrimFloat.abs` here even though `math.Abs` needs an import: `complex_div` lowers to the
   NATIVE Go `/` (body proof-only, suppressed by name), so `abs` is never extracted; and it is a trust-base
   `PrimFloat.*` primitive (no new axiom — `Print Assumptions` still PrimInt63/PrimFloat only).  Witness:
   `complex_div_branch_overflow_fixed` machine-checks the old branch was wrong and the new one right at
   mr=2^550, mi=2^600.  (Annex-G Inf/NaN-divisor postamble remains a documented model gap on DEGENERATE
   inputs — the native `/` gets it for free at runtime.)
10. **UTF-8 model is not a decoder.** `str_to_runes` picks width from the first byte and masks the rest
    with no validation (continuation prefixes, overlong, surrogates, >MaxRune, invalid leads).  `0x80
    0x41` → one 2-byte seq → `U+0001`; Go → `U+FFFD` then `A`.  `rune_bytes` emits surrogates/out-of-range
    directly (Go substitutes `U+FFFD`).  Golden tests only exercise VALID input.
    **→ DECODER RESOLVED (2026-06-22, golden byte-identical).**  `str_to_runes` is now a FAITHFUL Go
    `utf8.DecodeRune`: an invalid sequence yields `RuneError` (U+FFFD) and advances exactly ONE byte,
    rejecting cont-as-lead (0x80–0xBF), overlong-2 (0xC0/0xC1), bad/missing continuations, overlong-3/4
    (0xE0 c1<0xA0, 0xF0 c1<0x90), surrogates (0xED c1≥0xA0), >MaxRune (0xF4 c1≥0x90), and leads ≥0xF5
    (full accept-range table, structural recursion = advance-1 on error).  Body is proof-only (lowers by
    name to native `[]rune(s)` which does the same), so the fix only corrects the MODEL; golden unaffected.
    Witnesses: `utf8_cont_as_lead`/`utf8_overlong_2`/`utf8_surrogate`/`utf8_truncated_2` (invalid → U+FFFD)
    + `utf8_valid_2byte` and the existing round-trips (valid still decodes).  PrimInt63 base (helpers inlined
    as local `let`s so the unsigned `ltb`/`leb` stay in the suppressed body, never extracted).
    *(`rune_bytes` ENCODER substituting U+FFFD for surrogates/out-of-range is a smaller remaining model
    gap — the native `string(rs)` does it; tracked.)*

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
handle constructors + every invariant-carrying ctor [**`ComparableW` DONE 2026-06-21** — decidability
evidence field, all 4 instances proved, forge machine-checked-impossible, golden-stable; **`struct_eqb` also
DONE — SProp-erased `pf` param, break #4 fully closed**; `Sess`/handles still open]; (2) `ValidWorld`
invariant (loc 0 reserved, genuine
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

**Named-type tagging — the defined-type/struct map-KEY & channel-VALUE gap (DESIGN, 2026-06-22).**
After the break-#7 arc + the feature/ledger sweep, several remaining ✗ share ONE root: a NAMED type
(a defined type `type Celsius int64`, or a named struct `Point`) has NO `GoTypeTag`, so it cannot be a
map KEY, channel VALUE, or a defined-type-over-struct phantom (each demands a tag).  The obvious fix —
add a `TDef`/`TNamed` constructor — is BLOCKED by a foundational tension verified this session:
`tag_eq_refl` (`tag_eq t t = Some eq_refl`, load-bearing for the typed-heap read-after-write laws)
needs DECIDABLE structural type-equality.  The finite primitive/composite tags satisfy it, but an
open-ended named-type tag carrying `mk`/`proj` FUNCTIONS cannot (functions aren't comparable; the
`R1 = R2` proof isn't derivable, and axiomatising name→type-equality violates zero-axioms).  So
`GoTypeTag` is NOT extensible to named types without breaking its own foundation — a genuine design
constraint.  THREE candidate paths (multi-tick research; no clean single-tick slice):
(a) **ComparableW-keyed maps — RECOMMENDED.**  A map KEY needs only `key_eqb` + a comparability proof,
NOT full `tag_eq`.  `ComparableW K` (the break-#4 SEALED witness, already "distinct from the ambiguous
GoTypeTag") supplies exactly that, and a defined type CAN carry a `ComparableW`.  Refactor the map KEY
requirement from `GoTypeTag K` → `ComparableW K` (the VALUE still needs a tag for zero/storage); derive
`ComparableW` from a `GoTypeTag` for the existing primitive keys so the demo migration is mechanical;
the plugin renders the Go key type from the Coq key type via `pp_type` (`Celsius`→its defined-type
name).  Sidesteps the `tag_eq` tension; the 7d forcing theorem is UNAFFECTED (no new `GoTypeTag` ctor).
Also unblocks struct map KEYS by the same mechanism.  (b) **Restrict + fail-loud:** keep named types
un-taggable; a named-type map key / channel value aborts (`unsupported`) — honest, but a real gap.
(c) **`TDef` with a decidable name:** REJECTED — `tag_eq (TDef …) (TDef …) = Some eq_refl` for self is
unprovable without comparing carried functions or an axiom.  NEXT (impl, fresh tick): prototype (a),
starting with `ComparableW`-from-`GoTypeTag` derivation so primitive map keys are untouched, then a
defined-type map-key demo.
**OBSTACLE found (2026-06-22, experiment): the deftype `GoTypeTag` phantom BLOCKS axiom-free
comparability.**  A defined type is a 2-field record `{ c_val : <under> ; c_tag : GoTypeTag <under> }`
(the phantom KEPT so Coq doesn't unbox the single value field → distinct method-receiver).  To compare
two such records you must prove their `c_tag` fields equal — i.e. `forall (t : GoTypeTag GoI64), t = TI64`
— which is NOT provable axiom-free: `GoTypeTag` is indexed by `Type`, and a `Type`-indexed family's
eliminator cannot discriminate the index (`GoI64` vs `bool` vs `GoChan A` …) to prune the impossible
constructors (`destruct t` errors "Abstracting over … cannot be applied"; the motive can't case on
`Type`).  So `ComparableW Celsius` is NOT axiom-free with the current rep — the `tag_eq`-foundation
tension reappears one level down.  **REVISED path:** rework the deftype phantom from `GoTypeTag <under>`
to a phantom that is (i) KEPT/computational (still blocks unboxing), (ii) axiom-free-comparable, and (iii)
recognised+dropped by the plugin so extraction stays `type Name <under>`.  A `unit` second field fits
(i)+(ii) (a 2-field record isn't unboxed; `tt = tt` is trivial), but needs a PLUGIN change to the deftype
detection (currently keyed off the `GoTypeTag` phantom: `defined_prim_under`/`defined_prim_proj`) so a
`unit`-phantom deftype still emits `type Name <under>` + the ctor/proj casts.  That phantom-rework is the
real first implementation slice — a focused plugin + deftype-demo-migration effort, fresh context.
**PHANTOM-REWORK DONE (2026-06-22, commits 6ac4bb4 + bf063ce): defined-type COMPARABILITY shipped.**
Celsius's phantom is now `unit` (golden byte-identical; `comparable_celsius` axiom-free; `cw_celsius` the
sealed `ComparableW`; `ceqb` over Celsius → native `Celsius == Celsius`, in `comparable_demo`).  So a
defined type is a first-class COMPARABLE.  **But the MAP KEY itself hits a DEEPER gate (found 2026-06-22):
the map HEAP is HETEROGENEOUS** — `w_maps : int -> option MapCell`, one heap shared by ALL maps, and
`map_get_fn` recovers each cell's key/value type via `tag_eq kt kt'` + `eq_rect`.  A tagless defined-type
key has NO tag to store/recover, and `ComparableW` gives `key_eqb` but NOT the type-equality proof
`eq_rect` needs.  So `ComparableW`-keyed maps can't ride the shared heterogeneous heap; they need either
(x) a SEPARATE homogeneous map store (a [GoMap K V] whose cell is just `K -> option V` + the live count,
no tag — the K type is fixed per map, so no recovery needed; a parallel `map_make_cmp`/`map_set_cmp`/… set
that lowers to the SAME native Go `map[K]V`), or (y) a tag for named types (blocked, see above).  Path (x)
also entangles: Go maps are REFERENCE types, so a faithful map lives in the `World` heap — but the `World`
has ONE `w_maps` field (the heterogeneous, tag-recovered heap); a homogeneous ComparableW map would need
its OWN `World` heap field (a pervasive `mkWorld` cascade) or it sacrifices reference-type faithfulness.
**Honest conclusion:** a SHARED map heap across maps of different K REQUIRES per-cell type tags for
recovery, so tagless keys are fundamentally blocked short of either a tag for named types (breaks
`tag_eq_refl`) or a `World`-heap redesign — a depth DISPROPORTIONATE to this niche feature.  The achievable
part (defined-type COMPARABILITY) is shipped; defined-type MAP KEYS are deferred as a known, scoped
foundation limit (the `ComparableW` machinery is ready the day the heap is reworked).  **PIVOT** the loop
to other Go-spec corners rather than the `World`-heap redesign.

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
   **DYNAMIC-SPAWN TRANSFER, trace core (2026-06-22):** `dst_trace` / `dst_trace_wf` / `dst_trace_race_free`
   — `mp_trace`'s static handoff has both goroutines pre-live; here the reader is SPAWNED by the writer and
   the location is handed to that freshly-created child (the genuinely harder dynamic-tid shape). g0 writes
   x, SPAWNS child `cid`, sends c0; the child STARTS (its `KStart` back-points at the spawn — the
   child-identity edge `WfTrace` demands), recvs c0, reads x. The conflicting write/read pair is ordered by
   the handoff carried ACROSS the spawn boundary (write →po→ send →sync→ recv →po→ read), so the trace is
   well-formed AND race-free for ANY fresh child tid — axiom-free ("Closed under the global context"),
   proof-only ⇒ golden-stable. The all-interleavings invariant over the spawning PROGRAM (a `MpReach`-style
   reachability with the child tid existentially quantified) is the follow-on slice.
   **GENERATED BY A REAL EXECUTION (2026-06-22):** `dst_exec_trace`/`dst_exec_race_free`/`dst_exec_state`
   (concurrency.v after `mp_exec_state`) — `dst_trace` is no longer hand-written: a program combining
   dynamic spawn with channel handoff (g0 writes loc 0, SPAWNS the child — `rstep_spawn` allocates fresh
   tid 1 since only g0 starts live — then SENDS chan 0; the child RECVS then READS loc 0) EXECUTES its
   canonical interleaving to EXACTLY `dst_trace 1`, so its race-freedom is now about a reachable state of an
   actual spawn+channel program. `dst_exec_state`: g0's written `v0` survives the spawn AND the channel
   handoff (the value the child read) and the channel drains. All three axiom-free, golden-stable. This
   mirrors how `mp`/`fork` each progressed trace-core → exec → all-interleavings; the `DSTReach`
   all-interleavings invariant is the remaining brick for this third composition.

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
   COMPLETE (`diamond_reloops` instantiates it).

   **LOOPS FULLY LANDED (2026-06-22, `relooper.v`, proof-only, all axiom-free —
   `Print Assumptions` = "Closed under the global context").**  The control-flow
   semantics-preservation now covers EVERY structured loop pattern, not just the
   `while_realized` core: (a) GENERAL single-loop soundness — the loop-aware function
   `reloop_loop` is correct on ANY single-loop CFG (`reloop_loop_sound`), built from a
   fuel-indexed `cfg_halts_n`, a per-iteration `runs_term`, and `loop_body_iterates`;
   (b) SEQUENTIAL loops — `reloop_chain`/`reloop_chain_sound` (a chain of loops + an
   acyclic tail, e.g. `for{};for{};rest`); (c) NESTED loops to ANY DEPTH — the
   reusable calculus `inner_split`/`inner_split_cfg_n` (decompose an outer iteration
   that passes through an inner loop) + `inner_join` (the converse splice) + the
   proper-nesting predicate `InnerClosed` + `loop_to_exit`/`loop_to_exit_c` (lower an
   inner loop to an `LLoop`) + the realiser abstraction `Iterates`/`IteratesC`
   (realise-under-the-run, so a nested body qualifies) + `loop_sound_c`, assembled into
   `nested_iterates_gen` (the RECURSIVE depth-N builder: an inner loop that is itself an
   `IteratesC` composes to any depth) and the single general statement
   `nested_loop_sound_gen`; (d) their COMBINATION — `ChainSound`/`chain_c_sound`: a
   sequence of arbitrarily-nested loops (a whole function body `for{};for{for{}};tail`).
   Concrete end-to-end witnesses: `nested_loop_sound` (depth-2), `tri_nested_sound`
   (depth-3, by composing `nested_iterates_gen` with itself), `seq_nested_sound`
   (sequential+nested).  `reloop_chain_chainsound` bridges the `reloop_chain` FUNCTION
   to the `ChainSound` relation (the template the general reducible-CFG function will
   follow).  Still open: the FUNCTION that AUTO-DETECTS the loop nest from a raw
   reducible CFG (dominator / loop-nest analysis — a large effort), and connecting to
   the emitted Go AST.

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
   are captured.  Axiom-free.  This `cstep` is the self-contained channel-fragment pilot; the FULL-calculus
   integration is now DONE — `rstepC cap` (the whole `rstep` parameterised by a capacity, threaded as a
   `nat -> nat` argument rather than an `rc_cap` field, so NO `mkRCfg`-site cascade) carries the same
   `length < cap` send guard + cap-0 `rstepC_sync` rendezvous, and on it: SAFETY transfers for free
   (`rstepsC_embed`), capacity is a proven reachability invariant of the full state (`BoundedC` /
   `reachableC_bounded`), the deadlock characterization is the single IFF `rstuckC_iff_blocked` over ALL
   bounded programs, and the world-refinement is capacity-aware (`reachableC_refines_bounded`).

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
