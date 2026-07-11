# Result / control split + runtime-panic-value redesign — FINAL architecture (checkpoint-61)

STATUS: DESIGN ONLY — no code landed for this arc. The earlier "terminal OBlock" implementation
(9a79f61) was REVERTED per checkpoint-61: a terminal `OBlock`/`OFault` in `World -> Outcome` stops
`catch` from catching a block but DISCARDS the blocked computation's continuation, so it still cannot
model Go blocking or resumption — a transition artifact. This doc records the FINAL architecture to
build directly (the law: design the final control semantics first, implement that).

## The defect being fixed

`GoEffects.Outcome A = ORet A World | OPanic GoAny World`, and `catch` (Go's defer/recover) handles
EVERY `OPanic`. But three distinct things are currently all `OPanic`:
- genuine Go panics (nil deref, div-zero, bounds, closed-chan send/close, failed assert);
- would-block send/recv/select (`rt_chan_*_block`, `rt_select_block`);
- forged-handle model faults (`rt_forged_map`).
So a blocked op or a model-invalid state can be "recovered" as if it were a Go panic. Also, runtime
panic payloads are `anyt TString "..."`, but real `recover()` returns runtime OBJECTS with dynamic
types (verified on Go 1.23.2: `runtime.boundsError`, `runtime.errorString`, `runtime.plainError`,
`*runtime.TypeAssertionError`) — never a Go string. Both must be fixed together.

## Three domains (the split)

1. **AtomicIO** — nonblocking, immediately-completing effects only.
   `PanicValue := UserPanic GoAny | RuntimePanic RuntimeError`;
   `AtomicCompletion A := Returned A | Panicked PanicValue`;
   `AtomicResult A := { completion : AtomicCompletion A ; world : World }`;
   `AtomicIO A := World -> AtomicResult A`.
   No `Blocked`, no `ModelFault` in this genuine-completion domain. `bind` composes only
   returns/panics; `catch`/recover observes ONLY `Panicked` (a genuine `PanicValue`). Blocking
   operations are NOT `AtomicIO` actions.

2. **GoConcurrentSem** — the relational scheduler / configuration authority (seed: `unified.v`).
   Blocking send/recv/select are SCHEDULER COMMANDS: `UCmd` carries the continuation (`USend c v k`
   / `URecv c zero f` / `USelect cases`). A blocked goroutine STAYS in the `UConfig` holding its
   un-stepped `UCmd` (continuation retained); `ustep` advances a goroutine only when its action is
   ready; `ublocked` classifies a config where no goroutine can step. Supports readiness / suspension
   / RESUMPTION / synchronization / closed-chan / select-choice / scheduler steps / deadlock /
   divergence / termination / genuine unwind.

3. **Open-world diagnostics** — `ModelFault` (`FaultReason`), NOT a Go event. A malformed raw
   world/handle is outside certified closed-world execution. Theorem: `WorldRealizes Σ w -> ValueWF
   Σ v -> ...` certified evaluation never produces `ModelFault`. `catch` cannot observe it. A derived
   executable probe may surface `PollFault`, but it is not authoritative.

## Explicit decisions (checkpoint-61 order #1)

- **What stays AtomicIO**: heap ref/ptr/slice-index/struct-field read·write·alloc; output; pure
  numeric/string/compare; map get·set·delete·len; slice ops; type-assert (comma-ok); `close` (never
  blocks — closed/nil close is a genuine `Panicked RuntimePanic`); `make`.
- **Which ops are scheduler commands**: send, recv, comma-ok recv, select, spawn (`go`). A send/recv
  is authoritatively a `UCmd`; the shallow layer never blocks. A DERIVED nonblocking probe
  (`try_send`/`try_recv : AtomicIO (PollResult …)`, `PollResult A := Ready A World | WouldBlock
  BlockReason | PollPanic PanicValue World`) is theorem-related to a single `ustep`, but is NOT the
  authoritative semantics and never discards a continuation in the scheduler.
- **How a blocked goroutine retains continuation**: the `UCmd`'s `k`/`f`/`cases` IS the continuation;
  the blocked goroutine's config entry holds the un-stepped `UCmd`; `ustep` applies the continuation
  only once the complementary action fires.
- **Readiness**: send ready iff buffer has room OR a receiver waits; recv ready iff buffer nonempty
  OR closed OR a sender waits; select ready iff any case ready OR a `default` exists.
- **Deadlock vs temporary block**: temporary block = config where SOME goroutine is ready; deadlock =
  reachable config that is `ublocked` and not all-`URet`; divergence = an infinite `ustep` chain
  (coinductive); termination = an all-`URet` config. These are configuration-level, not atomic
  outcomes.
- **Panic-unwind vs goroutine control**: a `Panicked` unwinds the CURRENT goroutine's defer stack
  (per-goroutine); an unrecovered panic is a terminal program state. Blocking is orthogonal (a
  blocked goroutine cannot panic until it resumes; a deadlocked goroutine never panics).
- **ModelFault excluded from certified configs**: preservation (`ustep` preserves `WorldRealizes` +
  well-typedness) + progress (a well-formed config steps, is all-done, or is a genuine deadlock —
  never faults).
- **cmd restriction/translation**: `cmd.run_cmd`'s `option (Outcome A)` conflates absent-cell /
  tag-mismatch / blocked / no-run. Decision: TRANSLATE the channel constructors
  (`CChSend`/`CChRecv`/`CChClose`) into `UCmd` scheduler commands; keep the nonblocking Cmd fragment
  (heap/output/panic/defer) over `AtomicIO`. Under `WorldRealizes` the "absent cell" `None` is
  unreachable, so the nonblocking fragment's interpreter is total (no ambiguous `None`).
- **GoCFG restriction**: `CBlock` bodies use `AtomicIO` only — nonblocking control flow, so
  `blocks_eval` stays return/panic/jump (no block/fault case). Blocking control lives in
  `GoConcurrentSem`. Boundary: GoCFG = nonblocking control-flow authority; GoConcurrentSem =
  suspension/synchronization/scheduler.

## Runtime-panic-value redesign (checkpoint-61 order #2 — designed WITH the split)

`RuntimeError` inductive keyed to the verified Go 1.23.2 recover values:
`RENilDeref | REDivZero | RENegativeShift (count:Z) | REIndexBounds (i:Z)(n:nat) | RESliceBounds (…) |
REMakeSliceLen (n:Z) | REMakeSliceCap (len cap:Z) | REMakeChanSize (n:Z) | RENilMapAssign |
RESendClosed | RECloseClosed | RECloseNil | RETypeAssertion (src tgt:…) | …` (note: makeslice `len`
and `cap` are DISTINCT errors). `PanicValue := UserPanic GoAny | RuntimePanic RuntimeError`. Provide:
a recover dynamic-type model, an `Error()`-text renderer under the pinned toolchain (theorems for
exact text where claimed), OR an opaque runtime-error value if the certified subset forbids inspecting
recovered runtime errors (then enforce that restriction in `GoCompile`). Delete the `anyt TString`
payloads. Start with structured `RuntimeError` + `Error()` renderer + opaque-to-type-switch; add
dynamic-type-switch support only if the supported subset needs it.

## Acceptance theorems (the goals — gated, zero-axiom)

Control: `catch_handles_only_genuine_panic`, `blocked_{send,recv,select}_not_recoverable`,
`model_fault_not_recoverable`, `block_does_not_unwind_defer`,
`blocked_goroutine_retains_continuation`, `complementary_action_resumes_blocked_goroutine`,
`deadlock_classification_sound`, `well_typed_config_never_faults`.
Panic values: `runtime_panic_not_string`, `runtime_panic_error_text_correct` (per admitted error),
`recover_user_panic_preserves_dynamic_value`, `recover_runtime_panic_preserves_runtime_error_class`.

## Implementation order (checkpoint-61)

1. This doc (final relational design) — DONE. 2. Land `AtomicIO` + the `RuntimeError`/`PanicValue`
authority (together). 3. Build `GoConcurrentSem` blocking on the `unified.v` `ustep` seed
(continuation-retaining). 4. `SliceWF` over a backing object; slice ops consume/preserve it;
malformed → `ModelFault`. **PARTIAL (8b8798a):** the `sh_len <= sh_cap` header guard now fail-louds at
`slice_idx_get`/`slice_idx_set` BEFORE any cell access — `slice_idx_{get,set}_bad_shape_rejected` (gated in
`heap_aggregate_liveness_surface`, `exists p, = OPanic p w`, no exported marker) pin that a `cap < len` shape
is rejected. This closes ONLY the nat-shape malformation (an in-`len`-beyond-`cap` index can no longer reach a
spare/foreign cell); a WELL-shaped (`len <= cap`) header over a same-tag aliasing backing is UNCHANGED — the
standing checkpoint-59 typed-liveness frontier. STILL AHEAD — `SliceWF` over the backing OBJECT IDENTITY (not
just the `nat` shape), consume/preserve across subslice/append/clear/copy, and routing the fault to a distinct
`ModelFault` (it is `OPanic rt_nil_deref` today). 5. `StoreTyping`/`WorldRealizes`/`ValueWF` (Live* derived; alloc-extension;
preservation; `ModelFault` unreachable). 6. `AllocFrontierOk` (the frontier-only predicate) — DONE 7a67aeb;
the full `WorldWellFormed` (needs `WorldRealizes`) lands with #5. 7. Restrict
GoCFG to nonblocking bodies. 8. Translate Cmd channels → UCmd. 9. Finite vs unbounded channels.
10. Map representation. 11. Clean docs + full build.
