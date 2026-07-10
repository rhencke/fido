# Result / control split — design (checkpoint-60 finding 1)

## Problem (verified by reading `GoEffects.v`)

`Outcome A = ORet A World | OPanic GoAny World`, and `catch` handles EVERY `OPanic`. Blocking
(`rt_chan_send_block` / `rt_chan_recv_block` / `rt_select_block`) and the forged-handle fault (`rt_forged_map`)
are `OPanic` payloads — so `catch` on a would-block send runs the handler, a blocked op is "recovered", and any
defer/recover layer unwinds on a block or fault. Wrong Go semantics: a block / model fault is not a Go panic;
neither invokes recover nor runs defers.

## Approach

Separate the concepts at the TYPE level — the review: "the problem is the result algebra; do not add another
payload." Add `OBlock` and `OFault` constructors to `Outcome`; `catch` handles ONLY `OPanic` (`OBlock`/`OFault`
pass through); `bind` propagates every non-`ORet`; the channel block branches produce `OBlock`, the forged-map
branch produces `OFault`. This is Phase 1 — a terminal `OBlock` is only the DERIVED polling view. Phase 2 moves
blocking into the relational concurrency semantics so continuations resume; Phase 3 proves `OFault` unreachable
under the StoreTyping authority (finding 3). Phases 2–3 are not yet designed here.

## Acceptance criteria (from the review)

- A blocked channel op cannot be caught by recover/catch; blocking does not trigger defer unwinding.
- Model faults are not Go panics; catch cannot observe them.
- Blocked goroutines retain continuations and can resume (Phase 2, relational).
- `rt_chan_*_block` / `rt_forged_map` are no longer panic payloads in the authoritative semantics.

## Known vs open — do NOT act on the "open" items as if settled

VERIFIED (read the code):
- `Outcome`/`ORet`/`OPanic` are absent from the extracted Go (`grep -l 'Outcome\|ORet\|OPanic' *.go` → nothing).
  So the change is EXPECTED golden-safe (the plugin lowers ops/`catch` by name; `Outcome` is not extracted) —
  CONFIRM with `make check`, do not assume.
- Adding constructors breaks EVERY exhaustive `match … ORet | OPanic` at once (all-or-nothing to compile), so
  Phase 1 lands in one pass. Affected files (each imports `Outcome` via `GoEffects`): GoEffects, cmd.v,
  cmd_unified.v, GoChan, GoMap, GoHeap, GoCFG (import checked). Site counts are not yet pinned — grep per file.
- GoCFG `blocks_jump_wf : list (IO Next)` quantifies over ARBITRARY IO blocks (`cblock_denote (CBSeq body t) =
  bind body (fun _ => ret t)`, `body` an arbitrary `IO`), so a CFG block CAN block/fault. No freedom lemma is
  available: `blocks_jump_wf_progress` ("never stuck") must EITHER admit a blocked/faulted classification, OR add
  a block/fault-free well-formedness premise to `blocks_jump_wf`. Decide which at execution.

OPEN — verify at execution, do NOT assume:
- Whether heap ref/ptr/slice/struct ops can yield `OBlock`/`OFault`. They fail with `rt_nil_deref` (`OPanic`) and
  have no channel/forged-map path, so PLAUSIBLY not — but this is unchecked; confirm per op.
- Whether `plugin/go.ml` is affected by the constructor change and whether keeping the existing `GoAny` `rt_*`
  payloads (vs a distinct reason type) avoids extractor churn. It lowers by name and does not extract `Outcome`,
  so PLAUSIBLY unaffected — unchecked; confirm against `go.ml`'s suppression logic + `make check`.
- How `cmd.v run_cmd` (which already has its own `= None` would-block for the deterministic fragment) should map
  a shallow-IO `OBlock`/`OFault`.
- The Phase-2 relational design (concurrency.v's step relation) — not yet studied.

## Acceptance theorems to add (Phase 1, gated)

- `catch_does_not_handle_blocked`: `catch` on a would-block send passes the block through, NOT to the handler.
- `catch_does_not_handle_model_fault`: the analogue for a forged-map op.
- `defer_not_unwound_by_block` (cmd.v): a `run_cmd` reaching a block does not run the defer stack.

Execute Phase 1 in one focused pass; commit ONLY when `make check` is green and the manifest is empty.
