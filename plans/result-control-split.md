# Result / control split — design (checkpoint-60 finding 1)

**Problem.** `GoEffects.Outcome A = ORet A World | OPanic GoAny World`, and `catch` handles EVERY `OPanic`.
Blocking (`rt_chan_send_block` / `rt_chan_recv_block` / `rt_select_block`) and the model-invalid forged-handle
fault (`rt_forged_map`) are encoded as `OPanic` payloads — so `catch (would-block-send) h` runs `h`, a blocked
op is "recovered", and any defer/recover layer unwinds on a block or model fault. Wrong Go semantics: a block is
not a panic; a model fault is not a Go panic; neither invokes recover or runs defers.

**Golden-safety.** `Outcome`/`ORet`/`OPanic` are model-only — absent from extracted `*.go` (verified: `main.go`
has 0). The plugin lowers channel ops / `catch` to native Go (native block / native `recover`); the model-only
outcome branches are suppressed. So changing the `Outcome` algebra does NOT change golden output. This makes the
type change safe to make — only the `.v` proof side moves.

## Phase 1 — separate the result algebra (this is the first landable slice)

Add two constructors, keep `GoAny` payloads (reuse the existing `rt_*` values — smallest cascade, no
GoPanic.v / plugin-suppression-list churn; the CONSTRUCTOR, not the payload type, is the domain boundary):

```
Inductive Outcome (A : Type) : Type :=
  | ORet   : A -> World -> Outcome A       (* normal return *)
  | OPanic : GoAny -> World -> Outcome A    (* genuine Go panic — catch/recover handles ONLY this *)
  | OBlock : GoAny -> World -> Outcome A    (* would-block / suspended — a DERIVED polling result, NOT catchable *)
  | OFault : GoAny -> World -> Outcome A.    (* model-invalid state — NOT catchable; unreachable for well-typed *)
```

- `outcome_world` (GoEffects): add `| OBlock _ w => w | OFault _ w => w`.
- `bind`: `OBlock`/`OFault` short-circuit like `OPanic` (propagate) — a block/fault stops the continuation.
- `catch`: handles ONLY `OPanic`; `OBlock`/`OFault` PASS THROUGH unchanged (never run the handler).
  `fun w => match m w with ORet a w' => ORet a w' | OPanic v w' => h v w' | OBlock v w' => OBlock v w'
            | OFault v w' => OFault v w' end`.
- `run_bind` / `run_catch` lemma STATEMENTS: add the two arms to their RHS matches (passthrough); proofs stay
  `reflexivity`.

**Producer migration:**
- GoChan.v: `send` / `recv` / `select_recv2` / `select_wait2` block branches: `OPanic rt_chan_send_block` →
  `OBlock rt_chan_send_block`, likewise `rt_chan_recv_block`, `rt_select_block`. And EVERY lemma stating
  `= OPanic rt_chan_*_block w` → `= OBlock rt_chan_*_block w` (~15 sites).
- GoMap.v: forged branches `OPanic rt_forged_map` → `OFault rt_forged_map` (map_set/delete/clear + the
  `exists p, run_io = OPanic p w` anti-forgery theorems → `exists p, run_io = OFault p w`). ~9 sites.
- GoPanic.v: `rt_chan_*_block` / `rt_forged_map` stay defined (still the GoAny diagnostic payloads), but their
  doc comments change: they are BLOCK / FAULT reasons, no longer panic payloads.

**Exhaustive-match cascade (add `OBlock`/`OFault` arms — ~44 matches):** GoEffects 7, cmd.v 6, cmd_unified.v 8,
GoChan 5, GoMap 3, GoHeap 15. GoHeap/heap ops never block/fault → their arms are dead passthroughs
(`| OBlock v w' => OBlock v w' | OFault v w' => OFault v w'`) needed only to keep the match total. cmd.v
`run_cmd` / `oc_set_world` / `oc_unit`: block/fault short-circuit like panic (a Cmd that reaches a shallow-IO
block/fault stops — the Cmd layer's own would-block is `run_cmd = None`, a separate stuck notion).

**Acceptance theorems to ADD (gated):**
- `catch_does_not_handle_blocked` : `run_io (catch (send tag (MkChan 0) v) h) w = OBlock rt_chan_send_block w`
  (catch passes the block through — h is NOT run). Replaces the review's "red test" (which currently would show
  `= run_io (h rt_chan_send_block) w`).
- `catch_does_not_handle_model_fault` : the analogous fact for a forged-map op → `OFault …`.
- `defer_not_unwound_by_block` (cmd.v): a `run_cmd` reaching a block does not run the defer stack.

## Phase 2 — blocking becomes RELATIONAL (the review's real requirement)

A terminal `OBlock` is only the DERIVED polling layer (review arch C): it loses the continuation, so it cannot
model resumption. The authoritative concurrent semantics is the scheduler relation. Move channel send/recv/select
BLOCKING into `concurrency.v`'s small-step relation (`rstep`) where a blocked action has NO transition until a
complementary action is ready and its continuation stays in the scheduler configuration (retained / resumable).
Acceptance: `blocked_action_retains_continuation`, deadlock classified as deadlock/nontermination not panic. The
shallow-IO `send`/`recv` keep `OBlock` only as the ready/would-block POLLING view, explicitly non-authoritative.

## Phase 3 — model faults provably unreachable

`OFault` is diagnostic (open-world). Under `WorldRealizes` / `ValueWF` (checkpoint-60 finding 3, StoreTyping),
prove `well_typed_config_never_model_faults`: a well-typed configuration never yields `OFault`. `catch` cannot
observe `OFault` (Phase 1 already), and the well-typed path never produces it.

## Sequencing note

Phase 1 is all-or-nothing to COMPILE (adding constructors breaks every exhaustive match at once), so it lands in
one focused pass, not incrementally. Phases 2–3 depend on the concurrency relation and StoreTyping respectively.
