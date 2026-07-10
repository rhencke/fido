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

## Ripple analysis (from a PARTIAL spike — reverted, NOT compile-confirmed)

A spike added `OBlock`/`OFault` and worked through GoEffects + the producers, then was REVERTED at the GoCFG wall
BEFORE any green build — so the observations below are indications from a partial spike, not verified facts.
Confirm each at build time.

INDICATED mechanical (edited, but the spike never reached a compiling state to prove it): the GoEffects core
(`outcome_world` / `bind` / `catch` / `run_bind` / `run_catch` / `hoare` + the `bind_Proper` / `catch_Proper`
congruence destructs + `bind_ret_r` / `bind_assoc` / `hoare_bind` / `hoare_consequence` / `hoare_no_panic`
destructs) extends by adding arms: block/fault short-circuit like panic in `bind`, pass through `catch`, map to
`False` in `hoare` (a valid triple guarantees RETURN — no panic/block/fault). GoChan/GoMap producers migrate by a
targeted `OPanic rt_*` → `OBlock`/`OFault` replace; GoChan's `ORet` sites are LIST matches (checked by grep), so
NO Outcome-match break there — GoMap NOT separately checked, verify at build. (These files compile BEFORE GoCFG
in the DAG, so a green GoCFG would imply they passed, but the spike never got there.)

The REAL work is the outcome-CLASSIFICATION layers, where a naive 4th/5th arm is WRONG:
- **GoCFG.v `blocks_jump_wf_progress`** classifies `run_io b w` into done (`ORet None`) / jump (`ORet (Some pc')`) /
  panic (`OPanic`) and concludes "never stuck". SETTLED (read `GoCFG.v`): `blocks_jump_wf : list (IO Next) -> Prop`
  quantifies over ARBITRARY IO blocks, and `cblock_denote (CBSeq body t) = bind body (fun _ => ret t)` with `body`
  an arbitrary `IO` — so a block's `body` CAN be a channel op that BLOCKS (or a forged-map op that faults). The
  block class is NOT channel/map-free, so a freedom lemma is NOT available. The progress theorem must therefore
  EITHER (a) admit a blocked/faulted classification — "concludes OR steps OR **blocks** OR **faults**" (the
  faithful reading: a program that blocks at a straight-line block genuinely blocks), OR (b) add a
  block/fault-FREE well-formedness premise to `blocks_jump_wf` (restricting the certified CFG-block class to
  non-blocking bodies, deferring channel blocking to the Phase-2 scheduler). Pick (b) if the CFG layer should stay
  pure control-flow with concurrency at the scheduler; pick (a) to let the CFG progress theorem itself report
  blocking. Decide at execution; same for `blocks_step` / `cblock_denote_*` (GoCFG lines ~100/196/267/318).
- **cmd.v `run_cmd` / bridge**: the deep-embedded Cmd interpreter already has its OWN would-block notion
  (`run_cmd = None` for the deterministic-fragment stuck cases); decide how a shallow-IO `OBlock`/`OFault` from a
  `CChSend`/`CChRecv`/`CWrite` maps into `run_cmd` (short-circuit like panic, or the Cmd's `None`). cmd_unified.v
  and GoHeap.v exhaustive matches: heap ref/ptr/slice/struct ops fail with `rt_nil_deref` (an `OPanic`), have no
  channel/forged-map path, so they are EXPECTED to never yield `OBlock`/`OFault` (verify per op) — their dead
  arms are passthroughs, plus a freedom fact where a classification theorem can't otherwise discharge them.

So Phase 1 = GoEffects mechanical core + producer replace + resolving each classification layer's outcome
handling — a FREEDOM lemma where the layer is provably block/fault-free (heap ref/ptr/slice/struct — expected,
verify per op), ELSE a blocked/faulted classification or a wf-premise restriction where it is not. GoCFG is the
latter: its blocks are arbitrary IO (settled above), so it needs choice (a) blocked classification OR (b) a
block/fault-free wf premise on `blocks_jump_wf` — decide when executing. Budget it as a focused
multi-hour pass, not a loop-tick grind; land only when `make check` is green and the manifest is empty.
