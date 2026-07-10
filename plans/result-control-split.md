# Result / control split — design (checkpoint-60 finding 1)

**Problem.** `GoEffects.Outcome A = ORet A World | OPanic GoAny World`, and `catch` handles EVERY `OPanic`.
Blocking (`rt_chan_send_block` / `rt_chan_recv_block` / `rt_select_block`) and the model-invalid forged-handle
fault (`rt_forged_map`) are encoded as `OPanic` payloads — so `catch (would-block-send) h` runs `h`, a blocked
op is "recovered", and any defer/recover layer unwinds on a block or model fault. Wrong Go semantics: a block is
not a panic; a model fault is not a Go panic; neither invokes recover or runs defers.

**Golden-safety (expected, confirm with `make check`).** `Outcome`/`ORet`/`OPanic` are model-only — absent from
the extracted Go (VERIFIED: `grep -l Outcome\|ORet\|OPanic *.go` matches nothing, 0 across all `*.go`). The plugin
lowers channel ops / `catch` to native Go by NAME (native block / native `recover`), suppressing the op bodies —
so a body's `OPanic`→`OBlock`/`OFault` change is not seen by the extractor. This SHOULD leave golden output
unchanged (only the `.v` proof side moves), but the spike never reached a `make check`, so treat it as expected,
not proven.

## Phase 1 — separate the result algebra (the first slice)

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

## Ripple analysis

The lines below are split into VERIFIED (a fact I confirmed by reading the code) and UNVERIFIED (edits made in a
spike that was reverted before ANY green build, or expectations not yet checked). Nothing about what compiles is
verified — the spike never reached a green build.

VERIFIED (read `GoCFG.v`): `blocks_jump_wf : list (IO Next) -> Prop` quantifies over ARBITRARY IO blocks, and
`cblock_denote (CBSeq body t) = bind body (fun _ => ret t)` with `body` an arbitrary `IO`. So a CFG block CAN
block or fault — its `body` can be a channel op (would-block) or a forged-map op (fault). No block/fault-freedom
holds for the block class. VERIFIED (read `GoEffects.v`): the CFG layer, cmd.v, and cmd_unified.v import `Outcome`
via `GoEffects`; GoCFG imports only `GoRuntimeTypes` + `GoEffects` (NOT GoChan/GoMap) — so a GoChan/GoMap error and
a GoCFG error are independent; neither implies the other compiles.

UNVERIFIED — spike edits, compilation NOT confirmed (reverted at the first GoCFG error):
- GoEffects: added the two constructors and extended `outcome_world`/`bind`/`catch`/`run_bind`/`run_catch`/`hoare`
  + the `bind_Proper`/`catch_Proper`/`bind_ret_r`/`bind_assoc`/`hoare_bind`/`hoare_consequence`/`hoare_no_panic`
  destructs to four cases. Intended semantics (design, unproven): block/fault short-circuit like panic in `bind`,
  pass through `catch`, map to `False` in `hoare`.
- GoChan/GoMap: producer `OPanic rt_*` → `OBlock`/`OFault` replace. GoChan's producer `ORet` sites are LIST
  matches (grep), not `Outcome` matches; whether GoChan/GoMap have OTHER Outcome matches/destructs in proofs that
  break is UNCHECKED.

Consequences to DECIDE at execution:
- **GoCFG.v `blocks_jump_wf_progress`** ("never stuck": done `ORet None` / jump `ORet (Some pc')` / panic `OPanic`).
  Since blocks CAN block/fault (VERIFIED), a freedom lemma is NOT available. The theorem must EITHER (a) admit a
  blocked/faulted classification ("concludes OR steps OR blocks OR faults" — the faithful reading), OR (b) add a
  block/fault-free well-formedness premise to `blocks_jump_wf` (restricting the certified block class to
  non-blocking bodies, deferring channel blocking to the Phase-2 scheduler). Same for `blocks_step` /
  `cblock_denote_*` (GoCFG ~100/196/267/318).
- **cmd.v `run_cmd` / bridge** and **cmd_unified.v / GoHeap.v matches** — NOT reached by the spike, UNEXPLORED.
  `run_cmd` already has a `= None` would-block for the deterministic fragment; decide how a shallow-IO
  `OBlock`/`OFault` maps in. Heap ref/ptr/slice/struct ops fail with `rt_nil_deref` (`OPanic`) and have no
  channel/forged-map path, so they are PLAUSIBLY block/fault-free — an expectation to verify per op, not a fact;
  whether dead passthrough arms suffice or a freedom fact is needed is unexamined.

So Phase 1 = the GoEffects arm additions + producer replace (both compilation-UNVERIFIED) + the GoCFG (a)/(b)
decision (grounded in the one VERIFIED fact: blocks are arbitrary IO) + the cmd/heap handling (UNEXPLORED).
Execute in one focused pass; commit ONLY when `make check` is green and the manifest is empty.
