# The cmd↔unified EFFECT-bridge arc (chan/heap/spawn) — PAUSED at the heap milestone

GOAL: extend the bridge's common fragment past output/panic/return/defer — `Cmd` grows
heap/channel/spawn effects, `run_cmd` stays THE sequential authority, the public agreement
theorems grow to cover the new constructors. Proof-only (no golden/plugin risk).

DONE (theorems are the authority): slice 1 — value-parametric calculus (`Section
UnifiedVal`); slice 2 — heap read/write/ALLOC (`CWrite`/`CRead`/`CAlloc`, unallocated access = ABSENCE, deterministic allocation with the gated ValidWorld lemmas)
and the ONE conditional bridge `bridge_heap_agrees` (heap + defers + panics, final-heap
agreement from the `ustart_w` mirrored start; gated via `cmd_unified_surface`).

⚠ STANDING VALUE-SEMANTICS RULE: the GoAny instance carries NO zero semantics — Go's
closed-recv zero is PER ELEMENT TYPE, so every public bridge statement quantifies the
calculus' `vzero` universally, licensed by side conditions keeping runs inside mirrored
allocated cells. ⛔ PRECONDITION FOR CHANNELS: the closed-recv zero must be represented
STRUCTURALLY first (the channel element tag at the `URecv`/`USelect` boundary with
`zero_val`-style typed zeros); a global `GoAny` fallback is FORBIDDEN, and the slice must
land closed-recv proofs for at least TWO distinct element types.

## Remaining slices

2d. **`CAlloc` (design v2) — ★LANDED COMPLETE (fcede13 + the gate-lemma commit): every ledger box checked; the gate lemmas are IN `cmd_unified_surface` (manifest-gated).**
   ★LIVE WIP LEDGER (update as slices land; the tree may hold uncommitted WIP):
   [x] cmd.v: `CAlloc : GoAny -> (nat -> Cmd A) -> Cmd A` (appended LAST) + `cell_of_any`/
       `alloc_world` (+output lemma) + arms in Cmd_rect'/cbind/CmdEq(CE_al)/go/run_cmd +
       no_defer/cmd_no_panic/no_heap → false + all 7 induction/destruct patterns extended
       (3× Cmd_rect' patterns, 4× fix-style; run_cmd_eval/eval_run_cmd alloc cases mirror
       COut's shape — go/run_cmd are TOTAL on CAlloc).
   [x] unified.v: `UAlloc : V -> (nat -> UCmd) -> UCmd`; UConfig += `uc_next : nat` (LAST
       field — every mkUCfg gains a 9th arg, threading nx unchanged except ustep_alloc);
       `ustep_alloc` = allocate at EXACTLY uc_next, `upd h nx v`, emit `KWrite nx`, bump
       (allocation IS a write); UOnlyAcc/UMemFree deliberately gained NO UAlloc constructor
       (a dynamic location defeats the static ownership discipline — fail-closed absence;
       uprivate_disc_step's alloc inversion is vacuous); EVERY ustep
       inversion/case-analysis (~12 sites + uprivate_disc_step/uready_can_step/
       ustuck_blocked/out-trace-grows) gains the alloc case.
   [x] cmd_unified.v: `cmd_to_ucmd` CAlloc→UAlloc arm; UFrag UF_al ctor +
       cmd_to_ucmd_fragment case; ustart_w gains `(w_next w)` as uc_next;
       body_runs_sem (+ the defer-unwind ladder + the public theorems) thread the
       allocator agreement: config nx = `w_next w` in, `w_next (oc_world oc)` out
       (COut/CRead preserve w_next definitionally; CWrite via a heap_write_next lemma;
       CAlloc: both sides allocate at the SAME location, heap_agrees extends via
       any_of_cell (cell_of_any v) = v round-trip lemma).
   [x] regression obligations (gate lemmas, ValidWorld-premised): no location-0
       allocation from a valid start; no clobber of an allocated cell; preservation of
       ValidWorld through alloc (likely lands in GoHeap.v as valid_alloc_cmd or in
       cmd_unified.v).
   [x] GoSemSafe.v: two dead heap arms gain `| CAlloc _ _ =>` dead cases.
   Original design v2 spec follows:
   **(design v2 spec.)** Allocation must be DETERMINISTIC — an observably
   nondeterministic allocator leaks through the binder continuation and could clobber a
   mirrored-but-untraced cell. Shape: `CAlloc : GoAny -> (nat -> Cmd A) -> Cmd A`; `go`
   allocates at `w_next w` and bumps; unified side mirrors `uc_next` and `ustep_alloc`
   allocates EXACTLY there (emits `KWrite l` — allocation IS a write). Freshness is a
   THEOREM only under `GoHeap.ValidWorld`, so every public allocation surface carries a
   `ValidWorld w` premise with preservation through the body run and the defer unwind;
   the allocator agreement `uc_next = w_next w` threads beside `heap_agrees`. Landing
   obligations: no clobber of an allocated cell; no nil (location-0) allocation from a
   valid start; no unified allocation behavior beyond the cmd side's; a continuation
   branching on `Nat.eqb l 0` cannot reach the `l = 0` branch from a mirrored start.
   `no_heap`/`cmd_no_panic` map `CAlloc` to `false`; `UFrag`/`Cmd_rect'`/`cbind`/`CmdEq`
   gain the arm (and the `unwind_defers`/`eval_cmd` cases follow the interpreter's).

3. **CHANNELS** (single-goroutine deterministic fragment) — ★DESIGN v1 (2026-07-07),
   satisfying the ⛔ typed-zero precondition STRUCTURALLY:
   (a) cmd.v gains the channel trio, mirroring GoChan's OWN op shapes (its `recv` takes
   the element tag as an argument — the syntax carrying it is faithful, not invented):
   `CChSend : nat -> GoAny -> Cmd A -> Cmd A`,
   `CChRecv : nat -> {T : Type & GoTypeTag T} -> (GoAny -> Cmd A) -> Cmd A`,
   `CChClose : nat -> Cmd A -> Cmd A`.
   run_cmd against `w_chans` (the cell = tag + buffer + closed + cap): send on absent
   cell/full buffer/UNBUFFERED = None (a single goroutine can never complete a
   would-block — completion IS the deterministic-fragment gate); send-on-closed =
   `OPanic rt_send_closed`; payload/syntax tag vs cell tag mismatch = None (the
   well-typed discipline, exactly heap_write's); recv pops the buffer boxing through
   the CELL tag; recv on closed+drained binds `anyt tag (zero_val tag)` FROM THE
   SYNTAX TAG (checked equal to the cell's) — the per-element-type zero, no GoAny
   fallback anywhere; close on closed = `OPanic rt_close_closed`.
   (b) unified.v: `URecv` gains the closed-zero as a FIELD —
   `URecv : nat -> V -> (V -> UCmd) -> UCmd` — and `ustep_recv_closed`/`USelect`'s
   closed rule bind THAT field; the global `vzero` Section parameter DIES (the rstep
   embedding instantiates the field at 0 per site; the bridge instantiates it at the
   typed zero).  Killing vzero is the stronger form of the standing value-semantics
   rule: nothing left to quantify.
   (c) cmd_unified.v: the channel agreement kit — `chans_agree` (uc_bufs c mirrors the
   cell's buffer BOXED through the cell tag; closedb tr c mirrors the closed flag;
   position bookkeeping existential like the trace) beside heap_agrees + the allocator
   agreement; `cmd_to_ucmd` maps the trio (URecv's zero field := `anyt tag (zero_val
   tag)`); UFrag grows three ctors (the channel slice REPLACES the no-channel seal —
   the seal's claim narrows to no-spawn/no-select).
   (d) LANDING OBLIGATIONS: closed-recv agreement proofs for at least TWO distinct
   element types (TI64 and TString zeros); send-on-closed panic agreement; the
   would-block absences (unbuffered send, open-empty recv) have NO usteps
   counterpart demanded (absence is the gate); ustart_w starts with empty uc_bufs
   mirroring... a WORLD WITH LIVE CHANNELS must mirror them — `bufs_of_world` joins
   `heap_of_world`.  Every new public statement keeps run_cmd in its conclusion.
   NOTE the capacity mismatch to resolve at implementation: unified's `uroom` counts
   `length < cap` with `ucap` a RULE PARAMETER; the World's cell carries its own cap —
   the bridge instantiates `ucap := fun c => cell c's cap` via a mirroring function.

4. **SPAWN** (capstone; design deferred until reached): multi-goroutine ustep runs are
   schedule-nondeterministic vs sequential `run_cmd`. Candidate shapes: ∃-schedule
   agreement (weak); DRF ⇒ all schedules agree on observables (the payoff, composing
   `concurrency.v`); a restricted no-shared-effect child fragment. Decide with 1–3 DONE.

## Standing rules for this arc

- Ground every new projection in the existing authority via a proven equality and USE it
  the same tick. Public statements use PUBLIC vocabulary — completion is `run_cmd c w =
  Some oc`, never a bound. A real result is `Theorem` + `Print Assumptions` + PROGRESS
  "Current gates", never `Local`.
- At every landing: delete newly-subsumed demos/theorems, sweep status prose repo-wide,
  verify every "consumes/via X" against the actual proof.
- Work invariants + reductions on paper BEFORE coding (look for the one reconciliation
  law, not a parallel structure).
