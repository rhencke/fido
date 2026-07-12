(** ==================================================================================================
    GoPanic — the RUNTIME PANIC PAYLOADS (a KNOWN-INACCURATE current model; the accurate structured-
    runtime-error + result/control redesign is planned — see plans/result-control-split.md).
    ⚠ TWO CURRENT INACCURACIES, both to be FIXED by that redesign, NOT permanent:
    (1) Each payload is [anyt TString "..."].  Go's [recover] does NOT return a string — it returns a
        runtime ERROR OBJECT with a dynamic type ([runtime.boundsError] / [runtime.errorString] /
        [runtime.plainError] / [*runtime.TypeAssertionError], verified on Go 1.23.2).  The string here
        models at most the [Error()] TEXT; it is NOT the recovered dynamic value, and a type-switch on
        a recovered runtime panic would WRONGLY see [string].  Planned fix: a structured [RuntimeError]
        + [PanicValue = UserPanic | RuntimePanic].
    (2) The would-block markers ([rt_chan_send_block]/[rt_chan_recv_block]/[rt_select_block]) and the
        forged-handle guard ([rt_forged_map]) are CURRENTLY [OPanic] payloads, so [catch]/recover DOES
        observe them — WRONG: a block is a deadlock (recover never fires) and a forged handle is a
        model fault (not a Go event).  Planned fix: blocking moves into a continuation-retaining
        scheduler relation and model faults into a distinct [ModelFault] (to be PROVED unreachable, not
        asserted here); neither stays in the panic domain.  The faithful blocking authority today is
        [rstep] in [concurrency.v].
    Decimals come from the ONE decimal authority ([digits.print_Z]).  Model-only values (the ops lower
    to native Go operations).  No [IO]/[World] here — a payload is data, the PANICKING is
    [GoEffects.panic] at each op site.
    ================================================================================================ *)
Require Import Coq.Strings.String.
From Stdlib Require Import ZArith.
From Fido Require Import digits.
From Fido Require Import GoRuntimeTypes.

(** ---- Runtime-panic VALUES ----
    ⚠ Each payload is a TString modeling the runtime error's [Error()] TEXT only — NOT the dynamic
    value Go's [recover] returns (a runtime error OBJECT; see the file header, inaccuracy #1).  A
    [catch]/recover handler can distinguish these by TEXT, but the model does NOT yet expose the
    runtime-error dynamic type, so a type-switch/assert on a recovered runtime panic is not faithfully
    modeled (the planned structured [RuntimeError] fixes this).  Model-only: a runtime panic's intended Go is
    the NATIVE Go operation (whose own panic fires), so these values live solely in these op
    bodies and are never emitted. *)
Definition rt_nil_deref    : GoAny := anyt TString "runtime error: invalid memory address or nil pointer dereference"%string.
Definition rt_div_zero     : GoAny := anyt TString "runtime error: integer divide by zero"%string.   (* integer / and % by zero — consumed by GoSem's effectful denotation (not extracted) *)
Definition rt_shift_neg    : GoAny := anyt TString "runtime error: negative shift amount"%string.    (* a NEGATIVE runtime shift count — consumed by GoSem's T5 typed-shift denotation (not extracted); payload verified against gc via go run *)
(** Decimal rendering of a [Z] (for the runtime panic payloads' EXACT [Error()] TEXT below — NOT
    the recovered dynamic value; see the file header) — DEFINITIONALLY the ONE decimal authority
    ([digits.print_Z], shared with the verified printer, whose parse round-trip
    [GoPrint.print_parse_Z] gates it): no second digit-builder exists. *)
Notation Z_dec_string := digits.print_Z.
(** The EXACT Go bounds-panic [Error()] TEXT (verified against gc 1.23 via `go run`; the recovered
    VALUE is a [runtime.boundsError] object, not this string — see the file header): a non-negative
    out-of-range index reads "index out of range [i] with length n"; a NEGATIVE index reads
    "index out of range [i]" with NO length part.  Parametrized — every panic site supplies the
    actual index and length, no collapsed class-wide value. *)
Definition rt_index_oob (i : Z) (n : nat) : GoAny :=
  anyt TString (if (i <? 0)%Z
                then ("runtime error: index out of range [" ++ Z_dec_string i ++ "]")%string
                else ("runtime error: index out of range [" ++ Z_dec_string i ++ "] with length "
                      ++ Z_dec_string (Z.of_nat n))%string).
Definition rt_slice_bounds : GoAny := anyt TString "runtime error: slice bounds out of range"%string.
Definition rt_neg_make     : GoAny := anyt TString "runtime error: makeslice: len out of range"%string.
Definition rt_nil_map      : GoAny := anyt TString "assignment to entry in nil map"%string.
(** A map DELETE / CLEAR through a nonzero handle with NO tag-correct cell — an ABSENT (dangling) or WRONG-TAG
    forged handle — is a MODEL FAULT: INTENDED-unreachable (in real Go, maps are reference values you cannot
    forge; delete / clear on a genuine NIL map are Go no-ops, kept as such), but the MODEL currently lets one
    be constructed via [MkMap], so this branch is CURRENTLY reachable.  A CLOSED-WORLD FAIL-LOUD GUARD, NOT a
    Go panic (Go's delete/clear never panic).  The op lowers to native delete/clear; this [OPanic] branch is
    model-only.  ⚠ it is presently a catchable [OPanic]; the fix is a
    distinct [ModelFault], to be PROVED unreachable under StoreTyping/ValueWF (not asserted here). *)
Definition rt_forged_map   : GoAny := anyt TString "go: map delete/clear on a forged (absent or wrong-tag) handle — a model fault (intended-unreachable, not yet proved); closed-world fail-loud guard, not a Go panic"%string.
Definition rt_send_closed  : GoAny := anyt TString "send on closed channel"%string.
Definition rt_close_closed : GoAny := anyt TString "close of closed channel"%string.
Definition rt_close_nil    : GoAny := anyt TString "close of nil channel"%string.
Definition rt_assert_fail  : GoAny := anyt TString "interface conversion: interface is not the asserted type"%string.
(** Model-INTERNAL fail-loud for a [select] with no ready case and no [default]: the sequential [IO] model
    has no Blocked outcome, so it refuses LOUDLY rather than fabricate a value.  ⚠ this REUSES one payload for
    two causes: an all-EMPTY-OPEN select is a genuine DEADLOCK (not a panic), while a WRONG-TAG arm reads
    empty and also routes here — a forged MODEL FAULT.  This [OPanic] is presently reachable + catchable (to
    be fixed by the scheduler split for the block, a distinct [ModelFault] for the forgery — not asserted
    here), NOT unreachable.  The EXTRACTION is the native Go [select{}], which blocks faithfully, so this
    value lives only in the suppressed body — in [is_inlined_ref]. *)
Definition rt_select_block : GoAny := anyt TString "go: select would block (no ready case, no default)"%string.
(** Model-INTERNAL fail-loud emitted by [send] on any handle with no room.  Like its recv dual it REUSES one
    payload for DISTINCT causes: a GENUINE no-room block (a full [Some n] buffer, an unbuffered [Some 0] with
    no waiting receiver, or a nil channel) — Go BLOCKS (a DEADLOCK), which the sequential IO model cannot
    represent, so it refuses LOUDLY rather than over-append — whereas a FORGED wrong-tag / absent handle is a
    MODEL FAULT (impossible in real Go — a distinct [ModelFault] after the planned split, not asserted here).
    Lives only in the suppressed [send] body (native Go [ch <- v] blocks faithfully) — like the [rt_*] above,
    in [is_inlined_ref]. *)
Definition rt_chan_send_block : GoAny := anyt TString "go: send would block (buffer full / unbuffered, no receiver)"%string.
(** The recv-side dual, emitted by [recv]/[recv_ok] on any handle with no readable value.  It REUSES one
    NAMED payload (de-duplicating the [recv]/[recv_ok] block branches) for two DISTINCT causes the
    result/control split will separate: a GENUINE recv-block — an OPEN EMPTY (or nil) channel with no sender —
    BLOCKS in Go (a DEADLOCK; sequential [run_io] has no blocked/divergence outcome, so it FAILS LOUD here),
    whereas a FORGED wrong-tag / absent handle (which also reads empty) is a MODEL FAULT (impossible in real
    Go — a distinct [ModelFault] after the planned split, not asserted here).  Either way this is an honest
    fail-loud STAND-IN, NOT a faithful Go panic (Go deadlocks / faults, it does not panic); the faithful
    blocking semantics is the relational [rstep] in [concurrency.v].  Because this OPanic is a stand-in, it is
    NOT certified as an exact PUBLIC panic payload: the recv anti-forgery surface pins only CLEAN NEGATIVES
    ([<> ORet]: no value / no zero delivered by [recv], no result fired by [recv_ok]), never
    [recv = OPanic rt_chan_recv_block] as recoverable-panic semantics. *)
Definition rt_chan_recv_block : GoAny := anyt TString "go: recv would block (open empty channel, no sender) — a deadlock in sequential run_io; faithful blocking is rstep in concurrency.v"%string.
(** A [make(chan T, n)] with a NEGATIVE runtime size PANICS in Go (runtime/chan.go [plainError], no
    "runtime error:" prefix — the same convention as [rt_send_closed]).  [make_chan_buf] raises this LOUDLY
    instead of silently clamping a negative capacity to 0 via [Z.to_nat].  Like the [rt_*] above, it lives
    ONLY in the [make_chan_buf] body: its intended Go is native
    [make(chan T, n)], which panics on a negative size on its own, so this value is NEVER emitted. *)
Definition rt_makechan_size : GoAny := anyt TString "makechan: size out of range"%string.
