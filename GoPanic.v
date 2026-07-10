(** ==================================================================================================
    GoPanic — the RUNTIME PANIC PAYLOADS.  For a GENUINE modeled runtime error (nil deref,
    divide-by-zero, index/slice bounds, nil-map write, closed-channel send/close, negative
    shift/make) the string IS the exact value Go's [recover] sees — the abstraction relation to the
    Go panic value; decimals come from the ONE decimal authority ([digits.print_Z]).
    The would-block markers ([rt_chan_send_block]/[rt_chan_recv_block]/[rt_select_block]) and the
    forged-handle guard ([rt_forged_map]) are NOT recover-visible payloads: Go blocks/deadlocks, or
    (the forged handle) never reaches the state, so they are MODEL-INTERNAL fail-loud STAND-INS the
    sequential IO model raises where it cannot represent blocking — each carries its own caveat
    below, none is certified as an exact Go panic value, and the faithful blocking authority is
    [rstep] in [concurrency.v].
    Model-only values (the ops that panic with them lower to native Go operations).  No [IO]/[World]
    here — a payload is data, the PANICKING is [GoEffects.panic] at each op site.
    ================================================================================================ *)
Require Import Coq.Strings.String.
From Stdlib Require Import ZArith.
From Fido Require Import digits.
From Fido Require Import GoRuntimeTypes.

(** ---- Runtime-panic VALUES ----
    A GENUINE modeled runtime panic (the file header lists which; the would-block and forged-handle
    stand-ins are excluded) carries the SAME string Go's [recover] sees via the runtime error's
    [Error()] — so a [catch]/recover handler can DISTINGUISH runtime errors from each other AND
    from a user [panic] (which carries the user's own value).  The string IS the abstraction
    relation to Go's panic value.  Model-only: a runtime panic lowers to the NATIVE Go operation
    (whose own panic fires), so these values live solely in the suppressed op bodies and are never
    extracted — they are listed in the plugin's [is_inlined_ref]. *)
Definition rt_nil_deref    : GoAny := anyt TString "runtime error: invalid memory address or nil pointer dereference"%string.
Definition rt_div_zero     : GoAny := anyt TString "runtime error: integer divide by zero"%string.   (* integer / and % by zero — consumed by GoSem's effectful denotation (not extracted) *)
Definition rt_shift_neg    : GoAny := anyt TString "runtime error: negative shift amount"%string.    (* a NEGATIVE runtime shift count — consumed by GoSem's T5 typed-shift denotation (not extracted); payload verified against gc via go run *)
(** Decimal rendering of a [Z] (for the EXACT runtime panic payloads below) — DEFINITIONALLY
    the ONE decimal authority ([digits.print_Z], shared with the verified printer, whose parse
    round-trip [GoPrint.print_parse_Z] gates it): no second digit-builder exists. *)
Notation Z_dec_string := digits.print_Z.
(** The EXACT Go bounds-panic payload (verified against gc 1.23 via `go run`): a non-negative
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
    forged handle — is IMPOSSIBLE in a real program (Go maps are reference values you cannot forge; delete /
    clear on a genuine NIL map are Go no-ops, kept as such).  So this is a CLOSED-WORLD FAIL-LOUD GUARD for an
    unreachable state, NOT a faithful Go panic (Go's delete/clear never panic).  The op lowers to native
    delete/clear; this OPanic branch is model-only (plugin-suppressed) and unreachable for any allocated map. *)
Definition rt_forged_map   : GoAny := anyt TString "go: map delete/clear on a forged (absent or wrong-tag) handle — unreachable in a real program; closed-world fail-loud guard, not a Go panic"%string.
Definition rt_send_closed  : GoAny := anyt TString "send on closed channel"%string.
Definition rt_close_closed : GoAny := anyt TString "close of closed channel"%string.
Definition rt_close_nil    : GoAny := anyt TString "close of nil channel"%string.
Definition rt_assert_fail  : GoAny := anyt TString "interface conversion: interface is not the asserted type"%string.
(** Model-INTERNAL fail-loud for a [select] whose every case would block and that has no [default]:
    the sequential [IO] model has no Blocked outcome, so it refuses LOUDLY rather than fabricate a
    value.  Unreachable in a well-formed program; the EXTRACTION is the native Go [select{}] which
    blocks faithfully, so this value lives only in the suppressed body — in [is_inlined_ref]. *)
Definition rt_select_block : GoAny := anyt TString "go: select would block (no ready case, no default)"%string.
(** Model-INTERNAL fail-loud for a [send] with no buffer room (full [Some n], or unbuffered [Some 0] with no
    waiting receiver): Go BLOCKS, which the sequential IO model cannot represent, so it refuses LOUDLY rather
    than over-append.  Lives only in the suppressed [send] body (native Go [ch <- v] blocks
    faithfully) — like the [rt_*] above, in [is_inlined_ref]. *)
Definition rt_chan_send_block : GoAny := anyt TString "go: send would block (buffer full / unbuffered, no receiver)"%string.
(** The recv-side dual: a receive from an OPEN EMPTY channel (or a wrong-tag / absent handle, which reads
    empty) would BLOCK in Go.  Sequential [run_io] has no blocked/divergence outcome, so it FAILS LOUD with
    this NAMED payload rather than an inline string (de-duplicating the [recv]/[recv_ok] block branches) — an
    honest fail-loud STAND-IN, NOT a faithful Go panic (Go deadlocks, it does not panic); the faithful blocking
    semantics is the relational [rstep] in [concurrency.v].  Because this OPanic is a blocking stand-in, it is
    NOT certified as an exact PUBLIC panic payload: the recv anti-forgery surface pins only CLEAN NEGATIVES
    ([<> ORet]: no value / no zero delivered by [recv], no result fired by [recv_ok]), never
    [recv = OPanic rt_chan_recv_block] as recoverable-panic semantics. *)
Definition rt_chan_recv_block : GoAny := anyt TString "go: recv would block (open empty channel, no sender) — a deadlock in sequential run_io; faithful blocking is rstep in concurrency.v"%string.
(** A [make(chan T, n)] with a NEGATIVE runtime size PANICS in Go (runtime/chan.go [plainError], no
    "runtime error:" prefix — the same convention as [rt_send_closed]).  [make_chan_buf] raises this LOUDLY
    instead of silently clamping a negative capacity to 0 via [Z.to_nat].  Like the [rt_*] above, it lives
    ONLY in the suppressed [make_chan_buf] body: extraction lowers [make_chan_buf] by name to native Go
    [make(chan T, n)], which panics on a negative size on its own, so this value is in the plugin's
    [is_inlined_ref] suppression list and is NEVER emitted. *)
Definition rt_makechan_size : GoAny := anyt TString "makechan: size out of range"%string.
