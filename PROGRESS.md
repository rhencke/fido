# Fido — status

Live ledger, kept under ~10 KB — a compact CURRENT-STATE ledger, never a proof diary (per-lemma
history is in git; per-slice design is in `plans/`). Design: `ARCHITECTURE.md`; rules: `CLAUDE.md`;
mistakes: `LESSONS.md`; Go-spec: `SPEC_CONFORMANCE.md`. History is in git — **current** state only.

## The goal

Be **safer than Go's compiler can prove** — lift type/memory/concurrency safety to compile time —
while still lowering into ordinary Go. TARGET: prove, before emitting, that nil deref / OOB /
send-on-closed / failed assertion / data race / silent overflow cannot happen. ⚠️ TODAY the spine
gates STATIC compiler-admissibility (GoCompile: "this program would compile") on the main path;
behavioral safety is only the narrow off-main `emit_panic_free` seed.

**Honest claim:** *verified model components with a TRUSTED extraction backend* — NOT "formally
verified Go." No theorem relates emitted Go to its source term (gap #10). `emit_panic_free`
accepts iff the program denotes to `c` with `cmd_no_panic c` (any denotable panic rejected there;
an ABSENT program by non-denotation) — no full BehaviorSafe gate.

## Architecture (AST-first certified emission — `ARCHITECTURE.md` governs)

Spine: **GoAst** (syntactically valid) → **GoPrint** (round-trip/injectivity; SYNTAX only) →
**GoCompile** (STATIC compiler-admissibility: "would compile"; behavioral safety is a SEPARATE
layer — GoSemSafe/future GoSafe) → **GoEmit** (certificate-only emit). `GoTypes` = the shared
conservative classifier. **GoSem** gives semantics ATOP a compilable program (into `cmd.v`/`unified.v`).

**Live plugin bridge:** `plugin/go.ml` (trusted) still emits `main.go`; the extracted verified
printer prints a SMALL expression class on that path (binop trees over runtime locals, literals,
`^x`, plain field selectors, runtime numeric conversions, fixed-width bridging binops). The
plugin CONSTRUCTS the `GExpr`; only `gprint` is verified. NOT "verified Go."

## GREEN (proved / working)

- **Spine ZERO-AXIOM** (`make emit-verify`): digits / GoAst / GoPrint / GoTypes / GoCompile / GoEmit
  (digits.v = the shared decimal authority, compiled in both gated flows).
- **GoPrint injectivity** over the expression core (all postfix forms, `EConv`, slice/map composite
  literals, exact-lexer strings) — `gprint_inj` is now PARSER-FREE (applies `gtokens_inj` + `gtokens_lex`,
  NOT `parse_print_roundtrip`, which is demoted to derived parser self-consistency tooling;
  `canon_expr_unique` is a sibling corollary of `gtokens_inj`, not a dependency) — plus the statement layer
  (`print_stmt_inj`/`print_program_inj`, still STRING-injectivity). `GsDefer` supported+emittable+denoted; `GsShortDecl`
  gate-admitted; the expression-level env evaluator exists; statement-level env denotation is
  NEXT — short-decl programs are currently supported-but-undenoted.
- **GoCompile** (`GoCompile`/`go_compile_check`) — the STATIC compiler-admissibility gate
  ("this program would compile"): closed type errors rejected via `ptype`; slice + integer-key
  map literals admitted structurally; quarantines ledger-pinned; locals `x := e` via the sealed
  `ScopeS` fold (declare-only binding, marked uses, unused rejected; decl-free agreement
  `body_okS_nil_declfree`).  STATIC admissibility only, NOT behavioral safety.  (`GoCompile p :=
  go_compile_check p = true` today; the proof-bearing declarative relation is Phase 2 —
  `plans/gocompile.md`.)
- **GoEmit** — certificate-only (`EmittableProgram`); `make emit-demo` go-builds a certified
  program.
- **GoSem slice 1** (SURFACES are the authority — no theorem inventory): partial AST → `Cmd`
  denotation (print/println / panic / return / blank-assign / defer / call args) over the
  exact-or-absent constant fold; the runtime int + typed-runtime tiers SEALED through ONE shared
  evaluator with dispatch authorities pinned and boundary rows pinned absent; float constants
  exact-or-reject behind `floats_checked` with checker completeness `fsf_checked_complete` +
  guard-unreachability `floats_checked_total` (guard KEPT, fail-closed); denotation ⊆
  `GoCompile` (`gosem_sound`) + compositional converses; surfaces topic-split +
  manifest-gated. NO BehaviorSafe; main output still legacy. Zero axioms.
- **Model layer** (proof-only): the split model modules (GoNumeric → GoRuntimeTypes →
  GoEffects/GoPanic → GoSlice/GoMap/GoChan/GoHeap → GoSession/GoString/GoSwitch/GoComplex —
  `builtins.v` is DELETED), `cmd.v`, `unified.v`
  (race-freedom/liveness proved on `ustep`), `concurrency.v`.
- **cmd↔unified bridge** (`cmd_unified.v`): ONE bridge, `bridge_effects_agree` — any completing
  command (typed heap cells, ALLOCATION, the CHANNEL trio send/recv/close with per-site TYPED
  closed-recv zeros, arbitrary defer nesting, any panics) agrees with `run_cmd` end to end
  incl. final heaps/buffers/closedness, capacities pinned to the world's; the typed-zero
  obligations (TI64+TString instances, panic agreements, would-block absences, tag-mismatch
  rejection, the translation pin) are gated theorems. ⚠ catch + spawn/select later (the fragment
  covers panic PROPAGATION via `CDfr`, not recover). Zero axioms.
- **GoSemSafe** — panic-freedom properties + the narrow gate (`panic_free_gate` sound+complete,
  `emit_panic_free_gated`; both rejection mechanisms pinned). Off the main path; NOT
  BehaviorSafe. Zero axioms.
- **No project axioms; gated surfaces empty**: every manifest surface's `Print
  Assumptions` (incl. `main_effect`) is empty; gates fail the build on drift. Stdlib
  funext survives only at two named NON-gated families (`run_io_inj`; `unified.v`'s
  rstep-embedding lemmas).
- **Golden end-to-end**: `make check` diffs runtime output vs `expected_output.txt`.

## RED (not done — do not overclaim)

- Behavioral cert narrow + off-main; nil deref / send-on-closed / race unmodeled.
- **gap #10:** the MiniML→Go plugin is trusted/unverified; golden tests are the only end-to-end
  check.
- **Main output is the legacy path** (`main.go` from the plugin; `emit-demo` is the certified
  demo).
- **Map CONVERSIONS quarantined** (`ctmap_conv_unsupported_target_rejected` seals the class).
- Latent typed-lowering residuals remain dead but unproven.

## NEXT

- **The canonical relational syntax authority is the ACTIVE arc** (`plans/canonical-grammar.md`;
  syntax authority before spawn). Phases 1+2+3a landed: `CanonTy`/`CanonExpr`, `gprint_expr_canonical`,
  `lex_gprint_expr`, and `canon_ty_unique` (type-level token uniqueness, PARSER-FREE via `gttokens_ty_inj`).
  Phase 3b — parser-free EXPRESSION token uniqueness — is COMPLETE: `gtokens_inj`
  (`forall ctx e1 e2, gtokens ctx e1 = gtokens ctx e2 -> e1 = e2`, complete-list; NEVER via
  `gtokens_parse`/`parse_print_roundtrip` — assembled from the 14 same-constructor diagonals and 14
  destruct-`e2` rows over the balance/split + operator-precedence + `nonatom_len`/`olast`/first-token/
  `eb_find` toolkit; the last within-`TRP` case `ECall`-vs-`EConv` via `gtokens_ecall_neq_econv`: an
  expression prefix carries a `TLP`/`TLC` a type prefix cannot) ⇒ `canon_expr_unique` (from
  `canon_expr_tokens` + `gtokens_inj`). Both gated, zero axioms. (`ConvTy` = slice/chan/map only — the
  Option-B restriction that makes conversion-vs-call token-disjoint; named conversions need a compile env
  and are out of subset; directional channel TYPES are NOT modeled — `GoTy` has bidirectional `chan` only.)
  Phase 3c DONE: ALL printer injectivity is now PARSER-FREE — EXPRESSION `gprint_inj` off `gtokens_inj` +
  `gtokens_lex`, TYPE `print_ty_inj` off `gttokens_ty_inj` + `lex_print_ty`, and the statement/program
  DISJOINTNESS lemmas (`gprint_neq_return`/`_return_val`/`_blank`/`_defer`/`_shortdecl`) LEXICALLY
  (`gtokens_hd_not_return` + `lex_*_None`); the six dead `parse_str_*_None`/`parse_TReturn_None` bridges
  DELETED. No printer-injectivity or disjointness theorem depends on the executable parser; it survives as
  gated derived tooling — self-consistency round-trips (`parse_print_roundtrip`, `parse_gty_print_ty`) AND
  Phase-5 completeness against the grammar (`parse_complete` : `CanonExpr 0 e ts -> parse ts = Some (e, nil)`,
  and `parse_gty_complete` for types) — nothing certified depends on any of them. Phase 4 STATEMENT + PROGRAM canonical layers DONE: `stmt_tokens_inj` (via
  `gtokens_no_stmt` — expression tokens are statement-token-free) + the `CanonStmt` trio, and
  `program_tokens_inj` (body a `TSemi`-separated statement list split by `semi_free_split`, since
  `stmt_tokens` is `TSemi`-free) + the `CanonProgram` trio (`canon_program_tokens`/
  `gprint_program_canonical`/`canon_program_unique`), all gated, zero axioms — token-level uniqueness is now
  PARSER-FREE for types/expressions/statements/programs alike. LEXICAL faithfulness
  (`lex (print_stmt s) = Some (stmt_tokens s)`) is PROVED for the 3 lex-supported statement forms
  (`lex_print_stmt_exprstmt`/`_return`/`_returnval`, via `gtokens_lex`/`lex_return`/`lex_return_app`; gated).
  REMAINING (Phase 4/5): the `:=`/`=`/`defer` statement forms (need new lexer arms) and the program-level
  `lex_gprint_program` (a `TPackage`-keyword arm — "package" is a keyword that fails to lex today,
  `lex_package` — plus an ASI pass emitting `TSemi`). Phase 5: `parse_complete` (parser complete for the
  canonical grammar, `CanonExpr 0 e ts -> parse ts = Some (e, nil)`) and `parse_gty_complete` (the type
  analogue, `CanonTy t ts -> parse_gty ts = Some (t, nil)`) LANDED+gated. `parse_sound`
  (`parse ts = Some (e, nil) -> CanonExpr 0 e ts`) is FALSE as literally stated — the recursive-descent
  parser accepts REDUNDANT parens (`parse [TLP; TId x; TRP] = Some (EId x, nil)`, tokens ≠ `gtokens 0 (EId x)`)
  — so it is NOT a pursued goal in this form (would need a canonical-only parser or a reformulation).
- The cmd↔unified bridge (`plans/bridge-effects.md`): `CAlloc` AND the channel slice LANDED
  (typed zeros through the channel's own tag, gated obligations; `bridge_effects_agree` now
  exposes capacity agreement publicly). Cmd-level catch/recover, select, and spawn (the capstone)
  remain — deferred slices behind the syntax authority.
- Grow behavioral safety toward `BehaviorSafe` → `SafeProgram` → `emit_safe` — locals arc OPEN
  (`plans/gosem-locals.md`; next: the env statement layer); wire the certified path to the main
  output; widen the live GoPrint bridge — gate-honestly.

## Known trust base (TCB)

Rocq kernel · the string→`.go` extraction step · the Go toolchain · trusted foreign imports ·
the whole trusted plugin `plugin/go.ml` (gap #10) · and (once GoSem backs emission) the
`GoSem`≈real-Go adequacy assumption. No project-declared axioms; every GATED surface's
`Print Assumptions` is empty (stdlib funext survives at the two named non-gated families
— see SPEC_CONFORMANCE's trust ledger); the plugin is separate.

## Current gates

Zero-axiom is gated by `Print Assumptions` in THREE flows (single-sourced here): **manifest**
(`manifest-axioms.sh` vs empty `EXPECTED_ASSUMPTIONS.txt`) covers `main_effect` /
`gosem_trust_surface` / `gosem_string_authority_surface` / `cmd.cmd_semantics_surface` /
`cmd_unified_surface` / `gosem_panic_free_surface` / `GoSlice.slice_get_bounds_surface` /
`GoSlice.slice_index_ok_surface` (the comma-ok SAFE index slice_at_ok/arr_get_ok delivers element+true for a
STRUCTURALLY in-range index (0 <= i < List.length) and zero_val+false out of range — the safe-by-construction
panic-free slice/array read, the check-and-branch dual of the panicking slice_get. FAITHFUL on ALL states, NO
representability premise: the guard consults the STRUCTURAL List.length directly like slice_get — the whole
family (slice_get, slice_at_ok/arr_get_ok, arr_set's evidence) now uses structural bounds, so there is no
wrapped-len executable bad path; len_agrees_structural remains only as the emitted-len=structural seal. Signed
bound covers both ends, so a negative index yields ok=false) /
`GoString.str_index_ok_surface` (the comma-ok SAFE byte index str_at_ok delivers s[i]+true for a STRUCTURALLY
in-range index (0 <= i < String.length s) and 0+false out of range — the panic-free byte read. Like the slice
family, the guard consults the STRUCTURAL String.length directly (was the wrapped intraw (str_len s), the same
bad path now killed), so faithful on ALL states with no representability premise; negative index yields
ok=false) /
`GoCFG.blocks_cfg_surface` / `GoSwitch.value_switch_seal_surface` (the value-switch seal's
`*_rejects_dup` proof authority) / `GoChan.chan_wrong_tag_antiforgery_surface` /
`GoMap.map_wrong_tag_antiforgery_surface` / `GoHeap.ref_wrong_tag_antiforgery_surface` (the wrong-tag
anti-forgery cones — TYPED-LIVENESS negatives, not origin provenance — for channels / maps / refs) /
`GoMap.map_finite_surface` (map finite-support: MapFinite — the live keys (map_get_fn <>
None) are contained in a finite list — is an INDUCTIVE invariant ESTABLISHED by map_make_typed
(unconditionally: fresh cell stores fun _ => None, loc-0 nil map reads None everywhere) and PRESERVED by
map_delete/map_clear (unconditionally, any key type) and map_set (⚠ ONLY under Comparable kt — LOAD-BEARING:
the k::old_keys witness needs key_eqb soundness so the new key's class is {k}). ⚠ SCOPE (two boundaries): (1)
the CONSTRUCTOR map_make_typed GATES on a MapKeysOk (TMap kt vt) = true PROOF (a Prop, erased in extraction;
MapKeysOk is a bool Fixpoint over GoTypeTag, referenced only by that erased proof and proof-only lemmas;
RECURSIVE: every TMap node, outer key AND any
nested in the value, must have a comparable key), so a map with an invalid key at ANY nesting depth (e.g.
map[int]map[[]int]int) cannot be constructed THROUGH THIS ALLOCATOR (neg_noncomparable_key_map +
neg_nested_noncomparable_key_map are the Fail witnesses). ⚠ ALLOCATOR-BOUNDARY only, NOT global tag
unrepresentability and NOT renderability — the bad tag TMap (TSlice TI64) TI64 stays a constructible GoTypeTag
(the bad tag stays a constructible GoTypeTag; a bad-key map VALUE is constructible too, map_empty=MkMap 0
public). Emission-side the plugin has its OWN map-key rejection: go_type_of_tag (the tag→type renderer) fails
loud on a SLICE-or-MAP key — the only FIXTURE-PINNED closure (negtests/neg_chan_bad_map_key: make_chan
(TMap (TSlice TI64) TI64) aborts). The 2nd printer pp_type carries an analogous guard (pp_type_comparable_key)
for struct-field / defined-type map types, pinned by neg_map_field_bad_key (a type Bad map[[]int64]int64
aborts). MapKeysOk + these plugin checks are DUPLICATE map-key authorities GoTypeDesc must unify.
Residuals (GoTypeDesc frontier): a named-struct-with-non-comparable-field key would be uncaught by the plugin's
under-approximating goty_comparable_key `| _ -> true` — but it is currently unreachable on two counts: the only
GTNamed keys are the CLOSED nullary enumeration TListNode/TChanBox (both comparable; no generic named-struct tag
exists, so a bad-field struct can't be a GTNamed key), and a bad-field struct represented as an anonymous TProd
renders None (go_type_of_tag has no anonymous-product name, pinned by neg_map_prod_value). The frontier opens
only when GoTypeDesc adds a generic named tag. MapKeysOk doesn't prove renderability — a MapKeysOk-passing map value that the
plugin can't render fails loud, fixture-pinned by negtests/neg_map_{arrow,unit,prod}_value (TArrow-value = legal
Go but plugin-rejected; TUnit/TProd unrenderable). Do NOT read it as "a certified map is a valid Go map type".
(2)
map_set finiteness-preservation is gated only for Comparable kt (value-equal), NARROWER even than Go-comparable
— a Go-valid float64 key IS constructable (GoComparableType TFloat64=true) but not Comparable (float ±0: SFeqb
-0.0 +0.0 = true), so a float/non-value-equal set is admitted by the constructor gate but its preservation is
NOT covered — a DEFERRED frontier (support stays finite, needs per-type key_eqb-class enumeration). So the
finiteness guarantee is for VALUE-EQUAL-key maps, a SUBSET of the (Go-comparable) constructable maps. ⚠ PRESERVATION, NOT a global "every map is
finite" theorem — the function rep DOES admit an infinite-support f (a raw/forged handle carrying one is NOT
MapFinite, the typed-liveness frontier); the certified ops merely cannot PRODUCE one from a finite map. ⚠ finite SUPPORT
here; the STRONGER len(m) = |support| count-consistency is MapWF, GoMap.map_wf_surface below) /
`GoMap.map_count_transition_surface` (the STORED count field map_count steps correctly through the
map_cell_ok-guarded RAW update ROOTS (the world transformers map_upd/map_rem/map_clear_upd, NOT the IO ops that
wrap them): map_count_write_same read-back (map_count after a map_write to a tag-correct cell = the written sz)
+ deltas — map_upd +1 (new) / unchanged (existing), map_rem Nat.pred (present) / unchanged (absent),
map_clear_upd 0. ⚠ RAW-TRANSFORMER transitions on map_count ONLY — NOT map_set/map_delete/map_clear IO
semantics, NOT len(m) (= map_size); map_count = live-key support size is MapWF, GoMap.map_wf_surface below) /
`GoMap.map_wf_surface` (map COUNT-CONSISTENCY: MapWF — a NoDup key list EXACTLY enumerates
the live-key support (map_get_fn <> None) AND its length is the stored map_count, so map_count = len(m) is the
TRUE number of live keys — the count-transition surface's deferred "deeper MapWF", now PROVED. INDUCTIVE
invariant ESTABLISHED by map_make_typed (empty support, count 0, unconditionally) and PRESERVED by the guarded
PUBLIC IO ops map_set/map_delete (⚠ under Comparable kt — LOAD-BEARING, exactly as MapFinite: the k::keys
insert / filter(≠k) delete NoDup witness needs key_eqb soundness, so float ±0 keys stay the DEFERRED frontier) /
map_clear, via the raw roots map_upd/map_rem/map_clear_upd. The LIVE public-IO-op surface, parallel to
map_finite_surface — invariant preservation for the Comparable-key (value-equal) SUBSET of the constructable
maps, NOT a global "every map is count-consistent" theorem) /
`GoMap.map_semantics_surface` (the core IO-level "maps behave like Go maps" read/write laws — READ-YOUR-WRITE
(map_get_set_same: after m[k]=v, m[k] reads Some v) + erase duals (map_get_delete_same: delete(m,k) then m[k]
= None; map_get_clear: after clear(m) EVERY key = None); FRAME/locality (set/delete at k2 leaves read at k1 !=
k2 unchanged: map_get_set_diff/map_get_delete_diff); the nil-map read (map_get_empty: None for every key, any
world); get-or-default (map_get_or_hit/miss). Same-key write/read + frame laws carry Comparable kt (frame also
k1 != k2 + tag-correct cell); clear/empty/get_or need no key-comparability) /
`GoHeap.chan_state_ok_surface` ("no over-full channel" INVARIANT ChanCapOk — a bounded
channel's FIFO length <= cap — the channel analogue of SliceWF: gated across every PRIMITIVE state transition
— ESTABLISHED at construction by BOTH allocators (make_chan unbuffered + make_chan_buf: empty buffer, finite
cap; under AllocFrontierOk — nonzero-location allocation) and by every send (send_establishes_chancapok via
send_respects_capacity — the room [length<cap] gate forces it before the append), PRESERVED by recv (dequeue
shortens, or closed-drained leaves w unchanged) and close (flag-only). ⚠ the comma-ok/select RECEIVE COMBINATORS (recv_ok/select_recv2/select_recv_default) are
NOT separately gated — dequeue-then-CONTINUE forms whose channel effect is the same chan_recv_upd dequeue
already covered (only SHORTENS the FIFO) + a caller continuation out of scope, so they add no buffer-growing
transition and cannot break it. ⚠ SHAPE (buffer-length) only — a forged same-tag over-full handle stays the
typed-liveness frontier; None-cap (proof-only unbounded bridge) is vacuous, the residual
finite-vs-unbounded excision) /
`GoHeap.chan_finite_surface` (finite-vs-unbounded HALF: ChanFinite — a bounded Some cap — is
an INDUCTIVE invariant of the PRIMITIVE ops: ESTABLISHED by both constructors under AllocFrontierOk
(nonzero-location allocation; make_chan Some 0, make_chan_buf Some (Z.to_nat n)) and PRESERVED unconditionally
by send/recv/close (cap re-written unchanged). So a channel built by the allocators and evolved through
send/recv/close stays finite. ⚠ PRESERVATION, not a global confinement theorem
— chan_cap still reads None for nil/forged-absent/bridge cells (not characterised), and the comma-ok/select
receive combinators are continuation-parametric (dequeue is cap-invariant but the final world is the caller's),
OUT OF SCOPE. For a channel where both ChanFinite and ChanCapOk hold, the FIFO is bounded by a concrete n
(chan_bounded, the composition theorem, gated here)) /
`GoChan.chan_semantics_surface` (the core IO-level channel operational-semantics laws for a TAG-CORRECT
channel — the FIFO round-trip (send_recv: ch<-v into an OPEN, EMPTY channel with room, then <-ch = v; comma-ok
send_recv_ok = (v, true)); the 2-element FIFO ORDER (send_send_recv_recv_fifo: send a then b, two recvs return a
then b — a queue not a bag); and the Go-spec CLOSED-channel rules gated as DIRECT closed-state evidence for EACH
of send/receive/close: run_send_closed (send on a closed channel panics rt_send_closed), recv_ok_closed_empty
(comma-ok receive from a closed EMPTY channel = (zero_val, false)), run_close_closed (close on a closed channel
panics rt_close_closed) — plus the sequenced corollaries send_closed_panics (close then send) and
double_close_panics (close then close). ⚠ SCOPE: FAITHFUL Go behaviors ONLY — the BLOCKING cases (send with no
room, recv on empty-open — Go BLOCKS) are NOT gated here: the sequential model fails them loud, a would-block
stand-in (a DEADLOCK the sequential model can't represent) tracked for the scheduler split, deliberately excluded from the faithful gate) /
`GoHeap.heap_alloc_safety_surface` (the positive-liveness half: the
ptr/ref/map/chan allocator nonzero + live-cell + end-to-end panic-free-deref cone backing the `&x`
address-of public claim) / `GoHeap.ref_addr_of_surface` (the address-of/assignment SEMANTICS the SPEC ledger
cites: read-after-write, non-nil, read/write-through-`&x`, aliasing) / `GoHeap.heap_aggregate_liveness_surface`
(the AGGREGATE handles — slice backing + struct fields: allocator-produces-live + struct assign NO-PANIC +
struct assign/deref value-fidelity round-trip + slice read/write NO-PANIC for BOTH make allocators
(slice_make_lc + slice_make_h), in-bounds-gated & Go-faithful; PLUS the SliceWF index guard's REJECTING
direction — slice_idx_{get,set}_bad_shape_rejected fail loud (`exists p, run_io = OPanic p w`, no exported
marker) on a cap<len malformed header, pinning the index guard BOTH ways as slice_bulk_write_surface does for
clear/copy; ⚠ that rejects ONLY the nat-shape — a same-tag alias over a live backing still passes (typed
liveness, not provenance, the typed-liveness frontier); slice transformers subslice/append are out of
scope; the aggregate make-allocator no-panic cone matches the scalar families) / `GoHeap.slice_bulk_write_surface`
(the bulk slice ops clear/copy — tag-aware fail-loud guarded in the def; the GATED facts are: PRESERVE
AllocFrontierOk on the live path (valid_run_slice_clear_h/copy) AND REJECT-WHEN-GUARD-FALSE by failing loud —
slice_clear/copy_rejected (`exists p, run_io = OPanic p w`) fire whenever an impossible shape OR a
dead/dangling/wrong-tag cell makes the guard false, with _bad_shape_ corollaries pinning the impossible len>cap
shape for clear, copy's DST, and copy's SRC. So a shape-malformed / dangling / wrong-tag slice cannot silently
succeed, and the live path stays AllocFrontierOk; the per-cell writes are tag-aware BY CONSTRUCTION (no
fabricate/retype — a def property, not a separate gated theorem). ⚠ rejects malformed/dangling/wrong-tag, NOT
every forged handle — a same-tag alias over a live backing passes (typed liveness, not provenance)) /
`GoHeap.slice_transformer_wf_surface` (the transformer half, sh_len<=sh_cap SliceWF pinned
BOTH ways: REJECT a malformed cap<len parent — subslice/slice_append _bad_shape_rejected fail loud (exists p =
OPanic p w, no exported marker; subslice must guard on len<=cap or its b<=cap bounds check would silently
NORMALIZE a forged parent into a clean child) — AND PRESERVE well-formedness on every ORet output
(_preserves_wf). So a transformer neither launders nor manufactures a malformed header; the only malformed
source, a raw mkSliceH forgery, is caught by the index ops' bad_shape rejection, closing the well-formed slice
algebra. ⚠ nat-SHAPE only, NOT backing-object identity — the same-tag-alias case stays the typed-liveness
frontier) /
`GoHeap.live_handle_surface`
(the REUSABLE `Live*` family — the four SCALAR predicates LiveRef/LivePtr/LiveChan/LiveMap,
one canonical typed-liveness interface over the per-family checks; allocators produce Live*) /
`GoHeap.live_aggregate_handle_surface` (the two AGGREGATE peers completing the six-handle family — LiveSlice
= WELL-FORMED shape (sh_len<=sh_cap) + whole [0,cap) backing live, with LiveSlice_index_live the payoff (an
in-len index has a live typed cell — the theorem a len>cap forged header breaks, so the shape conjunct is
load-bearing), LiveStruct = NON-NIL pointer with every field live; BOTH slice makes produce LiveSlice,
gsptr_new (under AllocFrontierOk) produces LiveStruct, and gsptr_assign_live WIRES LiveStruct into the
whole-struct semantics — a live struct's assign returns, BOTH conjuncts consumed. gsptr_deref/gsptr_assign
NIL-GUARD on a zero base (rt_nil_deref) like the scalar Ptr ops and Go's `*p`, so even a zero-field struct's
nil deref FAILS LOUD — never claimed safe. LiveSlice bolts on NO base guard (a nil slice is a valid empty Go
slice that never faults), but DOES carry the len<=cap shape invariant) / `GoHeap.live_preserve_surface`
(each family's RAW UPDATE ROOT preserves Live* — ref/ptr ref_upd, chan_*_upd, map_*) / `GoHeap.live_op_preserve_surface`
(the CHECKED op preserves Live* for the always-succeeds-on-live writes: ref/ptr set, map set/delete/clear return
`ORet` with the world still Live) / `GoHeap.live_chan_op_preserve_surface` (the case-split channel ops
send/recv/close keep a live channel Live over the world after the outcome — covering their panic/block branches,
not asserting `ORet` (blocking is intended-faithful only in the RELATIONAL authority; the shallow-IO would-block
branch is an inaccurate `OPanic` stand-in — fix tracked in plans/result-control-split.md);
**printer** + **emit** (compiled STANDALONE incl. `digits.v`, grep `^Axioms:`) cover the spine. A
`Print Assumptions` under none of the three is not gated.

- `make check` — Docker: re-extract, run, golden diff; the three zero-axiom flows, the
  axiom-authority self-test, `negtests/`, the code-discipline gates
  (`plugin/smart-ctor-gate.sh`), `emit-demo`, gofmt, `go vet`.
- `make emit-verify` / `make printer-verify` — local mirrors. `make negtest` — fail-closed
  harness.
- Pre-commit hook: re-extracts on `.v`/plugin change and SEALS the tree (fail-closed if any `*.go` is
  tracked — the generated Go is gitignored, never committed); anti-axiom declaration scan.
