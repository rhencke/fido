# Go spec conformance ledger

Current-subset status against **go.dev/ref/spec** + **go.dev/ref/mem**, in spec-document
order. Each row: **status · authoritative theorem/model surface(s) · deviation/frontier.**
Mechanism lives in the cited theorems/modules; per-item history in git — this file is a
status matrix, not an encyclopedia.

**Legend** — ✓ modeled (a machine-checked `Example`/`Theorem` witness) · ⚠ bounded
deviation (documented, tracked, never silent) · ✗ not modeled / **fails loud** (any use
ABORTS extraction with `unsupported` or fails `go build` — an honest gap, never silently
wrong).

**Trust base.** NO project-declared axioms — every GATED `Print Assumptions` surface
(PROGRESS.md "Current gates") is asserted EMPTY non-bypassably in the Docker prover stage
(the source grep is a coarse tripwire only). Model = `Definition`s/`Theorem`s over CONCRETE
data (`Z` / `nat` locations / `spec_float`; the `PrimInt63`/`PrimFloat` kernel substrate is
eliminated). IO/effect algebra is funext-free (observational `io_eq`, proved pointwise).
Stdlib `functional_extensionality` survives at exactly TWO named NON-gated families:
`run_io_inj` (the Keystone `Denotes` bridge) and `unified.v`'s `rstep_embeds`. The plugin's
goto-CFG → idiomatic-Go structuring pass is TRUSTED (gap #10: no theorem relates emitted Go
to the CFG; control-flow coverage is demo-by-demo, golden-locked).

## Lexical / Constants
- **Identifiers** — ⚠ SUPPORTED SUBSET: `go_ident` admits only the ASCII identifier grammar
  (`_A-Za-z`-led, `_A-Za-z0-9` body, non-keyword). Go identifiers are UNICODE (`letter =
  unicode_letter | "_"`); a Unicode-letter name (`café`, `π`) is a REJECTED frontier — `is_idstart`/
  `is_idc` refuse every code point > 127, so it is UNREPRESENTABLE as an `Ident` (no `go_ident s =
  true` proof), never silently mishandled.
- **Integer/float literals** — ⚠ typed fixed-width view over the `Z`-records (untyped layer
  in Constants); lexical shapes round-trip (`neglit_demo`).
- **Constants / constant expressions** — ✓ representability (out-of-range constant is
  UNREPRESENTABLE — `u8_lit`…`i16_lit` demand a fit proof, `*_const_oob` `Fail`; all 8
  wrappers SProp-sealed vs constructor forging, `*_forged` `Fail`) + arbitrary-precision
  INTEGER (`i64c`/`u64c` `vm_compute` a closed `Z`; out-of-range fails to ELABORATE;
  `const_intermediate_exceeds`/`const_oob_*`) + exact-rational FLOAT (`FConst` `num/den`,
  exact `fc_add`/`sub`/`mul`, rounds once via `SFdiv`; ±Inf/NaN unconstructable). ⚠ the
  GoCompile float GATE subset is DYADIC exact-or-reject (`m·2^e`; `float64(1)/float64(3)` is
  valid Go the gate rejects — quarantined incompleteness, never a wrong value). ⚠ the plugin
  int64 fold declines magnitudes beyond int64 and fails loud (`neg_fconst_overflow`).

## Types
- **Boolean** — ✓ (Coq `bool` → Go `bool`).
- **Numeric** — ✓ ranges / two's-complement / DISTINCTNESS by construction (`u8_no_implicit`…
  `u8_u16_no_mix`, `int_vs_int64_distinct`, injectivity `tag_runtime_agrees`). Sub-64 widths
  are each their own record (`spec_i32_add_wrap`, `spec_u32_mul_wrap`); full-width `GoI64`/
  `GoU64` wrap at the true 2⁶³/2⁶⁴ (`spec_i64_add_wrap`, `spec_u64_*`, arithmetic `>>`
  `spec_i64_shr_arith`; evidence-carrying div/shift, `i64_div_zero`/`i64_shl_neg` `Fail`);
  platform `GoInt`/`GoUint` same `Z`-carried shape (deviation closed). ⚠ residual: the 64-bit
  WIDTH choice (spec allows 32-or-64); sub-64 narrows and `SliceH` index args ride the int63
  carrier (faithful — sub-63 values never reach 2⁶²). ⚠ a constant `MAX+1` in emitted Go
  trips Go's untyped-constant check instead of the modeled runtime wrap (the Constants gap).
- **String** — ✓ byte-sequence model (`GoString := string`): `len` bytes (`str_len`,
  `spec_str_len_Go`), safe comma-ok index (`str_at_ok`, cannot panic), concat (`str_concat`),
  proof-gated slice `s[a:b]` (`str_slice`; `str_slice_oob` `Fail`), byte-lexicographic compare
  (`str_eqb`/`str_ltb`, `spec_str_lt_*`), immutable/distinct (`str_no_implicit`). Rune view:
  `string`↔`[]rune`/`[]byte`, `string(rune)` → native conversions (suppressed UTF-8 codec).
  `range s` → native `for i, r := range s`, byte offsets = prefix sums of consumed widths
  (`str_range_offsets`, `str_range_invalid_offsets`). ✗ byte-level mutation (Go forbids it).
- **Array** `[N]T` — ✓ local fixed-size (size-erased `GoArray`, `arr_lit`→`[len]T{…}`,
  bounds-checked `arr_get_ok`, comparability `arr_eqb`, VALUE-COPY `arr_set` via copy-IIFE
  `arr_set_copy`) + TYPED POSITIONS for any CONCRETE size (`GoArr<N>` → `[N]T` in var/param/
  return/field). ⚠ a position polymorphic over a SYMBOLIC `N` (type-level-`N` phantom route)
  is deferred.
- **Struct** — ✓ value-struct (Rocq `Record` → keyed literal / projection; `point_proj_px`)
  + EMBEDDING with genuine method promotion (`peel_embedded`; struct, INTERFACE-dict, and
  POINTER `*T` embedding — `node_embed_demo`) + RECURSIVE structs via the tag-free phantom
  `Ptr` + a nullary nominal tag (`tag_eq`; `linked_list_demo`). ⚠ struct tags (no-op without
  reflection); ⚠ each recursive type needs its own tag ctor (no auto-registry). ✗ embedding a
  bare PRIMITIVE.
- **Method declarations** — ✓ value + pointer receivers (mutation observed by caller,
  `cell_incx`), method VALUES (`p.M`) and method EXPRESSIONS (`T.M`/`(*T).M`) for CONCRETE
  receivers, DEFINED types over a primitive with methods (`GoTypeTag` phantom → `type MyI64
  int64`). ONE eligibility authority `method_eligible` (shared decl + call site). ✗ a
  GENERIC-receiver method used bare (`neg_method_expr_generic`, fails loud).
- **Function types** — ✓ N-ary multiple returns: left-nested `A*B*C` flattened at all four
  sites (`flatten_prod_type`/`flatten_pair_value`/`flatten_destructure`), IO and pure-tail
  positions, wildcard binder blanked to `_` (`pp_destr_binder`), narrow components cast to
  their slot (`value_narrow_conv`). A non-left-nested `A*(B*C)` stays fail-closed.
- **Interface** — ⚠ modeled as the method DICTIONARY (a struct-of-func-fields vtable +
  captured value), faithful to the SEMANTICS (satisfaction checked in Rocq, dispatch provable
  `dispatch_area`/`dispatch_greet`): 1-method (`{m; gr_self}`), nullary (`unit→R`, unit arg
  erased), N-method, and EMBEDDING (flat-union dict + explicit upcast projections). ✗ the
  native `interface { … }` KEYWORD with structural satisfaction (we emit dict-structs — a
  deviation, not a gap).
- **Slice / Map / Channel** — ✓ two slice views: functional `GoSlice = list` (value) and
  heap-backed mutable `SliceH` (`{base;off;len;cap;tag}`) with backing-array ALIASING
  (`subslice_alias` + separation `slice_idx_set_frame`, `append` in-cap-aliases/past-cap-
  reallocs `slice_append_incap_aliases`, `make`/`clear`/`copy`); maps/channels via world
  state (get-after-write theorems). Pointer↔calculus bridge `Section KeystonePtr`
  (`ptr_write_sim`/`ptr_read_sim`), flagship `mp_end_to_end` (executes to `mp_trace`,
  race-free on every interleaving, Keystone-denotes real IO, one `run_io` world). SELF-
  REFERENTIAL channel type ✓ (`ChanBox`, `chan ChanBox`). ⚠ cross-goroutine aliasing rides
  the concurrency calculus, not the functional layer. ⚠ directional channel TYPES
  (`chan<-`/`<-chan`) NOT modeled (`GoTy` has bidirectional `chan` only).

## Operators / conversions
- **Arithmetic / Integer ops / Integer overflow** — ✓ fixed-width `+ - * / %` (`uN_*`/`iN_*`,
  truncating div toward zero with evidence-carried nonzero divisor `div_nz`, MININT/−1 wrap;
  `spec_u8_div`…`spec_i8_div_ovf`), bitwise `& | ^ &^` unary `^` (width-wrapped complement;
  `GoU64` Boolean algebra `u64_{and,or,xor}_{comm,assoc}`, signed↔unsigned faithfulness
  `i64_{and,or,xor}_via_u64`), shift `<< >>` (evidence-carried non-negative count `u8_shl_neg`
  `Fail`, logical `>>` for unsigned / ARITHMETIC for signed, count-≥64 saturation). Unsigned
  overflow = mod 2ⁿ, signed = two's-complement no panic (`u8_add_wraps`, `spec_i64_add_wrap`,
  `spec_u32_mul_wrap`). ✗ plugin does not yet emit `int` bitwise/shifts (the MODEL has them,
  GoSem tier R8: `int_and`/`int_shl`…). GATE shift-count rule: conservative platform-`uint`
  window (`untyped_count_overflow`).
- **Floating-point ops** — ✓ `float64` (IEEE binary64, unguarded `/`, `float_demo`) and
  `float32` (SOUND binary32 via SpecFloat, unforgeable `f32_round` proof; NaN/signed-zero
  corners machine-checked). Conversions: `float32↔float64` (overflow→Inf `f32_overflow`,
  underflow→0), int→float32 rounds the exact integer ONCE (`f32_of_i64` — through-binary64 is
  NOT double-rounding-innocuous above 2⁵³, `f32_of_i64_differs`), constant path `f32_of_fconst`
  rounds the rational once. Constant-vs-runtime: a non-runtime-operand float op is forced to a
  runtime IIFE (Go constants can't denote −0/±Inf/NaN). ⚠ FMA fusion (we round each op; Go MAY
  fuse — bounded). ⚠ `math.Float32bits`/`frombits` (needs `math` import + NaN payload) deferred.
- **Comparison** — ✓ int SIGNED `Z`-compare → Go `</<=` (unsigned-order-on-signed rejected);
  float `spec_float` IEEE incl. NaN unordered (`nan_eqb_false`, `f64_geb_nan`=swapped `leb b a`
  so `NaN>=1` is false); string byte-lexicographic. Direct `>`/`>=`/`!=` for `i64`/`u64`/
  `string`/`f64` (`i64_gtb`…; `u64_gtb (2⁶⁴-1) 1 = true`). ⚠ direct `>`/`>=`/`!=` for the
  narrow widths pending.
- **Logical** — ✓ `&&`/`||`/`!` = Coq `andb`/`orb`/`negb` (`spec_andb`…, by `reflexivity`;
  short-circuit unobservable — pure total bools).
- **Conversions** — ✓ integer↔integer all widths (`int_of_FW` real cast / `FW_of_int`
  truncate; implicit mixing rejected `*_no_implicit`), `int64`↔`uint64` reinterpret
  (`wrap64_wrapU64`; cast applies to a VARIABLE), narrow→`int64` widening (name-recognized
  `int64(x)`), `int`/`int64`→`float64` (native, exact below 2⁵³), `float64`→`int64`
  (truncate-toward-zero via `Prim2SF`, `i64_of_f64_*`; ⚠ NaN/±Inf/overflow impl-defined),
  string↔`[]byte`/`[]rune`, `string(rune)`. ✗ interface conversions beyond `type_assert`.
- **Index expressions** — ✓ slices/strings/maps single-goroutine: raw panicking `slice_get`
  (proof-gated where range is static) + safe comma-ok `slice_at_ok`/`str_at_ok` (force OOB
  handling, cannot panic) + map `map_get_opt`/`map_get_or` (never panics).
- **Composite / function literals / calls** — ✓ for the modeled forms (`T{…}`, `[]T{…}` via
  `slice_of_list`, closures carrying dict methods + `go`/`defer` bodies, `f(a)`/`recv.M(args)`).
- **Type assertions** — ✓ tagged-`GoAny` (`{A & A*GoTypeTag A}`): `type_assert` (match⇒value /
  mismatch⇒panic, `type_assert_ok`/`tag_coerce_refl`), comma-ok `type_assert_safe` (mismatch⇒
  zero,false — adversarial `type_assert_safe_mismatch`). ✗ assert-TO-`any` and `chan any`/`[]any`
  (removing `TAny` breaks the `GoTypeTag GoAny` universe cycle; sound — a dynamic type is always
  concrete).

## Statements
- **Variables / assignment** — ✓ mutable locals (`ref_new`/`get`/`set`, read-after-write
  `ref_sel_upd_same`/`ref_get_set_same` — gated in `GoHeap.ref_addr_of_surface`, which also gates the
  address-of read/write/aliasing theorems below); address-of `&x` end-to-end (`ref_as_ptr`,
  `ref_as_ptr_not_nil`: `&x` of an allocated local (`r_loc<>0`, which `ref_new` gives ONLY in a well-formed
  world — `ref_new_loc_nonzero`, the ref analogue of `ptr_new_nonzero`, both premised on `AllocFrontierOk`) is
  NON-NIL end-to-end (`ref_new_addr_nonnil`). NON-NIL is NOT safe-deref: a non-nil `&x` to an absent/wrong-tag
  cell still FAILS LOUD, so panic-free read/write ALSO require the live cell (`ref_sel_opt = Some`, which
  `ref_new` establishes — `ref_new_reads`) — a SEPARATE premise the non-nil lemmas do not prove. The PROVEN
  end-to-end safe-deref theorems (both premises chained) are `ref_alloc_addr_read_no_panic` /
  `ref_alloc_addr_write_no_panic` (ref analogue of `ptr_alloc_assign_no_panic`), manifest-gated zero-axiom in
  `GoHeap.heap_alloc_safety_surface`. NOT unconditional, since the
  public `mkRef 0` is a representable nil ref (and a malformed world would let even `ref_new` mint one);
  `ptr_set_ref_as_ptr_aliases`; plugin
  emits `&x` FAIL-CLOSED, bound-variable operand only, else `unsupported`).
- **Short variable declarations `x := e`** — AST gate `go_compile_check` (scope-threaded
  `stmt_okS`/`body_okS` over the sealed `ScopeS`; final `scope_all_used`): ✓ redeclare / blank
  LHS / untyped nil / unused / use-before-declare all rejected (`bad_programs`, each vs gc).
  ⚠ named narrowings — valid Go the gate REFUSES (`valid_unsupported_programs`, each vs gc):
  aggregate/map locals (no aggregate values in the evaluator), shadowing a checker-recognized
  name (`decl_ident_ok`), the conservative 32-bit default-`int` RHS bound. ⚠ **supported-but-
  undenoted**: STATEMENT denotation of `x := e` is ABSENT until the env statement layer
  (`shortdecl_supported_undenoted`; the expression-level env evaluator `denote_expr_env`
  exists). — This seam must close for MVP theorem completeness.
- **If / For / Switch / Goto / Return** — ✓ via ONE goto-CFG primitive (`run_blocks`/`Jump`/
  `Done`), lifted to idiomatic Go by the TRUSTED plugin structurer (dominators, natural loops,
  `if`/`for`/labeled break-continue, raw `goto` for irreducible graphs). Coverage is DEMO-BY-
  DEMO golden-locked (`sign_demo`, `count_demo`/`labeled_break_demo`, `for i,x := range`,
  Go-1.22 `int_range`, `irreducible_demo`) — gap #10, no emitted-Go↔CFG theorem, no
  completeness claim. native `switch` is emitted (not decomposed): the `GoSwitch` combinators
  lower int64/string expression switch (`int_switch2`/`3`/`str_switch2`/`3` — semantically an
  `==`-chain, first-match-wins) and `GoAny` type switch (`type_switch2`/`3` + or-forms) to native
  Go `switch x {case v:…}` / `switch v:=x.(type){…}`. ✓ DUPLICATE cases cannot emit a Go
  "duplicate case", by TWO mechanisms matched to where each is sound:
  · EXPRESSION switch (int64/string): the combinators carry a Rocq distinctness obligation
    (`i64_neqb`/`str_neqb`), so a duplicate-case switch is UNREPRESENTABLE at the source. Because
    the equality is the MODEL's own `i64_eqb`/`str_eqb`, ANY constant case expression is compared by
    VALUE (a folded arithmetic constant `i64_add v1 v2` as readily as a literal) — no rendered text,
    no trusted-rendering dependency. A NON-constant case cannot discharge the proof, so only
    distinct-constant switches are representable (a proved restriction). The recognizer that lowers
    these (`is_val_switch_ref`) is gated to EXACTLY the sealed combinators, each with a coqc
    `*_rejects_dup` lemma that applies the combinator to EQUAL cases and derives `False` — so the
    build fails if any obligation weakens, a `neqb` predicate weakens, or an unsealed value-switch is
    added (`plugin/smart-ctor-gate.sh`).
  · TYPE switch (`GoAny` tag): the case is a rendered type NAME, which cannot be model-sealed
    soundly (it would rest on the trusted tag→Go-type bridge being injective — gap #10), so the
    plugin's type-switch arms keep an emission-level `reject_dup_cases` comparing the actual
    `go_type_of_tag` names. Negtest `neg_type_switch_dup` pins the abort.
  ⚠ coverage is BOUNDED (fixed per-arity combinators; scrutinees limited to int64/string/tag). Other control
  flow decomposes through the goto-CFG.
- **Go statements** — ✓ `go f()` → `go func(){…}()`; the fork happens-before edge is race-free
  (`fork_program_race_free`). ⚠ scheduler / interleaving idealised away.
- **Defer statements** — THREE representations + one boundary, kept separate: (R1) trusted
  plugin `defer func(){…}()` (Go's LIFO; `defer_loop_demo`); (R2) `cmd.v` `CDfr`/`run_cmd`
  FAITHFUL model (LIFO at func-return, panicking defer replaces the active panic but older
  defers still run; `bridge_effects_agree`, `structurally_total_cmd`); (R3) GoAst `GsDefer`
  ✓ emittable + DENOTED into R2 (`denote_stmt GsDefer = CDfr d (CRet tt)`, `rc_defer_lifo`/
  `rc_defer_panic`; `defer panic(v)` rejected by `panic_free_gate_defer`). (B) shallow `IO`
  has NO defer meaning → FAILS LOUD (`GoExtractionHooks.defer_call` panics, not a silent no-op).
- **Send / Receive / Select / Close** — ✓ (each on a TAG-CORRECT cell, `chan_cell_ok = true`; a nil /
  absent / wrong-tag handle fails loud at the tag guard FIRST — the wrong-tag anti-forgery theorems,
  not these) send-on-closed panics (`run_send_closed`, the DIRECT closed-state law; `send_closed_panics`
  = the close-then-send sequence), comma-ok recv closed+drained ⇒ (zero,false) (`recv_ok_closed_empty`),
  close-on-closed panics (`run_close_closed`; `double_close_panics` = the close-then-close sequence) —
  the direct-per-operation closed-state evidence gated in `chan_semantics_surface`; `select` lowers to
  faithful Go (`select_recv2`/`select_recv_default`,
  closed-drained readiness `sel_ready_cl`). Relational/operational select layer axiom-free
  (`CSelect` first-class, `rstep_select` fires any ready case, `det_select_sound`/`_incomplete`/
  `_exact_unique`). ⚠ the SEQUENTIAL select MODEL is an unsound deterministic under-
  approximation: CHOICE (both ready ⇒ takes ch1; `det_select_incomplete` — the relational
  layer is the authority) and BLOCKING (none ready + no default ⇒ fail-loud `rt_select_block`;
  Go blocks — a local non-step). ✓ close(nil) PANICS (`MkChan 0`, Go's "close of nil channel").
  ✗ nil-SEND (blocks forever) idealised away. *Pending:* `select` send cases, N-ary.

## Built-in functions
- ✓ import-free set (all plugin-lowered): `len`, `append` (`slice_append`, cap decides realloc),
  `make` (chan/map; slice `make([]T,n)` fresh-zeroed `len=n`; slice `make([]T,len,cap)` via the
  heap `SliceH` — `slice_make_lc`, spare-cap `make_lc_append_inplace`; a NEGATIVE runtime size FAILS
  LOUD — buffered channels `rt_makechan_size` (`make_chan_buf_neg_panics`), slices `rt_neg_make` —
  matching Go's runtime panic, never a silent `Z.to_nat` clamp), `new` (`go_new` → fresh
  `*T` at the zero value), `copy` (`slice_copy`), `delete`, `panic`, `print`/`println`, `recover`
  (`catch`/`with_defer`), `close`, `clear` (maps `map_get_clear`; slices `slice_clear_h`), Go-1.21
  `min`/`max` on `int`/`int64`[signed]/`uint64`[unsigned]/`float`[NaN-propagation + signed-zero]
  (`spec_go_min`, `spec_i64_max`, `spec_u64_max_high`, `f64_min_nan`), and `complex`/`real`/`imag`
  on **`complex128`** (`GoComplex128` pair of `float64`; `go_complex`/`go_real`/`go_imag` +
  component-wise `complex_add`/`_sub`/`_mul`/`_neg`, `complex_div`→native `/`; law
  `go_real_complex`). ⚠ `cap` is faithful only on the heap `SliceH` (the explicit `sh_cap` field);
  the FUNCTIONAL value-slice `cap` is INTENTIONALLY not modeled (Go's cap-after-`append` is
  spec-underdetermined). ✗ `complex64` (only `complex128` modeled); string `min`/`max` not yet
  added (not blocked — the order `str_ltb` is settled).

## Memory model (go.dev/ref/mem)
- ✓ **partial order + race freedom, axiom-free** (`hb` = transitive closure, STRICT partial
  order `hb_irrefl`+`hb_transitive`; the hb/trace/Owned/region families are `Print Assumptions`
  = Closed AND funext-free — only the Keystone `run_io_inj` carries the documented holdout).
  Channel rules 1/3/4 (`hb_send_before_recv`/`hb_recv_before_send`/`unbuffered_rendezvous`;
  capacity calculus `Section BoundedChannels` proves SAFETY `csteps_cap_respected` + LIVENESS
  `buffered_send_progresses`), rule 2 close⤳zero-recv (`hbc_close_before_zero_recv`,
  `close_not_before_value_recv`), fork edge (`fork_hb`/`fork_program_race_free`, execution-
  grounded `fork_exec_race_free`), channel-handoff edge (`handoff_race_free`). **General
  ownership-transfer race-freedom** (`region_inv_f_race_free` via ONE `rstep` induction,
  `WTf`/`RegionInvF`/`BufLinF`): all THREE mechanisms (pointer-handoff, spawn-split, signal-
  handoff) race-free for arbitrary programs and ALL interleavings; axiom- AND funext-free;
  non-vacuity `region_inv_rejects_race`. Trace model `hbt_irrefl`/`trace_ordered_no_race`;
  every reachable trace well-formed (`reachable_wf`, `reachable_hb_strict`). Keystone bridge
  `Cmd`/`Denotes`/`denote_adequate` (single-goroutine) + `reachable_refines_and_safe`. Deadlock
  characterized (`rstuck_blocked`), freedom PROVEN for receive-free programs
  (`reachable_recvfree_progress`). Initialization / goroutine-destruction N/A (faithful by
  omission). ✗ Locks/Once/Atomics (need `sync` import).
- **Still open (honest gaps):** ⚠ the READ-OBSERVATION rule `W(r)` — prior-write slice under
  `Owned` only (`last_write_before`, `visible_write_hb_maximal`); no initial-write events, no
  visible-write for racy programs. ✗ Implementation Restrictions (no-out-of-thin-air, word
  tearing) unmodeled (we reason only about race-free programs). ⚠ `sequenced before` modeled as
  a TOTAL per-goroutine order (stronger than the spec's partial; sound for straight-line
  traces). Open: heap frame law, FIFO kth-recv↔kth-send refinement, disciplined deadlock-
  freedom for receiving programs, the unverified plugin lowering (gap #10).

## Runtime payloads
- **Bounds panic** — `rt_index_oob i n` renders Go's EXACT runtime payload (verified vs gc
  1.23): non-negative ⇒ `runtime error: index out of range [i] with length n`; negative ⇒ no
  length part. ONE payload authority for `slice_get`/`slice_idx_get`/`slice_idx_set` + GoSem
  tier R2; every length STRUCTURAL (`List.length`/`sh_len`), sealed by the manifest-gated
  `slice_get_bounds_surface` (+ `len_agrees_structural`).

## Generics
- ✓ type-parameter functions with the `comparable` constraint (witness erasure → `[K
  comparable]`, native `==`).
