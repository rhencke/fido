Claude Code milestone: Complex64/Complex128 Exact Constants and Intrinsic Typed Values

THIS FILE IS THE BINDING MILESTONE CONTRACT.

Before implementation

1. Stop any currently running `/loop`.

2. Replace the tracked repository file:

   .review/NEXT_STEPS.md

   with this directive VERBATIM.

   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not “improve,” weaken, or broaden the selected architecture while copying it.

3. Commit `.review/NEXT_STEPS.md` as the opening commit of this milestone, before implementation.

4. Record the contract commit SHA.

5. Read:

   .review/CODEX_REVIEW_POLICY.md

   before implementation and before every Codex stop review.

6. After the contract commit, issue this exact Claude Code command:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

The loop is authorized only for this milestone.

The loop must:

- implement only this binding milestone;
- use the permanent Codex review policy;
- repair blocking implementation defects within the declared scope;
- stop and notify the user on an architectural conflict;
- return GREEN when no blocking implementation defect or architectural conflict remains;
- not add an operation, type family, import, generic feature, or hostile-environment hardening merely because the new root makes it possible;
- after GREEN, run final verification, commit the completed checkpoint, notify the user, stop the loop, and wait.

Current baseline

Build from current tip:

  bc731fba9f97d5780b3be45c95b388da10b67c89

That baseline contains the completed Intrinsic Typed Constants and Exact Constant-to-Runtime Coherence foundation:

- one exact type-free `GoConst` domain;
- one intrinsic `TypedConst : GoType -> Type`;
- one `ResolvedConst`;
- one `TypedFloatConst` carrying exact rounded rational + stored runtime IEEE value + coherence;
- one single-rooted `round_typed_float` construction;
- no `ci_ok := True`;
- no second rounding during evaluation;
- no false total runtime-to-constant fallback;
- general runtime NaN/Inf/-0 values remain possible but do not denote constants;
- evaluation returns exactly the runtime stored in the resolved typed constant.

Do not reopen that architecture.

Milestone purpose

Continue the Static Type Universe Arc with the two Go complex types:

  complex64
  complex128

This milestone adds exact complex constants and intrinsically coherent typed/runtime complex values.

The permanent semantic distinction is:

  exact untyped ComplexConst
    -> intrinsic TypedComplexConst ct
         whose two components are existing TypedFloatConst values
    -> general runtime ComplexValue ct
         whose two components are existing FloatValue values

The component float foundation is the authority.

Do not duplicate float exact/runtime coherence inside a second complex-specific proof system.

This milestone also closes four small nonblocking residue items from the preceding review.

Scope

The operational target remains:

- Go language version 1.23;
- pinned Go 1.23 toolchain;
- linux/amd64;
- no imports;
- no generics;
- no workspaces;
- no ambient packages.

The current executable language remains:

- `func main`;
- builtin `println`;
- bool, integer, float, string, and new complex constant expressions;
- explicit integer, float, and new complex constant conversions.

Do not add:

- complex arithmetic;
- complex comparison;
- unary complex negation;
- complex division;
- `real`;
- `imag`;
- a general call expression;
- imaginary-literal syntax;
- `+`, `-`, `*`, `/`, shifts, or any other arithmetic expression;
- variables;
- assignments;
- user-defined functions;
- parameters or results;
- control flow;
- pointers;
- arrays;
- slices;
- structs;
- maps;
- channels;
- named types;
- methods;
- interfaces;
- imports;
- generics;
- `uintptr`, `byte`, or `rune` in this round;
- a second AST, typed AST, compiled AST, target AST, or text IR.

Standing law

Ruthless correctness or ruthless deletion.

History is a technical quarry.

The current one-AST architecture is the authority.

The AST is the IR.

There is:

- one raw AST;
- one `GoProgram`;
- one `GoType`;
- one `GoConst`;
- one intrinsic `TypedConst : GoType -> Type`;
- one runtime `GoValue` domain using the same `GoType`;
- no parallel runtime type tag;
- no handwritten OCaml language semantics;
- no name-based plugin lowering;
- no extraction-driven semantic wrapper trick;
- no false total projection from runtime values to constants.

Codex review cadence

Codex review is expensive and runs on Claude’s stop event. Structure this foundational milestone to maximize review value.

Use at most two intentional Codex review barriers:

1. Semantic-root review.
2. Final exhaustive review.

Do not intentionally stop for:

- progress narration;
- ordinary questions already answered by this contract;
- routine compilation;
- mechanical wiring;
- ordinary proof completion;
- fixtures;
- documentation;
- generated-artifact updates.

Work continuously until a barrier is genuinely ready.

Semantic-root review

Use one intermediate stop because this milestone introduces a foundational semantic authority.

Stop only when all of the following are true:

- the four residue cleanups are complete;
- `ComplexType`, `ComplexConst`, `ComplexValue`, and `TypedComplexConst` are implemented;
- component-derived complex rounding/construction is implemented and proved;
- `GoType`, `GoConst`, `TypedConst`, `ConstInfo`, conversion, defaulting, resolution, runtime projection, and renderer denotation are integrated;
- same-type identities and cross-numeric complex representability are universal, not merely concrete fixtures;
- old or competing complex authorities do not exist;
- the root compiles;
- the public assumption surfaces for the root are green;
- the whole-theory assumption audit is green;
- generated witnesses, broad real-Go fixtures, final docs, and tracked generated output may still be incomplete.

Before that stop, commit the coherent root checkpoint with a message beginning:

  milestone(root):

Any Codex-driven repairs to that root must be separate commits whose messages begin:

  review(root):

A re-review after a repair belongs to the same semantic-root barrier; it is not permission to create additional design barriers.

After the root review is GREEN, do not stop again until the final exhaustive review.

Final exhaustive review

After root GREEN:

- complete all witnesses;
- complete real-Go acceptance/rejection fixtures;
- update generated artifacts through the certified pipeline;
- reconcile all active documentation;
- run complete proof, audit, e2e, and repository gates.

Commit the final review candidate with a message beginning:

  milestone(final):

Any Codex-driven final repairs must be separate commits whose messages begin:

  review(final):

Keep implementation and review-driven repair commits separate.

Do not squash them together.

The commit history must preserve enough timestamp and diff evidence to evaluate whether the semantic-root review justified its 10–15 minute cost.

PART A — close the four small residue items first

1. Delete the stale “bijection” claim

`GoRender.v` still describes existence plus functionality as a “genuine bijection on the rendered image.”

That is false.

Different spellings may denote the same exact value, for example `0` and `-0`.

The proved property is:

- every Fido-rendered expression has a denotation;
- for a fixed source spelling, the denotation relation yields at most one `ConstInfo`.

Replace the stale wording with exactly that level of claim.

Do not weaken or remove `render_const_info_denotes_functional`.

2. Fix the stale `GoTypes.v` fragment description

The opening description still says “bool/integer/string fragment” despite live float support.

Update it to include the complete live scalar/constant fragment, and later in this milestone include complex.

3. Fix the stale assumptions-gate comment

`gate/axiom_gate.v` still refers to the deleted `const_value` path.

Replace that prose with the current authority:

  const_info
  const_info_exact
  TypedConst
  ResolvedConst

Do not reintroduce `const_value`.

4. Remove the duplicate gate entry

`Floats.float_representableb_spec` is listed twice in the public assumptions gate.

Keep one intentional entry.

Do not alter gate fail-closed counting incorrectly; update the expected count through the normal gate mechanism.

PART B — historical complex quarry

5. Read the old complex work before designing

Read the original complex128 landing:

  git show 11adcdd6dead22acf0656ef33ab8f67276496972

Read the axiom-free SpecFloat migration that rebased the old float/complex runtime values:

  git show 445aca38ef5a043f69e088be27a21713e822381f

Read the split mature complex file:

  git show c187bce691faf361044bfb0a613c0943816e7274:GoComplex.v

Read the Great Culling rationale:

  git show 33c8df0f2273adae8eed15ec0e45a7b000fb7235

Read the checkpoint that deleted the disconnected runtime/backend island:

  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5

Read the complex constant-versus-runtime soundness correction:

  git show 70106ab81a723bfb5d48a933a496d5e53a03671a

Read the documentation correction confirming that old work completed complex128 but left complex64 missing:

  git show c187bce691faf361044bfb0a613c0943816e7274

Useful searches:

  git log -S 'GoComplex128' --all
  git log -S 'complex64' --all
  git log -S 'go_complex' --all
  git log -S 'complex_const_runtime' --all
  git log -S 'complex_div' --all
  git log -S 'complex SOUNDNESS FIX' --all

6. Read later arithmetic commits only as deferred scars

These commits are useful future references but are OUT OF SCOPE now:

  52e83b499a9ccbadbaa22d67b2de87aeb7552425   complex + / -
  7268f09a83f8667a740a232bcd36054afdcf6855   complex == / !=
  f776a9215d196b0a5c5a5e4578b273c72a1977d6   complex multiply
  75a06972428e01ba7cb6943a0c89419b01351679   complex unary negation
  95fb3b62cec5bbdbb03045612694cc8716faad09   complex division

Do not transplant their operations.

Retain only their warning that runtime complex operations must not accidentally execute in Go’s exact constant world.

7. Required transplant ledger

Before implementation, put a concise ledger in the semantic-root commit message or a temporary review note:

| Historical item | Current destination | Disposition |
|---|---|---|
| complex value as two float components | `ComplexValue ct` | retain/generalize |
| exact real/imag projection laws | component projections | retain |
| SpecFloat component runtime values | existing `FloatValue` | retain |
| old `GoComplex128` record | none | replace shape |
| complex64 | new `ComplexType C64` | implement fresh |
| exact untyped complex constants | `ComplexConst` | implement fresh |
| intrinsic typed complex constants | `TypedComplexConst` | implement fresh from `TypedFloatConst` |
| old plugin `go_complex`/`real`/`imag` recognition | none | reject |
| extraction wrapper suppression | none | reject |
| complex arithmetic/comparison | future operations arc | defer |
| constant-vs-runtime soundness scar | proofs/docs/tests | retain |

Do not copy `GoComplex.v` wholesale.

PART C — one complex type authority

8. Add `Complexes.v`

Create a new certified module:

  Complexes.v

It may import `Floats.v`.

It must not import `GoTypes.v`.

This keeps dependency direction clean:

  Floats
    -> Complexes
    -> GoAST / GoTypes / GoSafe / GoRender

Add it to Dune/module coverage so the whole-theory audit includes it automatically.

9. Define exactly two complex types

Define:

  Inductive ComplexType :=
  | C64
  | C128.

Provide one authority for:

- decidable equality;
- keyword:
  - C64 -> `"complex64"`;
  - C128 -> `"complex128"`;
- component type:
  - C64 -> F32;
  - C128 -> F64.

Suggested root:

  complex_component_type : ComplexType -> FloatType

All complex precision and runtime properties must derive from this mapping.

Do not duplicate:

- precision values;
- exponent bounds;
- float keyword logic;
- a complex-specific float format tag.

10. Extend the one `GoType`

Extend:

  GoType

with exactly:

  TComplex : ComplexType -> GoType

The live universe becomes:

- TBool;
- TInteger IntegerType;
- TFloat FloatType;
- TComplex ComplexType;
- TString.

No placeholder future constructors.

No `TNumeric`, `TUnknown`, `TRaw`, or `TOpaque`.

PART D — exact untyped complex constants

11. Add exact `ComplexConst`

In `Complexes.v`, define:

  Record ComplexConst := {
    cc_real : FloatConst;
    cc_imag : FloatConst
  }.

A `ComplexConst` is exact mathematical meaning.

Its two components are exact canonical rationals.

It has:

- no signed zero;
- no infinity;
- no NaN;
- no runtime `spec_float` value;
- no source spelling.

Provide:

- decidable equality derived from `FloatConst` equality;
- `complex_zero`;
- `complex_of_real` or equivalent scalar embedding;
- exact imaginary-zero decision;
- component projection theorems.

Do not add proof fields that merely restate each component’s existing `FloatConst` canonicality.

12. Extend `GoConst`

Extend:

  GoConst

with:

  CComplex : ComplexConst -> GoConst

`GoConst` remains the one exact type-free constant domain.

Do not create a separate numeric constant sum beside it.

13. Add an intrinsic finite-decimal complex literal value

Add a raw-literal semantic domain composed of two existing `DecimalFloat` values, for example:

  Record DecimalComplex := {
    dc_real : DecimalFloat;
    dc_imag : DecimalFloat
  }.

Define:

  decimal_complex_value : DecimalComplex -> ComplexConst

by applying `decimal_value` independently to both components.

No additional proof field is needed beyond the intrinsic validity of each `DecimalFloat`.

The internal `ComplexConst` domain is wider than the raw decimal-complex literal domain.

Do not use:

- raw Go source text;
- imaginary-literal spelling;
- host complex values;
- `spec_float` as exact constant meaning.

PART E — raw complex syntax

14. Grow the AST minimally

Add exactly two raw expression constructors:

  EComplex : DecimalComplex -> GoExpr
  EComplexConvert : ComplexType -> GoExpr -> GoExpr

Equivalent names are acceptable.

`EComplex` is a semantic complex-literal node.

It is not a general function call.

It renders through a canonical use of Go’s predeclared `complex` function, but the raw AST does not gain:

- a call node;
- callee identifiers;
- argument lists;
- `real` or `imag` operations.

`EComplexConvert` is explicit `complex64(...)` / `complex128(...)` conversion syntax.

Keep `EIntConvert` and `EFloatConvert`.

Do not add imaginary literals in this milestone.

PART F — general runtime complex values and intrinsic typed complex constants

15. Add general `ComplexValue`

In `Complexes.v`, define:

  Record ComplexValue (ct : ComplexType) := {
    cv_real : FloatValue (complex_component_type ct);
    cv_imag : FloatValue (complex_component_type ct)
  }.

This is the general runtime complex domain.

Because each component is a general `FloatValue`, a runtime complex value may contain:

- finite components;
- positive or negative zero;
- infinity;
- NaN.

Do not narrow this domain to constant-origin values.

Future runtime operations will need the full IEEE component domain.

16. Add `TypedComplexConst`

Define:

  Record TypedComplexConst (ct : ComplexType) := {
    tcc_real : TypedFloatConst (complex_component_type ct);
    tcc_imag : TypedFloatConst (complex_component_type ct)
  }.

This is the core design.

Do not duplicate the float coherence fields.

Each component already carries:

- exact destination-rounded rational meaning;
- stored canonical runtime IEEE value;
- exact/runtime coherence;
- finite-or-positive-zero constant shape.

Define projections:

  typed_complex_exact : TypedComplexConst ct -> ComplexConst

  typed_complex_runtime : TypedComplexConst ct -> ComplexValue ct

using only component projections.

Prove componentwise:

- exact real/imag values are `tfc_exact`;
- runtime real/imag values are `tfc_runtime`;
- each runtime component reads back to its exact component;
- each runtime component is finite or positive zero;
- neither runtime component is negative zero, infinity, or NaN.

These should be short projection theorems.

17. Add one construction authority

Define:

  round_typed_complex :
    forall ct,
      ComplexConst ->
      option (TypedComplexConst ct)

It must:

1. derive the component `FloatType` from `complex_component_type ct`;
2. call `round_typed_float` exactly once for the real component;
3. call `round_typed_float` exactly once for the imaginary component;
4. fail if either component overflows or otherwise cannot produce a typed float constant;
5. package the two resulting `TypedFloatConst` values directly.

Two component roundings are required and correct.

Do not add a third rounding or a complex-specific reimplementation of float rounding.

Do not reconstruct component runtimes from their exact rational values later.

18. Make representability derivative

Define complex representability through existence of a typed result:

  ComplexConstRepresentable ct c :=
    exists tc,
      round_typed_complex ct c = Some tc

with a reflected boolean.

If a rational-only helper remains, it must be a projection of `round_typed_complex`, not a competing authority.

Overflow in either component rejects the whole complex conversion/defaulting operation.

Underflow of either component to zero is accepted and simplified to positive zero, inherited from `TypedFloatConst`.

PART G — extend intrinsic typed constants

19. Extend `TypedConst`

Add:

  TCComplex :
    forall ct,
      TypedComplexConst ct ->
      TypedConst (TComplex ct)

Then extend:

  typed_const_exact

with:

  TCComplex ct tc -> CComplex (typed_complex_exact tc)

No mismatched complex type/value pair can exist.

20. Extend `ResolvedConst` only by consequence

`ResolvedConst` is already existential over `TypedConst`.

Do not add a second complex-specific resolved package.

The existing generic package must handle complex constants automatically.

PART H — one complete numeric conversion authority

21. Add exact numeric helpers without creating a second authority

Add small helpers under `GoTypes` or `Complexes` as appropriate.

Conceptually useful exact projections:

  numeric_const_to_complex : GoConst -> option ComplexConst

with:

- CInt z -> `(fc_of_Z z, 0)`;
- CFloat q -> `(q, 0)`;
- CComplex c -> `c`;
- bool/string -> None.

And:

  complex_real_if_imag_zero : ComplexConst -> option FloatConst

which succeeds only when the exact imaginary component equals exact zero.

These helpers must be pure exact-value helpers.

They must not perform destination rounding themselves.

22. Extend integer-target conversion

For an integer destination:

- CInt z:
  - existing exact range rule;
- CFloat q:
  - existing exact-integral + range rule;
- CComplex c:
  - imaginary component must be exact zero;
  - real component must denote an exact integer;
  - that integer must fit the destination;
- bool/string:
  - reject.

This matches Go constant representability examples such as:

  int(complex(3.0, 0.0))

and rejection of:

  int(complex(3.0, 1.0))
  int(complex(3.5, 0.0))

No runtime truncation applies to constants.

23. Extend float-target conversion

For a float destination:

- CInt z:
  - existing exact integer embedding + destination rounding;
- CFloat q:
  - existing destination rounding;
- CComplex c:
  - imaginary component must be exact zero;
  - round the exact real component at the destination;
- bool/string:
  - reject.

For a source typed complex constant whose component type already equals the float destination and whose imaginary component is exact zero:

- return the existing `tcc_real` `TypedFloatConst` directly;
- do not reround it;
- do not reconstruct it from `tfc_exact`.

Thus converting a `complex64` typed constant with zero imaginary part to `float32` projects the existing real component.

The analogous `complex128` -> `float64` rule applies.

For a different float destination, round the exact real component once at the explicit boundary.

24. Add complex-target conversion

For a complex destination:

- integer source -> exact real integer + exact zero imaginary;
- float source -> exact real rational + exact zero imaginary;
- complex source -> both exact components;
- bool/string -> reject.

Then construct the destination through `round_typed_complex`.

Same-type typed complex conversion must return the existing `TypedComplexConst` unchanged:

  convert_const (TComplex ct)
    (CITyped (TComplex ct) tc)
  = Some tc

This theorem is load-bearing and universal.

Do not reround either component.

For a different complex destination:

- use `typed_complex_exact` from the source typed constant;
- round each exact component once at the new destination component format;
- preserve the explicit conversion boundary.

25. Reuse matching typed float components when constructing complex values

When converting a typed float constant to a complex destination whose component format is the same:

- reuse the existing typed float as the real component;
- construct only the positive-zero imaginary component;
- do not reround the real component.

For a different component format, round the exact real value once at the complex destination.

This is the component analogue of same-format float identity.

26. Keep `convert_const` the one authority

Extend the existing target-indexed:

  convert_const :
    forall target,
      ConstInfo ->
      option (TypedConst target)

with `TComplex`.

Do not add:

- `convert_complex_const` as a competing public authority;
- a renderer-specific conversion check;
- a runtime conversion path for constants;
- a second numeric representability table.

Small private helpers are acceptable only when `convert_const` remains the one public semantic authority.

27. Make untyped representability complete across numeric kinds

`ConstRepresentable` is derived from:

  type_untyped_const_at

Extend it to the actual Go constant representability rules:

- integer and floating constants may be represented by complex targets if both derived components fit;
- complex constants may be represented by integer or floating targets only when the exact imaginary component is zero and the real component satisfies the scalar target rule;
- complex constants are represented by complex targets componentwise;
- bool/string cross-kind cases reject.

Prefer routing numeric cases through the same conversion helpers rather than duplicating range and rounding logic.

Pin the official Go examples conceptually:

  0i          is representable as int
  42 + 0i     is representable as float32
  42i         is not representable as float32

28. Default untyped complex constants to complex128

Extend `default_const`:

  CComplex c
    -> round_typed_complex C128 c
    -> pack_resolved (TComplex C128)

A bare complex literal remains untyped before use-context defaulting.

If either component overflows complex128, defaulting fails.

Do not assign `complex128` directly inside the raw `EComplex` node.

29. Extend use-context resolution

`UsePrintlnArg` allows both complex types.

Update:

- `gotype_eqb`;
- `UseAllows`;
- `use_allowsb`;
- `ResolveExpr` proofs;
- statement/file/program typing reflection;
- determinism;
- all exhaustive matches.

No typed AST.

PART I — runtime projection and honest constant denotation

30. Extend `GoValue`

Add:

  VComplex :
    forall ct,
      ComplexValue ct ->
      GoValue

Then:

  value_type (VComplex ct _) = TComplex ct

A `ComplexValue` uses the same `ComplexType` and component mapping as the type system.

No `GoTypeTag`.

31. Extend typed-constant runtime projection

Extend:

  typed_const_to_value

with:

  TCComplex ct tc
    -> VComplex ct (typed_complex_runtime tc)

This is a projection.

It must not call:

- `round_typed_complex`;
- `round_typed_float`;
- `round_float_sf`;
- any runtime-to-constant fallback.

32. Extend `ValueDenotesConst`

Add one constructor through intrinsic typed complex coherence:

  VDComplex :
    forall ct (tc : TypedComplexConst ct),
      ValueDenotesConst
        (VComplex ct (typed_complex_runtime tc))
        (CComplex (typed_complex_exact tc))

Do not relate an arbitrary runtime complex value to a constant merely because both components happen to be finite.

Do not add a total runtime-complex-to-constant function.

33. Preserve the full runtime-only domain

Construct representative general runtime complex values containing:

- a NaN real component;
- an infinity imaginary component;
- a negative-zero component.

Prove they are valid `ComplexValue`s but do not satisfy the typed-constant denotation relation.

A `TypedComplexConst` must prove both components are finite or positive zero.

Do not narrow `ComplexValue` to make these cases impossible.

34. Evaluation must return the stored complex runtime exactly

The existing generic theorem:

  eval_expr_resolved_value

must continue to prove evaluation returns the runtime stored in the same resolved typed constant.

Add a complex corollary equivalent to:

  resolve_expr_const u e =
    Some (pack_resolved (TComplex ct) (TCComplex ct tc))
  ->
  eval_expr e =
    Some (VComplex ct (typed_complex_runtime tc))

This must be projection-driven.

No component is reconstructed or rerounded.

35. `GoSafe` responsibility remains unchanged

Complex constants and conversions introduce no panic, blocking, heap, scheduler, or nontermination behavior.

`GoSafe := True` remains honest for the current fragment.

Do not predeclare runtime complex arithmetic outcomes.

PART J — canonical source rendering

36. Render the raw complex literal canonically

Render:

  EComplex d

as exactly:

  complex(<canonical-real-decimal>, <canonical-imag-decimal>)

using existing `render_decimal` for both components.

Use one comma followed by one space.

Examples:

  complex(15.0e-1, -25.0e-1)
  complex(0.0, 0.0)

This is a dedicated canonical complex-literal spelling.

It does not introduce a general call renderer.

It does not preserve human source spelling.

37. Render explicit complex conversions

Render:

  EComplexConvert C64 e
    -> complex64(<render e>)

  EComplexConvert C128 e
    -> complex128(<render e>)

Use `complex_keyword` from the one `ComplexType` authority.

38. Add an independent complex-literal decoder

Add a small certified decoder for exactly the canonical Fido complex-literal subset.

It is not a general Go parser.

It should recognize:

- exact prefix `complex(`;
- one real decimal component;
- exact separator `, `;
- one imaginary decimal component;
- one closing `)`;
- no trailing bytes.

Reuse the existing independent `decode_decimal` for each component.

It must not call the renderer to decide what it accepts.

It may accept a harmless semantic superset if documented honestly.

Prove:

  decode_complex_literal (render_complex_literal d)
    = Some (decimal_complex_value d)

This is a semantic round trip.

Do not claim source-spelling inversion.

39. Prove complex rendering is ASCII and shape-safe

Prove:

- complex literal rendering is ASCII;
- complex conversion rendering is ASCII;
- it cannot be mistaken for a bare integer, bare float, bool, string, integer conversion, or float conversion;
- `complex(` is distinct from `complex64(` and `complex128(`.

40. Extend `RenderedConstInfoDenotes`

Add:

- bare complex constructor:
  - decoded canonical literal;
  - `CIUntyped (CComplex c)`;
- complex conversion constructor:
  - recursively denoting inner expression;
  - one `convert_const (TComplex ct)` result;
  - `CITyped (TComplex ct) tc`.

Do not repeat component representability or rounding in `GoRender`.

The renderer cites the one conversion authority.

41. Re-prove the renderer roots

Extend:

  render_const_info_denotes
  render_const_info_denotes_functional
  render_resolved_expr_denotes

The functional claim is exactly:

> one rendered spelling denotes at most one `ConstInfo`.

Do not call it a bijection.

The final resolved theorem must expose:

- raw `ConstInfo`;
- resolved intrinsic `TypedConst`;
- exact stored runtime;
- exact `GoType`;
- `ValueWF`;
- `ValueDenotesConst`;
- the same stored complex runtime for typed complex constants.

PART K — mandatory semantic scars and fixtures

42. Basic exact complex fixtures

Kernel-check:

- `complex(1.5, -2.5)` analyzes to an untyped exact `ComplexConst`;
- exact real projection is 3/2;
- exact imaginary projection is -5/2;
- zero has one exact value with no signed-zero component;
- bare complex defaults to `complex128` in `println`;
- explicit `complex64` resolves to `TComplex C64`;
- explicit `complex128` resolves to `TComplex C128`;
- C64 and C128 are distinct static types.

43. Component representability boundaries

Kernel-check:

- both F32-representable components -> complex64 accepts;
- real F32 overflow -> complex64 rejects;
- imaginary F32 overflow -> complex64 rejects;
- F64 overflow in either component -> complex128/defaulting rejects;
- negative underflow in either component produces exact zero + stored positive zero;
- no typed complex constant component is NaN, infinity, or negative zero.

44. Scalar-to-complex conversions

Accept and pin:

- `complex64(1)`;
- `complex128(1)`;
- `complex64(1.5)`;
- `complex128(1.5)`;
- typed float32 -> complex64 reuses the real component;
- typed float64 -> complex128 reuses the real component;
- imaginary component is stored positive zero.

Reject:

- `complex64(true)`;
- `complex128("x")`.

45. Complex-to-scalar constant conversions

Accept and pin:

- `int(complex(3.0, 0.0))` -> 3;
- `int8(complex(127.0, 0.0))` -> 127;
- `float32(complex(1.5, 0.0))`;
- `float64(complex(1.5, 0.0))`;
- typed complex64 zero-imag -> float32 projects its existing real typed float;
- typed complex128 zero-imag -> float64 projects its existing real typed float.

Reject:

- `int(complex(3.5, 0.0))`;
- `int(complex(3.0, 1.0))`;
- `int8(complex(128.0, 0.0))`;
- `float32(complex(1.5, 1.0))`;
- `float64(complex(1.5, -1.0))`.

46. Same-type complex identity

Universal theorem:

  convert_const (TComplex ct)
    (CITyped (TComplex ct) tc)
  = Some tc

for every `ct` and `tc`.

Concrete fixtures:

  complex64(complex64(complex(...)))
  complex128(complex128(complex(...)))

must retain the same intrinsic typed constant and stored runtime component objects.

47. Different-type component rerounding

Use the historical float scar value:

  2305843146652647425

Construct an exact complex constant with that value in at least the real component.

Prove:

- direct complex64 rounds that component directly at F32;
- explicit complex128 then complex64 rounds once at F64 and then once at F32;
- the resulting `TypedComplexConst C64` exact values differ;
- the stored runtime components differ accordingly;
- no additional hidden round occurs during evaluation.

Also prove component independence with the scar in the imaginary component, even if the external witness observes only the real zero-imag case exactly.

48. Preserve general runtime-only cases

Prove:

- a `ComplexValue C128` with NaN real component is valid runtime state and denotes no constant;
- a `ComplexValue C128` with infinity imaginary component is valid runtime state and denotes no constant;
- a `ComplexValue C64` or C128 with negative-zero component is valid runtime state and denotes no typed complex constant;
- constant/defaulting/conversion construction never produces those shapes.

PART L — compiler integration

49. Whole-program compiler responsibility is unchanged

`GoCompile` still consumes `ProgramTyped` over the same raw `GoProgram`.

No typed AST.

No copied file map.

No new broad error taxonomy.

Complex failures are ordinary `ErrTyping` cases:

- component overflow;
- wrong-type source;
- nonzero-imaginary scalar conversion;
- fractional/out-of-range scalar conversion;
- invalid nested conversion.

50. Add explicit compiler surfaces

Add a concrete accepted complex program containing:

- bare complex default;
- complex64 conversion;
- complex128 conversion;
- scalar-to-complex conversion;
- zero-imaginary complex-to-scalar conversion.

Prove it compiles.

Add concrete rejected programs for at least:

- complex64 component overflow;
- nonzero-imaginary complex-to-int conversion.

Prove:

- `go_compile` returns `Err ErrTyping`;
- no `CompilableProgram` exists.

PART M — generated witness and external Go adequacy

51. Grow the canonical witness readably

Add a small readable complex section to the canonical witness.

Suggested forms:

  println(complex(15.0e-1, -25.0e-1))
  println(complex64(complex(15.0e-1, -25.0e-1)))
  println(complex128(complex(15.0e-1, -25.0e-1)))
  println(int(complex(3.0e+0, 0.0)))
  println(float32(complex(15.0e-1, 0.0)))

Use the actual AST constructors and certified renderer.

Do not hand-edit generated Go.

52. Add an exact double-round observation

Use a separate complex witness if needed for readability.

Observe the real-component scar through a legal zero-imaginary scalar conversion:

  uint64(complex64(complex(2305843146652647425.0e+0, 0.0)))

versus:

  uint64(complex64(complex128(complex(2305843146652647425.0e+0, 0.0))))

Expected exact decimal observations under pinned Go 1.23:

  2305843284091600896
  2305843009213693952

This is integration evidence for the formal direct-versus-nested component theorem.

53. Real-Go acceptance fixtures

Under pinned Go 1.23, require acceptance of canonical generated forms covering:

- bare `complex(real, imag)` constant;
- complex64 conversion;
- complex128 conversion;
- integer -> complex64/complex128;
- float -> complex64/complex128;
- zero-imaginary complex -> integer;
- zero-imaginary complex -> float;
- same-type nested complex conversion;
- direct and nested double-round scar.

A Go rejection of any Fido-accepted rendered program is a blocking model bug.

54. Real-Go rejection fixtures

Add temporary handwritten fixtures proving pinned Go rejects what Fido makes impossible:

- `complex64(complex(1e39, 0))`;
- `complex64(complex(0, 1e39))`;
- `complex128(complex(1e309, 0))`;
- `int(complex(3.5, 0))`;
- `int(complex(3, 1))`;
- `float32(complex(1.5, 1))`;
- `complex64(true)`;
- `complex128("x")`.

No imports are required.

Do not compare binary output through shell command substitution.

55. Generated artifact workflow

After root review is GREEN and final integration is complete:

- build the pristine generated-module layer;
- run `make regenerate`;
- update tracked generated `.go` through the same sink;
- keep root `go.mod` unchanged unless there is a genuine module-spec reason;
- verify exact generated path set and bytes;
- require gofmt-clean output;
- require `go build ./...`;
- run the witness and reviewed goldens;
- keep `go vet` diagnostic-only.

The generated source is expected to change in this feature milestone.

PART N — public proof and assumption surfaces

56. `Complexes.v` public surfaces

Gate load-bearing representatives for:

- `ComplexType` equality;
- exact keywords;
- component mapping C64->F32 and C128->F64;
- `ComplexConst` equality;
- decimal-complex exact value projections;
- `round_typed_complex` component results;
- representability reflection;
- real-overflow rejection;
- imaginary-overflow rejection;
- underflow-to-positive-zero coherence;
- typed complex runtime component shape;
- typed complex runtime no NaN/Inf/-0;
- direct-versus-nested scar difference.

57. `GoTypes` public surfaces

Gate representatives for:

- `TComplex` identity;
- `TCComplex` exact-value erasure;
- default complex128;
- complex64/complex128 resolution;
- same-type complex identity;
- typed float -> matching complex component reuse;
- typed complex -> matching float component projection;
- integer/float -> complex conversions;
- zero-imaginary complex -> integer/float conversions;
- nonzero-imaginary rejection;
- component overflow rejection;
- direct/nested scar preservation;
- statement/program typing reflection unchanged.

58. `GoSafe` public surfaces

Gate representatives for:

- `typed_const_to_value` complex type preservation;
- complex `ValueWF`;
- complex runtime denotes exact typed complex constant;
- NaN/Inf/-0 component runtime values denote no constant;
- evaluation returns exactly the stored `typed_complex_runtime`;
- generic resolved evaluation theorem remains closed.

59. `GoRender` public surfaces

Gate representatives for:

- exact complex keyword rendering;
- canonical complex literal rendering;
- complex literal ASCII;
- complex decoder/render semantic round trip;
- complex conversion rendering;
- rendering preserves complex `ConstInfo`;
- denotation remains functional;
- final raw/status/resolved/runtime/type theorem includes complex.

60. `GoCompile` public surfaces

Gate representatives for:

- existing soundness/completeness unchanged;
- accepted complex program compiles;
- overflow complex program rejects;
- nonzero-imaginary scalar-conversion program rejects;
- rejection implies no compile certificate;
- empty program remains accepted.

61. Whole-theory audit

The whole-certified-theory assumption audit must automatically include `Complexes.v`.

No:

- `Axiom`;
- `Admitted`;
- `Parameter`;
- unchecked primitive float;
- source-text axiom scanner;
- tracked axiom-bearing fixture.

PART O — documentation

62. Reconcile active architecture documentation

Update:

- `.review/NEXT_STEPS.md` only by installing this contract verbatim;
- `ARCHITECTURE.md`;
- `CLAUDE.md`;
- `README.md`;
- `PROGRESS.md`;
- relevant module headers;
- `gate/axiom_gate.v` comments;
- Docker/e2e comments.

Required truths:

- complex64 and complex128 are live static types;
- complex64 components are float32;
- complex128 components are float64;
- untyped complex constants are exact pairs of rational components;
- default type is complex128;
- typed complex constants are pairs of existing coherent typed float constants;
- general runtime complex values may contain signed zero, infinity, and NaN;
- typed complex constants cannot;
- scalar/complex constant representability follows Go’s zero-imaginary rule;
- complex rendering uses a dedicated canonical `complex(real, imag)` form;
- no `real`, `imag`, arithmetic, comparison, or general calls exist yet;
- the next Static Type Universe phase remains uintptr/aliases unless review chooses otherwise.

Keep `PROGRESS.md` compact.

Do not turn `PAINFUL_LESSONS.md` into a feature diary.

Add at most one concise durable lesson if the implementation actually exposes a new recurring trap:

> A compound typed constant should be composed from already-coherent typed component constants; do not duplicate their validity or runtime-denotation proofs at the aggregate layer.

Do not add that lesson merely to satisfy a checklist if it adds no future value.

PART P — forbidden resurrection and feature creep

63. Do not restore rejected historical architecture

Forbidden:

- old `GoComplex128` extraction wrapper;
- plugin recognition by global basename;
- suppressed record constructors/projections;
- `GoTypeTag`;
- a parallel runtime complex type universe;
- `PrimFloat`;
- host complex arithmetic;
- handwritten OCaml complex lowering;
- a typed AST;
- a copied resolved expression;
- old `ptype`/`PTy` compiler authority;
- a separate complex representability authority duplicating float rounding.

64. Do not add operations

Do not add:

- `real`;
- `imag`;
- `complex` as a general builtin call node;
- complex addition/subtraction/multiplication/division;
- equality/inequality;
- unary negation;
- runtime arithmetic forcing machinery.

The historical operation commits remain future references only.

65. Do not fake future runtime semantics

Do not introduce:

- runtime variables;
- closures;
- heap objects;
- interfaces;
- arbitrary calls;
- fake operational state

merely to demonstrate complex values.

The current abstract `println` trace is sufficient.

PART Q — acceptance criteria

Workflow

- old loop stopped;
- this directive copied verbatim to `.review/NEXT_STEPS.md`;
- contract committed before implementation;
- exact `/loop 5m ...` command started;
- semantic-root commit uses `milestone(root):`;
- root-review fixes use `review(root):`;
- final candidate uses `milestone(final):`;
- final-review fixes use `review(final):`;
- implementation and review repairs are not squashed;
- no intentional stops outside root and final barriers;
- Codex reviewed under the permanent policy;
- GREEN reached;
- notification sent;
- loop stopped.

Cleanup

- no “bijection” overclaim;
- GoTypes header includes floats and complex;
- no stale `const_value` gate prose;
- no duplicate float representability gate entry.

Complex root

- exactly C64/C128;
- component type single-sourced;
- exact `ComplexConst` pair;
- intrinsic `DecimalComplex` raw domain;
- general `ComplexValue` pair;
- intrinsic `TypedComplexConst` pair of `TypedFloatConst`s;
- one `round_typed_complex` authority;
- representability derived from typed construction;
- no duplicated float coherence.

One type/constant/runtime authority

- `TComplex` added once;
- `CComplex` added once;
- `TCComplex` added once;
- `VComplex` added once;
- `ConstInfo` and `ResolvedConst` remain generic;
- no parallel tag or typed AST.

Conversion/defaulting

- scalar -> complex exact rules;
- complex -> scalar zero-imaginary rules;
- componentwise destination rounding;
- same-type complex conversion exact identity;
- matching typed float component reuse;
- matching typed complex real-component projection;
- different-type conversion rounds once per component at the explicit boundary;
- default complex128;
- wrong-type, overflow, fractional, and nonzero-imaginary cases reject.

Runtime coherence

- typed complex runtime is stored component runtime;
- evaluation projects it exactly;
- typed components finite/+0 only;
- general runtime complex values may contain -0/Inf/NaN;
- those runtime-only values denote no constant;
- no runtime-to-constant fallback.

Rendering

- canonical `complex(real, imag)` literal;
- canonical complex64/complex128 conversions;
- independent decoder;
- semantic round trip;
- all ASCII;
- one `RenderedConstInfoDenotes`;
- functional by spelling;
- final theorem ties syntax/status/typed constant/stored runtime/exact value/type.

Compiler/e2e

- accepted complex program compiles;
- rejected complex programs have no certificate;
- direct/nested component scar pinned;
- pinned Go accepts every Fido-accepted canonical form;
- pinned Go rejects every modeled-invalid fixture;
- generated module regenerated through the certified pipeline;
- gofmt-clean;
- `go build ./...` green;
- runtime goldens green;
- existing bool/int/float/string behavior remains green;
- empty and multi-package cases remain green;
- `go vet` remains nonblocking.

Proof

- public surfaces closed;
- whole-theory audit green;
- no axioms/admitted/parameters;
- no primitive-float trust regression;
- no source-text proof gate.

PART R — completion report

66. Completion report

When complete, report:

- contract commit SHA;
- semantic-root commit SHA;
- every `review(root):` commit SHA and finding;
- final-candidate commit SHA;
- every `review(final):` commit SHA and finding;
- final tip SHA;
- complete commit range;
- timestamps for root candidate, root repairs, final candidate, and final repairs;
- whether the semantic-root review prevented meaningful downstream rework;
- historical commits/files inspected;
- transplant ledger;
- four residue cleanups;
- final `ComplexType`;
- final component mapping;
- final `ComplexConst`;
- final raw `DecimalComplex` and AST constructors;
- final `ComplexValue`;
- final `TypedComplexConst`;
- exact `round_typed_complex` algorithm;
- proof each component rounds exactly once;
- same-type complex identity theorem;
- matching float-component reuse/projection rules;
- scalar/complex representability rules;
- default complex128 rule;
- runtime-only NaN/Inf/-0 examples;
- canonical source spelling;
- decoder grammar and round-trip theorem;
- direct/nested scar exact values;
- every theorem added or materially changed;
- complete `Print Assumptions` results;
- whole-theory audit result;
- real-Go acceptance/rejection fixtures;
- generated source diff;
- runtime golden evidence;
- `make prove`, `make e2e`, `make check`, and pre-commit results;
- Codex final result and nonblocking observations;
- confirmation notification sent;
- confirmation loop stopped.

Do not list a retained correctness flaw as a known limitation.

If a real obstacle requires changing this contract:

- classify it as an ARCHITECTURAL CONFLICT;
- notify the user;
- stop the loop;
- wait.

67. Hard stop

When Codex is GREEN and final verification passes:

1. Commit the completed checkpoint.
2. Notify the user through the configured completion-notification channel.
3. Stop the `/loop`.
4. Do not begin uintptr, aliases, structural types, or complex operations.
5. Wait for review.

Bottom line

This milestone produces:

  DecimalComplex
    -> exact untyped ComplexConst
    -> component-derived round_typed_complex
    -> intrinsic TypedComplexConst C64/C128
         composed from existing TypedFloatConst components
    -> ResolvedConst
    -> exact stored ComplexValue
    -> canonical complex(real, imag) source
    -> one renderer denotation root
    -> whole-program compiler acceptance
    -> pinned-Go differential alarms

No arithmetic.

No `real` or `imag`.

No general call node.

No second AST.

No duplicated float coherence.

Complex values become part of the type universe without skipping ahead to their operations.
