Claude Code milestone: open the Static Type Universe Arc, repair integer constant denotation, and add exact float32/float64 constants

THIS FILE IS THE BINDING MILESTONE CONTRACT.

Before implementation

1. Stop any currently running `/loop`.

2. Replace the tracked repository file:

   .review/NEXT_STEPS.md

   with this directive VERBATIM.

   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not “improve” the selected architecture while copying it.

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
- not keep running because a future type, operation, or hostile scenario could be added;
- after GREEN, run final verification, commit the completed checkpoint, notify the user, stop the loop, and wait.

Milestone purpose

This milestone opens a longer architectural campaign:

  STATIC TYPE UNIVERSE ARC

The campaign’s goal is:

> Complete and accurate static representation of Fido’s non-generic, no-import Go 1.23 type universe before building the operational foundations that consume those types.

The long-term campaign includes, in reviewed phases:

1. integer types and constant conversions;
2. float32/float64;
3. complex64/complex128;
4. remaining predeclared scalar identities and aliases, including uintptr, byte = uint8, and rune = int32;
5. unnamed structural types:
   - arrays;
   - slices;
   - structs;
   - pointers;
   - function signatures;
   - maps;
   - channels;
6. type aliases and defined named types;
7. type-name resolution, identity, underlying types, and valid recursive definitions;
8. method signatures and method sets as type-level facts;
9. non-generic value interfaces.

Operations come after the type roots they consume.

This milestone implements only:

A. the surgical integer-render-denotation repair identified by review;
B. the first new phase of the arc: exact float32/float64 constants, conversions, values, typing, rendering, and external adequacy.

Do not implement later phases in this loop.

Scope

The operational target remains:

- Go language version 1.23;
- linux/amd64;
- 64-bit `int`, `uint`, and eventually `uintptr`;
- no imports;
- no generics;
- no workspaces;
- no ambient packages.

The static language remains tiny:

- `func main`;
- builtin `println`;
- primitive constant expressions already represented;
- integer conversions;
- new float constants and float conversions.

No arithmetic operators are added.

No variables, assignments, functions, calls, control flow, field access, indexing, sends, receives, pointers, slices, maps, channels, structs, interfaces, or type declarations are added in this milestone.

Standing law

Ruthless correctness or ruthless deletion.

History is a technical quarry.

The current architecture is the authority.

The AST is the IR.

There is:

- one raw AST per `.go` file;
- one `GoProgram`;
- one static type authority;
- one exact constant-value authority;
- one runtime-value type authority derived from the same static types;
- no typed AST;
- no copied compiled program;
- no target AST;
- no text IR;
- no separate lowering tree;
- no parser authority;
- no handwritten OCaml language semantics;
- no name-based OCaml lowering;
- no extraction-driven semantic wrapper tricks.

PART A — repair integer constant denotation at the source

1. Delete the false “bare integer denotes typed int” premise

The current renderer relation labels every bare rendered integer constant as `IInt`, including a bare constant that is not representable as `int` but is valid inside an explicit conversion such as:

  uint64(9223372036854775808)

That semantic story is wrong.

The inner bare integer remains an untyped integer constant.

The outer explicit conversion directly assigns `uint64` after checking the exact value’s representability.

Do not patch this with an extra representability premise on the bare integer constructor. That would reject valid conversions.

Do not special-case `uint64`.

Correct the status model.

2. Reuse `ConstInfo` as the one render-time constant-status authority

Do not create:

- `IntegerConstStatus`;
- `FloatConstStatus`;
- a second parallel typed/untyped status universe;
- one denotation relation per numeric family that can drift.

The live type layer already owns the exact distinction:

  UntypedConst : GoConst -> ConstInfo
  TypedConst   : GoType -> GoConst -> ConstInfo

Make renderer denotation speak in that same vocabulary.

Preferred root:

  RenderedConstInfoDenotes : string -> ConstInfo -> Prop

Equivalent naming is acceptable.

It must represent at least:

- bare bool -> `UntypedConst (CBool b)`;
- bare integer -> `UntypedConst (CInt z)`;
- bare string -> `UntypedConst (CString bytes)`;
- integer conversion -> `TypedConst (TInteger target) (CInt z)`;
- later in this milestone, bare float -> `UntypedConst (CFloat q)`;
- float conversion -> `TypedConst (TFloat target) (CFloat rounded_q)`.

The relation must reuse the same conversion functions and exact values as `GoTypes`.

It must not independently reimplement representability or rounding.

3. Prove rendering preserves `const_info`

Add a theorem of the form:

  const_info e = Some ci ->
  RenderedConstInfoDenotes (render_expr e) ci

or an equivalent exact statement.

This becomes the source-spelling/constant-status root.

Then retain a final resolved theorem tying together:

- `ResolveExpr`;
- `eval_expr`;
- runtime `GoValue`;
- resolved `GoType`;
- `ValueWF`;
- rendered denotation.

Delete or demote `RenderedIntegerDenotes` if it remains a competing authority.

A convenience theorem may project integer facts from the generic relation, but it must not own another status model.

4. Required integer repair regressions

Kernel-check at least:

- rendered bare `9223372036854775808` denotes:
  `UntypedConst (CInt 9223372036854775808)`;
- it does not denote:
  `TypedConst (TInteger IInt) (CInt 9223372036854775808)`;
- rendered `uint64(9223372036854775808)` denotes:
  `TypedConst (TInteger IUint64) (CInt 9223372036854775808)`;
- rendered `uint64(18446744073709551615)` has final typed `IUint64` status and exact value;
- defaulting a bare value above `int_max` still fails in `println`;
- the same exact bare value succeeds inside `uint64(...)`.

Keep all existing generated bytes and integer e2e behavior unchanged for this repair.

PART B — historical float quarry

5. Read the mature historical float work before designing

Primary mature snapshot:

  7f4da96e72168d425d3e06c467448bd2a9979cc5

Read at least:

  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoNumeric.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoTypes.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoAst.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoRuntimeTypes.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoCompile.v

Read the Great Culling rationale:

  git show 33c8df0f2273adae8eed15ec0e45a7b000fb7235

The float mathematics was not disproved.

The old compiler authority, parallel runtime type universe, extraction architecture, and disconnected runtime island were rejected.

6. Read the focused float commits

Read the commit messages and diffs for:

  d76829aca5476cbb48210cadc4226ee086caa3e6

The original identification of the untyped-float-constant problem:
exact arbitrary-precision constants differ from runtime IEEE values.

  20f3a6172fc763aa618f38f2dc9894a7fded4de8

Exact-rational floating constants and the distinction between exact constant arithmetic and runtime per-step rounding.

  e6abddc1b69da54ab22f8255556b724be133dbc8

Exact rational constant division.

Arithmetic itself remains deferred, but the exact-rational representation and examples are relevant.

  16269a397486669d04ae42ba7f72436f7f5928cc

Direct exact-rational-to-binary32 rounding.

This contains the critical double-rounding counterexample and the rule that direct float32 conversion must not pass through float64.

  bcf066adac66bcb0c0e8129425886dae044bdcf8

Direct exact-rational-to-binary64 rounding and the corresponding double-rounding correction.

  445aca38ef5a043f69e088be27a21713e822381f

The axiom-free migration from primitive floats/integers to `SpecFloat.spec_float` and computable `Z` arithmetic.

  48aa47bdd03cf87ac63ce3e9e13687e888e8bed9

The historical discovery that `SpecFloat` already supplies precision-parameterized binary32 behavior.

Do not restore its arithmetic in this milestone.

  c72b62dd501bd116466cd57fd56bc463f5be4f87

Constant zero versus runtime signed zero.

Constant values never carry negative zero, NaN, or infinity.

Runtime float values may eventually carry all IEEE cases.

Useful history searches:

  git log -S 'FConst' --all
  git log -S 'f32_of_fconst' --all
  git log -S 'f64_of_fconst' --all
  git log -S 'sf_of_Z' --all
  git log -S 'binary_normalize' --all
  git log -S 'signed zero' --all
  git log -S 'double-round' --all

7. Required transplant ledger

Before implementation, write a concise transplant ledger in the opening implementation commit message or a temporary review note.

It must classify at least:

| Historical item | Current destination | Disposition |
|---|---|---|
| exact rational `FConst` concept | new exact `FloatConst` | retain/generalize |
| `sf_of_Z` | direct rational-to-SpecFloat rounding root | retain mathematics |
| direct `SFdiv 24 128` | float32 conversion | retain |
| direct `SFdiv 53 1024` | float64 conversion | retain |
| `renorm` / canonical SpecFloat concept | runtime `FloatValue` invariant | retain/generalize |
| constant/runtime signed-zero split | GoTypes/GoSafe | retain |
| double-rounding witnesses | kernel + real-Go fixtures | retain |
| `PrimFloat`, `Prim2SF`, `SF2Prim` | none | reject |
| old `GoFloat32` extraction wrapper shape | none | replace shape, retain invariant |
| `ptype` / `PTy` | none | reject |
| `GoTypeTag` | none | reject |
| plugin name-recognition/lowering | none | reject |
| old float arithmetic | future operational milestone | defer |
| complex arithmetic | future | defer |

Do not copy whole historical files.

PART C — one float type authority

8. Add `FloatType`

Create a certified low-level module, preferably:

  Floats.v

Define exactly:

  Inductive FloatType :=
  | F32
  | F64.

Provide one authority for:

- decidable equality;
- keyword:
  - F32 -> `"float32"`;
  - F64 -> `"float64"`;
- precision:
  - F32 -> 24;
  - F64 -> 53;
- exponent bound:
  - F32 -> 128;
  - F64 -> 1024.

Names may differ.

The semantics must derive from the one descriptor.

Do not add:

- complex types;
- float operations;
- target configuration;
- a second runtime float-type tag.

9. Extend the one `GoType`

Extend:

  GoType

with:

  TFloat : FloatType -> GoType

The complete live universe after this milestone is:

- `TBool`;
- `TInteger IntegerType`;
- `TFloat FloatType`;
- `TString`.

No placeholder composite type constructors.

No `TUnknown`, `TRaw`, or `TOpaque`.

PART D — exact untyped floating constants

10. Add one exact rational `FloatConst`

Add one exact, canonical, axiom-free rational value type for floating constants.

Preferred semantic shape:

  numerator   : Z
  denominator : positive

with:

- positive denominator;
- canonical reduction;
- canonical zero;
- decidable equality by canonical representation.

Using a standard-library canonical rational is acceptable only if:

- reduction is computational and transparent enough for the required proofs;
- no axiom enters the assumption closure;
- equality and rendering proofs remain tractable.

Do not use:

- `float`;
- `spec_float`;
- a decimal source string;
- a rounded float32/float64 value

as the semantic untyped constant.

`FloatConst` is exact mathematics.

11. Add an intrinsic finite-decimal literal value

The raw source constructor must carry semantic value, not arbitrary source spelling.

Add a small intrinsic finite-decimal domain, for example:

  coefficient : Z
  exponent10  : Z

with semantic value:

  coefficient * 10^exponent10

and canonicality such as:

- zero has one representation;
- a nonzero coefficient has no removable factor of ten;
- any declared magnitude/exponent bounds are intrinsic.

Equivalent finite-decimal representation is acceptable.

Call it, for example:

  DecimalFloat
  FloatLiteralValue
  DecimalConst

Do not use raw source text.

Do not preserve:

- underscore placement;
- decimal versus hexadecimal spelling;
- capitalization;
- leading-zero choices;
- negative zero spelling.

One semantic value has one canonical Fido spelling.

12. Bound the raw literal domain honestly

Fido’s `GoCompile` aims to agree with the pinned Go toolchain for every representable program.

The Go specification permits compiler implementation limits for arbitrary-precision floating constants.

Do not silently make every mathematical coefficient/exponent pair representable if the pinned Go compiler may refuse its source spelling for implementation-limit reasons.

Before finalizing the intrinsic literal domain:

- run focused experiments against pinned Go 1.23;
- choose a deliberately bounded coefficient/exponent domain that the pinned toolchain accepts reliably;
- state the exact bounds;
- carry them intrinsically;
- add boundary fixtures.

A smaller proven domain is acceptable.

A representable value that the pinned compiler rejects is not.

The internal `FloatConst` mathematics may be wider than the raw literal domain.

13. Extend `GoConst`

Extend:

  GoConst

with:

  CFloat : FloatConst -> GoConst

Then:

- a raw decimal float expression denotes `UntypedConst (CFloat exact_q)`;
- there is no rounding in raw constant interpretation;
- the exact value has no signed zero, NaN, or infinity.

Prove zero-sign agnosticism at the exact constant layer.

PART E — raw float syntax

14. Grow the raw AST minimally

Add exactly:

  EFloat : DecimalFloat -> GoExpr
  EFloatConvert : FloatType -> GoExpr -> GoExpr

Names may differ.

`EFloat` carries semantic finite-decimal value.

`EFloatConvert` is explicit Go conversion syntax.

Do not add:

- float arithmetic;
- a general conversion target;
- a raw type-expression universe prematurely;
- imaginary literals;
- complex literals;
- NaN/Inf constructors;
- runtime float variables;
- unary arithmetic operators beyond what the literal representation itself needs.

Keep `EIntConvert`.

A future raw type-expression milestone may consolidate conversion syntax when named and composite type expressions exist.

Do not conflate resolved `GoType` with future unresolved raw type syntax now.

PART F — direct single-round conversion semantics

15. Rebuild the historical direct rounding root

Use `SpecFloat.spec_float`, not primitive float operations.

Define an exact integer-to-SpecFloat embedding equivalent in responsibility to historical:

  sf_of_Z : Z -> spec_float

Define target-directed direct rounding of exact rational constants:

  round_float_sf : FloatType -> FloatConst -> spec_float

Conceptually:

  SFdiv precision emax
    (sf_of_Z numerator)
    (sf_of_Z denominator)

The denominator is nonzero by construction.

The conversion to F32 must directly use binary32 precision.

It must not:

- convert through F64;
- first round numerator and denominator independently to F64;
- use host OCaml floats;
- use primitive Rocq floats.

16. Convert the rounded SpecFloat back to exact constant meaning

Typed constants remain constants.

They carry an exact mathematical value after target rounding.

Define an exact denotation of a rounded finite/zero `spec_float` back into `FloatConst`:

- `S754_zero _` -> exact rational zero;
- `S754_finite sign mantissa exponent` -> exact dyadic rational;
- infinity -> not representable;
- NaN -> not representable.

Define:

  round_float_const : FloatType -> FloatConst -> option FloatConst

or an equivalent function.

It must:

1. round the exact source rational once at the destination precision;
2. reject overflow that produces infinity;
3. accept underflow that rounds to zero;
4. simplify any negative zero result to exact unsigned zero;
5. never produce NaN for a valid rational denominator.

17. One float representability authority

Define:

  FloatConstRepresentable : FloatType -> FloatConst -> Prop

and a reflected executable decision.

Exact intended rule:

- representable iff direct destination rounding succeeds without overflow;
- underflow to zero is representable;
- constant negative zero is simplified to zero;
- no constant NaN or infinity.

Prove exact reflection.

Do not create another float-overflow checker in `GoCompile` or `GoRender`.

PART G — target-directed constant conversion

18. Create one constant-conversion authority

Do not duplicate conversion semantics between:

- `EIntConvert`;
- `EFloatConvert`;
- typing;
- evaluation;
- rendering.

Introduce one target-directed exact conversion authority, conceptually:

  convert_const : GoType -> GoConst -> option GoConst

It may be split into small typed helpers, but there must be one semantic root.

Current rules:

A. Integer target from integer constant

- exact current behavior;
- destination representability required;
- result is exact `CInt z`.

B. Integer target from floating constant

- the exact rational must be an integer value;
- its exact integer must be representable by the destination integer type;
- result is exact `CInt z`;
- fractional constants reject;
- no runtime truncation rule applies to constants.

Examples:

  int(3.0)       accepts as typed integer constant 3
  int(3.5)       rejects
  int8(127.0)    accepts
  int8(128.0)    rejects
  uint8(-1.0)    rejects

C. Float target from integer constant

- embed exact integer as exact rational;
- round directly once to destination;
- reject overflow;
- result carries the exact rounded `CFloat`.

D. Float target from floating constant

- round exact current constant value directly to destination;
- a nested explicit conversion rounds at each explicit boundary;
- result carries the exact rounded `CFloat`.

E. bool/string sources to numeric targets

- reject.

19. Preserve constantness transitively

A conversion of a constant is a typed constant.

Never turn it into a runtime category.

Required nested behavior:

- `float32(float64(q))` rounds first to F64, then rounds that exact typed constant value to F32;
- direct `float32(q)` rounds once directly to F32;
- the two may differ;
- `int(float32(q))` sees the rounded float32 constant value;
- an invalid inner conversion cannot be revived by an outer conversion.

This is the float analogue of the historical `PtTIntConst` lesson.

PART H — type resolution and compilation

20. Default types

Extend:

  const_default_type

with:

  CFloat _ -> TFloat F64

Bare floating constants default to float64 only in a context requiring a typed value.

They remain untyped before that point.

21. Representability and `ResolveExpr`

Extend the one `ConstRepresentable` authority:

- `CFloat q` is representable as `TFloat ft` according to `round_float_const`;
- an integer constant may be representable as a float target through the conversion authority only when explicit conversion syntax supplies that target;
- cross-family wrong types reject;
- typed float constants retain their exact explicit type.

Update:

- `const_representableb`;
- reflection;
- `const_info`;
- `resolve_expr`;
- `ResolveExpr`;
- statement/file/program typing;
- soundness;
- completeness;
- determinism.

A bare float in `println` defaults to F64.

An explicit F32 conversion resolves to F32.

22. Whole-program compiler

`GoCompile` continues to consume the same `ProgramTyped` evidence.

No typed AST.

No copied program.

Float failures are static constant failures:

- raw default-F64 overflow;
- explicit F32/F64 overflow;
- invalid constant conversion operand;
- fractional float constant converted to integer;
- out-of-range float-to-integer constant conversion.

Use a small exact error representation.

Do not invent a general future type-error taxonomy.

The whole program remains all-or-nothing.

PART I — runtime float values without a second type universe

23. Add canonical runtime `FloatValue`

Runtime float values use `SpecFloat.spec_float`.

They must be tied to one `FloatType`.

Define a proof-carrying canonical runtime value, conceptually:

  FloatValue : FloatType -> Type

The invariant must ensure a value is in the canonical representation for its format.

It must be future-compatible with:

- finite values;
- positive and negative zero;
- infinity;
- NaN.

Do not use an invariant that only permits values originating from constants.

A suitable invariant may be:

- being in the image of a format normalizer;
- being a fixed point of a proved format normalizer;
- another exact canonical-format predicate.

The historical `renorm`/`binary_normalize` work is the reference.

Use proof fields for semantic validity, not to manipulate extraction.

24. Extend `GoValue`

Extend:

  GoValue

with an integer-family-parallel float constructor, conceptually:

  VFloat : forall ft, FloatValue ft -> GoValue

Then:

  value_type (VFloat ft _) = TFloat ft

There is still one `GoType`.

No `GoTypeTag`.

No raw untyped `spec_float` value may cross the public runtime value API.

25. Evaluate constants exactly

Evaluation remains derived from the one `ConstInfo`/conversion authority.

Required behavior:

- bare float defaults to F64 and rounds once;
- explicit F32/F64 returns that typed rounded value;
- nested conversions respect each explicit boundary;
- constant underflow produces positive zero;
- no constant evaluation produces negative zero, infinity, or NaN;
- `ValueWF` holds;
- resolved type equals runtime type.

Prove the generic resolved-expression type-preservation theorem still holds.

PART J — canonical source rendering

26. One canonical decimal spelling

Render `EFloat` through one canonical ASCII decimal floating-constant spelling.

A deliberately simple canonical form is preferred.

For a normalized `(coefficient, exponent10)` representation, an acceptable policy is:

- zero -> `0.0`;
- nonzero -> `<signed-coefficient>.0e<explicit-signed-exponent>`.

Examples:

  15 * 10^-1 -> `15.0e-1`
  25 * 10^-2, normalized to 25 * 10^-2 -> `25.0e-2`
  1 * 10^6 -> `1.0e+6`
  zero -> `0.0`

Equivalent canonical scientific notation is acceptable if it has:

- one spelling per intrinsic literal value;
- no locale dependence;
- no raw source payload;
- all ASCII;
- simple independent decoding;
- gofmt stability.

Do not emit host-formatted floats.

Do not use OCaml/Python floating conversion.

27. Independent canonical float decoder

Add a small certified decoder for exactly the canonical Fido decimal float subset.

It is not a general Go parser.

It must recover the exact untyped `FloatConst` meaning.

It may accept a harmless superset, but document the theorem honestly:

  decode(render(value)) = exact semantic value

Do not claim:

  render(decode(source)) = original source

for equivalent alternative spellings.

Prove:

- decoder/renderer semantic round trip;
- exact coefficient/exponent meaning;
- all output ASCII;
- no locale dependence;
- no accidental integer-token spelling;
- no raw NaN or Inf spelling.

28. Render explicit conversions directly

Render:

  EFloatConvert F32 e -> `float32(<render e>)`
  EFloatConvert F64 e -> `float64(<render e>)`

Keep integer conversion rendering.

No name-based OCaml lowering.

No formatter rewrite.

29. Generic rendered-constant denotation

Extend the Part A `RenderedConstInfoDenotes` root.

The rendering theorem must establish the exact `ConstInfo` produced by `GoTypes`.

For float conversions, the relation must use the same `round_float_const` authority.

Required source-level examples:

- bare `1.0e-1` denotes an untyped exact rational 1/10;
- `float32(1.0e-1)` denotes a typed F32 constant with the exact rounded dyadic value;
- `float64(-1.0e-1000)` denotes typed F64 exact zero;
- no intermediate F64 status appears in direct F32 conversion.

Then extend the final render/value/type theorem.

PART K — historical scars as mandatory fixtures

30. Direct binary32 rounding, not float64-mediated rounding

Restore the historical counterexample from:

  16269a397486669d04ae42ba7f72436f7f5928cc

Use the exact historical input:

  2305843146652647425

Prove and externally demonstrate:

- direct `float32(2305843146652647425)` rounds at F32 directly;
- explicit nested `float32(float64(2305843146652647425))` follows two explicit rounding boundaries;
- the results differ exactly as the historical commit established.

Do not merely assert “no double rounding.”

Pin both values.

31. Precision boundaries

Kernel fixtures:

- `float32(16777217)` rounds to 16777216;
- `float64(9007199254740993)` rounds to 9007199254740992;
- exact representable powers and small decimals remain exact where expected;
- direct F32/F64 conversions are deterministic.

32. Underflow and overflow

Add exact fixtures:

- a tiny negative constant representable as F64 by rounding to unsigned zero;
- a tiny constant representable as F32 by rounding to zero;
- an F32-overflowing constant rejects;
- an F64-overflowing constant rejects;
- underflow is not mislabeled as overflow.

The raw literal intrinsic bounds must still permit these reviewed fixtures.

33. Signed zero

Prove:

- exact `FloatConst` has one zero;
- negating the source spelling of zero, if representable through the intrinsic literal value, denotes the same exact zero;
- constant conversion to F32/F64 yields positive zero;
- no constant produces negative zero;
- runtime `FloatValue` remains capable of representing negative zero for future runtime operations.

34. Float-to-integer constants

Kernel fixtures:

- `int(3.0)` accepted;
- `int(3.5)` rejected;
- `int8(127.0)` accepted;
- `int8(128.0)` rejected;
- `uint8(-1.0)` rejected;
- `int(float32(16777217))` observes the rounded F32 constant value 16777216.

35. Wrong-type and nested failures

Reject:

- `float32(true)`;
- `float64("x")`;
- `int(float32(overflowing-constant))`;
- an outer conversion whose inner conversion failed;
- a float constant resolving as bool/string;
- a float32 typed constant resolving as float64 without an explicit conversion.

PART L — external Go adequacy

36. Canonical float spelling experiments

Use pinned Go 1.23 to confirm every canonical source form emitted by Fido is accepted.

Cover:

- zero;
- positive;
- negative;
- positive exponent;
- negative exponent;
- F32 conversion;
- F64 conversion;
- very small underflow case;
- reviewed boundary values.

A Go rejection is a blocking correctness failure.

37. Compile-rejection fixtures

Handwritten temporary Go fixtures must confirm pinned Go rejects:

- F32 overflow;
- F64 overflow;
- `int(3.5)`;
- `int8(128.0)`;
- `uint8(-1.0)`;
- wrong-type conversions.

Check rejection reason where practical, but acceptance status is the core contract.

38. Byte-/value-safe e2e evidence

Add a separate float witness if that keeps the canonical example readable.

The witness should include:

- bare default-F64 decimal constants;
- explicit F32;
- explicit F64;
- nested F64->F32;
- integer-to-float;
- float-to-integer exact conversion;
- underflow to zero.

For the direct-versus-nested rounding counterexample, print an exact integer observation:

  uint64(float32(big))
  uint64(float32(float64(big)))

Because those rounded constants are integer-valued, converting them back to uint64 produces exact decimal evidence without imports or binary float formatting ambiguity.

Use reviewed goldens.

Builtin `println` formatting remains integration evidence only.

Formal semantics are the exact rational, direct rounding, canonical runtime value, and rendering-denotation proofs.

PART M — proof and assumption gate

39. Public theorem surfaces

Add axiom-free public surfaces for at least:

Floats

- FloatType equality;
- exact keywords;
- precision/exponent settings;
- exact rational canonicality/equality;
- direct F32 rounding;
- direct F64 rounding;
- representability reflection;
- overflow rejection;
- underflow-to-zero acceptance;
- constant zero has no sign;
- direct-vs-nested rounding counterexample.

GoTypes

- bare float is untyped exact `CFloat`;
- default type F64;
- explicit F32/F64 produces typed constant;
- integer->float conversion;
- float->integer exact conversion;
- fractional float->integer rejection;
- nested conversion transitivity;
- resolution soundness/completeness/determinism;
- program typing reflection.

GoSafe

- canonical `FloatValue` well-formedness;
- constant evaluation produces no NaN/Inf/negative zero;
- runtime type agrees with resolved F32/F64;
- generic resolved-expression theorem remains closed.

GoRender

- generic `RenderedConstInfoDenotes`;
- repaired bare-integer untyped theorem;
- uint64-above-int rendering theorem;
- float literal decode/render semantic round trip;
- float literal ASCII;
- conversion rendering exactness;
- render preserves `const_info`;
- final render/value/type theorem.

GoCompile

- existing soundness/completeness remain;
- concrete float program compiles;
- concrete overflow/fractional conversion programs reject;
- empty program remains accepted.

The whole-certified-theory audit must include `Floats.v` automatically through Dune coverage.

No axiom, parameter, admitted proof, primitive float assumption, or source-text axiom scanner.

PART N — generated artifact

40. Grow the canonical witness carefully

The tracked generated module may change in this feature milestone.

Add a small readable float section to the canonical witness.

Keep the exact direct-vs-nested large-number evidence in a separate witness if it makes `main.go` unreadable.

Run:

  make regenerate

through the pristine generated-module layer and the same sink.

Do not hand-edit generated Go.

Verify:

- root `go.mod` unchanged unless there is a real module-spec reason;
- recursive generated path set as expected;
- generated bytes match the pristine layer;
- gofmt-clean;
- `go build ./...` green;
- runtime goldens green.

PART O — type-universe roadmap documentation

41. Record the long-term arc without implementing it

Add a concise section to `ARCHITECTURE.md` and `PROGRESS.md`:

  Static Type Universe Arc

State the reviewed order:

1. integers;
2. floats;
3. complex;
4. uintptr and aliases;
5. unnamed structural types;
6. aliases/defined named types and recursion;
7. method signatures/method sets;
8. non-generic value interfaces;
9. only then the operations consuming those roots.

Do not turn `PAINFUL_LESSONS.md` into a roadmap.

42. Clarify what “types before operations” means

The arc permits static facts such as:

- identity;
- underlying type;
- canonical rendering;
- zero-value classification;
- nilability;
- comparability;
- map-key admissibility;
- recursive validity;
- assignability;
- constant representability;
- function signatures;
- method signatures and method sets.

It does not yet require runtime models for:

- slice backing arrays;
- map heaps;
- channel queues;
- pointer heaps;
- function closures;
- interface dynamic values.

Do not resurrect fake operational values merely to say a static type exists.

43. Non-generic boundary

Document:

- no type parameters;
- no generic types;
- no generic aliases;
- no constraint-only interface semantics;
- no instantiation or inference;
- no imports.

The eventual `any`/`error`/ordinary interface story belongs to the non-generic interface phase.

PART P — required deletions and forbidden resurrection

44. Do not restore historical architecture

Forbidden:

- old `GoNumeric.v` wholesale;
- old `GoTypes.ptype`;
- `PTy`;
- `GoTypeTag`;
- `GoRuntimeTypes`;
- `Surface`;
- `TypedIR`;
- extraction plugins;
- plugin recognizer tables;
- primitive float operations;
- `PrimFloat`;
- `PrimInt63`;
- `Sint63`;
- one runtime type universe beside `GoType`;
- float64-mediated float32 conversion;
- per-node “exact-or-reject” conservative filter as compiler authority;
- runtime arithmetic;
- float comparisons;
- complex values;
- named/composite types before their milestones.

45. Delete superseded renderer status code

If the generic `RenderedConstInfoDenotes` root makes old integer-only denotation machinery redundant, delete it.

Do not retain two authorities “for compatibility.”

PART Q — acceptance criteria

Workflow

- Old loop stopped.
- This directive copied verbatim into `.review/NEXT_STEPS.md`.
- Contract committed before implementation.
- Exact `/loop 5m ...` command started.
- Codex reviewed under `.review/CODEX_REVIEW_POLICY.md`.
- No out-of-scope feature kept the loop alive.
- GREEN reached.
- Final notification sent.
- Loop stopped.

Integer repair

- Bare rendered integer constants remain untyped.
- Explicit conversion assigns the target type directly.
- `uint64(2^63)` and `uint64(maxuint64)` have no false intermediate typed-int premise.
- Default-int overflow still rejects.
- One generic constant-status render authority uses `ConstInfo`.
- No competing integer status universe remains.

Float type root

- Exactly F32/F64.
- Precision and exponent parameters single-sourced.
- `GoType` extended once.
- No placeholder types.
- No TargetConfig.

Exact constants

- Exact canonical rational `FloatConst`.
- Intrinsic bounded finite-decimal raw literal value.
- Raw interpretation exact, unrounded, unsigned-zero only.
- Default type F64.
- No NaN/Inf/negative-zero constants.

Conversions

- Direct target rounding through SpecFloat.
- F32 never passes through F64 unless source syntax explicitly says `float32(float64(...))`.
- Typed constants carry exact rounded values.
- Constantness survives nesting.
- Float->integer constants require exact integral value.
- Overflow rejects.
- Underflow to zero accepts.
- Wrong-type sources reject.

Runtime values

- Canonical proof-carrying FloatValue.
- F32/F64 identity retained.
- Runtime representation future-compatible with signed zero/Inf/NaN.
- Constant evaluation produces only finite/+0 values.
- ValueWF and type preservation proved.
- No GoTypeTag.

Rendering

- One canonical decimal spelling.
- Independent decoder.
- Semantic decode/render round trip.
- All ASCII.
- Generic renderer denotation preserves `ConstInfo`.
- Final rendering denotes exact value and resolved type.
- No general parser.
- No OCaml float formatting.

Historical scars

- 2^24+1 F32 rounding pinned.
- 2^53+1 F64 rounding pinned.
- direct-vs-nested historical double-round case pinned.
- underflow/overflow pinned.
- signed-zero split pinned.
- fractional constant-to-int rejection pinned.

Compiler/e2e

- Compiler soundness/completeness remain.
- Float witness compiles and runs.
- Rejection fixtures agree with pinned Go.
- Empty and existing integer/string programs remain valid.
- Generated artifact synchronized through the same sink.
- `make check` green.
- pre-commit staged verification green.

Proof

- Every new public surface closed.
- Whole-theory audit green.
- No primitive float assumptions.
- No tracked axiom fixture.

Roadmap

- Static Type Universe Arc recorded.
- Later phases not implemented.
- No fake operational model added for a merely static type.

PART R — completion report

46. Completion report

When complete, report:

- contract commit SHA;
- final implementation commit SHA;
- complete commit range;
- Codex final result and dispositions;
- historical files and commits inspected;
- transplant ledger;
- final integer denotation repair;
- old denotation code deleted;
- exact `FloatType`;
- exact raw decimal-float domain and its bounds;
- exact `FloatConst` representation;
- exact direct rounding algorithm;
- proof F32 does not use an implicit F64 intermediate;
- canonical runtime `FloatValue` invariant;
- constant zero/sign treatment;
- `convert_const` rules;
- float-to-integer constant rules;
- direct-vs-nested historical values;
- canonical source spelling;
- independent decoder grammar;
- every theorem added or materially changed;
- complete `Print Assumptions` results;
- whole-theory audit result;
- real-Go acceptance/rejection fixtures;
- generated source diff;
- runtime golden evidence;
- `make prove`, `make e2e`, `make check`, and pre-commit results;
- roadmap documentation changes;
- confirmation notification sent;
- confirmation loop stopped.

Do not list a retained correctness flaw as a known limitation.

If a real obstacle requires changing this contract:

- classify it as an ARCHITECTURAL CONFLICT;
- notify the user;
- stop the loop;
- wait.

47. Hard stop

When Codex is GREEN and final verification passes:

1. Commit the completed checkpoint.
2. Notify the user through the configured completion-notification channel.
3. Stop the `/loop`.
4. Do not start complex numbers or another type phase.
5. Wait for review.

Bottom line

This milestone produces:

  repaired rendered constant status
    -> exact untyped integer/float constants
    -> direct destination representability and rounding
    -> typed constants retaining exact value + type
    -> one static GoType authority
    -> canonical runtime integer/float values
    -> one generic render/ConstInfo denotation root
    -> exact direct renderer
    -> real-Go differential alarms

No arithmetic.

No second AST.

No parallel runtime type universe.

No primitive float axioms.

No double rounding unless the source explicitly requests two conversions.

This begins the type universe.

It does not skip ahead to its operations.
