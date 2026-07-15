Claude Code milestone: transplant the mature historical integer foundation into the current one-AST architecture

THIS FILE IS THE BINDING MILESTONE CONTRACT.

Before implementation

1. Stop any currently running `/loop`.

2. Replace the tracked repository file `.review/NEXT_STEPS.md` with this directive VERBATIM.
   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not “improve” the selected architecture while copying it.

3. Do not modify `.review/CODEX_REVIEW_POLICY.md` in this milestone unless the user explicitly directs it.
   The current permanent review policy remains binding.

4. Commit `.review/NEXT_STEPS.md` as the opening commit of this milestone, before implementation.

5. Record the contract commit SHA.

6. After the contract commit, issue this exact Claude Code command:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

The loop is authorized only for this milestone.

The loop must:

- work only toward `.review/NEXT_STEPS.md`;
- use `.review/CODEX_REVIEW_POLICY.md`;
- repair blocking implementation defects within the declared scope;
- never broaden the milestone merely because historical code contains more features;
- never restore a rejected historical architecture merely because its local definitions are useful;
- classify any necessary architecture change as an ARCHITECTURAL CONFLICT;
- notify the user and stop on an architectural conflict;
- stop when Codex is GREEN under the permanent review policy;
- after GREEN, run final verification, commit the checkpoint, notify the user, stop the loop, and wait.

Milestone purpose

This milestone has two ordered parts:

A. Perform a small documentation cleanup:
   - state the string theorem honestly as a semantic byte round trip, not a source-spelling round trip;
   - cull `PAINFUL_LESSONS.md` down to durable future-facing lessons.

B. Transplant the mature historical integer foundation into the CURRENT architecture:
   - one integer-type descriptor;
   - exact `Z` constant values;
   - generic representability;
   - typed constants that retain value and type;
   - explicit integer constant conversions;
   - one runtime integer value shape using the same type authority;
   - canonical direct rendering and real-Go differential evidence.

No arithmetic operators in this milestone.

No imports.

No identifiers, variables, assignments, user-defined functions, parameters, results, or control flow.

No second AST or IR.

History is the technical quarry.

The current architecture is the authority.

Standing project law

Ruthless correctness or ruthless deletion.

The AST is the IR.

There is:

- one raw `GoProgram`;
- one raw `GoExpr` tree per expression;
- one `GoType` authority;
- one exact constant-value authority;
- one whole-program `GoCompile`;
- one `GoSafe` value semantics using the same types;
- one direct Rocq renderer;
- no typed AST;
- no copied compiled AST;
- no target AST;
- no `Surface`;
- no `TypedIR`;
- no `GoTypeTag` parallel universe;
- no handwritten OCaml typechecker, compiler, numeric semantics, conversion logic, or renderer;
- no name-based extraction/lowering plugin;
- no general Go lexer or parser;
- no raw/opaque/text fallback constructor.

PART A — documentation cleanup

1. State the string result precisely

The current string implementation is correct.

Do not change the string encoder or decoder merely to force a source-spelling inverse.

Replace wording that says the decoder accepts “exactly the canonical subset” when that wording implies that equivalent noncanonical source spellings must be rejected.

Use this durable statement throughout active documentation and relevant source comments:

> Fido emits one canonical source spelling for every semantic string byte sequence. Its certified decoder assigns exact byte meaning to that spelling and may also accept semantically equivalent noncanonical spellings. The proved round trip is `decode(render(bytes)) = Some bytes`; no source-spelling round trip `render(decode(source)) = source` is claimed.

Examples:

- `"A"` and `"\x41"` may denote the same byte sequence.
- Fido always emits the canonical direct-printable spelling `"A"`.
- The theorem recovers the bytes, not the historical source spelling.

Keep:

  decode_string_literal (render_string_literal s) = Some s

Do not add a reverse theorem.

Do not narrow the decoder merely to make prose easier.

2. Cull `PAINFUL_LESSONS.md`

Rewrite `PAINFUL_LESSONS.md` as a concise set of durable architectural lessons likely to change future decisions.

Keep, in compact form:

1. A subset filter is not exact compiler admissibility.
2. The Go compilation unit is the whole module tree.
3. Gate the invariant actually advertised.
4. Handwritten OCaml is transport, never language semantics.
5. Proof-carrying provenance still requires a live assumption-closure gate.
6. Review rigor must match the component’s declared guarantee and threat model.
7. Audit compiled assumption closure, not source text.
8. No raw escape hatch, typed AST, copied program, or parallel semantic authority.
9. Untyped constants, typed constants, and runtime values are distinct.
10. Integration/differential tests are alarms, not proofs.
11. Foundations before feature breadth.
12. Generated Go may be tracked only as a derived artifact checked against the certified output.
13. String value is bytes; source spelling is a separate canonical proved encoding.

Compress the filesystem lesson to the durable points only:

- practical single-owner/cooperating-emitter threat model;
- one lock;
- sibling temporary files;
- complete image staged before installation;
- fail-closed ordinary filesystem observation;
- foreign Go/module rejection;
- no transaction-log/stage-record architecture.

Delete from `PAINFUL_LESSONS.md`:

- exact branch-ordering implementation manuals;
- review-round ping-pong;
- lists of every historical sink bug;
- commit-specific narratives;
- detailed Git-path attack cases;
- detailed shell-gate mechanics;
- stale implementation line counts;
- material that is already better located in `ARCHITECTURE.md`, source comments, tests, or Git history.

Do not turn the culled file into another status ledger.

PART B — historical integer transplant

3. Required historical reconnaissance

Before writing integer implementation code, inspect the mature historical work.

Primary mature snapshot immediately before the Great Culling:

  7f4da96e72168d425d3e06c467448bd2a9979cc5

Read these files at that snapshot:

  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoNumeric.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoTypes.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoAst.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoRuntimeTypes.v
  git show 7f4da96e72168d425d3e06c467448bd2a9979cc5:GoCompile.v

Use targeted historical searches rather than reading only the final monolith:

  git log -S 'PtTIntConst' --all --oneline
  git log -S 'int_const_repr' --all --oneline
  git log -S 'wrap64' --all --oneline
  git log -S 'i64_no_overflow' --all --oneline
  git log -S 'assignable_to_ty' --all --oneline
  git log -S 'untyped INTEGER constants' --all --oneline

Read the deletion decision:

  git show 33c8df0f2273adae8eed15ec0e45a7b000fb7235

The deletion rationale is binding context:

- the old numeric mathematics was not disproved;
- the old compiler authority was unsound;
- the old runtime/type-tag world was disconnected from certified emission;
- the extraction/plugin architecture and duplicated semantic universes were rejected.

Read these focused commits and their diffs:

A. Full-width signed int64 over `Z`

  86dce7fc72bee4f0c887fd8839d9f006fde576ab

B. Signed int64 division/remainder/bitwise/shifts

  65fdc312cb6040656613cf1cf8e83fcd78f17390

C. Full-width unsigned uint64 over `Z`

  2e90be356f556fe2b7b5739ebe10daac1e10a095

D. Arbitrary-precision untyped integer constants, type at use

  866fb86bf6830a8ba272facc4828615312224e0e

E. Constant-aware static categories; constness survives conversions and folds

  4317b56aa42ae59c6e507b84e21b13b9068ce7fc

F. No-overflow obligations imply exact mathematical arithmetic

  509e7c925c0e3c3caeb4710ded3fc014a7986810

G. Final removal of PrimInt63/Sint63 dependencies; zero-axiom numeric base

  445aca38ef5a043f69e088be27a21713e822381f

Optional earlier context:

  fa07722696ce22772167f3cd88e38df23c7e1992

This milestone may reuse definitions or proof ideas only after translating them into the current architecture.

Do not cherry-pick those commits.

Do not restore whole deleted files.

4. Historical transplant ledger

Use this disposition table as the binding transplant map.

| Historical item | Current destination | Disposition |
|---|---|---|
| `Z` integer carrier | `GoConst`, integer runtime values | Retain |
| `in_i8`…`in_u64` range mathematics | generic `IntegerType` range authority | Generalize |
| `int_ty_range` / `int_const_repr` | one reflected representability relation | Rebuild exactly |
| `wrap64`, `wrapU64`, `iN_norm_z` | future runtime arithmetic/conversion milestone | Mine proofs now, do not expose unused live ops |
| distinct `GoI8`…`GoUint` identities | one `IntegerType` descriptor | Retain identity, replace per-type records |
| `PtIntConst z` | untyped `ConstInfo` | Retain concept |
| `PtTIntConst t z` | typed `ConstInfo` | Retain concept |
| `PtRunInt t` | future runtime-expression static category | Do not add before a runtime expression needs it |
| constantness through nested conversions | current constant analyzer | Retain exactly |
| `conv_to_scalar` integer-constant arm | explicit integer conversion typing | Rebuild |
| `assignable_to_ty` | future assignment/argument/composite-literal milestone | Defer |
| `num_arith`, comparisons, shifts, div/rem | next integer-arithmetic milestone | Defer |
| no-overflow exactness theorems | next integer-arithmetic milestone | Preserve as reference |
| per-type `SProp` wrappers used to survive extraction | none | Do not restore for extraction reasons |
| `GoTypeTag` | none | Do not restore |
| conservative `ptype` subset classifier | none | Do not restore as compiler authority |
| 32-bit portable `int`/`uint` accept-set | none | Reject; current `int`/`uint` are pinned 64-bit |
| `i64c`/`u64c` tactic/Number Notation as compiler | none | Do not restore |
| name-based plugin folds/lowering | none | Do not restore |
| floats, maps, channels, heap, concurrency | none in this milestone | Do not restore |

5. Expand the one integer authority

Expand the existing `Ints.v` into the sole integer-family descriptor and range authority.

Do not create a second numeric-range module beside it.

Required type:

  Inductive IntegerType : Type :=
  | IInt
  | IInt8
  | IInt16
  | IInt32
  | IInt64
  | IUint
  | IUint8
  | IUint16
  | IUint32
  | IUint64.

Do not add:

- `uintptr`;
- `byte` as a distinct type;
- `rune` as a distinct type;
- floats;
- complex numbers;
- arbitrary user-defined integer types.

`byte` is an alias of `uint8`; `rune` is an alias of `int32`. They can receive source-name support only in a later reviewed milestone if syntax needs those aliases.

Define one authority for:

  integer_type_eqb
  integer_signed
  integer_bits
  integer_min
  integer_max
  integer_keyword

Required widths:

- `IInt` = signed 64-bit;
- `IUint` = unsigned 64-bit;
- fixed-width names match their suffix.

This is the existing pinned linux/amd64 semantic choice.

Do not reintroduce `TargetConfig`.

Define:

  IntRepresentable : IntegerType -> Z -> Prop
  integer_representableb : IntegerType -> Z -> bool

with exact inclusive ranges:

- signed W: `[-2^(W-1), 2^(W-1)-1]`;
- unsigned W: `[0, 2^W-1]`.

Prove at minimum:

- `integer_type_eqb it1 it2 = true <-> it1 = it2`;
- `integer_representableb it z = true <-> IntRepresentable it z`;
- every `integer_min it` is representable;
- every `integer_max it` is representable;
- `integer_min it - 1` is not representable;
- `integer_max it + 1` is not representable;
- `integer_keyword` is exact for all ten constructors;
- integer keywords are injective;
- `IInt` and `IInt64` are distinct types despite equal ranges;
- `IUint` and `IUint64` are distinct types despite equal ranges;
- `IInt`/`IUint` are exactly 64-bit.

Existing names such as `int_min`, `int_max`, and `uint_max` may remain only as definitions derived from this generic authority:

  int_min  := integer_min IInt
  int_max  := integer_max IInt
  uint_max := integer_max IUint

No duplicated numeric literals may become a second authority.

6. Grow the single `GoType`

Replace the old scalar `TInt` constructor with one parameterized integer family:

  Inductive GoType : Type :=
  | TBool
  | TInteger : IntegerType -> GoType
  | TString.

Update the one `GoType` equality authority.

The type of an ordinary defaulted integer literal is:

  TInteger IInt

Do not keep a second live `TInt` constructor.

A notation for `TInteger IInt` is permissible only if it is purely notation and does not become another semantic case.

Every exhaustive type consumer must handle the integer descriptor structurally.

7. Grow the raw AST only as needed

Add exactly one integer conversion constructor:

  EIntConvert : IntegerType -> GoExpr -> GoExpr

Its target is the intrinsic `IntegerType`, not a raw string keyword.

Examples represented by the AST:

  int8(42)
  uint64(18446744073709551615)
  uint8(int(300))
  int8(int16(127))

The last two are representable syntax but may be compiler-invalid.

Do not add:

- general named conversions;
- a raw type-name string;
- arithmetic;
- comparison;
- bitwise operations;
- shifts;
- division/remainder;
- variables;
- calls;
- a parenthesis node.

`EInt`/`ENeg` remain exact untyped integer literal syntax.

8. Keep one exact constant-value authority

Retain and extend the exact value meaning over the same raw AST.

A conversion does not change the mathematical constant value.

The value domain remains:

  GoConst :=
  | CBool bool
  | CInt Z
  | CString string.

Define or retain one total exact constant-value function over the current constant-only expression grammar:

  const_value : GoExpr -> GoConst

Required conversion rule:

  const_value (EIntConvert it e) = const_value e

No range check occurs in `const_value`.

No wrap occurs in `const_value`.

A raw integer constant remains arbitrary-precision `Z`, including values far outside every runtime integer range.

9. Add one constant-status analysis

Introduce one static constant result over the same AST, conceptually:

  Inductive ConstInfo : Type :=
  | UntypedConst : GoConst -> ConstInfo
  | TypedConst   : GoType -> GoConst -> ConstInfo.

Names may vary if responsibility remains exact.

Define one executable analyzer:

  const_info : GoExpr -> option ConstInfo

Required rules:

A. Raw literals

- `EBool b` -> `UntypedConst (CBool b)`;
- `EInt n` -> `UntypedConst (CInt (Z.of_N n))`;
- `ENeg n` -> `UntypedConst (CInt (- Z.of_N n))`;
- `EString s` -> `UntypedConst (CString s)`.

B. Integer constant conversion

For:

  EIntConvert target e

first analyze `e`.

The operand must be either:

- `UntypedConst (CInt z)`; or
- `TypedConst (TInteger source) (CInt z)`.

Then:

- if `integer_representableb target z = true`,
  return `TypedConst (TInteger target) (CInt z)`;
- otherwise reject with `None`.

Reject conversion operands that are bool/string constants.

A conversion of a constant remains a constant.

A typed constant retains:

- its exact `Z` value;
- its exact integer type.

Never silently convert a constant category into a runtime category merely to forget a failed obligation.

Required transitive behavior:

- `uint8(int(300))` rejects;
- `int8(int16(127))` accepts as typed `int8` constant value 127;
- `int8(int16(128))` rejects at the outer conversion;
- converting a typed constant to another integer type rechecks the exact value against the destination.

Prove:

- `const_info` agrees with `const_value` on the carried value;
- successful analysis is deterministic;
- typed integer constants carry a representable value;
- conversion preserves the exact mathematical `Z`;
- invalid nested conversion cannot be revived by an outer conversion.

Do not add a `RuntimeValue` static category in this milestone. There is no runtime expression source yet.

10. Generalize representability and defaulting

Update the one `ConstRepresentable` authority.

Required rules:

- `CBool b` is representable as `TBool`;
- `CString s` is representable as `TString`;
- `CInt z` is representable as `TInteger it` iff `IntRepresentable it z`;
- all cross-kind cases reject.

Update the reflected checker and its exact theorem.

Default types:

- bool constant -> `TBool`;
- untyped integer constant -> `TInteger IInt`;
- string constant -> `TString`.

Typed constants do not default again.

11. Generalize contextual expression resolution

`UsePrintlnArg` allows:

- `TBool`;
- every `TInteger it`;
- `TString`.

Update `ResolveExpr` and its executable reflection so:

A. Untyped constant

- choose `const_default_type`;
- require use-context allowance;
- require representability.

B. Typed constant

- retain its explicit type;
- require use-context allowance;
- require the carried value remains representable;
- do not default it to `int`;
- do not allow it to adapt as though untyped.

Required examples:

- bare `42` resolves as `TInteger IInt`;
- bare `2^63` does not resolve for `println` because it does not fit `int`;
- `uint64(2^63)` resolves as `TInteger IUint64`;
- `int64(2^63)` rejects;
- `uint8(255)` resolves;
- `uint8(256)` rejects;
- `int8(-128)` resolves;
- `int8(-129)` rejects.

Retain exact proofs:

- soundness;
- completeness;
- determinism;
- no successful resolution at the wrong type;
- reflected statement/file/program typing;
- empty program remains typed.

There must still be one live static typing path.

No `ptype`.

No typed AST.

12. Integrate with whole-program `GoCompile`

`GoCompile` remains:

  ProgramTyped
  +
  exactly one main declaration per package.

Update it to use the generalized integer type system.

Retain:

- whole-program all-or-nothing behavior;
- empty-program acceptance;
- package grouping by file path;
- one-main-per-package;
- soundness/completeness of executable compilation against the declarative judgment;
- rejection before rendering/emission.

The existing `ErrIntOverflow` name is no longer complete once typing can fail because:

- a constant does not fit any of ten integer types;
- a conversion operand is not integer;
- nested typed conversion is invalid.

Use one honest typing error, for example:

  ErrTyping

plus:

  ErrPackageMainCount

unless a finer error taxonomy is completely reflected and remains small.

Do not preserve an inaccurate error name merely for compatibility.

`CompilationFacts` remains evidence/facts over the same program.

Do not add a typed program.

13. Runtime integer values use the same type authority

Replace the old single `VInt Z` runtime case with one integer-family case.

Preferred minimal shape:

  Inductive GoValue : Type :=
  | VBool    : bool -> GoValue
  | VInteger : IntegerType -> Z -> GoValue
  | VString  : string -> GoValue.

Define:

  value_type (VInteger it z) = TInteger it.

Define one value well-formedness authority:

  ValueWF : GoValue -> Prop
  value_wfb : GoValue -> bool

with:

- every bool/string value well formed;
- `VInteger it z` well formed iff `IntRepresentable it z`.

A single generic proof-carrying `IntegerValue it` wrapper is acceptable only if it makes the complete proof surface smaller.

Do not create one Rocq record type per Go integer type.

Do not reintroduce `GoTypeTag`.

Do not make record shape serve an extraction plugin; there is no semantic extraction backend.

14. Evaluation must reuse constant analysis

Refactor expression evaluation so it does not invent another conversion/type/value authority.

Because raw syntax can now contain compiler-invalid conversions, evaluation may be partial:

  eval_expr : GoExpr -> option GoValue

or an equivalent resolved-evaluation function.

Required behavior under `UsePrintlnArg`:

- untyped bool -> `VBool`;
- untyped string -> `VString`;
- untyped integer -> `VInteger IInt z`, only if default-int representable;
- typed integer constant -> `VInteger target z`, only if its conversion chain is valid;
- invalid conversion -> `None`.

Evaluation must derive from the same `ConstInfo`/resolution result.

Do not duplicate constant folding or conversion representability in `GoSafe`.

Prove:

- `ResolveExpr use e t` implies evaluation succeeds;
- the resulting value has type `t`;
- the resulting value is `ValueWF`;
- explicit integer conversion preserves the exact `Z` value;
- `EInt 0` and `ENeg 0` remain semantically equal after default resolution;
- nested typed conversions preserve the exact value when accepted.

`GoSafe` may remain logically `True` in this milestone:

- constant conversion failure is a compile-time typing failure;
- no new runtime panic, blocking, heap, or nontermination source is introduced.

Do not add a panic/outcome model merely because future arithmetic division will need one.

15. Canonical direct rendering of integer conversions

Render every integer type using its exact Go keyword:

  int
  int8
  int16
  int32
  int64
  uint
  uint8
  uint16
  uint32
  uint64

Render:

  EIntConvert it e

as:

  <integer_keyword it>(<render_expr e>)

Examples:

  int8(42)
  uint64(18446744073709551615)
  uint8(int(300))

The renderer renders raw syntax even when the program is invalid, but certified emission remains impossible without `SafeProgram`.

No general parser.

No token layer.

No formatter rewrite.

No name-based OCaml lowering.

Prove:

- integer keywords are ASCII;
- converted expressions are ASCII;
- exact spelling fixtures for every integer keyword;
- nested conversion rendering is exact;
- existing literal rendering remains unchanged.

16. Honest rendered integer denotation

The old unconditional `render_expr_denotes` theorem must not remain falsely unconditional if a raw expression can now contain an invalid conversion.

Use a resolved-expression theorem.

Introduce a small certified denotation relation for the emitted integer-expression subset, conceptually:

  RenderedIntegerDenotes : string -> IntegerType -> Z -> Prop

It should cover:

A. Bare default-int literal

- canonical decimal or unary-minus decimal;
- denotes `IInt` and exact `Z`.

B. Explicit integer conversion

- canonical integer keyword;
- opening parenthesis;
- a recursively denoting inner integer expression;
- closing parenthesis;
- exact value preserved;
- destination representability required;
- outer result type is the destination type.

This relation may admit semantically equivalent spellings.

It is a denotation tool, not a general Go parser.

Extend `RenderedPrimitiveDenotes` so:

  VInteger it z

is denoted through `RenderedIntegerDenotes`.

Prove a root theorem such as:

  ResolveExpr UsePrintlnArg e t ->
  exists v,
    eval_expr e = Some v
    /\ value_type v = t
    /\ ValueWF v
    /\ RenderedPrimitiveDenotes (render_expr e) v.

Equivalent decomposition into smaller load-bearing theorems is acceptable.

Retain string byte-denotation and bool denotation.

Real Go parsing remains external adequacy.

17. Historical boundary fixtures to resurrect now

Add kernel-checked fixtures for every integer type’s exact boundaries.

Generic theorem surface:

- min accepted;
- max accepted;
- min - 1 rejected;
- max + 1 rejected.

Concrete fixtures must include at least:

Signed:

- `int8(-128)` accepted;
- `int8(127)` accepted;
- `int8(-129)` rejected;
- `int8(128)` rejected;
- `int16` min/max accepted;
- `int32` min/max accepted;
- `int64` min/max accepted;
- platform `int` min/max accepted.

Unsigned:

- `uint8(0)` accepted;
- `uint8(255)` accepted;
- `uint8(-1)` rejected;
- `uint8(256)` rejected;
- `uint16` max accepted;
- `uint32` max accepted;
- `uint64(18446744073709551615)` accepted;
- `uint64(18446744073709551616)` rejected;
- platform `uint` max accepted.

Type-at-use:

- bare `9223372036854775808` rejects as default `int`;
- `uint64(9223372036854775808)` accepts;
- `int64(9223372036854775808)` rejects.

Transitive typed-constant cases:

- `uint8(int(300))` rejects;
- `uint8(int(255))` accepts;
- `int8(int16(127))` accepts;
- `int8(int16(128))` rejects;
- `int8(true)` rejects;
- `uint64("x")` rejects.

Type identity:

- `IInt <> IInt64`;
- `IUint <> IUint64`;
- their keywords differ;
- their static types differ.

Arbitrary precision:

- a raw `CInt`/literal with a value above `2^64` remains exactly representable in the constant domain;
- it simply fails typed resolution to every current integer type.

Do not add arithmetic solely to recreate the historical `(1 << 70) >> 8` fixture.

Record that fixture as mandatory for the next arithmetic milestone.

18. Real-Go differential and generated witness

Grow the canonical witness to exercise accepted integer conversions.

Include readable coverage of all ten integer types.

At minimum print:

- signed minima/maxima for representative narrow and 64-bit types;
- unsigned maxima;
- platform `int` and `uint`;
- `uint64(2^63)`;
- nested accepted conversion such as `int8(int16(127))`.

Use exact reviewed goldens.

Add hand-written real-Go rejection fixtures for:

- `int8(128)`;
- `int8(-129)`;
- `uint8(-1)`;
- `uint8(256)`;
- `int64(9223372036854775808)`;
- `uint64(18446744073709551616)`;
- `uint8(int(300))`;
- integer conversion of bool/string.

The pinned Go 1.23 linux/amd64 toolchain must:

- accept every Fido-accepted rendered fixture;
- reject the representative Fido-rejected fixtures.

A disagreement is a model bug.

Regenerate tracked `main.go` only through:

  make regenerate

Do not hand-edit generated Go.

19. What is explicitly deferred

Do not implement in this milestone:

- binary arithmetic;
- unary complement;
- general unary minus over expressions;
- comparison;
- shifts;
- division;
- remainder;
- runtime wrapping operations;
- runtime integer-to-integer conversions;
- no-overflow arithmetic APIs;
- assignment;
- variables;
- function parameters/results;
- composite literals;
- aliases `byte`/`rune`;
- `uintptr`;
- floats;
- imports.

The historical arithmetic and wrap work is the required quarry for the next integer milestone.

The next milestone may add:

- exact untyped constant arithmetic over `Z`;
- typed constant arithmetic with result representability;
- runtime arithmetic with width normalization;
- no-overflow evidence and exactness theorems.

Do not begin it now.

20. Public theorem and assumption gate

Update `gate/axiom_gate.v` with meaningful public surfaces.

At minimum gate:

Ints

- integer-type equality reflection;
- representability reflection;
- exact 64-bit `int`/`uint`;
- generic min/max accepted;
- generic below/above rejected;
- keyword exactness/injectivity;
- type distinctness `IInt <> IInt64`, `IUint <> IUint64`.

GoTypes

- constant value exactness through conversion;
- successful conversion preserves `Z`;
- typed conversion representability;
- resolution soundness/completeness/determinism;
- default-int behavior;
- explicit uint64 type-at-use behavior;
- transitive nested-conversion rejection;
- program typing reflection.

GoCompile

- revised `prog_ok_iff`;
- compiler soundness/completeness;
- empty program accepted;
- a concrete integer-family program compiles;
- an invalid nested-conversion program has no `CompilableProgram`.

GoSafe

- resolved evaluation succeeds;
- value type agrees;
- value well-formedness;
- exact converted integer value;
- zero-sign agreement.

GoRender

- all ten keyword spellings;
- converted expression ASCII;
- nested conversion exact spelling;
- resolved render/value/type correspondence.

All surfaces must be closed.

The whole-certified-theory assumption audit must remain GREEN.

No `Axiom`, `Parameter`, `Admitted`, functional extensionality, primitive integer axiom, or source-text axiom scanner.

Do not import `PrimInt63` or `Sint63`.

21. Documentation reconciliation

Update:

- `.review/NEXT_STEPS.md`;
- `ARCHITECTURE.md`;
- `CLAUDE.md`;
- `README.md`;
- `PROGRESS.md`;
- culled `PAINFUL_LESSONS.md`;
- `Ints.v`;
- `GoAST.v`;
- `GoTypes.v`;
- `GoCompile.v`;
- `GoSafe.v`;
- `GoRender.v`;
- `GoEmit.v` comments if needed;
- `gate/axiom_gate.v`;
- e2e witness/goldens;
- Makefile/Dockerfile comments only where behavior changed.

Required truths:

A. Integer values

- exact mathematical integer constants are `Z`;
- runtime integer values retain their exact `IntegerType`;
- no `Sint63`.

B. Type identity

- `int` and `int64` are distinct types;
- `uint` and `uint64` are distinct types;
- they share ranges only because the current target is pinned 64-bit.

C. Constants

- raw literals are untyped;
- typed constants retain type and exact value;
- constants do not wrap;
- a conversion of a constant remains a typed constant;
- representability is checked at conversion/default use.

D. Runtime

- runtime wrapping arithmetic is not yet present;
- no claim is made about arithmetic or overflow execution in this milestone.

E. Architecture

- one AST;
- one `GoType`;
- no `GoTypeTag`;
- no historical `ptype`;
- no per-width runtime record family;
- no extraction plugin.

F. Strings

- canonical spelling;
- semantic byte round trip only;
- decoder may accept equivalent noncanonical spelling.

G. History

- historical source was mined and translated;
- the deleted architecture was not restored.

`PROGRESS.md` must remain compact.

22. Acceptance criteria

Workflow

- This directive was copied verbatim to `.review/NEXT_STEPS.md`.
- The contract was committed before implementation.
- The exact `/loop 5m ...` command was started.
- Codex reviewed under `.review/CODEX_REVIEW_POLICY.md`.
- No architectural conflict was silently implemented.
- Codex is GREEN.
- Notification sent.
- Loop stopped.

Cleanup

- String documentation states semantic byte round trip, not spelling inverse.
- No false “exactly canonical accepted language” claim remains.
- `PAINFUL_LESSONS.md` is concise and future-facing.
- Sink implementation detail/history was culled from the lessons file.

History

- All required historical files and commits were inspected.
- Completion report records what was retained, generalized, deferred, and rejected.
- No historical commit/file was restored wholesale.
- No cherry-pick of the old numeric/type/runtime subsystem.

Integer authority

- Exactly one `IntegerType`.
- Exactly ten live integer types.
- `int`/`uint` are pinned 64-bit.
- One range/representability authority.
- One keyword authority.
- No `TargetConfig`.
- No PrimInt63/Sint63.

AST and typing

- `EIntConvert` is the only new expression form.
- One exact `const_value`.
- One `ConstInfo` analyzer.
- Untyped and typed constants are distinct.
- Typed constants retain exact type + value through nesting.
- One reflected `ResolveExpr`.
- No typed AST.
- No `ptype`.
- No runtime static category added prematurely.

Compilation

- Whole-program compiler remains exact against its declarative judgment.
- Empty program remains valid.
- Invalid conversion rejects before bytes.
- Error names are honest.

Safety/value semantics

- One integer runtime value shape.
- Same `IntegerType`/`GoType` authority.
- Evaluation reuses constant analysis.
- Resolved evaluation succeeds, is well typed, and is range well formed.
- `GoSafe` does not pretend arithmetic safety was added.

Rendering

- Exact keyword + conversion spelling.
- All ASCII.
- Nested conversions render correctly.
- Resolved integer rendering denotes exact value and type.
- No parser/token/IR introduced.

Tests/e2e

- Every type’s min/max accepted.
- Every type’s below-min/above-max rejected.
- `uint64(2^63)` accepted while bare `2^63` and `int64(2^63)` reject.
- `uint8(int(300))` rejects.
- Real Go agrees on accepted/rejected representative fixtures.
- Canonical generated witness regenerated through certified output.
- `make check` GREEN.

Proof

- Public surfaces closed.
- Whole-theory audit GREEN.
- No project assumptions.
- No primitive integer axiom.

Scope

- No arithmetic, comparison, shifts, division, remainder, runtime wrapping, variables, functions, imports, floats, or aliases added.

23. Completion report

When complete, report:

- contract commit SHA;
- final implementation commit SHA;
- complete commit range;
- historical snapshot inspected;
- every focused historical commit inspected;
- historical files inspected;
- transplant ledger: retained/generalized/deferred/rejected;
- final `IntegerType`;
- final width/sign/range/keyword functions;
- final `GoType`;
- final raw conversion constructor;
- final `ConstInfo`;
- final constant analyzer rules;
- final defaulting and resolution rules;
- final runtime integer value shape;
- final value-well-formedness theorem;
- final evaluation theorem;
- final rendered integer denotation;
- exact generated witness delta;
- every boundary and nested-conversion fixture;
- real-Go differential results;
- every theorem added or materially changed;
- full `Print Assumptions` result;
- whole-theory audit result;
- final `PAINFUL_LESSONS.md` lesson list;
- all proof/build/e2e commands and results;
- Codex final result and nonblocking observations;
- confirmation notification sent;
- confirmation loop stopped.

Do not list a retained correctness defect as a known limitation.

If a real obstacle requires changing this architecture or scope, classify it as an ARCHITECTURAL CONFLICT, notify the user, stop the loop, and wait.

24. Hard stop

When Codex is GREEN and final verification passes:

1. Commit the completed checkpoint.
2. Notify the user through the configured completion-notification channel.
3. Stop the `/loop`.
4. Do not begin integer arithmetic.
5. Do not infer another feature.
6. Wait for joint review.

Bottom line

The permanent path after this milestone is:

  raw integer literal / explicit integer conversion
    -> exact arbitrary-precision `Z` constant value
    -> untyped or typed constant status
    -> one `IntegerType` family
    -> exact destination representability
    -> contextual `ResolveExpr`
    -> whole-program `GoCompile`
    -> one typed integer runtime value shape
    -> direct canonical conversion rendering
    -> certified DirectoryImage
    -> real Go differential alarm

Steal the mathematics.

Steal the semantic distinctions.

Steal the counterexamples.

Do not resurrect the old organism.
