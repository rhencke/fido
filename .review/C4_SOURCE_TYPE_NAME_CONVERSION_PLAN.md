# Claude Code directive: C4 source type names, compiler resolution, and unified numeric conversions

Repository:

`rhencke/fido`

Human authorization:

`C4-source-type-resolution-1`

Required baseline:

`8c9212a8c814c7a99a5e3ef1970a0ae32425a918`

This directive records Rob's decision that C3 is accepted and C4 is active. It is the accepted human Contract
Review for this C4 design. Do not request or run a Codex review. Rob has disabled the automatic Codex review
path. Complete the authorized work, report the frozen candidate, and stop for Rob's human Implementation Review.

Do not start from a dirty tree or a different commit. If `HEAD` is not the required baseline, or if tracked files
are dirty before this directive is installed, report the mismatch and stop.

===============================================================================
0. HUMAN DISPOSITION
===============================================================================

C3 is accepted at the required baseline.

C4 is one vertical checkpoint. Do not use the optional C4a/C4b split in the old roadmap.

The split is not sound for the current language. Today, the only live source positions that denote type names are
explicit conversion targets. A syntax-only C4a would therefore do one of three bad things:

- add dead type-name syntax;
- keep a second family-tag conversion path beside the new source-name path; or
- invent unresolved-name behavior for syntax that no valid program can contain.

None is allowed.

C4 must replace the three family-specific conversion constructors with one source-shaped conversion, resolve its
source type name in `GoCompile`, retain occurrence-keyed type-name facts, preserve the source spelling in
`GoRender`, and delete the old path in the same checkpoint.

The old roadmap also puts `byte` and `rune` alias resolution in C5 while C4.6 requires the source/semantic facts:

- `byte` resolves to semantic `uint8` but renders as `byte`;
- `rune` resolves to semantic `int32` but renders as `rune`.

This directive resolves that conflict. Source alias resolution for `byte` and `rune` is C4 work. C5 keeps:

- the new semantic type `uintptr`;
- exact untyped rune constants;
- rune literal rendering, defaulting, and conversion integration.

Do not add `TByte`, `TRune`, `IByte`, or `IRune`.

===============================================================================
1. INSTALL THE C4 AUTHORITY BEFORE CODE CHANGES
===============================================================================

1. Write this directive verbatim to:

   `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`

2. Compute its exact SHA-256.

3. Replace `.review/REVIEW_BASIS.md` with a concise C4 basis that records:

   - checkpoint: C4 source type names, compiler resolution, and unified numeric conversions;
   - contract path and exact SHA-256;
   - baseline commit above;
   - human authorization token above;
   - this directive as the accepted human Contract Review;
   - the claim surface in section 15;
   - the blocking defect classes in section 16;
   - the evidence required in section 17;
   - the forbidden overreach in section 18.

   Do not preserve the C3 review basis as current authority. Git history is its archive.

4. Replace `.review/NEXT_STEPS.md` with a compact active pointer that records:

   - active checkpoint: C4;
   - contract path and exact SHA-256;
   - accepted review basis path;
   - baseline commit;
   - human authorization token;
   - state: C4 implementation authorized;
   - automatic Codex review: disabled;
   - C5: forbidden.

5. Keep `.review/REVIEW_REQUEST.md` closed. Replace its stale C3 result with:

   ```text
   # Review Request

   state: closed
   review: Implementation Review
   confirmation: no
   confirmation_used: no
   human_override: C4-source-type-resolution-1
   result: none; human C4 Implementation Review is pending after the candidate is frozen

   contract: .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md
   contract_sha256: <exact hash>
   review_basis: .review/REVIEW_BASIS.md

   Automatic Codex review is disabled. No review is requested by this file.
   ```

6. Update `.review/SOURCE_FOREST_STATUS.md` to record:

   - C3 accepted at the baseline;
   - C4 active under this contract;
   - no C5 work;
   - no automatic Codex review.

7. Amend the active C4/C5 text in `.review/SOURCE_FOREST_MASTER_PLAN.md` only as needed to remove the conflict:

   - C4 is activated as one vertical checkpoint;
   - `byte` and `rune` source alias resolution is C4;
   - C5 retains `uintptr` and rune constants/literals;
   - arbitrary and qualified type names remain later work;
   - unresolved-name diagnostics are not a C4 requirement because unsupported names are intrinsically
     unrepresentable in this checkpoint.

   Do not rewrite the whole master plan.

8. Commit these authority changes before implementation:

   `review(contract): C4 — activate source type-name resolution`

No source, proof, test, generated, plugin, shell, or build change may enter that contract commit.

===============================================================================
2. C4 RESULT
===============================================================================

After C4, the live path must be:

```text
raw Go source AST
    EConvert TypeSyntax Expr
        |
        v
one retained GoIndex occurrence for the source type name
        |
        v
GoCompile current predeclared type context
        |
        v
occurrence-keyed resolved TypeNameFact
        |
        +------------------------+
        |                        |
        v                        v
GoTypes.convert_const        GoRender source spelling
semantic target              original type-name text
        |                        |
        +------------+-----------+
                     v
          exact accepted/rejected result
```

The raw AST owns source syntax only. `GoCompile` owns name binding. `GoTypes` owns semantic constant conversion.
`GoRender` owns source bytes and must read the source spelling, not reverse-map the semantic type.

There must be one production elaboration root, one retained index, one compiler occurrence visit per elaboration,
one type-name fact authority, one expression fact authority, one conversion semantic authority, and one renderer
path. The specification functions and the later SafeProgram renderer may traverse for their distinct proved jobs;
they must not become peer production compilers or rebuild compiler facts.

===============================================================================
3. EXACT LIVE SOURCE-NAME SCOPE
===============================================================================

C4 represents only these explicit conversion target spellings:

```text
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
float32
float64
complex64
complex128
byte
rune
```

The first fourteen preserve the existing conversion scope. `byte` and `rune` add source aliases with no new
semantic types.

The following remain unrepresentable as conversion targets in C4:

```text
bool
string
uintptr
any
error
comparable
unknown unqualified names
qualified names
user-declared type names
```

This exclusion is semantic, not cosmetic:

- representing `bool` or `string` would require exact accepted conversions that the current semantic domain does
  not implement;
- representing `uintptr` would pull C5 semantic identity into C4;
- representing `any`, `error`, or `comparable` would pull interface semantics into C4;
- representing arbitrary names would make `T(x)` depend on call-versus-conversion and declaration scope that the
  current language cannot express;
- representing qualified names would require imports and package binding that the current language cannot
  express.

Do not represent one of these forms and then reject all cases. Unsupported target forms must remain impossible to
construct.

Do not add variables, calls, declarations with names, parameters, results, imports, user types, selectors,
parenthesis nodes, or a parser to make broader names appear live.

===============================================================================
4. ONE SOURCE-NAME FOUNDATION
===============================================================================

Add a small source-name module, preferably `GoNames.v`, below `GoAST` and above semantic/compiler modules.
Use another name only if the dependency graph requires it.

It must own one intrinsic `IdentifierSyntax` domain. A proof-carrying ASCII subset is approved:

```text
[A-Za-z_][A-Za-z0-9_]*
```

with all pinned Go keywords excluded.

Required properties:

- no empty identifier;
- the first character is ASCII letter or underscore;
- each later character is ASCII letter, digit, or underscore;
- keywords cannot inhabit the domain;
- no unchecked `string` enters `IdentifierSyntax`;
- equality has a proved Boolean reflection;
- rendering is the stored source text;
- every rendered identifier is ASCII and valid in the approved bounded domain.

Non-ASCII Go identifiers remain honestly unrepresentable.

The same module must define the closed lexical class of the sixteen supported conversion type names. The lexical
class is source identity only. It must not contain:

- `GoType`;
- width or signedness;
- representability bounds;
- conversion rules;
- defaulting rules;
- renderer-only semantic tags.

Use one source-spelling authority. Construction, classification, equality, rendering, and proofs must derive from
one descriptor or one proved inverse pair. Do not repeat sixteen string tables across `GoAST`, `GoCompile`,
`GoRender`, tests, and diagnostics.

The raw type-name value must retain an `IdentifierSyntax`. A proof that it belongs to the approved sixteen-name
class is allowed. A semantic `IntegerType`, `FloatType`, `ComplexType`, or `GoType` in that raw source value is
not allowed.

Required source constructors or smart constructors must make all sixteen approved names easy to use in fixtures.
They must not provide a bypass for arbitrary strings.

===============================================================================
5. SPECIFICATION-SHAPED RAW AST
===============================================================================

Add only the live type syntax:

```text
TypeNameSyntax :=
  TNUnqualified <supported source type identifier>

TypeSyntax :=
  TSName TypeNameSyntax
```

Do not add a dead qualified-name constructor. Record the future direction in prose only. A qualified constructor
may become live only when imports and package-name binding become live.

Replace:

```text
EIntConvert     IntegerType GoExpr
EFloatConvert   FloatType GoExpr
EComplexConvert ComplexType GoExpr
```

with one constructor:

```text
EConvert TypeSyntax GoExpr
```

Delete the three old constructors in the same implementation. Do not keep:

- compatibility constructors;
- adapter functions that reconstruct old nodes;
- a second semantic-tag conversion AST;
- deprecated aliases;
- old fixture helpers that hide the old path.

All current conversion fixtures, examples, theorem statements, comments, rendering facts, safety facts, and e2e
witnesses must migrate to the one live constructor.

The AST must not decide that `byte` means `uint8` or that `rune` means `int32`.

===============================================================================
6. OCCURRENCE IDENTITY IN GoIndex
===============================================================================

Add one live type-name occurrence kind and a typed reference, for example:

```text
KTypeName
TypeNameRef
```

Do not add unused occurrence kinds for future type forms.

For `EConvert target operand`, the index must expose two children in source order:

1. the target type-name occurrence with role `RConversionTarget`;
2. the operand expression occurrence with role `RConversionOperand`.

`TypeSyntax` has only `TSName` in C4. Index the live type-name occurrence once. Do not add a redundant wrapper
occurrence that has no independent source identity or choice. Revisit that shape when a second type-syntax
constructor becomes live.

Extend the source view with the exact original `TypeNameSyntax`. Keep `NodeMeta` structural. Do not copy a
resolved type or semantic fact into the index.

Required index facts include:

- every conversion has exactly one target `TypeNameRef` and one operand `ExprRef`;
- the target precedes the operand in preorder;
- both have the conversion expression as parent with the exact roles above;
- every live type-name occurrence appears exactly once;
- every `TypeNameRef` extracts the exact source type name from the retained snapshot;
- repeated equal spellings in different source positions have distinct occurrence identities;
- foreign and wrong-kind keys cannot pass the typed-reference boundary;
- all existing parent, path, subtree-end, navigation, and visit exactness facts remain true.

Keep the existing one-pass standard-map index builder. Do not add a type-name side index built by a second AST
walk.

===============================================================================
7. COMPILER-OWNED NAME RESOLUTION
===============================================================================

`GoCompile` owns the current predeclared type context and the source-name-to-semantic-type map.

The exact current mapping is:

```text
int        -> TInteger IInt
int8       -> TInteger IInt8
int16      -> TInteger IInt16
int32      -> TInteger IInt32
int64      -> TInteger IInt64
uint       -> TInteger IUint
uint8      -> TInteger IUint8
uint16     -> TInteger IUint16
uint32     -> TInteger IUint32
uint64     -> TInteger IUint64
float32    -> TFloat F32
float64    -> TFloat F64
complex64  -> TComplex C64
complex128 -> TComplex C128
byte       -> TInteger IUint8
rune       -> TInteger IInt32
```

This table belongs in compiler binding logic, not `GoAST`, `GoTypes`, or `GoRender`.

The current language has no named declarations or imports, so do not build an empty general scope-stack
framework. A compact explicit current predeclared context is enough. Its interface must still make the ownership
clear so later declaration shadowing can replace or extend the lookup rather than rewrite the AST.

Define a resolved result that distinguishes source symbol identity from semantic type. It may retain the closed
predeclared symbol identity and must expose the resolved `GoType`. `byte` and `uint8` must remain distinct source
symbols even though their semantic type is equal. The same rule applies to `rune` and `int32`.

Resolution may return an option for future extension, but prove that it succeeds for every C4-live
`TypeNameSyntax`.

Do not copy the source identifier into the resolved fact. The `TypeNameRef` is the source identity and can recover
its spelling from the retained snapshot.

===============================================================================
8. OCCURRENCE-KEYED TYPE-NAME FACTS
===============================================================================

Add one sealed standard-map fact table keyed by the existing `NodeKey`, with a typed public query over
`TypeNameRef`, analogous to the current expression-fact table.

A fact must contain the resolved compiler result, not a copy of raw syntax.

Add it to `ElaborationFacts` and retain it in `CompilableProgram` through the existing provenance path.

Required facts and proofs:

- the table domain is exactly the live type-name occurrences;
- no expression, statement, file, package, or foreign key occurs in the table;
- every `TypeNameRef` has one exact fact;
- the fact equals `GoCompile` resolution of that reference's source `TypeNameSyntax` in the current context;
- the total public query returns the stored table entry and does not recompute resolution;
- table construction uses the one retained compiler program visit/index and does not recurse over the AST again;
- the same once-built table supplies failure diagnostics during elaboration and is sealed into `ElaborationFacts`
  on success; the failure path must not call the resolver again to rebuild equivalent facts;
- `CompilableProgram` retains the same index and facts returned by the one `elaborate` call.

Do not store a second map from source strings to semantic types in the facts. Do not cache a renderer spelling in
the facts.

===============================================================================
9. ONE CONVERSION SEMANTIC AUTHORITY
===============================================================================

`GoTypes.convert_const` remains the sole target-directed constant-conversion authority.

It must continue to receive a semantic `GoType` and a source constant status. It must not resolve source names.
It must not inspect renderer strings.

Refactor the expression typing path so a conversion node is handled as follows:

1. obtain the target `TypeNameRef` from the retained index;
2. obtain its retained resolved type-name fact;
3. obtain the already computed operand expression fact;
4. call `GoTypes.convert_const` once with the resolved semantic target;
5. store the resulting expression fact or exact invalid-conversion evidence.

The production path must remain bottom-up and occurrence-indexed. Do not recursively recompute an operand's
constant status from the raw subtree after its fact exists.

The current context-free `GoTypes.const_info` and `const_info_step` pattern-match semantic target tags in the old
AST. That shape cannot remain as a hidden peer authority.

Use one coherent arrangement:

- keep literal and target-directed semantic steps in `GoTypes`;
- parameterize any index-free specification by a resolver, or move the source-name-aware specification to
  `GoCompile`;
- keep the production occurrence pass in `GoCompile` and prove it exact against the declarative/index-free
  specification;
- do not put a private source-name-to-`GoType` table in `GoTypes` to avoid the refactor.

`ProgramTyped`, `program_typedb`, `SourceProgramValid`, diagnostics, and the production elaboration must all use
the same approved resolver and conversion step. A specification helper may exist only with an exact theorem to
the production facts. It is not a second public compiler or capability path.

Preserve all current exact conversion behavior, including:

- integer range checks;
- exact integral float/complex-to-integer conditions;
- one-round float conversion;
- same-format typed float identity;
- same-format typed complex identity;
- component reuse facts;
- nested conversion behavior;
- defaulting and use-context behavior.

Do not replace proofs with test matrices or bounded evaluation claims.

===============================================================================
10. DIAGNOSTICS
===============================================================================

Every C4-live type name resolves by construction. Therefore C4 has no unresolved-type-name diagnostic.

Do not create a fake unresolved-name diagnostic whose source syntax cannot inhabit `GoProgram`.

Unknown, qualified, user-defined, and unsupported predeclared target names remain unrepresentable. A later
checkpoint may widen `TypeNameSyntax` and add exact binding failures when the language has enough scope and call
syntax to classify them honestly.

Invalid conversions remain represented and rejected. Update the structured invalid-conversion reason so it
retains structural links to:

- the conversion expression occurrence;
- its target `TypeNameRef`;
- the resolved semantic target;
- the operand status required by the current diagnostic contract.

Do not copy the target's source text into the reason when the retained reference can recover it. Erased/user-facing
reporting must use the source type-name spelling. Thus an invalid `byte(...)` conversion reports `byte`, not
`uint8`; an invalid `rune(...)` conversion reports `rune`, not `int32`.

Preserve exact diagnostic properties:

- soundness;
- completeness;
- one reason per failing conversion occurrence;
- valid anchors and target-child relation;
- deterministic source order;
- current command/source precedence;
- exact success iff the full retained report is empty.

Do not add a second diagnostic traversal or reconstruct type-name facts while erasing a report.

===============================================================================
11. RENDERING AND SOURCE/SEMANTIC IDENTITY
===============================================================================

Render a conversion from its raw `TypeSyntax`:

```text
render_type_syntax target ++ "(" ++ render_expr operand ++ ")"
```

`render_type_name` must read the retained source `IdentifierSyntax`. It must not select a keyword from the
resolved `GoType`.

Delete the old renderer branches that use:

- `integer_keyword` as an AST target decoder;
- `float_keyword` as an AST target decoder;
- `complex_keyword` as an AST target decoder.

Small semantic keyword helpers may remain only if another approved semantic proof needs them. Delete them if
they have no consumer. Do not leave them as a peer source renderer.

Extend the independent certified denotation reader only for the closed C4 type-name set. Do not add a general Go
parser, token parser, round-trip AST, host parser, or trusted string-to-type bridge.

Required representative theorems:

```text
source name byte  <> source name uint8
render byte       <> render uint8
resolve byte      = TInteger IUint8
resolve uint8     = TInteger IUint8

source name rune  <> source name int32
render rune       <> render int32
resolve rune      = TInteger IInt32
resolve int32     = TInteger IInt32
```

Also prove the conversion rendering/denotation theorem for all sixteen live names and all expressions whose
constant status succeeds.

The public `render_program`/materialization path must still require the existing `SafeProgram` and consume the
same retained compilation facts/provenance. Do not add a raw-program renderer or emitter capability.

===============================================================================
12. REQUIRED TESTS AND DIFFERENTIALS
===============================================================================

Migrate every existing conversion fixture to `EConvert` and keep its result.

Add focused Rocq examples for all sixteen names. At minimum cover:

- one accepted and one rejected boundary case for each numeric semantic family;
- nested conversions across integer, float, and complex targets;
- same-target nested identity cases;
- repeated equal type names at distinct source occurrences;
- exact target/operand index roles and source order;
- total type-name fact queries;
- no fact on a wrong-kind or foreign reference;
- source alias identity versus semantic equality.

Alias scars must include:

```text
byte(0)       accepted
byte(255)     accepted
byte(256)     rejected
byte(-1)      rejected
uint8(255)    same semantic result as byte(255)

rune(-2147483648) accepted
rune(2147483647)  accepted
rune(-2147483649) rejected
rune(2147483648)  rejected
int32 cases       same semantic results at the same values
```

Add pinned-Go differential cases for the alias scars and representative migrated conversions. Compare exact
accepted/rejected outcomes and, where the current harness supports it, printed values/types. Use the existing
pinned Go/Docker path. Do not call the host Go toolchain as authority.

Add construction-failure examples or equivalent intrinsic-domain proofs that the following cannot enter a C4
conversion target:

```text
bool
string
uintptr
any
error
comparable
foo
pkg.T
```

Do not add hundreds of fixtures where one universal theorem closes the class.

===============================================================================
13. GENERATED OUTPUT AND PUBLIC PATH
===============================================================================

Before implementation, record the exact bytes of the tracked/generated `go.mod` and recursive `.go` files used
by the current regeneration guard.

After implementation:

- all pre-existing generated `go.mod` and `.go` bytes must be byte-identical;
- `make regenerate` must use the same proved `SafeProgram` path;
- `make regen-guard` must pass;
- no generated file may gain a C4-only alias fixture unless the existing public artifact already calls for it;
- no plugin, OCaml, shell, Docker, or sink code may implement type resolution or conversion semantics.

Alias differential tests may use disposable outputs. They must not change the canonical published image.

===============================================================================
14. DELETION AND NO-RESIDUE RULE
===============================================================================

After the new path is proved and used, delete all obsolete C4 predecessor residue, including as applicable:

- `EIntConvert`;
- `EFloatConvert`;
- `EComplexConvert`;
- old constructor-specific recursive cases;
- old constructor-specific index branches;
- old renderer branches;
- old conversion fixture helpers;
- old comments that say conversion targets are semantic AST tags;
- stale C4a/C4b active status text;
- stale claims that aliases first arrive in C5;
- compatibility wrappers with no approved consumer;
- duplicate type-name spelling tables.

Search the full tracked tree, not only `.v` files. Inspect each hit in context.

Do not keep dead code to reduce the diff.

===============================================================================
15. ACCEPTED C4 CLAIM SURFACE
===============================================================================

The C4 Implementation Review will assess these material claims:

1. **Intrinsic source identity**
   - every live conversion target contains a valid bounded source identifier;
   - only the exact sixteen approved target names are representable;
   - source spelling is retained independently of semantic type.

2. **Compiler-owned binding**
   - raw syntax contains no semantic target tag;
   - `GoCompile` alone resolves current source type names through the current predeclared context;
   - `byte`/`rune` retain source identity and resolve to `uint8`/`int32` semantics.

3. **One indexed semantic path**
   - every type-name occurrence has one retained identity and one exact fact;
   - conversion expression facts consume retained type-name and operand facts;
   - one `elaborate` result mints the only compilation capability.

4. **One conversion authority**
   - all explicit constant conversions route through `GoTypes.convert_const`;
   - all old family-specific source constructors and peer paths are deleted;
   - success and failure remain exact.

5. **Source-correct output and diagnostics**
   - rendering and reports preserve selected source names;
   - semantic aliases do not force canonical semantic spellings;
   - all prior generated source bytes remain unchanged.

6. **Trust and scope**
   - no assumptions, trusted parser, host semantic code, second AST, custom collection, or later language scope;
   - C5 work remains absent except the explicit alias-timing amendment in this contract.

===============================================================================
16. BLOCKING DEFECT CLASSES
===============================================================================

Any of these blocks C4:

- a semantic integer/float/complex/`GoType` tag remains in raw conversion syntax;
- the old and new conversion constructors coexist;
- arbitrary or qualified type names become representable without exact call/scope semantics;
- `bool`, `string`, `uintptr`, interface names, or user types become representable but valid Go cases are rejected;
- source name lookup exists outside the one compiler authority;
- rendering chooses a spelling from semantic type rather than raw source syntax;
- diagnostics lose `byte`/`rune` spelling;
- type-name facts copy syntax, accept foreign keys, omit live refs, or recompute on query;
- expression facts recursively recompute an already indexed operand;
- `GoTypes` hides a second source-name resolver;
- a specification helper becomes a peer production compiler;
- a second AST walk, type side index, parser, sort, custom map, or copied tree is added;
- exact soundness/completeness is replaced by examples, bounds, or fuel;
- a rejected program can mint `CompilableProgram`, `SafeProgram`, or `DirectoryImage`;
- existing generated source bytes drift;
- any C5 rune-literal or `uintptr` work enters the checkpoint;
- current permanent documents preserve conflicting C4/C5 authority.

===============================================================================
17. EVIDENCE REQUIRED AT HUMAN IMPLEMENTATION REVIEW
===============================================================================

The final report and repository must provide:

- the exact contract path, hash, baseline, and candidate range;
- a file-level change summary;
- the one source-name authority and its identifier/name exactness theorems;
- the exact index child/ref/domain facts for type-name occurrences;
- the compiler resolver and total exact type-name fact query;
- universal resolver facts for all sixteen names;
- the `byte`/`uint8` and `rune`/`int32` source-distinct/semantic-equal proofs;
- the exact production expression-fact theorem against the declarative source semantics;
- invalid-conversion diagnostic soundness, completeness, multiplicity, ordering, and anchor proofs;
- renderer/denotation proofs over source type names;
- evidence that the public renderer/materializer still consumes only `SafeProgram` from the one retained
  elaboration;
- full pinned-Go differential results;
- zero project assumptions and the updated readable assumption gate;
- standard-collection and no-second-traversal audits;
- exact generated-byte comparison;
- all required build, e2e, check, regeneration, and staged-hook results;
- a full-tree old-constructor and stale-authority search;
- current permanent documentation.

===============================================================================
18. FORBIDDEN OVERREACH
===============================================================================

Do not add:

- `uintptr`;
- rune literal syntax or a rune constant kind;
- general type declarations or user-defined types;
- variables, calls, selectors, parameters, results, imports, or packages beyond the current shape;
- qualified type-name syntax;
- unresolved-name diagnostics for unrepresentable names;
- `bool`, `string`, interface, pointer, array, struct, function, slice, map, or channel conversion targets;
- shadowing machinery with no live source declaration;
- a typed or resolved AST;
- a second AST, parser, token tree, round-trip model, or host parser;
- source semantics in OCaml, shell, Docker, or Go helpers;
- a second compiler, checker, renderer, emitter, or publication path;
- custom maps, sets, sorting, or collection wrappers where the pinned standard library suffices;
- fuel, fixed bounds, trusted shortcuts, admitted proofs, axioms, or test-only correctness claims;
- broad physical module reorganization reserved for C6;
- unrelated cleanup not required to make C4 exact and current.

===============================================================================
19. WORK ORDER
===============================================================================

After the authority commit:

1. Record pre-change generated-source hashes/bytes and the baseline gate count.
2. Add the intrinsic source-name foundation and its proofs.
3. Add the raw type syntax and replace all conversion constructors.
4. Extend `GoIndex` with exact type-name occurrence identity.
5. Add compiler resolution and the sealed type-name fact table.
6. Refactor expression semantics so production consumes retained target and operand facts and calls
   `GoTypes.convert_const` once.
7. Update exact source validity, diagnostics, capability provenance, and all related proofs.
8. Update rendering and independent denotation proofs from source type syntax.
9. Migrate fixtures and e2e witnesses; add focused alias scars and pinned-Go differentials.
10. Delete all old conversion paths and stale authority prose.
11. Update permanent docs, collection audit, assumption gate, and status files.
12. Run the full verification set in section 20 on the complete implementation tree.
13. Inspect the complete checkpoint diff from the contract commit's parent to the implementation head.
14. Commit coherent implementation changes. Prefer a small number of root-based commits. Do not create a commit
    for each proof repair.
15. Capture the exact implementation head SHA.
16. Update `.review/NEXT_STEPS.md` and `.review/SOURCE_FOREST_STATUS.md` to state:
    - C4 implementation candidate complete;
    - baseline and exact implementation head;
    - the human review range starts at the baseline and ends at the final freeze commit;
    - human Implementation Review pending;
    - automatic Codex review disabled;
    - C5 forbidden.
17. Keep `.review/REVIEW_REQUEST.md` closed.
18. Commit the status files as:

    `review(final): C4 — freeze source type-name candidate`

    That commit is the review head. The file may call it "this freeze commit"; report its exact SHA after Git
    creates it. Do not add another self-referential status commit merely to write its own SHA into the file.
19. Run the required final checks, including staged/pre-commit checks, on the exact freeze commit. If a repair is
    needed, make the repair, refresh the status if material facts changed, create a new freeze commit, and repeat
    the checks. Only the final passing freeze commit is the candidate head.
20. Push the final frozen candidate to `main` without force.
21. Report and stop.

Do not begin C5 after the checks pass.

===============================================================================
20. REQUIRED VERIFICATION
===============================================================================

Run and report all of these from a clean supported environment:

```text
make prove
make e2e
make check
make regenerate
make regen-guard
git diff --check
```

Run the repository's staged pre-commit verification on the complete candidate.

Also run and report:

- the readable load-bearing assumption gate with its exact new count;
- the whole-theory closure audit and all gate self-tests;
- the pinned-Go C4 differential matrix;
- exact pre/post comparison of tracked/generated `go.mod` and recursive `.go` bytes;
- a full tracked-tree search for the old conversion constructors and old family-specific source paths;
- a full tracked-tree search for `TByte`, `TRune`, `IByte`, `IRune`, C5 rune-literal work, and `uintptr` additions;
- a full tracked-tree search for duplicate source-name lookup/spelling tables;
- collection audit confirmation that only approved standard maps/lists are used;
- one-index/one compiler-visit production call-path evidence;
- final `git status --short` and `git log --oneline` for the checkpoint range.

A green command is evidence only for the claim it checks. Do not use command success as a substitute for the
universal theorems above.

===============================================================================
21. STOP AND REPORT
===============================================================================

Do not request Codex review. Do not set `state: requested`. Do not run a bounded confirmation. Do not claim C4 is
human-approved.

After pushing the complete candidate, return one concise report with:

- baseline SHA;
- contract commit SHA;
- contract SHA-256;
- candidate head SHA and full range;
- pushed branch;
- exact files added, changed, and deleted;
- the final source/semantic architecture;
- the sixteen live target names and exact alias mapping;
- load-bearing theorem names grouped by source names, index/facts, conversion/diagnostics, rendering, and
  capability provenance;
- pinned-Go differential result;
- assumption/gate count and result;
- every required verification command and result;
- exact generated-byte identity result;
- old-path/no-C5 residue search result;
- any honest limitation or conflict;
- state: awaiting Rob's human C4 Implementation Review;
- C5 not started.

Then stop. Do not repair or extend the checkpoint without a later explicit Rob directive.
