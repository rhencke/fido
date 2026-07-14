Claude Code milestone: close the remaining boundary gaps, then land the first Go type-system foundation

THIS FILE IS THE BINDING MILESTONE CONTRACT.

Before making any implementation change:

1. Replace the tracked repository file `.review/NEXT_STEPS.md` with this directive VERBATIM.
   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not “improve” its architecture while copying it.
2. Commit `.review/NEXT_STEPS.md` as the opening commit of this milestone, before implementation.
3. Record that contract commit SHA.
4. Treat `.review/NEXT_STEPS.md` as the binding scope, architecture, threat model, algorithm, and acceptance contract for every implementation change and Codex review in this milestone.
5. After the contract commit, issue this exact Claude Code command:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

The loop is intentionally authorized for this milestone.

The loop must:

- work only toward the current `.review/NEXT_STEPS.md`;
- run the Codex stop review against that binding contract;
- repair objective implementation defects that preserve the contract;
- never broaden scope or redesign a selected architecture merely to satisfy Codex;
- stop immediately on an architectural conflict, notify the user, and wait;
- stop when Codex is green;
- after Codex is green, run the complete final verification, commit the final checkpoint, notify the user, stop the loop, and wait.

“Codex green” means the implementation is airtight against this contract. It does not mean “the repository is maximally complete” or “Codex can imagine no future feature.”

If a real defect cannot be fixed without changing this milestone’s architecture, scope, guarantees, threat model, responsibility boundaries, type model, or selected algorithm:

- classify it as an ARCHITECTURAL CONFLICT;
- do not implement an alternative autonomously;
- notify the user;
- stop the loop;
- wait for review.

Milestone purpose

This is one bounded milestone with two ordered parts:

A. Close the remaining review findings in the sink and staged-index verification boundary.
B. Introduce the first permanent Go type-system foundation for the already-admitted bool/int fragment.

Part B must not begin by preserving a known defect from Part A. Both parts belong to this one milestone and one final review checkpoint.

No imports.

No new emitted language syntax.

The committed generated `go.mod` and every committed generated `.go` file must remain byte-identical throughout the type-foundation work.

Standing project law

Ruthless correctness or ruthless deletion.

Incomplete representable scope is acceptable.

Incorrect, approximate, duplicated, transitional, fail-open, or half-built foundations are not.

The AST is the IR.

There is:

- one raw AST per `.go` file;
- one `GoProgram`;
- no copied compiled AST;
- no typed AST;
- no target AST;
- no text IR;
- no separate lowering tree;
- no tokenizer;
- no lexer;
- no parser;
- no AST -> output -> AST round trip;
- no handwritten OCaml compiler semantics;
- no handwritten OCaml typechecker;
- no handwritten OCaml safety reasoning;
- no handwritten OCaml renderer.

The current `.review/NEXT_STEPS.md` is binding. Codex is an implementation auditor, not the architect.

No feature growth beyond the type foundation described here.

Do not add:

- imports;
- identifiers;
- variables;
- constants declarations;
- type declarations;
- user-defined ordinary functions;
- calls;
- parameters or results;
- strings;
- floats;
- runes;
- fixed-width integer types;
- unsigned integer types;
- pointers;
- arrays;
- slices;
- maps;
- structs;
- interfaces;
- channels;
- concurrency;
- control flow;
- conversions;
- assignments;
- another AST or IR.

The type foundation initially contains exactly the types already needed by the current fragment:

- bool;
- int.

PART A — close the remaining review findings

1. Scope recursive dirty-tree inspection to the Go-discovered namespace

The sink must not recurse indiscriminately into every foreign directory.

The current use case is generation into a Git repository root. The sink must never inspect, classify, reject because of, or delete metadata inside `.git` or equivalent ignored directory trees.

Use one directory-recursion policy aligned with the current Go `./...` discovery model and the existing intrinsic `FilePath` directory exclusions.

While recursively inspecting for:

- foreign `.go`;
- foreign or nested `go.mod`;
- nested `.fido`;
- abandoned `.fido-tmp-v1` files;
- stale generated `.go`;

apply these rules to a directory basename:

A. Exact root `.fido`

- `<root>/.fido` is the one control namespace.
- Validate its exact shape separately.
- Never recurse through it as ordinary tree content.

B. Nested `.fido`

- A `.fido` encountered in a directory that is otherwise inside the traversed Go-discovered namespace is an error, regardless of filesystem type.
- Reject and preserve it.
- Do not recurse into it.

C. Go-ignored directory names

Do not recurse into a directory whose basename:

- begins with `.`;
- begins with `_`;
- is exactly `testdata`;
- is exactly `vendor`.

Treat those trees as opaque foreign non-Go state.

Do not inspect, classify, clean, or reject because of files beneath those skipped directories.

This is the catchall that keeps Fido out of:

- `.git`;
- `.hg`;
- `.svn`;
- editor caches;
- hidden tool directories;
- underscore-private directories;
- Go-ignored `testdata`;
- Go-ignored `vendor`.

D. Do not over-skip ordinary directories

Do not skip a directory merely because its name is outside Fido’s deliberately narrow generated `FilePath` grammar if Go may still discover it.

For example, an ordinary visible foreign directory with an uppercase, hyphenated, or otherwise non-Fido-generated name may still contain Go input selected by `go build ./...`.

The foreign-Go scan must continue to detect applicable foreign `.go` and nested `go.mod` in ordinary visible directories.

Do not confuse:

- the narrow domain Fido may generate into; with
- the broader visible tree Go may compile.

2. Scope the reserved temporary suffix to possible Fido final paths

The reserved suffix remains:

  .fido-tmp-v1

The simple sibling-temp architecture remains binding.

A suffix-bearing regular file is Fido-owned as an abandoned temporary only if removing the suffix yields a path Fido could actually have staged:

- exactly the root `go.mod`; or
- a relative `.go` path accepted by the sink’s defensive `filepath_ok`, which must remain equivalent to the intrinsic `FilePath` output domain.

Examples of owned temporary forms:

  go.mod.fido-tmp-v1
  main.go.fido-tmp-v1
  sub/main.go.fido-tmp-v1

A suffix-bearing entry that does not map to one of those final forms is not Fido-owned.

For example:

  notes.fido-tmp-v1
  .git/refs/heads/release.fido-tmp-v1
  visible-dir/arbitrary.bin.fido-tmp-v1

must not be deleted.

Within the traversed namespace, a reserved-looking but non-mappable suffix entry should be preserved and should make the run refuse clearly rather than being silently adopted as Fido state.

A suffix entry under a skipped/opaque directory is not inspected at all.

Keep two-phase recovery:

1. complete fail-closed scan and collect valid abandoned Fido temps, deleting nothing;
2. only after the whole scan succeeds, re-lstat and remove those collected regular temps.

Do not reintroduce:

- stage records;
- nonces;
- stage directories;
- record parsing;
- manifests;
- device/inode identity;
- mount identity;
- a central staging directory.

3. Add repository-metadata regression gates

Add a regression tree containing at least:

  .git/refs/heads/release.go
  .git/refs/heads/release.fido-tmp-v1
  .git/logs/refs/heads/release.fido-tmp-v1

Use distinctive byte contents.

A sink run must:

- succeed when no visible foreign Go/module input exists;
- not reject because of `.go` metadata under `.git`;
- not classify the suffix-bearing Git metadata as Fido temp state;
- not alter or remove any byte beneath `.git`.

Add equivalent coverage for at least one generic hidden directory and one underscore directory.

Retain the existing nested-visible-`.fido` rejection tests.

Clarify in documentation:

- nested `.fido` is rejected in the traversed Go-discovered namespace;
- skipped Go-ignored/hidden directory trees are opaque and are not inspected.

4. Make the entire pre-commit path staged-tree authoritative

The pre-commit hook must verify the proposed commit—the Git index—and must not trust ordinary working-tree source bytes, gate scripts, build files, or generated files.

The current staged generated-byte comparison is not enough if the hook executes gate implementations from the unstaged working tree.

Required flow:

1. Locate the repository root.
2. Create one temporary directory.
3. Export the Git index exactly once into that directory using `git checkout-index`.
4. From that point onward, use the exported staged snapshot as the authoritative source tree.
5. Execute the staged copies of:
   - the OCaml-origin gate;
   - the generated-output policy gate;
   - the staged/generated comparison implementation;
   - any helper scripts.
6. Use the exported staged tree as the complete Buildx context.
7. Run the complete proof gate.
8. Run the complete Go e2e.
9. materialize the pristine `generated-artifact` built from that staged context;
10. recursively compare the staged snapshot’s generated root `go.mod` and every staged `.go` at every depth against the pristine artifact:
    - exact relative path set, both directions;
    - exact bytes;
    - regular-file shape;
    - canonical generated file mode.

Do not execute a working-tree script merely because the data it reads comes from the index.

A staged bad gate script or staged bad OCaml boundary must be the version the hook evaluates.

Implementation may parameterize the staged scripts with the exported root path. It must not require a `.git` directory inside the exported tree to inspect source contents.

5. Run the full staged verification on every ordinary commit

Delete the manually maintained conditional path list that decides whether Buildx verification is needed.

Every ordinary commit that does not use `--no-verify` must:

- export the staged tree;
- run the full cached proof gate;
- run the full cached Go e2e;
- compare staged generated output against the pristine generated layer.

Buildx caching is the optimization.

A manually maintained “relevant input path” list is not an authority.

This also ensures that the first normal commit after a prior `--no-verify` bypass re-establishes the generated-output invariant.

The prototype escape remains honest:

  git commit --no-verify

may bypass the hook.

Do not hide or remove that documented limitation. Future PR CI is still future work and is not part of this milestone.

6. Do not auto-stage or mutate the working tree from pre-commit

The staged verification hook must:

- not regenerate into the working tree;
- not alter the index;
- not run `git add`;
- not auto-fix generated files.

On mismatch it must fail with a clear command such as:

  make regenerate
  git add -A -- go.mod ':(top,glob)**/*.go'
  git commit

`make regenerate` remains the explicit working-tree update command and continues to use the pristine generated Buildx layer plus the same sink.

7. Delete the OCaml line-count cap

Delete the hard-coded line-count ceiling from `tools/ocaml-origin-gate.sh`.

Delete documentation and status prose that advertises the current sink’s line count.

Retain the useful gates:

- exact allowlist of handwritten OCaml files;
- filesystem-only files may not inspect Rocq terms;
- the bridge may not inspect program/AST/type/safety structures;
- deleted-backend hallmark names remain forbidden;
- behavioral tests exercise the live boundary.

A numeric source-line ceiling is not a correctness invariant.

Do not replace it with another arbitrary size metric.

8. Make the generated layer independent of committed generated bytes by construction

The pristine `generated-module` Buildx layer must not depend on committed `go.mod` or committed `.go` files.

Update `.dockerignore` so the ordinary build context excludes:

- the tracked root `go.mod`;
- tracked generated `.go` files recursively.

The generation stage must derive the pristine module only from:

- certified `.v` sources;
- Dune/project files;
- the transport plugin/sink;
- witness definitions;
- pinned toolchains;
- other genuine generation inputs.

Do not copy committed generated bytes into any generation/proof authority.

The committed generated files remain reviewed derived artifacts verified against the pristine layer.

9. Canonical tracked generated file mode

Require tracked generated `go.mod` and generated `.go` files to be regular files with canonical non-executable mode.

Use exact Git mode:

  100644

Reject:

- executable generated Go;
- symlinks;
- gitlinks;
- special/nonregular representations.

The pristine comparison remains primarily path-set + byte equality, but the repository policy gate must also enforce the canonical staged Git mode.

PART B — first permanent Go type-system foundation

10. Mine Git history as a quarry, not as code to resurrect wholesale

Before implementing the new type foundation, inspect the pre-deletion history for semantic knowledge and counterexamples.

Useful reference points include:

  git show e1954d3f84878d844a382dbdea621e4c69d32fd5:CoreType.v
  git show d5646d646fc5046b54eb04b664bed7035b763786:GoTypes.v
  git show d5646d646fc5046b54eb04b664bed7035b763786:GoAst.v

Use them to recover:

- exact range lemmas;
- the distinction between untyped constants, typed values, and runtime values;
- exhaustive per-type policies;
- useful Go-accept/Go-reject counterexamples;
- proof techniques that still fit the current architecture.

Do not cherry-pick or restore those files wholesale.

Do not resurrect:

- `Surface`;
- `TypedIR`;
- elaboration into a copied program;
- a second expression/declaration hierarchy;
- the old broad `PTy`/`ptype` supported-subset classifier;
- `TargetConfig`;
- portable-32-bit restrictions;
- raw/string rescue constructors;
- old printer/parser machinery;
- historical proof scaffolding disconnected from the live compiler.

No historical code is trusted merely because it once existed.

Restate every retained idea in the current one-AST architecture.

11. Create one Go type authority

Introduce a fresh certified module, preferably `GoTypes.v`, with exactly one permanent type universe:

  Inductive GoType : Type :=
  | TBool
  | TInt.

No other type constructor in this milestone.

Do not add placeholder constructors for future types.

Adding a future constructor must be a reviewed semantic milestone that updates:

- static typing;
- representability;
- compiler facts;
- safety/value semantics;
- rendering correspondence;
- tests;
- documentation.

`GoType` is not raw AST syntax.

Current literal expressions remain untyped raw syntax in `GoAST`.

12. Represent exact untyped constant values

Introduce one exact constant-value domain for the current raw literal fragment:

  Inductive GoConst : Type :=
  | CBool : bool -> GoConst
  | CInt  : Z -> GoConst.

Names may differ if the responsibilities remain exact.

Define one total constant interpretation of the current expressions:

  const_value : GoExpr -> GoConst

with exact behavior:

  EBool b -> CBool b
  EInt n  -> CInt (Z.of_N n)
  ENeg n  -> CInt (- Z.of_N n)

This is untyped constant meaning.

Do not range-check integer constants here.

Go integer constants are exact values; representability is a separate contextual obligation.

Prove at minimum:

- totality by construction;
- determinism;
- `EInt 0` and `ENeg 0` have the same constant value;
- positive and negative values are exact.

Do not create a duplicate constant evaluator in `GoCompile`, `GoSafe`, or `GoRender`.

13. Define default types separately from constant values

Define:

  const_default_type : GoConst -> GoType

with:

  CBool _ -> TBool
  CInt  _ -> TInt

The raw literal remains an untyped constant.

The default type is the type chosen in a context that requires a typed value.

Do not bake `TInt` directly into the raw `EInt`/`ENeg` constructors.

Do not claim the raw expression itself was syntactically typed.

This distinction is foundational for future:

- assignments;
- variables;
- function arguments;
- conversions;
- typed constants;
- additional numeric types.

14. Define representability as one type-directed authority

Define one declarative relation or proposition:

  ConstRepresentable : GoType -> GoConst -> Prop

with exact current rules:

- every `CBool b` is representable as `TBool`;
- no integer constant is representable as `TBool`;
- no boolean constant is representable as `TInt`;
- `CInt z` is representable as `TInt` iff:

    int_min <= z <= int_max

using the existing single `Ints` authority.

Define an executable reflector/checker:

  const_representableb : GoType -> GoConst -> bool

and prove exact reflection:

  const_representableb t c = true <-> ConstRepresentable t c

Do not leave a second integer-range checker elsewhere.

Delete or route every current int-literal admissibility decision through this authority.

15. Define use-context resolution

Introduce one current expression-use context:

  Inductive ExprUse : Type :=
  | UsePrintlnArg.

Define one exhaustive per-type use policy:

  UseAllows : ExprUse -> GoType -> Prop

or an equivalent reflected boolean.

For this milestone:

- `UsePrintlnArg` allows `TBool`;
- `UsePrintlnArg` allows `TInt`.

No other type exists.

Define the declarative resolved-typing relation:

  ResolveExpr : ExprUse -> GoExpr -> GoType -> Prop

It must express:

1. the expression denotes one exact untyped constant;
2. the constant’s default type is `t`;
3. the use context allows `t`;
4. the constant is representable as `t`.

Provide an executable resolver, for example:

  resolve_expr : ExprUse -> GoExpr -> option GoType

and prove:

- soundness;
- completeness;
- determinism;
- no successful resolution at the wrong type.

Equivalent formulations are acceptable if they preserve one authority and the untyped-constant/defaulting distinction.

Do not create a typed-expression AST.

Do not copy the original expression into a “resolved expression” record.

16. Replace the old ExprOk hierarchy

Delete the old parallel static-admissibility family after the new type authority is live:

- `ExprOk`;
- `StmtOk`;
- `DeclOk`;
- `FileOk`;
- `expr_ok`;
- `stmt_ok`;
- `decl_ok`;
- `file_ok`;
- their reflection lemmas, except reusable proof lemmas moved under the new authority.

Introduce whole-current-fragment typing judgments:

  StmtTyped
  DeclTyped
  FileTyped
  ProgramTyped

Exact current rules:

- `SPrintln args` is typed iff every argument resolves under `UsePrintlnArg`;
- `DMain body` is typed iff every statement is typed;
- a file is typed iff every declaration is typed;
- a program is typed iff every mapped file is typed;
- the empty file map is typed vacuously.

Provide executable reflected checkers and prove exact equivalence.

There must be one live static type path.

Do not keep the old `ExprOk` system “temporarily” beside the new one.

17. Integrate typing into GoCompile over the same AST

`GoCompile` remains the one whole-program compiler authority.

It must now consume the `ProgramTyped` judgment as the static typing foundation.

The whole program remains valid iff:

- every represented file/declaration/statement/expression is typed through the new type system;
- every package directory has exactly one `main`;
- all existing whole-program structural rules hold;
- the empty program remains valid.

`CompilationFacts p` must expose that the same `p` is typed.

Acceptable shapes include:

- a `cf_program_typed : ProgramTyped p` field; or
- an immediate canonical theorem/projection from the compiled evidence.

Do not store:

- a typed AST;
- a copied file map;
- per-node syntax duplicates;
- a second program;
- a target tree.

Because all current expressions are closed constants, do not introduce a large expression-annotation map merely to cache results that are directly computable.

Future symbols/types may enrich `CompilationFacts` when a construct actually requires them.

18. Preserve exact executable compiler proofs

Update the executable compiler so it succeeds exactly for the revised declarative `GoCompile`.

Retain or re-prove:

- `prog_ok_iff`;
- compiler soundness;
- compiler completeness;
- rejected program yields no `CompilableProgram`;
- all-or-nothing whole-program behavior;
- empty-program acceptance;
- exact package-main-count rejection.

The current type failure is still only integer default-type representability failure.

Do not invent a broad error taxonomy.

`ErrIntOverflow` may remain if it stays exact.

A narrowly named type error is also acceptable if it reflects only the current live failure and does not pretend future completeness.

19. Make GoSafe consume the same GoType authority

There must not be one compiler type universe and a separate safety/runtime type universe.

Retain the current runtime values:

  Inductive GoValue :=
  | VBool : bool -> GoValue
  | VInt  : Z -> GoValue.

Define:

  value_type : GoValue -> GoType

with:

  VBool _ -> TBool
  VInt  _ -> TInt

Prefer defining runtime expression evaluation from the single exact constant interpretation, for example through one conversion:

  const_to_value : GoConst -> GoValue
  eval_expr e := const_to_value (const_value e)

or an equivalent nonduplicating formulation.

Prove:

  eval_expr_resolved_type :
    forall use e t,
      ResolveExpr use e t ->
      value_type (eval_expr e) = t.

Also preserve:

- exact integer values;
- boolean values;
- zero-sign agnosticism;
- `EInt 0` and `ENeg 0` evaluate identically.

Do not index `GoValue` by `GoType` in this milestone unless it demonstrably makes the complete implementation and heterogeneous `println` traces smaller and clearer.

Do not introduce existential packaging merely for aesthetic type indexing.

Use taste and proof ergonomics, but keep one `GoType` authority.

20. Preserve the direct renderer and connect it to resolved typing

Do not change emitted bytes.

Do not add a parser, lexer, token layer, or round-trip theorem.

Keep the existing direct renderer and `render_expr_denotes`.

Add a root theorem connecting the current three authorities, for example:

  render_resolved_expr_denotes :
    forall e t,
      ResolveExpr UsePrintlnArg e t ->
      RenderedPrimitiveDenotes (render_expr e) (eval_expr e)
      /\ value_type (eval_expr e) = t.

An equivalent theorem split into smaller load-bearing theorems is acceptable.

The theorem must establish:

- the rendered spelling denotes the exact runtime value;
- that value has the statically resolved type.

Do not claim this is a theorem about the real Go parser.

Real-Go acceptance remains external adequacy, exercised differentially.

21. Required boundary and range fixtures

Add kernel-checked positive fixtures for:

- `EBool true` resolves to `TBool`;
- `EBool false` resolves to `TBool`;
- `EInt 0` resolves to `TInt`;
- `ENeg 0` resolves to `TInt`;
- `EInt 0` and `ENeg 0` have equal constant values;
- maximum `int` resolves;
- minimum `int` resolves;
- a mixed `println(true, 42, -1)` statement is typed;
- `println()` is typed;
- an empty file is typed;
- an empty program is typed.

Add negative fixtures for:

- `int_max + 1` fails resolution as `TInt`;
- `int_min - 1` fails resolution as `TInt`;
- boolean constants do not resolve as `TInt`;
- integer constants do not resolve as `TBool`;
- an out-of-range argument makes its statement/file/program fail typing;
- the whole program is rejected before rendering/emission.

Use the existing `Ints` constants. Do not duplicate numeric bounds.

22. Required theorem surfaces

Add or update the axiom-free public gate for the load-bearing new statements.

At minimum, gate meaningful representatives of:

GoTypes

- `const_value` zero-sign equality;
- default type exactness;
- representability reflection;
- expression-resolution soundness;
- expression-resolution completeness;
- resolution determinism;
- statement/program typing reflection;
- max/min accepted;
- overflow/underflow rejected.

GoCompile

- revised `prog_ok_iff`;
- compiler soundness;
- compiler completeness;
- rejection implies no compilation;
- empty program accepted under the new typing authority.

GoSafe

- resolved expression evaluates to a value of the resolved `GoType`;
- zero-sign-agnostic value theorem.

GoRender

- rendered resolved expression denotes the exact value and has the resolved type;
- existing decimal/header/ASCII facts remain.

The complete whole-certified-theory assumption audit must cover the new module automatically through exact Dune/module coverage.

No axiom, parameter, admitted proof, functional extensionality, or unchecked primitive.

23. No generated output delta

This milestone introduces a type foundation only.

It must not change:

- rendered `go.mod`;
- rendered `main.go`;
- generated relative path set;
- stdout;
- stderr;
- exit status;
- gofmt output.

The tracked generated module must remain byte-identical to its pre-milestone bytes.

The staged-index verification should enforce this naturally.

If the type foundation appears to require an output change, stop and classify the issue. Do not hide an output delta inside this milestone.

24. No language-growth escape hatch

Do not add `TString` because `println` will eventually support strings.

Do not add other type constructors from history.

Do not add generic “unknown,” “unsupported,” “opaque,” or “raw” types.

Do not add an untyped AST constructor or fallback.

The next type constructor must arrive only with the syntax and complete semantic obligations that need it.

This milestone’s permanent type universe is exactly:

  TBool
  TInt

25. Documentation updates

Update all active documentation and source headers to match the resulting architecture:

- `.review/NEXT_STEPS.md`;
- `ARCHITECTURE.md`;
- `CLAUDE.md`;
- `README.md`;
- `PROGRESS.md`;
- `PAINFUL_LESSONS.md`;
- `Makefile`;
- `Dockerfile`;
- `dune`;
- `GoAST.v`;
- new `GoTypes.v`;
- `GoCompile.v`;
- `GoSafe.v`;
- `GoRender.v`;
- `GoEmit.v` if its comments name the compile facts;
- plugin/sink headers;
- pre-commit/gate scripts.

Required truths:

A. One AST

Raw `GoExpr` remains untyped syntax.
There is no typed AST or copied program.

B. One type authority

`GoType` initially contains exactly `TBool` and `TInt`.

C. Untyped constants

Current literals denote exact untyped `GoConst` values.
Defaulting and representability happen in a use context.

D. Compilation

`ProgramTyped` is part of whole-program `GoCompile`.
`CompilationFacts` exposes typing evidence over the same program.

E. Safety

Runtime values use the same `GoType` authority.
Evaluation preserves resolved type.

F. Rendering

The direct renderer is unchanged.
Rendered resolved expressions denote the exact value and agree with the static type.
No parser or round trip exists.

G. Filesystem

Hidden/underscore/testdata/vendor directory trees are opaque to scanning.
Visible nested `.fido` is rejected.
Temporary ownership is limited to suffixes that map to root `go.mod` or an intrinsic `FilePath`.

H. Pre-commit

The complete verifier runs on every ordinary commit.
Every gate implementation and input comes from the exported staged snapshot.
No working-tree source is trusted.
`--no-verify` remains an explicit prototype bypass.

I. Trusted OCaml

Remove numeric line-count claims.
Keep semantic responsibility boundaries.

26. Painful lessons update

Keep `PAINFUL_LESSONS.md` concise.

Add or amend only durable lessons:

- Literal constants are not immediately typed values. Preserve exact untyped constant meaning, then default/resolve in context.
- A type system is evidence over the one AST, not permission to recreate `TypedIR`.
- Git history is a semantic quarry, not a branch to resurrect wholesale.
- The generated `FilePath` domain and the foreign Go-discovery scan have different responsibilities: do not skip visible directories Go may compile merely because Fido would not generate their names.
- A public temp suffix is acceptable under the chosen threat model, but ownership must still map to a possible Fido final path.
- A staged-tree verifier is only staged-authoritative when the gate implementations themselves come from the staged tree.
- A source-line cap is not a correctness invariant.

Do not turn the file into a commit diary.

27. Required build and regression behavior

The final `make check` must cover:

- complete proof gate;
- whole-theory assumption audit;
- existing Fido Emit provenance tests;
- existing sink crash/recovery/foreign-file tests;
- hidden/VCS metadata traversal regression;
- scoped temp-suffix ownership;
- visible nested `.fido` rejection;
- complete-image staging;
- exact Buildx generated-module;
- tracked generated-output policy;
- Go e2e;
- empty program;
- multi-package differential;
- no-main/duplicate-main rejection;
- nonblocking vet;
- type-system positive/negative kernel fixtures;
- no generated-byte delta.

The pre-commit self-test or documented reproducible gate must demonstrate:

- staged bad OCaml + safe working-tree OCaml is rejected;
- staged bad gate script + safe working-tree script cannot bypass;
- a stale/missing/modified recursive staged generated file is rejected;
- a docs-only normal commit still runs the complete cached verification;
- the hook never mutates the working tree or index.

Do not add flaky timing-dependent tests.

28. Acceptance criteria

The milestone is complete only if all applicable conditions hold.

Workflow

- This directive was copied verbatim to `.review/NEXT_STEPS.md`.
- The contract was committed before implementation.
- The exact `/loop 5m ...` command was started after the contract commit.
- Codex reviewed against `.review/NEXT_STEPS.md`.
- Codex is green.
- No architectural conflict was silently implemented.
- The loop stopped after notification.

Sink boundary

- No recursion into hidden, underscore, testdata, or vendor directory trees.
- `.git` metadata with `.go` or `.fido-tmp-v1` names is preserved and ignored.
- Visible nested `.fido` rejects.
- Visible foreign Go/module inputs still reject.
- A temp is owned only when stripping the suffix yields root `go.mod` or a valid intrinsic `.go` path.
- Non-mappable suffix entries are preserved and refuse in traversed scope.
- Two-phase recovery remains.
- No records/nonces/stage dirs/parser returned.
- Complete image stages before install.
- Existing crash/cleanup semantics remain honest.

Pre-commit

- The Git index is exported exactly once.
- The exported staged tree is the source for every gate implementation and source byte.
- Full cached prove + e2e + generated comparison runs on every ordinary commit.
- No conditional relevance path list remains.
- Recursive generated path set and bytes match exactly.
- Generated Git modes are exactly `100644`.
- No working-tree mutation or auto-stage.
- `--no-verify` remains documented.
- The OCaml line cap is deleted.
- Committed generated files are excluded from Buildx generation inputs.

Type foundation

- Fresh one-authority `GoType` with exactly `TBool` and `TInt`.
- Exact `GoConst` with bool and arbitrary-precision integer values.
- One `const_value`.
- One default-type authority.
- One type-directed representability authority.
- One reflected `ResolveExpr`.
- One `StmtTyped`/`DeclTyped`/`FileTyped`/`ProgramTyped` path.
- Old `ExprOk` hierarchy deleted.
- `GoCompile` consumes the new typing evidence.
- `CompilationFacts` exposes typing evidence over the same program.
- No typed AST, copied map, or annotation tree.
- `GoSafe` uses the same `GoType`.
- Evaluation preserves resolved type.
- Rendering correspondence includes resolved type.
- Empty program remains valid.
- Boundaries are exact.
- No new type or syntax constructor.
- No generated byte/path/behavior change.

Proof

- All new theorem surfaces are closed.
- Whole-theory audit remains green.
- Module coverage includes the new type module.
- No tracked axiom fixture.
- No source-text axiom scanner.

Documentation

- Every active document matches implementation.
- No stale line count.
- No claim that hidden/VCS trees are recursively inspected.
- No claim that raw literals are immediately typed.
- No old `TypedIR`/second-tree architecture returned.
- PROGRESS remains compact.

29. Completion report

When Codex is green and all criteria pass, report:

- contract commit SHA;
- final implementation commit SHA;
- complete commit range;
- files added, changed, deleted;
- exact directory-recursion policy;
- exact reserved-temp ownership predicate;
- `.git` metadata regression results;
- final staged-index hook algorithm;
- proof that gate implementations come from staged export;
- confirmation full verification runs every normal commit;
- line-cap deletion;
- `.dockerignore` generated-input exclusion;
- generated Git mode policy;
- historical files inspected and which ideas were retained/rejected;
- final `GoType` definition;
- final `GoConst` definition;
- constant interpretation;
- defaulting rule;
- representability relation/checker and reflection theorem;
- expression-use and resolution rules;
- old `ExprOk` code deleted;
- final `ProgramTyped` integration;
- `CompilationFacts` shape;
- GoSafe type-preservation theorem;
- render/type/value correspondence theorem;
- every theorem added or materially changed;
- complete `Print Assumptions` and whole-theory audit results;
- exact generated-module path/byte comparison;
- confirmation generated `go.mod`/`.go` bytes did not change;
- all proof/build/e2e commands and results;
- Codex dispositions;
- confirmation notification sent;
- confirmation loop stopped.

Do not list a retained correctness flaw as a known limitation.

If the contract cannot be implemented correctly, stop the loop, classify the obstacle as an architectural conflict, notify the user, and wait.

30. Hard stop

When Codex is green and final verification passes:

1. Commit the completed checkpoint.
2. Notify the user through the configured phone/completion-notification channel that the checkpoint is ready for review.
3. Stop the `/loop`.
4. Do not infer or begin another milestone.
5. Wait.

Bottom line

The permanent path after this milestone is:

  raw GoExpr
    -> exact untyped GoConst
    -> context resolution/defaulting through one GoType authority
    -> ProgramTyped evidence over the SAME GoProgram
    -> GoCompile / CompilationFacts over that same program
    -> GoSafe values whose type agrees with resolution
    -> unchanged direct renderer whose spelling denotes that value
    -> unchanged certified DirectoryImage
    -> simple sibling-temp dirty-directory sink
    -> pristine generated-module Buildx layer
    -> tracked generated Go verified from the exact staged Git tree

No imports.
No typed AST.
No second IR.
No new emitted syntax.
No generated-byte delta.
