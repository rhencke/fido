Claude Code milestone: reset Codex to the declared threat model, simplify prototype verification, and add exact Go strings

THIS FILE IS THE BINDING MILESTONE CONTRACT.

Before implementation

1. Stop the currently running `/loop`.
   - The prior loop has reached out-of-scope local-Git adversarial hardening.
   - Do not continue addressing new Codex findings under the old review standard.

2. Replace the tracked repository file `.review/NEXT_STEPS.md` with this directive VERBATIM.
   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not “improve” the selected architecture while copying it.

3. Create or replace the tracked file:

   .review/CODEX_REVIEW_POLICY.md

   with the exact policy in the section “Permanent Codex review policy” below.

4. Commit both review files as the opening commit of this milestone, before implementation.

5. Record the contract commit SHA.

6. Replace the locally hacked Codex stop-review prompt used by the automation with the small prompt in the section “Codex stop-review launcher prompt.”
   - Do not keep two active stop-review prompts.
   - The local prompt must defer to the two tracked review files.
   - Record the local prompt path in the completion report.

7. After the contract commit and review-prompt replacement, issue this exact Claude Code command:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

The loop is authorized only for this milestone.

The loop must:

- work only toward `.review/NEXT_STEPS.md`;
- use `.review/CODEX_REVIEW_POLICY.md`;
- repair blocking implementation defects within the declared scope and threat model;
- never expand the threat model merely because a more adversarial scenario can be imagined;
- never redesign an agreed architecture merely to satisfy Codex;
- classify a real concern requiring a contract change as an ARCHITECTURAL CONFLICT;
- stop and notify the user on an architectural conflict;
- stop when there are no blocking findings within scope, even if nonblocking observations remain;
- after Codex is green, run final verification, commit the completed checkpoint, notify the user, stop the loop, and wait.

Milestone purpose

This milestone has three ordered parts:

A. Permanently correct the Codex review mandate.
B. Cull the overbuilt prototype pre-commit review fortress and close one small sink-ordering defect.
C. Add Go string values completely across the existing one-AST pipeline.

The goal is to resume development of a stronger Go through Rocq.

The goal is not to make a repository-local pre-commit hook resistant to a developer deliberately attacking their own verifier.

No imports.

No identifiers.

No variables.

No user-defined functions.

No control flow.

No second AST or IR.

Standing project law

Ruthless correctness or ruthless deletion.

Apply that law to the certified language and its declared operational boundaries.

Do not silently inflate a component’s guarantee.

The AST is the IR.

There is:

- one raw AST per `.go` file;
- one `GoProgram`;
- one Go type authority;
- no typed AST;
- no copied compiled program;
- no target AST;
- no text IR;
- no separate lowering tree;
- no tokenizer;
- no general Go lexer;
- no general Go parser;
- no AST -> output -> AST authority;
- no handwritten OCaml compiler;
- no handwritten OCaml typechecker;
- no handwritten OCaml safety semantics;
- no handwritten OCaml renderer.

Permanent Codex review policy

Copy this section VERBATIM into `.review/CODEX_REVIEW_POLICY.md`.

---

# Fido Codex Review Policy

## Purpose

Codex is an implementation auditor.

Codex is not the product architect.

Codex reviews the current implementation against:

1. `.review/NEXT_STEPS.md`, the binding active-milestone contract;
2. this review policy;
3. the standing repository architecture where the active milestone is silent.

The active milestone wins over older prose when it explicitly changes a decision.

## Review standard follows the component

Different components have different guarantees and threat models.

Do not apply the strongest imaginable adversarial standard to every component.

### Certified language and proof boundary

Review the certified path ruthlessly.

Blocking defects include:

- a false or materially weaker theorem than advertised;
- an axiom, admitted dependency, unchecked assumption, or fail-open proof gate;
- two competing semantic authorities;
- a representable program whose modeled typing, value, safety, rendering, or compiler acceptance disagrees with the declared Go semantics;
- a typed or compiled copy of the AST where the contract requires evidence over one AST;
- an emitted program that the formal compiler accepts but real `go build ./...` rejects;
- a formal compiler rejection of a representable program real Go accepts;
- rendering that does not denote the proved value;
- a certification or emission boundary that can be crossed without the required proof;
- a violation of the active milestone architecture.

Formal claims must be exact within represented scope.

### Filesystem sink

Review the sink against its declared practical threat model:

- one project owner;
- cooperating Fido emitters serialized by one lock;
- ordinary filesystems;
- a stable directory namespace between runs;
- ordinary crashes;
- disk exhaustion;
- permission and I/O failures;
- generation into a dirty directory;
- foreign Go/module inputs rejected in the traversed Go-discovered namespace;
- ignored dot/underscore/testdata/vendor directory trees treated as opaque;
- no malicious concurrent filesystem adversary;
- no arbitrary unmount/remount/backing-store replacement model.

Blocking sink defects require a concrete ordinary supported-use counterexample that can:

- overwrite or delete foreign data in the traversed namespace;
- emit or retain foreign Go in the certified build tree;
- treat an ordinary operational error as absence or success;
- violate complete-image staging before installation;
- fail to converge after a declared recoverable crash once the stale lock is cleared;
- contradict the documented ownership or cleanup contract;
- violate the selected sibling-temp architecture.

Do not demand:

- hostile-process race freedom;
- unforgeable ownership;
- transaction logs;
- stage records;
- device/inode capabilities;
- mount-identity tracking;
- multi-file transactional filesystem commits;
- support for arbitrary mount replacement between runs.

### Prototype pre-commit hook

The pre-commit hook provides reasonable assurance against accidental stale generated output for a cooperating developer using ordinary Git commands.

Its supported workflow is:

- ordinary `git add`;
- ordinary `git commit`;
- a normal stage-0 index;
- the hook exports the proposed staged snapshot;
- proof/generation runs from that snapshot;
- staged generated paths and bytes are compared recursively with the pristine Buildx artifact;
- stale, missing, extra, or modified generated files reject;
- the hook does not mutate or auto-stage the working tree;
- `git commit --no-verify` is an explicit documented bypass.

Blocking pre-commit defects require a concrete ordinary developer workflow where stale or incorrect generated output can be committed accidentally despite using the hook normally.

The following are OUT OF SCOPE and must not block:

- a developer deliberately editing the hook and every verifier together;
- coordinated malicious edits to gate scripts, Dockerfile targets, tests, and documentation;
- `--no-verify`;
- hand-built index objects;
- direct `git update-index --cacheinfo` attacks;
- deliberate skip-worktree manipulation;
- hostile `core.symlinks` scenarios manufactured to fool the local hook;
- control-character or newline pathnames created to attack shell scripts;
- attempts to prove a repository-local hook “unbypassable”;
- mutation tests whose only purpose is to show that removing the verifier defeats the verifier.

Low-cost robustness already present may remain if it stays simple.

Do not grow new machinery for these scenarios.

A future protected PR check may establish a stronger server-side boundary. That is not the current pre-commit contract.

## Finding classifications

Every review item must be exactly one of:

### BLOCKING IMPLEMENTATION DEFECT

Use only when:

- the issue violates an explicit current guarantee;
- it occurs within the component’s declared threat model;
- there is a concrete reproducer or direct proof of contradiction;
- the repair preserves the active milestone architecture.

A blocking finding must state:

1. the violated contract clause;
2. the concrete supported scenario;
3. the observed wrong behavior;
4. the smallest architecture-preserving correction.

### ARCHITECTURAL CONFLICT

Use when the concern is real but repairing it would change:

- architecture;
- represented scope;
- threat model;
- responsibility boundaries;
- selected algorithm;
- public guarantees.

Do not prescribe or implement a replacement architecture.

Tell Claude to notify the user and stop.

### NONBLOCKING OBSERVATION

Use for:

- future features;
- speculative hardening;
- hostile or deliberately malicious scenarios outside the threat model;
- optional refactors;
- style preferences;
- completeness beyond the milestone;
- documentation wording that does not materially misstate a public guarantee;
- local verifier bypasses requiring deliberate verifier modification;
- concerns without a concrete supported-use reproducer.

Nonblocking observations do not prevent GREEN.

## Green condition

Return GREEN when there are:

- no blocking implementation defects within scope; and
- no unresolved architectural conflicts.

Do not require the absence of nonblocking observations.

Do not keep a loop alive because the system could be more general, portable, hostile-environment hardened, or feature-complete.

## Scope discipline

Review the full affected surface of the active milestone.

Do not reopen unrelated architecture.

Do not request new language features.

Do not request stronger semantics than the represented language claims.

After one structural repair attempt in a subsystem, a second proposed structural redesign is an ARCHITECTURAL CONFLICT unless the active milestone explicitly requires it.

## Review output

Use this exact top-level result:

- `GREEN`
- `BLOCKING`
- `ARCHITECTURAL CONFLICT`

When GREEN, nonblocking observations may follow under a clearly labeled optional section.

Do not use “anything still worth doing” as the gate.

The gate is:

> Correct implementation of the binding milestone within each component’s declared guarantee and threat model.

---

Codex stop-review launcher prompt

Replace the active locally hacked stop-review prompt with this minimal prompt:

---

Read `.review/CODEX_REVIEW_POLICY.md` and `.review/NEXT_STEPS.md` before reviewing.

Review the implementation as an implementation of the binding milestone under the permanent review policy.

Report only:

- BLOCKING IMPLEMENTATION DEFECTS within the declared scope and threat model;
- ARCHITECTURAL CONFLICTS whose repair would change the contract;
- optional NONBLOCKING OBSERVATIONS that do not prevent GREEN.

A finding is not blocking merely because a more adversarial, complete, portable, or generalized design can be imagined.

For the prototype pre-commit hook, deliberate verifier modification, `--no-verify`, Git-plumbing attacks, hostile pathnames, and coordinated malicious index construction are out of scope.

Return GREEN as soon as there are no blocking implementation defects and no architectural conflicts.

---

PART A — simplify the prototype boundaries and freeze them

1. Fix the one remaining sink classification-order defect

The runtime sink’s ignored-directory policy is correct:

- dot-prefixed directories are opaque;
- underscore-prefixed directories are opaque;
- `testdata` is opaque;
- `vendor` is opaque;
- ordinary visible directories remain traversed;
- root `.fido` is the sole control directory;
- visible nested `.fido` rejects.

The current entry classifier checks the `.fido-tmp-v1` suffix before it checks whether an entry is an ignored directory.

Therefore a hidden directory such as:

  .cache.fido-tmp-v1/

is currently treated as a nonregular reserved temp and rejected instead of being opaque.

Correct the order:

1. handle the special name `.fido`;
2. `lstat`;
3. if the entry is a directory and its basename is Go-ignored, skip it immediately;
4. otherwise classify reserved suffix;
5. classify `go.mod`;
6. classify visible `*.go`;
7. recurse into other visible directories.

Requirements:

- `.cache.fido-tmp-v1/` is opaque and preserved;
- `_cache.fido-tmp-v1/` is opaque and preserved;
- `testdata/x.go.fido-tmp-v1` is never inspected;
- `vendor/x.go` is never inspected;
- a visible regular `main.go.fido-tmp-v1` still recovers;
- a visible non-mappable `notes.fido-tmp-v1` still preserves + refuses;
- visible nested `.fido` still rejects;
- visible foreign `.go` and nested `go.mod` still reject.

After this fix, freeze the sibling-temp sink.

Do not add new filesystem hardening unless a future ordinary supported-use counterexample violates the declared sink contract.

2. Delete the “unbypassable pre-commit” claim

Delete every active claim that the local hook or staged gates are:

- unbypassable;
- tamper-proof;
- a security boundary;
- resistant to coordinated verifier modification.

Replace with the honest prototype guarantee:

> For a cooperating developer using ordinary Git staging and commit commands, the hook verifies the proposed staged snapshot, runs the cached proof and Go checks, and rejects stale, missing, extra, or modified generated output. It is bypassable with `--no-verify` and does not defend against deliberate modification of its own verifier.

3. Delete the pre-commit review fortress

Delete:

- `tools/precommit-selftest.sh`;
- the `precommit-selftest` Make target;
- mutation tests proving that deleting or weakening a gate defeats the gate;
- synthetic malicious Git-repository tests;
- skip-worktree bypass tests;
- `core.symlinks=false` attack tests;
- newline/control-character filename attack fixtures;
- “teeth” tests that exist only to prove an isolated verifier mutation is caught;
- status/prose enumerating those attacks.

Retain the small useful production mechanisms if they remain simple:

- export the staged snapshot;
- run staged proof/generation;
- recursively compare generated path set + bytes;
- exact generated mode 100644;
- no automatic staging;
- full cached verification on ordinary commits;
- explicit `--no-verify` bypass.

Existing `--ignore-skip-worktree-bits` may remain because it is low-cost.

The generated-mode gate may remain because it is small and directly states repository policy.

Do not add replacement self-defense machinery.

4. Simplify the OCaml-origin gate

Retain:

- the exact allowlist of handwritten OCaml transport/apply files;
- the rule that filesystem-only OCaml may not inspect Rocq terms;
- the rule that the transport bridge may not inspect program/AST/type/safety structures.

Delete the whole-repository “deleted backend hallmark” scanner.

Do not scan every document, shell script, and hook for historical identifier names.

Repository prose may discuss deleted history without becoming an implementation defect.

The real boundary is the OCaml allowlist and responsibility checks.

5. Separate working-tree verification from staged-index verification

`make check` must have one coherent meaning:

> verify the current working tree.

The pre-commit hook must have one coherent meaning:

> verify the proposed staged commit.

Refactor the shared mechanisms accordingly.

Working-tree path:

- `make check` builds/proves from the working tree;
- `make check` compares working-tree generated `go.mod` + recursive `.go` against the pristine artifact generated from working-tree proof inputs;
- `make check` does not compare an unrelated staged snapshot.

Staged path:

- the pre-commit hook exports the index once;
- proof/e2e/generation use that exported staged snapshot;
- staged generated output is compared against the pristine artifact built from the staged proof inputs;
- the hook never mutates the working tree or index.

Shared Buildx stages and comparison code should remain shared.

Names may be:

- `verify-generated` for working tree;
- `verify-staged-generated` for the hook;

or another clear split.

Do not duplicate the renderer or generation path.

6. Keep pre-commit simple

The normal hook should do only:

1. export the staged snapshot;
2. apply lightweight repository policy checks;
3. run cached proof;
4. run cached Go e2e;
5. materialize the pristine generated artifact;
6. compare exact staged generated path set + bytes;
7. reject on mismatch with a clear `make regenerate` instruction.

Do not:

- auto-stage;
- mutate the working tree;
- mutate the index;
- run mutation tests of itself;
- attempt to prove its own unbypassability;
- inspect malicious Git plumbing.

7. Documentation reconciliation

Update:

- `.review/CODEX_REVIEW_POLICY.md`;
- `.review/NEXT_STEPS.md`;
- `CLAUDE.md`;
- `ARCHITECTURE.md`;
- `PAINFUL_LESSONS.md`;
- `PROGRESS.md`;
- `README.md`;
- Makefile comments;
- hook and gate headers.

Required truths:

- formal/certified components remain reviewed ruthlessly;
- sink review follows its practical threat model;
- pre-commit provides reasonable assurance only;
- `--no-verify` is an explicit bypass;
- local verifier tamper resistance is out of scope;
- no self-test fortress remains;
- `make check` checks the working tree;
- pre-commit checks the staged snapshot;
- the sink is frozen after the ignored-directory ordering correction.

PART B — add exact byte-sequence Go strings

8. Historical quarry, not resurrection

Inspect useful pre-deletion history for string semantics and counterexamples.

At minimum inspect:

  git show e1954d3f84878d844a382dbdea621e4c69d32fd5:CoreType.v
  git show d5646d646fc5046b54eb04b664bed7035b763786:GoTypes.v
  git log -S 'PString' --all
  git log -S 'GoString' --all

Use history to recover:

- the byte-sequence meaning of Go strings;
- useful escaping lemmas;
- value/type distinctions;
- counterexamples.

Do not restore:

- Surface;
- TypedIR;
- extraction-era Go type tags;
- broad old type universes;
- raw string fallbacks;
- a second AST;
- old backend code;
- old parser/pretty-printer machinery.

9. Semantic string value is an exact byte sequence

Use Rocq `string` as the semantic Go string value, or a transparent alias/wrapper with exactly the same byte-sequence meaning.

Rocq `string` is a sequence of `ascii` bytes.

Do not model a Go string as:

- Unicode scalar values;
- Unicode code points;
- UTF-8-decoded characters;
- source literal spelling.

A Go string value is exact bytes.

Recommended name:

  Definition GoString := string.

A wrapper is acceptable only if it adds a genuine permanent invariant. No invariant is currently needed.

10. Grow the one raw AST

Add exactly one raw expression constructor:

  EString : string -> GoExpr

or:

  EStr : string -> GoExpr

Choose one name and use it consistently.

Its argument is the semantic byte value.

It is not raw Go source text.

It is not an already-escaped literal.

Do not add:

- raw string literal syntax;
- interpreted-literal source spelling;
- an opaque text escape;
- string concatenation;
- indexing;
- slicing;
- length;
- conversions;
- runes;
- byte slices.

11. Grow the one type authority

Extend:

  GoType

with exactly:

  TString

The complete current type universe becomes:

  TBool
  TInt
  TString

No placeholder future type constructors.

Update decidable equality and every exhaustive policy.

12. Grow exact untyped constants

Extend:

  GoConst

with:

  CString : string -> GoConst

Update the one exact constant interpretation:

  const_value (EString s) = CString s

The value is exact bytes.

No escaping or rendering occurs in `const_value`.

13. Default type and representability

Update:

  const_default_type (CString s) = TString

Every `CString s` is representable as `TString`.

No `CString` is representable as `TBool` or `TInt`.

No bool/int constant is representable as `TString`.

Update:

- declarative `ConstRepresentable`;
- executable reflector;
- exact reflection theorem;
- cross-type negative fixtures.

Do not introduce a string length limit.

Go string constants may contain arbitrary finite byte sequences in represented scope.

14. Use-context resolution

`UsePrintlnArg` allows `TString`.

Update:

- `UseAllows`;
- executable policy;
- resolution soundness;
- completeness;
- determinism;
- wrong-type rejection;
- statement/file/program typing reflection.

The existing type architecture remains evidence over the same raw AST.

No typed expression tree.

15. Compiler integration

`ProgramTyped` continues to be the single static typing foundation consumed by `GoCompile`.

String literals introduce no new compile error beyond the existing typing result.

Do not add a speculative broad error taxonomy.

All current string literals are representable as `TString`.

Package/main rules remain unchanged.

Empty programs remain accepted.

Imports remain absent.

16. Runtime values and safety semantics

Extend:

  GoValue

with:

  VString : string -> GoValue

Update:

  value_type (VString s) = TString

and:

  const_to_value (CString s) = VString s

Evaluation remains:

  eval_expr = const_to_value ∘ const_value

Do not add a second string evaluator.

Prove the existing root:

  ResolveExpr u e t ->
  value_type (eval_expr e) = t

for strings as well.

`GoSafe` remains `True` because a string literal passed to builtin `println` introduces no panic, blocking, heap, or nontermination behavior.

Do not predeclare string indexing/slicing safety.

17. Canonical Go interpreted string literal renderer

Render every semantic byte string using exactly one canonical interpreted-string spelling.

The source literal must be surrounded by double quotes.

Define a per-byte encoder with this exact policy:

- byte `0x22` (`"`) -> `\"`
- byte `0x5c` (`\`) -> `\\`
- byte `0x0a` (LF) -> `\n`
- byte `0x09` (TAB) -> `\t`
- byte `0x0d` (CR) -> `\r`
- bytes `0x20` through `0x7e`, excluding quote and backslash -> emit the byte directly
- every other byte -> `\xhh`

For `\xhh`:

- use exactly two hexadecimal digits;
- use lowercase `0`-`9`, `a`-`f`;
- represent the original byte exactly;
- do not use variable-width escapes.

Define conceptually:

  render_hex_nibble
  render_hex_byte
  render_string_byte
  render_string_body
  render_string_literal

Then:

  render_expr (EString s) = render_string_literal s

Do not emit raw-string literals.

Do not choose between multiple spellings.

One semantic byte string has one canonical source spelling.

18. Independent canonical-literal decoder/denotation

Add a small certified decoder for the exact canonical interpreted-literal subset emitted above.

It is not a general Go parser.

It must understand:

- opening and closing double quote;
- direct printable bytes allowed by the encoder;
- `\"`;
- `\\`;
- `\n`;
- `\t`;
- `\r`;
- `\xhh` with exactly two hex digits.

It must reject:

- malformed escapes;
- truncated `\x`;
- nonhex digits;
- unescaped quote inside the body;
- unescaped control/newline bytes;
- trailing bytes after the closing quote.

Names may be:

  decode_hex_digit
  decode_string_body
  decode_string_literal

The decoder must be structurally independent from the encoder.

Do not call the encoder to decide what the decoder accepts.

19. Root string proofs

Prove at minimum:

A. Exact value round trip

  decode_string_literal (render_string_literal s) = Some s

for every finite byte string `s`.

B. ASCII source

  str_ascii (render_string_literal s) = true

for every `s`, including bytes >= 128.

C. Quoting shape

The rendered literal begins and ends with a double quote and contains no unescaped newline or carriage return.

D. Hex exactness

Encoding then decoding every byte rendered by `\xhh` yields the original byte.

E. Canonical common escapes

Kernel fixtures pin exact spellings for:

- empty string;
- ordinary ASCII;
- quote;
- backslash;
- newline;
- tab;
- carriage return;
- NUL;
- DEL (`0x7f`);
- `0x80`;
- `0xff`.

F. Value/type/render correspondence

Extend `RenderedPrimitiveDenotes` with:

  VString bytes =>
    decode_string_literal rendered = Some bytes

Update:

  render_expr_denotes

for strings.

Retain and extend:

  render_resolved_expr_denotes

so a resolved string expression:

- renders to a spelling decoding to the exact runtime byte value;
- evaluates to `VString` of those bytes;
- has resolved type `TString`.

This remains a theorem about Fido’s canonical literal grammar.

It is not a kernel theorem about the complete real Go parser.

20. Renderer source remains ASCII

All generated `.go` source remains ASCII even when a semantic string contains arbitrary bytes.

Bytes outside printable ASCII must appear only through ASCII escape characters.

Update:

- `render_expr_ascii`;
- argument/statement/declaration/file ASCII proofs;
- DirectoryImage ASCII proofs if needed.

Do not weaken the existing all-ASCII claim.

21. Required type fixtures

Add positive kernel fixtures:

- empty string resolves to `TString`;
- ordinary ASCII string resolves to `TString`;
- arbitrary byte string containing `0x00`, `0x7f`, `0x80`, `0xff` resolves to `TString`;
- mixed `println(true, 42, "hello")` is typed;
- `println("")` is typed;
- a file/program containing string literals is typed and compilable.

Add negative kernel fixtures:

- `CString` is not representable as `TBool`;
- `CString` is not representable as `TInt`;
- bool/int constants do not resolve as `TString`;
- a string expression does not resolve as `TBool` or `TInt`.

22. Required e2e and differential coverage

Update the canonical primary witness to exercise readable strings.

Include at least:

- empty string;
- ordinary ASCII text;
- quote;
- backslash;
- newline;
- tab;
- carriage return.

The tracked generated `main.go` is allowed and expected to change in this feature milestone.

Regenerate it through the pristine Buildx layer and the same sink.

Add a separate string-byte witness for boundary bytes:

- `0x00`;
- `0x1f`;
- `0x7f`;
- `0x80`;
- `0xff`.

The separate witness must:

- emit valid Go;
- be gofmt-clean;
- compile under pinned Go 1.23;
- execute successfully;
- compare actual output bytes to a reviewed textual hexadecimal golden or another explicit byte-exact integration oracle.

Do not compare binary output through shell command substitution.

Use byte-safe comparison such as:

- `cmp`; or
- `od -An -v -tx1` normalized to a reviewed hex file.

Document that builtin `println` output is integration evidence, not the formal string semantics.

The formal string semantics are the exact byte value and the literal decoder theorem.

23. External Go adequacy experiments

Add focused real-Go fixtures confirming the chosen canonical literal forms are accepted:

- direct printable body;
- escaped quote and backslash;
- `\n`, `\t`, `\r`;
- `\x00`;
- `\x7f`;
- `\x80`;
- `\xff`.

A Go rejection of any Fido-rendered string is a hard correctness failure.

Do not introduce imports to perform these checks.

24. No feature creep

Do not add:

- string concatenation;
- comparison;
- indexing;
- slicing;
- len;
- conversion to or from byte/rune slices;
- UTF-8 decoding;
- rune literals;
- raw strings;
- identifiers;
- variables;
- calls;
- functions;
- imports.

This milestone adds string literal values passed to the existing builtin `println`, completely and exactly.

25. Public theorem gate

Add axiom-free public surfaces for at least:

GoTypes

- string default type;
- string representability;
- representability reflection;
- string resolution;
- cross-type rejection;
- mixed statement typing.

GoSafe

- string value type;
- resolved string evaluates to the resolved type.

GoRender

- exact escape fixtures;
- string render/decode round trip;
- string literal ASCII;
- string expression denotation;
- resolved render/value/type theorem.

GoCompile

- existing soundness/completeness remain;
- a concrete string program compiles;
- empty program remains accepted.

All surfaces must be closed.

The whole-certified-theory audit must automatically cover the changed modules.

No axioms, admitted proofs, functional extensionality, or unchecked primitives.

26. Generated artifact and repository workflow

After string support is complete:

- build the pristine generated-module layer;
- run `make regenerate`;
- update tracked root `go.mod` only if its bytes genuinely change (they should not);
- update tracked recursive `.go` to the new canonical witness;
- stage the generated changes;
- verify working-tree `make check`;
- verify staged pre-commit flow;
- confirm exact generated path set and bytes.

Do not hand-edit generated Go.

27. Documentation update

Update active documentation to say:

- Go strings are exact byte sequences;
- raw literals carry semantic bytes, not source spelling;
- `TString` is the third live type;
- strings are untyped constants defaulting to `TString`;
- every string constant is representable as `TString`;
- the renderer uses one canonical interpreted literal;
- source remains ASCII through escapes;
- the decoder theorem establishes exact byte round trip;
- real-Go parsing is external adequacy;
- no UTF-8 abstraction is claimed;
- no string operations exist yet;
- the pre-commit hook provides reasonable assurance, not tamper resistance;
- the sink is frozen under its practical threat model.

Keep `PROGRESS.md` compact.

Keep `PAINFUL_LESSONS.md` architectural.

Add durable lessons only:

- review rigor must match the component’s declared guarantee;
- a convenience hook is not a security boundary;
- exact string values are bytes, while source literal spelling is a separate proved encoding;
- a canonical escape grammar is preferable to multiple equivalent spellings;
- the decoder is a denotation tool, not a general Go parser.

28. Required deletion/culling

Delete code and prose that exist only for the abandoned “unbypassable local verifier” goal.

Expected deletions include:

- `tools/precommit-selftest.sh`;
- Makefile target/wiring for it;
- mutation-test prose;
- skip-worktree attack regressions;
- symlink-mode attack regressions;
- newline-path attack regressions;
- broad historical-name scanning across every tracked file;
- “unbypassable” status claims.

Do not delete low-cost production checks solely because their adversarial tests are deleted.

Do not reintroduce those tests during Codex review.

`.review/CODEX_REVIEW_POLICY.md` explicitly makes them out of scope.

29. Acceptance criteria

Workflow

- Current old loop stopped.
- This directive copied verbatim to `.review/NEXT_STEPS.md`.
- Permanent policy copied verbatim to `.review/CODEX_REVIEW_POLICY.md`.
- Both committed before implementation.
- Local Codex launcher replaced with the minimal launcher prompt.
- Exact `/loop 5m ...` command started after the contract commit.
- Codex reviews under the new policy.
- Nonblocking observations do not prevent GREEN.
- No architectural conflict silently implemented.
- Final notification sent.
- Loop stopped.

Review policy

- Certified core remains ruthlessly reviewed.
- Sink review follows its declared practical threat model.
- Pre-commit review is ordinary-workflow reasonable assurance.
- Deliberate verifier attacks are out of scope.
- GREEN means no blocking findings or architectural conflicts.
- “Anything still worth doing” is not the gate.

Prototype boundary cleanup

- Hidden ignored-directory classification occurs before suffix classification.
- Hidden suffix directories are opaque.
- Visible valid mapped temps recover.
- Visible non-mappable temps preserve + refuse.
- Visible nested `.fido` rejects.
- Precommit self-test fortress deleted.
- No “unbypassable” claim remains.
- Whole-repo historical hallmark scanner deleted.
- `make check` verifies working tree coherently.
- Pre-commit verifies staged snapshot coherently.
- Ordinary stale/missing/extra/modified generated output rejects.
- Hook does not mutate or auto-stage.
- `--no-verify` remains documented.

String syntax and type foundation

- One new raw expression constructor carrying semantic bytes.
- `GoType` contains exactly `TBool`, `TInt`, `TString`.
- `GoConst` contains exact `CString`.
- `GoValue` contains exact `VString`.
- One constant interpretation.
- One default-type authority.
- One representability authority.
- One resolution/typing path.
- No typed AST.
- No second IR.
- No imports or identifiers.

String rendering

- One canonical interpreted-literal encoder.
- Exact escape policy implemented.
- Independent decoder implemented.
- Decoder rejects malformed forms.
- Render/decode round trip proved for every byte string.
- Source ASCII proved.
- Exact common/boundary escape fixtures.
- Rendered string denotes exact runtime bytes.
- Resolved type agrees with runtime value.

Compiler/safety/e2e

- Existing compiler soundness/completeness remain.
- Existing bool/int behavior remains.
- String programs typecheck and compile.
- Empty program remains valid.
- SafeProgram boundary unchanged in responsibility.
- Primary generated witness grows strings.
- Boundary-byte witness compiles and runs.
- Byte output compared safely.
- `go build ./...` remains blocking.
- `go vet` remains nonblocking.
- No generated file hand-edited.

Proof

- New public surfaces closed.
- Whole-theory audit green.
- No axioms/admitted/parameters.
- No source-text axiom scanner.

30. Completion report

When complete, report:

- contract commit SHA;
- final implementation commit SHA;
- complete commit range;
- local Codex prompt path;
- final `.review/CODEX_REVIEW_POLICY.md`;
- Codex final result and any nonblocking observations;
- files deleted from the pre-commit fortress;
- final pre-commit guarantee;
- final `make check` working-tree algorithm;
- final staged pre-commit algorithm;
- sink ordering correction and regressions;
- historical string sources inspected;
- final `GoType`;
- final `GoConst`;
- final raw string AST constructor;
- semantic string representation;
- exact escape policy;
- decoder grammar;
- round-trip theorem;
- ASCII theorem;
- type/value/render correspondence theorem;
- every new or changed theorem;
- full `Print Assumptions` results;
- whole-theory audit result;
- generated source diff;
- string e2e output-byte evidence;
- all proof/build/e2e commands and results;
- confirmation notification sent;
- confirmation loop stopped.

Do not list a retained correctness flaw as a known limitation.

If a real obstacle requires changing this contract, classify it as an ARCHITECTURAL CONFLICT, notify the user, stop the loop, and wait.

31. Hard stop

When Codex is GREEN under the new policy and final verification passes:

1. Commit the completed checkpoint.
2. Notify the user through the configured phone/completion-notification channel.
3. Stop the `/loop`.
4. Do not infer the next feature.
5. Wait for review.

Bottom line

The permanent path after this milestone is:

  raw GoExpr
    -> exact untyped GoConst { bool, int, byte-string }
    -> contextual resolution through GoType { bool, int, string }
    -> ProgramTyped evidence over the SAME GoProgram
    -> GoCompile
    -> GoSafe values using the SAME GoType
    -> direct renderer
         string bytes -> one canonical ASCII interpreted literal
         -> independent exact decoder theorem
    -> certified DirectoryImage
    -> frozen practical sibling-temp sink
    -> pristine generated-module layer
    -> tracked generated Go
    -> reasonable-assurance staged pre-commit check

We are building the language again.

We are not building a hostile-Git security product.
