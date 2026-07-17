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

## Collection-architecture review criterion

Fido has a binding collection law (CLAUDE.md / ARCHITECTURE.md): use a mature standard collection when one
exists; a thin domain wrapper is allowed, a project-authored collection implementation is not. When reviewing:

- every new identity-keyed or membership-only collection must NAME its mature standard backing (a pinned Rocq
  stdlib map/set, an OCaml `Map`/`Set`, or a Rocq runtime set such as `Names.GlobRef.Set`);
- a retained `list` must have a source-order / repetition / positional-structure / rollback-stack / transport-
  enumeration reason, OR be a derived `elements`/`bindings` enumeration whose identity authority is the map/set;
- a project-authored collection STORAGE implementation (custom map/set/tree/trie/hash/multimap/graph, or
  `list + NoDup` as public identity-keyed storage, or a parallel association-list backing) is BLOCKING unless an
  explicit human-approved exception is recorded;
- a standard map `add` that OVERWRITES and erases duplicate source evidence is BLOCKING — a source builder must
  reject duplicates before insertion;
- a builder failure that DEFAULTS to empty/default (`match build … with Some c => c | None => empty`) is
  BLOCKING when failure means invalid structure.

This is an architectural review law backed by explicit audit and code inspection. Do NOT add a brittle
source-scanning "collection security gate" that pretends to prove architecture by regex.

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
