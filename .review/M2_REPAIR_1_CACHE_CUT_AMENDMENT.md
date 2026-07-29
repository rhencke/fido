# M2 REPAIR 1 — CACHE-CUT AMENDMENT

This amendment is part of the accepted M2 Repair 1 instruction. It supersedes any Repair 1 language that can be
read as requiring a completely empty Docker, BuildKit, image, package, or toolchain cache for canonical cold
measurements.

The existing Repair 1 findings and required corrections remain in force. This amendment changes only the meaning
and execution of cold, cached, and uncached measurement.

## Governing rule

A canonical cold measurement is cold from one declared **project-dependent invalidation root** downward.

It is not cold from the registry, Docker daemon, Buildx builder, base image, pinned toolchain, operating-system
packages, Rocq installation, Go installation, or other long-lived infrastructure acquisition.

The Build Observatory measures the cost created by Fido's repository and build graph. It does not include network
pull latency or one-time machine bootstrap in the canonical performance record.

## Canonical cache boundary

Before every canonical project measurement:

- the Buildx builder already exists;
- required base images are locally available;
- the pinned toolchain and package-acquisition layers are available;
- registry pulls are forbidden during the measured interval;
- builder creation and bootstrap are excluded from the measured interval;
- stable infrastructure ancestors through the declared cache boundary must remain cache hits;
- the named project-dependent invalidation root and every dependent stage must rebuild when the scenario requires
  a project-cold run.

A fully empty machine, empty registry cache, or missing-image run is an optional setup diagnostic only. It is not
canonical M2 performance evidence.

## Required scenario model

Replace global `cold.uncached` language with these stable scenario families:

```text
project.cold.<root>
project.cached.fresh
project.warm.noop
project.incremental.<edit>
environment.bootstrap
```

### `project.cold.<root>`

- Start a fresh command session.
- Retain all stable infrastructure ancestors.
- Invalidate exactly the named project-dependent root.
- Require that root and all graph-dependent descendants to execute.
- Require stable ancestors to remain cached.
- Record actual per-stage hit, miss, rebuilt, skipped, and unavailable state.
- Exclude registry pulls and builder bootstrap from elapsed time.

Examples include:

```text
project.cold.prover
project.cold.emit
project.cold.go-e2e
project.cold.generated-artifact
```

The registry must state which roots are meaningful for each command. Do not invent roots which do not correspond
to the current Docker or command graph.

### `project.cached.fresh`

- Use a completed project cache produced by the exact command's own prime run.
- Start a fresh command session.
- Do not reuse process state from the prime run.
- Require the declared project stages to be cache hits where the graph permits.

### `project.warm.noop`

- Use the same source and completed project cache.
- Run immediately again with no source change.
- Record no-op command and policy overhead separately from cache population.

### `project.incremental.<edit>`

- Start from the exact completed prime cache for that command.
- Apply one exact deterministic edit shape.
- Record the first invalidated project stage and every downstream rebuilt stage.
- Restore and verify the exact source after each sample.
- Prevent one sample's result from satisfying another sample as an exact cache hit, either by restoring the same
  immutable prime cache for every sample or by using distinct deterministic edit identities whose expected cache
  keys differ.
- Retain the edit ID in the metric identity.

### `environment.bootstrap`

Catalog and optionally time:

- Buildx builder creation;
- image pulls;
- toolchain acquisition;
- package acquisition;
- first machine setup.

This scenario is diagnostic, excluded from canonical trend comparison, and never required for `RECORD=1`.

## Per-command isolation

Every measured root command keeps its own project-cache measurement chain.

Commands may share immutable, long-lived infrastructure caches such as locally present base images and pinned
toolchain layers. They may not share project-result caches in a way that lets an earlier measured command satisfy a
later command's declared project-cold sample.

For each root command, execute one causal chain:

```text
stable infrastructure present
→ isolated project cache namespace
→ project.cold.<root>
→ exact prime result retained
→ project.cached.fresh
→ project.warm.noop
→ incremental edit samples from the exact prime state
```

The observation must retain the identity of the prime result used by every cached, warm, and incremental sample.

## Observation schema

Every sample must retain a structured cache-cut identity. At minimum:

```json
{
  "cache_cut": {
    "stable_through": "pinned-toolchain",
    "invalidated_from": "prover",
    "registry_pulls_included": false,
    "builder_bootstrap_included": false
  },
  "cache_observation": {
    "stages": {
      "pinned-toolchain": "hit",
      "prover": "rebuilt",
      "go-e2e": "not-required"
    }
  }
}
```

Use stable stage IDs from the suite registry. Do not identify stages by line number, output order, or a copied
ordinal.

The exact schema may use arrays or objects, but it must preserve:

- declared stable boundary;
- declared invalidation root;
- actual stage hit/miss/rebuilt/skipped state;
- builder identity;
- project-cache namespace identity;
- prime-result identity;
- whether registry pulls occurred;
- whether builder bootstrap occurred;
- source identity;
- effective concurrency.

## Validation

A canonical sample fails validation when:

- a registry pull occurs during the measured interval;
- builder creation or bootstrap occurs during the measured interval;
- a declared stable ancestor rebuilds;
- the named invalidation root remains cached;
- actual stage behavior contradicts the declared cache cut;
- the command uses another measured command's project-result cache;
- a cached, warm, or incremental sample cannot identify its exact prime result;
- a sample lacks stage-level cache evidence where Buildx exposes it;
- the cache cut is absent or unknown;
- an observation labels a fully empty infrastructure run as canonical project-cold evidence.

When a tool cannot observe a stage's cache state, record `unavailable` and state why. Do not infer a hit or miss from
elapsed time.

## Comparison

Two metrics are comparable only when all of these match:

```text
command ID
scenario family
invalidation root
stable cache boundary
edit ID, when present
derived parent, when present
resource scope
source-view kind
suite version
environment compatibility class
effective concurrency
```

A project-cold measurement may not be compared as equivalent to:

- a registry-pull run;
- a builder-bootstrap run;
- a fully empty infrastructure-cache run;
- a different invalidation root;
- a run whose stable ancestors rebuilt.

Report such pairs as `incomparable`, not improved or regressed.

## Recording

`RECORD=1` requires the full canonical suite and exact registry coverage, but does not require
`environment.bootstrap`.

The tracked canonical observation must contain project-cold, project-cached-fresh, project-warm-noop, and required
incremental measurements for every canonical command relation declared by the suite.

A partial `ONLY=` or `SCENARIO=` run remains ad hoc and may never replace the canonical observation.

## Usage

Generated help and listing output must explain:

```text
make observe
make observe ONLY=<command-or-group>
make observe SCENARIO=<scenario>
make observe ONLY=<selector> SCENARIO=<scenario>
make observe BASE=<git-ref-or-path>
make observe RECORD=1
make observe LIST=1
make observe HELP=1
```

Examples must use project-cache scenarios, such as:

```text
make observe ONLY=make.prove SCENARIO=project.cold.prover
make observe ONLY=make.check SCENARIO=project.warm.noop
make observe ONLY=precommit.prover SCENARIO=project.cached.fresh
```

Do not teach users to clear all Docker or registry caches for ordinary observatory use.

## Controls

Add must-fail controls for:

- project-cold sample with a registry pull;
- project-cold sample that creates the builder;
- project-cold sample whose stable toolchain ancestor rebuilds;
- project-cold sample whose invalidation root stays cached;
- sample whose actual cache behavior contradicts its declared cache cut;
- two root commands sharing a project-result cache;
- cached sample with no prime-result identity;
- comparison across different invalidation roots reported as comparable;
- comparison between project-cold and bootstrap reported as comparable;
- `RECORD=1` requiring bootstrap timing;
- help text which describes canonical cold as a fully empty Docker cache.

Add must-accept controls for:

- two commands sharing stable infrastructure layers while retaining isolated project-result caches;
- a project-cold run with all stable ancestors hit and the named root rebuilt;
- a canonical complete observation with no bootstrap measurement;
- a named `ONLY=` project-cold run which remains ad hoc.

Add every new root helper to the mutation harness and require its exact named controls to fail when its rule is
removed.

## Documentation ownership

Update the M2 contract, suite registry, observatory help, obligation matrix, and review request as required.

Do not copy the full cache-cut specification into `CLAUDE.md`. Keep only a terse pointer equivalent to:

```text
Use `make observe HELP=1`; the M2 suite registry owns command, scenario, cache-cut, recording, and comparison
definitions.
```

## Scope

This amendment repairs measurement meaning. It does not authorize:

- build optimization;
- Dockerfile reordering;
- cache-key redesign;
- stage consolidation;
- proof splitting;
- Make or hook architecture refactoring;
- M3 or M4 work.

When the measurements reveal waste or bad invalidation, record the evidence and assign the recommendation to M3
or the approved M4 plan.

The M2 framework remains:

```text
one suite registry
one observatory tool
one Make target
one tracked canonical observation
one ignored local-run area
Git history for historical observations
```

Repair the measurement semantics inside that framework. Do not create a second timing system.
