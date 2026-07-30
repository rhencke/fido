#!/usr/bin/env python3
"""The Build Observatory — one runner, validator, writer and comparator for Fido's timing evidence.

Fido has no measured account of what its build costs. Full acceptance approaches minutes, and nobody can say
which part is proof, extraction, transport, Go validation, policy gates or publication, which Rocq modules are
slow, what rebuild set an edit implies, or where the Make path repeats work Buildx already did. Opinions about
build cost are cheap and have been wrong before; M2 exists to replace them with one reproducible observation.

The permanent shape is five parts, and this file is one of them:

    .review/BUILD_OBSERVATORY_SUITE.json   the sole command and scenario registry
    .review/BUILD_OBSERVATION.json         one tracked canonical observation
    tools/build-observatory.py             this runner, validator, writer and comparator
    .build-observatory/                    ignored local run bundles and raw logs
    make observe                           the single public entry point

Git history is the historical observation database. Each accepted replacement of the tracked observation
becomes history through Git, so no growing tracked ledger is appended to.

Two things here have different lifetimes, and conflating them is the mistake M1 had to be repaired for twice.
The COVERAGE VALIDATOR is permanent: it runs in `make check` and the staged hook on every commit, reads only
the registry and the three surfaces it classifies, and never runs a timing suite. The MEASUREMENT modes are
M2's evidence: they are explicit, they take minutes, and no permanent path may invoke them.

An unimplemented execution mode FAILS rather than returning. A measurement facility that answered with an
empty result would report "no regression" for a suite it never ran, which is the one answer a timing tool must
never be able to give by accident.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONTRACT_REL = '.review/M2_BUILD_OBSERVATORY.md'
MATRIX_REL = '.review/M2_OBLIGATION_MATRIX.tsv'
SUITE_REL = '.review/BUILD_OBSERVATORY_SUITE.json'
OBSERVATION_REL = '.review/BUILD_OBSERVATION.json'
RECOMMENDATIONS_REL = '.review/M2_RECOMMENDATIONS.tsv'
DECLARED = (CONTRACT_REL, MATRIX_REL, SUITE_REL, OBSERVATION_REL, RECOMMENDATIONS_REL)

MAKEFILE_REL = 'Makefile'
DOCKERFILE_REL = 'Dockerfile'
HOOK_REL = '.githooks/pre-commit'
BUILDER = 'fido-builder'

SCHEMA = 'fido.build-observatory/1'
KINDS = ('make-target', 'precommit-stage', 'precommit-full', 'docker-stage',
         'rocq-module-analysis', 'history-analysis', 'setup', 'diagnostic')
SOURCE_VIEWS = ('working-tree', 'committed-tree', 'staged-index', 'staged-index-export',
                'disposable-copy', 'environment-only')
# How a side effect is CONTAINED while the command is measured. `not-measured` belongs only to a
# catalog-only entry, which by definition never runs.
ISOLATIONS = ('disposable-copy', 'temporary-docker-config', 'temporary-git-repo', 'not-measured')
SIDE_EFFECTS = ('none', 'writes-disposable-copy', 'writes-local-observation',
                'writes-tracked-observation', 'changes-repository-config')
MEASUREMENTS = ('direct', 'derived', 'catalog-only')
COMMAND_FIELDS = ('id', 'kind', 'groups', 'purpose', 'source_view', 'execution', 'side_effect',
                  'measurement', 'scenarios', 'samples', 'dependencies', 'expected_exit', 'outputs', 'owner',
                  'invalidation_roots', 'build_targets')
SCENARIO_FIELDS = ('id', 'canonical', 'purpose', 'session_state', 'cache_state', 'prime_steps',
                   'cache_cut')
# §3A.1 — a cache cut says what stays a hit, what must rebuild, and that nothing was pulled or
# bootstrapped inside the measured interval. A sample without one is a number with no meaning.
CUT_FIELDS = ('stable_through', 'invalidated_roots', 'registry_pulls_included',
              'builder_bootstrap_included')
STAGE_STATES = ('hit', 'rebuilt', 'skipped', 'not-required', 'unavailable')
# There is no coarse `buildkit_project_layers` authority, and its absence is the point: BuildKit stage
# truth is MIXED — a cold `make.e2e` rebuilds `go-e2e` while `emit` and `generated-module` are hits — and
# one field cannot hold that. The per-stage evidence in `cache_observation.stages` owns it instead.
#
# Each remaining project authority names the exact stages that touch it, so a transition can be derived
# from what those stages did rather than from whether ANY stage rebuilt. `make.prove` was reporting the Go
# build cache and the generated intermediates as primed without running a single Go or generated stage.
PROJECT_CACHES = ('dune_build', 'go_build', 'generated_intermediate')
CACHE_STAGES = {'dune_build': ('prover', 'emit', 'profile', 'module-graph'),
                'go_build': ('go-e2e',),
                'generated_intermediate': ('emit', 'generated-module', 'generated-artifact', 'sync')}
STABLE_CACHES = ('buildkit_toolchain_layers', 'apt_download', 'opam_download', 'go_module')

# A kind whose members are discovered from a live surface, paired with the surface that discovers them. A
# registry entry of one of these kinds is a claim about the repository, checked in BOTH directions.
DISCOVERED = {'make-target': MAKEFILE_REL, 'docker-stage': DOCKERFILE_REL,
              'precommit-stage': HOOK_REL, 'precommit-full': HOOK_REL}

ANCHOR = re.compile(r'^fido_observe (begin|end) (\S+)$')
POSITIONAL_OWNER = re.compile(r':\d+$')

PENDING = ('M2 measurement is pending: the runner, recorder and comparator are not implemented yet, and this '
           'tool will not report a measurement it did not take.')


class ObservatoryError(Exception):
    """A defect in the observatory's own inputs, distinct from a slow or failing measured command."""


def read_text(path: Path, label: str) -> str:
    try:
        return path.read_text(encoding='utf-8')
    except FileNotFoundError:
        raise ObservatoryError(f'{label}: {path} does not exist')
    except UnicodeDecodeError as exc:
        raise ObservatoryError(f'{label}: {path} is not valid UTF-8 ({exc})')
    except OSError as exc:
        raise ObservatoryError(f'{label}: {path} could not be read ({exc.__class__.__name__}: {exc})')


# ───────────────────────────────────────────────────────────────────── discovery
def make_targets(root: Path) -> set[str]:
    """The public interface is the Makefile's own `.PHONY` closure, including its line continuations.

    Reading the declaration rather than every `name:` line is the point: `.PHONY` is where the Makefile states
    which targets are an interface, and a private helper rule is not part of the measured surface."""
    text = read_text(root / MAKEFILE_REL, 'Makefile')
    decls = re.findall(r'^\.PHONY:((?:[^\n\\]*\\\n)*[^\n]*)$', text, re.M)
    if not decls:
        raise ObservatoryError(f'{MAKEFILE_REL}: no .PHONY declaration, so the public surface is undiscoverable')
    names = {n for d in decls for n in d.replace('\\\n', ' ').split()}
    if not names:
        raise ObservatoryError(f'{MAKEFILE_REL}: the .PHONY declaration is empty')
    return names


def docker_stages(root: Path) -> set[str]:
    text = read_text(root / DOCKERFILE_REL, 'Dockerfile')
    names = set(re.findall(r'^FROM\s+\S+\s+AS\s+(\S+)\s*$', text, re.M | re.I))
    if not names:
        raise ObservatoryError(f'{DOCKERFILE_REL}: no named build stages, so the stage surface is undiscoverable')
    return names


def docker_stage_graph(root: Path) -> dict:
    """Each named stage's direct stage predecessors, from `FROM <stage>` and `COPY --from=<stage>`.

    A predecessor counts only if it is a DECLARED stage: `FROM scratch` and `FROM <external image>` name no
    stage, and counting them invented a `scratch` stage in every command's build set."""
    text = read_text(root / DOCKERFILE_REL, 'Dockerfile')
    names = docker_stages(root)
    stage, pred = None, {n: set() for n in names}
    for line in text.split('\n'):
        s = line.strip()
        m = re.match(r'^FROM\s+(\S+)(?:\s+AS\s+(\S+))?\s*$', s, re.I)
        if m:
            base, name = m.group(1), m.group(2)
            if name:
                stage = name
                if base in names:
                    pred[stage].add(base)
            continue
        if stage:
            pred[stage] |= {f for f in re.findall(r'--from=(\S+)', s) if f in names}
    return pred


def stages_built_by(graph: dict, targets) -> set:
    """Every stage BuildKit must produce for these targets: the targets and all their ancestors.

    This is what makes the derived-child relation derivable instead of declared per stage. `docker.rocq-base`
    is observed under ten commands, and a registry that named one parent per stage called the other nine
    undeclared."""
    out, stack = set(), list(targets)
    while stack:
        node = stack.pop()
        if node in out:
            continue
        out.add(node)
        stack.extend(graph.get(node, ()))
    return out


def hook_anchor_pairs(root: Path) -> list[str]:
    """Anchor IDs in the live hook, proved paired and properly nested by one stack walk.

    A begin with no end would silently truncate a stage's duration; an interleaved pair would attribute one
    stage's time to another. Both are wrong answers rather than missing ones, so both fail here."""
    text = read_text(root / HOOK_REL, 'pre-commit hook')
    stack, seen = [], []
    for n, line in enumerate(text.split('\n'), start=1):
        m = ANCHOR.match(line.strip())
        if not m:
            continue
        event, anchor = m.groups()
        if event == 'begin':
            if anchor in stack:
                raise ObservatoryError(f'{HOOK_REL}:{n}: anchor {anchor!r} begins while already open')
            if anchor in seen:
                raise ObservatoryError(f'{HOOK_REL}:{n}: duplicate anchor pair {anchor!r}')
            stack.append(anchor)
        else:
            if not stack:
                raise ObservatoryError(f'{HOOK_REL}:{n}: anchor {anchor!r} ends with none open')
            if stack[-1] != anchor:
                raise ObservatoryError(
                    f'{HOOK_REL}:{n}: anchor {anchor!r} ends while {stack[-1]!r} is open — anchor pairs must '
                    f'nest, or one stage\'s time is attributed to another')
            stack.pop()
            seen.append(anchor)
    if stack:
        raise ObservatoryError(f'{HOOK_REL}: {len(stack)} anchor(s) never end: {stack}')
    if not seen:
        raise ObservatoryError(f'{HOOK_REL}: no observation anchors, so no hook stage can be measured')
    return seen


# ───────────────────────────────────────────────────────────────────── registry
def load_suite(root: Path) -> dict:
    """Parse and shape-check the registry. Every closed vocabulary is checked here, once."""
    raw = read_text(root / SUITE_REL, 'suite registry')
    try:
        suite = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ObservatoryError(f'{SUITE_REL}: not valid JSON ({exc})')
    if suite.get('schema') != SCHEMA:
        raise ObservatoryError(f'{SUITE_REL}: schema is {suite.get("schema")!r}, expected {SCHEMA!r}')
    for member in ('commands', 'scenarios'):
        if not isinstance(suite.get(member), list):
            raise ObservatoryError(f'{SUITE_REL}: member {member!r} is missing or not a list')

    stage_names = docker_stages(root)
    stage_graph = docker_stage_graph(root)

    by_scenario = {s['id']: s for s in suite['scenarios']}

    # A scenario's own cut is validated BEFORE any command is, because the command checks read it: asking
    # whether a command's roots agree with its cold scenarios is meaningless while a scenario's root set is
    # still unchecked, and it reported the disagreement instead of the malformed scenario that caused it.
    for s in suite['scenarios']:
        cut = s.get('cache_cut') or {}
        missing_cut = [f for f in CUT_FIELDS if f not in cut]
        if missing_cut:
            raise ObservatoryError(f'{SUITE_REL}: scenario {s["id"]}: cache_cut lacks {missing_cut}')
        roots = cut['invalidated_roots']
        if not isinstance(roots, list):
            raise ObservatoryError(f'{SUITE_REL}: scenario {s["id"]}: invalidated_roots must be a list')
        if s['id'].startswith('project.cold.'):
            if not roots:
                raise ObservatoryError(
                    f'{SUITE_REL}: scenario {s["id"]} is project-cold and invalidates nothing')
            suffix = s['id'].split('project.cold.', 1)[1]
            # A ONE-root cut must be named for its root. A COMPOUND cut gets a stable identity of its own —
            # `make audit-fresh` forces `prover` and `go-e2e` independently, and squeezing that into one
            # root name is what let a sample declare half of what it rebuilt. What a compound cut may NOT
            # do is borrow a single root's name, which would read as the smaller claim.
            if len(roots) == 1:
                if roots[0] != suffix:
                    raise ObservatoryError(
                        f'{SUITE_REL}: scenario {s["id"]} invalidates {roots[0]!r}, which is not the root '
                        f'its own name declares')
            elif suffix in roots:
                raise ObservatoryError(
                    f'{SUITE_REL}: scenario {s["id"]} invalidates {sorted(roots)} but is named for just '
                    f'{suffix!r}, so its name understates the cut')

    seen_cmd = set()
    for c in suite['commands']:
        missing = [f for f in COMMAND_FIELDS if f not in c]
        if missing:
            raise ObservatoryError(f'{SUITE_REL}: command {c.get("id")!r} is missing field(s) {missing}')
        cid = c['id']
        if cid in seen_cmd:
            raise ObservatoryError(f'{SUITE_REL}: duplicate command id {cid!r}')
        seen_cmd.add(cid)
        for field, allowed in (('kind', KINDS), ('source_view', SOURCE_VIEWS),
                               ('side_effect', SIDE_EFFECTS), ('measurement', MEASUREMENTS)):
            if c[field] not in allowed:
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid}: {field} is {c[field]!r}, not one of {", ".join(allowed)}')
        if c['measurement'] == 'catalog-only' and not c.get('catalog_only_reason', '').strip():
            raise ObservatoryError(
                f'{SUITE_REL}: {cid} is catalog-only with no reason — a command excluded from the canonical '
                f'timing run must say why, and must stay selectable when safe')
        # Build targets must name stages the Dockerfile actually declares, or the derived stage relation is
        # computed over a graph node that does not exist.
        unknown_targets = [x for x in c.get('build_targets', []) if x not in stage_names]
        if unknown_targets:
            raise ObservatoryError(
                f'{SUITE_REL}: {cid} declares build target(s) {unknown_targets} that name no Dockerfile '
                f'stage; the stages it produces could not be derived')
        if c['measurement'] != 'direct' and c.get('build_targets'):
            raise ObservatoryError(
                f'{SUITE_REL}: {cid} is {c["measurement"]} but declares build targets; only a command that '
                f'runs can build anything')
        # A root it can be measured cold from must be a stage it actually builds.
        outside = [r for r in c['invalidation_roots']
                   if c.get('build_targets') and r not in stages_built_by(stage_graph, c['build_targets'])]
        if outside:
            raise ObservatoryError(
                f'{SUITE_REL}: {cid} claims invalidation root(s) {outside} its build never reaches')

        # A command's invalidation roots and its cold scenarios state the same fact, so they must agree
        # exactly. `make prover-log` declared no root while running a buildx build of the prover stage,
        # which left it with a warm scenario and no prime it could ever take.
        # Read from each cold scenario's declared ROOT SET, not from its name: a compound cut carries a
        # stable identity of its own (`project.cold.audit-fresh`) precisely because no single root name
        # could describe the two independent roots that command forces.
        declared_roots = sorted(c['invalidation_roots'])
        cold_roots = sorted({r for sid in c['scenarios'] if sid.startswith('project.cold.')
                             for r in by_scenario[sid]['cache_cut']['invalidated_roots']})
        if c['measurement'] == 'direct':
            if declared_roots != cold_roots:
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid} declares invalidation roots {declared_roots} but its cold scenarios '
                    f'name {cold_roots}; a command rebuilds exactly the roots it can be measured cold from')
        elif declared_roots:
            # A derived command is an observation of work done inside a parent's run, and a catalog-only
            # entry never runs at all. Neither invalidates anything, and its scenarios mirror its parent's.
            raise ObservatoryError(
                f'{SUITE_REL}: {cid} is {c["measurement"]} but declares invalidation roots '
                f'{declared_roots}; it performs no build of its own')
        # A scenario declaring every cache `empty` can only be honoured by a builder that has none. The
        # isolation which creates and removes a throwaway builder is what establishes that; without it the
        # sample would run on the warm shared builder while recording `empty`, which §3A.4 forbids.
        if 'environment.bootstrap' in c['scenarios'] and c.get('isolation') != 'temporary-docker-config':
            raise ObservatoryError(
                f'{SUITE_REL}: {cid} claims environment.bootstrap with isolation {c.get("isolation")!r}; '
                f'only temporary-docker-config gives it the empty builder that scenario declares')
        if c['expected_exit'] != 0 and not c.get('expected_failure_reason', '').strip():
            raise ObservatoryError(
                f'{SUITE_REL}: {cid} expects exit {c["expected_exit"]} but declares no '
                f'expected_failure_reason; an exit code alone cannot tell one failure from another')
        if POSITIONAL_OWNER.search(c['owner']):
            raise ObservatoryError(
                f'{SUITE_REL}: {cid}: owner {c["owner"]!r} identifies its source by line number; a registry '
                f'names stable identities, because a line number is wrong the moment its file is edited')
        for s in c['scenarios']:
            if s not in c['samples']:
                raise ObservatoryError(f'{SUITE_REL}: {cid}: scenario {s!r} has no sample count')

    # §9.2 — commands declare their groups and group membership is DERIVED. Storing both invites two
    # statements of one fact that agree today and diverge silently later.
    if 'groups' in suite:
        raise ObservatoryError(
            f'{SUITE_REL}: a stored `groups` member is a second authority for a fact the command entries '
            f'already state; membership is derived from them')
    suite['groups'] = [{'id': g, 'members': sorted(c['id'] for c in suite['commands'] if g in c['groups'])}
                       for g in sorted({g for c in suite['commands'] for g in c['groups']})]

    seen_scn = set()
    for s in suite['scenarios']:
        missing = [f for f in SCENARIO_FIELDS if f not in s]
        if missing:
            raise ObservatoryError(f'{SUITE_REL}: scenario {s.get("id")!r} is missing field(s) {missing}')
        if s['id'] in seen_scn:
            raise ObservatoryError(f'{SUITE_REL}: duplicate scenario id {s["id"]!r}')
        seen_scn.add(s['id'])
        # §9.3 — command entries own applicability. A second inert representation of it is deleted rather
        # than kept for documentation.
        if 'applicable_groups' in s:
            raise ObservatoryError(
                f'{SUITE_REL}: scenario {s["id"]}: `applicable_groups` states an applicability the command '
                f'entries already own, and nothing consumes it')
        # §9.4 — the numbers decide what runs, so the numbers are the authority and the wording is generated.
        if 'sample_policy' in s:
            raise ObservatoryError(
                f'{SUITE_REL}: scenario {s["id"]}: `sample_policy` prose is a second statement of the sample '
                f'counts the command entries own; it is generated, not stored')

    # An incremental scenario with no edits would measure a no-op and file it as incremental, which is a
    # wrong number rather than a missing one. Every declared edit must also name a real, applicable file.
    edits = {e['id']: e for e in suite.get('edits', [])}
    if len(edits) != len(suite.get('edits', [])):
        raise ObservatoryError(f'{SUITE_REL}: duplicate edit id')
    for e in edits.values():
        if e['kind'] not in ('append-comment-line',):
            raise ObservatoryError(f'{SUITE_REL}: edit {e["id"]}: unknown kind {e["kind"]!r}')
        # Check the shape before using it as a path. A registry defect must arrive as a stated defect,
        # not as a TypeError from deep inside the loader.
        if not isinstance(e.get('path'), str) or not e['path'].strip():
            raise ObservatoryError(
                f'{SUITE_REL}: edit {e["id"]} declares path {e.get("path")!r}; an edit shape must name '
                f'exactly one file to change')
        if not (root / e['path']).is_file():
            raise ObservatoryError(f'{SUITE_REL}: edit {e["id"]} names {e["path"]!r}, which is not a file')
    for s in suite['scenarios']:
        # One incremental scenario, one edit shape: the edit IS the metric identity, so it cannot be a set
        # whose members get pooled, and it cannot be absent or the scenario measures a no-op.
        if s['id'].startswith('project.incremental.'):
            if s.get('edit') not in edits:
                raise ObservatoryError(
                    f'{SUITE_REL}: scenario {s["id"]} declares edit {s.get("edit")!r}, which is not a '
                    f'registered edit shape; it would measure a no-op and record it as a rebuild')
        elif 'edit' in s:
            raise ObservatoryError(
                f'{SUITE_REL}: scenario {s["id"]} names an edit but is not an incremental scenario')

        # The cache vocabulary, validated at LOAD so every run checks it. It used to live inside a function
        # only the self-test called, which meant the registry's cache states were never validated by a
        # measurement — only by the controls that tested the validator.
        declared = s.get('cache_state') or {}
        unknown = {k: v for k, v in declared.items() if v not in CACHE_STATES}
        if unknown:
            raise ObservatoryError(f'{SUITE_REL}: scenario {s["id"]}: cache state(s) {unknown} are not one '
                                   f'of {", ".join(CACHE_STATES)}')
        absent = [a for a in CACHE_AUTHORITIES if a not in declared]
        if absent:
            raise ObservatoryError(f'{SUITE_REL}: scenario {s["id"]}: cache authorities {absent} are '
                                   f'unstated; each must be recorded independently')

        # §3A.1 — the cut is what makes a cold number mean something. Its root set and name were checked in
        # the pre-pass above; what remains is what the cut ADMITS into the measured interval.
        cut = s['cache_cut']
        suffix = s['id'].split('project.cold.', 1)[-1]
        if s['id'].startswith('project.cold.'):
            if cut['registry_pulls_included'] or cut['builder_bootstrap_included']:
                raise ObservatoryError(
                    f'{SUITE_REL}: scenario {s["id"]} is canonical project-cold but admits registry pulls or '
                    f'builder bootstrap; that measures machine setup, not this repository')
            if cut['stable_through'] != suite.get('stable_through'):
                raise ObservatoryError(
                    f'{SUITE_REL}: scenario {s["id"]}: stable boundary {cut["stable_through"]!r} is not the '
                    f'registry-declared {suite.get("stable_through")!r}')
        if s.get('canonical') and (cut['registry_pulls_included'] or cut['builder_bootstrap_included']):
            raise ObservatoryError(
                f'{SUITE_REL}: scenario {s["id"]} is canonical but includes pulls or bootstrap; an empty-'
                f'machine run is diagnostic evidence, never canonical performance evidence')

    for s in suite['scenarios']:
        if 'canonical' not in s:
            raise ObservatoryError(f'{SUITE_REL}: scenario {s["id"]} does not say whether it is canonical')
        if not any(s['id'] in c['scenarios'] for c in suite['commands']):
            raise ObservatoryError(
                f'{SUITE_REL}: scenario {s["id"]} is declared but no command runs in it; a scenario nothing '
                f'can exercise reads as coverage it does not provide')

    for c in suite['commands']:
        unknown = [s for s in c['scenarios'] if s not in seen_scn]
        if unknown:
            raise ObservatoryError(f'{SUITE_REL}: {c["id"]}: unknown scenario(s) {unknown}')
        missing_dep = [d for d in c['dependencies'] if d not in seen_cmd]
        if missing_dep:
            raise ObservatoryError(f'{SUITE_REL}: {c["id"]}: unknown dependenc(ies) {missing_dep}')
        # §9.7 — a sample count is what actually runs, so a non-positive or non-integer one is a defect
        for scen, n in c['samples'].items():
            if not isinstance(n, int) or isinstance(n, bool) or n < 1:
                raise ObservatoryError(
                    f'{SUITE_REL}: {c["id"]}: sample count for {scen!r} is {n!r}; a count must be a positive '
                    f'integer, because it is the number of times the command is actually run')

    # §9.5 — a cycle closes under selection without ever reporting itself
    by_id = {c['id']: c for c in suite['commands']}

    def walk(cid: str, seen: tuple):
        if cid in seen:
            raise ObservatoryError(
                f'{SUITE_REL}: dependency cycle through {cid!r}: {" -> ".join(seen + (cid,))}')
        for dep in by_id[cid]['dependencies']:
            walk(dep, seen + (cid,))

    for cid in by_id:
        walk(cid, ())

    # §9.6 — a derived child is observed once per parent sample, so its scenarios and counts ARE its
    # parents'. Declaring its own list states the same fact twice and the two drift in both directions: a
    # scenario no parent runs can never be produced, and a scenario a parent does run gets observed and then
    # reported as undeclared.
    for c in suite['commands']:
        if c['measurement'] != 'derived':
            continue
        if c['scenarios'] or c['samples']:
            raise ObservatoryError(
                f'{SUITE_REL}: {c["id"]} is derived and declares its own scenarios or sample counts; a '
                f'derived child is observed once per parent sample, so both follow from its parents')
    return suite


def check_coverage(root: Path, suite: dict) -> str:
    """SURFACE <-> REGISTRY, both directions, for every surface the registry claims to classify.

    One direction alone is not coverage. Checking only that each entry still exists lets a new target go
    unclassified; checking only that each target has an entry lets a deleted one linger as a phantom."""
    live = {'make-target': {f'make.{t}' for t in make_targets(root)},
            'docker-stage': {f'docker.{s}' for s in docker_stages(root)}}
    anchors = set(hook_anchor_pairs(root))
    live['precommit-stage'] = anchors
    live['precommit-full'] = anchors

    declared: dict[str, set[str]] = {k: set() for k in DISCOVERED}
    for c in suite['commands']:
        if c['kind'] in declared:
            declared[c['kind']].add(c['id'])

    problems = []
    hook_declared = declared['precommit-stage'] | declared['precommit-full']
    for kind, surface in DISCOVERED.items():
        if kind in ('precommit-stage', 'precommit-full'):
            continue
        for missing in sorted(live[kind] - declared[kind]):
            problems.append(f'{surface} has {missing!r} with no registry entry')
        for stale in sorted(declared[kind] - live[kind]):
            problems.append(f'registry has {stale!r} but {surface} no longer declares it')
    for missing in sorted(anchors - hook_declared):
        problems.append(f'{HOOK_REL} anchors {missing!r} with no registry entry')
    for stale in sorted(hook_declared - anchors):
        problems.append(f'registry has {stale!r} but {HOOK_REL} carries no such anchor pair')

    for c in suite['commands']:
        path, _, token = c['owner'].partition(':')
        if not token:
            problems.append(f'{c["id"]}: owner {c["owner"]!r} names no token in its file')
            continue
        target = root / path
        if not target.is_file():
            problems.append(f'{c["id"]}: owner path {path!r} is not a file in this tree')
        elif token not in read_text(target, f'{c["id"]} owner'):
            problems.append(f'{c["id"]}: owner token {token!r} does not occur in {path}')

    if problems:
        raise ObservatoryError(
            f'{len(problems)} command-surface coverage defect(s): ' + '; '.join(problems[:8])
            + ('' if len(problems) <= 8 else f' … and {len(problems) - 8} more'))
    return (f'{len(suite["commands"])} command(s) classify {len(live["make-target"])} public Make target(s), '
            f'{len(anchors)} paired pre-commit anchor(s) and {len(live["docker-stage"])} Docker stage(s), '
            f'both directions; {len(suite["groups"])} group(s), {len(suite["scenarios"])} scenario(s); '
            f'every owner token resolves and none names a line number')


# ──────────────────────────────────────────────────────────── subject identity
def _git(root: Path, *args: str, check: bool = True) -> str:
    import subprocess
    proc = subprocess.run(['git', *args], cwd=root, capture_output=True, text=True)
    if check and proc.returncode != 0:
        raise ObservatoryError(f'git {" ".join(args)} failed in {root}: {proc.stderr.strip()}')
    return proc.stdout


def _sha256(data: bytes) -> str:
    import hashlib
    return hashlib.sha256(data).hexdigest()


def inventory_digest(root: Path) -> str:
    """One digest over every tracked path AND its blob hash, straight from the Git index.

    A commit id alone does not identify what was measured once the tree is dirty, and a path list alone does
    not notice an edited file. Hashing the index entries covers both without walking the filesystem."""
    entries = _git(root, 'ls-files', '-s')
    if not entries.strip():
        raise ObservatoryError(f'{root}: the Git index lists no files, so the subject cannot be identified')
    return _sha256(entries.encode('utf-8'))


SOURCE_VIEW_KINDS = ('committed-tree', 'staged-index', 'working-tree')


def source_view(root: Path, kind: str) -> dict:
    """The exact source a command will see — the ONE object that both identifies it and materialises it.

    Content alone was not a source view. Hashing bytes over tracked-plus-untracked files answered "what
    bytes were built" and nothing else, so a chmod-only change produced the same digest, a symlink was read
    through as though it were its target, and a staged index that differed from the working tree was
    described by the working tree's digest. The pre-commit path measured an exported INDEX while its sample
    carried a WORKING-TREE identity.

    So an entry carries path, Git mode (which is where the executable bit and the symlink type live) and
    either the blob identity or the link target. A tracked path deleted on disk is retained as an explicit
    ABSENCE rather than silently dropped, because absence is part of what the tree is.
    """
    import os
    import stat as _stat
    entries: list[str] = []
    deleted: list[str] = []
    if kind in ('staged-index', 'staged-index-export'):
        for line in _git(root, 'ls-files', '--stage', '-z').split('\0'):
            if not line:
                continue
            meta, path = line.split('\t', 1)
            mode, blob, _stage = meta.split()
            entries.append(f'{path}\t{mode}\t{blob}')
    elif kind == 'committed-tree':
        for line in _git(root, 'ls-tree', '-r', '-z', 'HEAD').split('\0'):
            if not line:
                continue
            meta, path = line.split('\t', 1)
            mode, _type, sha = meta.split()
            entries.append(f'{path}\t{mode}\t{sha}')
    elif kind == 'working-tree':
        tracked = {p for p in _git(root, 'ls-files', '-z').split('\0') if p}
        listing = _git(root, 'ls-files', '-z', '--cached', '--others', '--exclude-standard')
        for rel in sorted(p for p in listing.split('\0') if p):
            full = root / rel
            try:
                st = full.lstat()                  # lstat, so a symlink is a symlink and not its target
            except OSError:
                if rel in tracked:
                    deleted.append(rel)            # a tracked deletion IS part of the view
                continue
            if _stat.S_ISLNK(st.st_mode):
                entries.append(f'{rel}\t120000\t{os.readlink(full)}')
            elif _stat.S_ISREG(st.st_mode):
                entries.append(f'{rel}\t{"100755" if st.st_mode & 0o111 else "100644"}\t'
                               f'{_sha256(full.read_bytes())}')
            else:
                raise ObservatoryError(f'{rel}: neither a regular file nor a symlink, so this source view '
                                       f'cannot be reproduced exactly')
    else:
        raise ObservatoryError(f'source view {kind!r} is not one this tool can identify exactly')
    if not entries:
        raise ObservatoryError(f'{root}: no source files enumerated, so the subject cannot be identified')
    body = '\n'.join(sorted(entries) + [f'\x00absent\t{d}' for d in sorted(deleted)])
    return {'kind': kind, 'entry_count': len(entries), 'deleted': sorted(deleted),
            'id': _sha256(body.encode('utf-8'))}


def content_digest(root: Path) -> str:
    """The working-tree source view's identity."""
    return source_view(root, 'working-tree')['id']


def declared_source_digest(root: Path, command: dict) -> str | None:
    """The identity of the view this command DECLARES it reads, not always the working tree.

    A pre-commit sample measures an exported staged index; describing it with a working-tree digest named a
    tree the command never saw.
    """
    kind = command['source_view']
    if kind == 'environment-only':
        return None
    return source_view(root, {'staged-index-export': 'staged-index',
                              'disposable-copy': 'working-tree'}.get(kind, kind))['id']


def subject(root: Path) -> dict:
    """What exactly was measured. A dirty run says so and carries enough to tell two dirty runs apart."""
    dirty = bool(_git(root, 'status', '--porcelain=v2', '-z').strip('\0').strip())
    head = _git(root, 'rev-parse', 'HEAD').strip()
    tree = _git(root, 'rev-parse', 'HEAD^{tree}').strip()
    out = {'commit': head, 'tree': tree, 'inventory_digest': inventory_digest(root),
           'content_digest': content_digest(root),
           'dirty': dirty, 'source_view': 'working-tree' if dirty else 'committed-tree'}
    if dirty:
        out['head_commit'] = head
        out['working_tree_digest'] = out['content_digest']
    return out


# ──────────────────────────────────────────────────────── environment identity
def _pinned(root: Path) -> dict:
    """Toolchain identity read from the Dockerfile, which is where this repository PINS it.

    Asking a running container for its versions would report whatever happened to be there; the Dockerfile is
    the authority, and a drift between the two is a build defect rather than an environment reading."""
    text = read_text(root / DOCKERFILE_REL, 'Dockerfile')
    digests = dict(sorted(set(re.findall(r'^FROM\s+(\S+?)@(sha256:[0-9a-f]{64})', text, re.M))))
    versions = {}
    for pkg in ('rocq-core', 'rocq-stdlib', 'dune'):
        m = re.search(rf'\b{re.escape(pkg)}\.([0-9][0-9A-Za-z.+-]*)', text)
        versions[pkg] = m.group(1) if m else None
    m = re.search(r'ocaml/opam:debian-\d+-ocaml-([0-9.]+)', text)
    versions['ocaml'] = m.group(1) if m else None
    m = re.search(r'golang:([0-9.]+)-alpine', text)
    versions['go'] = m.group(1) if m else None
    if not digests or any(v is None for v in versions.values()):
        raise ObservatoryError(
            f'{DOCKERFILE_REL}: the pinned toolchain is not fully readable ({versions}); an observation may '
            f'not record an environment it could not identify')
    return {'base_image_digests': digests, 'toolchain_versions': versions}


def _concurrency(inspect: dict) -> dict:
    """Effective parallelism, decoded rather than captured.

    The first candidate recorded `make_jobs: " -- RECORD=1"` — the raw MAKEFLAGS string, which is not a job
    count and cannot be compared. Concurrency changes timing, so it belongs in the compatibility fingerprint
    as a NUMBER or as an explicit unknown.

    The provenance says HOW the count was decided, never the raw MAKEFLAGS text. MAKEFLAGS carries the
    variables of the invocation, so `ONLY=` and `SCENARIO=` end up in it; fingerprinting that string made
    every pair of runs with different selectors permanently incomparable for a reason unrelated to timing."""
    import os
    flags = os.environ.get('MAKEFLAGS', '')
    m = re.search(r'(?:^|\s)-?-j\s*(\d+)', flags)
    if m:
        jobs, source = int(m.group(1)), 'makeflags-explicit'
    elif re.search(r'(?:^|\s)-?-j(?:\s|$)', flags):
        jobs, source = 0, 'makeflags-unbounded'     # -j with no argument
    else:
        jobs, source = 1, 'default-serial'          # make is serial unless told otherwise
    bk = os.environ.get('BUILDKIT_MAX_PARALLELISM', '')
    return {'make_jobs': jobs, 'make_jobs_source': source,
            'buildkit_max_parallelism': int(bk) if bk.isdigit() else None,
            'buildkit_workers': inspect.get('Platforms', '').count(',') + 1 if inspect else None,
            'logical_cpus': os.cpu_count()}


def _host(root: Path, builder: str = None) -> dict:
    import os
    import platform
    import subprocess
    cpu_model = None
    try:
        for line in Path('/proc/cpuinfo').read_text(encoding='utf-8').split('\n'):
            if line.startswith('model name'):
                cpu_model = line.split(':', 1)[1].strip()
                break
    except OSError:
        pass
    mem_bytes = None
    try:
        for line in Path('/proc/meminfo').read_text(encoding='utf-8').split('\n'):
            if line.startswith('MemTotal:'):
                mem_bytes = int(line.split()[1]) * 1024
                break
    except OSError:
        pass

    def cmd(*args) -> str | None:
        try:
            p = subprocess.run(args, capture_output=True, text=True, timeout=30)
            return p.stdout.strip() or None
        except (OSError, subprocess.SubprocessError):
            return None

    # `docker buildx inspect --format` does not exist before buildx 0.14, and asking for it there returns a
    # usage error rather than a driver. Parse the human table once — every version prints it, and inspect
    # without --bootstrap does not start anything.
    # The first candidate inspected the developer's builder while the work ran on the observatory's, so
    # the observation carried the driver, BuildKit version and snapshotter of a builder that built nothing.
    inspect = dict(
        (k.strip(), v.strip())
        for k, _, v in (l.partition(':') for l in
                        (cmd('docker', 'buildx', 'inspect', builder or OBSERVATORY_BUILDER) or '').split('\n'))
        if v.strip())

    return {'platform': f'{platform.system()}/{platform.machine()}', 'kernel': platform.release(),
            'cpu_model': cpu_model, 'logical_cpus': os.cpu_count(), 'memory_bytes': mem_bytes,
            'filesystem_type': cmd('stat', '-f', '-c', '%T', str(root)),
            'measured_root': str(root),
            'docker_version': cmd('docker', 'version', '--format', '{{.Server.Version}}'),
            'buildx_version': cmd('docker', 'buildx', 'version'),
            'buildkit_identity': inspect.get('BuildKit version'),
            'builder_driver': inspect.get('Driver'),
            'buildkit_snapshotter': inspect.get('org.mobyproject.buildkit.worker.snapshotter'),
            'concurrency': _concurrency(inspect)}


# Fields whose value changes the timing a comparison may be made against. Free memory and load average are
# deliberately absent: they move between two runs on one machine, and folding them in would make every
# observation incomparable with every other.
FINGERPRINT_FIELDS = ('platform', 'kernel', 'cpu_model', 'logical_cpus', 'memory_bytes',
                      'docker_version', 'buildx_version', 'buildkit_identity', 'builder_driver',
                      'buildkit_snapshotter', 'filesystem_type', 'concurrency')


REQUIRED_ENVIRONMENT = ('platform', 'kernel', 'cpu_model', 'logical_cpus', 'memory_bytes',
                        'docker_version', 'buildx_version', 'buildkit_identity', 'builder_driver',
                        'buildkit_snapshotter', 'filesystem_type')


def check_environment_complete(env: dict) -> None:
    """Recording requires a COMPLETE environment, so an unread field fails rather than becoming null.

    A comparison decides compatibility from these values. A null one does not mean "the same as the other
    side"; it means nobody knows, and reporting a delta across it would be a number with no basis."""
    unread = [k for k in REQUIRED_ENVIRONMENT if env.get(k) in (None, '')]
    if unread:
        raise ObservatoryError(
            f'the environment is incomplete: {", ".join(unread)} could not be read; an observation may not '
            f'record an environment it could not identify')


def environment(root: Path, builder: str = None) -> dict:
    env = {**_host(root, builder), **_pinned(root)}
    env['builder'] = builder or OBSERVATORY_BUILDER
    stable = {k: env[k] for k in FINGERPRINT_FIELDS}
    stable['base_image_digests'] = env['base_image_digests']
    stable['toolchain_versions'] = env['toolchain_versions']
    env['host_class_fingerprint'] = _sha256(
        json.dumps(stable, sort_keys=True, ensure_ascii=False).encode('utf-8'))
    return env


# ──────────────────────────────────────────────────────────────────── selection
class Selection:
    """What one run will measure: the chosen commands, the support they pulled in, and the scenarios.

    `selected` and `support` stay distinct all the way into the observation. A dependency added on the user's
    behalf is real work and is measured, but it is not what the user asked about, and reporting the two as one
    set would let a selective run quietly present itself as broader than it was."""

    def __init__(self, selected: list[str], support: list[str], scenarios: list[str], partial: bool,
                 scenario_support: list[str] | None = None):
        self.selected, self.support = selected, support
        self.scenarios, self.partial = scenarios, partial
        self.scenario_support = scenario_support or []

    @property
    def order(self) -> list[str]:
        return self.support + self.selected


def _nearest(name: str, valid) -> str:
    import difflib
    close = difflib.get_close_matches(name, sorted(valid), n=3)
    return f'; nearest valid: {", ".join(close)}' if close else ''


def _expand(tokens: str, commands: dict, groups: dict, what: str) -> set[str]:
    chosen: set[str] = set()
    for raw in tokens.split(','):
        name = raw.strip()
        if not name:
            continue
        if name in commands:
            chosen.add(name)
        elif name in groups:
            chosen.update(groups[name])
        else:
            raise ObservatoryError(
                f'unknown {what} {name!r}{_nearest(name, set(commands) | set(groups))}')
    if not chosen:
        raise ObservatoryError(f'{what} selection expanded to nothing, so there is no work to measure')
    return chosen


def select(suite: dict, only: str | None = None, scenario: str | None = None,
           record: bool = False) -> Selection:
    """Resolve ONLY and SCENARIO into one closed, registry-ordered selection.

    Registry order is preserved rather than the order the user typed, so the same selection always runs the
    same way and two runs of one suite stay comparable. Dependencies are added automatically because a
    derived child measured without its live parent would be a number produced by a command the observatory
    invented rather than by the command the repository actually runs."""
    commands = {c['id']: c for c in suite['commands']}
    groups = {g['id']: list(g['members']) for g in suite['groups']}
    scenarios = {s['id']: s for s in suite['scenarios']}

    if record and (only or scenario):
        raise ObservatoryError(
            'RECORD=1 rejects ONLY and SCENARIO: a partial run cannot replace the canonical observation, '
            'because the file it would replace claims to be the whole suite')

    chosen = _expand(only, commands, groups, 'ONLY name') if only else set(commands)
    want_scenarios = (_expand(scenario, scenarios, {}, 'SCENARIO name') if scenario
                      else {sid for sid, s in scenarios.items() if s.get('canonical')})
    if not want_scenarios:
        raise ObservatoryError('no canonical scenario is declared, so the default run would measure nothing')

    closure, frontier = set(chosen), list(chosen)
    while frontier:
        cid = frontier.pop()
        for dep in commands[cid]['dependencies']:
            if dep not in closure:
                closure.add(dep)
                frontier.append(dep)

    order = [c['id'] for c in suite['commands'] if c['id'] in closure]
    selected = [cid for cid in order if cid in chosen]
    support = [cid for cid in order if cid not in chosen]

    runnable = [cid for cid in selected
                if set(commands[cid]['scenarios']) & want_scenarios
                or commands[cid]['measurement'] == 'derived']
    if not runnable:
        raise ObservatoryError(
            f'no selected command runs in scenario(s) {sorted(want_scenarios)}; '
            f'the registry owns the scenario matrix, and an empty run is not a result')

    # §5.5 — required setup is added automatically, and a cached or warm scenario REQUIRES the cold prime
    # of the same chain. Without it the run would name a prime it never took, and the provenance check would
    # correctly refuse every sample. Adding it is the same courtesy already extended to dependencies.
    needs_prime = any(family_rank(s) > 0 and s != 'environment.bootstrap' for s in want_scenarios)
    if needs_prime:
        colds = {c for cid in closure for c in commands[cid]['scenarios']
                 if c.startswith('project.cold.')}
        added = colds - want_scenarios
        if added:
            want_scenarios = want_scenarios | added

    partial = bool(only or scenario)
    return Selection(selected, support, sorted(want_scenarios), partial,
                     scenario_support=sorted(added) if needs_prime else [])


# ──────────────────────────────────────────────────────────────── measurement
RUNS_REL = '.build-observatory/runs'
# What `resource.getrusage` can honestly answer for. A command that shells out to Buildx does its real work
# in the daemon, so the wrapper's peak RSS is the wrapper's, not the build's. Saying which is measured is the
# difference between a number and a wrong number.
SCOPE_HOST = 'host-wrapper'
SCOPE_BUILDKIT = 'buildkit-stage'
SCOPE_UNAVAILABLE = 'unavailable'


def _monotonic_ns() -> int:
    import time
    return time.monotonic_ns()


def isolate(root: Path, command: dict, where: Path):
    """Contain a command's side effect for the duration of the sample, and return (cwd, env).

    A setup command that changes the machine cannot be measured in place and must not be excluded for
    having an effect — that would leave the surface unmeasured. Each isolation contains exactly what its
    command writes:

      disposable-copy         a detached worktree; the repository is untouched
      temporary-docker-config a private DOCKER_CONFIG and a throwaway builder name, so `buildx use`
                              switches a default nobody else reads
      temporary-git-repo      a standalone repository, because `git config` in a LINKED worktree writes the
                              config shared with the main checkout
    """
    kind = command.get('isolation')
    if kind is None:
        return None, {}
    if kind == 'disposable-copy':
        return where, {}
    if kind == 'temporary-docker-config':
        cfg = where / 'docker-config'
        cfg.mkdir(parents=True, exist_ok=True)
        return None, {'DOCKER_CONFIG': str(cfg),
                      'FIDO_OBSERVATORY_THROWAWAY_BUILDER': throwaway_builder(where)}
    if kind == 'temporary-git-repo':
        import subprocess
        repo = where / 'repo'
        repo.mkdir(parents=True, exist_ok=True)
        for args in (['init', '-q'], ['config', 'user.email', 'observatory@example.invalid'],
                     ['config', 'user.name', 'observatory']):
            subprocess.run(['git', *args], cwd=repo, check=True, capture_output=True)
        (repo / '.githooks').mkdir(exist_ok=True)
        (repo / 'Makefile').write_bytes((root / 'Makefile').read_bytes())
        return repo, {}
    raise ObservatoryError(f'{command["id"]}: isolation {kind!r} is declared but not implemented')


def throwaway_builder(scratch: Path) -> str:
    """The builder name a temporarily-isolated sample creates and destroys.

    Named in one place because three call sites must agree: the isolation that announces it, the invocation
    that must actually USE it, and the release that removes it."""
    return f'fido-throwaway-{scratch.name}'


def release_isolation(command: dict, where: Path, run) -> str | None:
    """Undo whatever the isolation created, and report a leak rather than hiding one.

    The builder is created under the sample's PRIVATE `DOCKER_CONFIG`, so removing it with the ambient
    environment always failed with `no builder found` — and the failure was discarded. `rmtree` then deleted
    that private config, erasing the registry entry and orphaning a running BuildKit container for good.
    Removal now runs against the same config that created it, BEFORE the directory goes, and says so when it
    cannot.

    `run` is the external-command effect, and it is REQUIRED rather than defaulted to `subprocess.run` on
    purpose: the deterministic self-test must exercise this decision logic on a machine with no Docker at
    all, and a default would let a future edit drop the injection and reach silently for the ambient
    `docker` binary again.  With no default, that edit is a `TypeError` at the call site instead.
    """
    import os
    import shutil
    problem = None
    if command.get('isolation') == 'temporary-docker-config':
        name = throwaway_builder(where)
        done = run(['docker', 'buildx', 'rm', name], capture_output=True, text=True,
                   env={**os.environ, 'DOCKER_CONFIG': str(where / 'docker-config')})
        if done.returncode != 0:
            problem = (f'{command["id"]}: could not remove the throwaway builder {name} '
                       f'({(done.stderr or done.stdout).strip().splitlines()[-1:] or ["no output"]})')
    shutil.rmtree(where, ignore_errors=True)
    return problem


def edit_probe(run_id: str, command_id: str, scenario_id: str) -> str:
    """The stamp written into an incremental edit's bytes, unique to this run, command and scenario.

    The RUN ID is the part that matters and the part that was missing. Without it the bytes are identical
    on every run, so the first run ever to use them pays the rebuild and every later run reads that result
    out of the BuildKit cache and records ~1.6s for work that costs ~116s. `edit_id` stays the comparison
    identity, so making the bytes run-unique costs no comparability.

    It is a DIGEST rather than the names themselves because the probe is written into a `.v` comment, and
    the M1 source law caps a comment at 120 characters. Spelled out it reached 136, so `make check` failed
    its own source-diet gate on every scenario that edits a `.v` file.
    """
    return _sha256(f'{run_id}.{command_id}.{scenario_id}'.encode('utf-8'))[:12]


def sample_provenance(command: dict, scenario: dict, primes: dict):
    """One provenance record for a sample, and the reason to skip it when its prime was never taken.

    Returns (provenance, skip_reason). Built in ONE place because there are two runners: three separate
    fixes today — the runner partition, the authority derivation, and the prime chain — each landed on the
    shell runner and left the analysis runner behind, every time because each had its own hand-built dict.
    """
    cid, sid = command['id'], scenario['id']
    # `cache_chain_id`, not `cache_namespace`. Every command shares ONE BuildKit store; this is a LOGICAL
    # causal chain, and calling it a namespace claimed a physical isolation that does not exist. What makes
    # a cold sample immune to another command's cache is the forced rebuild of its declared roots, not a
    # label. The chain id still distinguishes causal chains and still participates in prime validation.
    provenance = {'authorities': declared_authorities(command, scenario),
                  'host_page_cache': 'uncontrolled', 'builder': OBSERVATORY_BUILDER,
                  'chain_command': cid, 'cache_chain_id': f'{OBSERVATORY_BUILDER}:{cid}'}
    builds = bool(command['invalidation_roots'])
    if sid.startswith('project.cold.') or not builds or sid == 'environment.bootstrap':
        provenance['prime_sample_id'] = None
        return provenance, None
    key = (cid, 'prime')
    if key not in primes:
        return provenance, (f'{cid} [{sid}] skipped: this chain has no completed prime sample, and a cached '
                            f'number with no prime is a comparison against an unknown baseline')
    provenance['prime_sample_id'] = primes[key]['id']
    return provenance, None


def declared_authorities(command: dict, scenario: dict) -> dict:
    """The cache states that are true OF THIS COMMAND in this scenario.

    A command that invalidates no build root touches no project cache, so the scenario's generic `reused`
    states are not true of it. §3A.4 requires `not-applicable` rather than a state the runner cannot
    establish, and such a command has no prime to take either.
    """
    if not command['invalidation_roots']:
        return {k: 'not-applicable' for k in scenario['cache_state']}
    state = dict(scenario['cache_state'])
    # A scenario states a GENERIC cache posture; which of it is true depends on what this command builds.
    # A project cache none of whose stages this command reaches is `not-applicable` rather than inheriting
    # `empty` or `reused` — `make.prove` declaring the Go build cache empty described a cache its build
    # never comes near.
    reached = set(command.get('build_targets') or ())
    for k in PROJECT_CACHES:
        if k in state and not (set(CACHE_STAGES.get(k, ())) & reached):
            state[k] = 'not-applicable'
    return state


def host_load() -> float | None:
    """Report the host's 1-minute load average, or None where the kernel does not publish one.

    Wall-clock taken while the machine is busy with unrelated work is inflated by that work. This is
    recorded so a reader can see the condition; it is deliberately NOT a threshold and never rejects a
    sample, because a numeric cut-off invented here would stand in for a judgement nobody made.
    """
    try:
        return float(Path('/proc/loadavg').read_text().split()[0])
    except (OSError, ValueError, IndexError):
        return None


# Two runners, one partition. A shell runner spawns the command; the analysis runner performs the work in
# this process. `analysis.rocq-modules` declares `execution: ['observatory', ...]`, which is a marker rather
# than a program, so handing it to the shell runner tried to exec a binary named `observatory`.
ANALYSIS_KINDS = ('rocq-module-analysis', 'history-analysis')


def runner_for(command: dict) -> str | None:
    """Which runner owns this command: 'shell', 'analysis', or None for one that is never executed."""
    if command['measurement'] != 'direct':
        return None
    return 'analysis' if command['kind'] in ANALYSIS_KINDS else 'shell'


def sample_role(sel, cid: str, scenario_id: str) -> str:
    """Report whether a sample answers the operator's request or only supports it.

    A scenario the tool added on its own — the cold prime a warm selection needs — is support even when
    its command was named explicitly. Calling it `selected` would report a 130-second cold build as
    something the operator asked for.
    """
    if scenario_id in sel.scenario_support:
        return 'support'
    return 'selected' if cid in sel.selected else 'support'


def run_sample(root: Path, command: dict, scenario: dict, index: int, role: str,
               raw_dir: Path, cache_before: dict, cwd: Path | None = None,
               env_extra: dict | None = None, source_digest: str | None = None,
               edit_id: str | None = None) -> dict:
    """Run one command once and retain everything needed to defend the number afterwards.

    Duration is monotonic: a wall clock can step under NTP and produce a negative interval, and a timing tool
    that reports one has said something false rather than nothing.

    Resource use comes from `wait4` on THIS child, not from `RUSAGE_CHILDREN`. That aggregate is a high-water
    mark across every prior child of the observatory, so attributing it to one sample would report an earlier
    command's peak as this one's."""
    import datetime
    import os
    import subprocess

    scenario_id = scenario['id']
    raw_dir.mkdir(parents=True, exist_ok=True)
    log = raw_dir / (raw_log_name(command['id'], scenario_id, index, edit_id) + '.log')
    env = {**os.environ, **(env_extra or {})}
    start_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()

    load_before = host_load()
    t0 = _monotonic_ns()
    with log.open('wb') as sink:
        try:
            proc = subprocess.Popen(command['execution'], cwd=str(cwd or root), env=env,
                                    stdout=sink, stderr=subprocess.STDOUT)
        except OSError as exc:
            raise ObservatoryError(
                f'{command["id"]}: could not execute {command["execution"]!r} ({exc.__class__.__name__}: '
                f'{exc}); an unrunnable command is a defect in the registry, not a slow sample')
        _, status, usage = os.wait4(proc.pid, 0)
        proc.returncode = os.waitstatus_to_exitcode(status)
    wall_ns = _monotonic_ns() - t0
    load_after = host_load()

    if wall_ns < 0:
        raise ObservatoryError(
            f'{command["id"]}: the monotonic clock went backwards, which cannot happen; the sample is void')

    data = log.read_bytes()
    text = data.decode('utf-8', errors='replace')
    expected = command['expected_exit']
    status_word = 'ok' if proc.returncode == expected else 'unexpected-exit'
    reason = command.get('expected_failure_reason')
    if status_word == 'ok' and expected != 0 and reason and reason.encode('utf-8') not in data:
        status_word = 'wrong-failure-reason'

    stages = observe_stages(text)
    cut = dict(scenario['cache_cut'])
    cut['registry_pulls_included'] = pulled_from_registry(text)
    cut['builder_bootstrap_included'] = bootstrapped_builder(text)

    return {'command_id': command['id'], 'scenario_id': scenario_id, 'sample_index': index,
            'edit_id': edit_id, 'derived_parent_id': None,
            'sample_id': None, 'parent_sample_id': None,
            'selected_or_support': role, 'start_utc': start_utc, 'wall_ns': wall_ns,
            'user_cpu_ns': int(usage.ru_utime * 1e9), 'system_cpu_ns': int(usage.ru_stime * 1e9),
            'max_rss_bytes': usage.ru_maxrss * 1024, 'resource_scope': SCOPE_HOST,
            'measurement_kind': KIND_WALL,
            'host_load': {'before': load_before, 'after': load_after},
            'exit_code': proc.returncode, 'expected_exit': expected,
            'status': status_word, 'expected_failure_reason': reason,
            'cache_before': cache_before, 'cache_after': observe_cache_after(cache_before, stages),
            'cache_cut': cut, 'cache_observation': {'stages': stages},
            'source_digest': source_digest,
            'raw_log_sha256': _sha256(data), 'raw_log_bytes': len(data),
            'derived_stage_events': []}


ANCHOR_EVENT = re.compile(r'^(begin|end) (\S+) (\d+)$')
BUILDKIT_STEP = re.compile(r'^#(\d+) \[([^\]]+)\]')
BUILDKIT_DONE = re.compile(r'^#(\d+) (DONE ([0-9.]+)s|CACHED)\s*$')
# The hook's clock is CLOCK_MONOTONIC read from /proc/uptime, whose resolution is 10 ms. The observation
# records that rather than implying nanosecond precision it does not have.
HOOK_CLOCK = {'source': '/proc/uptime', 'kind': 'CLOCK_MONOTONIC', 'resolution_ns': 10_000_000}


def parse_anchor_log(text: str) -> list[dict]:
    """Hook stage durations from the anchor log the instrumented hook writes.

    The clock is monotonic, so an end before its begin cannot happen; if it does, the sample is void rather
    than reported as a negative duration."""
    open_at: dict[str, int] = {}
    events = []
    for line in text.split('\n'):
        stripped = line.strip()
        m = ANCHOR_EVENT.match(stripped)
        if not m:
            # A line that ANNOUNCES itself as an anchor and does not parse is a defect, not noise. The hook's
            # clock read `08` as octal and wrote an anchor with an empty timestamp; skipping it left the
            # anchor open, dropped the stage, and surfaced 100 minutes later as a coverage mismatch.
            if re.match(r'^(?:begin|end)\b', stripped):
                raise ObservatoryError(
                    f'malformed hook anchor {stripped!r}: an anchor line must carry a monotonic timestamp, '
                    f'so this sample lost a stage rather than measuring one')
            continue
        kind, anchor, ns = m.group(1), m.group(2), int(m.group(3))
        if kind == 'begin':
            open_at[anchor] = ns
        elif anchor in open_at:
            wall = ns - open_at.pop(anchor)
            if wall < 0:
                raise ObservatoryError(
                    f'hook anchor {anchor!r} ended before it began on a monotonic clock; every stage '
                    f'duration in this sample is void')
            if wall == 0:
                # The hook clock resolves to 10 ms, so a stage faster than one tick reads as exactly zero.
                # Zero is a measured claim and a false one: the stage ran. What is known is a BOUND — the
                # duration lies somewhere in [0, one tick) — and that is what gets retained, so a summary
                # can say "below resolution" instead of inventing a percentage against nothing.
                events.append({'id': anchor, 'wall_ns': None, 'source': 'hook-anchor',
                               'clock': HOOK_CLOCK, 'kind': KIND_INTERVAL,
                               'lower_ns': 0, 'upper_ns': HOOK_CLOCK['resolution_ns'],
                               'below_resolution': True})
            else:
                events.append({'id': anchor, 'wall_ns': wall, 'source': 'hook-anchor',
                               'clock': HOOK_CLOCK})
    if open_at:
        raise ObservatoryError(
            f'hook anchor(s) {sorted(open_at)} began and never ended; the stages they name are missing from '
            f'this sample and their absence would read as coverage')
    return events


def parse_buildkit_progress(text: str) -> list[dict]:
    """Per-stage step work from BuildKit's plain progress output.

    The value is the SUM of that stage's step durations. Parallel steps overlap, so it is aggregate step
    work and is named `aggregate_step_ns` — publishing it as elapsed wall time would be one number wearing
    another's name."""
    stage_of: dict[str, str] = {}
    totals: dict[str, int] = {}
    cached: dict[str, int] = {}
    for line in text.split('\n'):
        head = BUILDKIT_STEP.match(line.strip())
        if head:
            name = head.group(2).split()[0]
            if name != 'internal':
                stage_of[head.group(1)] = name
            continue
        done = BUILDKIT_DONE.match(line.strip())
        if done:
            name = stage_of.get(done.group(1))
            if not name:
                continue
            if done.group(3):
                totals[name] = totals.get(name, 0) + int(float(done.group(3)) * 1e9)
            else:
                cached[name] = cached.get(name, 0) + 1
    return sorted(
        ({'id': f'docker.{name}', 'aggregate_step_ns': totals.get(name, 0),
          'cached_steps': cached.get(name, 0), 'source': 'buildkit-progress'}
         for name in set(totals) | set(cached)),
        key=lambda e: e['id'])


def derive_child_samples(parent: dict, events: list[dict], known: set[str],
                         role_of=None) -> list[dict]:
    """One sample per derived child, from its parent's own events, keyed BY that parent.

    Merging one stage observed under four parents into a single median answers a question nobody asked, so
    the parent is part of the identity. CPU and memory are the parent's and are absent here."""
    out = []
    for event in events:
        if event['id'] not in known:
            continue
        buildkit = event['source'] == 'buildkit-progress'
        # The child's OWN role, not the parent's. Spreading the parent stamped a selected child `support`
        # whenever its live parent was support — `ONLY=docker.prover` is exactly that shape, and §3A.5 claims
        # the opposite in as many words.
        out.append({**parent, 'command_id': event['id'],
                    # The exact parent SAMPLE, not merely its command: one stage is observed under several
                    # parents and several repetitions, and naming only the command left a child that could
                    # not say which run of which parent produced it. `sample_id` is cleared so the child is
                    # stamped with its own rather than inheriting the parent's through the spread above.
                    'parent_sample_id': parent.get('sample_id'), 'sample_id': None,
                    'selected_or_support': (role_of(event['id']) if role_of
                                            else parent['selected_or_support']),
                    'derived_parent_id': parent['command_id'],
                    'wall_ns': None if (buildkit or event.get('untimed')) else event.get('wall_ns'),
                    'aggregate_step_ns': event.get('aggregate_step_ns'),
                    'untimed': bool(event.get('untimed')),
                    'cached_steps': event.get('cached_steps'),
                    'user_cpu_ns': None, 'system_cpu_ns': None, 'max_rss_bytes': None,
                    'resource_scope': SCOPE_BUILDKIT if buildkit else SCOPE_UNAVAILABLE,
                    # A BuildKit child contributes the SUM of its step durations; a hook anchor contributes
                    # a real elapsed interval; an artifact derived from another command's build contributes
                    # no duration at all. Naming which one it is here is what stops the summary from
                    # printing the first under the second's name, or the third as an exact zero.
                    'measurement_kind': (KIND_AGGREGATE if buildkit
                                         else KIND_UNTIMED if event.get('untimed')
                                         else event.get('kind') or KIND_WALL),
                    'lower_ns': event.get('lower_ns'), 'upper_ns': event.get('upper_ns'),
                    'below_resolution': bool(event.get('below_resolution')),
                    'measurement_source': event['source'],
                    'clock': event.get('clock'), 'derived_stage_events': []})
    return out


def analysis_sample(command_id: str, scenario: dict, role: str, wall_ns: int,
                    provenance: dict, events: list[dict], source_digest: str | None = None,
                    index: int = 0) -> dict:
    """A sample for work the observatory performs itself rather than shelling out for."""
    import datetime
    return {'command_id': command_id, 'scenario_id': scenario['id'], 'sample_index': index,
            'edit_id': None, 'derived_parent_id': None, 'selected_or_support': role,
            'sample_id': None, 'parent_sample_id': None,
            'start_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'wall_ns': wall_ns, 'user_cpu_ns': None, 'system_cpu_ns': None, 'max_rss_bytes': None,
            'resource_scope': SCOPE_UNAVAILABLE, 'measurement_kind': KIND_WALL,
            'exit_code': 0, 'expected_exit': 0, 'status': 'ok',
            'host_load': {'before': host_load(), 'after': host_load()},
            'expected_failure_reason': None, 'cache_before': provenance,
            'cache_after': dict(provenance, observed=True), 'cache_cut': dict(scenario['cache_cut']),
            'cache_observation': {'stages': {}}, 'source_digest': source_digest,
            'raw_log_sha256': None, 'derived_stage_events': events}


def raw_log_name(command_id: str, scenario_id: str, index: int, edit_id: str | None = None) -> str:
    """The full stable raw-log identity, so two samples can never share one path.

    The first candidate keyed logs by command, scenario and index only, so six edit shapes overwrote each
    other and the observation retained digests for files that were gone.

    There is no parent here.  Only DIRECT samples own a raw log — a derived sample is read out of its
    parent's evidence and carries `raw_log_sha256: None` — so a parent component could never be supplied by
    any caller, and the one that existed was dead weight reading as provenance.
    """
    parts = [command_id, scenario_id]
    if edit_id:
        parts.append(edit_id)
    parts.append(str(index))
    return '.'.join(parts)


# BuildKit prints one of these per step. `CACHED` is a hit; a `DONE` on a step that was not cached is work
# that actually ran. Inferring either from elapsed time is the thing the contract forbids.
_BK_CACHED = re.compile(r'^#(\d+) CACHED\s*$')
_BK_DONE = re.compile(r'^#(\d+) DONE\s+[0-9.]+s\s*$')
# A real pull moves bytes or extracts a layer. `resolve <ref> 0.1s done` is LOCAL reference resolution and
# is not a pull — matching it would fail every canonical sample on a machine that already has the images,
# which is precisely the machine the amendment says to measure on.
_BK_PULL = re.compile(r'^#\d+ (?:extracting |pulling image |sha256:\S+ [0-9.]+[KMG]?B / )', re.I)
# Builder bootstrap is a BuildKit step, not an English word. Matching a bare `bootstrap` anywhere in the
# log matched this tool's OWN control names, printed by the mutation harness the pre-commit hook runs, and
# rejected a valid cold sample for a builder nobody created.
_BK_BOOTSTRAP = re.compile(
    r'^#\d+ (?:\[internal\] booting buildkit|creating container buildx_buildkit_)', re.I)


# One buildx invocation numbers its steps from #1. A command that runs several — the pre-commit hook runs
# one per stage it verifies — concatenates them into one log, and the numbers START OVER. This line is where
# one invocation ends and the next begins.
_BK_INVOCATION = re.compile(r'^#0 building with ')


def observe_stages(text: str) -> dict:
    """Per-stage hit / rebuilt state, read from BuildKit rather than inferred from elapsed time.

    A stage's FROM step is base-image RESOLUTION, and it reports DONE even when the image is already local.
    Counting that as work would report every stable ancestor as rebuilt, which is exactly the claim a
    project-cold sample must be able to deny. Only an executed non-FROM step means the stage rebuilt.

    A step number identifies a step only WITHIN its invocation, so the log is split per invocation before
    anything is attributed. Resolving `#27` against a map built from the whole file reported `rocq-base` as
    rebuilt from another build's ordinal, which is the copied-ordinal failure in log form."""
    segments, current = [], []
    for line in text.split('\n'):
        if _BK_INVOCATION.match(line.strip()) and current:
            segments.append(current)
            current = []
        current.append(line)
    segments.append(current)

    cached, ran, seen = {}, {}, set()
    for segment in segments:
        stage_of, is_from = {}, {}
        for line in segment:
            head = BUILDKIT_STEP.match(line.strip())
            if head:
                step, label = head.group(1), head.group(2)
                name = label.split()[0]
                if name == 'internal':
                    continue
                if stage_of.get(step, name) != name:
                    raise ObservatoryError(
                        f'step #{step} names both {stage_of[step]!r} and {name!r} in one invocation; the log '
                        f'holds concatenated builds this reader failed to separate, and every stage state '
                        f'read from it would be attributed to the wrong stage')
                stage_of[step] = name
                seen.add(name)
                rest = line.strip()[head.end():].strip()
                if rest.startswith('FROM '):
                    is_from[step] = True
                continue
            m = _BK_CACHED.match(line.strip())
            if m and m.group(1) in stage_of:
                name = stage_of[m.group(1)]
                cached[name] = cached.get(name, 0) + 1
                continue
            m = _BK_DONE.match(line.strip())
            if m and m.group(1) in stage_of and not is_from.get(m.group(1)):
                name = stage_of[m.group(1)]
                ran[name] = ran.get(name, 0) + 1
    out = {}
    for name in sorted(seen):
        if ran.get(name):
            out[name] = 'rebuilt'
        elif cached.get(name):
            out[name] = 'hit'
        else:
            out[name] = 'unavailable'
    return out


def pulled_from_registry(text: str) -> bool:
    """Whether an image was fetched inside the measured interval, which a canonical sample forbids."""
    return any(_BK_PULL.match(l.strip()) for l in text.split('\n'))


def bootstrapped_builder(text: str) -> bool:
    """Whether a builder was booted inside the measured interval, which a canonical sample forbids."""
    return any(_BK_BOOTSTRAP.match(l.strip()) for l in text.split('\n'))


def observe_cache_after(before: dict, stages: dict) -> dict:
    """The state AFTER the command, observed. Copying `cache_before` was the first candidate's false record:
    a command that built the whole theory reported that nothing changed."""
    after = {k: v for k, v in before.items() if k != 'authorities'}
    authorities = dict(before.get('authorities', {}))
    for k in PROJECT_CACHES:
        if k not in authorities or authorities[k] == 'not-applicable':
            continue
        # Derived from the stages that touch THIS authority, never from "did anything rebuild". The old
        # rule marked every project cache primed whenever one stage ran, so a `make.prove` sample claimed
        # the Go build cache and the generated intermediates had been filled by a run that compiled no Go
        # and generated nothing.
        touched = [stages[st] for st in CACHE_STAGES.get(k, ()) if st in stages]
        if not touched:
            continue
        if 'rebuilt' in touched:
            authorities[k] = 'primed'
    after['authorities'] = authorities
    after['observed'] = True
    return after


def run_id_for(subject_info: dict, started_utc: str, digest: str) -> str:
    """Descriptive, not authority — but it must not collide.

    The first candidate dropped fractional seconds, so two runs of one subject started inside the same second
    produced the same path and could overwrite each other. Full precision plus a random part makes that
    impossible; `new_bundle` additionally refuses a path that already exists."""
    import secrets
    stamp = started_utc.replace(':', '').replace('-', '').replace('.', '').replace('+', 'p')
    return f'{stamp}-{subject_info["commit"][:7]}-{digest[:8]}-{secrets.token_hex(3)}'


def new_bundle(root: Path, run_id: str, bundle_root: Path | None = None) -> Path:
    """A fresh bundle. Reusing an existing path would let one run overwrite another's evidence.

    `bundle_root` puts the ACTIVE bundle outside every measured source tree.  Written inside the repository,
    a run's own growing raw logs join the input of every later sample: one exact source subject then times
    differently depending on how much old residue happens to be lying around, and the observer has changed
    what it observes.  The containerized runner mounts a directory outside the repository and names it here.
    """
    bundle = (bundle_root / run_id) if bundle_root else (root / RUNS_REL / run_id)
    if bundle.exists():
        raise ObservatoryError(f'{bundle}: a bundle already exists at this run id; refusing to overwrite '
                               f'another run\'s evidence')
    (bundle / 'raw').mkdir(parents=True, exist_ok=True)
    return bundle


def checkpointer(bundle: Path, header: dict):
    """Write the local observation after every completed sample.

    The first candidate wrote it only when the suite returned, so a suite that was KILLED left raw logs and
    nothing to inspect. The safety half held — a cancelled run can never record — but the evidence half only
    worked on the failure path."""
    def write(samples: list[dict], incomplete: list[str]):
        partial = {**header, 'measurements': samples,
                   'derived': {'summaries': summarise(samples), 'status': 'incomplete',
                               'incomplete': list(incomplete)}}
        write_json(bundle / 'observation.json', partial)

    # Write it once at creation. A bundle that only becomes inspectable after the FIRST sample completes
    # leaves the longest samples — the expensive ones, the ones most likely to be interrupted — with a
    # directory that says nothing about what was being attempted.
    write([], [])
    return write


def verify_raw_logs(root: Path, bundle: Path, obs: dict) -> str:
    """Every DIRECT sample's raw log must exist and still match its retained digest.

    A digest for a file that is gone is a claim nobody can check, and a changed log means the evidence and
    the number no longer describe the same run. A derived sample names its parent's log rather than
    inventing one of its own."""
    missing, changed = [], []
    for s in obs['measurements']:
        if s.get('derived_parent_id') or s.get('raw_log_sha256') is None:
            continue
        name = raw_log_name(s['command_id'], s['scenario_id'], s['sample_index'], s.get('edit_id'))
        log = bundle / 'raw' / f'{name}.log'
        if not log.is_file():
            missing.append(name)
        elif _sha256(log.read_bytes()) != s['raw_log_sha256']:
            changed.append(name)
    if missing or changed:
        raise ObservatoryError(
            f'{len(missing)} raw log(s) absent and {len(changed)} changed since they were measured; '
            f'first {(missing + changed)[:3]}')
    direct = sum(1 for s in obs['measurements'] if not s.get('derived_parent_id'))
    return f'{direct} direct raw log(s) present and matching their retained digests'


def canonical_bytes(obj) -> bytes:
    """One writer for every canonical file here, so a digest taken over one is comparable with the other."""
    return (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=False) + '\n').encode('utf-8')


def suite_digest_of(suite: dict) -> str:
    return _sha256(canonical_bytes(suite))


def write_json(path: Path, obj) -> bytes:
    data = canonical_bytes(obj)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return data


KIND_WALL = 'wall_elapsed'
KIND_AGGREGATE = 'aggregate_step_work'
KIND_INTERVAL = 'duration_interval'
KIND_UNTIMED = 'untimed_artifact'
MEASUREMENT_KINDS = (KIND_WALL, KIND_AGGREGATE, KIND_INTERVAL, KIND_UNTIMED,
                     'cpu_user', 'cpu_system', 'rss_peak')


def measured(sample: dict) -> tuple[int | None, str]:
    """The one number a sample contributes to a summary, and WHAT KIND of number it is.

    Elapsed wall time and the sum of BuildKit step durations are different measurements: steps that run in
    parallel make aggregate work exceed elapsed time, so pooling them or printing one under the other's name
    states something false. The kind travels with the value from here on, and it is part of the identity, so
    two kinds can never land in one median.
    """
    kind = sample.get('measurement_kind') or KIND_WALL
    if kind == KIND_UNTIMED:
        # An artifact derived from another command's build has no duration of its own. It was retained as
        # `wall_ns: 0`, which is a measured claim and a false one — work happened. It is an ARTIFACT now, so
        # it stays in the record and out of every median.
        return None, kind
    if kind == KIND_AGGREGATE:
        return sample.get('aggregate_step_ns'), kind
    return sample.get('wall_ns'), kind


def metric_identity(sample: dict) -> str:
    """The one identity every sample, summary, comparison row, log path and citation uses.

    The first candidate keyed on command and scenario alone, so six edit shapes shared one median and one
    Docker stage observed under four parents shared another. An identity that omits what distinguishes two
    measurements makes them look like repetitions of one.

    Role and measurement kind are in the key for the same reason: a selected child mislabelled `support`, or
    aggregate step work sitting beside elapsed wall time, would otherwise close the coverage relation while
    describing a different measurement than the one the registry required."""
    return '|'.join((sample['command_id'], sample['scenario_id'],
                     sample.get('edit_id') or '-', sample.get('derived_parent_id') or '-',
                     sample.get('selected_or_support') or '-',
                     sample.get('resource_scope') or '-',
                     sample.get('measurement_kind') or KIND_WALL))


def docker_context_inputs(root: Path) -> list[str]:
    """Every path pattern the Dockerfile COPYs FROM THE BUILD CONTEXT, in Dockerfile order.

    `COPY --from=<stage>` is excluded: that moves bytes between stages and names nothing in the context, so
    counting it would make every stage output look like a repository input.
    """
    patterns: list[str] = []
    for line in read_text(root / DOCKERFILE_REL, 'Dockerfile').split('\n'):
        s = line.strip()
        if not s.upper().startswith('COPY ') or '--from=' in s:
            continue
        parts = [p for p in s.split()[1:] if not p.startswith('--')]
        patterns.extend(parts[:-1])                # the last operand is the destination
    return patterns


def is_build_input(rel_path: str, patterns: list[str]) -> bool:
    """Whether editing this path can invalidate a Docker stage at all.

    Derived from the Dockerfile's own COPY set rather than declared a second time beside it. A tool or a
    document that no stage copies cannot rebuild anything, and an incremental sample that claims otherwise
    is describing work that did not happen.
    """
    import fnmatch
    for pat in patterns:
        clean = pat.rstrip('/')
        if fnmatch.fnmatch(rel_path, clean) or fnmatch.fnmatch(rel_path, f'{clean}/*'):
            return True
        if '/' not in clean and fnmatch.fnmatch(rel_path.split('/')[-1], clean) and '/' not in rel_path:
            return True
    return False


def check_edit_effect(sample: dict, edit: dict, command: dict, patterns: list[str]) -> None:
    """The intended invalidation actually happened, not merely that the edit bytes differed.

    Unique bytes prove the runner did not reuse a previous sample's result. They do NOT prove the edit
    reached the build: a future `.v` incremental sample whose stages were all cache hits would have been
    accepted, and it would have reported a rebuild cost for a rebuild that never ran.
    """
    stages = (sample.get('cache_observation') or {}).get('stages', {})
    if not stages or not command.get('build_targets'):
        return                                     # a command that drives no Docker graph claims nothing
    rebuilt = sorted(st for st, state in stages.items() if state == 'rebuilt')
    where = f'{sample["command_id"]} [{sample["scenario_id"]}] {edit["id"]}'
    if is_build_input(edit['path'], patterns):
        if not rebuilt:
            raise ObservatoryError(
                f'{where}: {edit["path"]!r} is copied into the build, yet every stage was a cache hit; this '
                f'sample reports the cost of a rebuild that never ran')
    elif rebuilt:
        raise ObservatoryError(
            f'{where}: {edit["path"]!r} is copied into no stage, yet {rebuilt} rebuilt; the edit cannot be '
            f'what invalidated them, so this sample attributes work to the wrong cause')


def sample_id_for(run_id: str, sample: dict) -> str:
    """The identity of ONE retained sample, distinct from the metric CLASS it belongs to.

    `prime_sample_id` used to hold a metric class — `make.prove|project.cold.prover|-|-|host-wrapper` — and
    the record-time check could then only prove that SOME retained metric of that class was cold and
    successful. It could not prove the reused sample descended from the exact prime that populated its
    cache. A class is not an identity: it omits the run, the sample index, and therefore which of three
    repetitions is being named.
    """
    return f'{run_id}#{metric_identity(sample)}#{sample["sample_index"]}'


def check_cut_observed(sample: dict, scenario: dict, suite: dict, graph: dict | None = None) -> None:
    """What the scenario DECLARED against what BuildKit actually did.

    A declared cut is a claim about the run. Left unchecked it is exactly the defect that blocked the first
    candidate: a label describing work that had already been done by something else."""
    cut, stages = sample['cache_cut'], sample['cache_observation']['stages']
    if cut['registry_pulls_included'] and scenario.get('canonical'):
        raise ObservatoryError(
            f'{sample["command_id"]} [{scenario["id"]}]: an image was pulled inside the measured interval, '
            f'so this is machine setup rather than canonical project evidence')
    if cut['builder_bootstrap_included'] and scenario.get('canonical'):
        raise ObservatoryError(
            f'{sample["command_id"]} [{scenario["id"]}]: the builder was bootstrapped inside the measured '
            f'interval, which the cache cut excludes')
    roots = list(cut.get('invalidated_roots') or [])
    cold = scenario['id'].startswith('project.cold.')
    # A cold claim needs evidence FOR it, not merely the absence of evidence against it. Two commands
    # discard their build output on purpose, and their cold samples were passing this check vacuously:
    # no stage map, nothing to contradict, cold by default.
    for root in roots if cold else []:
        if stages.get(root) is None:
            raise ObservatoryError(
                f'{sample["command_id"]} [{scenario["id"]}]: no observed state for the invalidation root '
                f'{root!r}, so its cold claim rests on absent evidence; record `unavailable` and do not '
                f'call it cold')
    if not stages:
        return                                     # a command that drives no BuildKit graph claims nothing
    stable = cut.get('stable_through')
    if stable and stages.get(stable) == 'rebuilt':
        raise ObservatoryError(
            f'{sample["command_id"]} [{scenario["id"]}]: the declared stable ancestor {stable!r} rebuilt, so '
            f'this measured more than the cut says it did')
    for root in roots if cold else []:
        if stages[root] != 'rebuilt':
            raise ObservatoryError(
                f'{sample["command_id"]} [{scenario["id"]}]: the invalidation root {root!r} was '
                f'{stages[root]}, not rebuilt; a cold sample whose root stayed cached is not a cold sample')
    if not cold:
        return

    # Every OTHER rebuilt stage must be explained by a declared root: either it is one, or it is downstream
    # of one. An undeclared INDEPENDENT root is the defect this closes — `make audit-fresh` forces `prover`
    # and `go-e2e` separately, declared only `prover`, and the extra rebuild was invisible because nothing
    # asked what else had run.
    graph = graph or {}
    reachable = set(roots)
    if graph:
        frontier = list(roots)
        while frontier:
            stage = frontier.pop()
            for child, parents in graph.items():
                if stage in parents and child not in reachable:
                    reachable.add(child)
                    frontier.append(child)
    unexplained = sorted(st for st, state in stages.items()
                         if state == 'rebuilt' and st not in reachable and st != stable)
    if unexplained and graph:
        raise ObservatoryError(
            f'{sample["command_id"]} [{scenario["id"]}]: stage(s) {unexplained} rebuilt but are neither a '
            f'declared invalidation root {sorted(roots)} nor downstream of one; an undeclared independent '
            f'root means the cut describes less work than the sample did')


def definition_fingerprints(suite: dict) -> dict:
    """A digest per DEFINITION, so a changed meaning makes a metric incomparable rather than regressed.

    Fingerprinting commands alone left two observations comparable across a changed scenario meaning, a
    changed edit procedure or a changed sample policy — a delta between two different questions."""
    return {
        'commands': {c['id']: _sha256(canonical_bytes(c)) for c in suite['commands']},
        'scenarios': {s['id']: _sha256(canonical_bytes(s)) for s in suite['scenarios']},
        'edits': {e['id']: _sha256(canonical_bytes(e)) for e in suite.get('edits', [])},
        'stable_through': suite.get('stable_through'),
    }


def repeated_work(suite: dict, samples: list[dict]) -> dict:
    """Containment and repeated execution by stable ID, as machine-readable fact rather than prose.

    M2 records that a check runs the same policy gate the hook runs; M3 decides whether either is safe to
    drop. Recording the relation is the part M2 owes."""
    by_id = {c['id']: c for c in suite['commands']}
    contains: dict[str, list[str]] = {}
    for c in suite['commands']:
        for dep in c['dependencies']:
            contains.setdefault(dep, []).append(c['id'])

    # A policy performed both by a Make target and by a hook stage is repeated execution. Which policy a
    # command performs is DECLARED: inferring it from name similarity matched some pairs by coincidence of
    # spelling and missed others entirely.
    by_policy: dict[str, dict] = {}
    for c in suite['commands']:
        if not c.get('policy'):
            continue
        side = 'make' if c['kind'] == 'make-target' else (
            'hook' if c['kind'] in ('precommit-stage', 'precommit-full') else 'other')
        by_policy.setdefault(c['policy'], {}).setdefault(side, []).append(c['id'])
    repeated = []
    for policy, sides in sorted(by_policy.items()):
        if 'make' in sides and 'hook' in sides:
            repeated.append({'policy': policy, 'make_commands': sorted(sides['make']),
                             'hook_stages': sorted(sides['hook']),
                             'reason': 'the working tree and the proposed commit are different subjects, '
                                       'so both runs are wanted; the cost of running both is the finding'})
    measured = {s['command_id'] for s in samples}
    return {'containment': {k: sorted(v) for k, v in sorted(contains.items())},
            'repeated_execution': sorted(repeated, key=lambda r: r['policy']),
            'measured_commands': sorted(measured)}


def observed_load(samples: list[dict]) -> dict:
    """The host load actually seen across a run, so the condition each number was taken under is readable.

    Reported, never judged. A threshold here would be a magic number standing in for a judgement nobody
    made, and load is deliberately absent from the comparison fingerprint because it moves between two runs
    on one machine."""
    seen = [v for s in samples
            for v in ((s.get('host_load') or {}).get('before'), (s.get('host_load') or {}).get('after'))
            if isinstance(v, (int, float))]
    if not seen:
        return {'samples': 0, 'min': None, 'max': None, 'unavailable': True}
    return {'samples': len(seen), 'min': min(seen), 'max': max(seen), 'unavailable': False}


def summarise(samples: list[dict]) -> dict:
    """Derived median, minimum and maximum, alongside the samples they came from — never instead of them.

    An average alone cannot be rechecked and hides the spread that decides whether a delta means anything.
    The validator recomputes every value here from the retained samples."""
    by_key: dict[str, list[int]] = {}
    kinds: dict[str, str] = {}
    intervals: dict[str, dict] = {}
    for s in samples:
        value, kind = measured(s)
        key = metric_identity(s)
        if kind == KIND_INTERVAL:
            # A stage faster than one clock tick has a BOUND, not a value. It gets a summary row carrying
            # that bound, so the report can say "below resolution" rather than either dropping the stage or
            # printing a median of zero it could then compute a percentage against.
            row = intervals.setdefault(key, {'samples': 0, 'measurement_kind': kind,
                                             'below_resolution': True, 'lower_ns': 0, 'upper_ns': 0})
            row['samples'] += 1
            row['lower_ns'] = min(row['lower_ns'], s.get('lower_ns') or 0)
            row['upper_ns'] = max(row['upper_ns'], s.get('upper_ns') or 0)
            continue
        if value is None:
            continue
        by_key.setdefault(key, []).append(value)
        kinds[key] = kind
    out = {}
    for key, values in sorted(by_key.items()):
        ordered = sorted(values)
        mid = len(ordered) // 2
        median = ordered[mid] if len(ordered) % 2 else (ordered[mid - 1] + ordered[mid]) // 2
        # `median_ns`, not `median_wall_ns`: the field carried aggregate step work for every derived
        # BuildKit child while calling it elapsed wall time, and the comparator and report repeated the
        # claim. The kind is stated beside the number instead of assumed by the field's name.
        out[key] = {'samples': len(ordered), 'measurement_kind': kinds[key], 'median_ns': median,
                    'min_ns': ordered[0], 'max_ns': ordered[-1]}
    return dict(sorted({**out, **intervals}.items()))


# ────────────────────────────────────────────────────────── cache provenance
OBSERVATORY_BUILDER = 'fido-observatory'
CACHE_AUTHORITIES = PROJECT_CACHES + STABLE_CACHES
CACHE_STATES = ('empty', 'primed', 'reused', 'not-applicable', 'uncontrolled')


def _assert_observatory_builder(name: str) -> None:
    """The one guard between a measurement and a developer's afternoon.

    Every destructive cache operation routes through here. The observatory owns exactly one builder; being
    handed any other name is a bug in the observatory, and pruning someone else's build cache to produce a
    cold number is not a trade this project makes."""
    if name != OBSERVATORY_BUILDER:
        raise ObservatoryError(
            f'refusing to modify builder {name!r}: the observatory may only create, prune or remove '
            f'{OBSERVATORY_BUILDER!r}, and never the developer\'s builder or its cache')


STABLE_BASES = ('rocq-base', 'python-tools')


def toolchain_prime(root: Path, progress=print) -> dict:
    """Establish every stable base so a cold PROJECT build is not also a toolchain download.

    `project.cold.prover` and `bootstrap.project.cold.prover` are different questions: the first asks what
    building this project costs, the second what starting from nothing costs. Without this step they collapse
    into one number dominated by apt and opam.

    It returns what it did rather than only doing it, because the observation has to be able to say that the
    bootstrap and the registry pulls happened OUTSIDE every measured interval. A preflight nobody can see in
    the record is indistinguishable from one that never ran.
    """
    import subprocess
    primed = []
    for target in STABLE_BASES:
        progress(f'fido: observe — priming stable base {target} (outside every measured interval)')
        proc = subprocess.run(
            ['docker', 'buildx', 'build', '--builder', OBSERVATORY_BUILDER, '--platform', 'linux/amd64',
             '--target', target, '.'], cwd=str(root), capture_output=True, text=True)
        if proc.returncode != 0:
            raise ObservatoryError(f'the stable-base prime for {target} failed: {proc.stderr.strip()[-400:]}')
        primed.append(target)
    return {'stable_bases_primed': primed, 'required': True,
            'note': 'builder bootstrap and registry pulls happen here, before any measured interval'}



def apply_edit(copy_root: Path, edit: dict, index: int = 0, probe: str = '') -> None:
    """Apply one named edit to a DISPOSABLE copy, and prove exactly one file changed.

    The real working tree is never touched. Verifying that the intended file changed AND that nothing else
    did is the half that matters: an edit scenario whose blast radius is wrong measures a rebuild nobody
    asked about and attributes it to the wrong shape.

    `probe` carries the OWNING COMMAND into the bytes. Distinct bytes per sample INDEX stopped a command
    from being its own cache hit; it did nothing about four commands whose sample 0 wrote the same probe to
    the same file, produced the same tree, and let whichever ran first pay for all of them."""
    target = copy_root / edit['path']
    if not target.is_file():
        raise ObservatoryError(f'edit {edit["id"]}: {edit["path"]} is not a file in the disposable copy')
    original = target.read_bytes()
    if edit['kind'] == 'append-comment-line':
        if not original.endswith(b'\n'):
            raise ObservatoryError(f'edit {edit["id"]}: {edit["path"]} does not end in a newline')
        # Unique across the whole suite: `{n}` separates samples, the probe separates commands.
        stamp = f'{probe}-{index}' if probe else str(index)
        target.write_bytes(original + edit['text'].format(n=stamp).encode('utf-8'))
    else:
        raise ObservatoryError(f'edit {edit["id"]}: unknown edit kind {edit["kind"]!r}')
    return None


def disposable_copy(root: Path, dest: Path, view_kind: str = 'committed-tree') -> Path:
    """An exact, throwaway copy of the SELECTED source view — never silently of HEAD.

    The first candidate always took HEAD. On a dirty run its non-mutating samples ran in the dirty tree while
    its incremental samples ran at HEAD, so one observation contained samples from two different source trees
    under one subject. A worktree is used because a plain copy breaks every target that reads the index; for
    a dirty view the uncommitted bytes are then applied on top, so the copy is what was really there."""
    import os
    import shutil
    import stat as _stat
    _git(root, 'worktree', 'add', '--detach', '--quiet', str(dest), 'HEAD')
    if view_kind == 'working-tree':
        listing = [p for p in _git(root, 'ls-files', '-z', '--cached', '--others',
                                   '--exclude-standard').split('\0') if p]
        present = set()
        for rel in listing:
            src, dst = root / rel, dest / rel
            try:
                st = src.lstat()
            except OSError:
                continue                           # a tracked deletion: handled below, never copied back
            present.add(rel)
            dst.parent.mkdir(parents=True, exist_ok=True)
            if dst.is_symlink() or dst.exists():
                dst.unlink()
            if _stat.S_ISLNK(st.st_mode):
                # Reproduced AS a symlink. Copying through it wrote the target's bytes into a regular file,
                # which is a different tree than the one being measured.
                os.symlink(os.readlink(src), dst)
            elif _stat.S_ISREG(st.st_mode):
                shutil.copy2(src, dst)
        # A tracked file DELETED in the working tree must be absent here too. The worktree starts at HEAD,
        # so without this the deletion was silently reintroduced and the copy measured a tree that no
        # longer existed.
        for rel in [p for p in _git(root, 'ls-files', '-z').split('\0') if p]:
            if rel not in present:
                (dest / rel).unlink(missing_ok=True)
    elif view_kind != 'committed-tree':
        raise ObservatoryError(
            f'disposable copy: source view {view_kind!r} is not one this tool can materialise exactly')

    # The materialised tree must BE the view that was selected. Identity and materialisation come from one
    # object precisely so this can be asserted rather than assumed; two parallel authorities disagreed.
    want = source_view(root, view_kind)['id']
    got = source_view(dest, view_kind)['id']
    if want != got:
        raise ObservatoryError(
            f'the disposable copy of the {view_kind} view is not that view ({want[:12]} vs {got[:12]}); '
            f'every sample taken in it would describe a tree nobody selected')
    return dest


def drop_disposable_copy(root: Path, dest: Path) -> None:
    _git(root, 'worktree', 'remove', '--force', str(dest), check=False)


def tree_digest(root: Path, paths: list[str]) -> str:
    parts = []
    for rel in sorted(paths):
        f = root / rel
        parts.append(f'{rel}:{_sha256(f.read_bytes()) if f.is_file() else "absent"}')
    return _sha256('\n'.join(parts).encode('utf-8'))


def restore_and_verify(copy_root: Path, edit: dict, original: bytes, before_digest: str,
                       paths: list[str], index: int = 0) -> None:
    """Put the exact bytes back and prove it, or the next sample measures a tree nobody described."""
    (copy_root / edit['path']).write_bytes(original)
    after = tree_digest(copy_root, paths)
    if after != before_digest:
        raise ObservatoryError(
            f'edit {edit["id"]}: the disposable copy did not restore byte-exactly '
            f'({before_digest[:12]} -> {after[:12]}); every later sample in this scenario is void')


# ──────────────────────────────────────────────────────── observation and record
OBSERVATION_MEMBERS = ('schema', 'suite_digest', 'subject', 'environment', 'cache_model', 'commands',
                       'measurements', 'module_graph', 'history_analysis', 'derived', 'selection')
SAMPLE_FIELDS = ('command_id', 'scenario_id', 'sample_index', 'edit_id', 'derived_parent_id',
                 'selected_or_support', 'start_utc', 'user_cpu_ns', 'system_cpu_ns',
                 'sample_id', 'parent_sample_id',
                 'max_rss_bytes', 'resource_scope', 'measurement_kind',
                 'host_load', 'exit_code', 'expected_exit', 'status',
                 'cache_before', 'cache_after', 'cache_cut', 'cache_observation', 'source_digest',
                 'raw_log_sha256', 'expected_failure_reason', 'derived_stage_events')

# Each rule is stated once, here, and checked by the function below in this order. A recording that skipped
# one would produce a tracked file claiming to be the whole suite when it is not, and every later comparison
# would be made against it.
RECORDING_RULES = (
    ('R01', 'no ONLY, SCENARIO or other partial selector is present'),
    ('R02', 'the suite registry validates'),
    ('R03', 'the working tree and index were clean before the run'),
    ('R04', 'the subject is one exact committed ref'),
    ('R05', 'every canonical command and scenario completed'),
    ('R06', 'every expected-success command succeeded'),
    ('R07', 'every expected-failure fixture failed for its expected reason'),
    ('R08', 'every cache state and prime relation validates'),
    ('R09', 'every incremental edit was restored byte-exactly'),
    ('R10', 'the observation validates against its schema and suite digest'),
    ('R11', 'the environment is recorded completely'),
    ('R12', 'the result was written first as a local run bundle'),
    ('R13', 'recording changes only the canonical observation'),
    ('R14', 'the tool neither commits nor stages the file'),
)


def identity_problems(obs: dict) -> list[str]:
    """Every defect in this observation's run, sample, parent and prime relations, from retained data alone.

    ONE implementation, because there were two consumers with two answers: recording checked these relations
    and comparison did not. Returning problems rather than raising lets the recording path report all of
    them and the validator refuse on the first.
    """
    problems: list[str] = []
    # Keyed by the exact SAMPLE identity, not the metric class: a class matches any of three repetitions,
    # so `prime not in retained` could only ever prove that SOME sample of that class existed.
    retained = {s['sample_id']: s for s in obs['measurements'] if s.get('sample_id')}
    order = {s.get('sample_id'): i for i, s in enumerate(obs['measurements'])}

    for s in obs['measurements']:
        authorities = (s.get('cache_before') or {}).get('authorities', {})
        if not any(authorities.get(a) == 'reused' for a in PROJECT_CACHES):
            continue
        prime = (s.get('cache_before') or {}).get('prime_sample_id')
        where = f'{s["command_id"]} [{s["scenario_id"]}]'
        if not prime:
            problems.append(f'{where} reuses a project cache and names no prime sample, so its number is a '
                            f'comparison against an unknown baseline')
        elif prime not in retained:
            problems.append(f'{where} names prime {prime!r}, which this observation does not retain')
        elif not retained[prime]['scenario_id'].startswith('project.cold.'):
            problems.append(f'{where} names a prime that is not a cold sample: '
                            f'{retained[prime]["scenario_id"]}')
        elif retained[prime]['status'] != 'ok':
            problems.append(f'{where} names a prime whose own status is {retained[prime]["status"]!r}')
        elif retained[prime].get('derived_parent_id'):
            # Asked BEFORE "does it belong to this command": whether the named sample ran at all is the more
            # basic question, and every derived child carries a different command id, so the command check
            # would otherwise answer first and this rule could never be reached.
            problems.append(f'{where} names a DERIVED sample as its prime; only a sample that actually ran '
                            f'can have populated a cache')
        elif retained[prime]['command_id'] != s['command_id']:
            problems.append(f'{where} names a prime belonging to {retained[prime]["command_id"]}; another '
                            f"command's cold run did not populate this chain")
        elif (retained[prime].get('cache_before') or {}).get('cache_chain_id') != \
                (s.get('cache_before') or {}).get('cache_chain_id'):
            problems.append(f'{where} names a prime from another cache chain')
        elif order.get(prime, -1) >= order.get(s.get('sample_id'), -1):
            problems.append(f'{where} names a prime that does not precede it; a cache cannot have been '
                            f'populated by a run that had not happened yet')

    # Identity itself: one run, and one id per retained sample. A duplicate would let two measurements be
    # cited as one, and every relation above is keyed on it.
    if not obs.get('run_id'):
        problems.append('the observation retains no run identity, so no sample in it can be named exactly')
    ids = [s.get('sample_id') for s in obs['measurements']]
    if any(not i for i in ids):
        problems.append('a retained sample carries no sample identity')
    elif len(set(ids)) != len(ids):
        dup = sorted({i for i in ids if ids.count(i) > 1})
        problems.append(f'duplicate sample identit(ies) {dup[:3]}; two measurements sharing one id can be '
                        f'cited as each other')

    for s in obs['measurements']:
        parent = s.get('parent_sample_id')
        if not s.get('derived_parent_id'):
            if parent:
                problems.append(f'{s["command_id"]} is a direct sample yet names a parent sample')
            continue
        if not parent:
            problems.append(f'{s["command_id"]} is derived and names no exact parent sample')
        elif parent not in retained:
            problems.append(f'{s["command_id"]} names parent sample {parent!r}, which this observation does '
                            f'not retain')
        elif retained[parent]['command_id'] != s['derived_parent_id']:
            problems.append(f'{s["command_id"]} names a parent sample belonging to '
                            f'{retained[parent]["command_id"]}, not its declared parent '
                            f'{s["derived_parent_id"]}')
        elif retained[parent]['scenario_id'] != s['scenario_id']:
            problems.append(f'{s["command_id"]} was observed under a parent running a different scenario')
        elif order.get(parent, 1 << 30) >= order.get(s.get('sample_id'), -1):
            problems.append(f'{s["command_id"]} was observed inside a parent run that had not started yet')
    return problems


def validate_observation(obs: dict, suite_digest: str) -> str:
    """Shape, digest and — the part that matters — every summary recomputed from its own samples.

    A stored median is a claim about data that is right there. Trusting it would let a tampered or stale
    summary survive every other check in this file, so it is recomputed rather than read."""
    missing = [m for m in OBSERVATION_MEMBERS if m not in obs]
    if missing:
        raise ObservatoryError(f'the observation is missing member(s) {missing}')
    if obs['schema'] != SCHEMA:
        raise ObservatoryError(f'the observation schema is {obs["schema"]!r}, expected {SCHEMA!r}')
    if obs['suite_digest'] != suite_digest:
        raise ObservatoryError(
            f'the observation was taken against suite digest {obs["suite_digest"][:12]}… but the registry '
            f'now digests to {suite_digest[:12]}…; the two describe different suites')

    samples = obs['measurements']
    if not samples:
        raise ObservatoryError('the observation retains no samples, so nothing in it can be rechecked')
    for i, s in enumerate(samples):
        absent = [f for f in SAMPLE_FIELDS if f not in s]
        if absent:
            raise ObservatoryError(f'sample {i} ({s.get("command_id")}) is missing field(s) {absent}')
        # A derived BuildKit child has aggregate step work rather than elapsed wall time, so `wall_ns` is
        # absent by design. What is forbidden is a NEGATIVE duration, which a monotonic clock cannot produce.
        for field in ('wall_ns', 'aggregate_step_ns'):
            if s.get(field) is not None and s[field] < 0:
                raise ObservatoryError(f'sample {i} ({s["command_id"]}) has a negative {field}')
        kind = s.get('measurement_kind') or KIND_WALL
        if kind not in MEASUREMENT_KINDS:
            raise ObservatoryError(f'sample {i}: measurement_kind {kind!r} is not a known kind')
        if kind == KIND_INTERVAL and (s.get('lower_ns') is None or s.get('upper_ns') is None
                                      or s['lower_ns'] > s['upper_ns']):
            raise ObservatoryError(
                f'sample {i} ({s["command_id"]}) is a below-resolution interval without a usable bound')
        if (s.get('wall_ns') is None and s.get('aggregate_step_ns') is None
                and kind not in (KIND_UNTIMED, KIND_INTERVAL)):
            raise ObservatoryError(
                f'sample {i} ({s["command_id"]}) records neither an elapsed duration nor aggregate step '
                f'work, so it measures nothing')
        # An untimed artifact must SAY it is one and carry no duration. Zero was the old representation and
        # it is a measured claim: it asserts the work took no time, which was never true.
        if kind == KIND_UNTIMED and (s.get('wall_ns') is not None or s.get('aggregate_step_ns') is not None):
            raise ObservatoryError(
                f'sample {i} ({s["command_id"]}) is declared an untimed artifact yet carries a duration')
        if kind != KIND_UNTIMED and s.get('wall_ns') == 0 and s.get('aggregate_step_ns') is None:
            raise ObservatoryError(
                f'sample {i} ({s["command_id"]}) records an elapsed duration of exactly zero; work that '
                f'happened takes time, so this is either an untimed artifact or a below-resolution interval')
        # The authority map must be DERIVABLE from the stage evidence beside it. Two records of one fact
        # that are merely stored next to each other will disagree eventually, and the one that disagreed
        # here was the one a reader would have trusted.
        if s.get('cache_before') and s.get('cache_after') and not s.get('derived_parent_id'):
            want = observe_cache_after(s['cache_before'],
                                       (s.get('cache_observation') or {}).get('stages', {}))
            if s['cache_after'].get('authorities') != want.get('authorities'):
                raise ObservatoryError(
                    f'sample {i} ({s["command_id"]}): the recorded cache authorities '
                    f'{s["cache_after"].get("authorities")} are not what the retained stage evidence '
                    f'derives ({want.get("authorities")})')
        if s['resource_scope'] not in (SCOPE_HOST, SCOPE_BUILDKIT, SCOPE_UNAVAILABLE):
            raise ObservatoryError(f'sample {i}: resource_scope {s["resource_scope"]!r} is not a known scope')

    # A median is only meaningful over samples of the SAME program. Metric identity deliberately excludes the
    # source digest — an incremental scenario changes bytes on purpose — so the rule is stated in both
    # directions: without an edit the digests must agree, with an edit they must all differ.
    by_identity: dict[str, list[dict]] = {}
    for s in samples:
        if s.get('source_digest'):
            by_identity.setdefault(metric_identity(s), []).append(s)
    for key, group in sorted(by_identity.items()):
        digests = [g['source_digest'] for g in group]
        if group[0].get('edit_id') is None:
            if len(set(digests)) != 1:
                raise ObservatoryError(
                    f'{key}: {len(set(digests))} different source digests are pooled into one summary, but '
                    f'this scenario applies no edit; the tree moved during the run and the samples measure '
                    f'different programs')
        elif len(set(digests)) != len(digests):
            raise ObservatoryError(
                f'{key}: {len(digests) - len(set(digests))} sample(s) repeat an earlier sample\'s exact '
                f'source, so a cached no-op is recorded under an incremental label')

    # A command named as selected and measured in nothing must say which it was. Otherwise the reader sees
    # it listed beside the results and reads its absence as a measurement that went missing.
    sel_block = obs.get('selection') or {}
    measured = {s['command_id'] for s in samples}
    accounted = set(sel_block.get('commands_with_no_scenario_here') or [])
    # A catalog-only command is never measured BY DEFINITION and the registry already carries the reason,
    # so it is accounted for by its classification rather than by a per-run note. My rule flagged all three
    # of them, which would have made every complete observation unrecordable.
    # Self-contained on purpose: a baseline from another ref may have been built against a different
    # registry, so the observation carries this itself rather than being judged against today's suite.
    catalog = set(sel_block.get('commands_never_measured') or [])
    orphans = sorted(set(sel_block.get('commands_selected') or []) - measured - accounted - catalog)
    if orphans:
        raise ObservatoryError(
            f'{orphans} are recorded as selected but produced no sample and are not listed among the '
            f'commands this selection could not measure')

    # The same rule ACROSS commands. Distinct bytes per sample stopped a command being its own cache hit;
    # four commands whose sample 0 wrote identical bytes to Float.v still produced one tree, so whichever
    # ran first paid the rebuild and the rest recorded ~1.7s under an incremental label — against 117.5s
    # for the same scenario measured on its own.
    owners: dict[str, set] = {}
    for s in samples:
        if s.get('edit_id') and s.get('source_digest') and not s.get('derived_parent_id'):
            owners.setdefault(s['source_digest'], set()).add(s['command_id'])
    shared = {d: sorted(c) for d, c in owners.items() if len(c) > 1}
    if shared:
        first = next(iter(shared.items()))
        raise ObservatoryError(
            f'{len(shared)} incremental source(s) are shared between commands, so one command\'s rebuild '
            f'satisfies another\'s incremental sample; {first[0][:12]} is used by {first[1]}')

    recomputed = summarise(samples)
    stored = obs['derived'].get('summaries', {})
    if stored != recomputed:
        differing = sorted(set(stored) ^ set(recomputed)) or \
            [k for k in recomputed if stored.get(k) != recomputed[k]]
        raise ObservatoryError(
            f'{len(differing)} stored summar(ies) do not equal recomputation from the retained samples, '
            f'first {differing[:3]}')
    # The identity relations are part of VALIDITY, not only of recording eligibility. Leaving them out of
    # here is what let comparison conclude from an observation recording would have refused.
    problems = identity_problems(obs)
    if problems:
        raise ObservatoryError(f'{len(problems)} identity defect(s), first: {problems[0]}')
    return (f'{len(samples)} retained sample(s) over {len(recomputed)} command-scenario pair(s); every '
            f'summary equals recomputation; run, sample, parent and prime identities resolve; suite digest '
            f'matches')


def expected_relation(suite: dict, canonical_only: bool = True, graph: dict | None = None) -> dict:
    """The exact set of metrics a complete run must produce, derived from the validated registry.

    R05 used to check that each classified command appeared at least ONCE. A command measured in one scenario
    could therefore stand in for every scenario it never ran, which is how seven canonical pairs went missing
    while coverage read green. This states the relation the observation must equal — in both directions.

    Both sides of that equality are keyed by `metric_identity` and nothing else. Building the required key
    here by hand would be a second key authority, and the two would drift the moment either changed — which
    is exactly how a wildcard crept into one side and stayed invisible."""
    scenarios = {s['id']: s for s in suite['scenarios']}
    commands = {c['id']: c for c in suite['commands']}

    def scope_and_kind(c: dict) -> tuple[str, str]:
        """What a command MUST report, derived from how it is executed rather than read back from a sample.

        Deriving it is the point: read back from the sample it would agree with itself no matter what the
        sample said, which is how a direct command could have claimed BuildKit stage scope unchallenged.
        """
        if c['measurement'] == 'derived':
            if c['execution'][1] == 'buildkit-progress':
                return SCOPE_BUILDKIT, KIND_AGGREGATE
            if c['execution'][0] == 'observatory':
                return SCOPE_UNAVAILABLE, KIND_UNTIMED
            return SCOPE_UNAVAILABLE, KIND_WALL
        if c['kind'] in ANALYSIS_KINDS:
            return SCOPE_UNAVAILABLE, KIND_WALL
        return SCOPE_HOST, KIND_WALL

    # A Docker stage is observed under EVERY command whose build reaches it, so its parents are derived from
    # the stage graph and each command's declared build targets — not declared one-per-stage. `dependencies`
    # keeps its own job: the single parent to RUN when this child is selected.
    stage_parents: dict[str, set] = {}
    if graph:
        for c in suite['commands']:
            if c['measurement'] != 'direct' or not c.get('build_targets'):
                continue
            for st in stages_built_by(graph, c['build_targets']):
                stage_parents.setdefault(f'docker.{st}', set()).add(c['id'])

    derived_parents: dict[str, list[str]] = {}
    for c in suite['commands']:
        if c['measurement'] == 'derived':
            derived_parents[c['id']] = sorted(stage_parents.get(c['id'], set())) or list(c['dependencies'])

    expected: dict[str, dict] = {}
    for c in suite['commands']:
        if c['measurement'] == 'catalog-only':
            continue
        if c['measurement'] == 'derived':
            # A derived child is observed once per PARENT SAMPLE, in whatever scenario the parent ran. Its
            # scenarios and counts are therefore its parents', and a child that declared its own list stated
            # the same fact twice: `docker.emit` named only `project.cold.emit` while being observed, as a
            # hit, in every cold scenario any of its six producers runs in.
            for parent in derived_parents[c['id']]:
                for sid, count in commands[parent]['samples'].items():
                    if canonical_only and not scenarios[sid].get('canonical'):
                        continue
                    edit = scenarios[sid].get('edit')
                    scope, kind = scope_and_kind(c)
                    spec = {'command_id': c['id'], 'scenario_id': sid, 'edit_id': edit,
                            'derived_parent_id': parent, 'selected_or_support': 'selected',
                            'resource_scope': scope, 'measurement_kind': kind, 'samples': count}
                    expected[metric_identity(spec)] = spec
            continue
        for sid in c['scenarios']:
            if canonical_only and not scenarios[sid].get('canonical'):
                continue
            edit = scenarios[sid].get('edit')
            scope, kind = scope_and_kind(c)
            spec = {'command_id': c['id'], 'scenario_id': sid, 'edit_id': edit,
                    'derived_parent_id': None, 'selected_or_support': 'selected',
                    'resource_scope': scope, 'measurement_kind': kind,
                    'samples': c['samples'][sid]}
            expected[metric_identity(spec)] = spec
    return expected


def observed_relation(samples: list[dict]) -> dict:
    """The same shape, taken from what actually ran, under the SAME identity the summaries use.

    This used to wildcard resource scope "so the two can meet", which is the wrong way round: the relation
    was made to close by discarding the fields that distinguish one measurement from another. A selected
    child mislabelled `support`, a direct command claiming BuildKit stage scope, or aggregate step work
    standing in for elapsed wall time all closed the relation while describing a different measurement than
    the registry asked for. The two sides meet on the full key or they do not meet."""
    out: dict[str, int] = {}
    for s in samples:
        key = metric_identity(s)
        out[key] = out.get(key, 0) + 1
    return out


def check_relation_closed(suite: dict, samples: list[dict], canonical_only: bool = True,
                          graph: dict | None = None) -> str:
    """Exact equality in both directions: nothing missing, nothing extra, every count right."""
    expected = expected_relation(suite, canonical_only, graph)
    observed = observed_relation(samples)
    missing = sorted(set(expected) - set(observed))
    extra = sorted(set(observed) - set(expected))
    wrong = sorted(k for k in set(expected) & set(observed)
                   if observed[k] != expected[k]['samples'])
    problems = []
    if missing:
        problems.append(f'{len(missing)} declared metric(s) produced no sample: {missing[:4]}')
    if extra:
        problems.append(f'{len(extra)} metric(s) the registry never declared: {extra[:4]}')
    if wrong:
        problems.append(f'{len(wrong)} metric(s) have the wrong sample count, e.g. '
                        f'{wrong[0]} got {observed[wrong[0]]} of {expected[wrong[0]]["samples"]}')
    if problems:
        raise ObservatoryError('; '.join(problems))
    return f'{len(expected)} declared metric(s), each with exactly its required sample count'


def check_record_eligible(root: Path, sel: Selection, suite: dict, suite_digest: str, obs: dict,
                          bundle: Path, clean_before: bool, edits_restored: bool,
                          incomplete: list[str]) -> list[str]:
    """The fourteen rules, in order, each named in its own failure. A failed command is a failed observation."""
    satisfied = []
    graph = docker_stage_graph(root)

    def ok(rule: str):
        satisfied.append(rule)

    def bad(rule: str, why: str):
        text = dict(RECORDING_RULES)[rule]
        raise ObservatoryError(f'recording rule {rule} ({text}) is not met: {why}')

    if sel.partial:
        bad('R01', 'the run was selective, and a partial run cannot claim to be the whole suite')
    ok('R01')

    if suite_digest_of(suite) != suite_digest:
        bad('R02', 'the registry changed between validation and recording, so the run and the file the '
                   'observation names describe different suites')
    ok('R02')

    if not clean_before:
        bad('R03', 'the working tree or index was dirty before the run')
    ok('R03')

    if obs['subject']['dirty'] or obs['subject']['source_view'] != 'committed-tree':
        bad('R04', 'the subject is not one exact committed ref')
    ok('R04')

    if incomplete:
        bad('R05', f'{len(incomplete)} command-scenario pair(s) did not complete: {incomplete[:4]}')
    try:
        check_relation_closed(suite, obs['measurements'], graph=graph)
    except ObservatoryError as exc:
        bad('R05', f'{exc}; a registry that declares more than the observation measures is coverage on paper')
    ok('R05')

    wrong = [f'{s["command_id"]}/{s["scenario_id"]}' for s in obs['measurements'] if s['status'] != 'ok']
    if wrong:
        bad('R06', f'{len(wrong)} sample(s) did not meet their expected exit: {wrong[:4]}')
    ok('R06')

    # R06 compares exit CODES. R07 is about the REASON, which is a different claim: a fixture that fails for
    # the wrong reason still exits nonzero. An earlier draft marked this satisfied because R06 had run, which
    # was prose outrunning proof inside the rule that exists to stop exactly that.
    fixtures = [c for c in suite['commands'] if c['expected_exit'] != 0]
    wrong_reason = [f'{s["command_id"]}/{s["scenario_id"]}' for s in obs['measurements']
                    if s['status'] == 'wrong-failure-reason']
    if wrong_reason:
        bad('R07', f'{len(wrong_reason)} expected-failure sample(s) failed for the wrong reason: '
                   f'{wrong_reason[:4]}')
    if not fixtures:
        satisfied.append('R07(vacuous: no command declares a nonzero expected exit)')
    else:
        ok('R07')

    # A sample that reuses a PROJECT result must name the exact prime that produced it, and that prime must
    # be a cold, successful sample retained in THIS observation. The old rule asked a stringified dict
    # whether it contained the word `reused`, which is true of the stable caches in every cold sample, and
    # then looked for `primed_by_run` — a key live samples have never carried.
    # ONE implementation of these relations, shared with `validate_observation`. Recording checked them and
    # comparison did not, so an observation that comparison happily produced verdicts from was one recording
    # would have refused. Reporting every problem rather than the first is why this returns a list.
    for problem in identity_problems(obs):
        bad('R08', problem)
    ok('R08')

    if not edits_restored:
        bad('R09', 'at least one incremental edit did not restore byte-exactly')
    ok('R09')

    validate_observation(obs, suite_digest)
    ok('R10')

    check_environment_complete(obs['environment'])
    ok('R11')

    if not (bundle / 'observation.json').is_file():
        bad('R12', f'no local run bundle was written first at {bundle}')
    try:
        verify_raw_logs(root, bundle, obs)
    except ObservatoryError as exc:
        bad('R12', str(exc))
    ok('R12')

    dirty = [l[3:] for l in _git(root, 'status', '--porcelain').split('\n') if l.strip()]
    unexpected = [p for p in dirty if p != OBSERVATION_REL]
    if unexpected:
        bad('R13', f'recording would leave {len(unexpected)} other path(s) changed: {unexpected[:4]}')
    ok('R13')

    if _git(root, 'diff', '--cached', '--name-only').strip():
        bad('R14', 'the index is not empty; this tool never stages or commits')
    ok('R14')
    return satisfied


# ─────────────────────────────────────────────────────────────── module graph
def parse_module_graph(depend_mk: str, wall_ns: dict[str, int]) -> dict:
    """The adjacency the TOOLCHAIN emitted, plus what it implies about rebuild cost.

    `rocq dep` prints Makefile rules — targets before the colon, dependencies after. Only `.vo` dependencies
    are edges between certified modules; `.v` sources and glob files are the rule's own inputs, not module
    edges. Reading the toolchain's output rather than scanning `Require Import` lines is the whole point: an
    import scan is a second authority that can disagree with the build, and would disagree silently."""
    edges: dict[str, set[str]] = {m: set() for m in wall_ns}
    for raw in depend_mk.replace('\\\n', ' ').split('\n'):
        line = raw.strip()
        if not line or ':' not in line:
            continue
        targets, _, deps = line.partition(':')
        owners = {Path(t).stem for t in targets.split() if t.endswith('.vo')}
        needed = {Path(d).stem for d in deps.split() if d.endswith('.vo')}
        for owner in owners & set(edges):
            edges[owner] |= (needed & set(edges)) - {owner}
    if not any(edges.values()):
        raise ObservatoryError(
            'the dependency output contains no module-to-module edges; the graph would be a list of isolated '
            'modules, which no rebuild set can be derived from')

    def transitive_downstream(module: str) -> set[str]:
        out, frontier = set(), [module]
        while frontier:
            current = frontier.pop()
            for other, deps in edges.items():
                if current in deps and other not in out:
                    out.add(other)
                    frontier.append(other)
        return out

    downstream = {m: sorted(transitive_downstream(m)) for m in edges}
    downstream_cost = {m: wall_ns[m] + sum(wall_ns.get(d, 0) for d in ds) for m, ds in downstream.items()}

    # Longest path by summed compile cost. The graph is acyclic by construction — Rocq forbids cyclic
    # requires — so one memoised walk suffices, and a cycle would be a toolchain defect, not a slow build.
    best: dict[str, tuple[int, list[str]]] = {}

    def longest(module: str, seen: frozenset) -> tuple[int, list[str]]:
        if module in best:
            return best[module]
        if module in seen:
            raise ObservatoryError(f'the dependency graph has a cycle through {module!r}')
        cost, path = wall_ns[module], [module]
        for dep in sorted(edges[module]):
            sub_cost, sub_path = longest(dep, seen | {module})
            if sub_cost > cost - wall_ns[module]:
                cost, path = wall_ns[module] + sub_cost, sub_path + [module]
        best[module] = (cost, path)
        return best[module]

    critical = max((longest(m, frozenset()) for m in edges), key=lambda cp: cp[0])
    return {
        'source': 'rocq dep',
        'modules': sorted(edges),
        'adjacency': {m: sorted(d) for m, d in sorted(edges.items())},
        'self_ns': dict(sorted(wall_ns.items())),
        'downstream': downstream,
        'downstream_cost_ns': dict(sorted(downstream_cost.items())),
        'critical_path': {'modules': critical[1], 'total_ns': critical[0]},
    }


def rebuild_impact(graph: dict) -> list[dict]:
    """Every module ranked by what an edit to it costs downstream. No threshold, and that is deliberate.

    An earlier draft reported only modules above a 0.5 share. That constant would have decided, on a number
    nobody reviewed, which dependencies count as "too broad" — and a foundation with half the theory below it
    is not automatically wrong. Ranking everything reports the cost and leaves the judgement to M3, which is
    the only part of this M2 is allowed to do."""
    total = len(graph['modules'])
    out = [{'module': m, 'downstream_modules': len(graph['downstream'][m]),
            'share_of_theory': round(len(graph['downstream'][m]) / total, 3) if total else 0,
            'downstream_rebuild_ns': graph['downstream_cost_ns'][m],
            'self_ns': graph['self_ns'][m]}
           for m in graph['modules']]
    return sorted(out, key=lambda r: (-r['downstream_rebuild_ns'], r['module']))


# ───────────────────────────────────────────────────────────── history analysis
# The exact accepted range this analysis is defined over, named by the contract.
HISTORY_START = '39ea7e3b012ec798c6a756c971c10bb363557ef8'
HISTORY_END = '6524b437bd7a7d6b2616563b8789e28a00c7af13'

# A commit belongs to the M1 source-diet campaign by its SUBJECT, not by its position in the range. M1 was a
# one-time sweep across nearly every file in the repository; letting it define "normal" edit frequency would
# make every module look equally hot and the weighting worthless.
CAMPAIGN_PREFIXES = ('diet(', 'repair(m1)', 'freeze(m1)', 'accept(m1)')

HISTORY_VIEWS = ('all', 'implementation', 'excluding_campaign')

CHANGE_CLASSES = ('rocq-source', 'tool-and-build', 'current-documentation', 'generated-artifact',
                  'review-only', 'life-md')


def classify_path(rel: str) -> str:
    if rel.endswith('.v'):
        return 'rocq-source'
    if rel == 'life.md':
        return 'life-md'
    if rel == 'go.mod' or rel.endswith('.go'):
        return 'generated-artifact'
    if (rel.startswith('tools/') or rel.startswith('.githooks/') or rel.startswith('plugin/')
            or rel.startswith('e2e/') or rel in ('Makefile', 'Dockerfile', 'dune', 'dune-project',
                                                 '.dockerignore', '.editorconfig', '.gitignore')):
        return 'tool-and-build'
    if rel.startswith('.review/'):
        return 'review-only'
    return 'current-documentation'


def history_analysis(root: Path, start: str = HISTORY_START, end: str = HISTORY_END) -> dict:
    """Edit frequency, co-change and edit shapes over one exact range, reported three ways.

    Three views, because one would lie. `all` is what happened. `implementation` drops review-only and
    life-only commits, which move no build input. `excluding_campaign` additionally drops M1's one-time sweep
    — a campaign that touched almost every file at once, and which would otherwise flatten every module's
    apparent edit frequency into the same number."""
    if not _git(root, 'cat-file', '-t', start, check=False).strip():
        raise ObservatoryError(f'history range start {start[:12]} is not an object in this repository')
    if not _git(root, 'cat-file', '-t', end, check=False).strip():
        raise ObservatoryError(f'history range end {end[:12]} is not an object in this repository')

    raw = _git(root, 'log', '--no-merges', '--format=%x01%H%x02%s', '--name-only', f'{start}..{end}')
    commits = []
    for chunk in raw.split('\x01'):
        if not chunk.strip():
            continue
        head, _, body = chunk.partition('\n')
        sha, _, subject = head.partition('\x02')
        paths = sorted(p for p in body.split('\n') if p.strip())
        classes = sorted({classify_path(p) for p in paths})
        commits.append({'commit': sha, 'subject': subject, 'paths': paths, 'classes': classes,
                        'campaign': subject.startswith(CAMPAIGN_PREFIXES),
                        'implementation_bearing': bool(
                            {'rocq-source', 'tool-and-build', 'generated-artifact'} & set(classes))})
    if not commits:
        raise ObservatoryError(f'the range {start[:7]}..{end[:7]} contains no commits to analyse')

    def view(selected: list[dict]) -> dict:
        edits: dict[str, int] = {}
        pairs: dict[str, int] = {}
        shapes: dict[str, int] = {}
        for c in selected:
            for p in c['paths']:
                edits[p] = edits.get(p, 0) + 1
            for i, a in enumerate(c['paths']):
                for b in c['paths'][i + 1:]:
                    pairs[f'{a}\x00{b}'] = pairs.get(f'{a}\x00{b}', 0) + 1
            shape = '+'.join(c['classes']) or '(empty)'
            shapes[shape] = shapes.get(shape, 0) + 1
        return {
            'commits': len(selected),
            'edit_count_by_file': dict(sorted(edits.items(), key=lambda kv: (-kv[1], kv[0]))),
            'co_change_by_pair': {k.replace('\x00', ' + '): v for k, v in
                                  sorted(pairs.items(), key=lambda kv: (-kv[1], kv[0]))},
            'common_edit_shapes': dict(sorted(shapes.items(), key=lambda kv: (-kv[1], kv[0]))),
            'change_class_totals': {cl: sum(1 for c in selected if cl in c['classes'])
                                    for cl in CHANGE_CLASSES},
        }

    implementation = [c for c in commits if c['implementation_bearing']]
    return {
        'range': {'start': start, 'end': end},
        'views': dict(zip(HISTORY_VIEWS, (
            view(commits),
            view(implementation),
            view([c for c in implementation if not c['campaign']]),
        ))),
        'campaign_commits': sum(1 for c in commits if c['campaign']),
    }


def weighted_rebuild_cost(history: dict, module_graph: dict | None, view: str = 'excluding_campaign') -> dict:
    """Edit frequency x measured downstream rebuild cost, with BOTH inputs retained beside the product.

    Storing only the product would leave a number nobody can argue with: a file could rank high because it
    changes constantly or because rebuilding it is ruinous, and those call for opposite responses."""
    if not module_graph:
        return {'view': view, 'basis': 'unavailable', 'rows': [],
                'reason': 'no module graph was measured in this observation'}
    downstream = module_graph.get('downstream_cost_ns', {})
    edits = history['views'][view]['edit_count_by_file']
    rows = []
    for module, cost_ns in sorted(downstream.items()):
        frequency = edits.get(f'{module}.v', 0)
        rows.append({'module': module, 'edit_frequency': frequency,
                     'downstream_rebuild_ns': cost_ns, 'weighted_ns': frequency * cost_ns})
    rows.sort(key=lambda r: (-r['weighted_ns'], r['module']))
    return {'view': view, 'basis': 'edit_frequency x downstream_rebuild_ns', 'rows': rows}


# ────────────────────────────────────────────────────────────────── comparison
CLASSIFICATIONS = ('improved', 'regressed', 'overlapping-range', 'unchanged', 'added', 'removed',
                   'incomparable')


def command_fingerprints(suite: dict) -> dict:
    """A digest per command definition, retained in every observation.

    The suite digest alone can only say two runs used different suites. Keeping a fingerprint per command
    lets a comparison say WHICH definitions were added, removed or changed — so a registry edit narrows an
    old observation rather than voiding it."""
    return {c['id']: _sha256(canonical_bytes(c)) for c in suite['commands']}


def load_observation(root: Path, where: str) -> tuple[dict, str]:
    """An observation from a local path or a Git ref. Unreadable input is an error, never an empty result."""
    p = Path(where)
    if p.is_file():
        try:
            return json.loads(p.read_text(encoding='utf-8')), str(p)
        except json.JSONDecodeError as exc:
            raise ObservatoryError(f'{where}: not a valid observation ({exc})')
    if p.is_dir():
        return load_observation(root, str(p / 'observation.json'))
    raw = _git(root, 'show', f'{where}:{OBSERVATION_REL}', check=False)
    if not raw.strip():
        raise ObservatoryError(
            f'{where}: no readable observation — not a file, not a run bundle, and no {OBSERVATION_REL} at '
            f'that Git ref')
    try:
        return json.loads(raw), f'{where}:{OBSERVATION_REL}'
    except json.JSONDecodeError as exc:
        raise ObservatoryError(f'{where}:{OBSERVATION_REL}: not a valid observation ({exc})')


def _comparable(obs: dict, side: str) -> None:
    """An observation that never measured anything is not a baseline; say so rather than fail on its nulls."""
    if obs.get('state') == 'pending':
        raise ObservatoryError(
            f'the {side} observation is still pending — it records no measurement, so there is nothing to '
            f'compare against')
    # Ask about incompleteness BEFORE reaching for members an unfinished run has not written yet. A partial
    # bundle blamed for a missing 'environment' sends the reader looking for a corrupt file instead of a run
    # that is still going.
    if (obs.get('derived') or {}).get('status') == 'incomplete':
        raise ObservatoryError(
            f'the {side} observation is an incomplete run — it was checkpointed mid-suite and its samples do '
            f'not cover what it claims to; finish or discard the run before comparing')
    for member in ('environment', 'derived', 'measurements'):
        if not isinstance(obs.get(member), (dict, list)):
            raise ObservatoryError(f'the {side} observation has no usable {member!r} member')


def compare(base: dict, cand: dict, only: str | None = None, suite: dict | None = None) -> dict:
    """Two observations, metric by metric, with the reason for every verdict it declines to give.

    There is no fixed percentage threshold anywhere in here. A hidden one would decide, on a constant nobody
    reviewed, which measured differences are allowed to count — so when two sample ranges overlap this says
    they overlap, and when one side has a single sample it reports the delta and refuses the noise call."""
    _comparable(base, 'baseline')
    _comparable(cand, 'candidate')
    # §13 — the COMPLETE validator, on both sides, before any verdict. Comparison used to check basic
    # members and recompute summaries only, so an observation with a member removed still produced metric
    # verdicts: the system had more than one definition of a valid observation, and comparison held the
    # weaker one. A selector may be applied after this, never instead of it.
    for side, obs in (('baseline', base), ('candidate', cand)):
        try:
            validate_observation(obs, obs.get('suite_digest', ''))
        except ObservatoryError as exc:
            raise ObservatoryError(f'the {side} observation does not validate, so no verdict can rest on '
                                   f'it: {exc}') from None
    # §7.2 — a stored summary is a CLAIM about samples that are right there, and trusting it would let a
    # tampered median produce a verdict about data that never changed. It is recomputed inside the complete
    # validator above, for both sides, so there is no second copy of that rule here to drift away from it.
    # §7.5 asks for one exact scope per metric. That is now STRUCTURAL rather than checked: resource scope
    # is part of the metric identity, so two scopes are two metrics and cannot meet in one row. A check
    # here would be unreachable, and an unreachable guard reads as protection it does not give.
    same_host = (base['environment'].get('host_class_fingerprint')
                 == cand['environment'].get('host_class_fingerprint'))
    b_sum, c_sum = base['derived'].get('summaries', {}), cand['derived'].get('summaries', {})
    b_cmds = base.get('commands', {}) or {}
    c_cmds = cand.get('commands', {}) or {}
    if isinstance(b_cmds, list):
        b_cmds = {cid: None for cid in b_cmds}
    if isinstance(c_cmds, list):
        c_cmds = {cid: None for cid in c_cmds}

    definitions = {
        'added': sorted(set(c_cmds) - set(b_cmds)),
        'removed': sorted(set(b_cmds) - set(c_cmds)),
        'changed': sorted(k for k in set(b_cmds) & set(c_cmds)
                          if b_cmds[k] is not None and c_cmds[k] is not None and b_cmds[k] != c_cmds[k]),
    }
    # §7.3 — a metric is a question. If the scenario, the edit or the boundary changed, the two sides asked
    # different questions and their difference is not an improvement or a regression.
    b_def, c_def = base.get('definitions') or {}, cand.get('definitions') or {}
    changed_scenarios = {k for k in set(b_def.get('scenarios', {})) & set(c_def.get('scenarios', {}))
                         if b_def['scenarios'][k] != c_def['scenarios'][k]}
    changed_edits = {k for k in set(b_def.get('edits', {})) & set(c_def.get('edits', {}))
                     if b_def['edits'][k] != c_def['edits'][k]}
    boundary_moved = (b_def.get('stable_through') != c_def.get('stable_through')
                      and b_def.get('stable_through') is not None
                      and c_def.get('stable_through') is not None)
    b_conc = (base['environment'].get('concurrency') or {}).get('make_jobs')
    c_conc = (cand['environment'].get('concurrency') or {}).get('make_jobs')
    concurrency_changed = b_conc != c_conc
    definitions['changed_scenarios'] = sorted(changed_scenarios)
    definitions['changed_edits'] = sorted(changed_edits)
    definitions['stable_boundary_moved'] = boundary_moved
    definitions['concurrency_changed'] = concurrency_changed

    # §7.4 — run mode expands groups and rejects unknown names; comparison used a bare string set, so
    # `ONLY=acceptance` silently produced no rows and an unknown name exited successfully.
    wanted = None
    if only:
        if suite is not None:
            commands = {c['id']: c for c in suite['commands']}
            groups = {g['id']: list(g['members']) for g in suite['groups']}
            wanted = _expand(only, commands, groups, 'ONLY name')
        else:
            wanted = {x.strip() for x in only.split(',') if x.strip()}

    metrics = []
    for key in sorted(set(b_sum) | set(c_sum)):
        command_id = key.split('|')[0]
        if wanted is not None and command_id not in wanted:
            continue
        b, c = b_sum.get(key), c_sum.get(key)
        row = {'key': key, 'command_id': command_id, 'scenario_id': key.split('|')[1],
               'baseline': b, 'candidate': c}
        if b is None:
            metrics.append({**row, 'classification': 'added', 'reason': 'absent from the baseline'})
            continue
        if c is None:
            metrics.append({**row, 'classification': 'removed', 'reason': 'absent from the candidate'})
            continue
        if not same_host:
            metrics.append({**row, 'classification': 'incomparable',
                            'reason': 'the two runs have different host-class fingerprints'})
            continue
        # No scope guard here, and deliberately none: resource scope is a FIELD OF THE KEY, so two sides of
        # one key cannot disagree about it. The guard that used to sit here compared a two-part
        # `command|scenario` string against the full five-part key and so could never match — an unreachable
        # check reading as evidence. A scope that really changes now changes the key, and surfaces as an
        # added/removed pair, which is what it is.
        scenario_id = key.split('|')[1]
        edit_id = key.split('|')[2]
        for changed, why in ((command_id in definitions['changed'], 'the command definition changed'),
                             (scenario_id in changed_scenarios, f'the meaning of {scenario_id} changed'),
                             (edit_id in changed_edits, f'the edit procedure {edit_id} changed'),
                             (boundary_moved, 'the stable cache boundary moved'),
                             (concurrency_changed,
                              f'effective concurrency changed ({b_conc} -> {c_conc})')):
            if changed:
                metrics.append({**row, 'classification': 'incomparable', 'reason': why})
                break
        else:
            pass
        if metrics and metrics[-1].get('key') == key and \
                metrics[-1]['classification'] == 'incomparable':
            continue

        # A below-resolution row carries a BOUND rather than a median. Asking it for one, or computing a
        # percentage against it, would manufacture an exact delta out of "we could not tell".
        if 'median_ns' not in b or 'median_ns' not in c:
            metrics.append({**row, 'classification': 'incomparable',
                            'reason': 'the stage is below the clock resolution on at least one side, so '
                                      'only a bound is known'})
            continue
        delta = c['median_ns'] - b['median_ns']
        pct = (delta / b['median_ns'] * 100) if b['median_ns'] else None
        single = b['samples'] < 2 or c['samples'] < 2
        overlap = max(b['min_ns'], c['min_ns']) <= min(b['max_ns'], c['max_ns'])
        if delta == 0:
            classification, reason = 'unchanged', 'the medians are equal'
        elif not single and overlap:
            classification, reason = 'overlapping-range', 'the two sample ranges overlap'
        elif delta < 0:
            classification, reason = 'improved', 'the candidate median is lower'
        else:
            classification, reason = 'regressed', 'the candidate median is higher'
        metrics.append({**row, 'delta_ns': delta, 'delta_percent': pct,
                        'classification': classification, 'reason': reason,
                        'noise_basis': 'single-sample' if single else 'sample-ranges'})

    counts = {c: sum(1 for m in metrics if m['classification'] == c) for c in CLASSIFICATIONS}
    return {'schema': SCHEMA, 'same_host_class': same_host,
            'baseline_subject': base['subject'], 'candidate_subject': cand['subject'],
            'suite_definitions': definitions, 'metrics': metrics, 'counts': counts}


def render_comparison(cmp: dict) -> str:
    def ms(ns):
        return f'{ns / 1e6:,.1f}ms' if ns is not None else '—'

    lines = [f'baseline  {cmp["baseline_subject"]["commit"][:12]}  '
             f'{"dirty" if cmp["baseline_subject"]["dirty"] else "clean"}',
             f'candidate {cmp["candidate_subject"]["commit"][:12]}  '
             f'{"dirty" if cmp["candidate_subject"]["dirty"] else "clean"}',
             f'host class {"same" if cmp["same_host_class"] else "DIFFERENT — every metric is incomparable"}',
             '']
    d = cmp['suite_definitions']
    if d['added'] or d['removed'] or d['changed']:
        lines += [f'suite definitions: {len(d["added"])} added, {len(d["removed"])} removed, '
                  f'{len(d["changed"])} changed', '']
    lines += [f'{"METRIC":<46} {"BASELINE":>12} {"CANDIDATE":>12} {"DELTA":>12} {"":>8}  CLASSIFICATION', '─' * 118]
    for m in cmp['metrics']:
        b, c = m['baseline'], m['candidate']
        pct = f'{m["delta_percent"]:+.1f}%' if m.get('delta_percent') is not None else ''
        lines.append(f'{m["key"]:<46} {ms(b["median_ns"]) if b else "—":>12} '
                     f'{ms(c["median_ns"]) if c else "—":>12} '
                     f'{ms(m.get("delta_ns")):>12} {pct:>8}  {m["classification"]}')
        if b and c:
            lines.append(f'{"":<46} [{ms(b["min_ns"])}–{ms(b["max_ns"])}] '
                         f'[{ms(c["min_ns"])}–{ms(c["max_ns"])}]  '
                         f'n={b["samples"]}/{c["samples"]}  {m["reason"]}')
        else:
            lines.append(f'{"":<46} {m["reason"]}')
    lines += ['', '  '.join(f'{k}={v}' for k, v in cmp['counts'].items() if v)]
    return '\n'.join(lines)


# ───────────────────────────────────────────────────────────────── the run
def materialise_execution(command: dict, scenario: dict | None = None,
                          builder: str = OBSERVATORY_BUILDER) -> list[str]:
    """The live invocation, with builder and cache cut supplied from OUTSIDE the registry.

    Which builder a command uses, and which stage a scenario invalidates, are properties of this run rather
    than of what the command IS. Storing either in the registry would make two observations from different
    machines look like different commands.

    A project-cold sample passes NOCACHE=<root>, which invalidates exactly that stage and everything
    downstream while its stable ancestors stay cache hits. That is what makes the sample cold WITHOUT
    emptying the machine — and it is also what makes it immune to an earlier measured command's cache,
    because the root is forced to rebuild whatever anyone else left behind."""
    argv = list(command['execution'])
    roots = (scenario or {}).get('cache_cut', {}).get('invalidated_roots') or []
    cold = bool(scenario) and scenario['id'].startswith('project.cold.')
    if command['kind'] == 'make-target':
        argv = argv + [f'BUILDER={builder}']
        if cold and roots:
            argv.append('NOCACHE=' + ' '.join(roots))
        return argv
    if command['kind'] == 'precommit-full':
        env = ['env', f'FIDO_BUILDER={builder}']
        if cold and roots:
            env.append('FIDO_NOCACHE=' + ' '.join(roots))
        return env + argv
    return argv


def ensure_observatory_builder() -> None:
    import subprocess
    _assert_observatory_builder(OBSERVATORY_BUILDER)
    probe = subprocess.run(['docker', 'buildx', 'inspect', OBSERVATORY_BUILDER],
                           capture_output=True, text=True)
    if probe.returncode != 0:
        created = subprocess.run(['docker', 'buildx', 'create', '--name', OBSERVATORY_BUILDER,
                                  '--driver', 'docker-container', '--bootstrap'],
                                 capture_output=True, text=True)
        if created.returncode != 0:
            raise ObservatoryError(f'could not create {OBSERVATORY_BUILDER}: {created.stderr.strip()}')


def instrumentation_env(command: dict, anchor_log: Path, scenario: dict | None = None) -> dict:
    """Switch the instrumentation on, by environment only.

    `FIDO_OBSERVE` makes the hook's anchors write instead of no-op; `BUILDKIT_PROGRESS=plain` makes buildx
    emit the structured step output the stage timings are read from. Neither changes a hook line or a Make
    recipe, so behaviour with the observatory absent is exactly what it always was."""
    env = {}
    if command['kind'] == 'precommit-full':
        env['FIDO_OBSERVE'] = str(anchor_log)
    if command['kind'] in ('make-target', 'precommit-full'):
        env['BUILDKIT_PROGRESS'] = 'plain'
    return env


def collect_events(command: dict, anchor_log: Path, raw_log: Path) -> list[dict]:
    """Every derived event this sample produced, from whichever instrumentation applies to it."""
    events = []
    if anchor_log.is_file():
        events.extend(parse_anchor_log(read_text(anchor_log, 'hook anchor log')))
    if raw_log.is_file():
        events.extend(parse_buildkit_progress(raw_log.read_text(encoding='utf-8', errors='replace')))
    return events


# The chain runs in one order and only one: a cold sample fills the cache, a fresh session then reuses it,
# the warm sample repeats with nothing changed, and incremental edits start from that same prime.
FAMILY_ORDER = ('project.cold.', 'project.cached.fresh', 'project.warm.noop', 'project.incremental.',
                'environment.bootstrap')


def family_rank(scenario_id: str) -> int:
    for i, prefix in enumerate(FAMILY_ORDER):
        if scenario_id == prefix or scenario_id.startswith(prefix):
            return i
    raise ObservatoryError(
        f'scenario {scenario_id!r} belongs to no known family, so it has no place in a measurement chain')


def scenario_order(suite: dict, wanted: list[str]) -> list[str]:
    """Scenarios in chain order: a scenario that reuses a cache runs after the one that filled it.

    Running warm before its prime would either fail the provenance check or — worse — measure a cache
    somebody else filled, which is the defect that blocked the first candidate."""
    known = {s['id'] for s in suite['scenarios']}
    unknown = [s for s in wanted if s not in known]
    if unknown:
        raise ObservatoryError(f'unknown scenario(s) {unknown} cannot be ordered into a chain')
    return sorted(wanted, key=lambda s: (family_rank(s), s))


def _flushed(message: str) -> None:
    """Progress must reach the operator as it happens: stdout is block-buffered when it is not a terminal,
    so an unflushed multi-hour suite is indistinguishable from a hung one."""
    print(message, flush=True)


def run_observation(root: Path, suite: dict, sel: Selection, raw_dir: Path, run_id: str,
                    progress=_flushed, checkpoint=None) -> tuple[dict, list[str], bool]:
    """Execute the selection as PER-ROOT MEASUREMENT CHAINS and return the observation.

    The first candidate primed once per scenario and then ran every command in that shared state, so a
    command labelled cold observed a cache an earlier measured command had filled. Here each root command
    owns its chain: its cold sample invalidates its own declared root, and everything cached, warm or
    incremental in that chain names the exact prime sample it reused.

    Isolation is by INVALIDATION rather than by namespace. A root forced to rebuild cannot be satisfied by
    anything another command left behind, which is what makes one shared builder honest."""
    import datetime
    import subprocess as _subprocess
    commands = {c['id']: c for c in suite['commands']}
    scenarios = {s['id']: s for s in suite['scenarios']}
    edits = {e['id']: e for e in suite.get('edits', [])}
    derived_ids = {c['id'] for c in suite['commands'] if c['measurement'] == 'derived'}

    # The canonical order, and every step of it is load-bearing.  Capturing the environment BEFORE the
    # builder existed described a builder the suite then replaced: on first use the observation named one
    # builder and the samples ran against another.  Priming stable infrastructure before the environment is
    # read means the recorded identities are the ones the samples actually used, and that the toolchain
    # download is outside every measured interval rather than inside the first cold sample.
    subj = subject(root)
    ensure_observatory_builder()
    preflight = toolchain_prime(root, progress)
    env = environment(root)
    env['preflight'] = preflight
    # The Dockerfile's own stage graph, so a cold sample can be asked what ELSE rebuilt and not merely
    # whether its declared root did, and its COPY set, so an incremental sample can be asked whether the
    # edit it made could have invalidated anything at all.
    stage_graph = docker_stage_graph(root)
    context_inputs = docker_context_inputs(root)

    samples: list[dict] = []
    incomplete: list[str] = []
    unmeasured: list[str] = []
    edits_ok = True
    graph, history = None, None
    primes: dict[tuple, dict] = {}          # (command_id, root) -> the exact prime sample identity

    def emit(sample: dict):
        # Stamped HERE, in the one place every sample passes through, rather than in each of the three
        # constructors — a fourth constructor would otherwise be one more chance to forget.
        sample['sample_id'] = sample_id_for(run_id, sample)
        samples.append(sample)
        if checkpoint:
            checkpoint(samples, incomplete)

    for cid in sel.order:
        command = commands[cid]
        if runner_for(command) != 'shell':
            continue
        chain = [s for s in scenario_order(suite, sel.scenarios) if s in command['scenarios']]
        if not chain:
            # Selected, and measured in nothing. Silence here would leave the command listed as selected with
            # no sample beside it and no reason, which reads as a measurement that went missing.
            unmeasured.append(cid)
            progress(f'fido: observe — {cid} has no scenario in this selection ('
                     f'{", ".join(command["scenarios"])}), so it contributes no sample')
            continue
        progress(f'fido: observe — chain {cid}: {", ".join(chain)}')

        for scenario_id in chain:
            scenario = scenarios[scenario_id]
            role = sample_role(sel, cid, scenario_id)
            # A command that invalidates no build root touches no project cache, so the scenario's generic
            # `reused` states are not true of it and there is no prime for it to take. §3A.4 requires
            # `not-applicable` here rather than a state the runner cannot establish.
            provenance, skip = sample_provenance(command, scenario, primes)
            root_stage = tuple(scenario['cache_cut']['invalidated_roots'])
            if skip:
                incomplete.append(f'{cid}/{scenario_id}')
                progress(f'fido: observe — {skip}')
                continue

            edit = edits.get(scenario.get('edit'))
            wanted = command['samples'][scenario_id]

            for index in range(wanted):
                label = f'{cid}/{scenario_id}' + (f'/{edit["id"]}' if edit else '')
                progress(f'fido: observe — {label} sample {index + 1}/{wanted} ({role})')
                copy = None
                scratch = None
                try:
                    iso_kind = command.get('isolation')
                    needs_copy = iso_kind == 'disposable-copy' or edit is not None
                    iso_env = {}
                    if needs_copy:
                        copy = raw_dir.parent / 'copies' / f'{cid}.{scenario_id}.{index}'
                        copy.parent.mkdir(parents=True, exist_ok=True)
                        disposable_copy(root, copy, subj['source_view'])
                    elif iso_kind:
                        scratch = raw_dir.parent / 'isolated' / f'{cid}.{scenario_id}.{index}'
                        # The scratch directory is where an isolation keeps ITS OWN files. It becomes the
                        # working directory only if the isolation says so: `temporary-docker-config` supplies
                        # environment variables and the command still runs in the repository.
                        cwd_override, iso_env = isolate(root, command, scratch)
                        copy = cwd_override
                    target = copy or root
                    before = None
                    if edit:
                        paths = [edit['path']]
                        before = tree_digest(target, paths)
                        original = (target / edit['path']).read_bytes()
                        # The RUN ID belongs in the bytes. Without it the probe is the same on every run,
                        # so the first run ever to use it pays the rebuild and every later run reads that
                        # result out of the BuildKit cache and records ~1.6s for work that costs ~116s.
                        # `edit_id` remains the comparison identity, so comparability is unaffected.
                        apply_edit(target, edit, index, probe=edit_probe(run_id, cid, scenario_id))
                        if tree_digest(target, paths) == before:
                            raise ObservatoryError(f'edit {edit["id"]}: the intended file did not change')
                    # A command declared environment-only reads no repository source, so a repository
                    # digest beside it would suggest an input it never had.
                    digest = declared_source_digest(target, command)
                    anchor_log = raw_dir / (raw_log_name(cid, scenario_id, index,
                                                         edit['id'] if edit else None) + '.anchors')
                    # A bootstrap sample must build the builder it is timing. Handing it the observatory's
                    # existing builder measured `buildx inspect` finding one already there — 0.20s, and
                    # `builder_bootstrap_included: false` under a scenario whose whole subject is bootstrap.
                    builder = (throwaway_builder(scratch)
                               if scratch is not None and iso_kind == 'temporary-docker-config'
                               else OBSERVATORY_BUILDER)
                    s = run_sample(root, {**command,
                                          'execution': materialise_execution(command, scenario, builder)},
                                   scenario, index, role, raw_dir, provenance, cwd=copy,
                                   env_extra={**instrumentation_env(command, anchor_log, scenario),
                                              **iso_env},
                                   source_digest=digest, edit_id=edit['id'] if edit else None)
                    s['derived_stage_events'] = collect_events(
                        command, anchor_log,
                        raw_dir / (raw_log_name(cid, scenario_id, index,
                                                edit['id'] if edit else None) + '.log'))
                    check_cut_observed(s, scenario, suite, stage_graph)
                    if edit:
                        check_edit_effect(s, edit, command, context_inputs)
                    emit(s)
                    for child in derive_child_samples(
                            s, s['derived_stage_events'], derived_ids,
                            role_of=lambda kid: sample_role(sel, kid, scenario_id)):
                        emit(child)
                    if edit:
                        restore_and_verify(target, edit, original, before, [edit['path']], index)
                    if scenario_id.startswith('project.cold.') and s['status'] == 'ok':
                        primes[(cid, 'prime')] = {'id': s['sample_id'], 'root': root_stage}
                except ObservatoryError as exc:
                    incomplete.append(label)
                    if edit:
                        edits_ok = False
                    progress(f'fido: observe — {label} did not complete: {exc}')
                    break
                finally:
                    # The scratch directory owns the isolation's own artefacts, including a throwaway
                    # builder, and must be released whether or not the isolation also moved the cwd.
                    if scratch is not None:
                        # Collected rather than raised: this runs in a `finally`, and raising here would
                        # replace whatever exception sent us into it.
                        leak = release_isolation(command, scratch, _subprocess.run)
                        if leak:
                            incomplete.append(leak)
                    elif copy is not None:
                        drop_disposable_copy(root, copy)

    for cid in sel.order:
        command = commands[cid]
        if runner_for(command) != 'analysis':
            continue
        # Chain order, same as the shell runner: a cold sample fills the cache before a warm one reuses it.
        # Iterating the selection's order ran the warm sample first whenever the selection listed it first.
        for scenario_id in [s for s in scenario_order(suite, sel.scenarios)
                            if s in command['scenarios']]:
            scenario = scenarios[scenario_id]
            role = sample_role(sel, cid, scenario_id)
            provenance, skip = sample_provenance(command, scenario, primes)
            if skip:
                incomplete.append(f'{cid}/{scenario_id}')
                progress(f'fido: observe — {skip}')
                continue
            wanted = command['samples'][scenario_id]
            for index in range(wanted):
                progress(f'fido: observe — {cid} [{scenario_id}] sample {index + 1}/{wanted} ({role})')
                try:
                    t0 = _monotonic_ns()
                    if command['kind'] == 'history-analysis':
                        history = history_analysis(root)
                        events = []
                    else:
                        graph = measure_module_graph(root, raw_dir / f'module-graph.{index}',
                                                     progress, scenario)
                        events = graph.pop('stage_events', []) + [
                            {'id': 'analysis.dune-graph', 'wall_ns': None, 'untimed': True, 'source': 'same-build'}]
                    s = analysis_sample(cid, scenario, role, _monotonic_ns() - t0, provenance, events,
                                        subj['content_digest'], index)
                    emit(s)
                    # An analysis command that builds has a prime to offer, exactly like a shell command.
                    if scenario_id.startswith('project.cold.') and s['status'] == 'ok':
                        primes[(cid, 'prime')] = {'id': s['sample_id'],
                                                  'root': tuple(scenario['cache_cut']['invalidated_roots'])}
                    for child in derive_child_samples(
                            s, events, derived_ids,
                            role_of=lambda kid: sample_role(sel, kid, scenario_id)):
                        emit(child)
                except ObservatoryError as exc:
                    incomplete.append(f'{cid}/{scenario_id}')
                    progress(f'fido: observe — {cid} [{scenario_id}] did not complete: {exc}')
                    break

    derived = {'summaries': summarise(samples) if samples else {},
               'selected': sel.selected, 'support': sel.support,
               'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'hook_clock': HOOK_CLOCK}
    if graph:
        derived['rebuild_impact'] = rebuild_impact(graph)
    if history:
        derived['weighted_rebuild_cost'] = weighted_rebuild_cost(history, graph)
    if graph or history:
        derived['repeated_work'] = repeated_work(suite, samples)

    # The reader I claimed this had. Recording the host load and then surfacing it nowhere made it a required
    # field nothing consumes, which is a blocked class in the accepted review basis — and I committed it in
    # the same batch where I made `invalidation_roots` load-bearing for exactly that reason. It stays a
    # DISCLOSURE and never a threshold: the range is reported, and no rule rejects a sample for it.
    derived['host_load'] = observed_load(samples)

    observation = {
        'schema': SCHEMA, 'suite_digest': suite_digest_of(suite), 'subject': subj, 'environment': env,
        'cache_model': {s: scenarios[s]['cache_cut'] for s in sel.scenarios if s in scenarios},
        'commands': command_fingerprints(suite), 'definitions': definition_fingerprints(suite),
        'measurements': samples, 'module_graph': graph, 'history_analysis': history, 'derived': derived,
        # What was asked for, and what the tool added on its own to make the answer mean anything. A reader
        # who sees a cold build in a warm-only run is owed the reason in the bundle, not in the terminal
        # scrollback that outlived it.
        'selection': {'partial': sel.partial, 'commands_selected': sorted(sel.selected),
                      'commands_support': sorted(sel.support), 'scenarios': list(sel.scenarios),
                      'scenarios_added_as_support': list(sel.scenario_support),
                      'commands_with_no_scenario_here': sorted(unmeasured),
                      'commands_never_measured': sorted(
                          c['id'] for c in suite['commands'] if c['measurement'] == 'catalog-only')},
    }
    return observation, incomplete, edits_ok


def measure_module_graph(root: Path, out_dir: Path, progress=print, scenario: dict | None = None) -> dict:
    """Build the pinned module-graph stage, export its artifacts, and derive the graph from them.

    The heavy work happens in the container, where the toolchain is pinned; this side only reads what came
    out. Raw per-sentence logs stay local in the bundle, and only per-module totals reach the observation."""
    import subprocess
    out_dir.mkdir(parents=True, exist_ok=True)
    ensure_observatory_builder()
    proc = subprocess.run(
        ['docker', 'buildx', 'build', '--builder', OBSERVATORY_BUILDER, '--platform', 'linux/amd64',
         *[a for r in ((scenario or {}).get('cache_cut', {}).get('invalidated_roots') or []
                       if (scenario or {}).get('id', '').startswith('project.cold.') else [])
             for a in ('--no-cache-filter', r)],
         '--progress=plain', '--target', 'module-graph-log', '--output', f'type=local,dest={out_dir}', '.'],
        cwd=str(root), capture_output=True, text=True)
    build_log = proc.stdout + proc.stderr
    (out_dir / 'build.log').write_text(build_log, encoding='utf-8')
    if proc.returncode != 0:
        raise ObservatoryError(f'the module-graph stage failed (exit {proc.returncode}); its log is at '
                               f'{out_dir / "build.log"}')
    wall_file = out_dir / 'module-wall-ns.txt'
    depend_file = out_dir / 'depend.mk'
    if not wall_file.is_file() or not depend_file.is_file():
        raise ObservatoryError(f'the module-graph stage produced no adjacency or timing under {out_dir}')
    wall = {}
    for line in read_text(wall_file, 'module wall times').split('\n'):
        if line.strip():
            name, _, ns = line.partition(' ')
            wall[name] = int(ns)
    if not wall:
        raise ObservatoryError('the module-graph stage measured no modules')
    progress(f'fido: observe — analysis.rocq-modules: {len(wall)} module(s) measured')
    graph = parse_module_graph(read_text(depend_file, 'module adjacency'), wall)
    graph['stage_events'] = parse_buildkit_progress(build_log)
    return graph


def sample_policy(suite: dict, scenario_id: str) -> str:
    """The sample policy stated FROM the counts that will actually run.

    The registry used to carry prose beside the numbers. Two statements of one fact agree until they do not,
    and the prose is the one nobody re-reads — so the numbers are the authority and this is generated."""
    counts = sorted({c['samples'][scenario_id] for c in suite['commands']
                     if scenario_id in c['scenarios']})
    if not counts:
        return 'no command runs in this scenario'
    words = {1: 'one sample', 2: 'two samples', 3: 'three samples'}
    if len(counts) == 1:
        return words.get(counts[0], f'{counts[0]} samples')
    return ' to '.join(words.get(n, f'{n} samples') for n in (counts[0], counts[-1]))


def render_list(suite: dict) -> str:
    """Every stable ID with what it is and how it is measured. Counts are reported, never copied into prose."""
    rows = ['ID                                KIND                  MEASURED   SIDE EFFECT              SOURCE VIEW',
            '─' * 118]
    for c in suite['commands']:
        rows.append(f'{c["id"]:<33} {c["kind"]:<21} {c["measurement"]:<10} '
                    f'{c["side_effect"]:<24} {c["source_view"]}')
        rows.append(f'    {c["purpose"]}')
        scen = ', '.join(f'{s}×{c["samples"][s]}' for s in c['scenarios']) or '(none — cataloged only)'
        rows.append(f'    groups: {", ".join(c["groups"])}   scenarios: {scen}')
        if c['dependencies']:
            rows.append(f'    requires: {", ".join(c["dependencies"])}')
        if c['measurement'] == 'catalog-only':
            rows.append(f'    cataloged, not benchmarked: {c["catalog_only_reason"]}')
        rows.append('')
    rows.append(f'{len(suite["commands"])} command(s) in {len(suite["groups"])} group(s):')
    for g in suite['groups']:
        rows.append(f'  {g["id"]:<14} {len(g["members"])} member(s)')
    rows.append('')
    rows.append(f'{len(suite["scenarios"])} scenario(s):')
    for s in suite['scenarios']:
        caches = ', '.join(f'{k}={v}' for k, v in sorted(s['cache_state'].items()))
        rows.append(f'  {s["id"]:<26} {sample_policy(suite, s["id"])}')
        rows.append(f'    {s["purpose"]}')
        rows.append(f'    session: {s["session_state"]}   primed by: '
                    f'{", ".join(s["prime_steps"]) or "(nothing — this is the prime)"}')
        rows.append(f'    caches: {caches}')
    return '\n'.join(rows)


def render_usage(suite: dict) -> str:
    """Usage generated from the registry and the argument model, so a second guide cannot drift from it."""
    groups = ', '.join(g['id'] for g in suite['groups'])
    scenarios = ', '.join(s['id'] for s in suite['scenarios'])
    return f"""fido Build Observatory — one entry point, every mode a variable on it.

  make observe                        the complete canonical suite, compared with the tracked observation
  make observe ONLY=<ids>             only these command or group IDs, plus their required setup
  make observe SCENARIO=<ids>         only these cache scenarios
  make observe BASE=<ref-or-path>     compare against an observation from a Git ref or a local bundle
  make observe COMPARE=<ref-or-path>  compare two existing observations without running anything
  make observe RECORD=1               replace the tracked observation from a clean, complete run
  make observe LIST=1                 every stable command ID and how it is measured
  make observe HELP=1                 this text

ONLY and SCENARIO take comma-separated stable IDs. ONLY also accepts a group:
  groups     {groups}
  scenarios  {scenarios}

Examples
  make observe ONLY=make.prove SCENARIO=project.cold.prover
  make observe ONLY=make.check SCENARIO=project.warm.noop
  make observe ONLY=precommit.prover SCENARIO=project.cached.fresh
  make observe ONLY=acceptance SCENARIO=project.incremental.foundation.float

Cold means PROJECT-cold, from one declared invalidation root downward. The builder, the base images and the
pinned toolchain are already present and stay cache hits; exactly the named root and its dependents rebuild.
Registry pulls and builder bootstrap are excluded from the measured interval and fail a canonical sample.
There is never a reason to clear your Docker or registry caches for ordinary observatory use — an
empty-machine run is `environment.bootstrap`, which is diagnostic and never canonical.

A cached, warm or incremental selection automatically adds its own cold prime, because a cached number whose
prime was never taken is a comparison against an unknown baseline.

Selection rules
  Unknown names fail and name the nearest valid ones; an empty expansion fails.
  Duplicates collapse; registry order is preserved so two runs stay comparable.
  Required setup and dependencies are added automatically and printed before execution.
  Selected and support commands stay distinct in the observation.
  A derived child runs through its live parent, never through a command invented here.
  RECORD=1 rejects ONLY and SCENARIO; a partial run can never update the canonical observation.

Cache axes are independent: cold/warm is the SESSION, cached/uncached is the CACHE.
{chr(10).join(f'  {s["id"]:<26} {s["purpose"]}' for s in suite["scenarios"])}
  The host page cache is uncontrolled and is never flushed by the canonical suite.

Recording requires all of: no selector; a validating registry; a clean tree and index; one exact committed
subject; every canonical command and scenario complete; every expected-success command succeeded; every
expected-failure fixture failed for its expected reason; every cache state and prime relation valid; every
incremental edit restored byte-exactly; a schema- and digest-valid observation; a complete environment; a
local bundle written first; only {OBSERVATION_REL} changed; and no commit or staging by this tool.

Comparison classifies each metric improved, regressed, overlapping-range, unchanged, added, removed or
incomparable. There is no hidden percentage threshold: overlapping sample ranges are reported as overlapping
rather than as a verdict, and a one-sample side reports its delta without claiming a noise conclusion.
Comparison exits nonzero only for invalid or unreadable data, never for a regression.

Outputs
  .build-observatory/runs/<run-id>/   local bundle: observation.json, raw/, comparison.json, comparison.txt
  {OBSERVATION_REL}      the one tracked canonical observation
  {RECOMMENDATIONS_REL}    findings, each assigned to M3, M4 or retain

Permanent versus checkpoint: `make observatory` is the coverage validator and runs on every commit.
Everything above is M2 evidence, is explicit, and takes minutes."""


def resolve(root: Path) -> list[Path]:
    """Every path this tool owns must exist, because a dangling one silently disarms a later gate."""
    missing = [rel for rel in DECLARED if not (root / rel).is_file()]
    if missing:
        raise ObservatoryError(f'{len(missing)} declared observatory path(s) do not resolve: {missing}')
    return [root / rel for rel in DECLARED]


# ─────────────────────────────────────────────────────── adversarial controls
def self_test(root: Path) -> int:
    """Deterministic fixtures needing neither Docker nor Rocq. A skipped control is never a passed one."""
    import shutil
    import tempfile
    failures = []
    counts = {'total': 0, 'must_fail': 0}

    def scenario(label: str, mutate, expect: str | None = None):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with tempfile.TemporaryDirectory() as d:
            work = Path(d) / 'tree'
            work.mkdir(parents=True)
            for rel in (SUITE_REL, MAKEFILE_REL, DOCKERFILE_REL, HOOK_REL, CONTRACT_REL):
                dst = work / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(root / rel, dst)
            # every file the registry's edits name must exist in the fixture, or the edit-path rule fires
            # first and every control above it reports the wrong reason
            for e in json.loads((work / SUITE_REL).read_text(encoding='utf-8')).get('edits', []):
                if e.get('path'):
                    stub = work / e['path']
                    stub.parent.mkdir(parents=True, exist_ok=True)
                    stub.write_text('placeholder\n', encoding='utf-8')
            try:
                mutate(work)
            except Exception as exc:                                  # a fixture that cannot be built
                failures.append(f'{label}: fixture failed to build ({exc.__class__.__name__}: {exc})')
                return
            try:
                check_coverage(work, load_suite(work))
            except ObservatoryError as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')
                return
            if expect is not None:
                failures.append(f'{label}: expected failure containing {expect!r}, but the check passed')

    def suite_of(work: Path) -> dict:
        return json.loads((work / SUITE_REL).read_text(encoding='utf-8'))

    def write_suite(work: Path, suite: dict):
        (work / SUITE_REL).write_text(json.dumps(suite, sort_keys=True, indent=2, ensure_ascii=False) + '\n',
                                      encoding='utf-8')

    def edit(work: Path, cid: str, field: str, value):
        s = suite_of(work)
        next(c for c in s['commands'] if c['id'] == cid)[field] = value
        write_suite(work, s)

    def drop(work: Path, cid: str):
        s = suite_of(work)
        s['commands'] = [c for c in s['commands'] if c['id'] != cid]
        write_suite(work, s)

    def append_hook(work: Path, text: str):
        p = work / HOOK_REL
        p.write_text(p.read_text(encoding='utf-8') + text, encoding='utf-8')

    scenario('the canonical registry classifies the whole live surface', lambda w: w)

    scenario('a public Make target absent from the registry',
             lambda w: drop(w, 'make.diet'),
             expect="has 'make.diet' with no registry entry")
    scenario('a stale registry Make target',
             lambda w: edit(w, 'make.diet', 'id', 'make.no-such-target'),
             expect='no longer declares it')
    scenario('a Docker stage absent from the registry',
             lambda w: drop(w, 'docker.prover'),
             expect="has 'docker.prover' with no registry entry")
    scenario('a stale registry Docker stage',
             lambda w: edit(w, 'docker.prover', 'id', 'docker.no-such-stage'),
             expect='no longer declares it')
    scenario('a pre-commit anchor absent from the registry',
             lambda w: drop(w, 'precommit.naming'),
             expect="anchors 'precommit.naming' with no registry entry")
    scenario('a registry pre-commit stage with no anchor pair',
             lambda w: edit(w, 'precommit.naming', 'id', 'precommit.no-such-stage'),
             expect='carries no such anchor pair')

    scenario('an invented cache state value',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'cache_state': {**s['cache_state'], 'dune_build': 'warmish'}}
                 for s in suite_of(w)['scenarios']]}),
             expect='are not one of')
    scenario('a scenario leaving a cache authority unstated',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'cache_state': {k: v for k, v in s['cache_state'].items() if k != 'dune_build'}}
                 for s in suite_of(w)['scenarios']]}),
             expect='are unstated')

    scenario('a scenario no command can run in',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': suite_of(w)['scenarios'] + [
                 {'id': 'orphan.scenario', 'canonical': False, 'purpose': 'p', 'session_state': 'fresh',
                  'cache_state': {a: 'not-applicable' for a in CACHE_AUTHORITIES}, 'prime_steps': [],
                  'cache_cut': {'stable_through': 'rocq-base', 'invalidated_roots': [],
                                'registry_pulls_included': False,
                                'builder_bootstrap_included': False}}]}),
             expect='no command runs in it')
    scenario('a scenario that does not say whether it is canonical',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {k: v for k, v in s.items() if k != 'canonical'} for s in suite_of(w)['scenarios']]}),
             expect="missing field(s) ['canonical']")

    scenario('an incremental scenario with no edit',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {k: v for k, v in s.items() if k != 'edit'}
                 if s['id'].startswith('project.incremental.') else s
                 for s in suite_of(w)['scenarios']]}),
             expect='would measure a no-op and record it as a rebuild')
    scenario('an incremental scenario whose edit changes nothing',
             lambda w: write_suite(w, {**suite_of(w),
                 'edits': suite_of(w)['edits'] + [{'id': 'edit.nothing', 'kind': 'append-comment-line',
                                                   'path': None, 'purpose': 'p', 'rationale': 'r',
                                                   'text': ''}],
                 'scenarios': [{**s, 'edit': 'edit.nothing'}
                               if s['id'].startswith('project.incremental.') else s
                               for s in suite_of(w)['scenarios']]}),
             expect='an edit shape must name exactly one file to change')

    scenario('an incremental scenario naming an unregistered edit',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'edit': 'edit.no.such'} if s['id'].startswith('project.incremental.') else s
                 for s in suite_of(w)['scenarios']]}),
             expect='not a registered edit shape')
    scenario('a non-incremental scenario carrying an edit',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'edit': 'edit.leaf.emit'} if s['id'] == 'project.warm.noop' else s
                 for s in suite_of(w)['scenarios']]}),
             expect='is not an incremental scenario')
    scenario('a canonical cold scenario that admits a registry pull',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'cache_cut': {**s['cache_cut'], 'registry_pulls_included': True}}
                 if s['id'].startswith('project.cold.') else s
                 for s in suite_of(w)['scenarios']]}),
             expect='measures machine setup, not this repository')
    scenario('a cold scenario invalidating a root its own name does not declare',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'cache_cut': {**s['cache_cut'], 'invalidated_roots': ['emit']}}
                 if s['id'] == 'project.cold.prover' else s
                 for s in suite_of(w)['scenarios']]}),
             expect='is not the root its own name declares')
    scenario('an edit naming a file that is not there',
             lambda w: write_suite(w, {**suite_of(w), 'edits': [
                 {**e, 'path': 'NoSuchModule.v'} for e in suite_of(w)['edits']]}),
             expect='which is not a file')

    scenario('a duplicate command id',
             lambda w: edit(w, 'make.diet', 'id', 'make.fmt'),
             expect='duplicate command id')
    scenario('a stored group membership beside the command entries',
             lambda w: write_suite(w, {**suite_of(w), 'groups': [{'id': 'x', 'members': []}]}),
             expect='second authority for a fact the command entries already state')
    scenario('a scenario carrying an applicability nothing consumes',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'applicable_groups': ['acceptance']} for s in suite_of(w)['scenarios']]}),
             expect='nothing consumes it')
    scenario('a scenario carrying sample-policy prose beside the counts',
             lambda w: write_suite(w, {**suite_of(w), 'scenarios': [
                 {**s, 'sample_policy': 'three samples'} for s in suite_of(w)['scenarios']]}),
             expect='generated, not stored')
    scenario('a dependency cycle in the registry',
             lambda w: (edit(w, 'make.prove', 'dependencies', ['make.emit']),
                        edit(w, 'make.emit', 'dependencies', ['make.prove'])),
             expect='dependency cycle')
    scenario('a zero sample count',
             lambda w: edit(w, 'make.diet', 'samples', {'project.warm.noop': 0}),
             expect='must be a positive integer')
    scenario('a fractional sample count',
             lambda w: edit(w, 'make.diet', 'samples', {'project.warm.noop': 1.5}),
             expect='must be a positive integer')
    scenario('a derived child declaring its own scenarios',
             lambda w: (edit(w, 'docker.profile', 'scenarios', ['project.cold.prover']),
                        edit(w, 'docker.profile', 'samples', {'project.cold.prover': 1})),
             expect='both follow from its parents')
    scenario('a derived child declaring only its own sample counts',
             lambda w: edit(w, 'docker.profile', 'samples', {'project.cold.profile': 1}),
             expect='both follow from its parents')
    scenario('a duplicate anchor pair in the hook',
             lambda w: append_hook(w, 'fido_observe begin precommit.naming\n'
                                      'fido_observe end precommit.naming\n'),
             expect='duplicate anchor pair')
    scenario('an anchor that never ends',
             lambda w: append_hook(w, 'fido_observe begin precommit.dangling\n'),
             expect='never end')
    scenario('an anchor that ends with none open',
             lambda w: append_hook(w, 'fido_observe end precommit.stray\n'),
             expect='ends with none open')
    scenario('interleaved anchor pairs',
             lambda w: append_hook(w, 'fido_observe begin precommit.outer\n'
                                      'fido_observe begin precommit.inner\n'
                                      'fido_observe end precommit.outer\n'
                                      'fido_observe end precommit.inner\n'),
             expect='anchor pairs must nest')

    scenario('an expected-failure fixture with no declared reason',
             lambda w: edit(w, 'make.diet', 'expected_exit', 2),
             expect='declares no expected_failure_reason')

    scenario('a catalog-only command with no reason',
             lambda w: edit(w, 'make.observe', 'catalog_only_reason', '   '),
             expect='catalog-only with no reason')
    scenario('a command identified by source line number',
             lambda w: edit(w, 'make.diet', 'owner', 'Makefile:110'),
             expect='identifies its source by line number')
    scenario('an owner token that does not occur in its file',
             lambda w: edit(w, 'make.diet', 'owner', 'Makefile:no-such-target-token'),
             expect='does not occur in Makefile')
    scenario('an owner path that is not a file',
             lambda w: edit(w, 'make.diet', 'owner', 'no/such/file.mk:diet'),
             expect='is not a file in this tree')

    scenario('an unknown command kind',
             lambda w: edit(w, 'make.diet', 'kind', 'invented-kind'),
             expect='not one of')
    scenario('an unknown side-effect class',
             lambda w: edit(w, 'make.diet', 'side_effect', 'harmless'),
             expect='not one of')
    scenario('a scenario reference with no sample count',
             lambda w: (edit(w, 'make.diet', 'scenarios', ['project.cold.prover']),
                        edit(w, 'make.diet', 'invalidation_roots', ['prover'])),
             expect='has no sample count')
    scenario('a build target naming no Dockerfile stage',
             lambda w: edit(w, 'make.prove', 'build_targets', ['no-such-stage']),
             expect='name no Dockerfile stage')
    scenario('a derived command claiming it builds something',
             lambda w: edit(w, 'docker.prover', 'build_targets', ['prover']),
             expect='only a command that runs can build anything')
    scenario('a cold root the command never builds',
             lambda w: edit(w, 'make.emit', 'invalidation_roots', ['go-e2e']),
             expect='its build never reaches')

    scenario('a bootstrap claim with no builder to establish it',
             lambda w: edit(w, 'make.builder', 'isolation', None),
             expect='only temporary-docker-config gives it the empty builder')

    scenario('a command claiming a root its cold scenarios do not name',
             lambda w: edit(w, 'make.diet', 'invalidation_roots', ['prover']),
             expect='a command rebuilds exactly the roots it can be measured cold from')
    scenario('a derived command claiming it invalidates something',
             lambda w: edit(w, 'docker.prover', 'invalidation_roots', ['prover']),
             expect='it performs no build of its own')

    scenario('an unknown scenario reference',
             lambda w: (edit(w, 'make.diet', 'scenarios', ['no.such.scenario']),
                        edit(w, 'make.diet', 'samples', {'no.such.scenario': 1})),
             expect='unknown scenario')
    scenario('an unknown dependency',
             lambda w: edit(w, 'make.diet', 'dependencies', ['make.no-such']),
             expect='unknown dependenc')
    scenario('a registry that is not valid JSON',
             lambda w: (w / SUITE_REL).write_text('{ not json', encoding='utf-8'),
             expect='not valid JSON')
    scenario('a registry with the wrong schema',
             lambda w: write_suite(w, {**suite_of(w), 'schema': 'other/9'}),
             expect='schema is')
    scenario('a Makefile with no .PHONY declaration',
             lambda w: (w / MAKEFILE_REL).write_text('all:\n\t@true\n', encoding='utf-8'),
             expect='no .PHONY declaration')
    scenario('a Dockerfile with no named stages',
             lambda w: (w / DOCKERFILE_REL).write_text('FROM scratch\n', encoding='utf-8'),
             expect='no named build stages')
    scenario('a hook with no anchors at all',
             lambda w: (w / HOOK_REL).write_text('#!/bin/sh\nset -e\n', encoding='utf-8'),
             expect='no observation anchors')

    # ── selection closure, over the real registry: these rules are pure and need no fixture tree
    suite = load_suite(root)

    def scen_of(s: dict, sid: str) -> dict:
        return next(x for x in s['scenarios'] if x['id'] == sid)

    def selection(label: str, expect: str | None = None, **kw):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        try:
            result = select(suite, **kw)
        except ObservatoryError as exc:
            if expect is None:
                failures.append(f'{label}: expected success, failed with: {exc}')
            elif expect not in str(exc):
                failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')
            return None
        if expect is not None:
            failures.append(f'{label}: expected failure containing {expect!r}, but selection succeeded')
        return result

    def expect_that(label: str, ok: bool, why: str):
        counts['total'] += 1
        if not ok:
            failures.append(f'{label}: {why}')

    counts['total'] += 1
    default = select(suite)
    non_canonical = [s['id'] for s in suite['scenarios'] if not s.get('canonical')]
    if any(s in default.scenarios for s in non_canonical):
        failures.append(f'the default run must be the canonical closure, but took {default.scenarios}')
    if not default.scenarios:
        failures.append('the default run selected no scenario at all')

    counts['total'] += 1
    named = select(suite, scenario='environment.bootstrap')
    if named.scenarios != ['environment.bootstrap']:
        failures.append(f'a non-canonical scenario must still be selectable by name: {named.scenarios}')

    full = selection('the whole registry selects with no ONLY or SCENARIO')
    if full:
        expect_that('the full selection is not partial', not full.partial, 'a full run reported itself partial')
        expect_that('the full selection has no support commands', not full.support,
                    f'a full run pulled in support: {full.support}')

    one = selection('one command selects', only='make.prove')
    if one:
        expect_that('one command selects exactly itself', one.selected == ['make.prove'],
                    f'selected {one.selected}')
        expect_that('one command reports itself partial', one.partial, 'a selective run reported itself full')

    grp = selection('a group selects its members', only='policy')
    if grp:
        members = next(g['members'] for g in suite['groups'] if g['id'] == 'policy')
        expect_that('a group expands to exactly its registry members', set(grp.selected) == set(members),
                    f'group policy expanded to {sorted(set(grp.selected) ^ set(members))} difference')

    dup = selection('duplicate names collapse without reordering', only='make.prove,make.diet,make.prove')
    if dup and one:
        order = [c['id'] for c in suite['commands']]
        expect_that('a duplicated selection keeps registry order',
                    dup.selected == [c for c in order if c in {'make.prove', 'make.diet'}],
                    f'selected {dup.selected}')

    child = selection('a derived child pulls in its live parent', only='precommit.prover')
    if child:
        expect_that('a derived child is measured through the live parent',
                    child.support == ['precommit.full'], f'support was {child.support}')
        expect_that('the parent is support, not a selected result',
                    child.selected == ['precommit.prover'], f'selected {child.selected}')

    stage = selection('a derived docker stage pulls in the build that produces it', only='docker.go-e2e')
    if stage:
        expect_that('a docker stage names its live parent build', stage.support == ['make.e2e'],
                    f'support was {stage.support}')

    # The fixture observation is generated FROM expected_relation, so it cannot judge it. These assertions
    # state the relation independently: from the Dockerfile graph, and from the registry's own scenario lists.
    counts['total'] += 1
    _graph = docker_stage_graph(root)
    _rel = expected_relation(suite, graph=_graph)
    _cmds = {c['id']: c for c in suite['commands']}
    for key, spec in _rel.items():
        parent = spec['derived_parent_id']
        if parent and spec['scenario_id'] not in _cmds[parent]['scenarios']:
            failures.append(f'{key} expects a child under a parent that never runs in that scenario')
            break
    builders = {c['id'] for c in suite['commands'] if c.get('build_targets')}
    for stage, want in (('docker.sync', {'make.regenerate'}),
                        ('docker.generated-artifact', {'make.check', 'precommit.full'})):
        got = {spec['derived_parent_id'] for k, spec in _rel.items() if spec['command_id'] == stage}
        if got != want & builders:
            failures.append(f'{stage} is expected under {sorted(got)}, but the Dockerfile graph and the '
                            f'declared build targets say {sorted(want & builders)}')

    counts['total'] += 1
    warm_only = select(suite, only='make.prove', scenario='project.warm.noop')
    if 'project.cold.prover' not in warm_only.scenarios:
        failures.append(f'a warm selection must pull in its own cold prime: {warm_only.scenarios}')
    if 'project.cold.prover' not in warm_only.scenario_support:
        failures.append('the added prime must be reported as support, not presented as requested')

    # The role a SAMPLE carries, not just the role the selection computed. These are separate mistakes:
    # the selection can know the prime was added and the sample can still be stamped `selected`.
    counts['total'] += 1
    if sample_role(warm_only, 'make.prove', 'project.cold.prover') != 'support':
        failures.append('a sample in an auto-added prime scenario must be stamped support, '
                        'or the observation claims the operator asked for the cold build')
    counts['total'] += 1
    if sample_role(warm_only, 'make.prove', 'project.warm.noop') != 'selected':
        failures.append('the scenario the operator actually asked for must stay selected')
    counts['total'] += 1
    if sample_role(warm_only, 'docker.prover', 'project.warm.noop') != 'support':
        failures.append('a command that was never selected stays support')

    # §3A.5 in as many words: a selected derived child is marked selected even when its live parent is
    # support. Spreading the parent's fields into the child stamped it `support` and the control that
    # existed only checked the Selection object, which was right, rather than the sample, which was not.
    counts['total'] += 1
    child_sel = select(suite, only='docker.prover')
    parent_of_child = 'make.prove'
    if parent_of_child not in child_sel.support:
        failures.append(f'selecting a derived child must pull in its live parent: {child_sel.support}')
    kid = derive_child_samples(
        {'command_id': parent_of_child, 'scenario_id': 'project.cold.prover',
         'selected_or_support': sample_role(child_sel, parent_of_child, 'project.cold.prover')},
        [{'id': 'docker.prover', 'aggregate_step_ns': 5, 'source': 'buildkit-progress'}],
        {'docker.prover'},
        role_of=lambda k: sample_role(child_sel, k, 'project.cold.prover'))
    if not kid or kid[0]['selected_or_support'] != 'selected':
        failures.append('a SELECTED derived child was stamped support because it inherited its parent\'s '
                        'role, which is the reverse of what the contract states')

    counts['total'] += 1
    cold_only = select(suite, only='make.prove', scenario='project.cold.prover')
    if cold_only.scenario_support:
        failures.append(f'a cold selection needs no prime added: {cold_only.scenario_support}')

    combo = selection('ONLY and SCENARIO combine', only='make.check', scenario='project.warm.noop')
    if combo:
        expect_that('a combined selection keeps the named scenario and its required prime',
                    set(combo.scenarios) == {'project.warm.noop', 'project.cold.generated-artifact'},
                    f'scenarios were {combo.scenarios}')

    selection('an unknown ONLY name', expect='unknown ONLY name', only='make.prov')
    selection('an unknown SCENARIO name', expect='unknown SCENARIO name', scenario='warm.noop')
    selection('an empty ONLY expansion', expect='expanded to nothing', only=' , ')
    selection('RECORD with ONLY', expect='RECORD=1 rejects ONLY', only='make.prove', record=True)
    selection('RECORD with SCENARIO', expect='RECORD=1 rejects ONLY', scenario='project.cached.fresh', record=True)
    selection('a selection with no command in the named scenario',
              expect='no selected command runs in scenario',
              only='make.fmt', scenario='project.incremental.foundation.float')

    counts['total'] += 1
    near = None
    try:
        select(suite, only='make.prov')
    except ObservatoryError as exc:
        near = str(exc)
    if not near or 'make.prove' not in near:
        failures.append(f'an unknown name names the nearest valid one: got {near!r}')

    # ── cache provenance and edit restoration, over disposable fixtures
    import tempfile as _tempfile

    def guarded(label: str, fn, expect: str | None = None):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with _tempfile.TemporaryDirectory() as d:
            work = Path(d) / 'tree'
            work.mkdir(parents=True)
            try:
                fn(work)
            except ObservatoryError as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')
                return
            if expect is not None:
                failures.append(f'{label}: expected failure containing {expect!r}, but it succeeded')

    reusing = next(s for s in suite['scenarios'] if 'reused' in s['cache_state'].values())
    guarded('the developer\'s builder is never modified',
            lambda _: _assert_observatory_builder('fido-builder'),
            expect='refusing to modify builder')
    guarded('the observatory builder is the one it may modify',
            lambda _: _assert_observatory_builder(OBSERVATORY_BUILDER))

    EDIT = {'id': 'edit.leaf', 'path': 'leaf.v', 'kind': 'append-comment-line',
            'text': '(* observatory: inert timing probe *)\n'}
    STAMPED = {**EDIT, 'text': '(* observatory: inert edit probe {n} *)\n'}

    # The observatory writes its probe into a `.v` comment, so the line it writes must obey the repository's
    # own source law: one line, at most 120 characters. Spelled out it was 136 and `make check` failed its
    # own gate on every scenario that edits a `.v` file — the M1 law catching an M2 edit.
    counts['total'] += 1
    long_probe = edit_probe('20260730T031242123456p0000-6ffb586-5ea202d6-bcb7a8',
                            'make.check', 'project.incremental.foundation.float')
    for e in suite['edits']:
        if not e['path'].endswith('.v'):
            continue
        rendered = e['text'].format(n=f'{long_probe}-0').rstrip('\n')
        if len(rendered) > 120 or '\n' in rendered:
            failures.append(f'the edit written into {e["path"]} is {len(rendered)} characters, past the '
                            f'120-character source law it must satisfy: {rendered!r}')

    # Same edit shape, same sample index, two different RUNS: the bytes must differ, or the second run reads
    # the first run's build out of the BuildKit cache and records a hit as though it were a rebuild. This is
    # the across-time twin of the across-command case below, and it cost two canonical observations.
    counts['total'] += 1
    with _tempfile.TemporaryDirectory() as d:
        w = Path(d)
        runs = []
        for rid in ('20260730T010101-aaaaaaa-1111', '20260730T020202-bbbbbbb-2222'):
            (w / 'leaf.v').write_bytes(b'Definition x := 1.\n')
            apply_edit(w, {'id': 'edit.leaf', 'path': 'leaf.v', 'kind': 'append-comment-line',
                           'text': '(* observatory: inert edit probe {n} *)\n'},
                       0, probe=edit_probe(rid, 'make.prove', 'project.incremental.leaf.emit'))
            runs.append((w / 'leaf.v').read_bytes())
        if runs[0] == runs[1]:
            failures.append('two runs wrote identical incremental bytes, so the second measures the first '
                            'run\'s cached build and reports it as a rebuild')

    # Same edit shape, same sample index, two different commands: the bytes must differ, or the two trees
    # are identical and whichever command builds first pays for both.
    counts['total'] += 1
    with _tempfile.TemporaryDirectory() as d:
        w = Path(d)
        written = []
        for probe in ('make.prove.project.incremental.leaf.emit',
                      'make.check.project.incremental.leaf.emit'):
            (w / 'leaf.v').write_bytes(b'Definition x := 1.\n')
            apply_edit(w, STAMPED, 0, probe=probe)
            written.append((w / 'leaf.v').read_bytes())
        if written[0] == written[1]:
            failures.append('two commands wrote identical incremental bytes for the same sample index, so '
                            'one command\'s rebuild would satisfy the other\'s incremental sample')

    def edit_cycle(work: Path, restore: bool):
        (work / 'leaf.v').write_bytes(b'Definition x := 1.\n')
        (work / 'other.v').write_bytes(b'Definition y := 2.\n')
        paths = ['leaf.v', 'other.v']
        before = tree_digest(work, paths)
        original = (work / 'leaf.v').read_bytes()
        apply_edit(work, EDIT)
        if tree_digest(work, paths) == before:
            raise ObservatoryError('edit.leaf: the intended file did not change')
        if (work / 'other.v').read_bytes() != b'Definition y := 2.\n':
            raise ObservatoryError('edit.leaf: a file outside the edit changed')
        if not restore:
            (work / 'leaf.v').write_bytes(original + b'stray\n')
        restore_and_verify(work, EDIT, original if restore else original + b'stray\n', before, paths)

    guarded('one exact incremental edit and restore', lambda w: edit_cycle(w, restore=True))
    guarded('an incremental edit that is not restored', lambda w: edit_cycle(w, restore=False),
            expect='did not restore byte-exactly')
    guarded('an edit whose target is missing',
            lambda w: apply_edit(w, EDIT), expect='is not a file in the disposable copy')
    guarded('an unknown edit kind',
            lambda w: ((w / 'leaf.v').write_bytes(b'x\n'), apply_edit(w, {**EDIT, 'kind': 'patch'})),
            expect='unknown edit kind')

    # ── observation validation and the fourteen recording rules, over a synthetic observation
    digest = suite_digest_of(suite)

    def sample(**over) -> dict:
        base = {'command_id': 'make.fmt', 'scenario_id': 'project.warm.noop', 'sample_index': 0,
                'edit_id': None, 'derived_parent_id': None,
                'cache_cut': {'stable_through': 'rocq-base', 'invalidated_roots': [],
                              'registry_pulls_included': False, 'builder_bootstrap_included': False},
                'cache_observation': {'stages': {}}, 'source_digest': 'e0' * 32,
                'selected_or_support': 'selected', 'start_utc': '2026-01-01T00:00:00+00:00',
                'wall_ns': 1_000_000, 'user_cpu_ns': 500_000, 'system_cpu_ns': 400_000,
                'max_rss_bytes': 1024, 'resource_scope': SCOPE_HOST, 'measurement_kind': KIND_WALL,
                'exit_code': 0, 'expected_exit': 0,
                'host_load': {'before': 0.5, 'after': 0.5},
                'status': 'ok', 'cache_before': {'authorities': {}, 'primed_by_run': 'run-a'},
                'cache_after': {}, 'raw_log_sha256': 'ab' * 32,
                'expected_failure_reason': None, 'derived_stage_events': [], 'parent_sample_id': None}
        s = {**base, **over}
        # Stamped exactly as the runner stamps it, so a fixture cannot satisfy an identity rule the live
        # path would fail.
        s['sample_id'] = over.get('sample_id') or sample_id_for('run-fixture', s)
        return s

    def observation(samples=None, **over) -> dict:
        samples = samples if samples is not None else [sample(sample_index=i, wall_ns=n)
                                                       for i, n in enumerate((900_000, 1_000_000, 1_100_000))]
        base = {'schema': SCHEMA, 'suite_digest': digest, 'run_id': 'run-fixture',
                'subject': {'commit': 'a' * 40, 'tree': 'b' * 40, 'inventory_digest': 'c' * 64,
                            'dirty': False, 'source_view': 'committed-tree'},
                'environment': {**{k: 'x' for k in REQUIRED_ENVIRONMENT}, 'host_class_fingerprint': 'd' * 64},
                'cache_model': {}, 'commands': {'make.fmt': 'f0' * 32},
                'definitions': {'commands': {'make.fmt': 'f0' * 32}, 'scenarios': {}, 'edits': {},
                                'stable_through': 'rocq-base'},
                'measurements': samples,
                'module_graph': None, 'history_analysis': None,
                # Derived from the samples this fixture actually holds, so it cannot drift into naming a
                # command the observation never measured.
                'selection': {'partial': False,
                              'commands_selected': sorted({s['command_id'] for s in samples}),
                              'commands_support': [],
                              'scenarios': sorted({s['scenario_id'] for s in samples}),
                              'scenarios_added_as_support': [],
                              'commands_with_no_scenario_here': [],
                              'commands_never_measured': []},
                'derived': {'summaries': summarise(samples)}}
        return {**base, **over}

    def observed(label: str, fn, expect: str | None = None):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        try:
            fn()
        except ObservatoryError as exc:
            if expect is None:
                failures.append(f'{label}: expected success, failed with: {exc}')
            elif expect not in str(exc):
                failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')
            return
        if expect is not None:
            failures.append(f'{label}: expected failure containing {expect!r}, but it succeeded')

    observed('a complete observation validates',
             lambda: validate_observation(observation(), digest))
    observed('an observation with a suite digest mismatch',
             lambda: validate_observation(observation(), 'f' * 64),
             expect='describe different suites')
    observed('an observation missing a required member',
             lambda: validate_observation({k: v for k, v in observation().items() if k != 'module_graph'},
                                          digest),
             expect='missing member')
    observed('an observation retaining no samples',
             lambda: validate_observation(observation(samples=[], derived={'summaries': {}}), digest),
             expect='retains no samples')
    observed('a sample missing a required field',
             lambda: validate_observation(
                 observation(samples=[{k: v for k, v in sample().items() if k != 'max_rss_bytes'}],
                             derived={'summaries': summarise([sample()])}), digest),
             expect='missing field')
    observed('a negative duration',
             lambda: validate_observation(
                 observation(samples=[sample(wall_ns=-1)],
                             derived={'summaries': summarise([sample(wall_ns=-1)])}), digest),
             expect='negative wall_ns')

    # ── §10 zero is a measured claim, and it is false whenever work happened
    def only(s):
        return lambda: validate_observation(
            observation(samples=[s], derived={'summaries': summarise([s])}), digest)

    observed('an authority map that disagrees with the stage evidence beside it',
             only(sample(cache_observation={'stages': {'prover': 'rebuilt'}},
                         cache_before={'authorities': {'dune_build': 'empty'}, 'primed_by_run': 'run-a'},
                         cache_after={'authorities': {'dune_build': 'empty'}})),
             expect='not what the retained stage evidence derives')
    observed('work timed as exactly zero',
             only(sample(wall_ns=0)), expect='elapsed duration of exactly zero')
    observed('an untimed artifact still carrying a duration',
             only(sample(measurement_kind=KIND_UNTIMED, wall_ns=5)),
             expect='untimed artifact yet carries a duration')
    observed('a below-resolution interval with no bound',
             only(sample(measurement_kind=KIND_INTERVAL, wall_ns=None, lower_ns=None, upper_ns=None)),
             expect='without a usable bound')
    observed('a below-resolution interval whose bounds are inverted',
             only(sample(measurement_kind=KIND_INTERVAL, wall_ns=None, lower_ns=9, upper_ns=1)),
             expect='without a usable bound')

    counts['total'] += 1
    accepted = sample(measurement_kind=KIND_UNTIMED, wall_ns=None, aggregate_step_ns=None)
    interval = sample(measurement_kind=KIND_INTERVAL, wall_ns=None, aggregate_step_ns=None,
                      lower_ns=0, upper_ns=HOOK_CLOCK['resolution_ns'], below_resolution=True)
    for label, s in (('an untimed artifact', accepted), ('a below-resolution interval', interval)):
        try:
            validate_observation(observation(samples=[s], derived={'summaries': summarise([s])}), digest)
        except ObservatoryError as exc:
            failures.append(f'{label} was rejected: {exc}')
    rows = summarise([interval])
    if not rows or not all(r.get('below_resolution') and 'median_ns' not in r for r in rows.values()):
        failures.append('a below-resolution stage was summarised with a median it cannot have')
    # A hook anchor that begins and ends within one clock tick must become a BOUND, never a zero.
    counts['total'] += 1
    ticks = parse_anchor_log('begin precommit.fast 1000000000\nend precommit.fast 1000000000\n')
    if not ticks or ticks[0].get('wall_ns') is not None or not ticks[0].get('below_resolution'):
        failures.append(f'a hook stage faster than one clock tick was recorded as {ticks} rather than a '
                        'below-resolution bound')
    observed('an unknown resource scope',
             lambda: validate_observation(
                 observation(samples=[sample(resource_scope='guessed')],
                             derived={'summaries': summarise([sample(resource_scope='guessed')])}), digest),
             expect='not a known scope')
    observed('a tampered stored summary',
             lambda: validate_observation(observation(derived={'summaries': {'make.fmt|project.warm.noop': {
                 'samples': 3, 'median_ns': 1, 'min_ns': 1, 'max_ns': 1}}}), digest),
             expect='do not equal recomputation')

    def complete_observation(**over):
        """An observation that measured EXACTLY the relation the registry declares.

        Generating it from `expected_relation` rather than by hand is the point: a fixture written by hand
        would drift from the rule it exists to get past, which is how the earlier one let R13 and R14 pass
        by never being reached."""
        every = over.pop('samples', None)
        if every is None:
            every = []
            for spec in expected_relation(suite, graph=docker_stage_graph(root)).values():
                for i in range(spec['samples']):
                    # An incremental sample edits distinct bytes, so its disposable copy hashes differently.
                    # The fixture has to model that or it would not reach the rule which requires it.
                    digest_i = (_sha256(f'{spec["command_id"]}|{spec["scenario_id"]}|{i}'.encode('utf-8'))
                                if spec['edit_id'] else 'e0' * 32)
                    # Scope and kind come from the SPEC, not from the generic fixture default. Stamping
                    # every fixture sample `host-wrapper`/`wall_elapsed` modelled a world where an analysis
                    # command and a BuildKit stage report the same thing a shell command does, and the
                    # relation could only close because it wildcarded exactly those fields.
                    value = {KIND_AGGREGATE: {'aggregate_step_ns': 1_000_000, 'wall_ns': None},
                             KIND_UNTIMED: {'aggregate_step_ns': None, 'wall_ns': None},
                             }.get(spec['measurement_kind'], {})
                    every.append(sample(command_id=spec['command_id'], scenario_id=spec['scenario_id'],
                                        edit_id=spec['edit_id'], derived_parent_id=spec['derived_parent_id'],
                                        selected_or_support=spec['selected_or_support'],
                                        resource_scope=spec['resource_scope'],
                                        measurement_kind=spec['measurement_kind'],
                                        sample_index=i, source_digest=digest_i, **value))
            # Parents before children, then each child bound to the EXACT parent sample it came from. The
            # relation is generated from a sorted key set, which does not put a producer before the stage it
            # produces, and a child whose parent had not happened yet is exactly what the ordering rule
            # exists to refuse.
            every.sort(key=lambda s: bool(s.get('derived_parent_id')))
            by_parent: dict[tuple, str] = {}
            for s in every:
                if not s.get('derived_parent_id'):
                    by_parent.setdefault((s['command_id'], s['scenario_id']), s['sample_id'])
            for s in every:
                if s.get('derived_parent_id'):
                    s['parent_sample_id'] = by_parent.get((s['derived_parent_id'], s['scenario_id']))
        over.setdefault('derived', {'summaries': summarise(every)})
        return observation(samples=every, **over)

    def record_check(**over):
        args = {'sel': Selection([], [], [], partial=False), 'suite': suite, 'suite_digest': digest,
                'obs': complete_observation(),
                'clean_before': True, 'edits_restored': True, 'incomplete': []}
        args.update(over)
        with _tempfile.TemporaryDirectory() as d:
            bundle = Path(d) / 'bundle'
            bundle.mkdir(parents=True)
            if args.pop('bundle_written', True):
                write_json(bundle / 'observation.json', args['obs'])
            return check_record_eligible(root, bundle=bundle, **args)

    observed('a partial run with RECORD', lambda: record_check(sel=Selection([], [], [], partial=True)),
             expect='recording rule R01')

    # R08 against the LIVE prime authority, over a COMPLETE observation with exactly one sample perturbed,
    # so coverage still closes and R08 is the rule that speaks.
    def pick(obs, what, predicate):
        """One retained sample matching `predicate`, or a REPORTED failure.

        Never a bare `next()`: an uncaught StopIteration aborts the whole self-test, so every control after
        this one would go unexercised while still looking load-bearing to the mutation harness.
        """
        found = next((s for s in obs['measurements'] if predicate(s)), None)
        if found is None:
            raise ObservatoryError(f'the fixture retains no {what} to select')
        return found

    def first_derived(obs):
        return pick(obs, 'derived sample', lambda s: s.get('derived_parent_id'))

    def prove_sample(obs, scenario_id):
        return pick(obs, f'make.prove sample in {scenario_id}',
                    lambda s: s['command_id'] == 'make.prove' and s['scenario_id'] == scenario_id)

    def with_reuse(prime):
        obs = complete_observation()
        target = next(s for s in obs['measurements']
                      if s['command_id'] == 'make.prove' and s['scenario_id'] == 'project.warm.noop')
        target['cache_before'] = {**target['cache_before'],
                                  'authorities': {a: 'reused' for a in PROJECT_CACHES},
                                  'prime_sample_id': prime}
        return obs

    observed('a reused project cache naming no prime',
             lambda: record_check(obs=with_reuse(None)), expect='recording rule R08')
    observed('a reused project cache naming a prime nothing retains',
             lambda: record_check(obs=with_reuse('make.prove|project.cold.prover|-|-|selected|nowhere|wall_elapsed')),
             expect='recording rule R08')
    def not_cold_prime():
        """A prime that is a real retained sample of the right command, and simply is not COLD.

        It used to name a metric CLASS string, which now fails at "this observation does not retain that
        sample" — so the cold rule was never reached and its mutant reported the rule unprotected.
        `project.cached.fresh` sorts before `project.warm.noop`, so it also precedes the sample it primes.
        """
        obs = with_reuse(None)
        warm = prove_sample(obs, 'project.warm.noop')
        warm['cache_before']['prime_sample_id'] = prove_sample(obs, 'project.cached.fresh')['sample_id']
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('a prime that is not a cold sample',
             lambda: record_check(obs=not_cold_prime()), expect='is not a cold sample')
    # ── §14 the exact relation closes over role, scope and kind, not only over command and scenario
    def relabelled(command_id: str, scenario_id: str, **fields):
        """One retained sample given a different role, scope or kind than the registry requires.

        A missing target is reported rather than raised as `StopIteration`: an uncaught exception here
        aborts the whole self-test, so a later control's rule would go unexercised and look load-bearing
        when nothing had reached it.
        """
        obs = complete_observation()
        target = next((s for s in obs['measurements']
                       if s['command_id'] == command_id and s['scenario_id'] == scenario_id), None)
        if target is None:
            raise ObservatoryError(f'the fixture retains no {command_id} sample in {scenario_id} to relabel')
        target.update(fields)
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('a selected sample relabelled support',
             lambda: record_check(obs=relabelled('make.diet', 'project.warm.noop',
                                                 selected_or_support='support')),
             expect='coverage on paper')
    def with_support_extra():
        """A support-role sample beside the selected ones for a pair the registry declares.

        It keeps the command, scenario and index of a real sample, so the raw-log rule still passes and the
        ONLY thing that distinguishes it is its role. Without role in the key it would be invisible.
        """
        obs = complete_observation()
        twin = dict(pick(obs, 'make.diet sample', lambda s: s['command_id'] == 'make.diet'),
                    selected_or_support='support')
        obs['measurements'] = obs['measurements'] + [twin]
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('a support sample beside the selected ones for a declared pair',
             lambda: record_check(obs=with_support_extra()), expect='coverage on paper')
    observed('a direct sample claiming BuildKit stage scope',
             lambda: record_check(obs=relabelled('make.diet', 'project.warm.noop',
                                                 resource_scope=SCOPE_BUILDKIT)),
             expect='coverage on paper')
    observed('aggregate step work presented as elapsed wall time',
             lambda: record_check(obs=relabelled('docker.prover', 'project.cold.prover',
                                                 measurement_kind=KIND_WALL)),
             expect='coverage on paper')

    # A parallel stage does MORE aggregate work than the elapsed time it took. Pooling the two, or printing
    # one under the other's name, states something arithmetically impossible; the kind is in the key, so the
    # summary keeps them apart and says which is which.
    counts['total'] += 1
    parallel = [sample(command_id='docker.prover', derived_parent_id='make.prove',
                       resource_scope=SCOPE_BUILDKIT, measurement_kind=KIND_AGGREGATE,
                       wall_ns=None, aggregate_step_ns=9_000_000),
                sample(command_id='make.prove', wall_ns=3_000_000)]
    pooled = summarise(parallel)
    if len(pooled) != 2:
        failures.append('aggregate step work and elapsed wall time were pooled into one summary')
    else:
        kinds = {v['measurement_kind'] for v in pooled.values()}
        if kinds != {KIND_AGGREGATE, KIND_WALL}:
            failures.append(f'a summary did not state which kind of measurement it holds: {kinds}')
        if any('wall' in field for v in pooled.values() for field in v if field.endswith('_ns')):
            failures.append('a summary field still names wall time for a value that may be aggregate work')

    # ── §4 exact run, sample, parent and prime identities
    def mangled(fn):
        obs = complete_observation()
        fn(obs)
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('an observation with no run identity',
             lambda: record_check(obs=mangled(lambda o: o.pop('run_id'))),
             expect='retains no run identity')
    observed('two samples sharing one identity',
             lambda: record_check(obs=mangled(
                 lambda o: o['measurements'][1].update(sample_id=o['measurements'][0]['sample_id']))),
             expect='duplicate sample identit')
    observed('a derived child naming no exact parent sample',
             lambda: record_check(obs=mangled(lambda o: first_derived(o).update(parent_sample_id=None))),
             expect='names no exact parent sample')
    observed('a derived child naming a parent from another run',
             lambda: record_check(obs=mangled(
                 lambda o: first_derived(o).update(parent_sample_id='run-elsewhere#x#0'))),
             expect='does not retain')
    observed('a direct sample claiming a parent sample',
             lambda: record_check(obs=mangled(
                 lambda o: pick(o, 'direct sample',
                                lambda s: not s.get('derived_parent_id')).update(parent_sample_id='x'))),
             expect='direct sample yet names a parent sample')

    def reuse_naming(choose):
        """A cached make.prove sample whose prime is chosen by `choose` from the retained samples."""
        obs = with_reuse(None)
        warm = prove_sample(obs, 'project.warm.noop')
        warm['cache_before']['prime_sample_id'] = choose(obs)
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('a cached sample naming a metric class instead of a sample',
             lambda: record_check(obs=reuse_naming(
                 lambda o: metric_identity(prove_sample(o, 'project.cold.prover')))),
             expect='does not retain')
    observed("a cached sample naming another command's prime",
             lambda: record_check(obs=reuse_naming(
                 lambda o: pick(o, "another command's cold sample",
                                lambda s: s['command_id'] == 'make.emit'
                                and s['scenario_id'].startswith('project.cold.'))['sample_id'])),
             expect='belonging to')
    observed('a cached sample naming a derived sample as its prime',
             lambda: record_check(obs=reuse_naming(
                 lambda o: first_derived(o)['sample_id'])),
             expect='names a DERIVED sample as its prime')

    def prime_after():
        """The prime moved to AFTER the sample that claims it: a cache cannot have been filled by a run
        that had not happened yet."""
        obs = with_reuse(None)
        warm, cold = prove_sample(obs, 'project.warm.noop'), prove_sample(obs, 'project.cold.prover')
        warm['cache_before']['prime_sample_id'] = cold['sample_id']
        obs['measurements'].remove(cold)
        obs['measurements'].append(cold)
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('a cached sample naming a prime that does not precede it',
             lambda: record_check(obs=prime_after()), expect='does not precede it')

    # A sample reusing only STABLE infrastructure needs no project prime: the preflight established it
    # outside every measured interval, so demanding one would refuse every honest warm sample.
    counts['total'] += 1
    stable_only = sample(cache_before={'authorities': {k: 'reused' for k in STABLE_CACHES},
                                       'cache_chain_id': 'x', 'prime_sample_id': None})
    try:
        record_check(obs=complete_observation(samples=[stable_only]))
    except ObservatoryError as exc:
        if 'R08' in str(exc):
            failures.append(f'stable-only cache reuse was made to require a project prime: {exc}')

    # The chain identity is LOGICAL. Claiming physical isolation would be a claim about a BuildKit store
    # that does not exist — every command shares one.
    counts['total'] += 1
    _prov, _ = sample_provenance([c for c in suite['commands'] if c['id'] == 'make.prove'][0],
                                 [s for s in suite['scenarios'] if s['id'] == 'project.cold.prover'][0], {})
    if 'cache_namespace' in _prov:
        failures.append('the cache chain is recorded as a namespace, which claims a physical isolation no '
                        'command has: they share one BuildKit store')
    if not _prov.get('cache_chain_id'):
        failures.append('a sample records no cache chain identity, so two causal chains cannot be told apart')

    observed('a registry that changed between validation and recording',
             lambda: record_check(suite_digest='9' * 64), expect='recording rule R02')
    observed('a dirty tree with RECORD', lambda: record_check(clean_before=False),
             expect='recording rule R03')
    observed('a dirty subject with RECORD',
             lambda: record_check(obs=complete_observation(subject={
                 'commit': 'a' * 40, 'tree': 'b' * 40, 'inventory_digest': 'c' * 64,
                 'dirty': True, 'source_view': 'working-tree'})),
             expect='recording rule R04')
    observed('a classified command that produced no sample',
             lambda: record_check(obs=observation()),
             expect='coverage on paper')
    observed('a canonical pair absent from the observation',
             lambda: record_check(obs=complete_observation(
                 samples=[s for s in complete_observation()['measurements']
                          if s['command_id'] != 'make.diet'])),
             expect='produced no sample')
    observed('an undeclared pair present in the observation',
             lambda: record_check(obs=complete_observation(
                 samples=complete_observation()['measurements']
                 + [sample(command_id='make.diet', scenario_id='project.cold.prover')])),
             expect='the registry never declared')
    observed('a required sample missing from one pair',
             lambda: record_check(obs=complete_observation(
                 samples=[s for s in complete_observation()['measurements']
                          if not (s['command_id'] == 'make.diet' and s['sample_index'] == 2)])),
             expect='wrong sample count')
    observed('an incomplete suite with RECORD',
             lambda: record_check(incomplete=['make.prove/project.cold.prover']),
             expect='recording rule R05')
    observed('a failed command with RECORD',
             lambda: record_check(obs=complete_observation(
                 samples=[sample(status='unexpected-exit', exit_code=2)],
                 derived={'summaries': summarise([sample(status='unexpected-exit', exit_code=2)])})),
             expect='recording rule R0')
    observed('an unrestored edit with RECORD', lambda: record_check(edits_restored=False),
             expect='recording rule R09')
    observed('a bundle that was not written first', lambda: record_check(bundle_written=False),
             expect='recording rule R12')

    # R13 and R14 read the repository itself, so they need a real one. Without this fixture every control
    # above fails at an earlier rule and those two are never exercised at all — a gap that would leave the
    # last two rules asserted rather than checked.
    import subprocess as _sp

    def in_clean_repo(mutate=None, stage=False):
        with _tempfile.TemporaryDirectory() as d:
            repo = Path(d) / 'repo'
            (repo / '.review').mkdir(parents=True)
            for cmd in (['init', '-q'], ['config', 'user.email', 'f@example.com'],
                        ['config', 'user.name', 'fixture']):
                _sp.run(['git', *cmd], cwd=repo, check=True, capture_output=True)
            (repo / OBSERVATION_REL).write_text('{}\n', encoding='utf-8')
            (repo / '.gitignore').write_text('.build-observatory/\n', encoding='utf-8')
            (repo / 'other.txt').write_text('one\n', encoding='utf-8')
            # The registry's build targets name real Dockerfile stages, and the expected derived-child
            # relation is derived from that graph, so the fixture repository needs the same Dockerfile.
            (repo / DOCKERFILE_REL).write_bytes((root / DOCKERFILE_REL).read_bytes())
            _sp.run(['git', 'add', '-A'], cwd=repo, check=True, capture_output=True)
            _sp.run(['git', 'commit', '-qm', 'fixture'], cwd=repo, check=True, capture_output=True)
            (repo / OBSERVATION_REL).write_text('{"recorded": true}\n', encoding='utf-8')
            if mutate:
                mutate(repo)
            if stage:
                _sp.run(['git', 'add', 'other.txt'], cwd=repo, check=True, capture_output=True)
            bundle = repo / RUNS_REL / 'fixture-run'
            bundle.mkdir(parents=True)
            obs_fixture = complete_observation()
            # the fixture must PRODUCE the evidence it claims, or R12 is satisfied by a fixture that
            # asserts digests for files nobody wrote
            (bundle / 'raw').mkdir(parents=True, exist_ok=True)
            for s in obs_fixture['measurements']:
                if s.get('derived_parent_id') or s.get('raw_log_sha256') is None:
                    continue
                name = raw_log_name(s['command_id'], s['scenario_id'], s['sample_index'], s.get('edit_id'))
                (bundle / 'raw' / f'{name}.log').write_bytes(b'fixture')
                s['raw_log_sha256'] = _sha256(b'fixture')
            obs_fixture['derived'] = {'summaries': summarise(obs_fixture['measurements'])}
            write_json(bundle / 'observation.json', obs_fixture)
            return check_record_eligible(repo, sel=Selection([], [], [], partial=False), suite=suite, suite_digest=digest,
                                         obs=obs_fixture, bundle=bundle, clean_before=True,
                                         edits_restored=True, incomplete=[])

    counts['total'] += 1
    try:
        rules = in_clean_repo()
        ids = [r.split('(')[0] for r in rules]
        if [r for r, _ in RECORDING_RULES] != ids:
            failures.append(f'a clean complete record-eligible run: satisfied {rules}, '
                            f'expected all {len(RECORDING_RULES)} rules in order')
        if not any(r.startswith('R07(vacuous') for r in rules):
            failures.append('R07 must declare itself vacuous while no command declares a nonzero '
                            'expected exit, rather than reporting a check it did not make')
    except ObservatoryError as exc:
        failures.append(f'a clean complete record-eligible run: expected success, failed with: {exc}')

    observed('recording which changes a second tracked file',
             lambda: in_clean_repo(mutate=lambda r: (r / 'other.txt').write_text('two\n', encoding='utf-8')),
             expect='recording rule R13')
    observed('a staged index with RECORD',
             lambda: in_clean_repo(mutate=lambda r: (r / 'other.txt').write_text('two\n', encoding='utf-8'),
                                   stage=True),
             expect='recording rule R1')

    def cmp_guard(*args, **kw):
        """`compare`, but a refusal is REPORTED rather than raised.

        An unguarded raise inside the self-test discards every failure collected before it, so a mutation
        that makes a fixture invalid aborted the run and the control that was supposed to catch it never
        printed. A control nobody can see failing is not evidence.
        """
        try:
            return compare(*args, **kw)
        except ObservatoryError as exc:
            failures.append(f'a self-test comparison was refused: {exc}')
            # The SAME members a real comparison returns, so a caller that renders the result reports the
            # refusal instead of dying on a missing key — which is the abort this helper exists to prevent.
            return {'metrics': [{'key': '-', 'classification': 'refused', 'reason': str(exc)}],
                    'counts': {'added': 0, 'removed': 0, 'refused': 1},
                    'suite_definitions': {'added': [], 'removed': []}}

    # ── comparison: the classification for a pair, and the reasons it declines to give one
    def verdict(label: str, base_obs: dict, cand_obs: dict, expect: str, key: str = 'make.fmt|project.warm.noop|-|-|selected|host-wrapper|wall_elapsed'):
        counts['total'] += 1
        result = cmp_guard(base_obs, cand_obs)
        row = next((m for m in result['metrics'] if m['key'] == key), None)
        if row is None:
            failures.append(f'{label}: no metric row for {key}')
        elif row['classification'] != expect:
            failures.append(f'{label}: classified {row["classification"]!r}, expected {expect!r} '
                            f'({row.get("reason")})')

    def timed(*walls) -> dict:
        s = [sample(sample_index=i, wall_ns=n) for i, n in enumerate(walls)]
        return observation(samples=s, derived={'summaries': summarise(s)})

    verdict('an equal median is unchanged', timed(1_000_000, 1_000_000), timed(1_000_000, 1_000_000),
            'unchanged')
    verdict('a clearly faster candidate is improved', timed(900, 1_000, 1_100), timed(100, 110, 120),
            'improved')
    verdict('a clearly slower candidate is regressed', timed(100, 110, 120), timed(900, 1_000, 1_100),
            'regressed')
    verdict('overlapping sample ranges refuse a verdict', timed(100, 200, 300), timed(150, 250, 350),
            'overlapping-range')
    verdict('a single sample reports a delta without a noise claim', timed(100), timed(900), 'regressed')

    counts['total'] += 1
    single = cmp_guard(timed(100), timed(900))['metrics'][0]
    if single.get('noise_basis') != 'single-sample':
        failures.append(f'a one-sample side must say so: noise_basis was {single.get("noise_basis")!r}')

    counts['total'] += 1
    other_host = observation()
    other_host['environment'] = {**other_host['environment'], 'host_class_fingerprint': 'e' * 64}
    row = cmp_guard(observation(), other_host)['metrics'][0]
    if row['classification'] != 'incomparable' or 'delta_percent' in row:
        failures.append('an incomparable host class must not be reported as an ordinary percentage delta')

    counts['total'] += 1
    # Resource scope is part of the metric identity now, so a changed scope is not the same metric at all.
    # That is stronger than `incomparable`: the two never meet in one row to be given a verdict.
    scoped = timed(100, 110, 120)
    scoped['measurements'] = [dict(s, resource_scope=SCOPE_BUILDKIT) for s in scoped['measurements']]
    scoped['derived'] = {'summaries': summarise(scoped['measurements'])}
    rows = cmp_guard(timed(100, 110, 120), scoped)['metrics']
    verdicts = {r['classification'] for r in rows}
    if verdicts - {'added', 'removed'}:
        failures.append(f'a changed resource scope must not produce a delta: {verdicts}')

    counts['total'] += 1
    changed_def = observation(commands={'make.fmt': 'aa' * 32})
    if cmp_guard(observation(), changed_def)['metrics'][0]['classification'] != 'incomparable':
        failures.append('a changed command definition must be incomparable')

    counts['total'] += 1
    # A metric present on one side and absent on the other — which is what added/removed MEANS. This used
    # to compare against a zero-sample observation, and a run that measured nothing is not a valid
    # observation to draw any verdict from, so the fixture was asking the comparator a question it should
    # refuse rather than answer.
    other = observation(samples=[sample(command_id='make.diet', sample_index=i, wall_ns=n)
                                 for i, n in enumerate((900_000, 1_000_000, 1_100_000))])
    added = cmp_guard(other, observation())
    removed = cmp_guard(observation(), other)
    if added['counts']['added'] != 1 or removed['counts']['removed'] != 1:
        failures.append(f'added/removed metrics were not reported: {added["counts"]}, {removed["counts"]}')

    counts['total'] += 1
    defs = cmp_guard(observation(commands={'make.fmt': 'f0' * 32, 'make.gone': 'a1' * 32}),
                   observation(commands={'make.fmt': 'f0' * 32, 'make.new': 'b2' * 32}))['suite_definitions']
    if defs['added'] != ['make.new'] or defs['removed'] != ['make.gone']:
        failures.append(f'a suite change must narrow an old observation, not void it: {defs}')

    counts['total'] += 1
    filtered = cmp_guard(observation(), observation(), only='make.nothing')
    if filtered['metrics']:
        failures.append('ONLY must be able to filter comparison output')

    # ── §5.4 isolations: every declared one is implemented and contains what it claims
    counts['total'] += 1
    declared_iso = {c.get('isolation') for c in suite['commands'] if c.get('isolation')}
    for kind in sorted(declared_iso - {'not-measured'}):
        with _tempfile.TemporaryDirectory() as d:
            fake = {'id': 'probe', 'isolation': kind}
            try:
                cwd, env = isolate(root, fake, Path(d) / 'iso')
            except ObservatoryError as exc:
                failures.append(f'isolation {kind!r} is declared but not implemented: {exc}')
                continue
            if kind == 'temporary-docker-config' and 'DOCKER_CONFIG' not in env:
                failures.append('a temporary Docker config must redirect DOCKER_CONFIG, or `buildx use` '
                                'switches the developer default')
            if kind == 'temporary-git-repo':
                if cwd is None or not (cwd / '.git').exists():
                    failures.append('a temporary Git repo must be standalone: git config in a LINKED '
                                    'worktree writes the config shared with the main checkout')
            # The release is exercised through a FAKE command runner, never the real Docker CLI.  These
            # controls have to pass on a machine with no Docker at all — the review environment is one, and
            # so is the pinned image they now run in — and a real `docker buildx rm` here would reach out and
            # remove a builder belonging to whoever ran the self-test.
            seen: list[tuple[list[str], str | None]] = []

            def runner(code: int):
                def _run(argv, **kwargs):
                    seen.append(([str(a) for a in argv], (kwargs.get('env') or {}).get('DOCKER_CONFIG')))
                    return _sp.CompletedProcess(argv, code, '', 'no builder found')
                return _run

            # A builder that could not be removed must be REPORTED rather than discarded — that discarded
            # failure orphaned a running container for two hours.
            leak = release_isolation(fake, Path(d) / 'iso', runner(1))
            if kind == 'temporary-docker-config':
                if not leak:
                    failures.append('a throwaway builder that could not be removed reported success, so a '
                                    'real leak would report success too')
                if not seen:
                    failures.append('releasing a temporary Docker config removed no builder at all')
                else:
                    argv, cfg = seen[-1]
                    if throwaway_builder(Path(d) / 'iso') not in argv:
                        failures.append(f'the release removed {argv} rather than this sample\'s own '
                                        'throwaway builder')
                    if cfg is None or 'docker-config' not in cfg:
                        failures.append('the release ran outside the private DOCKER_CONFIG that created the '
                                        'builder, which is how the original leak reported success')
            if kind != 'temporary-docker-config':
                if leak:
                    failures.append(f'isolation {kind!r} reported a builder leak it cannot have: {leak}')
                if seen:
                    failures.append(f'isolation {kind!r} ran an external command it has no builder for')

        # A release that SUCCEEDS must report no leak, or the leak signal carries no information.
        with _tempfile.TemporaryDirectory() as d:
            probe = {'id': 'probe', 'isolation': 'temporary-docker-config'}
            isolate(root, probe, Path(d) / 'iso')
            if release_isolation(probe, Path(d) / 'iso', lambda argv, **kw:
                                 _sp.CompletedProcess(argv, 0, '', '')) is not None:
                failures.append('a throwaway builder that was removed cleanly still reported a leak')
            if (Path(d) / 'iso').exists():
                failures.append('the release left its scratch directory behind')

    guarded('an isolation the runner does not implement',
            lambda w: isolate(root, {'id': 'probe', 'isolation': 'wishful-thinking'}, w),
            expect='declared but not implemented')

    counts['total'] += 1
    setup_cmds = [c for c in suite['commands'] if 'setup' in c['groups'] and c['measurement'] == 'direct']
    unisolated = [c['id'] for c in setup_cmds if not c.get('isolation')]
    if unisolated:
        failures.append(f'a safely measurable setup command must be measured, not cataloged: {unisolated}')

    # ── the repeated-work relation the contract requires as machine-readable fact
    counts['total'] += 1
    rw = repeated_work(suite, [sample(command_id='make.diet')])
    if not rw['repeated_execution']:
        failures.append('the repeated-work relation must record policies run by both make and the hook')
    by_policy = {r['policy']: r for r in rw['repeated_execution']}
    law = by_policy.get('source-comment-law')
    if not law or 'make.diet' not in law['make_commands'] or \
            'precommit.source-diet.check' not in law['hook_stages']:
        failures.append(f'the source-comment law runs in both places and must be recorded: {law}')
    if not by_policy.get('scoped-names'):
        failures.append('the scoped-name policy runs in both places and must be recorded')
    if not rw['containment']:
        failures.append('the repeated-work relation must record containment by stable ID')

    # ── §8 bundles: identity that cannot collide, evidence that must exist
    counts['total'] += 1
    subj = {'commit': 'a' * 40}
    ids = {run_id_for(subj, '2026-07-29T04:00:00.000000+00:00', 'd' * 64) for _ in range(50)}
    if len(ids) != 50:
        failures.append('two runs started in the same second must not share a run id')

    guarded('a bundle path that already exists',
            lambda w: (new_bundle(w, 'dup'), new_bundle(w, 'dup')),
            expect='refusing to overwrite')
    guarded('a fresh bundle path', lambda w: new_bundle(w, 'fresh'))

    def bundle_with(work: Path, obs_in: dict, write_logs=True, corrupt=False):
        b = work / 'b'
        (b / 'raw').mkdir(parents=True, exist_ok=True)
        for s in obs_in['measurements']:
            if s.get('derived_parent_id') or s.get('raw_log_sha256') is None:
                continue
            name = raw_log_name(s['command_id'], s['scenario_id'], s['sample_index'], s.get('edit_id'))
            if write_logs:
                (b / 'raw' / f'{name}.log').write_bytes(b'other' if corrupt else b'fixture')
            s['raw_log_sha256'] = _sha256(b'fixture')
        return verify_raw_logs(work, b, obs_in)

    guarded('a retained raw-log digest whose file is absent',
            lambda w: bundle_with(w, observation(), write_logs=False),
            expect='raw log(s) absent')
    guarded('a raw log that changed after it was measured',
            lambda w: bundle_with(w, observation(), corrupt=True),
            expect='changed since they were measured')
    guarded('every direct raw log present and matching', lambda w: bundle_with(w, observation()))

    counts['total'] += 1
    with _tempfile.TemporaryDirectory() as d:
        b = Path(d) / 'bundle'
        (b / 'raw').mkdir(parents=True)
        write = checkpointer(b, {'schema': SCHEMA, 'suite_digest': digest})
        if not (b / 'observation.json').is_file():
            failures.append('a bundle must be inspectable from creation, not only after the first sample')
        write([sample()], ['make.prove/project.cold.prover'])
        mid = json.loads((b / 'observation.json').read_text(encoding='utf-8'))
        if mid['derived'].get('status') != 'incomplete':
            failures.append('a checkpoint written mid-run must mark itself incomplete')
        if not mid['measurements']:
            failures.append('a checkpoint must retain the samples taken so far')

    # ── §7 comparison: validated before it concludes, and one selector model
    def without(member):
        """An observation with one sample member removed — the reviewer's own reproduction."""
        obs = observation()
        obs['measurements'][0].pop(member)
        return obs

    observed('a comparison against an observation with a sample member removed',
             lambda: compare(without('cache_before'), observation()),
             expect='does not validate, so no verdict can rest on it')
    observed('a comparison against an observation with no run identity',
             lambda: compare(observation(run_id=None), observation()),
             expect='does not validate, so no verdict can rest on it')
    observed('a comparison against a tampered stored summary',
             lambda: compare(observation(derived={'summaries': {'x|y|-|-|host-wrapper': {
                 'samples': 1, 'median_ns': 1, 'min_ns': 1, 'max_ns': 1}}}), observation()),
             expect='do not equal recomputation from the retained samples')

    counts['total'] += 1
    two_scopes = [sample(sample_index=0), dict(sample(sample_index=1), resource_scope=SCOPE_BUILDKIT)]
    if len(summarise(two_scopes)) != 2:
        failures.append('one metric must measure one resource scope: two scopes must be two metrics')

    counts['total'] += 1
    grp = cmp_guard(observation(), observation(), only='policy', suite=suite)
    if grp['metrics'] and False:
        pass
    try:
        compare(observation(), observation(), only='no.such.name', suite=suite)
        failures.append('comparison must reject an unknown selector, as a run does')
    except ObservatoryError as exc:
        if 'unknown ONLY name' not in str(exc):
            failures.append(f'comparison rejected an unknown selector for the wrong reason: {exc}')

    counts['total'] += 1
    base_defs = {**observation()['definitions'], 'scenarios': {'project.warm.noop': 'aa' * 32}}
    cand_defs = {**observation()['definitions'], 'scenarios': {'project.warm.noop': 'bb' * 32}}
    changed_scn = observation(definitions=base_defs)
    row = cmp_guard(changed_scn, observation(definitions=cand_defs))['metrics'][0]
    if row['classification'] != 'incomparable' or 'meaning of' not in row['reason']:
        failures.append(f'a changed scenario meaning must be incomparable: {row}')

    counts['total'] += 1
    slow = observation()
    slow['environment'] = {**slow['environment'],
                           'concurrency': {'make_jobs': 4, 'make_jobs_source': '-j4'}}
    row = cmp_guard(slow, observation())['metrics'][0]
    if row['classification'] != 'incomparable' or 'concurrency' not in row['reason']:
        failures.append(f'a changed effective concurrency must be incomparable: {row}')

    observed('an observation path that does not exist',
             lambda: load_observation(root, '/nonexistent/observation.json'),
             expect='no readable observation')
    observed('a Git ref with no tracked observation',
             lambda: load_observation(root, '0000000000000000000000000000000000000000'),
             expect='no readable observation')

    counts['total'] += 1
    with _tempfile.TemporaryDirectory() as d:
        p = Path(d) / 'observation.json'
        write_json(p, observation())
        loaded, where = load_observation(root, str(p))
        if loaded['schema'] != SCHEMA or where != str(p):
            failures.append('a local path comparison input did not load')

    counts['total'] += 1
    # A REFUSED comparison is not rendered: the renderer reads members a refusal has no values for, and
    # the assertion below reports the empty text rather than the run dying inside the formatter.
    _cmp = cmp_guard(timed(100, 110, 120), timed(900, 1_000, 1_100))
    text = '' if _cmp['counts'].get('refused') else render_comparison(_cmp)
    if 'regressed' not in text or 'n=3/3' not in text:
        failures.append('the plain comparison must show the classification and the sample counts')

    # ── module graph: adjacency, rebuild sets and the critical path, over a small exact fixture
    DEP = ('A.vo A.glob A.v.beautified: A.v /opt/rocq/rocqworker\n'
           'B.vo B.glob: B.v _build/default/A.vo\n'
           'C.vo: C.v _build/default/B.vo\n'
           'D.vo: D.v _build/default/A.vo\n')
    WALL = {'A': 1_000, 'B': 2_000, 'C': 4_000, 'D': 8_000}

    counts['total'] += 1
    try:
        g = parse_module_graph(DEP, WALL)
        checks = {
            'adjacency reads .vo edges only': g['adjacency'] == {'A': [], 'B': ['A'], 'C': ['B'],
                                                                 'D': ['A']},
            'downstream is transitive': g['downstream']['A'] == ['B', 'C', 'D'],
            'a leaf has no downstream': g['downstream']['C'] == [],
            'downstream cost sums the set': g['downstream_cost_ns']['A'] == 1_000 + 2_000 + 4_000 + 8_000,
            'the critical path is the costliest chain': g['critical_path']['modules'] == ['A', 'D'],
            'the critical path total is its sum': g['critical_path']['total_ns'] == 9_000,
        }
        for why, ok_ in checks.items():
            if not ok_:
                failures.append(f'the module graph: {why} — got {json.dumps(g["adjacency"])}, '
                                f'downstream {json.dumps(g["downstream"])}, cp {json.dumps(g["critical_path"])}')
    except ObservatoryError as exc:
        failures.append(f'the module graph: expected success, failed with: {exc}')

    observed('a dependency output with no module edges',
             lambda: parse_module_graph('A.vo: A.v\nB.vo: B.v\n', {'A': 1, 'B': 1}),
             expect='no module-to-module edges')
    observed('a dependency cycle',
             lambda: parse_module_graph('A.vo: A.v _build/default/B.vo\nB.vo: B.v _build/default/A.vo\n',
                                        {'A': 1, 'B': 1}),
             expect='has a cycle')

    counts['total'] += 1
    impact = rebuild_impact(parse_module_graph(DEP, WALL))
    if [f['module'] for f in impact] != ['A', 'D', 'B', 'C']:
        failures.append(f'rebuild impact must rank EVERY module by downstream cost: '
                        f'{[f["module"] for f in impact]}')
    if any('threshold' in k for f in impact for k in f):
        failures.append('rebuild impact must not carry a cutoff; ranking is the report')

    counts['total'] += 1
    hist = {'views': {'excluding_campaign': {'edit_count_by_file': {'A.v': 3, 'D.v': 1}}}}
    w = weighted_rebuild_cost(hist, parse_module_graph(DEP, WALL))
    top = w['rows'][0]
    if top['module'] != 'A' or top['weighted_ns'] != 3 * 15_000:
        failures.append(f'weighted rebuild cost must multiply frequency by downstream cost: {top}')
    if 'edit_frequency' not in top or 'downstream_rebuild_ns' not in top:
        failures.append('weighted rebuild cost must retain BOTH inputs beside the product')

    counts['total'] += 1
    if weighted_rebuild_cost(hist, None)['basis'] != 'unavailable':
        failures.append('with no module graph, the weighting must say it is unavailable, not report zeros')

    counts['total'] += 1
    for view in ('all', 'implementation', 'excluding_campaign'):
        if view not in HISTORY_VIEWS:
            failures.append(f'the history views must be declared once: {view} is missing')

    # ── a mutating command run in the source tree
    counts['total'] += 1
    writers = [c for c in suite['commands'] if c['side_effect'] != 'none' and c['measurement'] == 'direct']
    in_place = [c['id'] for c in writers if not c.get('isolation')]
    if in_place:
        failures.append(f'a mutating command run in the source tree: {in_place} declare a side effect but '
                        f'no isolation, so measuring them would change the thing being measured')

    counts['total'] += 1
    unknown_iso = [c['id'] for c in suite['commands'] if c.get('isolation') not in
                   (None, *ISOLATIONS)]
    if unknown_iso:
        failures.append(f'these commands declare an isolation the runner does not implement: {unknown_iso}')

    counts['total'] += 1
    if any(c.get('isolation') and c['side_effect'] == 'none' for c in suite['commands']):
        failures.append('a command declaring an isolation must say what effect it is containing')

    # ── the cache cut: a declared claim checked against what BuildKit actually did
    def cut_sample(stages, scenario_id='project.cold.prover', **over):
        s = sample(scenario_id=scenario_id, cache_observation={'stages': stages})
        s['cache_cut'] = {'stable_through': 'rocq-base', 'invalidated_roots': ['prover'],
                          'registry_pulls_included': False, 'builder_bootstrap_included': False, **over}
        return s

    cold_scn = {'id': 'project.cold.prover', 'canonical': True}

    # ── §7 a cut owns an exact ROOT SET, and the set must explain every project stage that rebuilt
    _g = docker_stage_graph(root)
    compound = {'id': 'project.cold.audit-fresh', 'canonical': True}

    def two_root_sample(stages):
        s = sample(scenario_id='project.cold.audit-fresh', cache_observation={'stages': stages})
        s['cache_cut'] = {'stable_through': 'rocq-base', 'invalidated_roots': ['go-e2e', 'prover'],
                          'registry_pulls_included': False, 'builder_bootstrap_included': False}
        return s

    observed('a compound cut missing one of its declared roots',
             lambda: check_cut_observed(two_root_sample({'prover': 'rebuilt', 'go-e2e': 'hit',
                                                         'rocq-base': 'hit'}), compound, suite, _g),
             expect="root 'go-e2e' was hit, not rebuilt")
    observed('an undeclared independent root that rebuilt alongside the declared one',
             lambda: check_cut_observed(cut_sample({'prover': 'rebuilt', 'go-e2e': 'rebuilt',
                                                    'rocq-base': 'hit'}), cold_scn, suite, _g),
             expect='neither a declared invalidation root')

    counts['total'] += 1
    emit_scn = {'id': 'project.cold.emit', 'canonical': True}
    emit_sample = sample(scenario_id='project.cold.emit',
                         cache_observation={'stages': {'emit': 'rebuilt', 'generated-module': 'rebuilt',
                                                       'rocq-base': 'hit'}})
    emit_sample['cache_cut'] = {'stable_through': 'rocq-base', 'invalidated_roots': ['emit'],
                                'registry_pulls_included': False, 'builder_bootstrap_included': False}
    try:
        # `generated-module` COPYs from `emit`, so its rebuild is EXPLAINED by the declared root and must be
        # accepted; refusing it would make every real cold sample unrecordable. (`prover` has no descendants
        # at all — it and `emit` are siblings from `rocq-base` — which is why the fixture uses `emit`.)
        check_cut_observed(emit_sample, emit_scn, suite, _g)
        check_cut_observed(two_root_sample({'prover': 'rebuilt', 'go-e2e': 'rebuilt', 'rocq-base': 'hit'}),
                           compound, suite, _g)
    except ObservatoryError as exc:
        failures.append(f'a rebuild downstream of a declared root was refused: {exc}')

    # A changed root set changes the scenario definition, so two observations across it are incomparable
    # rather than comparable — the same command measured under a different cut is a different question.
    counts['total'] += 1
    _base_suite = {**suite, 'scenarios': [{**s, 'cache_cut': {**s['cache_cut'],
                                                              'invalidated_roots': ['prover']}}
                                          if s['id'] == 'project.cold.audit-fresh' else s
                                          for s in suite['scenarios']]}
    if definition_fingerprints(_base_suite)['scenarios']['project.cold.audit-fresh'] == \
            definition_fingerprints(suite)['scenarios']['project.cold.audit-fresh']:
        failures.append('a changed invalidation root set left the scenario fingerprint unchanged, so two '
                        'observations taken under different cuts would compare as if they matched')

    # ── §5 the source view owns identity AND materialisation, and distinguishes what bytes alone cannot
    counts['total'] += 1
    with _tempfile.TemporaryDirectory() as d:
        w = Path(d) / 'r'
        w.mkdir()
        _sp.run(['git', 'init', '-q'], cwd=w, check=True, capture_output=True)
        for k, v in (('user.email', 'o@example.invalid'), ('user.name', 'observatory')):
            _sp.run(['git', 'config', k, v], cwd=w, check=True, capture_output=True)
        (w / 'kept.v').write_text('Definition x := 1.\n', encoding='utf-8')
        (w / 'gone.v').write_text('Definition y := 2.\n', encoding='utf-8')
        (w / 'tool.sh').write_text('#!/bin/sh\n', encoding='utf-8')
        _sp.run(['git', 'add', '-A'], cwd=w, check=True, capture_output=True)
        _sp.run(['git', 'commit', '-qm', 'base'], cwd=w, check=True, capture_output=True)
        base = source_view(w, 'working-tree')['id']

        (w / 'tool.sh').chmod(0o755)
        if source_view(w, 'working-tree')['id'] == base:
            failures.append('a mode-only change left the source view identical, so an executable bit could '
                            'change under one identity')
        (w / 'tool.sh').chmod(0o644)

        target = w / 'target.txt'
        target.write_text('payload\n', encoding='utf-8')
        (w / 'link').symlink_to('target.txt')
        with_link = source_view(w, 'working-tree')
        (w / 'link').unlink()
        (w / 'link').write_text('payload\n', encoding='utf-8')   # the SAME bytes, as a regular file
        if source_view(w, 'working-tree')['id'] == with_link['id']:
            failures.append('a symlink and a regular file holding its target\'s bytes shared one source '
                            'view identity, so the link was followed rather than recorded')
        (w / 'link').unlink()
        target.unlink()

        _sp.run(['git', 'add', '-A'], cwd=w, check=True, capture_output=True)
        staged = source_view(w, 'staged-index')['id']
        (w / 'kept.v').write_text('Definition x := 999.\n', encoding='utf-8')
        if source_view(w, 'staged-index')['id'] != staged:
            failures.append('an unstaged working-tree edit changed the STAGED index identity')
        if source_view(w, 'working-tree')['id'] == staged:
            failures.append('the staged index and a differing working tree shared one identity, so a '
                            'pre-commit sample could carry a digest for a tree it never saw')

        # A command declaring `staged-index-export` must be identified by the STAGED index it will export,
        # not by the working tree it never sees.
        hook_cmd = {'source_view': 'staged-index-export'}
        if declared_source_digest(w, hook_cmd) != staged:
            failures.append('a staged-index-export command was identified by something other than the '
                            'staged index it exports')
        if declared_source_digest(w, {'source_view': 'working-tree'}) == staged:
            failures.append('a working-tree command and a staged-index-export command were given the same '
                            'identity for two different trees')

        (w / 'gone.v').unlink()
        view = source_view(w, 'working-tree')
        if 'gone.v' not in view['deleted']:
            failures.append('a tracked file deleted on disk is not retained as an absence in the view')

    # ── §8 an incremental sample must exhibit the effect its edit was chosen for
    _inputs = docker_context_inputs(root)
    counts['total'] += 1
    for path, want in (('Float.v', True), ('Compilable.v', True), ('Emit.v', True),
                       ('plugin/sink.ml', True), ('gate/Assumptions.v', True),
                       ('tools/source-diet.py', False), ('ARCHITECTURE.md', False),
                       ('.review/NEXT_STEPS.md', False)):
        if is_build_input(path, _inputs) != want:
            failures.append(f'{path!r} was classified {"a" if not want else "not a"} Docker build input, '
                            f'which the Dockerfile COPY set contradicts')

    def edit_sample(edit_id, path, stages, cmd='make.prove'):
        s = sample(command_id=cmd, scenario_id=f'project.incremental.{edit_id}', edit_id=f'edit.{edit_id}',
                   cache_observation={'stages': stages})
        return s, {'id': f'edit.{edit_id}', 'path': path}, \
            [c for c in suite['commands'] if c['id'] == cmd][0]

    observed('a .v edit whose stages were all cache hits',
             lambda: check_edit_effect(*edit_sample('foundation.float', 'Float.v',
                                                    {'prover': 'hit', 'rocq-base': 'hit'}), _inputs),
             expect='reports the cost of a rebuild that never ran')
    observed('a tool edit claiming a project rebuild',
             lambda: check_edit_effect(*edit_sample('tool.source-diet', 'tools/source-diet.py',
                                                    {'prover': 'rebuilt'}), _inputs),
             expect='attributes work to the wrong cause')
    observed('a documentation edit claiming a project rebuild',
             lambda: check_edit_effect(*edit_sample('doc.architecture', 'ARCHITECTURE.md',
                                                    {'prover': 'rebuilt'}), _inputs),
             expect='attributes work to the wrong cause')

    counts['total'] += 1
    for label, args in (('a .v edit that rebuilt its stage',
                         edit_sample('foundation.float', 'Float.v',
                                     {'prover': 'rebuilt', 'rocq-base': 'hit'})),
                        ('a tool edit that rebuilt nothing',
                         edit_sample('tool.source-diet', 'tools/source-diet.py',
                                     {'prover': 'hit', 'rocq-base': 'hit'})),
                        ('a documentation edit that rebuilt nothing',
                         edit_sample('doc.architecture', 'ARCHITECTURE.md',
                                     {'prover': 'hit', 'rocq-base': 'hit'}))):
        try:
            check_edit_effect(*args, _inputs)
        except ObservatoryError as exc:
            failures.append(f'{label} was refused: {exc}')

    # Every registered edit must be classifiable, or a later edit could be added whose intended effect
    # nothing checks.
    counts['total'] += 1
    for e in suite.get('edits', []):
        scen = [s for s in suite['scenarios'] if s.get('edit') == e['id']]
        if not scen:
            failures.append(f'edit {e["id"]} belongs to no scenario, so its effect is never observed')

    observed('a cold sample whose invalidation root stayed cached',
             lambda: check_cut_observed(cut_sample({'prover': 'hit', 'rocq-base': 'hit'}), cold_scn, suite),
             expect='not rebuilt; a cold sample whose root stayed cached is not a cold sample')
    observed('a sample whose declared stable ancestor rebuilt',
             lambda: check_cut_observed(cut_sample({'prover': 'rebuilt', 'rocq-base': 'rebuilt'}),
                                        cold_scn, suite),
             expect='declared stable ancestor')
    observed('a canonical sample that pulled from the registry',
             lambda: check_cut_observed(cut_sample({'prover': 'rebuilt'}, registry_pulls_included=True),
                                        cold_scn, suite),
             expect='machine setup rather than canonical project evidence')
    observed('a canonical sample that bootstrapped the builder',
             lambda: check_cut_observed(cut_sample({'prover': 'rebuilt'},
                                                   builder_bootstrap_included=True), cold_scn, suite),
             expect='bootstrapped inside the measured')
    observed('a cold sample whose root rebuilt and whose ancestors held',
             lambda: check_cut_observed(cut_sample({'prover': 'rebuilt', 'rocq-base': 'hit'}),
                                        cold_scn, suite))

    counts['total'] += 1
    before = {'authorities': {'buildkit_project_layers': 'empty', 'dune_build': 'empty'}}
    after_rebuilt = observe_cache_after(before, {'prover': 'rebuilt'})
    after_hit = observe_cache_after(before, {'prover': 'hit'})
    if after_rebuilt['authorities'] == before['authorities']:
        failures.append('cache_after must be observed, not copied: a rebuild left the state unchanged')
    if after_hit['authorities'] != before['authorities']:
        failures.append('cache_after must be observed: a pure cache hit changed the recorded state')

    counts['total'] += 1
    from_only = observe_stages('#1 [rocq-base 1/5] FROM docker.io/library/debian:12-slim\n#1 DONE 0.1s\n'
                               '#2 [rocq-base 2/5] RUN apt-get update\n#2 CACHED\n')
    if from_only.get('rocq-base') != 'hit':
        failures.append(f'a FROM step must not count as a rebuilt stage: rocq-base read {from_only}')

    counts['total'] += 1
    ran = observe_stages('#1 [prover 1/2] FROM x\n#1 DONE 0.1s\n'
                         '#2 [prover 2/2] RUN dune build\n#2 DONE 61.0s\n')
    if ran.get('prover') != 'rebuilt':
        failures.append(f'an executed non-FROM step means the stage rebuilt: prover read {ran}')

    counts['total'] += 1
    if pulled_from_registry('#3 resolve docker.io/library/debian:12-slim@sha256:abc 0.1s done\n'):
        failures.append('local reference resolution is not a registry pull')
    if not pulled_from_registry('#3 extracting sha256:abcdef 1.2s\n'):
        failures.append('an extracted layer IS a registry pull and must be detected')

    # ── the observation SHAPE a real run assembles: direct samples, analysis samples and derived
    #    children together. Assembly failing at the end of a multi-hour suite is the expensive way to learn.
    counts['total'] += 1
    direct = sample(command_id='make.prove', scenario_id='project.cached.fresh')
    ana = analysis_sample('analysis.rocq-modules', scen_of(suite, 'project.cached.fresh'),
                          'selected', 5_000, {}, [])
    kids = derive_child_samples(direct, [{'id': 'docker.prover', 'aggregate_step_ns': 900,
                                          'source': 'buildkit-progress'}], {'docker.prover'})
    kids += derive_child_samples(ana, [{'id': 'analysis.dune-graph', 'wall_ns': None, 'untimed': True,
                                        'source': 'same-build'}], {'analysis.dune-graph'})
    mixed = [direct, ana, *kids]
    # Stamped exactly as `emit` stamps them, and in emission order, because that is the shape a real run
    # assembles: the constructors leave `sample_id` unset and one place fills it in.
    for _s in mixed:
        _s['sample_id'] = sample_id_for('run-fixture', _s)
    for _kid, _parent in ((kids[0], direct), (kids[1], ana)):
        _kid['parent_sample_id'] = _parent['sample_id']
    shaped = observation(samples=mixed, derived={'summaries': summarise(mixed)})
    try:
        validate_observation(shaped, digest)
    except ObservatoryError as exc:
        failures.append(f'the observation shape a real run assembles must validate: {exc}')

    counts['total'] += 1
    scopes = {s['command_id']: s['resource_scope'] for s in mixed}
    if scopes.get('docker.prover') != SCOPE_BUILDKIT:
        failures.append(f'a BuildKit-derived child must say so: {scopes}')
    if scopes.get('analysis.dune-graph') != SCOPE_UNAVAILABLE:
        failures.append('a child produced by the same build has no resource figures of its own')

    # Two runners, one partition: every direct command belongs to exactly one, and nothing else is executed.
    # An analysis command reached the shell runner and it tried to exec a binary named `observatory`, which
    # cost the chain its prime and every cached sample that depended on it.
    counts['total'] += 1
    direct = [c for c in suite['commands'] if c['measurement'] == 'direct']
    shell = {c['id'] for c in direct if runner_for(c) == 'shell'}
    analysis = {c['id'] for c in direct if runner_for(c) == 'analysis'}
    if shell & analysis:
        failures.append(f'commands claimed by both runners: {sorted(shell & analysis)}')
    if shell | analysis != {c['id'] for c in direct}:
        missing = {c['id'] for c in direct} - shell - analysis
        failures.append(f'direct commands no runner owns: {sorted(missing)}')
    spawned = [c['id'] for c in direct if runner_for(c) == 'shell'
               and c['execution'] and c['execution'][0] not in ('make', 'sh', 'env')]
    if spawned:
        failures.append(f'the shell runner would try to exec these non-programs: {spawned}')

    # ── every registry execution must actually be runnable, and a bad one must be diagnosable
    counts['total'] += 1
    unrunnable = [c['id'] for c in suite['commands']
                  if c['measurement'] == 'direct'
                  and runner_for(c) == 'shell'
                  and c['execution'] and c['execution'][0] not in ('make', 'sh', 'env')]
    if unrunnable:
        failures.append(f'these direct commands name an execution nothing can run: {unrunnable}')

    observed('a command whose execution cannot be run',
             lambda: run_sample(root, {'id': 'bogus', 'kind': 'make-target',
                                       'execution': ['no-such-binary-xyz'], 'expected_exit': 0},
                                scen_of(suite, 'project.warm.noop'), 0, 'selected', Path('/tmp'), {}),
             expect='an unrunnable command is a defect in the registry')

    counts['total'] += 1
    asample = analysis_sample('analysis.history', scen_of(suite, 'project.warm.noop'),
                              'selected', 1234, {}, [])
    absent = [f for f in SAMPLE_FIELDS if f not in asample]
    if absent:
        failures.append(f'an analysis sample must carry every sample field, missing {absent}')
    elif asample['resource_scope'] != SCOPE_UNAVAILABLE or asample['max_rss_bytes'] is not None:
        failures.append("an analysis sample must not report the observatory's own memory as the analysis's")

    # ── derived stage events: the instrumentation must be switched on, and must produce child samples
    counts['total'] += 1
    hook_cmd = next(c for c in suite['commands'] if c['kind'] == 'precommit-full')
    env = instrumentation_env(hook_cmd, Path('/tmp/x.anchors'))
    if 'FIDO_OBSERVE' not in env:
        failures.append('the hook must be measured with its anchors switched on, or they are dead weight')
    make_cmd = next(c for c in suite['commands'] if c['kind'] == 'make-target')
    if instrumentation_env(make_cmd, Path('/tmp/x')).get('BUILDKIT_PROGRESS') != 'plain':
        failures.append('a make target must be measured with structured BuildKit progress')

    counts['total'] += 1
    events = parse_anchor_log('begin a 1000\nbegin b 1100\nend b 1400\nend a 2000\n')
    if {e['id']: e['wall_ns'] for e in events} != {'b': 300, 'a': 1000}:
        failures.append(f'nested anchors must each get their own duration: {events}')

    # A cold sample with no stage evidence at all used to pass: nothing observed, nothing to contradict.
    counts['total'] += 1
    cold_scen = next(s for s in suite['scenarios'] if s['id'] == 'project.cold.prover')
    blind = {'command_id': 'make.prove', 'cache_cut': dict(cold_scen['cache_cut']),
             'cache_observation': {'stages': {}}}
    try:
        check_cut_observed(blind, cold_scen, suite)
        failures.append('a cold sample with no observed stage state was accepted, so a command that hides '
                        'its build output is cold by default')
    except ObservatoryError:
        pass

    observed('a hook anchor with no timestamp',
             lambda: parse_anchor_log('begin a 1000\nend a \n'),
             expect='must carry a monotonic timestamp')
    observed('a hook anchor that never ends',
             lambda: parse_anchor_log('begin a 1000\nbegin b 1100\nend b 1400\n'),
             expect='began and never ended')

    observed('a hook anchor whose clock went backwards',
             lambda: parse_anchor_log('begin a 2000\nend a 1000\n'),
             expect='ended before it began')

    counts['total'] += 1
    stages = parse_buildkit_progress('#5 [prover 5/5] RUN x\n#5 DONE 2.5s\n'
                                     '#6 [internal] load metadata\n#6 DONE 9.9s\n'
                                     '#7 [emit 1/7] COPY y\n#7 CACHED\n')
    by_id = {e['id']: e for e in stages}
    if 'docker.internal' in by_id:
        failures.append('BuildKit internal steps are not Docker stages of this project')
    if by_id.get('docker.prover', {}).get('aggregate_step_ns') != 2_500_000_000:
        failures.append(f'a stage duration must come from its own DONE line: {stages}')
    if by_id.get('docker.emit', {}).get('cached_steps') != 1:
        failures.append(f'a cached step must be recorded as cached, not as zero time: {stages}')

    counts['total'] += 1
    parent = {'command_id': 'make.e2e', 'scenario_id': 'project.cached.fresh', 'sample_index': 0,
              'selected_or_support': 'selected', 'wall_ns': 99, 'max_rss_bytes': 5}
    kids = derive_child_samples(parent, [{'id': 'docker.go-e2e', 'aggregate_step_ns': 42,
                                          'source': 'buildkit-progress'},
                                         {'id': 'docker.unknown', 'aggregate_step_ns': 7,
                                          'source': 'buildkit-progress'}],
                                {'docker.go-e2e'})
    if [k['command_id'] for k in kids] != ['docker.go-e2e']:
        failures.append(f'only REGISTERED derived commands become child samples: {kids}')
    elif kids[0]['max_rss_bytes'] is not None or kids[0]['resource_scope'] != SCOPE_BUILDKIT:
        failures.append("a derived child must not inherit its parent's host RSS as its own")
    elif kids[0]['derived_parent_id'] != 'make.e2e':
        failures.append('a derived child must name the parent it came from')

    # ── scenario ordering and unusable comparison inputs
    counts['total'] += 1
    order = scenario_order(suite, ['project.warm.noop', 'project.cold.prover', 'project.cached.fresh'])
    if order.index('project.cold.prover') > order.index('project.cached.fresh') or \
            order.index('project.cached.fresh') > order.index('project.warm.noop'):
        failures.append(f'scenarios must run in prime order, got {order}')

    counts['total'] += 1
    if scenario_order(suite, ['project.cold.prover']) != ['project.cold.prover']:
        failures.append('a scenario with no prime step must order to itself alone')

    observed('a scenario belonging to no chain family',
             lambda: scenario_order({'scenarios': [{'id': 'made.up'}]}, ['made.up']),
             expect='belongs to no known family')

    observed('comparing against a pending observation',
             lambda: compare({'state': 'pending'}, observation()),
             expect='still pending')
    # A catalog-only command is never measured by classification, and an observation that lists it as
    # never-measured is complete. Without this exemption every complete observation was unrecordable.
    counts['total'] += 1
    try:
        validate_observation(observation(selection={
            'partial': False, 'commands_selected': ['make.fmt', 'make.observe'], 'commands_support': [],
            'scenarios': ['project.warm.noop'], 'scenarios_added_as_support': [],
            'commands_with_no_scenario_here': [], 'commands_never_measured': ['make.observe']}), digest)
    except ObservatoryError as exc:
        failures.append(f'a catalog-only command listed as never measured was refused: {exc}')

    counts['total'] += 1
    try:
        validate_observation(observation(selection={
            'partial': True, 'commands_selected': ['make.fmt', 'make.builder'], 'commands_support': [],
            'scenarios': ['project.warm.noop'], 'scenarios_added_as_support': [],
            'commands_with_no_scenario_here': [], 'commands_never_measured': []}), digest)
        failures.append('a selected command with no sample and no reason was accepted')
    except ObservatoryError:
        pass

    # A command that runs several buildx invocations concatenates their logs, and step numbers restart at
    # #1 each time. Resolving a step number against the whole file attributed one build's ordinal to another
    # build's stage and reported a stable ancestor as rebuilt.
    counts['total'] += 1
    # The second invocation reuses #5 for an INTERNAL step, which carries no stage name. Without splitting,
    # #5 still resolves to the first invocation's stage and its DONE marks that stage rebuilt.
    two_invocations = (
        '#0 building with "b" instance using docker-container driver\n'
        '#5 [rocq-base 2/5] RUN apt-get update\n'
        '#5 CACHED\n'
        '#0 building with "b" instance using docker-container driver\n'
        '#5 [internal] load build context\n'
        '#5 DONE 12.0s\n'
        '#6 [go-e2e 9/9] RUN go build ./...\n'
        '#6 DONE 12.0s\n')
    stages = observe_stages(two_invocations)
    if stages.get('rocq-base') != 'hit':
        failures.append(f"a later invocation's step number was attributed to an earlier stage: {stages}")
    if stages.get('go-e2e') != 'rebuilt':
        failures.append(f'the stage that actually ran was not reported rebuilt: {stages}')

    counts['total'] += 1
    unsplit = ('#5 [rocq-base 2/5] RUN apt-get update\n#5 CACHED\n'
               '#5 [go-e2e 9/9] RUN go build ./...\n#5 DONE 12.0s\n')
    try:
        observe_stages(unsplit)
        failures.append('concatenated builds with no invocation marker were read as one, so every stage '
                        'state would be attributed to the wrong stage')
    except ObservatoryError:
        pass

    # Recorded AND read: the range is derived from the retained samples, so a reader sees the condition and
    # the validator can recompute it. No rule rejects a sample for load — that would be an invented cut-off.
    counts['total'] += 1
    loaded = observed_load([{'host_load': {'before': 0.5, 'after': 2.5}},
                            {'host_load': {'before': 1.5, 'after': None}}])
    if (loaded['samples'], loaded['min'], loaded['max']) != (3, 0.5, 2.5):
        failures.append(f'the observed host-load range was not derived from the samples: {loaded}')
    if observed_load([{'host_load': {'before': None, 'after': None}}])['unavailable'] is not True:
        failures.append('a run whose kernel published no load must say unavailable, not invent a range')

    # Both detectors read BuildKit steps. The word `bootstrap` appears in this tool's own control names,
    # which the pre-commit hook prints, and a log carrying arbitrary tool output must not be read for
    # English words that happen to name a Docker action.
    counts['total'] += 1
    innocent = ('  detected  a bootstrap sample building the builder it times  (tools/x.py)\n'
                '  detected  the empty builder a bootstrap claim requires\n'
                '#5 [prover 2/5] COPY *.v ./\n#5 CACHED\n'
                '#9 resolve docker.io/library/debian:12-slim@sha256:abc 0.1s done\n')
    if bootstrapped_builder(innocent):
        failures.append('a bootstrap was reported from log text that only NAMES bootstrapping')
    if pulled_from_registry(innocent):
        failures.append('a registry pull was reported from local reference resolution')
    real_boot = '#1 [internal] booting buildkit\n#1 creating container buildx_buildkit_fido-throwaway-x\n'
    if not bootstrapped_builder(real_boot):
        failures.append('a builder that was actually booted went unreported')
    if not pulled_from_registry('#1 pulling image moby/buildkit:buildx-stable-1\n'):
        failures.append('an image pulled inside the interval went unreported')

    # The isolation announces a throwaway builder, the invocation must USE it, and the release removes it.
    # When the invocation used the observatory's builder instead, `make builder` found one already there and
    # a bootstrap sample timed `buildx inspect`.
    counts['total'] += 1
    with _tempfile.TemporaryDirectory() as d:
        scratch = Path(d) / 'iso'
        scratch.mkdir()
        name = throwaway_builder(scratch)
        builder_cmd = [c for c in suite['commands'] if c['id'] == 'make.builder'][0]
        boot = [s for s in suite['scenarios'] if s['id'] == 'environment.bootstrap'][0]
        argv = materialise_execution(builder_cmd, boot, name)
        if f'BUILDER={name}' not in argv:
            failures.append(f'a bootstrap invocation did not use the builder it creates: {argv}')
        if f'BUILDER={OBSERVATORY_BUILDER}' in argv:
            failures.append('a bootstrap invocation reused the observatory builder, so it times an inspect')
        _, env = isolate(Path(d), builder_cmd, scratch)
        if env.get('FIDO_OBSERVATORY_THROWAWAY_BUILDER') != name:
            failures.append('the isolation and the invocation named different throwaway builders')

    # One provenance builder for both runners, exercised directly. Three fixes today landed on the shell
    # runner and left the analysis runner behind, each time because each loop built its own dict.
    counts['total'] += 1
    _cold = [s for s in suite['scenarios'] if s['id'] == 'project.cold.module-graph'][0]
    _warm2 = [s for s in suite['scenarios'] if s['id'] == 'project.warm.noop'][0]
    _ana = [c for c in suite['commands'] if c['id'] == 'analysis.rocq-modules'][0]
    prov, skip = sample_provenance(_ana, _cold, {})
    if skip or prov['prime_sample_id'] is not None:
        failures.append(f'a cold analysis sample must need no prime: skip={skip} prov={prov}')
    prov, skip = sample_provenance(_ana, _warm2, {})
    if not skip:
        failures.append('a warm analysis sample with no prime taken must be skipped, not recorded')
    prov, skip = sample_provenance(_ana, _warm2, {('analysis.rocq-modules', 'prime'): {'id': 'X', 'root': 'r'}})
    if skip or prov['prime_sample_id'] != 'X':
        failures.append(f'a warm analysis sample must name the prime its chain took: {prov}')

    # Both runners must derive a sample's cache authorities identically. They did not: the shell runner used
    # the helper and the analysis runner took the scenario's raw state, which handed `analysis.history` a
    # reused project cache it never touches. One derivation, checked here so the two cannot drift again.
    counts['total'] += 1
    _warm = [s for s in suite['scenarios'] if s['id'] == 'project.warm.noop'][0]
    for cid in ('analysis.history', 'make.diet', 'make.prove'):
        cmd = [c for c in suite['commands'] if c['id'] == cid][0]
        want = declared_authorities(cmd, _warm)
        builds = bool(cmd['build_targets']) or bool(cmd['invalidation_roots'])
        if not builds and set(want.values()) != {'not-applicable'}:
            failures.append(f'{cid} builds nothing yet claims {sorted(set(want.values()))}')
        if builds:
            # A building command keeps the scenario's posture for the authorities its stages TOUCH, and
            # `not-applicable` for the rest. Inheriting the scenario state wholesale is what let `make.prove`
            # describe the Go build cache its build never comes near.
            reached = set(cmd.get('build_targets') or ())
            for auth, state in want.items():
                touches = bool(set(CACHE_STAGES.get(auth, ())) & reached) or auth not in PROJECT_CACHES
                expected = _warm['cache_state'][auth] if touches else 'not-applicable'
                if state != expected:
                    failures.append(f'{cid}: authority {auth} is {state!r}, expected {expected!r} for a '
                                    f'command whose build reaches {sorted(reached)}')

    # ── §6 a cache transition states what THAT cache did, not what any stage did
    counts['total'] += 1
    _before = {'authorities': {'dune_build': 'empty', 'go_build': 'empty',
                               'generated_intermediate': 'empty'}}
    _after = observe_cache_after(_before, {'prover': 'rebuilt', 'rocq-base': 'hit'})['authorities']
    if _after['dune_build'] != 'primed':
        failures.append('a rebuilt prover left the dune build cache unprimed, which it cannot')
    if _after['go_build'] == 'primed' or _after['generated_intermediate'] == 'primed':
        failures.append('one rebuilt stage marked every project cache primed: a prover-only run cannot '
                        f'have filled the Go build cache or the generated intermediates ({_after})')
    # A MIXED stage map is the ordinary case and must be reported as mixed, not collapsed either way.
    _mixed = observe_cache_after({'authorities': {k: 'reused' for k in PROJECT_CACHES}},
                                 {'go-e2e': 'rebuilt', 'emit': 'hit', 'generated-module': 'hit'})
    if _mixed['authorities']['go_build'] != 'primed':
        failures.append('a rebuilt go-e2e left the Go build cache unprimed')
    if _mixed['authorities']['generated_intermediate'] != 'reused':
        failures.append('stages observed as HITS were reported as having primed their cache: '
                        f'{_mixed["authorities"]}')
    # An authority the runner cannot establish stays untouched rather than being invented.
    if observe_cache_after({'authorities': {'go_build': 'not-applicable'}},
                           {'go-e2e': 'rebuilt'})['authorities']['go_build'] != 'not-applicable':
        failures.append('a not-applicable cache was given a transition the runner never established')

    # A policy command builds nothing, so it cannot claim the caches a build scenario declares.
    counts['total'] += 1
    warm = [s for s in suite['scenarios'] if s['id'] == 'project.warm.noop'][0]
    fmt_cmd = [c for c in suite['commands'] if c['id'] == 'make.fmt'][0]
    prove_cmd = [c for c in suite['commands'] if c['id'] == 'make.prove'][0]
    if set(declared_authorities(fmt_cmd, warm).values()) != {'not-applicable'}:
        failures.append('a command that invalidates no root claimed a project cache it never touches')
    # `make.prove` builds only `prover`: the dune build cache is the one project authority it touches, and
    # the Go build cache and the generated intermediates are `not-applicable` to it. Reporting the scenario's
    # posture for all three is the overclaim this closes.
    _prove_auth = declared_authorities(prove_cmd, warm)
    if _prove_auth.get('dune_build') != warm['cache_state']['dune_build']:
        failures.append('a command that does build lost the cache state of an authority it touches')
    if {_prove_auth.get('go_build'), _prove_auth.get('generated_intermediate')} != {'not-applicable'}:
        failures.append('make.prove claims a project cache no stage of its build reaches: '
                        f'{_prove_auth}')

    # Two invocations that differ only in what the operator selected must stay comparable. MAKEFLAGS carries
    # `ONLY=` and `SCENARIO=`, so this is the difference between a compatibility check and a coin flip.
    counts['total'] += 1
    import os as _os
    _saved = _os.environ.get('MAKEFLAGS')
    try:
        _os.environ['MAKEFLAGS'] = ' -- SCENARIO=project.warm.noop ONLY=make.prove'
        first = _concurrency({})
        _os.environ['MAKEFLAGS'] = ' -- SCENARIO=project.cold.prover ONLY=make.check RECORD=1'
        second = _concurrency({})
        _os.environ['MAKEFLAGS'] = ' -j4 -- ONLY=make.prove'
        parallel = _concurrency({})
    finally:
        if _saved is None:
            _os.environ.pop('MAKEFLAGS', None)
        else:
            _os.environ['MAKEFLAGS'] = _saved
    if first != second:
        failures.append('two runs differing only in the selector recorded different concurrency: '
                        f'{first} vs {second}')
    if parallel['make_jobs'] != 4 or parallel['make_jobs_source'] != 'makeflags-explicit':
        failures.append(f'an explicit -j4 was not decoded: {parallel}')

    # Both directions, because a rule that only rejects one shape launders the other.
    observed('a summary pooling samples taken against different sources',
             lambda: validate_observation(
                 observation(samples=[sample(sample_index=0, source_digest='1a' * 32),
                                      sample(sample_index=1, source_digest='2b' * 32)]), digest),
             expect='the tree moved during the run')
    observed('two commands whose incremental samples share one source',
             lambda: validate_observation(
                 observation(samples=[
                     sample(command_id='make.prove', sample_index=0, edit_id='edit.leaf.emit',
                            scenario_id='project.incremental.leaf.emit', source_digest='aa' * 32),
                     sample(command_id='make.check', sample_index=0, edit_id='edit.leaf.emit',
                            scenario_id='project.incremental.leaf.emit', source_digest='aa' * 32)]), digest),
             expect='satisfies another')

    observed('an incremental scenario whose samples repeat one source',
             lambda: validate_observation(
                 observation(samples=[sample(sample_index=0, edit_id='edit.leaf.emit',
                                             scenario_id='project.incremental.leaf.emit'),
                                      sample(sample_index=1, edit_id='edit.leaf.emit',
                                             scenario_id='project.incremental.leaf.emit')]), digest),
             expect='a cached no-op is recorded under an incremental label')

    observed('comparing against a run that never finished',
             lambda: compare({**observation(), 'derived': {'summaries': {}, 'status': 'incomplete'}},
                             observation()),
             expect='incomplete run')
    observed('comparing against an observation with no environment',
             lambda: compare({k: v for k, v in observation().items() if k != 'environment'}, observation()),
             expect="no usable 'environment'")

    # Recording the condition is only worth something if the reading is real where the kernel offers one.
    counts['total'] += 1
    if Path('/proc/loadavg').is_file():
        if not isinstance(host_load(), float):
            failures.append('the host load is published by this kernel but was not read')
    elif host_load() is not None:
        failures.append('a load reading was invented on a kernel that publishes none')

    counts['total'] += 1
    usage_text = render_usage(suite)
    # §Usage — help that teaches a path the tool does not support is a failure, so every example is parsed
    import re as _re
    for line in usage_text.split('\n'):
        m = _re.match(r'\s+make observe (ONLY=(\S+))?\s*(SCENARIO=(\S+))?\s*$', line)
        if not m or not (m.group(2) or m.group(4)):
            continue
        try:
            select(suite, only=m.group(2), scenario=m.group(4))
        except ObservatoryError as exc:
            failures.append(f'a documented example does not resolve: {line.strip()} -> {exc}')
    if 'empty' in usage_text.lower() and 'docker cache' in usage_text.lower():
        failures.append('help must not teach clearing the Docker cache as ordinary use')

    counts['total'] += 1
    usage = render_usage(suite)
    missing_in_usage = [s['id'] for s in suite['scenarios'] if s['id'] not in usage]
    if missing_in_usage:
        failures.append(f'the generated usage omits scenario(s) {missing_in_usage}')

    counts['total'] += 1
    listing = render_list(suite)
    missing_in_list = [c['id'] for c in suite['commands'] if c['id'] not in listing]
    if missing_in_list:
        failures.append(f'the listing omits {len(missing_in_list)} command(s), first {missing_in_list[:3]}')

    total, must_fail = counts['total'], counts['must_fail']
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: BUILD-OBSERVATORY SELF-TEST FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: build-observatory self-test OK — {total} controls '
          f'({must_fail} must-fail with the reason pinned, {total - must_fail} must-accept) ✓')
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description='Fido Build Observatory')
    p.add_argument('--root', default=str(ROOT))
    p.add_argument('--self-test', action='store_true', help='the deterministic coverage controls')
    p.add_argument('--check', action='store_true',
                   help='the permanent command-surface coverage validator (no timing)')
    p.add_argument('--paths', action='store_true', help='verify that every declared observatory path resolves')
    p.add_argument('--only', help='command or group IDs to select (M2 measurement)')
    p.add_argument('--scenario', help='scenario IDs to select (M2 measurement)')
    p.add_argument('--base', help='observation to compare against (M2 measurement)')
    p.add_argument('--compare', help='observation to compare (M2 measurement)')
    p.add_argument('--record', action='store_true', help='replace the canonical observation (M2 measurement)')
    p.add_argument('--list', action='store_true', help='print every stable command ID')
    p.add_argument('--usage', action='store_true', help='print the generated usage text')
    p.add_argument('--observe', action='store_true', help='the measurement entry point')
    p.add_argument('--bundle-root', default=None,
                   help='write the active run bundle here, outside every measured source tree')
    args = p.parse_args(argv)
    root = Path(args.root).resolve()

    try:
        if args.self_test:
            return self_test(root)
        if args.paths:
            paths = resolve(root)
            print(f'fido: build-observatory paths OK — {len(paths)} declared path(s) resolve under {root} ✓')
            return 0
        if args.check:
            print(f'fido: build-observatory coverage OK — {check_coverage(root, load_suite(root))} ✓')
            return 0
        if args.usage:
            print(render_usage(load_suite(root)))
            return 0
        if args.list:
            print(render_list(load_suite(root)))
            return 0
        if args.compare:
            base_where = args.base or OBSERVATION_REL
            base_obs, base_from = load_observation(root, base_where)
            cand_obs, cand_from = load_observation(root, args.compare)
            print(f'fido: build-observatory — comparing {cand_from} against {base_from}')
            print(render_comparison(compare(base_obs, cand_obs, only=args.only,
                                            suite=load_suite(root))))
            return 0

        if args.observe:
            import datetime
            suite = load_suite(root)
            check_coverage(root, suite)
            sel = select(suite, only=args.only, scenario=args.scenario, record=args.record)
            clean_before = not _git(root, 'status', '--porcelain').strip()
            if sel.support:
                print(f'fido: build-observatory — {len(sel.support)} dependenc(ies) added to the selection '
                      f'and measured as support: {", ".join(sel.support)}')
            print(f'fido: build-observatory — {len(sel.selected)} selected command(s) over '
                  f'{len(sel.scenarios)} scenario(s){" (PARTIAL run)" if sel.partial else ""}')

            started = datetime.datetime.now(datetime.timezone.utc).isoformat()
            subj = subject(root)
            run_id = run_id_for(subj, started, subj['inventory_digest'])
            bundle = new_bundle(root, run_id,
                                Path(args.bundle_root).resolve() if args.bundle_root else None)
            print(f'fido: build-observatory — run {run_id}, bundle {bundle}')

            header = {'schema': SCHEMA, 'suite_digest': suite_digest_of(suite),
                      'subject': subj, 'run_id': run_id}
            obs, incomplete, edits_restored = run_observation(
                root, suite, sel, bundle / 'raw', run_id,
                checkpoint=checkpointer(bundle, header))
            if incomplete:
                obs['derived']['status'] = 'incomplete'
                obs['derived']['incomplete'] = incomplete
            write_json(bundle / 'observation.json', obs)

            base_where = args.base or OBSERVATION_REL
            try:
                base_obs, base_from = load_observation(root, base_where)
                result = compare(base_obs, obs, only=args.only, suite=suite)
                write_json(bundle / 'comparison.json', result)
                (bundle / 'comparison.txt').write_text(render_comparison(result) + '\n', encoding='utf-8')
                print(render_comparison(result))
            except ObservatoryError as exc:
                print(f'fido: build-observatory — no comparison: {exc}')

            if incomplete:
                print(f'fido: BUILD-OBSERVATORY INCOMPLETE — {len(incomplete)} pair(s) did not complete: '
                      f'{", ".join(incomplete[:6])}; the bundle is kept and cannot be recorded',
                      file=sys.stderr)
                return 1

            if args.record:
                rules = check_record_eligible(root, sel, suite, suite_digest_of(suite), obs, bundle,
                                              clean_before, edits_restored, incomplete)
                write_json(root / OBSERVATION_REL, obs)
                print(f'fido: build-observatory recorded — {OBSERVATION_REL} replaced after all '
                      f'{len(rules)} recording rules passed; nothing was staged or committed ✓')
            else:
                print(f'fido: build-observatory OK — {len(obs["measurements"])} sample(s) in {bundle}; '
                      f'RECORD=1 would replace {OBSERVATION_REL} ✓')
            return 0
    except ObservatoryError as exc:
        print(f'fido: BUILD-OBSERVATORY FAILED — {exc}', file=sys.stderr)
        return 1

    print(f'fido: BUILD-OBSERVATORY UNAVAILABLE — {PENDING}', file=sys.stderr)
    return 1


if __name__ == '__main__':
    sys.exit(main())
