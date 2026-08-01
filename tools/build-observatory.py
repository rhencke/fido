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
# §3B — how a command's number is ACQUIRED. `direct` runs it; `derived` observes a stage or anchor inside a
# parent's run and takes its parent's scenarios; `catalog-only` never runs. `contained` is the one this repair
# adds, and it differs from `derived` in exactly one way that matters: a contained command is a PUBLIC command
# with a life of its own, so it declares the STATES it must be measured under, and its trace root has to run
# under every one of them. A derived stage cannot ask for a state; a contained target must.
MEASUREMENTS = ('direct', 'derived', 'catalog-only')
COMMAND_FIELDS = ('id', 'kind', 'groups', 'purpose', 'source_view', 'execution', 'side_effect',
                  'measurement', 'scenarios', 'samples', 'dependencies', 'expected_exit', 'outputs', 'owner',
                  'invalidation_roots', 'build_targets', 'contained_in')
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


MAKE_ANCHOR = re.compile(r'\$\(call\s+fido_anchor,(begin|end),([^)]+)\)')


def make_anchor_pairs(root: Path) -> list[str]:
    """Anchor IDs in the live Makefile, proved paired.

    The same relation the hook's anchors have carried since Repair 1, now that Make emits the same grammar.
    Without it a Make checkpoint could name anything at all: a target could lose its `end`, or gain an anchor
    for a command the registry has never heard of, and the first sign would be a contained metric that never
    arrived four hours into a canonical run.

    Nesting is NOT checked here the way it is for the hook. A prerequisite's anchors close before the
    dependent recipe's body opens, so Make's pairs are siblings in file order rather than a stack, and
    demanding a stack would reject the correct shape."""
    text = read_text(root / 'Makefile', 'Makefile')
    opened: dict[str, int] = {}
    closed: list[str] = []
    for n, line in enumerate(text.split('\n'), start=1):
        m = MAKE_ANCHOR.search(line)
        if not m:
            continue
        event, anchor = m.group(1), m.group(2).strip()
        if event == 'begin':
            if anchor in opened:
                raise ObservatoryError(f'Makefile:{n}: anchor {anchor!r} begins twice')
            opened[anchor] = n
        else:
            if anchor not in opened:
                raise ObservatoryError(f'Makefile:{n}: anchor {anchor!r} ends without beginning')
            closed.append(anchor)
    unmatched = sorted(set(opened) - set(closed))
    if unmatched:
        raise ObservatoryError(
            f'Makefile: anchor(s) {unmatched} begin and never end; the interval they name would be missing '
            f'from every trace that contains them, and absence reads as coverage')
    return sorted(closed)


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

    # Which commands never run, and which Docker stages a command that DOES run actually builds. Both are
    # read below to catch a derived child that no runnable parent can ever produce.
    commands_by_id = {c['id']: c for c in suite['commands'] if isinstance(c, dict) and 'id' in c}
    cataloged_ids = {c['id'] for c in suite['commands'] if c.get('measurement') == 'catalog-only'}
    reachable_stages = {st for c in suite['commands'] if c.get('measurement') != 'catalog-only'
                        for st in stages_built_by(stage_graph, c.get('build_targets', []))}

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
        # A derived command is observed INSIDE a parent's run, so if every parent is cataloged there is no
        # run to be observed inside and this child is selected forever and measured never. Three Docker
        # stages sat in exactly that state: I cataloged make.pytools and make.observatory-runner correctly
        # and left their stage children derived, and nothing objected until the very last recording rule of
        # a four-hour run. The parent set is the stage graph's where the graph reaches it, and the declared
        # dependencies otherwise — the same rule the coverage relation uses, not a second one.
        if c['measurement'] == 'derived':
            built_here = cid.startswith('docker.') and cid[len('docker.'):] in reachable_stages
            parents = built_here or [p for p in c['dependencies'] if p not in cataloged_ids]
            if not parents:
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid} is derived but every command that could produce it is cataloged, so '
                    f'it can only ever be selected and never measured; catalog it with the reason instead')
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
        # §3B.3 — CONTAINMENT. A contained command names the trace root whose run establishes it, and only a
        # command that actually RUNS can establish anything. Chaining containment would mean an interval owned
        # by an owner that is itself only an interval, and the root that must be scheduled would stop being
        # derivable from the row.
        # §3B.3/§8 — CONTAINMENT IS A RELATION, NOT A CLASSIFICATION. `contained_in` says: when this command
        # and its root are both required in the SAME state, the root's one run establishes both and this
        # command is not executed again. It does NOT say the command has stopped being runnable. That
        # distinction is load-bearing: §11 requires `ONLY=make.prove SCENARIO=project.cold.prover` to keep
        # working, and a classification that replaced `direct` erased exactly that. So the row keeps its build
        # targets, its invalidation roots and its own cold state, and the planner decides per scenario.
        root_id = (c.get('contained_in') or '').strip()
        if root_id:
            if c['measurement'] != 'direct':
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid} is {c["measurement"]} and names trace root {root_id!r}; only a '
                    f'command that runs can also be contained in another command\'s run')
            if root_id == cid:
                raise ObservatoryError(f'{SUITE_REL}: {cid} names itself as its trace root')
            root_cmd = commands_by_id.get(root_id)
            if root_cmd is None:
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid} is contained in {root_id!r}, which is not a command in this registry')
            if root_cmd['measurement'] != 'direct':
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid} is contained in {root_id}, which is {root_cmd["measurement"]} rather '
                    f'than direct; a trace root has to be something that runs')
            # Chaining would mean an interval owned by an owner that is itself only an interval, and the root
            # to schedule would stop being derivable from the row.
            if (root_cmd.get('contained_in') or '').strip():
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid} is contained in {root_id}, which is itself contained in '
                    f'{root_cmd["contained_in"]}; containment does not chain')
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
            # §3B.8 — CANONICAL MULTIPLICITY IS ONE. The fixed triplicate cost three warm executions of
            # every command and, crossed with five edit shapes over four overlapping commands, sixty
            # incremental executions of work the suite had already observed. It also bought precision where
            # there was none to buy: `make.check` under a `.v` edit measured 480/481/478s, a 0.6% spread,
            # while the warm no-op it repeated just as often measured 1.6/1.8/1.6s, a 12% one. Repeats are
            # ad hoc now, through REPEAT=, and can never accompany RECORD=1.
            # Only a genuine integer above one is a MULTIPLICITY claim. Zero and a fraction are malformed
            # counts and belong to the positive-integer rule below, which says so in its own words; catching
            # them here would answer a different question than the one they ask.
            if isinstance(c['samples'][s], int) and not isinstance(c['samples'][s], bool) \
                    and c['samples'][s] > 1:
                raise ObservatoryError(
                    f'{SUITE_REL}: {cid}: scenario {s!r} declares {c["samples"][s]} canonical samples; '
                    f'canonical acquisition is ONE real trace per identity, and repetition is ad hoc')

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

    # §7/§16 — the SAME relation for Make checkpoints, in both directions, now that Make emits the same
    # anchors. A checkpoint naming nothing the registry knows would produce a contained metric nobody
    # declared; a public target with neither a checkpoint nor a catalog reason would be measured only as
    # part of whatever contains it, with no way to say that was intended.
    make_anchors = set(make_anchor_pairs(root))
    known = {c['id'] for c in suite['commands']}
    for missing in sorted(make_anchors - known):
        # `<command>-body` is the declared form for a compound recipe's own unowned segment: `make.check` is
        # a trace root measured as a whole process, and its recipe body is a separate interval §7 requires
        # to be named rather than folded into the parent.
        if missing.endswith('-body') and missing[:-len('-body')] in known:
            continue
        problems.append(f'Makefile anchors {missing!r}, which is neither a registry command nor the '
                        f'`<command>-body` segment form')
    for c in suite['commands']:
        if c['kind'] != 'make-target' or c['measurement'] == 'catalog-only':
            continue
        if c['id'] in make_anchors or f'{c["id"]}-body' in make_anchors:
            continue
        problems.append(f'{c["id"]} is a public Make target with no checkpoint and no catalog reason, so its '
                        f'interval cannot be recovered from any trace that contains it')

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
    # §6 — READ BACK, never assumed. This used to report `BUILDKIT_MAX_PARALLELISM` from the environment: a
    # variable buildkitd does not consult and nothing in this repository sets, so the field was permanently
    # null while claiming to describe effective parallelism. The builder itself echoes the daemon flags it
    # was created with, so the observation now records what the builder SAYS rather than what someone hoped.
    flags = (inspect or {}).get('BuildKit daemon flags', '')
    seen = OCI_PARALLELISM.search(flags)
    return {'make_jobs': jobs, 'make_jobs_source': source,
            'buildkit_max_parallelism': int(seen.group(1)) if seen else None,
            'buildkit_parallelism_source': 'builder-daemon-flags' if seen else 'not-reported',
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


def host_class_fingerprint(env: dict) -> str:
    """The host-class identity, DERIVED from the retained fields every time it is needed.

    §7 E3 — it was computed once at capture and thereafter trusted. The reviewer changed
    `concurrency.buildkit_max_parallelism` from 1 to 2, left the stored hash alone, and the observation still
    validated: comparison then read the two runs as the same host class and printed ordinary timing verdicts
    across a doubling of build parallelism. A fingerprint nobody recomputes is a claim, not a check."""
    stable = {k: env.get(k) for k in FINGERPRINT_FIELDS}
    stable['base_image_digests'] = env.get('base_image_digests')
    stable['toolchain_versions'] = env.get('toolchain_versions')
    return _sha256(json.dumps(stable, sort_keys=True, ensure_ascii=False).encode('utf-8'))


def environment(root: Path, builder: str = None) -> dict:
    env = {**_host(root, builder), **_pinned(root)}
    env['builder'] = builder or OBSERVATORY_BUILDER
    env['host_class_fingerprint'] = host_class_fingerprint(env)
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
        # A trace root is pulled in by CONTAINMENT, not by a second declaration. Naming it in `dependencies`
        # as well would state one fact twice, and the copy that drifts is the one nobody reads: selecting a
        # contained command would then plan metrics whose owner never runs, which the plan refuses — as it
        # did for `ONLY=make.prove` until this followed `contained_in` here.
        roots = [] if bool(only or scenario) else [(commands[cid].get("contained_in") or "").strip()]
        for dep in list(commands[cid]["dependencies"]) + roots:
            if dep and dep not in closure:
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


def parse_anchor_log(text: str, known: set | None = None) -> list[dict]:
    """§3 — the RUNTIME checkpoint state machine, which fails closed by itself.

    Static source pairing proves the Makefile and the hook are written correctly. It says nothing about what
    a run actually wrote, and contained timing is derived from that log rather than from the source. Three
    malformed logs were accepted silently: an `end` with no `begin` produced no event at all, a second
    `begin` overwrote the first so the pair reported its LAST fragment as the whole interval, and a second
    `end` was ignored.

    ONE stack serves both grammars, because both obey stack discipline for different reasons rather than by
    coincidence, and neither is forced into the other's model:

      MAKE — flat SIBLINGS. `check: pytools hostpython names fcb claims diet observatory prove e2e builder`
      runs each prerequisite to completion before the next begins, and `make.check-body` brackets only the
      recipe. There is deliberately no enclosing `make.check` anchor: prerequisites run before the recipe, so
      one there would begin after most of the work. At most one checkpoint is ever open.

      PRE-COMMIT — one root, `precommit.full`, with sibling stages nested inside it. Two open at a time, and
      the root closes last.

    So an end must close the INNERMOST open checkpoint. That rejects interleaving without assuming Make
    nests, and it is the same rule the hook needs. Exact start and end are retained, not only the duration:
    §4's partition cannot be proved from durations alone."""
    stack: list[tuple[str, int]] = []
    closed: dict[str, int] = {}
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
        if known is not None and anchor not in known:
            raise ObservatoryError(
                f'checkpoint {anchor!r} is not one this trace declares, so the log describes work the '
                f'registry cannot name; a checkpoint nobody declared is not evidence')
        if kind == 'begin':
            already = [a for a, _ in stack if a == anchor]
            if already:
                raise ObservatoryError(
                    f'checkpoint {anchor!r} began while already open; the second begin silently replaced the '
                    f'first and the pair reported the LAST fragment as the whole interval')
            if anchor in closed:
                raise ObservatoryError(
                    f'checkpoint {anchor!r} completed a second pair in one trace; canonical multiplicity is '
                    f'one, so two intervals under one identity are two answers to one question')
            stack.append((anchor, ns))
        else:
            # TWO rules, stated once each rather than as one compound condition. An end with nothing open is
            # a different defect from an end that closes the wrong checkpoint, and a reader of either failure
            # is owed the one that happened.
            top = stack[-1][0] if stack else None
            if top is None:
                raise ObservatoryError(
                    f'checkpoint {anchor!r} ended while nothing was the open checkpoint; an unmatched end '
                    f'was previously ignored and its interval attributed to nobody')
            if top != anchor:
                raise ObservatoryError(
                    f'checkpoint {anchor!r} ended while {top!r} was the open checkpoint, so these intervals '
                    f'interleave rather than nest and neither can be attributed')
            _, started = stack.pop()
            closed[anchor] = ns
            wall = ns - started
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
                               'clock': HOOK_CLOCK, 'start_ns': started, 'end_ns': ns, 'depth': len(stack),
                               'lower_ns': 0, 'upper_ns': HOOK_CLOCK['resolution_ns'],
                               'below_resolution': True})
            else:
                events.append({'id': anchor, 'wall_ns': wall, 'source': 'hook-anchor',
                               'clock': HOOK_CLOCK, 'start_ns': started, 'end_ns': ns, 'depth': len(stack)})
    if stack:
        raise ObservatoryError(
            f'checkpoint(s) {sorted(a for a, _ in stack)} began and never ended; the stages they name are '
            f'missing from this sample and their absence would read as coverage')
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
                         role_of=None, contained: set | None = None) -> list[dict]:
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
                    # A CONTAINED public command's interval is `contained_wall_elapsed`, never plain elapsed
                    # time: acquisition kind is part of metric identity, and that is what keeps it out of
                    # the same median as the direct execution of the same command in a state where its root
                    # does not run. The expected relation says the same thing from the registry side; these
                    # two must agree or the coverage relation fails at the end of the suite.
                    'measurement_kind': (KIND_AGGREGATE if buildkit
                                         else KIND_UNTIMED if event.get('untimed')
                                         else KIND_CONTAINED if event['id'] in (contained or set())
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


def sample_rule_problems(samples: list[dict]) -> list[str]:
    """Every per-sample rule, stated ONCE, for both the fragment check and the final validator.

    These began as a raising loop inside the final validator. Copying them into the fragment check gave one
    fact two statements, and the mutation harness said so immediately: an existing mutant's anchor matched in
    two places. Two copies of a rule agree until one is edited, and the one a reader would trust is whichever
    they happened to open."""
    problems: list[str] = []
    for i, s in enumerate(samples):
        absent = [f for f in SAMPLE_FIELDS if f not in s]
        if absent:
            problems.append(f'sample {i} ({s.get("command_id")}) is missing field(s) {absent}')
            continue
        # A derived BuildKit child has aggregate step work rather than elapsed wall time, so `wall_ns` is
        # absent by design. What is forbidden is a NEGATIVE duration, which a monotonic clock cannot produce.
        for field in ('wall_ns', 'aggregate_step_ns'):
            if s.get(field) is not None and s[field] < 0:
                problems.append(f'sample {i} ({s["command_id"]}) has a negative {field}')
        kind = s.get('measurement_kind') or KIND_WALL
        if kind not in MEASUREMENT_KINDS:
            problems.append(f'sample {i}: measurement_kind {kind!r} is not a known kind')
        if s.get('below_resolution') and (s.get('lower_ns') is None or s.get('upper_ns') is None
                                          or s['lower_ns'] > s['upper_ns']):
            problems.append(
                f'sample {i} ({s["command_id"]}) is a below-resolution interval without a usable bound')
        # A below-resolution read is elapsed time known as a bound, so it carries no point value on purpose.
        # It must SAY so: without the flag this is a sample that measured nothing and claimed a kind.
        if s.get('below_resolution') and s.get('wall_ns') is not None:
            problems.append(
                f'sample {i} ({s["command_id"]}) is declared below resolution yet carries a point duration')
        if (s.get('wall_ns') is None and s.get('aggregate_step_ns') is None
                and not s.get('below_resolution') and kind != KIND_UNTIMED):
            problems.append(
                f'sample {i} ({s["command_id"]}) records neither an elapsed duration nor aggregate step '
                f'work, so it measures nothing')
        # An untimed artifact must SAY it is one and carry no duration. Zero was the old representation and
        # it is a measured claim: it asserts the work took no time, which was never true.
        if kind == KIND_UNTIMED and (s.get('wall_ns') is not None or s.get('aggregate_step_ns') is not None):
            problems.append(
                f'sample {i} ({s["command_id"]}) is declared an untimed artifact yet carries a duration')
        if kind != KIND_UNTIMED and s.get('wall_ns') == 0 and s.get('aggregate_step_ns') is None:
            problems.append(
                f'sample {i} ({s["command_id"]}) records an elapsed duration of exactly zero; work that '
                f'happened takes time, so this is either an untimed artifact or a below-resolution interval')
        # The authority map must be DERIVABLE from the stage evidence beside it. Two records of one fact
        # that are merely stored next to each other will disagree eventually, and the one that disagreed
        # here was the one a reader would have trusted.
        if s.get('cache_before') and s.get('cache_after') and not s.get('derived_parent_id'):
            want = observe_cache_after(s['cache_before'],
                                       (s.get('cache_observation') or {}).get('stages', {}))
            if s['cache_after'].get('authorities') != want.get('authorities'):
                problems.append(
                    f'sample {i} ({s["command_id"]}): the recorded cache authorities '
                    f'{s["cache_after"].get("authorities")} are not what the retained stage evidence '
                    f'derives ({want.get("authorities")})')
        if s['resource_scope'] not in (SCOPE_HOST, SCOPE_BUILDKIT, SCOPE_UNAVAILABLE):
            problems.append(f'sample {i}: resource_scope {s["resource_scope"]!r} is not a known scope')
    return problems


def fragment_problems(partial: dict) -> list[str]:
    """Everything checkable about the samples acquired SO FAR, without executing anything.

    §12 — the canonical suite must never be the first place a structural rule is exercised, and a defect in
    an earlier trace must not wait for the last recording rule of the run to surface. Repair 2 lost four
    hours to exactly that twice: once to a metric identity that only misbehaved on a fast stage, once to a
    run identity nothing produced. Both were visible in the first fragment that contained them.

    It reuses the same per-sample rules and the same identity relations the final validator uses rather than
    a cheaper local copy, because a fragment check that passes what the final check rejects is worse than no
    fragment check at all — it would say the expensive part was safe to continue."""
    return (sample_rule_problems(partial.get('measurements', []))
            + identity_problems(partial)
            + retained_trace_problems(partial))


SUITE_COST_MEMBERS = ('suite_started', 'suite_completed', 'suite_wall_ns', 'preflight_wall_ns',
                      'validation_wall_ns', 'validation_components', 'trace_wall_ns',
                      'direct_trace_count', 'contained_metric_count')


def suite_cost_problems(obs: dict) -> list[str]:
    """§7 E2 — ONE suite-cost validator, for recording, loading, resume and comparison alike.

    The block was retained and never checked, so its counts were free to disagree with the samples beside
    them and its per-trace entries free to name traces the run never had. Meta-evidence that nothing verifies
    is the same shape as the coverage-on-paper this repair keeps refusing everywhere else."""
    cost = obs.get('suite_cost')
    if not isinstance(cost, dict):
        return ['the observation retains no suite cost, so the facility reports every cost but its own']
    absent = [m for m in SUITE_COST_MEMBERS if m not in cost]
    if absent:
        return [f'suite cost is missing member(s) {absent}']

    problems = []
    samples = obs.get('measurements') or []
    direct = [s for s in samples if not s.get('derived_parent_id')]
    contained = [s for s in samples if s.get('derived_parent_id')]
    if cost['direct_trace_count'] != len(direct):
        problems.append(f'suite cost claims {cost["direct_trace_count"]} direct trace(s) beside '
                        f'{len(direct)} retained direct sample(s)')
    if cost['contained_metric_count'] != len(contained):
        problems.append(f'suite cost claims {cost["contained_metric_count"]} contained metric(s) beside '
                        f'{len(contained)} retained derived sample(s)')
    for field in ('suite_wall_ns', 'preflight_wall_ns', 'validation_wall_ns'):
        value = cost[field]
        if not isinstance(value, int) or value < 0:
            problems.append(f'suite cost {field} is {value!r}, which is not a duration')
    if isinstance(cost.get('validation_components'), dict):
        parts = sum(v for v in cost['validation_components'].values() if isinstance(v, int))
        if isinstance(cost['validation_wall_ns'], int) and parts != cost['validation_wall_ns']:
            problems.append(f'suite cost validation components sum to {parts}, not the retained '
                            f'{cost["validation_wall_ns"]}')
    if cost['suite_started'] >= cost['suite_completed']:
        problems.append(f'suite cost starts at {cost["suite_started"]} and completes at '
                        f'{cost["suite_completed"]}, so its own timestamps do not order')

    # Every per-trace entry names an EXACT trace of this run, and every timed direct sample has one.
    named = set(cost.get('trace_wall_ns') or {})
    real = {trace_id_of(s['command_id'], s['scenario_id'], s.get('edit_id'), s['sample_index'])
            for s in direct if s.get('wall_ns') is not None}
    for orphan in sorted(named - real):
        problems.append(f'suite cost retains a cost for {orphan}, which is not a trace this run performed')
    for missed in sorted(real - named):
        problems.append(f'suite cost retains no cost for {missed}, which this run did perform')
    return problems


ARTIFACT_MEMBERS = ('module_graph', 'history_analysis')


def artifact_problems(obs: dict) -> list[str]:
    """§7 E4 — an analysis artifact is BOUND to the trace that established it, and its views are recomputed.

    The schema required `module_graph` and `history_analysis` to be present and permitted them to be null or
    unrelated while their analysis samples sat beside them claiming the work had happened. Presence is not
    evidence: the binding is what makes the artifact answerable for the samples that produced it.

    The mapping from command to member is NOT restated here. Each trace's completion object already names the
    members its run established, so the rule reads that instead of a second table which would drift."""
    problems: list[str] = []
    samples = obs.get('measurements') or []
    traces = obs.get('traces') or []

    # An analysis command runs in SEVERAL cache states — `analysis.rocq-modules` in both
    # `project.cold.module-graph` and `project.warm.noop` — and each run establishes a graph whose per-module
    # wall times differ, so their digests differ too while the observation retains ONE member. The producer's
    # rule is that the last such trace's artifact is the retained one, and the record states that rather than
    # pretending a single establishing trace or quietly accepting any of them.
    owner_of: dict[str, list[str]] = {}
    last_digest: dict[str, str] = {}
    for t in traces:
        for member, want in (t.get('analysis_artifacts') or {}).items():
            owner_of.setdefault(member, []).append(t.get('trace_id'))
            last_digest[member] = want

    for member, owners in owner_of.items():
        have = obs.get(member)
        if have is None:
            problems.append(f'trace(s) {sorted(owners)} established {member}, and the observation retains '
                            f'none — the samples claim work whose product is absent')
        elif artifact_digest(have) != last_digest[member]:
            problems.append(f'the retained {member} does not hash to what its establishing trace '
                            f'{owners[-1]} recorded, so it is not the artifact that trace produced')

    for member in ARTIFACT_MEMBERS:
        if obs.get(member) is not None and member not in owner_of:
            problems.append(f'the observation retains a {member} that no trace established, so nothing binds '
                            f'it to a run')

    # An analysis command that produced a sample must have produced its artifact with it.
    for s in samples:
        if s.get('derived_parent_id') or not s['command_id'].startswith('analysis.'):
            continue
        mine = [t for t in traces if t.get('root_sample_id') == s.get('sample_id')]
        if mine and not (mine[0].get('analysis_artifacts') or {}):
            problems.append(f'{s["command_id"]} produced a sample whose trace establishes no artifact, so '
                            f'the analysis is recorded as having run and left nothing behind')

    # THE DERIVED VIEWS EQUAL RECOMPUTATION from those exact artifacts. A view is a claim about an artifact;
    # if it does not follow from the artifact retained beside it, one of the two is not what it says it is.
    derived = obs.get('derived') or {}
    graph, history = obs.get('module_graph'), obs.get('history_analysis')
    if graph and 'rebuild_impact' in derived and derived['rebuild_impact'] != rebuild_impact(graph):
        problems.append('the retained rebuild impact is not what its own module graph produces')
    if history and 'weighted_rebuild_cost' in derived \
            and derived['weighted_rebuild_cost'] != weighted_rebuild_cost(history, graph):
        problems.append('the retained weighted rebuild cost is not what its own artifacts produce')
    return problems


def retained_trace_problems(partial: dict) -> list[str]:
    """Every retained trace object, checked AGAINST THE SAMPLES the same record holds.

    Checking a completion object only against itself is what made the reviewer's reproduction possible: they
    deleted `make.prove`, `docker.prover` and `make.fcb` in turn from a completed `make.check` fragment and
    every mutilated fragment still passed. An object's own lists stay self-consistent when a sample vanishes
    from beside it, so the binding to the record is the rule that matters."""
    traces = partial.get('traces') or []
    samples = partial.get('measurements') or []
    by_id = {s.get('sample_id'): s for s in samples if s.get('sample_id')}
    present = observed_relation(samples)
    problems: list[str] = []
    owner_of: dict[str, str] = {}
    for obj in traces:
        if any(m not in obj for m in TRACE_MEMBERS):
            problems += trace_problems(obj)
            continue
        label = obj['trace_id']
        # ORDER MATTERS. Each defect must report the reason that IS its defect: an omitted child otherwise
        # surfaces as a metric-count mismatch, and a misfiled child as a child-count mismatch, so a control
        # asserting the real reason would pass on a message about something else.
        for sid in [obj['root_sample_id'], *obj['child_sample_ids']]:
            if sid is None:
                continue
            if sid not in by_id:
                problems.append(f'{label}: names sample {sid}, which this record does not contain')
                continue
            if sid in owner_of and owner_of[sid] != label:
                problems.append(f'sample {sid} is claimed by two traces, {owner_of[sid]} and {label}')
            owner_of[sid] = label
        for sid in obj['child_sample_ids']:
            child = by_id.get(sid)
            if child is None:
                continue
            if (child.get('derived_parent_id') != obj['command_id']
                    or child.get('scenario_id') != obj['scenario_id']):
                problems.append(f'{label}: child {sid} was derived inside '
                                f'{child.get("derived_parent_id")}/{child.get("scenario_id")}, so it is '
                                f'retained under a trace that did not produce it')
        problems += trace_problems(obj)
        for metric in sorted(set(obj['observed_metrics'])):
            claimed = obj['observed_metrics'].count(metric)
            if present.get(metric, 0) < claimed:
                problems.append(f'{label}: claims metric {metric} {claimed} time(s), and the retained '
                                f'samples hold {present.get(metric, 0)}')
    return problems


def wanted_samples(command: dict, scenario_id: str, role: str, repeat: int = 1) -> int:
    """How many times this command runs in this state.

    §3B.8 — the canonical count is ONE, always. `REPEAT` is ad hoc variance for a named investigation, so it
    multiplies only what the operator SELECTED: a support command pulled in to make the answer mean anything
    is not what they asked about, and repeating it would spend minutes nobody wanted on a number nobody
    requested. The registry's own count stays the authority for everything else."""
    base = command['samples'][scenario_id]
    return base * repeat if (repeat > 1 and role == 'selected') else base


def resume_incompatibilities(prior: dict, subj: dict, suite: dict, env: dict, plan: dict) -> list[str]:
    """Every reason this bundle's traces may NOT be carried into the current run, named individually.

    §13 — a changed commit, suite, producer, environment, serial configuration or trace plan makes an earlier
    fragment incompatible, and provenance is never reconstructed to bridge the gap. Resume exists so an
    interrupted four-hour suite need not start over; it does not exist to let a sample from one candidate
    stand in for another. Returning every reason rather than the first is deliberate — a reader deciding
    whether to rerun wants the whole list, not a scavenger hunt through six invocations.

    `inventory_digest` covers the measured source view, so a changed observatory, a changed registry and a
    changed theory each move it; they are still reported separately where the record allows it, because
    "the tree differs" and "the suite you are running is not the suite that produced this" send a reader to
    different places."""
    reasons = []
    before = prior.get('subject') or {}
    for field, human in (('commit', 'committed subject'), ('inventory_digest', 'measured source'),
                         ('source_view', 'source view'), ('dirty', 'working-tree cleanliness')):
        if before.get(field) != subj.get(field):
            reasons.append(f'{human} differs: {before.get(field)!r} then, {subj.get(field)!r} now')
    if prior.get('suite_digest') != suite_digest_of(suite):
        reasons.append('the suite registry differs, so the plan that produced those traces is not this plan')
    prior_env = prior.get('environment') or {}
    if prior_env.get('host_class_fingerprint') != env.get('host_class_fingerprint'):
        reasons.append('the host class differs, so timings from that bundle describe another machine')
    prior_conc = (prior_env.get('concurrency') or {})
    now_conc = (env.get('concurrency') or {})
    for field in ('make_jobs', 'buildkit_max_parallelism'):
        if prior_conc.get(field) != now_conc.get(field):
            reasons.append(f'the serial configuration differs: {field} was {prior_conc.get(field)!r}, '
                           f'now {now_conc.get(field)!r}')
    prior_traces = {(s['command_id'], s['scenario_id']) for s in prior.get('measurements', [])
                    if not s.get('derived_parent_id')}
    planned = {(t['command_id'], t['scenario_id']) for t in plan['traces']}
    stray = sorted(prior_traces - planned)
    if stray:
        reasons.append(f'{len(stray)} retained trace(s) are not in this plan at all, e.g. {stray[0]}; the '
                       f'trace definition changed and those samples measure something else now')
    return reasons


def resumable_traces(prior: dict) -> tuple[set, list[str]]:
    """The traces a compatible bundle may contribute, and why the rest may not.

    Only COMPLETE, individually validated fragments qualify. A half-written trace is not a cheap head start:
    its metrics would enter the coverage relation as though the work had been observed."""
    problems = fragment_problems(prior)
    if problems:
        return set(), [f'the bundle does not validate, so none of its traces may be reused: {problems[0]}']
    done = {(s['command_id'], s['scenario_id']) for s in prior.get('measurements', [])
            if not s.get('derived_parent_id') and s.get('status') == 'ok'}
    unfinished = sorted({(s['command_id'], s['scenario_id']) for s in prior.get('measurements', [])
                         if not s.get('derived_parent_id') and s.get('status') != 'ok'} - done)
    notes = [f'{len(unfinished)} trace(s) did not complete and will be rerun, e.g. {unfinished[0]}'] \
        if unfinished else []
    return done, notes


class ValidationClock:
    """§7 E1 — what the facility spends CHECKING itself, on the suite's own monotonic source.

    Repair 3 required this and the implementation never produced it, so the one cost the observation could
    not report was the cost of the thing doing the reporting. It accumulates per component — the deterministic
    preflight, the per-trace fragment checks, the final recording rules — because a single total cannot say
    whether validating got expensive or merely happened more often.

    Only the validating call is inside the interval. A measured command's own time is never counted here: the
    whole point is to separate what the suite spends proving from what it spends measuring."""

    def __init__(self):
        self.components: dict[str, int] = {}

    def measure(self, component: str, fn, *args, **kwargs):
        started = _monotonic_ns()
        try:
            return fn(*args, **kwargs)
        finally:
            self.components[component] = self.components.get(component, 0) + (_monotonic_ns() - started)

    def total_ns(self) -> int:
        return sum(self.components.values())


def checkpointer(bundle: Path, header: dict, clock: 'ValidationClock | None' = None):
    """Write the local observation after every completed sample, and CHECK it before the next one starts.

    The first candidate wrote it only when the suite returned, so a suite that was KILLED left raw logs and
    nothing to inspect. The safety half held — a cancelled run can never record — but the evidence half only
    worked on the failure path."""
    def write(samples: list[dict], incomplete: list[str], traces: list[dict] | None = None):
        partial = {**header, 'measurements': samples, 'traces': list(traces or []),
                   'derived': {'summaries': summarise(samples), 'status': 'incomplete',
                               'incomplete': list(incomplete)}}
        write_json(bundle / 'observation.json', partial)
        # §12 — stop IMMEDIATELY. Continuing past a defective fragment spends the rest of the suite proving
        # nothing, and the bundle is already written, so the evidence for the failure survives the stop.
        problems = (clock.measure('per_trace', fragment_problems, partial) if clock
                    else fragment_problems(partial))
        if problems:
            raise ObservatoryError(
                f'trace fragment is invalid after {len(samples)} sample(s), so the rest of the suite would '
                f'measure against a broken record: {problems[0]}'
                + (f' (and {len(problems) - 1} more)' if len(problems) > 1 else ''))

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
KIND_UNTIMED = 'untimed_artifact'
# §3B.4 — an interval measured INSIDE a trace by a checkpoint pair is not the same quantity as running that
# command yourself: it excludes the process start the standalone run pays and it sits inside a parent's cache
# and scheduling state. Since acquisition kind is part of metric identity, the two can never land in one
# median or one delta row, which is what stops a trace-based baseline being compared against a direct one.
KIND_CONTAINED = 'contained_wall_elapsed'
MEASUREMENT_KINDS = (KIND_WALL, KIND_CONTAINED, KIND_AGGREGATE, KIND_UNTIMED,
                     'cpu_user', 'cpu_system', 'rss_peak')


def measured(sample: dict) -> tuple[int | None, str]:
    """The one number a sample contributes to a summary, and WHAT KIND of number it is.

    Elapsed wall time and the sum of BuildKit step durations are different measurements: steps that run in
    parallel make aggregate work exceed elapsed time, so pooling them or printing one under the other's name
    states something false. The kind travels with the value from here on, and it is part of the identity, so
    two kinds can never land in one median.

    A hook stage that finished inside one clock tick is elapsed time too — it is the same quantity on the
    same clock, known only as a bound. It contributes no point value here and is summarised as a bound.
    """
    kind = sample.get('measurement_kind') or KIND_WALL
    if sample.get('below_resolution'):
        return None, kind
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
    describing a different measurement than the one the registry required.

    PRECISION is deliberately NOT in the key. A hook stage that runs faster than one 10 ms tick is known as a
    bound rather than a point, and a `duration_interval` kind once carried that — which made a metric's
    identity depend on its own value, so a stage changed identity by being fast. The registry declared
    `wall_elapsed` and could not have declared otherwise; the run produced a kind nobody could predict, and
    the coverage rule correctly reported the declared metric unmeasured and the produced one undeclared. The
    quantity and its instrument name the metric; `below_resolution` and the bound describe the read."""
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
    # A stage faster than one clock tick has a BOUND, not a value, and precision is not part of the identity,
    # so the SAME metric can hold both point reads and below-resolution ones across its repetitions. Both are
    # collected under one key here and the row shape is decided once, below, from what actually landed.
    bounds: dict[str, dict] = {}
    for s in samples:
        value, kind = measured(s)
        key = metric_identity(s)
        kinds.setdefault(key, kind)
        if s.get('below_resolution'):
            row = bounds.setdefault(key, {'samples': 0, 'lower_ns': None, 'upper_ns': None})
            row['samples'] += 1
            low, high = s.get('lower_ns') or 0, s.get('upper_ns') or 0
            row['lower_ns'] = low if row['lower_ns'] is None else min(row['lower_ns'], low)
            row['upper_ns'] = high if row['upper_ns'] is None else max(row['upper_ns'], high)
            continue
        if value is None:
            continue
        by_key.setdefault(key, []).append(value)
    out = {}
    for key in sorted(set(by_key) | set(bounds)):
        values = sorted(by_key.get(key, []))
        bound = bounds.get(key)
        if bound is None:
            mid = len(values) // 2
            median = values[mid] if len(values) % 2 else (values[mid - 1] + values[mid]) // 2
            # `median_ns`, not `median_wall_ns`: the field carried aggregate step work for every derived
            # BuildKit child while calling it elapsed wall time, and the comparator and report repeated the
            # claim. The kind is stated beside the number instead of assumed by the field's name.
            out[key] = {'samples': len(values), 'measurement_kind': kinds[key], 'median_ns': median,
                        'min_ns': values[0], 'max_ns': values[-1]}
            continue
        # ANY below-resolution repetition makes the whole row a bound. A median over only the point reads
        # would describe a subset while being labelled the metric — with two ticks under 10 ms and one read
        # at 20 ms, "median 20 ms" is the maximum wearing the median's name. The bound spans every read, so
        # it stays true of all of them and no percentage can be computed against a number nobody measured.
        out[key] = {'samples': len(values) + bound['samples'], 'measurement_kind': kinds[key],
                    'below_resolution': True, 'below_resolution_samples': bound['samples'],
                    'lower_ns': min([bound['lower_ns']] + values),
                    'upper_ns': max([bound['upper_ns']] + values)}
    return dict(sorted(out.items()))


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
    # A SELF-CONTAINED repository, not a linked worktree.
    #
    # A worktree's `.git` is a FILE pointing back into the main repository's `.git/worktrees/<name>`. Every
    # gate that runs inside the copy is given the copy and nothing else — the pinned image mounts one
    # directory — so git there resolves that pointer to a path which does not exist and reports "not a git
    # repository". `make check` and the staged hook both died exactly that way, and a shallow local clone
    # costs a second and carries its own object store.
    head = _git(root, 'rev-parse', 'HEAD').strip()
    _git(root, 'clone', '--quiet', '--depth', '1', f'file://{root}', str(dest))
    got = _git(dest, 'rev-parse', 'HEAD').strip()
    if got != head:
        raise ObservatoryError(
            f'the disposable copy is at {got[:12]} but the repository is at {head[:12]}; a copy that is not '
            f'the subject would measure a tree nobody selected')
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
    """Remove the copy. It is a standalone clone, so the main repository holds no registration to undo."""
    import shutil
    shutil.rmtree(dest, ignore_errors=True)


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
# The COMPLETE member set, and the only authority for it. `run_id` was demanded by identity_problems and
# named nowhere else, so the producer never emitted it, the member check never missed it, and the self-test
# fixture supplied it by hand — three places disagreeing about one fact, with the fixture making the
# disagreement invisible. The producer now asserts it emits exactly this set and the fixture must match it.
OBSERVATION_MEMBERS = ('schema', 'suite_digest', 'run_id', 'subject', 'environment', 'cache_model',
                       'commands', 'definitions', 'measurements', 'traces', 'module_graph',
                       'history_analysis', 'derived', 'selection', 'suite_cost')
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
        # The prime relation belongs to samples that RAN. A derived child performs no build of its own; its
        # cache provenance is a copy of its parent's, prime reference included, and asking whether that prime
        # belongs to the CHILD's command compares a stage id against the command that built it, which can
        # never match. The parent carries the identical relation and is checked here with the right identity,
        # so nothing is lost by not asking the child twice. The rule already knew derived samples do not run
        # — it refuses one AS a prime, two branches below — and then asked this of them anyway.
        if s.get('derived_parent_id'):
            continue
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
    # ONE statement of the per-sample rules, shared with the fragment check that runs between traces.
    for problem in sample_rule_problems(samples):
        raise ObservatoryError(problem)

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

    # §7 E3 — the fingerprint is RE-DERIVED from the fields beside it, never trusted. Changing a host field
    # while leaving the hash alone made two different host classes compare as one.
    env_block = obs.get('environment') or {}
    if env_block.get('host_class_fingerprint') != host_class_fingerprint(env_block):
        raise ObservatoryError(
            'the retained host-class fingerprint is not the one its own environment fields produce, so the '
            'observation describes a host it did not run on')

    # §2 — the SAME trace rules a fragment is held to, and BEFORE the downstream symptoms. A recorded
    # observation checked more loosely than the partial bundles that preceded it would let the final write
    # launder what every intermediate check caught. It speaks first because a lost child also makes its
    # command look unmeasured, and the reader is owed the defect rather than its consequence.
    bad_traces = retained_trace_problems(obs)
    if bad_traces:
        raise ObservatoryError(
            f'{len(bad_traces)} retained trace defect(s): {bad_traces[0]}'
            + (f' (and {len(bad_traces) - 1} more)' if len(bad_traces) > 1 else ''))

    # §7 E4 — analysis artifacts are bound to the traces that established them and their views recomputed.
    bad_artifacts = artifact_problems(obs)
    if bad_artifacts:
        raise ObservatoryError(
            f'{len(bad_artifacts)} analysis-artifact defect(s): {bad_artifacts[0]}'
            + (f' (and {len(bad_artifacts) - 1} more)' if len(bad_artifacts) > 1 else ''))

    # §7 E2 — the suite's own cost, held to the standard of everything it reports. AFTER the trace rules: a
    # lost child also makes the contained count disagree, and the count is the symptom, not the defect.
    bad_cost = suite_cost_problems(obs)
    if bad_cost:
        raise ObservatoryError(
            f'{len(bad_cost)} suite-cost defect(s): {bad_cost[0]}'
            + (f' (and {len(bad_cost) - 1} more)' if len(bad_cost) > 1 else ''))

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

    # §2 — every DIRECT sample must be covered by exactly one closed trace object. The runner refuses a trace
    # that does not close, so reaching here with an uncovered root means the object was lost or never built —
    # and the whole point is that completion is never inferred from a root sample that merely succeeded.
    covered: dict[str, str] = {}
    for obj in obs.get('traces') or []:
        rid = obj.get('root_sample_id')
        if rid:
            if rid in covered:
                raise ObservatoryError(
                    f'sample {rid} is the root of two trace objects, {covered[rid]} and '
                    f'{obj.get("trace_id")}; one execution closed twice')
            covered[rid] = obj.get('trace_id')
    roots = [s for s in samples if not s.get('derived_parent_id')]
    uncovered = sorted(s['sample_id'] for s in roots if s.get('sample_id') not in covered)
    if uncovered:
        raise ObservatoryError(
            f'{len(uncovered)} direct sample(s) have no trace-completion object, so the record cannot say '
            f'the work they started ever finished: {uncovered[:3]}')

    # The two answers are exclusive, and one bundle may not give both. A contained command is measured INSIDE
    # its parent and reaches the observation through child derivation, so filing it under the commands this
    # selection could not measure claims its samples do not exist while they sit in the same file — and hides
    # a genuinely unmeasured command in a list a reader has learned to discount.
    both = sorted(measured & accounted)
    if both:
        raise ObservatoryError(
            f'{both} produced sample(s) and are ALSO listed among the commands this selection could not '
            f'measure; a command is measured or it is not, and this observation says both')

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


def contained_here(cmd: dict, sid: str, commands: dict, partial: bool = False) -> str | None:
    """The trace root that establishes this command in THIS state, or None if it must run itself.

    One rule, read by the expected relation, the planner and the runner alike. A command is contained in a
    state exactly when it is MEASURED in that state, it names a root, AND that root is itself required in the
    same state: then one run produces both, and scheduling the command again would acquire one relation
    twice. In any other state the root is not running, so the command has to — which is what keeps an ad hoc
    `ONLY=make.prove SCENARIO=project.cold.prover` a direct execution rather than an impossible request."""
    root_id = (cmd.get('contained_in') or '').strip()
    if not root_id:
        return None
    # The command must DECLARE this state. Three of this rule's four readers iterate a command's own
    # scenarios and so could never ask otherwise; the child derivation asks for every command under one
    # parent state, and without this the six warm-only gates were derived under all eight `make.check`
    # states. `make.claims` is measured warm and only warm: the claims gate does run inside a cold
    # acceptance trace, but the registry declares no metric there, and minting one is exactly the
    # measured-but-never-declared half of the coverage relation. R05 refused the run over 44 of them.
    if sid not in cmd.get('scenarios', ()):
        return None
    # §11 — an AD HOC run takes the smallest valid execution. Containment exists to stop the CANONICAL suite
    # paying twice for one relation; asked for one command by name, running its whole acceptance trace to
    # recover an interval is the opposite of cheap. `ONLY=make.prove` planned NINE `make.check` traces before
    # this, and `ONLY=docker.go-e2e` dragged in `make.check` to reach a stage its own producer builds. A
    # public Make target can always run itself, and the metric it yields then is a direct one — a different
    # kind, so it can never be confused with the contained interval the canonical suite records.
    if partial and cmd.get('kind') == 'make-target':
        return None
    root = commands.get(root_id)
    if root is None or sid not in root.get('scenarios', ()):
        return None
    return root_id


def expected_relation(suite: dict, canonical_only: bool = True, graph: dict | None = None,
                      partial: bool = False) -> dict:
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
                    # A stage's parent is the PROCESS whose BuildKit progress carries it. When the command
                    # that builds it is itself contained in this state, that process is the trace root, not
                    # the contained command — which never starts a buildx invocation of its own here. Leaving
                    # the parent unresolved names a sample that state never produced.
                    owner = contained_here(commands[parent], sid, commands, partial) or parent
                    spec = {'command_id': c['id'], 'scenario_id': sid, 'edit_id': edit,
                            'derived_parent_id': owner, 'selected_or_support': 'selected',
                            'resource_scope': scope, 'measurement_kind': kind, 'samples': count}
                    expected[metric_identity(spec)] = spec
            continue
        for sid in c['scenarios']:
            if canonical_only and not scenarios[sid].get('canonical'):
                continue
            edit = scenarios[sid].get('edit')
            scope, kind = scope_and_kind(c)
            # Contained IN THIS STATE: the root's single run establishes it, so the metric is a checkpoint
            # interval inside that run rather than an elapsed time of its own. The CPU and memory belong to
            # the root, and the kind differs — so this can never be pooled with the direct execution of the
            # same command in a state where the root does not run.
            owner = contained_here(c, sid, commands, partial)
            if owner:
                scope, kind = SCOPE_UNAVAILABLE, KIND_CONTAINED
            spec = {'command_id': c['id'], 'scenario_id': sid, 'edit_id': edit,
                    'derived_parent_id': owner, 'selected_or_support': 'selected',
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


# §2 — A COMPLETED SAMPLE IS NOT A COMPLETED TRACE.
#
# Per-sample validation checked that each sample was well formed and that no two shared an identity. It could
# not notice a sample that never arrived. A reviewer removed `make.prove`, `docker.prover` and `make.fcb` in
# turn from a real completed `make.check` fragment, and every mutilated fragment still passed: a lost
# checkpoint, a lost stage or a lost contained command consumed the remaining suite and failed only at R05,
# after the last trace. That is the multi-hour failure this repair exists to remove.
#
# So a trace states, when it ends, the exact relation it was required to establish and the exact relation it
# did establish, and the two must be equal in both directions with exact counts. The expected side is READ
# FROM THE PLAN — `establishes` is already the planner's own per-trace metric list — because a completion
# object that recomputed it would be a second authority against the thing it exists to check.
TRACE_MEMBERS = ('trace_id', 'command_id', 'scenario_id', 'edit_id', 'sample_index', 'root_sample_id',
                 'expected_metrics', 'observed_metrics', 'child_sample_ids', 'prime_sample_id',
                 'analysis_artifacts', 'partition', 'state')

TRACE_COMPLETE = 'complete'


def artifact_digest(artifact) -> str:
    """One digest over an analysis artifact's exact retained bytes.

    §7 E4 — the observation may hold a `module_graph` or a `history_analysis` unrelated to the samples beside
    it. Binding the artifact to the trace that established it needs one value both sides can compare, and it
    must be taken from the canonical serialisation the observation itself stores rather than from a live
    object, or the two would agree only while nothing round-tripped."""
    return _sha256(json.dumps(artifact, sort_keys=True, separators=(',', ':')).encode('utf-8'))


def trace_expectations(suite: dict, graph: dict | None, partial: bool, role_of) -> dict[tuple, list[str]]:
    """What each trace is required to establish: the registry's metrics, carrying this run's roles.

    TWO authorities, composed rather than one guessed. `expected_relation` says WHICH metrics a trace
    establishes; the selection says which ROLE each carries, and role is part of metric identity. Taking the
    planner's per-trace `establishes` instead looked equivalent and was not, for two reasons that only appear
    in an ad hoc run: the plan filters metrics by what was SELECTED, while a trace that runs produces all of
    its children regardless; and the registry states every role as `selected`, while `ONLY=make.check
    SCENARIO=project.warm.noop` legitimately makes the cold support trace's children `support` too.

    A real smoke run failed on exactly that — nine metrics observed that the filtered plan required zero
    times, every one of them a role difference or an unselected child the trace produced anyway."""
    required = expected_relation(suite, canonical_only=True, graph=graph, partial=partial)
    out: dict[tuple, list[str]] = {}
    for spec in required.values():
        owner = spec.get('derived_parent_id') or spec['command_id']
        keyed = metric_identity({**spec,
                                 'selected_or_support': role_of(spec['command_id'], spec['scenario_id'])})
        out.setdefault((owner, spec['scenario_id']), []).append(keyed)
    return {k: sorted(v) for k, v in out.items()}


def trace_id_of(command_id: str, scenario_id: str, edit_id: str | None, index: int) -> str:
    """One trace is one root EXECUTION, so the repetition index is part of its identity.

    Keying on command and scenario alone would let a second repetition overwrite the first, which is the same
    defect §6 finds in per-trace suite cost."""
    return '|'.join((command_id, scenario_id, edit_id or '-', str(index)))


OVERHEAD_SUFFIX = '.unattributed'


def partition_of(command_id: str, parent_ns: int | None, events: list[dict]) -> dict:
    """§4 — the parent's elapsed time as top-level children plus ONE retained remainder.

    Which intervals partition the parent is DERIVED, not declared twice. A hook trace writes a root anchor
    whose id is the command itself and nests its stages inside it, so the partition is the stages at depth 1.
    A Make trace writes flat siblings and no enclosing anchor, so the partition is everything at depth 0.
    Taking the top level blindly would have made `precommit.full` its own partition and reported the whole
    trace as one child covering everything.

    TWO CLOCKS. The anchors are written by `/bin/sh` from `/proc/uptime`; the parent's elapsed time is read
    by the runner. Both are monotonic and both measure the same seconds, but their epochs are unrelated, so
    an absolute `start >= parent_start` comparison would be comparing coordinates in different frames. What
    IS comparable is duration: the anchors' own span cannot exceed the parent's elapsed time, and the covered
    sum cannot either. That is the honest form of "inside the parent" across two clocks, and it still refuses
    a child that ran longer than the process containing it.

    BuildKit aggregate step work is deliberately absent: parallel steps overlap, so it is not elapsed time
    and summing it into a wall partition would be one quantity wearing another's name."""
    walls = [e for e in events if e.get('source') == 'hook-anchor' and e.get('depth') is not None]
    base = 1 if any(e['id'] == command_id and e['depth'] == 0 for e in walls) else 0
    members = sorted((e for e in walls if e['depth'] == base), key=lambda e: e['start_ns'])

    for earlier, later in zip(members, members[1:]):
        if later['start_ns'] < earlier['end_ns']:
            raise ObservatoryError(
                f'{command_id}: checkpoints {earlier["id"]!r} and {later["id"]!r} overlap, so the parent '
                f'does not partition into them and the same nanosecond is attributed twice')

    covered = sum(e['end_ns'] - e['start_ns'] for e in members)
    if parent_ns is None:
        return {'parent_ns': None, 'covered_ns': covered, 'overhead_ns': None,
                'overhead_id': f'{command_id}{OVERHEAD_SUFFIX}',
                'members': [{'id': e['id'], 'start_ns': e['start_ns'], 'end_ns': e['end_ns']}
                            for e in members]}

    span = (max(e['end_ns'] for e in members) - min(e['start_ns'] for e in members)) if members else 0
    if span > parent_ns:
        raise ObservatoryError(
            f'{command_id}: its checkpoints span {span} ns inside a parent that elapsed {parent_ns} ns, so '
            f'at least one interval lies outside the process that is supposed to contain it')
    # No separate "covered exceeds the parent" rule: members are proved pairwise non-overlapping above, so
    # their durations sum to at most their span, and the span is proved to fit the parent. A third check
    # could never fire, and a rule that cannot speak reads as protection nobody has.
    return {'parent_ns': parent_ns, 'covered_ns': covered, 'overhead_ns': parent_ns - covered,
            'overhead_id': f'{command_id}{OVERHEAD_SUFFIX}',
            'members': [{'id': e['id'], 'start_ns': e['start_ns'], 'end_ns': e['end_ns']}
                        for e in members]}


def chain_after_resume(command_id: str, chain: list[str], resume_done: set, progress=None) -> list[str]:
    """§13 — the states still to run after reusing what a resumed bundle already holds.

    ONE rule, both runners. It lived inside the shell chain loop and the analysis runner never consulted it,
    so a resumed analysis chain carried its completed traces and ran them again — a real smoke resume produced
    24 samples where 12 were carried. That is duplicate acquisition, which only R05 would have caught, at the
    end of the suite."""
    if not resume_done:
        return list(chain)
    keep = [s for s in chain if (command_id, s) not in resume_done]
    if len(keep) != len(chain) and progress:
        progress(f'fido: observe — {command_id}: {len(chain) - len(keep)} trace(s) reused from the resumed '
                 f'bundle, {len(keep)} still to run')
    return keep


def primes_from_traces(traces: list[dict], scenarios: dict) -> dict:
    """§6 D1 — the prime relation a set of resumed traces re-establishes.

    A cold trace is what fills the cache the cached, warm and incremental traces after it reuse. Resume
    carried sample rows and started `primes` empty, so a reused cold trace left every later trace in its
    chain unprimed and skipped. The identity is the retained one: a reconstructed equal peer is a different
    sample claiming the same role, which is what `sample_provenance` exists to distinguish."""
    out: dict[tuple, dict] = {}
    for t in traces or []:
        sid = t.get('scenario_id') or ''
        if not sid.startswith('project.cold.') or not t.get('root_sample_id'):
            continue
        cut = (scenarios.get(sid) or {}).get('cache_cut') or {}
        out[(t['command_id'], 'prime')] = {'id': t['root_sample_id'],
                                           'root': tuple(cut.get('invalidated_roots') or ())}
    return out


def resumable_artifacts(traces: list[dict], prior: dict) -> tuple[dict, list[str]]:
    """§6 D2 — the exact artifacts a set of resumed analysis traces established, and who cannot be resumed.

    Resume carried sample rows only, so a reused `analysis.rocq-modules` or `analysis.history` trace left
    `module_graph` and `history_analysis` null in an observation whose samples claimed the analysis had run.
    The artifact must be the one the prior bundle still holds AND must hash to what the completion object
    recorded; anything else and that trace reruns rather than inheriting a gap."""
    artifacts: dict = {}
    rerun: list[str] = []
    for t in list(traces):
        for member, want in (t.get('analysis_artifacts') or {}).items():
            have = prior.get(member)
            if have is None or artifact_digest(have) != want:
                rerun.append(f'{t["command_id"]}/{t["scenario_id"]}')
                break
            artifacts[member] = have
    return artifacts, rerun


def trace_object(root: dict, children: list[dict], expected: list[str],
                 prime_sample_id: str | None, artifacts: dict, partition: dict | None = None) -> dict:
    """One completed root execution and everything derived inside it."""
    return {
        'trace_id': trace_id_of(root['command_id'], root['scenario_id'],
                                root.get('edit_id'), root['sample_index']),
        'command_id': root['command_id'], 'scenario_id': root['scenario_id'],
        'edit_id': root.get('edit_id'), 'sample_index': root['sample_index'],
        'root_sample_id': root.get('sample_id'),
        'expected_metrics': sorted(expected),
        'observed_metrics': sorted(metric_identity(s) for s in [root] + children),
        'child_sample_ids': [s.get('sample_id') for s in children],
        'prime_sample_id': prime_sample_id,
        'analysis_artifacts': dict(artifacts),
        # §4 — validation evidence, and one place. The reviewer's near-equality on the warm `make.check`
        # trace (362,263,112,436 ns parent against 362,220,000,000 ns of anchors) was useful and unproved;
        # the 43,112,436 ns difference was retained nowhere, so nothing could tell an honest remainder from
        # a lost child.
        'partition': dict(partition) if partition is not None else None,
        'state': TRACE_COMPLETE,
    }


def trace_problems(obj: dict, expectations: dict | None = None) -> list[str]:
    """Everything that makes a retained trace object something other than a closed trace."""
    absent = [m for m in TRACE_MEMBERS if m not in obj]
    if absent:
        return [f'trace object missing member(s) {absent}; completion cannot be inferred from what is there']
    problems = []
    label = obj.get('trace_id')
    if obj['state'] != TRACE_COMPLETE:
        problems.append(f'{label}: state is {obj["state"]!r}, so this trace was retained before it closed')
    if not obj['root_sample_id']:
        problems.append(f'{label}: no direct root sample identity, so nothing binds this object to a run')

    exp, obs = list(obj['expected_metrics']), list(obj['observed_metrics'])
    # BOTH directions with exact counts. A subset check accepts a lost child, and a superset check accepts a
    # duplicate — the two defects this object exists to catch.
    for metric in sorted(set(exp) | set(obs)):
        want, got = exp.count(metric), obs.count(metric)
        if want != got:
            problems.append(f'{label}: metric {metric} was required {want} time(s) and observed {got}')
    if len(obj['child_sample_ids']) != len(obs) - 1 and obj['root_sample_id']:
        problems.append(f'{label}: {len(obj["child_sample_ids"])} child sample identity(ies) beside '
                        f'{len(obs) - 1} child metric(s); one of the two is not the truth')
    if len(set(obj['child_sample_ids'])) != len(obj['child_sample_ids']):
        problems.append(f'{label}: a child sample identity is retained twice')

    # §4 — the partition CLOSES: covered children plus the retained remainder equal the parent exactly.
    # Exactly, not approximately: both sides come from the same integers, so a tolerance here would be a
    # place for a lost child to hide.
    part = obj.get('partition')
    if part:
        ids = [m['id'] for m in part.get('members') or []]
        if len(set(ids)) != len(ids):
            problems.append(f'{label}: a checkpoint appears twice in the partition, so a nested interval is '
                            f'counted at two levels')
        recomputed = sum(m['end_ns'] - m['start_ns'] for m in part.get('members') or [])
        if recomputed != part.get('covered_ns'):
            problems.append(f'{label}: the retained covered time {part.get("covered_ns")} is not the sum of '
                            f'the retained member intervals ({recomputed})')
        if part.get('parent_ns') is not None:
            if part.get('overhead_ns') is None or part['overhead_ns'] < 0:
                problems.append(f'{label}: the uncovered remainder is {part.get("overhead_ns")!r}, so the '
                                f'parent does not partition into its children plus explicit overhead')
            elif part['covered_ns'] + part['overhead_ns'] != part['parent_ns']:
                problems.append(f'{label}: {part["covered_ns"]} covered plus {part["overhead_ns"]} '
                                f'unattributed is not the parent\'s {part["parent_ns"]} ns')
            if not part.get('overhead_id'):
                problems.append(f'{label}: the uncovered remainder is retained under no stable identity')

    if expectations is not None:
        key = (obj['command_id'], obj['scenario_id'])
        want = expectations.get(key)
        if want is None:
            problems.append(f'{label}: the current plan schedules no such trace, so this object was closed '
                            f'against an expectation the registry no longer states')
        elif sorted(want) != sorted(exp):
            problems.append(f'{label}: the retained expectation differs from the current plan '
                            f'({len(exp)} metric(s) retained, {len(want)} planned)')
    return problems


def acquisition_plan(suite: dict, sel: 'Selection', graph: dict | None = None) -> dict:
    """What a run WOULD execute, and which required metric each execution establishes.

    Derived from `expected_relation`, never restated beside it. The relation already knows every metric the
    registry requires and how each is acquired, so a planner that recomputed that from the rows would be a
    second authority — and the failure mode of a second authority here is a plan that promises coverage the
    recording rules then refuse, discovered hours later instead of before anything runs."""
    required = expected_relation(suite, canonical_only=True, graph=graph, partial=sel.partial)
    commands = {c['id']: c for c in suite['commands']}
    chosen = set(sel.selected) | set(sel.support)
    want = set(sel.scenarios)

    traces: dict[tuple, dict] = {}
    contained: list[dict] = []
    for key, spec in sorted(required.items()):
        cid, sid = spec['command_id'], spec['scenario_id']
        if cid not in chosen or sid not in want:
            continue
        cmd = commands[cid]
        owner = spec.get('derived_parent_id') or ''
        if cmd['measurement'] == 'direct' and not owner:
            row = traces.setdefault((cid, sid), {'command_id': cid, 'scenario_id': sid,
                                                 'edit_id': spec['edit_id'], 'samples': spec['samples'],
                                                 'establishes': []})
            row['establishes'].append(key)
        else:
            # Established INSIDE someone else's run: a derived stage or anchor by its parent, a contained
            # target by the root whose run reaches it in THIS state. Either way it costs no execution here.
            contained.append({'command_id': cid, 'scenario_id': sid, 'owner': owner, 'metric': key})

    for row in contained:
        anchor = (row['owner'], row['scenario_id'])
        if anchor in traces:
            traces[anchor]['establishes'].append(row['metric'])

    cataloged = [{'command_id': c['id'], 'reason': c.get('catalog_only_reason', '')}
                 for c in suite['commands'] if c['measurement'] == 'catalog-only']
    return {'traces': [traces[k] for k in sorted(traces)],
            'contained': contained,
            'cataloged': sorted(cataloged, key=lambda r: r['command_id']),
            'required_metrics': len(required),
            'trace_count': len(traces),
            'direct_executions': sum(t['samples'] for t in traces.values())}


def plan_problems(plan: dict) -> list[str]:
    """The acquisition defects §8 says recording must refuse, checked BEFORE anything runs.

    Each of these was affordable to discover here and expensive to discover at the end of a four-hour run."""
    problems = []
    seen: dict[str, str] = {}
    for trace in plan['traces']:
        for metric in trace['establishes']:
            owner = f'{trace["command_id"]}/{trace["scenario_id"]}'
            if metric in seen and seen[metric] != owner:
                problems.append(f'{metric} is claimed by two traces, {seen[metric]} and {owner}; one interval '
                                f'cannot belong to two runs')
            seen[metric] = owner
    for row in plan['contained']:
        if not row['owner']:
            problems.append(f'{row["command_id"]} in {row["scenario_id"]} is acquired inside another run but '
                            f'names no owner, so no trace establishes it')
        elif row['metric'] not in seen:
            problems.append(f'{row["command_id"]} in {row["scenario_id"]} is owned by {row["owner"]}, which '
                            f'this plan never runs in that state, so the metric could not be produced')
    return problems


def render_plan(plan: dict, sel: 'Selection', problems: list[str]) -> str:
    out = [f'fido: acquisition plan — {plan["trace_count"]} trace(s), '
           f'{plan["direct_executions"]} direct execution(s), '
           f'{len(plan["contained"])} metric(s) established inside them, '
           f'{plan["required_metrics"]} required metric(s) total',
           '', 'TRACES TO RUN']
    for t in plan['traces']:
        edit = f'  edit={t["edit_id"]}' if t['edit_id'] else ''
        out.append(f'  {t["command_id"]:<24} {t["scenario_id"]:<32}{edit}')
        out.append(f'      establishes {len(t["establishes"])} metric(s)')
    if plan['cataloged']:
        out += ['', 'CATALOGED, NOT BENCHMARKED']
        for c in plan['cataloged']:
            out.append(f'  {c["command_id"]:<24} {c["reason"][:90]}')
    out += ['', f'PARTIAL RUN — cannot record' if sel.partial else 'COMPLETE RUN — may record']
    if problems:
        out += ['', 'PLAN REFUSED']
        out += [f'  {p}' for p in problems]
    return '\n'.join(out)


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
    # §7 E3 — ALL effective timing concurrency, not only Make's. Reading `make_jobs` alone reported ordinary
    # percentage deltas across a doubling of BuildKit parallelism, which changes what a build costs at least
    # as much as Make's job count does.
    CONCURRENCY_FIELDS = ('make_jobs', 'buildkit_max_parallelism')
    b_conc = {k: (base['environment'].get('concurrency') or {}).get(k) for k in CONCURRENCY_FIELDS}
    c_conc = {k: (cand['environment'].get('concurrency') or {}).get(k) for k in CONCURRENCY_FIELDS}
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
            # NAME THE CAUSE. Effective concurrency is part of the host-class fingerprint, so a changed
            # builder configuration also changes the hash — and reporting only "different fingerprints"
            # tells a reader that something about the machine differs while withholding the one thing that
            # actually explains the timings.
            metrics.append({**row, 'classification': 'incomparable',
                            'reason': (f'effective concurrency changed ({b_conc} -> {c_conc})'
                                       if concurrency_changed
                                       else 'the two runs have different host-class fingerprints')})
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
    # §14 — the facility's own cost, compared like anything else. Without this the suite is the one thing in
    # the repository whose regressions are invisible, because `make.observe` is cataloged and can never be a
    # measured command. A baseline that predates the field says so rather than reporting a delta against
    # nothing.
    b_cost, c_cost = base.get('suite_cost') or {}, cand.get('suite_cost') or {}
    suite_cost: dict = {'comparable': bool(b_cost) and bool(c_cost)}
    if suite_cost['comparable']:
        for field in ('suite_wall_ns', 'preflight_wall_ns'):
            was, now = b_cost.get(field), c_cost.get(field)
            suite_cost[field] = {'baseline': was, 'candidate': now,
                                 'delta_ns': (now - was) if was is not None and now is not None else None}
        for field in ('direct_trace_count', 'contained_metric_count'):
            suite_cost[field] = {'baseline': b_cost.get(field), 'candidate': c_cost.get(field)}
    else:
        suite_cost['reason'] = ('one side retains no suite cost, so its own elapsed time is not a number this '
                                'comparison can rest a verdict on')
    return {'schema': SCHEMA, 'same_host_class': same_host,
            'baseline_subject': base['subject'], 'candidate_subject': cand['subject'],
            'suite_definitions': definitions, 'metrics': metrics, 'counts': counts,
            'suite_cost': suite_cost}


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
    # §14 — the suite's own cost, beside the costs it reports. It is deliberately printed apart from the
    # metric table: it is meta-evidence, not a measured command, and putting it in the same table would
    # invite it to be read as one.
    sc = cmp.get('suite_cost') or {}
    if sc.get('comparable'):
        wall, pre = sc.get('suite_wall_ns', {}), sc.get('preflight_wall_ns', {})
        lines += ['', f'SUITE COST   wall {ms(wall.get("baseline"))} -> {ms(wall.get("candidate"))} '
                      f'({ms(wall.get("delta_ns"))})   preflight {ms(pre.get("baseline"))} -> '
                      f'{ms(pre.get("candidate"))}',
                  f'             traces {sc.get("direct_trace_count", {}).get("baseline")} -> '
                  f'{sc.get("direct_trace_count", {}).get("candidate")}   contained '
                  f'{sc.get("contained_metric_count", {}).get("baseline")} -> '
                  f'{sc.get("contained_metric_count", {}).get("candidate")}']
    elif sc:
        lines += ['', f'SUITE COST   not compared: {sc.get("reason", "")}']
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


# §6 — the observatory-only serial configuration. A serial projection sums intervals and is only honest if
# they cannot overlap, so the decomposing layer has to actually be serial. `--oci-max-parallelism=1` is a real
# buildkitd flag, and `docker buildx inspect` reports it back under "BuildKit daemon flags" — which is why it
# is used instead of a buildkitd.toml the suite could set and never see again. The normal developer builder is
# untouched: this flag lives only on the observatory's own builder.
SERIAL_MAX_PARALLELISM = 1
SERIAL_MAKE_JOBS = 1
SERIAL_BUILDKITD_FLAG = f'--oci-max-parallelism={SERIAL_MAX_PARALLELISM}'
BUILDKITD_FLAGS_LINE = re.compile(r'^BuildKit daemon flags:\s*(.*)$', re.MULTILINE)
OCI_PARALLELISM = re.compile(r'--oci-max-parallelism[= ](\d+)')


def observed_builder_parallelism(name: str) -> int | None:
    """The parallelism the builder ACTUALLY reports, read back rather than assumed.

    §6 says not to set a variable and trust it. `buildx inspect` echoes the daemon flags the builder was
    created with, so a builder that predates this setting — or was made by hand without it — is visible as
    such instead of quietly producing overlapping steps under a serial label."""
    import subprocess
    probe = subprocess.run(['docker', 'buildx', 'inspect', name], capture_output=True, text=True)
    if probe.returncode != 0:
        return None
    flags = BUILDKITD_FLAGS_LINE.search(probe.stdout)
    if not flags:
        return None
    found = OCI_PARALLELISM.search(flags.group(1))
    return int(found.group(1)) if found else None


def ensure_observatory_builder() -> None:
    import subprocess
    _assert_observatory_builder(OBSERVATORY_BUILDER)
    probe = subprocess.run(['docker', 'buildx', 'inspect', OBSERVATORY_BUILDER],
                           capture_output=True, text=True)
    if probe.returncode == 0 and observed_builder_parallelism(OBSERVATORY_BUILDER) != SERIAL_MAX_PARALLELISM:
        # It exists and is NOT serial. Recreating the observatory's own builder is exactly what the guard
        # above permits, and leaving it would mean summing intervals that were free to overlap.
        subprocess.run(['docker', 'buildx', 'rm', OBSERVATORY_BUILDER], capture_output=True, text=True)
        probe.returncode = 1
    if probe.returncode != 0:
        created = subprocess.run(['docker', 'buildx', 'create', '--name', OBSERVATORY_BUILDER,
                                  '--driver', 'docker-container',
                                  '--buildkitd-flags', SERIAL_BUILDKITD_FLAG, '--bootstrap'],
                                 capture_output=True, text=True)
        if created.returncode != 0:
            raise ObservatoryError(f'could not create {OBSERVATORY_BUILDER}: {created.stderr.strip()}')
    seen = observed_builder_parallelism(OBSERVATORY_BUILDER)
    if seen != SERIAL_MAX_PARALLELISM:
        raise ObservatoryError(
            f'{OBSERVATORY_BUILDER} reports BuildKit max parallelism {seen!r}, not {SERIAL_MAX_PARALLELISM}; '
            f'a serial projection sums intervals that must not be able to overlap, so an unproved serial '
            f'builder is refused rather than trusted')


def instrumentation_env(command: dict, anchor_log: Path, scenario: dict | None = None) -> dict:
    """Switch the instrumentation on, by environment only.

    `FIDO_OBSERVE` makes the hook's anchors write instead of no-op; `BUILDKIT_PROGRESS=plain` makes buildx
    emit the structured step output the stage timings are read from. Neither changes a hook line or a Make
    recipe, so behaviour with the observatory absent is exactly what it always was."""
    env = {}
    # EVERY observed command gets a temp directory the HOST daemon can see at the same absolute path.
    # A recipe that `mktemp -d`s and then BIND-MOUNTS that path has the mount resolved by the HOST daemon,
    # which substitutes a fresh root-owned empty directory for a path existing only inside the runner. The
    # hook's staged export vanished that way. I fixed it for the hook alone — the instance I had just
    # debugged — and left the class open, so `make fcb-write`, which publishes through exactly such a mount,
    # failed identically for three more runs while an earlier recording rule masked it. Scoping a fix to the
    # instance you happen to be holding is how the second one gets to hide.
    #
    # The bundle is mounted at its own host path and is the same tmpfs as the default TMPDIR, so this is
    # visible from both sides and changes no measured cost; recipes clean up their own temp trees.
    #
    # Verifying the first one on the HOST is what let it through: there the path is already a host path, so
    # the bug cannot appear. The test has to run where the thing runs.
    command_tmp = anchor_log.parent / f'{anchor_log.stem}.tmp'
    command_tmp.mkdir(parents=True, exist_ok=True)
    env['TMPDIR'] = str(command_tmp)
    # Both kinds emit the SAME anchor grammar now, so both need the log named. Setting this for the hook
    # alone left every Make checkpoint inert during measurement: the anchors were correct, the parser was
    # correct, the registry relation was correct, and no contained metric would ever have arrived — a
    # coverage failure at the END of the suite, which is precisely the four-hour shape this repair exists to
    # stop. Found by asking what the smoke trace would prove rather than by running it.
    if command['kind'] in ('make-target', 'precommit-full'):
        env['FIDO_OBSERVE'] = str(anchor_log)
        env['BUILDKIT_PROGRESS'] = 'plain'
    return env


def declared_anchor_ids(suite: dict, root: Path) -> set:
    """Every checkpoint identity the SOURCES declare, taken from those sources.

    §3 refuses an unknown checkpoint, and the set it is refused against has to be the one the rest of the
    tool already reads. My first version used the command ids alone and refused a real run over
    `make.check-body` — which the coverage gate has always known about, because `<command>-body` is the
    declared form for a compound recipe's own unowned segment that §4 requires to be named rather than folded
    into its parent. A narrower vocabulary here is not caution; it rejects work the registry does declare."""
    return ({c['id'] for c in suite['commands']}
            | set(make_anchor_pairs(root)) | set(hook_anchor_pairs(root)))


def collect_events(command: dict, anchor_log: Path, raw_log: Path,
                   known_anchors: set | None = None) -> list[dict]:
    """Every derived event this sample produced, from whichever instrumentation applies to it."""
    events = []
    if anchor_log.is_file():
        events.extend(parse_anchor_log(read_text(anchor_log, 'hook anchor log'), known_anchors))
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
                    progress=_flushed, checkpoint=None,
                    resume_done: set | None = None,
                    resume_samples: list | None = None,
                    resume_traces: list | None = None,
                    resume_artifacts: dict | None = None,
                    clock: 'ValidationClock | None' = None,
                    repeat: int = 1) -> tuple[dict, list[str], bool]:
    """Execute the selection as PER-ROOT MEASUREMENT CHAINS and return the observation.

    The first candidate primed once per scenario and then ran every command in that shared state, so a
    command labelled cold observed a cache an earlier measured command had filled. Here each root command
    owns its chain: its cold sample invalidates its own declared root, and everything cached, warm or
    incremental in that chain names the exact prime sample it reused.

    Isolation is by INVALIDATION rather than by namespace. A root forced to rebuild cannot be satisfied by
    anything another command left behind, which is what makes one shared builder honest."""
    import datetime
    import os as _os
    import subprocess as _subprocess
    commands = {c['id']: c for c in suite['commands']}
    scenarios = {s['id']: s for s in suite['scenarios']}
    edits = {e['id']: e for e in suite.get('edits', [])}
    derived_ids = {c['id'] for c in suite['commands'] if c['measurement'] == 'derived'}

    def contained_ids_for(parent_id: str, scenario_id: str) -> set:
        """Only the CONTAINED public commands, whose intervals carry the contained kind."""
        return {c["id"] for c in suite["commands"]
                if contained_here(c, scenario_id, commands, sel.partial) == parent_id}

    def child_ids_for(parent_id: str, scenario_id: str) -> set:
        """Which events this parent's run may turn into samples, in THIS state.

        Derived stages and hook anchors always qualify. A CONTAINED command qualifies only where its trace
        root is this parent and this state — which is the same `contained_here` rule the expected relation
        and the planner read, so the runner cannot produce a child the relation does not require, or omit
        one it does. The smoke trace found this: every contained interval was in the anchor log and none
        reached the observation, because the runner accepted `derived` commands alone."""
        return derived_ids | {c["id"] for c in suite["commands"]
                              if contained_here(c, scenario_id, commands, sel.partial) == parent_id}

    # The canonical order, and every step of it is load-bearing.  Capturing the environment BEFORE the
    # builder existed described a builder the suite then replaced: on first use the observation named one
    # builder and the samples ran against another.  Priming stable infrastructure before the environment is
    # read means the recorded identities are the ones the samples actually used, and that the toolchain
    # download is outside every measured interval rather than inside the first cold sample.
    # §14 — the suite's own clock starts here, on the SAME monotonic source every measured interval uses, so
    # its cost and the costs it reports are the same kind of number.
    suite_t0 = _monotonic_ns()
    suite_started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    subj = subject(root)
    ensure_observatory_builder()
    preflight = toolchain_prime(root, progress)
    preflight_ns = _monotonic_ns() - suite_t0
    env = environment(root)
    env['preflight'] = preflight
    # The Dockerfile's own stage graph, so a cold sample can be asked what ELSE rebuilt and not merely
    # whether its declared root did, and its COPY set, so an incremental sample can be asked whether the
    # edit it made could have invalidated anything at all.
    stage_graph = docker_stage_graph(root)
    context_inputs = docker_context_inputs(root)

    # §13 — reused samples seed the record so the coverage relation sees the whole suite, not only what this
    # invocation ran. They arrive already validated: `resumable_traces` refuses a bundle that does not, and
    # offers only traces that completed.
    samples: list[dict] = list(resume_samples or [])
    resume_done = resume_done or set()
    incomplete: list[str] = []
    unmeasured: list[str] = []
    edits_ok = True
    graph, history = None, None
    primes: dict[tuple, dict] = {}          # (command_id, root) -> the exact prime sample identity

    # §6 D1/D2 — a resumed trace restores the CAUSAL state it established, or it is not resumed at all.
    #
    # `primes` started empty on every resumed run. A cold trace reused from the prior bundle is removed from
    # the chain, so the prime it would have offered was never recorded, and `sample_provenance` then found no
    # prime for the cached, warm and incremental traces that depend on it — each skipped as unprimed. The
    # only resume demonstrated so far used a warm-only command, which is precisely the shape that cannot
    # exhibit the defect. The prime is taken from the retained completion object rather than reconstructed:
    # a reconstructed equal peer is a different sample claiming the same role.
    primes.update(primes_from_traces(resume_traces or [], scenarios))
    # The artifact itself, not a stub naming it. The prior bundle holds the exact object its analysis trace
    # established; the caller has already required its digest to equal the one that trace retained, so what
    # is restored here is the evidence rather than a reference to it.
    graph = (resume_artifacts or {}).get('module_graph', graph)
    history = (resume_artifacts or {}).get('history_analysis', history)

    traces: list[dict] = list(resume_traces or [])
    expectations = trace_expectations(suite, stage_graph, sel.partial,
                                      lambda cid, sid: sample_role(sel, cid, sid))

    def emit(sample: dict):
        # Stamped HERE, in the one place every sample passes through, rather than in each of the three
        # constructors — a fourth constructor would otherwise be one more chance to forget.
        sample['sample_id'] = sample_id_for(run_id, sample)
        samples.append(sample)
        if checkpoint:
            checkpoint(samples, incomplete, traces)

    def close_trace(root_sample: dict, children: list[dict], prime_sample_id: str | None,
                    artifacts: dict, events: list[dict] | None = None) -> None:
        """§2 — the trace states what it owed and what it produced, and the two must agree HERE.

        Not at recording. A lost checkpoint, a lost Docker stage or a lost contained command that surfaces at
        the final rule has already spent every remaining trace, which is the multi-hour failure this replaces.
        The expected side is the planner's own `establishes` list, so this cannot drift from the plan it
        checks."""
        obj = trace_object(root_sample, children,
                           expectations.get((root_sample['command_id'], root_sample['scenario_id']), []),
                           prime_sample_id, artifacts,
                           partition_of(root_sample['command_id'], root_sample.get('wall_ns'),
                                        events or []))
        bad = trace_problems(obj, expectations)
        if bad:
            raise ObservatoryError(
                f'trace {obj["trace_id"]} did not close: {bad[0]}'
                + (f' (and {len(bad) - 1} more)' if len(bad) > 1 else ''))
        traces.append(obj)
        if checkpoint:
            checkpoint(samples, incomplete, traces)

    for cid in sel.order:
        command = commands[cid]
        if runner_for(command) != 'shell':
            continue
        # WHETHER this selection holds any state of this command is decided HERE, on the declared chain,
        # before anything is elided from it. An elision means the state is measured somewhere else, which is
        # the opposite of unmeasured, and the two answers were about to be filed under one name: a fully
        # contained command emits samples through child derivation, so it would have been reported as
        # measured AND as impossible to measure, in the same bundle.
        chain = [s for s in scenario_order(suite, sel.scenarios) if s in command['scenarios']]
        if not chain:
            # Selected, and this selection holds no state of it. Silence here would leave the command listed
            # as selected with no sample beside it and no reason, which reads as a measurement that went missing.
            unmeasured.append(cid)
            progress(f'fido: observe — {cid} has no scenario in this selection ('
                     f'{", ".join(command["scenarios"])}), so it contributes no sample')
            continue
        # §8 — a relation an exact containing trace already measures is NOT executed here. The plan says so,
        # the expected relation says so, and the runner has to say the same or the two disagree: PLAN
        # scheduled ONE `make.prove` trace while the runner ran six, re-running precisely the work the trace
        # cover exists to remove and heading for a duplicate-acquisition refusal at the end of the suite. The
        # rule is `contained_here`, the same one the relation, the planner and the child derivation read.
        contained_away = [s for s in chain if contained_here(command, s, commands, sel.partial)]
        if contained_away:
            chain = [s for s in chain if s not in contained_away]
            progress(f'fido: observe — {cid}: {len(contained_away)} state(s) measured inside '
                     f'{command["contained_in"]}, not run again here')

        # §13 — a trace this bundle already completed is not rerun. The filter is per SCENARIO rather than
        # per command, so an interrupted chain resumes at the scenario it stopped in instead of from the top;
        # only complete, individually validated fragments reach `resume_done` at all. The rule is shared with
        # the analysis runner, which is where it was missing.
        chain = chain_after_resume(cid, chain, resume_done, progress)
        if not chain:
            # Every declared state was elided, so all of them are accounted for — inside a containing trace,
            # or by the resumed bundle that already holds them. Nothing runs here and nothing is missing.
            progress(f'fido: observe — {cid}: nothing left to run; every selected state is measured '
                     f'{"inside " + command["contained_in"] if contained_away else "in the resumed bundle"}')
            continue
        progress(f'fido: observe — chain {cid}: {", ".join(chain)}')

        # ONE disposable tree per CHAIN, not one per sample.
        #
        # A fresh copy per sample is a fresh Docker build CONTEXT per sample, and its COPY layers cannot hit
        # the cache the chain's earlier samples filled: measured directly, an ARCHITECTURE.md-only edit —
        # which no stage copies — re-ran every COPY step and rebuilt the theory for 123.2s. So every
        # incremental sample was measuring "build in a new directory", not "the cost of this edit", and a
        # leaf edit came out the same as a critical-path edit because neither edit was what rebuilt.
        #
        # Sharing one tree across the chain makes the edit the ONLY difference between a warm sample and the
        # incremental sample after it. The chain's cold sample pays the new-tree cost, which is correct: a
        # cold sample rebuilds its declared roots by definition.
        chain_copy = None
        if command.get('isolation') == 'disposable-copy' or any(
                scenarios[s].get('edit') for s in chain):
            chain_copy = raw_dir.parent / 'copies' / cid
            chain_copy.parent.mkdir(parents=True, exist_ok=True)
            disposable_copy(root, chain_copy, subj['source_view'])
            # And PRIME it, outside every measured interval.
            #
            # A new tree is a new Docker build context, so the first build in it rebuilds every stage whose
            # COPY reads that context — not only the root a cold scenario declares. Measured directly, a
            # cold `make.e2e` in a fresh tree rebuilt `emit`, which is UPSTREAM of its declared `go-e2e`
            # root, and the cut checker refused the sample for describing less work than it did. It was
            # right to: the sample was measuring the tree's newness on top of its declared cut.
            #
            # Same principle as the toolchain preflight. What a project-cold scenario means is "everything
            # present except this root and its descendants", so the tree has to be warm before the cut can
            # mean anything.
            if command.get('build_targets'):
                progress(f'fido: observe — priming {cid} tree (outside every measured interval)')
                done = _subprocess.run(materialise_execution(command, None, OBSERVATORY_BUILDER),
                                       cwd=str(chain_copy), capture_output=True, text=True)
                if done.returncode != command['expected_exit']:
                    # The REASON, not only the code. Reporting the exit status alone cost a whole diagnosis
                    # cycle: the prime was failing because the copy was a linked worktree whose gitdir the
                    # container could not resolve, and the message said none of that.
                    why = ((done.stderr or done.stdout).strip().splitlines() or ['no output'])[-1][:200]
                    incomplete.append(f'{cid}: the chain tree prime exited {done.returncode} ({why}), so '
                                      f'every sample in this chain would measure an unprimed tree')
                    drop_disposable_copy(root, chain_copy)
                    continue
        elif command.get('build_targets') and command['side_effect'] == 'none':
            # A chain with no tree of its own still needs a warm one, and `precommit.full` is the case that
            # proves it: the hook EXPORTS the staged index into a fresh directory on every run, so its first
            # build of a subject reads a context BuildKit has never seen. Measured directly, a cold hook run
            # under a `prover` cut also rebuilt `emit`'s last two steps, and the root-closure check refused
            # the sample for describing less work than it did.
            #
            # One unmeasured run first, so the cache has seen this subject's bytes before anything is timed.
            # Restricted to commands that change nothing: priming a writer would be a side effect nobody
            # asked for, performed outside the record.
            progress(f'fido: observe — priming {cid} (outside every measured interval)')
            done = _subprocess.run(materialise_execution(command, None, OBSERVATORY_BUILDER),
                                   cwd=str(root), capture_output=True, text=True,
                                   env={**_os.environ,
                                        **instrumentation_env(command, raw_dir / f'{cid}.prime.anchors')})
            if done.returncode != command['expected_exit']:
                why = ((done.stderr or done.stdout).strip().splitlines() or ['no output'])[-1][:200]
                incomplete.append(f'{cid}: the chain prime exited {done.returncode} ({why}), so every '
                                  f'sample in this chain would measure an unprimed cache')
                continue

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
            wanted = wanted_samples(command, scenario_id, role, repeat)

            for index in range(wanted):
                label = f'{cid}/{scenario_id}' + (f'/{edit["id"]}' if edit else '')
                progress(f'fido: observe — {label} sample {index + 1}/{wanted} ({role})')
                copy = None
                scratch = None
                try:
                    iso_kind = command.get('isolation')
                    iso_env = {}
                    if chain_copy is not None:
                        copy = chain_copy           # the chain's one tree; see the note above the loop
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
                                                edit['id'] if edit else None) + '.log'),
                        # §3 — an UNKNOWN checkpoint is refused, against the vocabulary the registry, the
                        # Makefile and the hook actually declare, so a log naming work none of them declares
                        # cannot quietly become a metric.
                        known_anchors=declared_anchor_ids(suite, root))
                    check_cut_observed(s, scenario, suite, stage_graph)
                    if edit:
                        check_edit_effect(s, edit, command, context_inputs)
                    emit(s)
                    kids = list(derive_child_samples(
                        s, s['derived_stage_events'], child_ids_for(cid, scenario_id),
                        contained=contained_ids_for(cid, scenario_id),
                        role_of=lambda kid: sample_role(sel, kid, scenario_id)))
                    for child in kids:
                        emit(child)
                    if edit:
                        restore_and_verify(target, edit, original, before, [edit['path']], index)
                    if scenario_id.startswith('project.cold.') and s['status'] == 'ok':
                        primes[(cid, 'prime')] = {'id': s['sample_id'], 'root': root_stage}
                    # Every child and artifact is emitted; only now can the trace say it closed.
                    close_trace(s, kids, provenance.get('prime_sample_id'), {}, s['derived_stage_events'])
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
                    elif copy is not None and copy is not chain_copy:
                        drop_disposable_copy(root, copy)

        # The chain's tree outlives its samples and is dropped once, here — dropping it per sample is what
        # made every sample build in a new directory.
        if chain_copy is not None:
            drop_disposable_copy(root, chain_copy)

    for cid in sel.order:
        command = commands[cid]
        if runner_for(command) != 'analysis':
            continue
        # Chain order, same as the shell runner: a cold sample fills the cache before a warm one reuses it.
        # Iterating the selection's order ran the warm sample first whenever the selection listed it first.
        #
        # §13 — and the SAME resume filter as the shell runner. It was applied only there, so a resumed
        # analysis chain carried its completed traces AND ran them again: a real smoke resume produced 24
        # samples where 12 were carried, which is duplicate acquisition that only R05 would have caught, at
        # the end of the suite. Two runners, one rule.
        analysis_chain = chain_after_resume(
            cid, [s for s in scenario_order(suite, sel.scenarios) if s in command['scenarios']],
            resume_done, progress)
        for scenario_id in analysis_chain:
            scenario = scenarios[scenario_id]
            role = sample_role(sel, cid, scenario_id)
            provenance, skip = sample_provenance(command, scenario, primes)
            if skip:
                incomplete.append(f'{cid}/{scenario_id}')
                progress(f'fido: observe — {skip}')
                continue
            wanted = wanted_samples(command, scenario_id, role, repeat)
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
                    kids = list(derive_child_samples(
                        s, events, child_ids_for(cid, scenario_id),
                        contained=contained_ids_for(cid, scenario_id),
                        role_of=lambda kid: sample_role(sel, kid, scenario_id)))
                    for child in kids:
                        emit(child)
                    # §6 D2 — the ARTIFACT this trace established, named by the trace that established it.
                    # Resume carried sample rows only, so a reused analysis trace left `module_graph` and
                    # `history_analysis` null while its samples claimed the analysis had happened.
                    artifacts = {}
                    if command['kind'] == 'history-analysis' and history is not None:
                        artifacts['history_analysis'] = artifact_digest(history)
                    elif graph is not None:
                        artifacts['module_graph'] = artifact_digest(graph)
                    close_trace(s, kids, provenance.get('prime_sample_id'), artifacts, events)
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

    # Per-trace wall time is the elapsed time of each ROOT execution — the direct samples. A contained metric
    # is inside one of those, so adding it here would count the same nanoseconds twice.
    direct = [s for s in samples if not s.get('derived_parent_id')]
    suite_cost = {
        'suite_started': suite_started,
        'suite_completed': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'suite_wall_ns': _monotonic_ns() - suite_t0,
        'preflight_wall_ns': preflight_ns,
        # §7 E1 — the facility's own checking cost, kept apart from what it measured.
        'validation_wall_ns': (clock.total_ns() if clock else 0),
        'validation_components': dict(clock.components) if clock else {},
        # §6 D4 — keyed by the EXACT trace, repetition index and all. `command|scenario` let ad hoc repeated
        # traces overwrite each other, so a five-repetition investigation retained one cost and the suite's
        # own accounting silently disagreed with the run that produced it.
        'trace_wall_ns': {trace_id_of(s['command_id'], s['scenario_id'],
                                      s.get('edit_id'), s['sample_index']): s.get('wall_ns')
                          for s in direct if s.get('wall_ns') is not None},
        'direct_trace_count': len(direct),
        'contained_metric_count': sum(1 for s in samples if s.get('derived_parent_id')),
    }

    observation = {
        'schema': SCHEMA, 'suite_digest': suite_digest_of(suite), 'run_id': run_id,
        'subject': subj, 'environment': env,
        'cache_model': {s: scenarios[s]['cache_cut'] for s in sel.scenarios if s in scenarios},
        'commands': command_fingerprints(suite), 'definitions': definition_fingerprints(suite),
        'measurements': samples, 'traces': traces,
        'module_graph': graph, 'history_analysis': history, 'derived': derived,
        # What was asked for, and what the tool added on its own to make the answer mean anything. A reader
        # who sees a cold build in a warm-only run is owed the reason in the bundle, not in the terminal
        # scrollback that outlived it.
        'selection': {'partial': sel.partial, 'commands_selected': sorted(sel.selected),
                      'commands_support': sorted(sel.support), 'scenarios': list(sel.scenarios),
                      'scenarios_added_as_support': list(sel.scenario_support),
                      'commands_with_no_scenario_here': sorted(unmeasured),
                      'commands_never_measured': sorted(
                          c['id'] for c in suite['commands'] if c['measurement'] == 'catalog-only')},
        # §14 — THE FACILITY'S OWN COST, retained as meta-evidence rather than measured as a command. It is
        # not a recursive observation: nothing here is a sample, nothing enters the coverage relation, and
        # `make.observe` stays cataloged. What it buys is that another multi-hour regression in the suite
        # cannot hide behind the one command the observatory is forbidden to measure. The last one was found
        # by a human noticing four hours had passed.
        'suite_cost': suite_cost,
    }
    # The producer answers to the SAME member list the validator reads, here, where a divergence is a bug in
    # this function rather than a mystery four hours later at the last recording rule.
    if set(observation) != set(OBSERVATION_MEMBERS):
        raise ObservatoryError(
            f'the observation this run assembled does not match the declared member set: '
            f'missing {sorted(set(OBSERVATION_MEMBERS) - set(observation))}, '
            f'unexpected {sorted(set(observation) - set(OBSERVATION_MEMBERS))}')
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
  make observe PLAN=1                 the exact acquisition plan; runs nothing and cannot record
  make observe RESUME=<bundle>        reuse an exact same-subject bundle's completed traces
  make observe REPEAT=<n>             ad hoc repetition of a NAMED selection; never with RECORD=1
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

    def edit_makefile(work: Path, old: str, new: str):
        """One exact substitution in the working copy's Makefile, refusing an ambiguous target.

        A control that silently matched nothing would prove the rule load-bearing while changing no rule."""
        p = work / 'Makefile'
        text = p.read_text(encoding='utf-8')
        if text.count(old) != 1:
            raise ObservatoryError(f'the control needs exactly one {old!r} in the Makefile, '
                                   f'found {text.count(old)}')
        p.write_text(text.replace(old, new), encoding='utf-8')

    scenario('the canonical registry classifies the whole live surface', lambda w: w)

    scenario('a public Make target absent from the registry',
             lambda w: drop(w, 'make.diet'),
             expect="has 'make.diet' with no registry entry")

    # §7/§16 — the Make checkpoint relation, both directions and paired.
    scenario('a Make checkpoint that begins and never ends',
             lambda w: edit_makefile(w, '\t$(call fido_anchor,end,make.names)\n', ''),
             expect='begin and never end')
    scenario('a Make checkpoint naming nothing the registry knows',
             lambda w: (edit_makefile(w, '$(call fido_anchor,begin,make.names)',
                                      '$(call fido_anchor,begin,make.nonesuch)'),
                        edit_makefile(w, '$(call fido_anchor,end,make.names)',
                                      '$(call fido_anchor,end,make.nonesuch)')),
             expect='neither a registry command nor the')
    scenario('a public Make target with no checkpoint and no catalog reason',
             lambda w: (edit_makefile(w, '\t$(call fido_anchor,begin,make.names)\n', ''),
                        edit_makefile(w, '\t$(call fido_anchor,end,make.names)\n', '')),
             expect='no checkpoint and no catalog reason')
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
    # The policy this repair deleted, reinstated: three warm executions of every command, and sixty
    # incremental ones once crossed with five edit shapes over four overlapping commands.
    scenario('canonical triplicate sampling',
             lambda w: edit(w, 'make.diet', 'samples', {'project.warm.noop': 3}),
             expect='canonical acquisition is ONE real trace per identity')
    # §3B.3 — the containment relation. `make.names` is contained in `make.check`, so these edit a real
    # contained row rather than inventing one the registry has never seen.
    scenario('a trace root that does not exist',
             lambda w: edit(w, 'make.names', 'contained_in', 'make.nonesuch'),
             expect='not a command in this registry')
    scenario('a command naming itself as its trace root',
             lambda w: edit(w, 'make.names', 'contained_in', 'make.names'),
             expect='names itself as its trace root')
    scenario('containment chained through a second contained command',
             lambda w: edit(w, 'make.names', 'contained_in', 'make.claims'),
             expect='containment does not chain')
    scenario('a derived stage claiming to be contained in a run',
             lambda w: edit(w, 'docker.prover', 'contained_in', 'make.check'),
             expect='only a command that runs can also be contained')
    scenario('a trace root that is not a command which runs',
             lambda w: edit(w, 'make.names', 'contained_in', 'make.observe'),
             expect='a trace root has to be something that runs')


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
    # Turning a cataloged stage back into a derived one restores the exact state that survived to the last
    # recording rule of a four-hour run: a child whose only producer never runs.
    scenario('a derived child whose every producer is cataloged',
             lambda w: edit(w, 'docker.python-tools', 'measurement', 'derived'),
             expect='every command that could produce it is cataloged')
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
    # These edit a command that still RUNS. `make.diet` used to serve here and is now contained, so the same
    # edits trip the containment rules first and prove a different rule than the one being asked about.
    scenario('a scenario reference with no sample count',
             lambda w: (edit(w, 'make.emit', 'scenarios', ['project.cold.emit', 'project.warm.noop']),
                        edit(w, 'make.emit', 'samples', {'project.cold.emit': 1})),
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
             lambda w: edit(w, 'make.fmt', 'invalidation_roots', ['prover']),
             expect='a command rebuilds exactly the roots it can be measured cold from')
    scenario('a derived command claiming it invalidates something',
             lambda w: edit(w, 'docker.prover', 'invalidation_roots', ['prover']),
             expect='it performs no build of its own')

    scenario('an unknown scenario reference',
             lambda w: (edit(w, 'make.fmt', 'scenarios', ['no.such.scenario']),
                        edit(w, 'make.fmt', 'samples', {'no.such.scenario': 1})),
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
    cold_only = select(suite, only='make.check', scenario='project.cold.acceptance')
    if cold_only.scenario_support:
        failures.append(f'a cold selection needs no prime added: {cold_only.scenario_support}')

    combo = selection('ONLY and SCENARIO combine', only='make.check', scenario='project.warm.noop')
    if combo:
        # ONE cold prime, not one per cold state. `make.check` used to name a cold scenario per stage, which
        # made a warm selection drag in three cold traces; the compound acceptance cut is a single state that
        # leaves the cache warm for what follows.
        expect_that('a combined selection keeps the named scenario and its required prime',
                    set(combo.scenarios) == {'project.warm.noop', 'project.cold.acceptance'},
                    f'scenarios were {combo.scenarios}')

    # §6 — the serial configuration is READ BACK, not declared. A projection sums intervals and is honest
    # only if they could not overlap, so an unproved serial builder must be refused rather than trusted.
    counts['total'] += 1
    if OCI_PARALLELISM.search(SERIAL_BUILDKITD_FLAG) is None:
        failures.append('the serial buildkitd flag the observatory sets is not one it can read back, so the '
                        'configuration could never be verified')
    for flags, want in (('--oci-max-parallelism=1 --allow-insecure-entitlement=network.host', 1),
                        ('--oci-max-parallelism 4', 4),
                        ('--allow-insecure-entitlement=network.host', None)):
        decoded = OCI_PARALLELISM.search(flags)
        got = int(decoded.group(1)) if decoded else None
        if got != want:
            failures.append(f'observed parallelism decoded as {got!r} from {flags!r}, wanted {want!r}')

    counts['total'] += 1
    serial = _concurrency({'BuildKit daemon flags': '--oci-max-parallelism=1', 'Platforms': 'linux/amd64'})
    if serial['buildkit_max_parallelism'] != 1 or serial['buildkit_parallelism_source'] != 'builder-daemon-flags':
        failures.append(f'a serial builder was not recorded as serial from its own flags: {serial}')
    unproved = _concurrency({'Platforms': 'linux/amd64'})
    if unproved['buildkit_max_parallelism'] is not None \
            or unproved['buildkit_parallelism_source'] != 'not-reported':
        failures.append(f'a builder reporting no parallelism flag was recorded as though it had one: '
                        f'{unproved}')

    # THE CONTAINMENT RELATION ITSELF. The same command is contained where its root runs and direct where it
    # does not — which keeps §11's `ONLY=make.prove SCENARIO=project.cold.prover` a real execution rather than
    # an impossible request, while the canonical states cost no second run.
    counts['total'] += 1
    cmds = {c['id']: c for c in suite['commands']}
    if contained_here(cmds['make.names'], 'project.warm.noop', cmds) != 'make.check':
        failures.append('a command was not contained in a state its trace root runs, so the suite would '
                        'execute it a second time for a metric the root already establishes')
    # A state `make.prove` DECLARES and `make.check` does not, so only the root rule can decide it. Asking
    # this of `make.names` in a state it never declares let the command-declares-the-state rule answer first,
    # and the control then passed whatever the root rule did — a control that cannot fail for its own reason.
    if contained_here(cmds['make.prove'], 'project.cold.prover', cmds) is not None:
        failures.append('a command was reported contained in a state its trace root never runs, so the plan '
                        'would promise a metric no trace produces')
    # And the other half: a state the COMMAND does not declare is not contained either, whatever its root
    # does. `make.names` is measured warm and only warm; the naming gate does run inside a cold acceptance
    # trace, but the registry declares no metric there and minting one is a metric nobody declared.
    if contained_here(cmds['make.names'], 'project.cold.acceptance', cmds) is not None:
        failures.append('a command was reported contained in a state it does not declare, so a trace would '
                        'mint a metric the registry never asked for')
    if contained_here(cmds['make.check'], 'project.warm.noop', cmds) is not None:
        failures.append('a command naming no trace root was reported contained')

    # ── §8 the acquisition plan. It is computed from the SAME expected relation the recording rules close
    # over, so a plan that passes here and a run that fails at the end would mean the two had drifted.
    counts['total'] += 1
    canonical_sel = select(suite)
    canonical_plan = acquisition_plan(suite, canonical_sel, graph=docker_stage_graph(root))
    canonical_problems = plan_problems(canonical_plan)
    if canonical_problems:
        failures.append(f'the canonical plan refuses itself: {canonical_problems[0]}')
    if canonical_plan['trace_count'] < 1 or canonical_plan['required_metrics'] < 1:
        failures.append(f'the canonical plan measures nothing: {canonical_plan["trace_count"]} trace(s)')
    # Every trace the plan schedules must establish at least the metric it was scheduled for; a trace that
    # establishes nothing is an execution nobody asked for.
    barren = [t for t in canonical_plan['traces'] if not t['establishes']]
    if barren:
        failures.append(f'{len(barren)} scheduled trace(s) establish no metric, e.g. {barren[0]}')

    counts['total'] += 1
    orphan = {'traces': [], 'contained': [{'command_id': 'make.prove', 'scenario_id': 'project.warm.noop',
                                           'owner': 'make.check', 'metric': 'm'}],
              'cataloged': [], 'required_metrics': 1, 'trace_count': 0, 'direct_executions': 0}
    if not any('could not be produced' in p for p in plan_problems(orphan)):
        failures.append('a contained metric whose owner the plan never runs was accepted')

    counts['total'] += 1
    ownerless = {'traces': [], 'contained': [{'command_id': 'make.prove', 'scenario_id': 'project.warm.noop',
                                              'owner': '', 'metric': 'm'}],
                 'cataloged': [], 'required_metrics': 1, 'trace_count': 0, 'direct_executions': 0}
    if not any('names no owner' in p for p in plan_problems(ownerless)):
        failures.append('a metric acquired inside a run that names no owner was accepted')

    counts['total'] += 1
    twice = {'traces': [{'command_id': 'make.check', 'scenario_id': 'project.warm.noop', 'edit_id': None,
                         'samples': 1, 'establishes': ['m']},
                        {'command_id': 'make.e2e', 'scenario_id': 'project.warm.noop', 'edit_id': None,
                         'samples': 1, 'establishes': ['m']}],
             'cataloged': [], 'contained': [], 'required_metrics': 1, 'trace_count': 2,
             'direct_executions': 2}
    if not any('claimed by two traces' in p for p in plan_problems(twice)):
        failures.append('one metric claimed by two traces was accepted; an interval cannot belong to two runs')

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

    # §7 E4 — the fixture's analysis samples come WITH the artifacts they establish, because that is what the
    # producer emits. A fixture holding an analysis sample and a null artifact describes the defect, not the
    # system, and every observation built on it would be exercising a shape no run can produce.
    FIXTURE_DEP = ('A.vo A.glob A.v.beautified: A.v /opt/rocq/rocqworker\n'
                   'B.vo B.glob B.v.beautified: B.v A.vo\n')
    FIXTURE_WALL = {'A': 1_000, 'B': 2_000}
    FIXTURE_HISTORY = {'views': {'excluding_campaign': {'edit_count_by_file': {'A.v': 3}}}}

    def fixture_artifacts(samples: list[dict]) -> dict:
        """Which artifacts a set of samples establishes, keyed by the member each analysis command owns."""
        out = {}
        for s in samples:
            if s.get('derived_parent_id'):
                continue
            if s['command_id'] == 'analysis.rocq-modules':
                out['module_graph'] = parse_module_graph(FIXTURE_DEP, FIXTURE_WALL)
            elif s['command_id'] == 'analysis.history':
                out['history_analysis'] = FIXTURE_HISTORY
        return out

    def fixture_environment(**over) -> dict:
        """An environment whose fingerprint is what its own fields produce.

        Modelling a DIFFERENT host class means changing a field — a different CPU, a different job count —
        and letting the hash follow. Changing only the hash models nothing that can happen."""
        env = {**{k: 'x' for k in REQUIRED_ENVIRONMENT},
               'concurrency': {'make_jobs': 1, 'buildkit_max_parallelism': 1},
               'base_image_digests': {}, 'toolchain_versions': {}}
        env.update(over)
        env['host_class_fingerprint'] = host_class_fingerprint(env)
        return env

    def fixture_suite_cost(samples: list[dict], **over) -> dict:
        """Suite cost derived from the samples it accompanies, exactly as the producer derives it."""
        direct = [s for s in samples if not s.get('derived_parent_id')]
        cost = {'suite_started': '2026-01-01T00:00:00+00:00',
                'suite_completed': '2026-01-01T00:01:00+00:00',
                'suite_wall_ns': 60_000_000_000, 'preflight_wall_ns': 1_000_000_000,
                'validation_wall_ns': 3, 'validation_components': {'preflight_controls': 2, 'per_trace': 1},
                'trace_wall_ns': {trace_id_of(s['command_id'], s['scenario_id'],
                                              s.get('edit_id'), s['sample_index']): s['wall_ns']
                                  for s in direct if s.get('wall_ns') is not None},
                'direct_trace_count': len(direct),
                'contained_metric_count': len(samples) - len(direct)}
        cost.update(over)
        return cost

    def traces_for(samples: list[dict]) -> list[dict]:
        """One closed trace per direct sample, through the REAL constructor.

        Any fixture that rewrites `measurements` after construction must rebuild these too. A control that
        replaced every sample's resource scope left the traces claiming the identities the samples used to
        have — which the new rules correctly refused, and which is the fixture lying rather than the rule
        being wrong."""
        out = []
        for rootsample in samples:
            if rootsample.get('derived_parent_id'):
                continue
            kids = [k for k in samples
                    if k.get('derived_parent_id') == rootsample['command_id']
                    and k.get('scenario_id') == rootsample['scenario_id']]
            mine = {m: artifact_digest(a) for m, a in fixture_artifacts([rootsample]).items()}
            out.append(trace_object(rootsample, kids,
                                    [metric_identity(s) for s in [rootsample] + kids], None, mine))
        return out

    def observation(samples=None, **over) -> dict:
        samples = samples if samples is not None else [sample(sample_index=i, wall_ns=n)
                                                       for i, n in enumerate((900_000, 1_000_000, 1_100_000))]
        base = {'schema': SCHEMA, 'suite_digest': digest, 'run_id': 'run-fixture',
                'subject': {'commit': 'a' * 40, 'tree': 'b' * 40, 'inventory_digest': 'c' * 64,
                            'dirty': False, 'source_view': 'committed-tree'},
                # §7 E3 — the fixture's fingerprint is DERIVED from its own fields, like the producer's. A
                # hand-written hash described a host the fields did not, which is the defect itself.
                'environment': fixture_environment(),
                'cache_model': {}, 'commands': {'make.fmt': 'f0' * 32},
                'definitions': {'commands': {'make.fmt': 'f0' * 32}, 'scenarios': {}, 'edits': {},
                                'stable_through': 'rocq-base'},
                'measurements': samples,
                # §2 — one closed trace per DIRECT sample, built by the real constructor from the samples
                # this fixture holds. Hand-writing them would let the fixture describe a completion shape the
                # producer never emits, which is exactly how the run identity hid for a whole repair.
                'traces': traces_for(samples),
                **{m: fixture_artifacts(samples).get(m) for m in ARTIFACT_MEMBERS},
                # §14 meta-evidence. The fixture carries it because the DECLARED shape carries it — the
                # shape control refuses a fixture that invents or omits a member, which is what caught this
                # the moment `suite_cost` joined the member list.
                # §7 E2 — DERIVED from the samples this fixture holds, like the producer's. A hand-kept
                # count was free to disagree with the measurements beside it, which is the defect.
                'suite_cost': fixture_suite_cost(samples),
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
             only(sample(below_resolution=True, wall_ns=None, lower_ns=None, upper_ns=None)),
             expect='without a usable bound')
    observed('a below-resolution interval whose bounds are inverted',
             only(sample(below_resolution=True, wall_ns=None, lower_ns=9, upper_ns=1)),
             expect='without a usable bound')
    observed('a below-resolution read that also carries a point duration',
             only(sample(below_resolution=True, wall_ns=7, lower_ns=0, upper_ns=9)),
             expect='below resolution yet carries a point duration')

    counts['total'] += 1
    accepted = sample(measurement_kind=KIND_UNTIMED, wall_ns=None, aggregate_step_ns=None)
    interval = sample(wall_ns=None, aggregate_step_ns=None,
                      lower_ns=0, upper_ns=HOOK_CLOCK['resolution_ns'], below_resolution=True)
    for label, s in (('an untimed artifact', accepted), ('a below-resolution interval', interval)):
        try:
            validate_observation(observation(samples=[s], derived={'summaries': summarise([s])}), digest)
        except ObservatoryError as exc:
            failures.append(f'{label} was rejected: {exc}')
    rows = summarise([interval])
    if not rows or not all(r.get('below_resolution') and 'median_ns' not in r for r in rows.values()):
        failures.append('a below-resolution stage was summarised with a median it cannot have')

    # PRECISION IS NOT IDENTITY. A stage that reads as a bound in one repetition and as a point in another is
    # ONE metric; when the bound carried its own `measurement_kind` the two repetitions keyed apart, and the
    # registry — which cannot predict which way a 10 ms tick falls — was told it had declared a metric nobody
    # measured and measured one nobody declared. This is the control for that whole failure.
    counts['total'] += 1
    point = sample(wall_ns=20_000_000)
    if metric_identity(point) != metric_identity(interval):
        failures.append('a stage measured as a bound and as a point keyed as two metrics, so being fast '
                        'changed what a metric was')
    mixed_rows = summarise([interval, interval, point])
    if len(mixed_rows) != 1:
        failures.append(f'one metric with mixed precision summarised into {len(mixed_rows)} rows')
    else:
        row = next(iter(mixed_rows.values()))
        if 'median_ns' in row:
            failures.append('a metric with a below-resolution repetition published a median over the point '
                            'reads alone, which is a subset wearing the whole metric\'s name')
        if (row.get('samples'), row.get('below_resolution_samples')) != (3, 2):
            failures.append(f'a mixed-precision row lost repetitions: {row}')
        if (row.get('lower_ns'), row.get('upper_ns')) != (0, 20_000_000):
            failures.append(f'a mixed-precision bound does not span every read: {row}')
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
                # R12 wants a raw log per DIRECT sample. Writing none made every control here depend on an
                # earlier rule firing first: the moment one of them started passing, R12 spoke instead and
                # six controls reported the wrong reason. A control that only works while another rule fails
                # is not testing what it says it tests.
                raw = bundle / 'raw'
                raw.mkdir(parents=True, exist_ok=True)
                for s in args['obs'].get('measurements', []):
                    if s.get('derived_parent_id') or s.get('raw_log_sha256') is None:
                        continue
                    name = raw_log_name(s['command_id'], s['scenario_id'], s['sample_index'], s.get('edit_id'))
                    body = f'{s["sample_id"]}\n'.encode('utf-8')
                    (raw / f'{name}.log').write_bytes(body)
                    s['raw_log_sha256'] = _sha256(body)
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

    # The prime relation applies to samples that RAN — `identity_problems` skips contained ones on purpose,
    # because their cache provenance is a copy of their root's. So a control that perturbs a prime has to
    # perturb a sample which actually ran, and the trace root is the command that always does. Pinning these
    # to `make.prove` made them silently inert the moment it became contained: the perturbation had no effect
    # and whichever rule spoke next was reported as the answer.
    ROOT_CMD, ROOT_COLD = 'make.check', 'project.cold.acceptance'

    def prove_sample(obs, scenario_id, cid=ROOT_CMD):
        return pick(obs, f'{cid} sample in {scenario_id}',
                    lambda s: s['command_id'] == cid and s['scenario_id'] == scenario_id
                    and not s.get('derived_parent_id'))

    def with_reuse(prime):
        obs = complete_observation()
        target = next(s for s in obs['measurements']
                      if s['command_id'] == ROOT_CMD and s['scenario_id'] == 'project.warm.noop'
                      and not s.get('derived_parent_id'))
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
                 lambda o: metric_identity(prove_sample(o, ROOT_COLD)))),
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
        warm, cold = prove_sample(obs, 'project.warm.noop'), prove_sample(obs, ROOT_COLD)
        warm['cache_before']['prime_sample_id'] = cold['sample_id']
        obs['measurements'].remove(cold)
        obs['measurements'].append(cold)
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('a cached sample naming a prime that does not precede it',
             lambda: record_check(obs=prime_after()), expect='does not precede it')

    # A DERIVED child copies its parent's cache provenance, prime reference included. Asking whether that
    # prime belongs to the child's own command compares a Docker stage id against the command that built it,
    # so it can never match and every real observation carrying a warm derived child was unrecordable. The
    # parent is checked with the right identity; the child must not be asked again.
    counts['total'] += 1
    inherited = with_reuse(None)
    parent = prove_sample(inherited, 'project.warm.noop')
    child = {**parent, 'command_id': 'docker.prover', 'sample_id': f'{parent["sample_id"]}#child',
             'derived_parent_id': parent['command_id'], 'parent_sample_id': parent['sample_id'],
             'wall_ns': None, 'aggregate_step_ns': 1_000_000, 'resource_scope': SCOPE_BUILDKIT,
             'measurement_kind': KIND_AGGREGATE, 'derived_stage_events': []}
    inherited['measurements'].append(child)
    inherited['derived'] = {'summaries': summarise(inherited['measurements'])}
    kids = [p for p in identity_problems(inherited) if 'docker.prover' in p]
    if kids:
        failures.append(f'a derived child was held to a prime relation it cannot satisfy: {kids[0]}')

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
    # Under canonical multiplicity of one, a metric cannot be short a repetition — dropping its only sample
    # removes the metric, which the coverage relation reports as declared-but-unmeasured. The count defect
    # that remains reachable is the OPPOSITE one, and it is the acquisition defect this repair exists to
    # refuse: one relation acquired twice.
    def duplicated_relation():
        obs = complete_observation()
        twin = next(s for s in obs['measurements'] if s['command_id'] == 'make.diet')
        obs['measurements'].append({**twin, 'sample_index': twin['sample_index'] + 1,
                                    'sample_id': f'{twin["sample_id"]}#twin'})
        obs['derived'] = {'summaries': summarise(obs['measurements'])}
        return obs

    observed('one relation acquired twice',
             lambda: record_check(obs=duplicated_relation()),
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

    # §8 — THE PLAN AND THE RUNNER MUST AGREE. They diverged in a live canonical run: PLAN scheduled one
    # `make.prove` trace and the runner ran six, because the runner walked every scenario a command declares
    # without asking whether a containing trace already measures it. The plan was right; the runner was a
    # second authority. This states the relation both must satisfy — for every command and every canonical
    # state, a trace is scheduled exactly when the state is NOT contained.
    counts['total'] += 1
    scenarios_by_id = {s["id"]: s for s in suite["scenarios"]}
    canon_sel = select(suite)
    canon_plan = acquisition_plan(suite, canon_sel, graph=docker_stage_graph(root))
    planned_pairs = {(t['command_id'], t['scenario_id']) for t in canon_plan['traces']}
    cmds_by_id = {c['id']: c for c in suite['commands']}
    would_run = set()
    for c in suite['commands']:
        if c['measurement'] != 'direct':
            continue
        for sid in c['scenarios']:
            if not scenarios_by_id.get(sid, {}).get('canonical'):
                continue
            if contained_here(c, sid, cmds_by_id, canon_sel.partial) is None:
                would_run.add((c['id'], sid))
    if would_run != planned_pairs:
        only_run = sorted(would_run - planned_pairs)[:3]
        only_plan = sorted(planned_pairs - would_run)[:3]
        failures.append(f'the runner and the plan disagree about what executes: runner-only {only_run}, '
                        f'plan-only {only_plan}; one of them is a second authority')

    # §2 — A TRACE'S EXPECTATION CARRIES THIS RUN'S ROLES. A real smoke run refused nine metrics it had just
    # produced, because the expectation came from the planner's per-trace list: that list is filtered by what
    # was SELECTED, while a trace which runs produces all of its children regardless, and the registry states
    # every role as `selected` while an ad hoc run legitimately marks an unselected support child `support`.
    # Role is part of metric identity, so the two disagreed on identity alone.
    counts['total'] += 1
    part_sel = select(suite, only='make.check', scenario='project.warm.noop')
    part_exp = trace_expectations(suite, docker_stage_graph(root), part_sel.partial,
                                  lambda cid, sid: sample_role(part_sel, cid, sid))
    produced = [m for pair, ms in part_exp.items() if pair[0] == 'make.check' for m in ms]
    if not produced:
        failures.append('an ad hoc make.check selection expects no metrics at all')
    elif not any(m.split('|')[4] == 'support' for m in produced):
        failures.append('an ad hoc selection must carry the roles it actually assigns; every expected metric '
                        'claims `selected`, which is the registry speaking rather than the run')

    # §8 — and the CHILDREN a trace derives must be exactly the contained metrics the registry declares under
    # that parent and state. The control above pins SCHEDULING; this pins DERIVATION, and they are different
    # projections of one rule — which is why the first one passed while the second was wrong. Three of
    # `contained_here`'s readers iterate a command's own scenarios and could never ask about a state it does
    # not declare; the derivation asks about every command under one parent state, so the six warm-only
    # gates were minted under all eight `make.check` states. R05 refused the run over 44 undeclared metrics,
    # 97 minutes in. Asking the question here costs nothing and answers it before anything builds.
    counts['total'] += 1
    declared_kids: dict[tuple, set] = {}
    for spec in expected_relation(suite, graph=docker_stage_graph(root)).values():
        if spec['measurement_kind'] == KIND_CONTAINED:
            declared_kids.setdefault((spec['derived_parent_id'], spec['scenario_id']), set()).add(
                spec['command_id'])
    derived_kids: dict[tuple, set] = {}
    for t in canon_plan['traces']:
        kids = {c['id'] for c in suite['commands']
                if contained_here(c, t['scenario_id'], cmds_by_id, canon_sel.partial) == t['command_id']}
        if kids:
            derived_kids[(t['command_id'], t['scenario_id'])] = kids
    if derived_kids != declared_kids:
        extra = sorted({(p, s, k) for (p, s), ks in derived_kids.items()
                        for k in ks - declared_kids.get((p, s), set())})[:3]
        missing = sorted({(p, s, k) for (p, s), ks in declared_kids.items()
                          for k in ks - derived_kids.get((p, s), set())})[:3]
        failures.append(f'the contained children a trace derives are not the ones the registry declares: '
                        f'derived-only {extra}, declared-only {missing}')

    # §10 — REPEAT multiplies only what was SELECTED. Repeating support work spends minutes nobody asked for
    # on a number nobody requested, and repeating the whole suite is the fixed multiplicity this repair
    # deleted wearing a different name.
    counts['total'] += 1
    probe_cmd = {'samples': {'project.warm.noop': 1}}
    for role, rep, want in (('selected', 3, 3), ('support', 3, 1), ('selected', 1, 1), ('support', 1, 1)):
        got = wanted_samples(probe_cmd, 'project.warm.noop', role, rep)
        if got != want:
            failures.append(f'REPEAT={rep} on a {role} command asked for {got} sample(s), wanted {want}')
    if wanted_samples({'samples': {'project.warm.noop': 1}}, 'project.warm.noop', 'selected') != 1:
        failures.append('canonical acquisition without REPEAT is not one sample per identity')

    # §13 — RESUME refuses across every identity it names. Its whole value is the refusal: reusing a sample
    # from another candidate would be indistinguishable from measuring this one, and cheaper.
    counts['total'] += 1
    live_suite = load_suite(root)
    live_plan = acquisition_plan(live_suite, select(live_suite), graph=docker_stage_graph(root))
    now_subj = {'commit': 'a' * 40, 'inventory_digest': 'c' * 64, 'source_view': 'committed-tree',
                'dirty': False}
    now_env = {'host_class_fingerprint': 'd' * 64,
               'concurrency': {'make_jobs': 1, 'buildkit_max_parallelism': 1}}

    def prior_bundle(**over):
        # `run_id` is here because the identity relations require it. Without it `resumable_traces` bailed
        # out on validation before reaching the completeness filter, and the control below passed whether or
        # not that filter existed — a control made inert by an absent fixture field, which is the fifth time
        # this checkpoint that exact shape has cost something.
        base = {'run_id': 'run-fixture', 'subject': dict(now_subj),
                'suite_digest': suite_digest_of(live_suite),
                'environment': {'host_class_fingerprint': 'd' * 64,
                                'concurrency': {'make_jobs': 1, 'buildkit_max_parallelism': 1}},
                'measurements': []}
        base.update(over)
        return base

    if resume_incompatibilities(prior_bundle(), now_subj, live_suite, now_env, live_plan):
        failures.append('an identical bundle was refused for resume, so an interrupted suite could never be '
                        'continued at all')
    for label, over, want in (
            ('a different commit', {'subject': {**now_subj, 'commit': 'b' * 40}}, 'committed subject differs'),
            ('a different measured source',
             {'subject': {**now_subj, 'inventory_digest': 'f' * 64}}, 'measured source differs'),
            ('a dirty tree against a clean one',
             {'subject': {**now_subj, 'dirty': True}}, 'working-tree cleanliness differs'),
            ('a different suite', {'suite_digest': 'deadbeef'}, 'the suite registry differs'),
            ('another machine',
             {'environment': {'host_class_fingerprint': 'z' * 64,
                              'concurrency': {'make_jobs': 1, 'buildkit_max_parallelism': 1}}},
             'the host class differs'),
            ('a non-serial builder',
             {'environment': {'host_class_fingerprint': 'd' * 64,
                              'concurrency': {'make_jobs': 1, 'buildkit_max_parallelism': None}}},
             'the serial configuration differs')):
        reasons = resume_incompatibilities(prior_bundle(**over), now_subj, live_suite, now_env, live_plan)
        if not any(want in r for r in reasons):
            failures.append(f'resume accepted {label}: wanted a reason containing {want!r}, got {reasons}')

    counts['total'] += 1
    half = prior_bundle(measurements=[sample(command_id='make.fmt', scenario_id='project.warm.noop',
                                             status='unexpected-exit', exit_code=2)])
    done, notes = resumable_traces(half)
    if ('make.fmt', 'project.warm.noop') in done:
        failures.append('a trace that did not complete was offered for reuse, so its metrics would enter the '
                        'coverage relation as though the work had been observed')
    if not notes:
        failures.append('a bundle with an unfinished trace said nothing about it')

    # §14 — the suite's own cost is compared, or the comparison says why it is not. Without this the suite is
    # the one thing in the repository whose regressions cannot be seen, because `make.observe` is cataloged
    # forever and can never be a measured command.
    # ONE sample per side. The default fixture holds three samples of one identity sharing a source digest,
    # which is fine here but makes this control fail under a mutation of the UNRELATED source-pooling rule —
    # collateral noise that reports a rule unprotected when it is only untested by this control.
    counts['total'] += 1
    one = observation(samples=[sample()])
    costed = compare(one, observation(samples=[sample()]))
    if not (costed.get('suite_cost') or {}).get('comparable'):
        failures.append('two observations that both retain a suite cost were not compared on it')
    elif 'suite_wall_ns' not in costed['suite_cost']:
        failures.append('a comparable suite cost reported no wall time delta')
    older = observation(samples=[sample()])
    older.pop('suite_cost', None)
    try:
        stale = compare(older, observation(samples=[sample()]))
        if (stale.get('suite_cost') or {}).get('comparable'):
            failures.append('a baseline retaining no suite cost was compared on it anyway, which is a delta '
                            'against nothing')
    except ObservatoryError:
        pass    # refusing the whole comparison is also honest; inventing the delta is what is forbidden

    counts['total'] += 1
    single = cmp_guard(timed(100), timed(900))['metrics'][0]
    if single.get('noise_basis') != 'single-sample':
        failures.append(f'a one-sample side must say so: noise_basis was {single.get("noise_basis")!r}')

    counts['total'] += 1
    # A DIFFERENT HOST is a different field, and the hash follows. Changing only the hash modelled a machine
    # that cannot exist, and once the fingerprint is re-derived that fixture is simply invalid.
    other_host = observation(environment=fixture_environment(cpu_model='some other processor'))
    row = cmp_guard(observation(), other_host)['metrics'][0]
    if row['classification'] != 'incomparable' or 'delta_percent' in row:
        failures.append('an incomparable host class must not be reported as an ordinary percentage delta')

    counts['total'] += 1
    # Resource scope is part of the metric identity now, so a changed scope is not the same metric at all.
    # That is stronger than `incomparable`: the two never meet in one row to be given a verdict.
    scoped = timed(100, 110, 120)
    scoped['measurements'] = [dict(s, resource_scope=SCOPE_BUILDKIT) for s in scoped['measurements']]
    scoped['derived'] = {'summaries': summarise(scoped['measurements'])}
    scoped['traces'] = traces_for(scoped['measurements'])
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
        # The header is the one the RUNNER builds. It used to omit `run_id`, which the identity relations
        # require, so this fixture described a partial observation the tool never writes.
        head = {'schema': SCHEMA, 'suite_digest': digest, 'run_id': 'run-fixture'}
        write = checkpointer(b, head)
        if not (b / 'observation.json').is_file():
            failures.append('a bundle must be inspectable from creation, not only after the first sample')
        write([sample()], ['make.prove/project.cold.prover'])
        mid = json.loads((b / 'observation.json').read_text(encoding='utf-8'))
        if mid['derived'].get('status') != 'incomplete':
            failures.append('a checkpoint written mid-run must mark itself incomplete')
        if not mid['measurements']:
            failures.append('a checkpoint must retain the samples taken so far')

    # §12 — a defective fragment STOPS the suite instead of letting the remaining hours measure against a
    # broken record. Both Repair 2 defects that cost four hours each were visible in the first fragment that
    # contained them, and neither was looked at until the final recording rule.
    counts['total'] += 1
    with _tempfile.TemporaryDirectory() as d:
        b2 = Path(d) / 'bundle'
        (b2 / 'raw').mkdir(parents=True)
        stopper = checkpointer(b2, {'schema': SCHEMA, 'suite_digest': digest, 'run_id': 'run-fixture'})
        try:
            stopper([sample(wall_ns=-1)], [])
            failures.append('a fragment with a negative duration did not stop the suite, so every later '
                            'trace would have measured against a record already known to be broken')
        except ObservatoryError as exc:
            if 'trace fragment is invalid' not in str(exc):
                failures.append(f'a defective fragment was refused for the wrong reason: {exc}')
        if not (b2 / 'observation.json').is_file():
            failures.append('a fragment that stopped the suite must still be on disk; the evidence for the '
                            'failure is the fragment itself')

    # ── §7 E4 analysis artifacts are bound and their views recomputed.
    observed('an analysis sample whose artifact is null',
             lambda: validate_observation(complete_observation(module_graph=None), digest),
             expect='the observation retains none')
    observed('an artifact that hashes to no establishing trace',
             lambda: validate_observation(
                 complete_observation(module_graph=parse_module_graph(FIXTURE_DEP, {'A': 9, 'B': 9})),
                 digest),
             expect='does not hash to what its establishing trace')
    observed('an artifact no trace established',
             lambda: validate_observation(
                 complete_observation(traces=[{**t, 'analysis_artifacts': {}}
                                              for t in complete_observation()['traces']]), digest),
             expect='that no trace established')

    def tampered_view(which):
        obs = complete_observation()
        obs['derived'] = {**obs['derived'], which: {'tampered': True}}
        return obs

    observed('a tampered derived rebuild view',
             lambda: validate_observation(tampered_view('rebuild_impact'), digest),
             expect='not what its own module graph produces')
    observed('a tampered derived history view',
             lambda: validate_observation(tampered_view('weighted_rebuild_cost'), digest),
             expect='not what its own artifacts produce')

    counts['total'] += 1
    # MUST ACCEPT — a resumed observation carrying the exact artifacts its traces established. This is the
    # shape §6 D2 now produces, validated by the rules §7 E4 adds, so the two halves are proved to agree.
    resumed = complete_observation()
    try:
        validate_observation(resumed, digest)
    except ObservatoryError as exc:
        failures.append(f'an observation carrying the exact artifacts its traces established was refused: '
                        f'{exc}')

    # ── §7 the observation's self-evidence is evidence, not assertion.
    observed('an observation whose fingerprint is not what its own fields produce',
             lambda: validate_observation(
                 observation(environment={**fixture_environment(),
                                          'concurrency': {'make_jobs': 1,
                                                          'buildkit_max_parallelism': 2}}), digest),
             expect='not the one its own environment fields produce')

    def perturbed_cost(**over):
        """A complete observation whose suite cost has been perturbed in one exact way."""
        obs = complete_observation()
        obs['suite_cost'] = {**obs['suite_cost'], **over}
        return obs

    for label, over, want in (
            ('missing validation cost', {'validation_wall_ns': None}, 'not a duration'),
            ('a negative validation cost', {'validation_wall_ns': -1}, 'not a duration'),
            ('components that do not sum to the total', {'validation_components': {'x': 99}},
             'components sum to'),
            ('a false direct count', {'direct_trace_count': 999}, 'direct trace(s) beside'),
            ('a false contained count', {'contained_metric_count': 999}, 'contained metric(s) beside'),
            ('timestamps that do not order', {'suite_completed': '2025-01-01T00:00:00+00:00'},
             'do not order'),
            ('a cost naming no trace', {'trace_wall_ns': {'nobody|nowhere|-|0': 5}},
             'not a trace this run performed')):
        observed(f'suite cost with {label}',
                 lambda over=over: validate_observation(perturbed_cost(**over), digest),
                 expect=want)

    counts['total'] += 1
    counts['must_fail'] += 1
    # A trace the run performed with no cost retained is the other direction of the same rule.
    thin = complete_observation()
    first = next(iter(thin['suite_cost']['trace_wall_ns']))
    thin['suite_cost'] = {**thin['suite_cost'],
                          'trace_wall_ns': {k: v for k, v in thin['suite_cost']['trace_wall_ns'].items()
                                            if k != first}}
    try:
        validate_observation(thin, digest)
        failures.append('a performed trace with no retained cost was accepted')
    except ObservatoryError as exc:
        if 'retains no cost for' not in str(exc):
            failures.append(f'a performed trace with no retained cost was refused wrongly: {exc}')

    counts['total'] += 1
    # E1 — the clock times VALIDATING and nothing else, per component.
    clk = ValidationClock()
    clk.measure('preflight_controls', lambda: None)
    clk.measure('per_trace', lambda: None)
    clk.measure('per_trace', lambda: None)
    if set(clk.components) != {'preflight_controls', 'per_trace'} or clk.total_ns() != sum(
            clk.components.values()):
        failures.append(f'the validation clock must accumulate per component and total them: {clk.components}')

    # ── §6 resume carries the CAUSAL state, not only the sample rows.
    counts['total'] += 1
    # D1 — a resumed COLD trace must supply the prime its later traces depend on. The only resume shown
    # before used a warm-only command, which is exactly the shape that cannot exhibit this: with no cold
    # trace in the chain there is no prime to lose.
    cold_trace = trace_object(sample(command_id='make.prove', scenario_id='project.cold.prover',
                                     sample_index=0),
                              [], [metric_identity(sample(command_id='make.prove',
                                                          scenario_id='project.cold.prover'))],
                              None, {}, None)
    restored = primes_from_traces([cold_trace], {s['id']: s for s in suite['scenarios']})
    if ('make.prove', 'prime') not in restored:
        failures.append('a resumed cold trace must restore the prime its later traces depend on, or every '
                        'cached, warm and incremental trace after it is skipped as unprimed')
    elif restored[('make.prove', 'prime')]['id'] != cold_trace['root_sample_id']:
        failures.append('a restored prime must be the EXACT retained sample identity, not a reconstructed '
                        'peer claiming the same role')

    counts['total'] += 1
    counts['must_fail'] += 1
    # D2 — an analysis trace is resumable only against the exact artifact it established, proved by digest.
    real_graph = {'adjacency': {'A.v': []}, 'wall_ns': {'A.v': 5}}
    ana_trace = trace_object(sample(command_id='analysis.rocq-modules', scenario_id='project.warm.noop'),
                             [], [], None, {'module_graph': artifact_digest(real_graph)}, None)
    for label, bundle_holds, want_resumable in (
            ('the exact artifact', real_graph, True),
            ('an unrelated artifact', {'adjacency': {'B.v': []}, 'wall_ns': {'B.v': 5}}, False),
            ('no artifact at all', None, False)):
        got, rerun = resumable_artifacts([ana_trace], {'module_graph': bundle_holds})
        if want_resumable and (rerun or got.get('module_graph') != bundle_holds):
            failures.append(f'resuming an analysis trace against {label} must carry that exact artifact: '
                            f'{got}, rerun={rerun}')
        if not want_resumable and not rerun:
            failures.append(f'resuming an analysis trace against {label} must rerun it rather than inherit '
                            f'a null or unrelated artifact')

    counts['total'] += 1
    # D — BOTH runners honour resume. The filter lived only in the shell chain loop, so a resumed ANALYSIS
    # chain carried its completed traces and ran them again: a real smoke resume produced 24 samples where 12
    # were carried. That is duplicate acquisition, and only R05 would have caught it, at the end of the suite.
    both = {'shell': chain_after_resume('analysis.rocq-modules',
                                        ['project.cold.module-graph', 'project.warm.noop'],
                                        {('analysis.rocq-modules', 'project.cold.module-graph')}),
            'empty': chain_after_resume('x', ['a', 'b'], set())}
    if both['shell'] != ['project.warm.noop']:
        failures.append(f'a resumed trace must not run again: {both["shell"]}')
    if both['empty'] != ['a', 'b']:
        failures.append(f'with nothing resumed the whole chain runs: {both["empty"]}')

    counts['total'] += 1
    # D4 — per-trace cost keyed by the exact trace. Two repetitions of one command and scenario are two
    # costs; keying on command and scenario alone retained one and lost the other.
    reps = {trace_id_of('make.prove', 'project.warm.noop', None, i): 100 + i for i in range(3)}
    if len(reps) != 3:
        failures.append(f'repeated traces must each retain their own cost: {reps}')

    # ── §4 the parent partitions into non-overlapping children plus ONE retained remainder.
    def anchors(*spans, depth=0):
        return [{'id': i, 'start_ns': a, 'end_ns': b, 'source': 'hook-anchor', 'depth': depth,
                 'wall_ns': b - a, 'clock': HOOK_CLOCK} for i, a, b in spans]

    counts['total'] += 1
    # MAKE grammar: flat siblings, no enclosing anchor, so every depth-0 interval partitions the parent.
    flat = partition_of('make.check', 1000, anchors(('make.names', 0, 300), ('make.prove', 300, 700)))
    if (flat['covered_ns'], flat['overhead_ns'], flat['overhead_id']) != (700, 300, 'make.check.unattributed'):
        failures.append(f'a flat Make partition must cover its children and retain the rest: {flat}')

    counts['total'] += 1
    # HOOK grammar: the root anchor IS the command, so the partition is its children — not the root itself.
    # Taking the top level blindly made `precommit.full` its own single child covering everything.
    nested = partition_of('precommit.full', 1000,
                          anchors(('precommit.full', 0, 900))
                          + anchors(('precommit.builder', 10, 200), ('precommit.naming', 200, 800), depth=1))
    if [m['id'] for m in nested['members']] != ['precommit.builder', 'precommit.naming']:
        failures.append(f'a nested hook partition must be the stages, not the root anchor: {nested}')
    if (nested['covered_ns'], nested['overhead_ns']) != (790, 210):
        failures.append(f'a nested hook partition must retain the uncovered remainder: {nested}')

    counts['total'] += 1
    counts['must_fail'] += 1
    for label, args, want in (
            ('overlapping children',
             ('make.check', 1000, anchors(('a', 0, 400), ('b', 300, 700))), 'overlap'),
            ('a child interval outside its parent',
             ('make.check', 100, anchors(('a', 0, 400))), 'lies outside'),
            ('children spanning more than the parent elapsed',
             ('make.check', 500, anchors(('a', 0, 300), ('b', 300, 600))), 'lies outside')):
        try:
            partition_of(*args)
            failures.append(f'{label} was accepted, so the parent does not partition')
        except ObservatoryError as exc:
            if want not in str(exc):
                failures.append(f'{label} was refused for the wrong reason: {exc}')

    counts['total'] += 1
    counts['must_fail'] += 1
    base_trace = complete_observation()['traces'][0]
    for label, part, want in (
            ('a remainder that does not close the parent',
             {'parent_ns': 1000, 'covered_ns': 700, 'overhead_ns': 100,
              'overhead_id': 'x.unattributed', 'members': [{'id': 'a', 'start_ns': 0, 'end_ns': 700}]},
             'is not the parent'),
            ('a nested interval counted at two levels',
             {'parent_ns': 1000, 'covered_ns': 600, 'overhead_ns': 400, 'overhead_id': 'x.unattributed',
              'members': [{'id': 'a', 'start_ns': 0, 'end_ns': 300},
                          {'id': 'a', 'start_ns': 300, 'end_ns': 600}]},
             'appears twice in the partition'),
            ('a remainder retained under no identity',
             {'parent_ns': 1000, 'covered_ns': 700, 'overhead_ns': 300, 'overhead_id': '',
              'members': [{'id': 'a', 'start_ns': 0, 'end_ns': 700}]},
             'retained under no stable identity')):
        found = trace_problems({**base_trace, 'partition': part})
        if not any(want in p for p in found):
            failures.append(f'{label} was accepted by the partition rules: {found}')

    counts['total'] += 1
    # THE REVIEWER'S OWN NUMBERS, from the retained warm `make.check` trace. They observed the near-equality
    # and said plainly that no rule proved it and the difference was retained nowhere. It is retained now.
    real = partition_of('make.check', 362_263_112_436, anchors(('make.check-body', 0, 362_220_000_000)))
    if real['overhead_ns'] != 43_112_436:
        failures.append(f'the reviewer\'s retained warm make.check remainder must be exact: {real}')

    # §2 — THE REVIEWER'S OWN REPRODUCTION, on the fragment path where they ran it. They took the cumulative
    # prefix through a real completed `make.check/project.warm.noop`, removed `make.prove`, `docker.prover`
    # and `make.fcb` in turn, and every mutilated fragment still passed with no finding. The fragment check
    # now carries the trace rules, so a lost child stops the suite where it happens instead of at R05 after
    # the last trace.
    counts['total'] += 1
    counts['must_fail'] += 1
    with _tempfile.TemporaryDirectory() as d:
        b3 = Path(d) / 'bundle'
        (b3 / 'raw').mkdir(parents=True)
        keeper = checkpointer(b3, {'schema': SCHEMA, 'suite_digest': digest, 'run_id': 'run-fixture'})
        whole = complete_observation()
        kept = [s for s in whole['measurements']
                if s.get('derived_parent_id') in (None, 'make.check')]
        closed = [t for t in whole['traces'] if t['command_id'] == 'make.check']
        exercised = 0
        for victim in ('make.prove', 'docker.prover', 'make.fcb'):
            mutilated = [s for s in kept if s['command_id'] != victim]
            if len(mutilated) == len(kept):
                continue                    # that child is not in this fixture; the next one still proves it
            exercised += 1
            try:
                keeper(mutilated, [], closed)
                failures.append(f'a completed trace fragment missing its {victim} child was accepted, which '
                                f'is the exact false green this repair exists to remove')
            except ObservatoryError as exc:
                if 'trace fragment is invalid' not in str(exc):
                    failures.append(f'a fragment missing {victim} was refused for the wrong reason: {exc}')
        # A control that skipped every case would report the same green as one that proved all three.
        if exercised != 3:
            failures.append(f'the reviewer reproduction exercised {exercised} of 3 named children; the '
                            f'production-shaped observation no longer contains the others')

    # ── §2 trace completion. A COMPLETED SAMPLE IS NOT A COMPLETED TRACE.
    #
    # Every must-fail below was reproduced by the reviewer against a real completed `make.check` fragment and
    # passed, because per-sample rules cannot see a sample that never arrived.
    def drop_sample(pick):
        """A completed observation minus one retained sample, with its trace objects left intact."""
        obs = complete_observation()
        victim = pick(obs['measurements'])
        obs['measurements'] = [s for s in obs['measurements'] if s is not victim]
        return obs

    observed('a contained child omitted from a completed trace',
             lambda: validate_observation(
                 drop_sample(lambda ss: pick({'measurements': ss}, 'contained child',
                                             lambda s: s.get('measurement_kind') == KIND_CONTAINED)), digest),
             expect='which this record does not contain')
    observed('a derived Docker child omitted from a completed trace',
             lambda: validate_observation(
                 drop_sample(lambda ss: pick({'measurements': ss}, 'docker child',
                                             lambda s: s['command_id'].startswith('docker.'))), digest),
             expect='which this record does not contain')

    def trace_with(mutate):
        """A completed observation whose FIRST trace object has been mutated in place."""
        obs = complete_observation()
        obs['traces'] = [dict(obs['traces'][0])] + obs['traces'][1:]
        mutate(obs['traces'][0], obs)
        return obs

    def add_child(obj, obs):
        extra = sample(command_id='docker.prover', scenario_id=obj['scenario_id'],
                       derived_parent_id=obj['command_id'], measurement_kind=KIND_AGGREGATE,
                       resource_scope=SCOPE_BUILDKIT, aggregate_step_ns=5, wall_ns=None)
        extra['sample_id'] = 'extra-child'
        obs['measurements'] = obs['measurements'] + [extra]
        obj['observed_metrics'] = sorted(obj['observed_metrics'] + [metric_identity(extra)])
        obj['child_sample_ids'] = obj['child_sample_ids'] + ['extra-child']

    observed('an extra child inserted into a completed trace',
             lambda: validate_observation(trace_with(add_child), digest),
             expect='was required 0 time(s) and observed 1')

    def steal_child(obj, obs):
        """One child moved under a trace that did not produce it, sample and all."""
        other = next((t for t in obs['traces'][1:] if t['child_sample_ids']), None)
        if other is None:
            raise ObservatoryError('the fixture retains no second trace with a child to move')
        obj['child_sample_ids'] = obj['child_sample_ids'] + [other['child_sample_ids'][0]]

    observed('a child retained under a trace that did not produce it',
             lambda: validate_observation(trace_with(steal_child), digest),
             expect='retained under a trace that did not produce it')

    observed('one expected metric produced twice in a trace',
             lambda: validate_observation(
                 trace_with(lambda obj, obs: obj.update(
                     observed_metrics=sorted(obj['observed_metrics'] + [obj['observed_metrics'][0]]))), digest),
             expect='was required 1 time(s) and observed 2')
    observed('a trace retained before its children were derived',
             lambda: validate_observation(
                 trace_with(lambda obj, obs: obj.update(state='in-progress')), digest),
             expect='retained before it closed')
    def missing_one_trace():
        """A complete observation minus one completion object that establishes no ARTIFACT.

        Removing an analysis trace would unbind its artifact and report that rule instead, so this control
        would pass on a message about something else."""
        obs = complete_observation()
        victim = next(t for t in obs['traces'] if not t['analysis_artifacts'])
        obs['traces'] = [t for t in obs['traces'] if t is not victim]
        return obs

    observed('a completed direct root with no trace-completion object',
             lambda: validate_observation(missing_one_trace(), digest),
             expect='no trace-completion object')
    counts['total'] += 1
    counts['must_fail'] += 1
    stale = complete_observation()['traces'][0]
    against_plan = trace_problems(stale, {(stale['command_id'], stale['scenario_id']): ['a', 'b']})
    if not any('differs from the current plan' in p for p in against_plan):
        failures.append('a trace object closed against an expectation the current plan does not state was '
                        f'accepted: {against_plan}')
    unplanned = trace_problems(stale, {('nobody', 'nowhere'): []})
    if not any('schedules no such trace' in p for p in unplanned):
        failures.append(f'a trace the current plan does not schedule at all was accepted: {unplanned}')

    # Must-accept: the exact shapes a real suite produces. `complete_observation` is generated FROM the
    # expected relation, so `make.check/project.warm.noop` appears here with the exact child relation the
    # registry declares for it — the reviewer's own must-accept case, without depending on a recorded file.
    observed('a complete observation whose every direct sample closes its trace',
             lambda: validate_observation(complete_observation(), digest))

    counts['total'] += 1
    shapes = {'direct-only': 0, 'direct-plus-contained': 0, 'direct-plus-docker': 0}
    for obj in complete_observation()['traces']:
        kids = [m.split('|')[0] for m in obj['observed_metrics']
                if m != metric_identity({'command_id': obj['command_id'], 'scenario_id': obj['scenario_id'],
                                         'edit_id': obj['edit_id'], 'selected_or_support': 'selected',
                                         'resource_scope': SCOPE_HOST, 'measurement_kind': KIND_WALL})]
        if not kids:
            shapes['direct-only'] += 1
        if any(k.startswith('docker.') for k in kids):
            shapes['direct-plus-docker'] += 1
        if any(not k.startswith('docker.') for k in kids):
            shapes['direct-plus-contained'] += 1
    if not all(shapes.values()):
        failures.append(f'the accepted trace shapes are not all exercised by the production-shaped '
                        f'observation: {shapes}')

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
    # BOTH halves of effective concurrency. Reading `make_jobs` alone let the reviewer double BuildKit
    # parallelism and still receive ordinary percentage deltas.
    for label, conc in (('Make jobs', {'make_jobs': 4, 'buildkit_max_parallelism': 1}),
                        ('BuildKit parallelism', {'make_jobs': 1, 'buildkit_max_parallelism': 2})):
        counts['total'] += 1
        slow = observation(environment=fixture_environment(concurrency=conc))
        row = cmp_guard(slow, observation())['metrics'][0]
        if row['classification'] != 'incomparable' or 'concurrency' not in row['reason']:
            failures.append(f'a changed {label} must make the comparison incomparable: {row}')

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
    # THE FIXTURE MUST BE THE SHAPE THE TOOL EMITS. This one hand-supplied `run_id`, which identity_problems
    # requires and OBSERVATION_MEMBERS did not name, so every control here passed against a shape the real
    # producer never built: the tool would have failed its own last recording rule at the end of a four-hour
    # run. A fixture free to carry a field the contract omits tests something that does not exist.
    counts['total'] += 1
    fixture_members, declared = set(observation()), set(OBSERVATION_MEMBERS)
    if fixture_members != declared:
        failures.append(f'the self-test observation fixture is not the declared shape: it omits '
                        f'{sorted(declared - fixture_members)} and invents '
                        f'{sorted(fixture_members - declared)}')

    counts['total'] += 1
    hook_cmd = next(c for c in suite['commands'] if c['kind'] == 'precommit-full')
    env = instrumentation_env(hook_cmd, Path('/tmp/x.anchors'))
    if 'FIDO_OBSERVE' not in env:
        failures.append('the hook must be measured with its anchors switched on, or they are dead weight')
    make_cmd = next(c for c in suite['commands'] if c['kind'] == 'make-target')
    if instrumentation_env(make_cmd, Path('/tmp/x')).get('BUILDKIT_PROGRESS') != 'plain':
        failures.append('a make target must be measured with structured BuildKit progress')
    # A Make target's checkpoints are inert unless the log is named, exactly as the hook's are. Without this
    # every contained metric goes missing and the coverage relation fails at the END of the suite.
    if not instrumentation_env(make_cmd, Path('/tmp/x.anchors')).get('FIDO_OBSERVE'):
        failures.append('a make target is measured with its checkpoints switched off, so every metric '
                        'contained in it would be absent from the observation')

    # EVERY kind, not just the hook. A recipe that bind-mounts a `mktemp -d` path needs that path to exist
    # on the HOST; scoping the guarantee to the one command whose failure I had already debugged is what let
    # `make fcb-write` fail the same way. This asks the question of every kind the registry declares.
    counts['total'] += 1
    for kind in sorted({c['kind'] for c in suite['commands']}):
        some = next(c for c in suite['commands'] if c['kind'] == kind)
        where = instrumentation_env(some, Path('/tmp/x')).get('TMPDIR')
        if not where:
            failures.append(f'a {kind} command is measured without a host-visible TMPDIR, so any recipe of '
                            f'that kind that bind-mounts a temp directory silently gets an empty one')
        elif not Path(where).is_absolute():
            failures.append(f'a {kind} command was given a relative TMPDIR {where!r}, which cannot name the '
                            f'same directory to the runner and to the host daemon')

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

    # §3 — THE THREE MALFORMED LOGS THE OLD PARSER ACCEPTED SILENTLY. Each was reproduced by the reviewer
    # against the live parser: the first produced no event at all, the second reported a 50 ns interval for
    # work that took 100, and the third was discarded. Runtime checkpoint output is the evidence contained
    # timing is derived FROM, so static source pairing cannot stand in for any of them.
    observed('an end with no begin',
             lambda: parse_anchor_log('end make.prove 200\n'),
             expect='ended while nothing was the open checkpoint')
    observed('a second begin for an already-open checkpoint',
             lambda: parse_anchor_log('begin make.prove 100\nbegin make.prove 150\nend make.prove 200\n'),
             expect='began while already open')
    observed('a second end for a checkpoint already closed',
             lambda: parse_anchor_log('begin make.prove 100\nend make.prove 200\nend make.prove 250\n'),
             expect='ended while nothing was the open checkpoint')
    observed('a second completed pair for one checkpoint',
             lambda: parse_anchor_log('begin make.prove 100\nend make.prove 200\n'
                                      'begin make.prove 300\nend make.prove 400\n'),
             expect='completed a second pair in one trace')
    observed('an end that does not close the innermost open checkpoint',
             lambda: parse_anchor_log('begin a 100\nbegin b 150\nend a 200\nend b 250\n'),
             expect="ended while 'b' was the open checkpoint")
    observed('a checkpoint the registry never declared',
             lambda: parse_anchor_log('begin make.invented 100\nend make.invented 200\n',
                                      known=declared_anchor_ids(suite, root)),
             expect='is not one this trace declares')
    # MUST ACCEPT — and this refused a real `make.check` run. The declared vocabulary is the registry's
    # commands AND the checkpoints the Makefile and hook emit: `<command>-body` is the declared form for a
    # compound recipe's own unowned segment, which §4 requires to be named rather than folded into its
    # parent. Building the set from command ids alone rejected work the registry does declare.
    counts['total'] += 1
    live_vocab = declared_anchor_ids(suite, root)
    unspeakable = sorted((set(make_anchor_pairs(root)) | set(hook_anchor_pairs(root))) - live_vocab)
    if unspeakable:
        failures.append(f'the sources emit checkpoint(s) the declared vocabulary refuses: {unspeakable}')
    observed('a compound recipe body checkpoint',
             lambda: parse_anchor_log('begin make.check-body 100\nend make.check-body 200\n',
                                      known=live_vocab))

    counts['total'] += 1
    # Exact start and end, not only the duration. §4's partition cannot be proved from durations alone, and
    # a parser that retained only the difference made the containment question unanswerable.
    bounds = parse_anchor_log('begin a 1000\nbegin b 1100\nend b 1400\nend a 2000\n')
    if [(e['id'], e.get('start_ns'), e.get('end_ns')) for e in bounds] != [('b', 1100, 1400),
                                                                          ('a', 1000, 2000)]:
        failures.append(f'a checkpoint must retain its exact start and end, not only its duration: {bounds}')

    counts['total'] += 1
    # Both real grammars parse. MAKE is flat siblings with no enclosing root; the HOOK is one root with
    # sibling stages inside it. One stack serves both, and neither is forced into the other's shape.
    make_log = ('begin make.names 100\nend make.names 200\n'
                'begin make.prove 200\nend make.prove 500\n'
                'begin make.check-body 500\nend make.check-body 900\n')
    hook_log = ('begin precommit.full 100\nbegin precommit.builder 110\nend precommit.builder 150\n'
                'begin precommit.naming 150\nend precommit.naming 400\nend precommit.full 500\n')
    for label, log, want in (('make siblings', make_log, 3), ('hook nesting', hook_log, 3)):
        got = parse_anchor_log(log)
        if len(got) != want:
            failures.append(f'{label}: expected {want} checkpoint interval(s), got {len(got)}')

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

    # The other side of the same field. A CONTAINED command is measured inside its parent and reaches the
    # observation through child derivation, so listing it among the commands this selection could not measure
    # claims its own samples do not exist while they sit in the same file. The runner was one elided chain
    # away from writing exactly that, because it decided `unmeasured` AFTER containment emptied the chain.
    observed('a command listed as both measured and impossible to measure',
             lambda: validate_observation(observation(selection={
                 'partial': False, 'commands_selected': ['make.fmt'], 'commands_support': [],
                 'scenarios': ['project.warm.noop'], 'scenarios_added_as_support': [],
                 'commands_with_no_scenario_here': ['make.fmt'], 'commands_never_measured': []}), digest),
             expect='says both')

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
    p.add_argument('--plan', action='store_true',
                   help='print the exact acquisition plan and run nothing (M2 measurement)')
    p.add_argument('--resume', help='reuse the completed traces of an exact same-subject local bundle')
    p.add_argument('--repeat', type=int, default=1,
                   help='ad hoc repetition of a NAMED selection; never with --record')
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

            # §8 — PLAN runs nothing. It prints what a run would execute and what each execution establishes,
            # then stops, so a redundant or unownable acquisition costs a second to find instead of the last
            # recording rule of a four-hour suite. It cannot record: it has measured nothing to record.
            if args.plan:
                # The usage error is refused BEFORE the plan is printed. Printing a plan and then rejecting
                # the request reads as though the plan were the answer to it.
                if args.record:
                    raise ObservatoryError(
                        'PLAN and RECORD are exclusive: a plan measures nothing, so it has nothing to record')
                plan = acquisition_plan(suite, sel, graph=docker_stage_graph(root))
                problems = plan_problems(plan)
                print(render_plan(plan, sel, problems))
                if problems:
                    raise ObservatoryError(
                        f'{len(problems)} acquisition defect(s) in the plan; nothing was run')
                return 0

            # §12 — THE PREFLIGHT. The canonical suite must never be the first place a structural rule is
            # exercised. Everything here is deterministic and costs seconds: the registry is already
            # validated by `load_suite`, the coverage relation is exercised against a production-shaped
            # synthetic observation built from the SAME expected relation the recording rules close over,
            # that observation is validated by the complete validator and rendered, and the plan is checked
            # for redundant or unownable acquisition. Repair 2 lost four hours twice to defects that every
            # one of these steps would have caught before the first trace.
            # §7 E1 — the facility's own checking cost is timed from here, on the suite's monotonic source.
            clock = ValidationClock()
            if clock.measure('preflight_controls', self_test, root) != 0:
                raise ObservatoryError(
                    'the deterministic controls do not pass, so nothing measured here could be trusted; '
                    'the suite refuses to spend hours proving that')
            preflight_plan = acquisition_plan(suite, sel, graph=docker_stage_graph(root))
            preflight_problems = clock.measure('preflight_plan', plan_problems, preflight_plan)
            if preflight_problems:
                raise ObservatoryError(
                    f'{len(preflight_problems)} acquisition defect(s) in the plan; nothing was run: '
                    + '; '.join(preflight_problems[:3]))
            print(f'fido: build-observatory — preflight OK; plan is {preflight_plan["trace_count"]} trace(s) '
                  f'establishing {preflight_plan["required_metrics"]} required metric(s)')

            # §10 — REPEAT is AD HOC variance and can never touch a canonical result. Both refusals happen
            # before any measurement: a run that would be rejected at the end is a run nobody should start.
            repeat = max(1, int(args.repeat or 1))
            if repeat > 1:
                # §6 D3 — REPEAT and RESUME have no exact joint meaning, so they are refused together rather
                # than given one. Resume identity is the trace, not the trace-and-its-repetition-count, so a
                # bundle holding one repetition would satisfy a request for five and the run would report a
                # multiplicity nobody performed. Keeping the design simple is the reviewer's own direction.
                if args.resume:
                    raise ObservatoryError(
                        'REPEAT and RESUME are exclusive: a resumed trace is reused whole, so a bundle with '
                        'fewer repetitions would silently satisfy a request for more')
                if args.record:
                    raise ObservatoryError(
                        'REPEAT and RECORD are exclusive: canonical acquisition is one real trace per '
                        'identity, so a repeated run is an investigation and never the tracked observation')
                if not sel.partial:
                    raise ObservatoryError(
                        'REPEAT needs a named selection: repeating the WHOLE suite is the fixed multiplicity '
                        'this repair deleted, and it costs hours to buy precision where there is none to buy')
                print(f'fido: build-observatory — REPEAT={repeat}: each selected command runs {repeat} times '
                      f'in each of its states; support commands keep their registry count')

            # §13 — RESUME is decided BEFORE anything runs, and refuses with every reason at once. A bundle
            # that cannot be carried is a rerun the operator should learn about now, not after the first
            # trace has already been paid for.
            resume_done, resume_samples, resume_traces, resume_artifacts = set(), [], [], {}
            if args.resume:
                prior_path = Path(args.resume).resolve()
                if prior_path.is_dir():
                    prior_path = prior_path / 'observation.json'
                if not prior_path.is_file():
                    raise ObservatoryError(f'no observation to resume at {prior_path}')
                prior = json.loads(prior_path.read_text(encoding='utf-8'))
                plan = acquisition_plan(suite, sel, graph=docker_stage_graph(root))
                why = resume_incompatibilities(prior, subject(root), suite, environment(root), plan)
                if why:
                    raise ObservatoryError(
                        f'{prior_path} cannot be resumed into this run; {len(why)} reason(s): '
                        + '; '.join(why))
                resume_done, notes = resumable_traces(prior)
                for note in notes:
                    print(f'fido: build-observatory — resume: {note}')
                keep = {(t['command_id'], t['scenario_id']) for t in plan['traces']} & resume_done
                resume_samples = [s for s in prior.get('measurements', [])
                                  if (s.get('derived_parent_id') or s['command_id'], s['scenario_id']) in keep
                                  or (s['command_id'], s['scenario_id']) in keep]
                resume_done = keep
                # §6 D1/D2 — the CAUSAL state, not only the sample rows. A resumed cold trace is the prime a
                # later cached, warm or incremental trace depends on, and a resumed analysis trace owns the
                # artifact its samples claim. Carrying rows alone left `primes` empty, so every later trace
                # in the chain was skipped as unprimed, and left `module_graph`/`history_analysis` null in an
                # observation whose samples said the analysis had run. Only traces whose completion object
                # validates are carried, so the state comes from evidence rather than from assumption.
                resume_traces = [t for t in (prior.get('traces') or [])
                                 if (t.get('command_id'), t.get('scenario_id')) in keep
                                 and not trace_problems(t)]
                # An analysis trace is resumable only if the prior bundle still holds the EXACT artifact its
                # completion object names, proved by digest. Anything else and the trace reruns: a resumed
                # analysis sample beside a null or unrelated artifact is the defect, not the remedy.
                resume_artifacts, artifact_gap = resumable_artifacts(resume_traces, prior)
                resume_traces = [t for t in resume_traces
                                 if f'{t["command_id"]}/{t["scenario_id"]}' not in set(artifact_gap)]
                if artifact_gap:
                    print(f'fido: build-observatory — resume: {len(artifact_gap)} analysis trace(s) will '
                          f'RERUN because the bundle no longer holds the exact artifact they established: '
                          f'{", ".join(sorted(set(artifact_gap))[:3])}')
                carried = {t['trace_id'] for t in resume_traces}
                lost = sorted(f'{c}/{s}' for c, s in keep
                              if not any(t['command_id'] == c and t['scenario_id'] == s
                                         for t in resume_traces))
                if lost:
                    # A trace whose completion object does not validate is NOT resumable, whatever its
                    # samples look like. Reporting it is the difference between rerunning it and silently
                    # inheriting a gap.
                    print(f'fido: build-observatory — resume: {len(lost)} trace(s) will RERUN because their '
                          f'completion objects do not validate: {", ".join(lost[:3])}')
                    keep -= {(c, s) for c, s in keep if f'{c}/{s}' in set(lost)}
                    resume_done = keep
                    resume_samples = [s for s in resume_samples
                                      if (s.get('derived_parent_id') or s['command_id'],
                                          s['scenario_id']) in keep
                                      or (s['command_id'], s['scenario_id']) in keep]
                print(f'fido: build-observatory — resuming {len(keep)} completed trace(s) from {prior_path}, '
                      f'carrying {len(resume_samples)} sample(s) and {len(carried)} completion object(s)')

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
                checkpoint=checkpointer(bundle, header, clock), clock=clock,
                resume_done=resume_done, resume_samples=resume_samples,
                resume_traces=resume_traces, resume_artifacts=resume_artifacts,
                repeat=repeat)
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
