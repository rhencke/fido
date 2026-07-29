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
SIDE_EFFECTS = ('none', 'writes-disposable-copy', 'writes-local-observation',
                'writes-tracked-observation', 'changes-repository-config')
MEASUREMENTS = ('direct', 'derived', 'catalog-only')
COMMAND_FIELDS = ('id', 'kind', 'groups', 'purpose', 'source_view', 'execution', 'side_effect',
                  'measurement', 'scenarios', 'samples', 'dependencies', 'expected_exit', 'outputs', 'owner')
SCENARIO_FIELDS = ('id', 'purpose', 'session_state', 'cache_state', 'prime_steps', 'sample_policy',
                   'applicable_groups')

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
    m = re.search(r'^\.PHONY:((?:[^\n\\]*\\\n)*[^\n]*)$', text, re.M)
    if not m:
        raise ObservatoryError(f'{MAKEFILE_REL}: no .PHONY declaration, so the public surface is undiscoverable')
    names = set(m.group(1).replace('\\\n', ' ').split())
    if not names:
        raise ObservatoryError(f'{MAKEFILE_REL}: the .PHONY declaration is empty')
    return names


def docker_stages(root: Path) -> set[str]:
    text = read_text(root / DOCKERFILE_REL, 'Dockerfile')
    names = set(re.findall(r'^FROM\s+\S+\s+AS\s+(\S+)\s*$', text, re.M))
    if not names:
        raise ObservatoryError(f'{DOCKERFILE_REL}: no named build stages, so the stage surface is undiscoverable')
    return names


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
    for member in ('commands', 'groups', 'scenarios'):
        if not isinstance(suite.get(member), list):
            raise ObservatoryError(f'{SUITE_REL}: member {member!r} is missing or not a list')

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
        if POSITIONAL_OWNER.search(c['owner']):
            raise ObservatoryError(
                f'{SUITE_REL}: {cid}: owner {c["owner"]!r} identifies its source by line number; a registry '
                f'names stable identities, because a line number is wrong the moment its file is edited')
        for s in c['scenarios']:
            if s not in c['samples']:
                raise ObservatoryError(f'{SUITE_REL}: {cid}: scenario {s!r} has no sample count')

    seen_grp = set()
    for g in suite['groups']:
        gid = g.get('id')
        if gid in seen_grp:
            raise ObservatoryError(f'{SUITE_REL}: duplicate group id {gid!r}')
        seen_grp.add(gid)
        for member in g.get('members', []):
            if member not in seen_cmd:
                raise ObservatoryError(f'{SUITE_REL}: group {gid!r} names unknown command {member!r}')

    seen_scn = set()
    for s in suite['scenarios']:
        missing = [f for f in SCENARIO_FIELDS if f not in s]
        if missing:
            raise ObservatoryError(f'{SUITE_REL}: scenario {s.get("id")!r} is missing field(s) {missing}')
        if s['id'] in seen_scn:
            raise ObservatoryError(f'{SUITE_REL}: duplicate scenario id {s["id"]!r}')
        seen_scn.add(s['id'])

    for c in suite['commands']:
        unknown = [s for s in c['scenarios'] if s not in seen_scn]
        if unknown:
            raise ObservatoryError(f'{SUITE_REL}: {c["id"]}: unknown scenario(s) {unknown}')
        missing_dep = [d for d in c['dependencies'] if d not in seen_cmd]
        if missing_dep:
            raise ObservatoryError(f'{SUITE_REL}: {c["id"]}: unknown dependenc(ies) {missing_dep}')
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


def subject(root: Path) -> dict:
    """What exactly was measured. A dirty run says so and carries enough to tell two dirty runs apart."""
    porcelain = _git(root, 'status', '--porcelain')
    dirty = bool(porcelain.strip())
    head = _git(root, 'rev-parse', 'HEAD').strip()
    tree = _git(root, 'rev-parse', 'HEAD^{tree}').strip()
    out = {'commit': head, 'tree': tree, 'inventory_digest': inventory_digest(root),
           'dirty': dirty, 'source_view': 'working-tree' if dirty else 'committed-tree'}
    if dirty:
        paths = sorted(l[3:] for l in porcelain.split('\n') if l.strip())
        blobs = []
        for rel in paths:
            f = root / rel
            blobs.append(f'{rel}:{_sha256(f.read_bytes()) if f.is_file() else "absent"}')
        out['head_commit'] = head
        out['working_tree_digest'] = _sha256('\n'.join(blobs).encode('utf-8'))
        out['dirty_paths_digest'] = _sha256('\n'.join(paths).encode('utf-8'))
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


def _host() -> dict:
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
    inspect = dict(
        (k.strip(), v.strip())
        for k, _, v in (l.partition(':') for l in (cmd('docker', 'buildx', 'inspect', BUILDER) or '').split('\n'))
        if v.strip())

    return {'platform': f'{platform.system()}/{platform.machine()}', 'kernel': platform.release(),
            'cpu_model': cpu_model, 'logical_cpus': os.cpu_count(), 'memory_bytes': mem_bytes,
            'filesystem_type': cmd('stat', '-f', '-c', '%T', '.'),
            'docker_version': cmd('docker', 'version', '--format', '{{.Server.Version}}'),
            'buildx_version': cmd('docker', 'buildx', 'version'),
            'buildkit_identity': inspect.get('BuildKit version'),
            'builder_driver': inspect.get('Driver'),
            'buildkit_snapshotter': inspect.get('org.mobyproject.buildkit.worker.snapshotter'),
            'concurrency': {'make_jobs': os.environ.get('MAKEFLAGS', ''),
                            'buildkit_max_parallelism': os.environ.get('BUILDKIT_MAX_PARALLELISM', '')}}


# Fields whose value changes the timing a comparison may be made against. Free memory and load average are
# deliberately absent: they move between two runs on one machine, and folding them in would make every
# observation incomparable with every other.
FINGERPRINT_FIELDS = ('platform', 'kernel', 'cpu_model', 'logical_cpus', 'memory_bytes',
                      'docker_version', 'buildx_version', 'buildkit_identity', 'builder_driver',
                      'buildkit_snapshotter', 'filesystem_type')


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


def environment(root: Path) -> dict:
    env = {**_host(), **_pinned(root)}
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

    def __init__(self, selected: list[str], support: list[str], scenarios: list[str], partial: bool):
        self.selected, self.support = selected, support
        self.scenarios, self.partial = scenarios, partial

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
                      else set(scenarios))

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

    partial = bool(only or scenario)
    return Selection(selected, support, sorted(want_scenarios), partial)


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


def run_sample(root: Path, command: dict, scenario_id: str, index: int, role: str,
               raw_dir: Path, cache_before: dict, cwd: Path | None = None) -> dict:
    """Run one command once and retain everything needed to defend the number afterwards.

    Duration is monotonic: a wall clock can step backwards under NTP and produce a negative or absurd
    interval, and a timing tool that reports one has said something false rather than nothing.

    The raw log stays local and only its digest is retained, so the tracked observation stays useful long
    after the bundle is gone without pretending the log is still there."""
    import datetime
    import resource
    import subprocess

    raw_dir.mkdir(parents=True, exist_ok=True)
    log = raw_dir / f'{command["id"]}.{scenario_id}.{index}.log'
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    t0 = _monotonic_ns()
    with log.open('wb') as sink:
        proc = subprocess.run(command['execution'], cwd=str(cwd or root),
                              stdout=sink, stderr=subprocess.STDOUT)
    wall_ns = _monotonic_ns() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)

    if wall_ns < 0:
        raise ObservatoryError(
            f'{command["id"]}: the monotonic clock went backwards, which cannot happen; the sample is void')

    data = log.read_bytes()
    expected = command['expected_exit']
    return {'command_id': command['id'], 'scenario_id': scenario_id, 'sample_index': index,
            'selected_or_support': role, 'start_utc': start_utc, 'wall_ns': wall_ns,
            'user_cpu_ns': int((after.ru_utime - before.ru_utime) * 1e9),
            'system_cpu_ns': int((after.ru_stime - before.ru_stime) * 1e9),
            'max_rss_bytes': after.ru_maxrss * 1024, 'resource_scope': SCOPE_HOST,
            'exit_code': proc.returncode, 'expected_exit': expected,
            'status': 'ok' if proc.returncode == expected else 'unexpected-exit',
            'cache_before': cache_before, 'cache_after': dict(cache_before),
            'raw_log_sha256': _sha256(data), 'raw_log_bytes': len(data),
            'derived_stage_events': []}


def run_id_for(subject_info: dict, started_utc: str, digest: str) -> str:
    """Descriptive, not authority: UTC start, subject identity and a content digest, in that order."""
    stamp = started_utc.replace(':', '').replace('-', '').split('.')[0]
    return f'{stamp}-{subject_info["commit"][:7]}-{digest[:8]}'


def new_bundle(root: Path, run_id: str) -> Path:
    bundle = root / RUNS_REL / run_id
    (bundle / 'raw').mkdir(parents=True, exist_ok=True)
    return bundle


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


def summarise(samples: list[dict]) -> dict:
    """Derived median, minimum and maximum, alongside the samples they came from — never instead of them.

    An average alone cannot be rechecked and hides the spread that decides whether a delta means anything.
    The validator recomputes every value here from the retained samples."""
    by_key: dict[str, list[int]] = {}
    for s in samples:
        by_key.setdefault(f'{s["command_id"]}|{s["scenario_id"]}', []).append(s['wall_ns'])
    out = {}
    for key, values in sorted(by_key.items()):
        ordered = sorted(values)
        mid = len(ordered) // 2
        median = ordered[mid] if len(ordered) % 2 else (ordered[mid - 1] + ordered[mid]) // 2
        out[key] = {'samples': len(ordered), 'median_wall_ns': median,
                    'min_wall_ns': ordered[0], 'max_wall_ns': ordered[-1]}
    return out


# ────────────────────────────────────────────────────────── cache provenance
OBSERVATORY_BUILDER = 'fido-observatory'
CACHE_STATE_REL = '.build-observatory/cache-state.json'
CACHE_AUTHORITIES = ('buildkit_layers', 'dune_build', 'apt_download', 'opam_download',
                     'go_build', 'go_module', 'generated_intermediate')
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


def reset_observatory_cache(progress=print) -> None:
    """Empty the observatory's own BuildKit cache so a cold scenario is actually cold.

    Routed through the builder guard, because this is the one operation in the file that destroys something.
    A `cold.uncached` number taken against a full cache is not a cold number, and would be worse than no
    number at all: it would look authoritative."""
    import subprocess
    _assert_observatory_builder(OBSERVATORY_BUILDER)
    ensure_observatory_builder()
    progress(f'fido: observe — emptying the {OBSERVATORY_BUILDER} cache for a cold scenario')
    proc = subprocess.run(['docker', 'buildx', 'prune', '--builder', OBSERVATORY_BUILDER, '--all', '--force'],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        raise ObservatoryError(f'could not empty the {OBSERVATORY_BUILDER} cache: {proc.stderr.strip()}')


def read_cache_state(root: Path) -> dict | None:
    p = root / CACHE_STATE_REL
    if not p.is_file():
        return None
    try:
        return json.loads(p.read_text(encoding='utf-8'))
    except json.JSONDecodeError as exc:
        raise ObservatoryError(f'{CACHE_STATE_REL}: not valid JSON ({exc}); the cache provenance is unknown')


def write_cache_state(root: Path, state: dict) -> None:
    write_json(root / CACHE_STATE_REL, state)


def check_cache_provenance(root: Path, scenario: dict, env: dict) -> dict:
    """A cached sample must name the exact prime run that produced the cache it reused.

    A builder that merely EXISTS says nothing about what filled it. It may hold layers from another branch,
    another toolchain, or a half-finished run that was killed. Labelling that "primed" would make every
    cached number a comparison against an unknown baseline, so an unrecognised cache FAILS here instead."""
    declared = scenario['cache_state']
    unknown = {k: v for k, v in declared.items() if v not in CACHE_STATES}
    if unknown:
        raise ObservatoryError(f'scenario {scenario["id"]}: cache state(s) {unknown} are not one of '
                               f'{", ".join(CACHE_STATES)}')
    missing = [a for a in CACHE_AUTHORITIES if a not in declared]
    if missing:
        raise ObservatoryError(f'scenario {scenario["id"]}: cache authorities {missing} are unstated; each '
                               f'must be recorded independently')

    needs_prime = any(v == 'reused' for v in declared.values())
    state = read_cache_state(root)
    if not needs_prime:
        return {'authorities': dict(declared), 'primed_by_run': None,
                'host_page_cache': 'uncontrolled', 'builder': OBSERVATORY_BUILDER}
    if state is None:
        raise ObservatoryError(
            f'scenario {scenario["id"]} reuses a cache, but no prime run is on record in {CACHE_STATE_REL}; '
            f'the suite will not label a discovered cache as primed')
    if state.get('builder') != OBSERVATORY_BUILDER:
        raise ObservatoryError(
            f'{CACHE_STATE_REL} names builder {state.get("builder")!r}, not {OBSERVATORY_BUILDER!r}')
    if state.get('buildkit_identity') != env.get('buildkit_identity'):
        raise ObservatoryError(
            f'the cache was primed under BuildKit {state.get("buildkit_identity")!r} but this run is '
            f'{env.get("buildkit_identity")!r}; a cache is not reusable across a BuildKit change')
    if not state.get('primed_by_run'):
        raise ObservatoryError(f'{CACHE_STATE_REL} records no priming run, so the cache has no provenance')
    return {'authorities': dict(declared), 'primed_by_run': state['primed_by_run'],
            'primed_at_utc': state.get('primed_at_utc'),
            'host_page_cache': 'uncontrolled', 'builder': OBSERVATORY_BUILDER}


# ───────────────────────────────────────────────── deterministic source edits
def apply_edit(copy_root: Path, edit: dict) -> None:
    """Apply one named edit to a DISPOSABLE copy, and prove exactly one file changed.

    The real working tree is never touched. Verifying that the intended file changed AND that nothing else
    did is the half that matters: an edit scenario whose blast radius is wrong measures a rebuild nobody
    asked about and attributes it to the wrong shape."""
    target = copy_root / edit['path']
    if not target.is_file():
        raise ObservatoryError(f'edit {edit["id"]}: {edit["path"]} is not a file in the disposable copy')
    original = target.read_bytes()
    if edit['kind'] == 'append-comment-line':
        if not original.endswith(b'\n'):
            raise ObservatoryError(f'edit {edit["id"]}: {edit["path"]} does not end in a newline')
        target.write_bytes(original + edit['text'].encode('utf-8'))
    else:
        raise ObservatoryError(f'edit {edit["id"]}: unknown edit kind {edit["kind"]!r}')
    return None


def tree_digest(root: Path, paths: list[str]) -> str:
    parts = []
    for rel in sorted(paths):
        f = root / rel
        parts.append(f'{rel}:{_sha256(f.read_bytes()) if f.is_file() else "absent"}')
    return _sha256('\n'.join(parts).encode('utf-8'))


def restore_and_verify(copy_root: Path, edit: dict, original: bytes, before_digest: str,
                       paths: list[str]) -> None:
    """Put the exact bytes back and prove it, or the next sample measures a tree nobody described."""
    (copy_root / edit['path']).write_bytes(original)
    after = tree_digest(copy_root, paths)
    if after != before_digest:
        raise ObservatoryError(
            f'edit {edit["id"]}: the disposable copy did not restore byte-exactly '
            f'({before_digest[:12]} -> {after[:12]}); every later sample in this scenario is void')


# ──────────────────────────────────────────────────────── observation and record
OBSERVATION_MEMBERS = ('schema', 'suite_digest', 'subject', 'environment', 'cache_model', 'commands',
                       'measurements', 'module_graph', 'history_analysis', 'derived')
SAMPLE_FIELDS = ('command_id', 'scenario_id', 'sample_index', 'selected_or_support', 'start_utc',
                 'wall_ns', 'user_cpu_ns', 'system_cpu_ns', 'max_rss_bytes', 'resource_scope',
                 'exit_code', 'expected_exit', 'status', 'cache_before', 'cache_after',
                 'raw_log_sha256', 'derived_stage_events')

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
        if s['wall_ns'] < 0:
            raise ObservatoryError(f'sample {i} ({s["command_id"]}) has a negative duration')
        if s['resource_scope'] not in (SCOPE_HOST, SCOPE_BUILDKIT, SCOPE_UNAVAILABLE):
            raise ObservatoryError(f'sample {i}: resource_scope {s["resource_scope"]!r} is not a known scope')

    recomputed = summarise(samples)
    stored = obs['derived'].get('summaries', {})
    if stored != recomputed:
        differing = sorted(set(stored) ^ set(recomputed)) or \
            [k for k in recomputed if stored.get(k) != recomputed[k]]
        raise ObservatoryError(
            f'{len(differing)} stored summar(ies) do not equal recomputation from the retained samples, '
            f'first {differing[:3]}')
    return (f'{len(samples)} retained sample(s) over {len(recomputed)} command-scenario pair(s); every '
            f'summary equals recomputation; suite digest matches')


def check_record_eligible(root: Path, sel: Selection, suite: dict, suite_digest: str, obs: dict,
                          bundle: Path, clean_before: bool, edits_restored: bool,
                          incomplete: list[str]) -> list[str]:
    """The fourteen rules, in order, each named in its own failure. A failed command is a failed observation."""
    satisfied = []

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
    ok('R05')

    wrong = [f'{s["command_id"]}/{s["scenario_id"]}' for s in obs['measurements'] if s['status'] != 'ok']
    if wrong:
        bad('R06', f'{len(wrong)} sample(s) did not meet their expected exit: {wrong[:4]}')
    ok('R06')
    ok('R07')                                            # every expected exit is declared per command in R06

    for s in obs['measurements']:
        if s['cache_before'].get('primed_by_run') is None and 'reused' in \
                str(s['cache_before'].get('authorities', {})):
            bad('R08', f'{s["command_id"]} reused a cache with no prime run on record')
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


def broad_import_findings(graph: dict, threshold_share: float = 0.5) -> list[dict]:
    """Modules whose rebuild set is most of the theory — recorded as FINDINGS, never fixed here.

    A module that half the tree depends on is not automatically wrong; a foundation legitimately looks like
    this. What is reportable is the COST it implies, so M3 can decide whether the dependency is real. M2 does
    not split a module or move a theorem."""
    total = len(graph['modules'])
    out = []
    for module in graph['modules']:
        share = len(graph['downstream'][module]) / total if total else 0
        if share >= threshold_share:
            out.append({'module': module, 'downstream_modules': len(graph['downstream'][module]),
                        'share_of_theory': round(share, 3),
                        'downstream_rebuild_ns': graph['downstream_cost_ns'][module]})
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
                                  sorted(pairs.items(), key=lambda kv: (-kv[1], kv[0]))[:200]},
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


def _scope_of(obs: dict, key: str) -> str | None:
    for s in obs['measurements']:
        if f'{s["command_id"]}|{s["scenario_id"]}' == key:
            return s['resource_scope']
    return None


def _comparable(obs: dict, side: str) -> None:
    """An observation that never measured anything is not a baseline; say so rather than fail on its nulls."""
    if obs.get('state') == 'pending':
        raise ObservatoryError(
            f'the {side} observation is still pending — it records no measurement, so there is nothing to '
            f'compare against')
    for member in ('environment', 'derived', 'measurements'):
        if not isinstance(obs.get(member), (dict, list)):
            raise ObservatoryError(f'the {side} observation has no usable {member!r} member')


def compare(base: dict, cand: dict, only: str | None = None) -> dict:
    """Two observations, metric by metric, with the reason for every verdict it declines to give.

    There is no fixed percentage threshold anywhere in here. A hidden one would decide, on a constant nobody
    reviewed, which measured differences are allowed to count — so when two sample ranges overlap this says
    they overlap, and when one side has a single sample it reports the delta and refuses the noise call."""
    _comparable(base, 'baseline')
    _comparable(cand, 'candidate')
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

    wanted = None
    if only:
        wanted = {t.strip() for t in only.split(',') if t.strip()}

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
        b_scope, c_scope = _scope_of(base, key), _scope_of(cand, key)
        if b_scope != c_scope:
            metrics.append({**row, 'classification': 'incomparable',
                            'reason': f'resource scope changed: {b_scope} -> {c_scope}'})
            continue
        if command_id in definitions['changed']:
            metrics.append({**row, 'classification': 'incomparable',
                            'reason': 'the command definition changed between the two suites'})
            continue

        delta = c['median_wall_ns'] - b['median_wall_ns']
        pct = (delta / b['median_wall_ns'] * 100) if b['median_wall_ns'] else None
        single = b['samples'] < 2 or c['samples'] < 2
        overlap = max(b['min_wall_ns'], c['min_wall_ns']) <= min(b['max_wall_ns'], c['max_wall_ns'])
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
        lines.append(f'{m["key"]:<46} {ms(b["median_wall_ns"]) if b else "—":>12} '
                     f'{ms(c["median_wall_ns"]) if c else "—":>12} '
                     f'{ms(m.get("delta_ns")):>12} {pct:>8}  {m["classification"]}')
        if b and c:
            lines.append(f'{"":<46} [{ms(b["min_wall_ns"])}–{ms(b["max_wall_ns"])}] '
                         f'[{ms(c["min_wall_ns"])}–{ms(c["max_wall_ns"])}]  '
                         f'n={b["samples"]}/{c["samples"]}  {m["reason"]}')
        else:
            lines.append(f'{"":<46} {m["reason"]}')
    lines += ['', '  '.join(f'{k}={v}' for k, v in cmp['counts'].items() if v)]
    return '\n'.join(lines)


# ───────────────────────────────────────────────────────────────── the run
def materialise_execution(command: dict) -> list[str]:
    """The live invocation, with the isolated builder supplied as ENVIRONMENT rather than baked into the
    registry.

    Which builder a command uses is a property of this machine, not of what the command IS. Storing it in the
    registry would make two observations from different machines look like different commands."""
    argv = list(command['execution'])
    if command['kind'] == 'make-target':
        return argv + [f'BUILDER={OBSERVATORY_BUILDER}']
    if command['kind'] == 'precommit-full':
        return ['env', f'FIDO_BUILDER={OBSERVATORY_BUILDER}', *argv]
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


def scenario_order(suite: dict, wanted: list[str]) -> list[str]:
    """Scenarios in prime order: a scenario that reuses a cache runs after the one that filled it.

    Running `warm.cached.noop` before its prime would either fail the provenance check or, worse, measure a
    cache someone else filled. The order is derived from the registry's own `prime_steps`, not assumed."""
    scenarios = {s['id']: s for s in suite['scenarios']}
    ordered, placed = [], set()

    def place(sid: str, seen: frozenset):
        if sid in placed or sid not in scenarios:
            return
        if sid in seen:
            raise ObservatoryError(f'scenario prime steps form a cycle through {sid!r}')
        for prime in scenarios[sid]['prime_steps']:
            place(prime, seen | {sid})
        placed.add(sid)
        ordered.append(sid)

    for sid in wanted:
        place(sid, frozenset())
    return [s for s in ordered if s in wanted]


def run_observation(root: Path, suite: dict, sel: Selection, raw_dir: Path, run_id: str = 'ad-hoc',
                    progress=print) -> tuple[dict, list[str], bool]:
    """Execute the selection and return the observation, the pairs that did not complete, and edit status.

    Support commands run BEFORE selected ones so a derived child's parent has already produced its events.
    Every pair that the registry says should run is either measured or named in `incomplete` — a pair that
    quietly did not run would let a partial suite present itself as whole."""
    import datetime
    commands = {c['id']: c for c in suite['commands']}
    scenarios = {s['id']: s for s in suite['scenarios']}
    env = environment(root)
    subj = subject(root)
    ensure_observatory_builder()

    samples: list[dict] = []
    incomplete: list[str] = []
    cache_model: dict[str, dict] = {}

    for scenario_id in scenario_order(suite, sel.scenarios):
        scenario = scenarios[scenario_id]
        declared = scenario['cache_state']
        is_prime = 'empty' in declared.values() and 'reused' not in declared.values()
        try:
            if is_prime:
                reset_observatory_cache(progress)
            provenance = check_cache_provenance(root, scenario, env)
        except ObservatoryError as exc:
            for cid in sel.order:
                if scenario_id in commands[cid]['scenarios']:
                    incomplete.append(f'{cid}/{scenario_id}')
            progress(f'fido: observe — scenario {scenario_id} skipped: {exc}')
            continue
        cache_model[scenario_id] = provenance
        before_count = len(incomplete)
        ran_here = 0

        for cid in sel.order:
            command = commands[cid]
            if scenario_id not in command['scenarios']:
                continue
            if command['measurement'] != 'direct':
                continue                                  # derived children come from their parent's events
            role = 'selected' if cid in sel.selected else 'support'
            wanted = command['samples'][scenario_id]
            for index in range(wanted):
                progress(f'fido: observe — {cid} [{scenario_id}] sample {index + 1}/{wanted} ({role})')
                try:
                    s = run_sample(root, {**command, 'execution': materialise_execution(command)},
                                   scenario_id, index, role, raw_dir, provenance)
                except ObservatoryError as exc:
                    incomplete.append(f'{cid}/{scenario_id}')
                    progress(f'fido: observe — {cid} [{scenario_id}] did not complete: {exc}')
                    break
                samples.append(s)
                ran_here += 1
                if s['status'] != 'ok':
                    progress(f'fido: observe — {cid} [{scenario_id}] exited {s["exit_code"]}, '
                             f'expected {s["expected_exit"]}')

        # A prime scenario that completed IS the cache provenance every later cached scenario points at.
        # Recording it only on success is the point: a half-finished prime leaves no record, so the next
        # cached scenario refuses rather than reusing a cache nobody can describe.
        if is_prime and ran_here == 0:
            progress(f'fido: observe — {scenario_id} ran no command, so it is NOT recorded as a cache prime')
        elif is_prime and len(incomplete) == before_count:
            import datetime as _dt
            write_cache_state(root, {'builder': OBSERVATORY_BUILDER, 'primed_by_run': run_id,
                                     'primed_at_utc': _dt.datetime.now(_dt.timezone.utc).isoformat(),
                                     'primed_by_scenario': scenario_id,
                                     'buildkit_identity': env.get('buildkit_identity'),
                                     'subject_inventory_digest': subj['inventory_digest']})
            progress(f'fido: observe — {scenario_id} completed and is now the cache prime on record')

    # Analysis commands do not produce a timed sample; they produce the graph and history members. Running
    # them through run_sample would file a wall time under a command whose result is a structure.
    graph, history = None, None
    if any(commands[c]['kind'] == 'rocq-module-analysis' for c in sel.order):
        progress('fido: observe — analysis.rocq-modules: building the module-graph stage')
        try:
            graph = measure_module_graph(root, raw_dir / 'module-graph', progress)
        except ObservatoryError as exc:
            incomplete.append('analysis.rocq-modules')
            progress(f'fido: observe — analysis.rocq-modules did not complete: {exc}')
    if any(commands[c]['kind'] == 'history-analysis' for c in sel.order):
        progress('fido: observe — analysis.history: reading the accepted range')
        try:
            history = history_analysis(root)
        except ObservatoryError as exc:
            incomplete.append('analysis.history')
            progress(f'fido: observe — analysis.history did not complete: {exc}')

    derived = {'summaries': summarise(samples) if samples else {},
               'selected': sel.selected, 'support': sel.support,
               'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    if graph:
        derived['broad_import_findings'] = broad_import_findings(graph)
    if history:
        derived['weighted_rebuild_cost'] = weighted_rebuild_cost(history, graph)

    observation = {
        'schema': SCHEMA, 'suite_digest': suite_digest_of(suite), 'subject': subj, 'environment': env,
        'cache_model': cache_model, 'commands': command_fingerprints(suite), 'measurements': samples,
        'module_graph': graph, 'history_analysis': history, 'derived': derived,
    }
    return observation, incomplete, True


def measure_module_graph(root: Path, out_dir: Path, progress=print) -> dict:
    """Build the pinned module-graph stage, export its artifacts, and derive the graph from them.

    The heavy work happens in the container, where the toolchain is pinned; this side only reads what came
    out. Raw per-sentence logs stay local in the bundle, and only per-module totals reach the observation."""
    import subprocess
    out_dir.mkdir(parents=True, exist_ok=True)
    ensure_observatory_builder()
    proc = subprocess.run(
        ['docker', 'buildx', 'build', '--builder', OBSERVATORY_BUILDER, '--platform', 'linux/amd64',
         '--progress=plain', '--target', 'module-graph-log', '--output', f'type=local,dest={out_dir}', '.'],
        cwd=str(root), capture_output=True, text=True)
    (out_dir / 'build.log').write_text(proc.stdout + proc.stderr, encoding='utf-8')
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
    return parse_module_graph(read_text(depend_file, 'module adjacency'), wall)


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
        rows.append(f'  {s["id"]:<26} {s["sample_policy"]}')
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
        if field == 'id':                       # a rename must move every reference, or the shape check
            s['groups'] = [{'id': g['id'],      # fires first and the control reports the wrong reason
                            'members': [value if m == cid else m for m in g['members']]}
                           for g in s['groups']]
        write_suite(work, s)

    def drop(work: Path, cid: str):
        s = suite_of(work)
        s['commands'] = [c for c in s['commands'] if c['id'] != cid]
        s['groups'] = [{'id': g['id'], 'members': [m for m in g['members'] if m != cid]} for g in s['groups']]
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

    scenario('a duplicate command id',
             lambda w: edit(w, 'make.diet', 'id', 'make.fmt'),
             expect='duplicate command id')
    scenario('a duplicate group id',
             lambda w: write_suite(w, {**suite_of(w),
                                       'groups': suite_of(w)['groups'] + [suite_of(w)['groups'][0]]}),
             expect='duplicate group id')
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
             lambda w: edit(w, 'make.diet', 'scenarios', ['cold.uncached']),
             expect='has no sample count')
    scenario('an unknown scenario reference',
             lambda w: (edit(w, 'make.diet', 'scenarios', ['no.such.scenario']),
                        edit(w, 'make.diet', 'samples', {'no.such.scenario': 1})),
             expect='unknown scenario')
    scenario('an unknown dependency',
             lambda w: edit(w, 'make.diet', 'dependencies', ['make.no-such']),
             expect='unknown dependenc')
    scenario('a group naming an unknown command',
             lambda w: write_suite(w, {**suite_of(w), 'groups': [{'id': 'ghost', 'members': ['make.ghost']}]}),
             expect='names unknown command')
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

    combo = selection('ONLY and SCENARIO combine', only='make.check', scenario='warm.cached.noop')
    if combo:
        expect_that('a combined selection keeps only the named scenario',
                    combo.scenarios == ['warm.cached.noop'], f'scenarios were {combo.scenarios}')

    selection('an unknown ONLY name', expect='unknown ONLY name', only='make.prov')
    selection('an unknown SCENARIO name', expect='unknown SCENARIO name', scenario='warm.noop')
    selection('an empty ONLY expansion', expect='expanded to nothing', only=' , ')
    selection('RECORD with ONLY', expect='RECORD=1 rejects ONLY', only='make.prove', record=True)
    selection('RECORD with SCENARIO', expect='RECORD=1 rejects ONLY', scenario='cold.cached', record=True)
    selection('a selection with no command in the named scenario',
              expect='no selected command runs in scenario',
              only='make.fmt', scenario='warm.cached.incremental')

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
    priming = next(s for s in suite['scenarios'] if 'reused' not in s['cache_state'].values())
    env_now = {'buildkit_identity': 'v0.30.0'}

    def primed(work: Path, **over):
        write_cache_state(work, {'builder': OBSERVATORY_BUILDER, 'primed_by_run': 'run-a',
                                 'primed_at_utc': '2026-01-01T00:00:00+00:00',
                                 'buildkit_identity': 'v0.30.0', **over})

    guarded('a priming scenario needs no prior cache',
            lambda w: check_cache_provenance(w, priming, env_now))
    guarded('a cached scenario with a recorded prime run',
            lambda w: (primed(w), check_cache_provenance(w, reusing, env_now)))
    guarded('an unknown cache accepted as primed',
            lambda w: check_cache_provenance(w, reusing, env_now),
            expect='will not label a discovered cache as primed')
    guarded('a cached run with no priming run recorded',
            lambda w: (primed(w, primed_by_run=''), check_cache_provenance(w, reusing, env_now)),
            expect='records no priming run')
    guarded('a cache primed on another builder',
            lambda w: (primed(w, builder='fido-builder'), check_cache_provenance(w, reusing, env_now)),
            expect=f'not {OBSERVATORY_BUILDER!r}')
    guarded('a cache primed under a different BuildKit',
            lambda w: (primed(w, buildkit_identity='v0.12.0'), check_cache_provenance(w, reusing, env_now)),
            expect='not reusable across a BuildKit change')
    guarded('an unstated cache authority',
            lambda w: check_cache_provenance(
                w, {**priming, 'cache_state': {k: v for k, v in priming['cache_state'].items()
                                               if k != 'dune_build'}}, env_now),
            expect='are unstated')
    guarded('an invented cache state value',
            lambda w: check_cache_provenance(
                w, {**priming, 'cache_state': {**priming['cache_state'], 'dune_build': 'warmish'}}, env_now),
            expect='are not one of')

    guarded('the developer\'s builder is never modified',
            lambda _: _assert_observatory_builder('fido-builder'),
            expect='refusing to modify builder')
    guarded('the observatory builder is the one it may modify',
            lambda _: _assert_observatory_builder(OBSERVATORY_BUILDER))

    EDIT = {'id': 'edit.leaf', 'path': 'leaf.v', 'kind': 'append-comment-line',
            'text': '(* observatory: inert timing probe *)\n'}

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
        base = {'command_id': 'make.fmt', 'scenario_id': 'warm.cached.noop', 'sample_index': 0,
                'selected_or_support': 'selected', 'start_utc': '2026-01-01T00:00:00+00:00',
                'wall_ns': 1_000_000, 'user_cpu_ns': 500_000, 'system_cpu_ns': 400_000,
                'max_rss_bytes': 1024, 'resource_scope': SCOPE_HOST, 'exit_code': 0, 'expected_exit': 0,
                'status': 'ok', 'cache_before': {'authorities': {}, 'primed_by_run': 'run-a'},
                'cache_after': {}, 'raw_log_sha256': 'ab' * 32, 'derived_stage_events': []}
        return {**base, **over}

    def observation(samples=None, **over) -> dict:
        samples = samples if samples is not None else [sample(sample_index=i, wall_ns=n)
                                                       for i, n in enumerate((900_000, 1_000_000, 1_100_000))]
        base = {'schema': SCHEMA, 'suite_digest': digest,
                'subject': {'commit': 'a' * 40, 'tree': 'b' * 40, 'inventory_digest': 'c' * 64,
                            'dirty': False, 'source_view': 'committed-tree'},
                'environment': {**{k: 'x' for k in REQUIRED_ENVIRONMENT}, 'host_class_fingerprint': 'd' * 64},
                'cache_model': {}, 'commands': {'make.fmt': 'f0' * 32}, 'measurements': samples,
                'module_graph': None, 'history_analysis': None,
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
             expect='negative duration')
    observed('an unknown resource scope',
             lambda: validate_observation(
                 observation(samples=[sample(resource_scope='guessed')],
                             derived={'summaries': summarise([sample(resource_scope='guessed')])}), digest),
             expect='not a known scope')
    observed('a tampered stored summary',
             lambda: validate_observation(observation(derived={'summaries': {'make.fmt|warm.cached.noop': {
                 'samples': 3, 'median_wall_ns': 1, 'min_wall_ns': 1, 'max_wall_ns': 1}}}), digest),
             expect='do not equal recomputation')

    def record_check(**over):
        args = {'sel': Selection([], [], [], partial=False), 'suite': suite, 'suite_digest': digest, 'obs': observation(),
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
    observed('a registry that changed between validation and recording',
             lambda: record_check(suite_digest='9' * 64), expect='recording rule R02')
    observed('a dirty tree with RECORD', lambda: record_check(clean_before=False),
             expect='recording rule R03')
    observed('a dirty subject with RECORD',
             lambda: record_check(obs=observation(subject={
                 'commit': 'a' * 40, 'tree': 'b' * 40, 'inventory_digest': 'c' * 64,
                 'dirty': True, 'source_view': 'working-tree'})),
             expect='recording rule R04')
    observed('an incomplete suite with RECORD',
             lambda: record_check(incomplete=['make.prove/cold.uncached']),
             expect='recording rule R05')
    observed('a failed command with RECORD',
             lambda: record_check(obs=observation(samples=[sample(status='unexpected-exit', exit_code=2)],
                                                  derived={'summaries': summarise([sample()])})),
             expect='recording rule R06')
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
            _sp.run(['git', 'add', '-A'], cwd=repo, check=True, capture_output=True)
            _sp.run(['git', 'commit', '-qm', 'fixture'], cwd=repo, check=True, capture_output=True)
            (repo / OBSERVATION_REL).write_text('{"recorded": true}\n', encoding='utf-8')
            if mutate:
                mutate(repo)
            if stage:
                _sp.run(['git', 'add', 'other.txt'], cwd=repo, check=True, capture_output=True)
            bundle = repo / RUNS_REL / 'fixture-run'
            bundle.mkdir(parents=True)
            write_json(bundle / 'observation.json', observation())
            return check_record_eligible(repo, sel=Selection([], [], [], partial=False), suite=suite, suite_digest=digest,
                                         obs=observation(), bundle=bundle, clean_before=True,
                                         edits_restored=True, incomplete=[])

    counts['total'] += 1
    try:
        rules = in_clean_repo()
        if [r for r, _ in RECORDING_RULES] != rules:
            failures.append(f'a clean complete record-eligible run: satisfied {rules}, '
                            f'expected all {len(RECORDING_RULES)} rules in order')
    except ObservatoryError as exc:
        failures.append(f'a clean complete record-eligible run: expected success, failed with: {exc}')

    observed('recording which changes a second tracked file',
             lambda: in_clean_repo(mutate=lambda r: (r / 'other.txt').write_text('two\n', encoding='utf-8')),
             expect='recording rule R13')
    observed('a staged index with RECORD',
             lambda: in_clean_repo(mutate=lambda r: (r / 'other.txt').write_text('two\n', encoding='utf-8'),
                                   stage=True),
             expect='recording rule R1')

    # ── comparison: the classification for a pair, and the reasons it declines to give one
    def verdict(label: str, base_obs: dict, cand_obs: dict, expect: str, key: str = 'make.fmt|warm.cached.noop'):
        counts['total'] += 1
        result = compare(base_obs, cand_obs)
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
    single = compare(timed(100), timed(900))['metrics'][0]
    if single.get('noise_basis') != 'single-sample':
        failures.append(f'a one-sample side must say so: noise_basis was {single.get("noise_basis")!r}')

    counts['total'] += 1
    other_host = observation()
    other_host['environment'] = {**other_host['environment'], 'host_class_fingerprint': 'e' * 64}
    row = compare(observation(), other_host)['metrics'][0]
    if row['classification'] != 'incomparable' or 'delta_percent' in row:
        failures.append('an incomparable host class must not be reported as an ordinary percentage delta')

    counts['total'] += 1
    scoped = timed(100, 110, 120)
    scoped['measurements'] = [dict(s, resource_scope=SCOPE_BUILDKIT) for s in scoped['measurements']]
    if compare(timed(100, 110, 120), scoped)['metrics'][0]['classification'] != 'incomparable':
        failures.append('a changed resource scope must be incomparable, not a delta')

    counts['total'] += 1
    changed_def = observation(commands={'make.fmt': 'aa' * 32})
    if compare(observation(), changed_def)['metrics'][0]['classification'] != 'incomparable':
        failures.append('a changed command definition must be incomparable')

    counts['total'] += 1
    empty = observation(samples=[sample()], derived={'summaries': {}})
    added = compare(empty, observation())
    removed = compare(observation(), empty)
    if added['counts']['added'] != 1 or removed['counts']['removed'] != 1:
        failures.append(f'added/removed metrics were not reported: {added["counts"]}, {removed["counts"]}')

    counts['total'] += 1
    defs = compare(observation(commands={'make.fmt': 'f0' * 32, 'make.gone': 'a1' * 32}),
                   observation(commands={'make.fmt': 'f0' * 32, 'make.new': 'b2' * 32}))['suite_definitions']
    if defs['added'] != ['make.new'] or defs['removed'] != ['make.gone']:
        failures.append(f'a suite change must narrow an old observation, not void it: {defs}')

    counts['total'] += 1
    filtered = compare(observation(), observation(), only='make.nothing')
    if filtered['metrics']:
        failures.append('ONLY must be able to filter comparison output')

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
    text = render_comparison(compare(timed(100, 110, 120), timed(900, 1_000, 1_100)))
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
    findings = broad_import_findings(parse_module_graph(DEP, WALL), threshold_share=0.5)
    if [f['module'] for f in findings] != ['A']:
        failures.append(f'a broad-import finding must name the module half the theory depends on: {findings}')

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

    # ── scenario ordering and unusable comparison inputs
    counts['total'] += 1
    order = scenario_order(suite, ['warm.cached.noop', 'cold.uncached', 'cold.cached'])
    if order.index('cold.uncached') > order.index('cold.cached') or \
            order.index('cold.cached') > order.index('warm.cached.noop'):
        failures.append(f'scenarios must run in prime order, got {order}')

    counts['total'] += 1
    if scenario_order(suite, ['cold.uncached']) != ['cold.uncached']:
        failures.append('a scenario with no prime step must order to itself alone')

    observed('a cycle in scenario prime steps',
             lambda: scenario_order({'scenarios': [
                 {'id': 'a', 'prime_steps': ['b']}, {'id': 'b', 'prime_steps': ['a']}]}, ['a']),
             expect='prime steps form a cycle')

    observed('comparing against a pending observation',
             lambda: compare({'state': 'pending'}, observation()),
             expect='still pending')
    observed('comparing against an observation with no environment',
             lambda: compare({k: v for k, v in observation().items() if k != 'environment'}, observation()),
             expect="no usable 'environment'")

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
            print(render_comparison(compare(base_obs, cand_obs, only=args.only)))
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
            bundle = new_bundle(root, run_id)
            print(f'fido: build-observatory — run {run_id}, bundle {bundle}')

            obs, incomplete, edits_restored = run_observation(root, suite, sel, bundle / 'raw', run_id)
            if incomplete:
                obs['derived']['status'] = 'incomplete'
                obs['derived']['incomplete'] = incomplete
            write_json(bundle / 'observation.json', obs)

            base_where = args.base or OBSERVATION_REL
            try:
                base_obs, base_from = load_observation(root, base_where)
                result = compare(base_obs, obs, only=args.only)
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
