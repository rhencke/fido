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


def write_json(path: Path, obj) -> bytes:
    data = (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=False) + '\n').encode('utf-8')
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
        if args.observe:
            suite = load_suite(root)
            check_coverage(root, suite)
            sel = select(suite, only=args.only, scenario=args.scenario, record=args.record)
            if sel.support:
                print(f'fido: build-observatory — {len(sel.support)} dependenc(ies) added to the selection '
                      f'and measured as support: {", ".join(sel.support)}')
            print(f'fido: build-observatory — {len(sel.selected)} selected command(s) over '
                  f'{len(sel.scenarios)} scenario(s){" (PARTIAL run)" if sel.partial else ""}')
    except ObservatoryError as exc:
        print(f'fido: BUILD-OBSERVATORY FAILED — {exc}', file=sys.stderr)
        return 1

    print(f'fido: BUILD-OBSERVATORY UNAVAILABLE — {PENDING}', file=sys.stderr)
    return 1


if __name__ == '__main__':
    sys.exit(main())
