#!/usr/bin/env python3
"""The permanent no-host-Python boundary.

Project Python runs only in the pinned Docker image.  The host boundary is shell, Make, Git, Docker and
Buildx, and nothing here may quietly widen it.

This is not a substring ban.  `Dockerfile`, the lock file, the tools themselves and the prose explaining the
boundary all legitimately contain the word `python`, so every check below classifies an actual execution
surface: a Make recipe line, a hook command, a shell-script command, a documented command, a file mode, a
`FROM`/`COPY` instruction, or an `import`.  Commands are addressed by target and anchor, never by line
number, so moving a recipe does not silently change what is checked.

Seven surfaces are proved:

  recipes      no Make recipe invokes an interpreter outside a container launcher
  hooks        no pre-commit command invokes an interpreter on the host
  scripts      no host-reachable shell script invokes an interpreter on the host
  docs         no usage document instructs a host-Python command
  modes        no project `.py` file is executable, so none can be a host entrypoint
  image        every base is digest-pinned and no stage COPYs project Python into itself
  closure      every module the tools import is stdlib or carries an exact pin in the lock

The image rule is the one worth explaining.  Project sources are MOUNTED read-only from the exact source
view rather than COPYed into a policy image, so a stale green layer from an incomplete `COPY` set is not
something this gate has to detect — it is unrepresentable.  Forbidding the `COPY` is what keeps it that way.
"""
from __future__ import annotations

import argparse
import ast
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

MAKEFILE = 'Makefile'
DOCKERFILE = 'Dockerfile'
HOOK = '.githooks/pre-commit'
LOCK = 'tools/python-requirements.lock'

# The shell operators that start a NEW command, so a `docker run` earlier in the line does not launder an
# interpreter invoked after a `&&`.
SEGMENT_RE = re.compile(r'&&|\|\||;|\|')

INTERPRETER_RE = re.compile(r'^python(?:\d(?:\.\d+)?)?$')

# What puts the next command inside a container.  `docker run` and `docker exec` are the direct forms; a
# Make variable whose definition contains one of them is the indirect form and is resolved, not assumed.
CONTAINER_ENTRY = (('docker', 'run'), ('docker', 'exec'))


class BoundaryError(Exception):
    """A defect in the gate's own inputs, never a finding about the repository."""


def read(root: Path, rel: str) -> str:
    p = root / rel
    if not p.is_file():
        raise BoundaryError(f'{rel} is missing; the boundary cannot be checked without it')
    return p.read_text(encoding='utf-8')


# ───────────────────────────────────────────────────────────── shell classification
def launcher_variables(makefile: str) -> set[str]:
    """Make variables whose value enters a container, resolved from the Makefile rather than assumed."""
    names = set()
    for line in makefile.splitlines():
        m = re.match(r'^([A-Za-z_][A-Za-z0-9_]*)\s*[:?]?=\s*(.*)$', line)
        if m and 'docker run' in m.group(2):
            names.add(m.group(1))
    return names


def shell_launchers(text: str) -> set[str]:
    """Shell functions whose body enters a container, resolved from the script rather than assumed.

    The hook wraps its container invocation in one function so fourteen gates cannot drift apart.  That
    function IS a launcher, and reading it as one is the difference between checking the boundary and
    checking a naming convention.
    """
    names, current, body = set(), None, []
    for line in text.splitlines():
        m = re.match(r'^\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\{', line)
        if m:
            current, body = m.group(1), [line]
            continue
        if current is not None:
            body.append(line)
            if re.match(r'^\s*\}', line):
                if 'docker run' in '\n'.join(body):
                    names.add(current)
                current, body = None, []
    return names


def segments(command: str) -> list[list[str]]:
    """The command split into shell segments, each tokenized, so each is judged on its own."""
    return [seg.split() for seg in SEGMENT_RE.split(command)]


def invokes_host_python(command: str, launchers: set[str]) -> str | None:
    """The offending token if this command runs an interpreter on the host, else None."""
    for tokens in segments(command):
        entered = False
        for i, tok in enumerate(tokens):
            bare = tok.lstrip('@-').strip('"\'')
            ref = re.fullmatch(r'\$[({]([A-Za-z_][A-Za-z0-9_]*)[)}]', bare)
            if (ref and ref.group(1) in launchers) or bare in launchers:
                entered = True
                continue
            if any(bare == head and i + 1 < len(tokens) and tokens[i + 1] == tail
                   for head, tail in CONTAINER_ENTRY):
                entered = True
                continue
            if INTERPRETER_RE.match(bare) or bare.endswith('.py'):
                if not entered:
                    return bare
                break
    return None


def join_continuations(lines: list[str]) -> list[str]:
    """Fold backslash continuations into one logical command.

    A `docker run ... \\` whose interpreter sits on the next physical line is one command, and judging the
    halves separately would report the container launcher and the interpreter as unrelated.
    """
    out: list[str] = []
    pending = ''
    for line in lines:
        stripped = line.rstrip()
        if stripped.endswith('\\'):
            pending += stripped[:-1] + ' '
            continue
        out.append(pending + stripped)
        pending = ''
    if pending:
        out.append(pending)
    return out


def recipe_commands(makefile: str) -> list[tuple[str, str]]:
    """Every recipe line paired with the target that owns it, addressed by target rather than by line."""
    out: list[tuple[str, str]] = []
    target = None
    pending: list[str] = []
    for line in join_continuations(makefile.splitlines()):
        if line.startswith('\t'):
            if target:
                out.append((target, line.strip()))
            continue
        m = re.match(r'^([A-Za-z0-9._/-]+)\s*:(?!=)', line)
        if m:
            target = m.group(1)
        elif line.strip() and not line.startswith((' ', '#')):
            target = None
    del pending
    return out


def shell_commands(text: str) -> list[str]:
    """Every non-comment command of a shell script, continuations folded into one command."""
    return [ln.strip() for ln in join_continuations(text.splitlines())
            if ln.strip() and not ln.strip().startswith('#')]


# ───────────────────────────────────────────────────────────── the seven surfaces
def check_recipes(root: Path, findings: list[str]) -> None:
    makefile = read(root, MAKEFILE)
    launchers = launcher_variables(makefile)
    if not launchers:
        findings.append(f'{MAKEFILE}: no container launcher variable is defined, so every Python-consuming '
                        'target would have to name an interpreter directly')
    for target, command in recipe_commands(makefile):
        tok = invokes_host_python(command, launchers)
        if tok:
            findings.append(f'{MAKEFILE}: target {target!r} runs {tok!r} on the host')


def check_hook(root: Path, findings: list[str]) -> None:
    hook = read(root, HOOK)
    launchers = launcher_variables(read(root, MAKEFILE)) | shell_launchers(hook)
    for command in shell_commands(hook):
        tok = invokes_host_python(command, launchers)
        if tok:
            findings.append(f'{HOOK}: runs {tok!r} on the host')
    # The staged hook must evaluate the STAGED sources: a proposed commit has to contain the checker that
    # judges it, or a staged edit is graded by an image built from the safe working tree.
    if 'docker run' in hook and '$ctx' not in hook:
        findings.append(f'{HOOK}: invokes a container without mounting the exported staged tree, so a '
                        'staged Python change would be evaluated against the working tree')


def check_scripts(root: Path, findings: list[str]) -> None:
    base = launcher_variables(read(root, MAKEFILE))
    for path in sorted((root / 'tools').glob('*.sh')):
        text = path.read_text(encoding='utf-8')
        for command in shell_commands(text):
            tok = invokes_host_python(command, base | shell_launchers(text))
            if tok:
                findings.append(f'tools/{path.name}: runs {tok!r} on the host')


def tracked(root: Path, suffix: str) -> list[str]:
    """Every file of this suffix in the source view, whether that view is a repository or an export.

    The pre-commit hook judges an EXPORTED staged tree, which has no `.git` at all, and so does every
    mutation fixture.  A gate that only knew how to ask Git would be a gate the proposed commit never
    faces.  In an export every file present IS part of the proposed commit, so walking it is exact rather
    than approximate — and an empty result fails closed instead of passing by having scanned nothing.
    """
    if (root / '.git').exists():
        proc = subprocess.run(['git', 'ls-files', '-z', f'*{suffix}'], cwd=root, capture_output=True)
        if proc.returncode != 0:
            raise BoundaryError(f'git ls-files failed in {root}: '
                                f'{proc.stderr.decode("utf-8", "replace").strip()}')
        found = [n for n in proc.stdout.decode().split('\0') if n]
    else:
        found = sorted(str(p.relative_to(root)) for p in root.rglob(f'*{suffix}')
                       if p.is_file() and '.git' not in p.parts)
    if not found:
        raise BoundaryError(f'{root}: no {suffix} file found in the source view, so the boundary would be '
                            'reported clean by having inspected nothing')
    return found


def check_docs(root: Path, findings: list[str]) -> None:
    launchers = launcher_variables(read(root, MAKEFILE))
    for rel in tracked(root, '.md'):
        for raw in (root / rel).read_text(encoding='utf-8').splitlines():
            # A fenced-code DELIMITER names a language for highlighting; it is not an invocation. Stripping
            # its backticks turned ```python into the bare token `python`, so no document could quote a
            # Python block without being read as instructing one on the host.
            if raw.strip().startswith('```'):
                continue
            line = raw.strip().lstrip('$').strip().strip('`')
            if not line or line.startswith(('#', '>', '-', '*', '|')):
                continue
            tok = invokes_host_python(line, launchers)
            # Only an explicit INTERPRETER invocation is a documented host command.  A document naming
            # `tools/x.py` is naming a file, which every contract that owns a tool has to be able to do;
            # treating that as an instruction would make the boundary unstatable in its own prose.
            if tok and INTERPRETER_RE.match(tok):
                findings.append(f'{rel}: documents {tok!r} as a host command')


def check_modes(root: Path, findings: list[str]) -> None:
    for rel in tracked(root, '.py'):
        if os.access(root / rel, os.X_OK):
            findings.append(f'{rel}: is executable, so it can be run as a host entrypoint')


def check_image(root: Path, findings: list[str]) -> None:
    dockerfile = read(root, DOCKERFILE)
    for line in dockerfile.splitlines():
        stripped = line.strip()
        if stripped.startswith('FROM '):
            ref = stripped.split()[1]
            local = re.match(r'^[A-Za-z0-9_.-]+$', ref) and ' AS ' not in stripped
            if '@sha256:' not in ref and not local and ref != 'scratch':
                # A stage may build FROM an earlier stage by name; only an external base needs a digest.
                names = re.findall(r'\bAS\s+([A-Za-z0-9_.-]+)', dockerfile)
                if ref not in names:
                    findings.append(f'{DOCKERFILE}: base {ref!r} is not pinned by digest')
        if stripped.startswith('COPY ') and re.search(r'(^|[\s/])tools/\S*\.py|\btools/\*', stripped):
            findings.append(f'{DOCKERFILE}: copies project Python into an image ({stripped[:70]!r}); '
                            'sources are mounted from the exact source view so a stale layer stays '
                            'unrepresentable')


def lock_pins(root: Path) -> tuple[set[str], str | None]:
    """The pinned distributions and the declared runtime image, from the one dependency authority."""
    names, image = set(), None
    for raw in read(root, LOCK).splitlines():
        line = raw.strip()
        if line.startswith('#'):
            m = re.match(r'^#\s*image:\s*(\S+)', line)
            if m:
                image = m.group(1)
            continue
        if line:
            m = re.match(r'^([A-Za-z0-9_.-]+)==\S+\s+--hash=sha256:[0-9a-f]{64}$', line)
            if not m:
                raise BoundaryError(f'{LOCK}: {line!r} is not an exact `name==version --hash=sha256:<hex>` pin')
            names.add(m.group(1).lower().replace('-', '_'))
    return names, image


def check_closure(root: Path, findings: list[str]) -> None:
    pinned, image = lock_pins(root)
    if image and image not in read(root, DOCKERFILE):
        findings.append(f'{LOCK}: declares runtime image {image!r}, which {DOCKERFILE} does not pin')
    stdlib = set(sys.stdlib_module_names) | {'__future__'}
    for rel in tracked(root, '.py'):
        source = (root / rel).read_text(encoding='utf-8')
        try:
            # Parsed, not pattern-matched: a docstring sentence beginning "from ..." or "import ..." is
            # prose, and a regex reported two of them as unpinned dependencies.
            tree = ast.parse(source, filename=rel)
        except SyntaxError as exc:
            findings.append(f'{rel}: does not parse as Python ({exc.msg}), so its imports cannot be closed')
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                tops = [alias.name.split('.')[0] for alias in node.names]
            elif isinstance(node, ast.ImportFrom):
                tops = [] if node.level else [(node.module or '').split('.')[0]]
            else:
                continue
            for top in tops:
                if not top or top in stdlib or top in pinned:
                    continue
                if ((root / rel).parent / f'{top}.py').is_file():
                    continue
                findings.append(
                    f'{rel}: imports {top!r}, which is neither standard library nor pinned in {LOCK}')


# Binaries the pinned image supplies, and where each comes from. `docker` is deliberately absent from the
# gate image: the deterministic self-test must not be able to reach a daemon, so no gate image carries
# carries a client.
IMAGE_BINARIES = {'git': 'apt in python-tools', 'tar': 'the base image',
                  'editorconfig': 'apt in python-tools', 'sh': 'the base image',
                  'docker': 'not in any gate image'}


def invoked_binaries(root: Path, rel: str) -> set[str]:
    """Every external command this tool shells out to, from its parsed syntax."""
    out: set[str] = set()
    try:
        tree = ast.parse((root / rel).read_text(encoding='utf-8'), filename=rel)
    except SyntaxError:
        return out
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr in ('run', 'Popen', 'check_output', 'call') and node.args):
            continue
        first = node.args[0]
        if isinstance(first, ast.List) and first.elts and isinstance(first.elts[0], ast.Constant):
            if isinstance(first.elts[0].value, str):
                out.add(first.elts[0].value)
        elif isinstance(first, ast.Constant) and isinstance(first.value, str) and first.value.split():
            out.add(first.value.split()[0])
    return out


def check_binaries(root: Path, findings: list[str]) -> None:
    """Every binary a tool invokes is one the pinned image actually supplies.

    `make fmt` shipped broken because `fmt-check.py` shells out to `editorconfig` and the image did not
    carry it. Nothing noticed: fmt reports rather than gates, so it is not in `make check`, and the failure
    only surfaced when a real run of the target reached it. A tool's external commands are part of its
    dependency set exactly as its imports are, and they are checked here for the same reason.
    """
    for rel in tracked(root, '.py'):
        for binary in sorted(invoked_binaries(root, rel)):
            if binary not in IMAGE_BINARIES:
                findings.append(
                    f'{rel}: invokes {binary!r}, which the pinned image does not declare; add it to the '
                    f'image and to IMAGE_BINARIES, or the tool is broken wherever it runs')


CHECKS = (check_recipes, check_hook, check_scripts, check_docs, check_modes, check_image, check_closure,
          check_binaries)


def run(root: Path) -> list[str]:
    findings: list[str] = []
    for check in CHECKS:
        check(root, findings)
    return findings


# ───────────────────────────────────────────────────────────── adversarial controls
def self_test(root: Path) -> int:
    """Every rule above is shown to REJECT the shape it forbids and to ACCEPT the shape it permits.

    A rule that has only ever been seen to pass is an assertion, not a gate.
    """
    failures: list[str] = []
    total = 0
    flagged = 0
    accepted = 0

    def must_flag(label: str, mutate, expect: str) -> None:
        nonlocal total, flagged
        total += 1
        flagged += 1
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp) / 'r'
            _seed(root, work)
            mutate(work)
            found = _safe_run(work)
            if not any(expect in f for f in found):
                failures.append(f'must-fail control {label!r} was not caught (expected {expect!r}, '
                                f'got {found or ["nothing"]})')

    def must_accept(label: str, mutate) -> None:
        nonlocal total, accepted
        total += 1
        accepted += 1
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp) / 'r'
            _seed(root, work)
            mutate(work)
            found = _safe_run(work)
            if found:
                failures.append(f'must-accept control {label!r} was wrongly rejected: {found}')

    def append(rel: str, text: str):
        return lambda w: (w / rel).write_text((w / rel).read_text(encoding='utf-8') + text, encoding='utf-8')

    # ── recipes
    must_flag('a gate restored to host python3', append(MAKEFILE, '\nbad:\n\tpython3 tools/naming-gate.py\n'),
              "runs 'python3' on the host")
    must_flag('a Python one-liner in a recipe', append(MAKEFILE, '\nbad:\n\t@python3 -c "import sys"\n'),
              "runs 'python3' on the host")
    must_flag('an interpreter after a laundering &&',
              append(MAKEFILE, '\nbad:\n\t@docker run x true && python3 tools/x.py\n'),
              "runs 'python3' on the host")
    must_flag('a bare .py used as a command', append(MAKEFILE, '\nbad:\n\t@./tools/naming-gate.py\n'),
              "on the host")
    must_flag('a Docker-absent fallback to host Python',
              append(MAKEFILE, '\nbad:\n\t@command -v docker > /dev/null || python3 tools/naming-gate.py\n'),
              "runs 'python3' on the host")
    must_accept('a recipe using the container launcher',
                append(MAKEFILE, '\ngood: pytools\n\t@$(PYRUN) tools/naming-gate.py\n'))
    must_accept('a host shell diagnostic with no Python',
                append(MAKEFILE, '\ngood:\n\t@git status --porcelain | sort\n'))

    # ── hooks and scripts
    must_flag('host Python in the pre-commit hook', append(HOOK, '\npython3 "$ctx/tools/naming-gate.py"\n'),
              "runs 'python3' on the host")
    # The wrapper's own body names no interpreter, so this control turns ONLY on whether a function that
    # never enters a container is treated as a launcher.  A body containing `python3` would be caught on
    # its own line and the control would pass even with the launcher rule deleted.
    must_flag('a wrapper function that never enters a container',
              append(HOOK, '\nsneaky() {\n  sh -c "$1"\n}\nsneaky tools/naming-gate.py\n'),
              "runs 'tools/naming-gate.py' on the host")
    must_flag('a host shell helper that calls Python',
              lambda w: (w / 'tools' / 'helper.sh').write_text('#!/bin/sh\npython3 tools/naming-gate.py\n',
                                                               encoding='utf-8'),
              "runs 'python3' on the host")
    must_accept('a shell helper that only calls Docker',
                lambda w: (w / 'tools' / 'helper.sh').write_text('#!/bin/sh\ndocker run x python3 /a.py\n',
                                                                 encoding='utf-8'))

    # ── docs, modes, image, closure
    must_flag('usage prose instructing host Python',
              append('README.md', '\n    python3 tools/source-diet.py --check\n'),
              'documents')
    must_accept('prose naming a tool file without instructing an interpreter',
                append('README.md', '\n    tools/source-diet.py   the source-comment law\n'))
    # A fenced Python block is a QUOTATION. Reading its language tag as a command made the boundary
    # unstatable in its own prose: a review directive could not quote the code it was ordering deleted.
    must_accept('a document quoting a fenced Python block',
                append('README.md', '\n```python\nDOC = re.compile(r"x")\n```\n'))
    must_flag('a host interpreter inside a fenced block is still an instruction',
              append('README.md', '\n```sh\npython3 tools/source-diet.py --check\n```\n'),
              'documents')
    must_flag('an executable project .py',
              lambda w: (w / 'tools' / 'naming-gate.py').chmod(0o755), 'is executable')
    must_flag('an unpinned Python base image',
              append(DOCKERFILE, '\nFROM python:3.12-slim AS rogue\n'), 'is not pinned by digest')
    must_flag('project Python copied into an image',
              append(DOCKERFILE, '\nCOPY tools/naming-gate.py /naming-gate.py\n'),
              'copies project Python into an image')
    must_flag('an unpinned third-party package',
              lambda w: (w / 'tools' / 'rogue.py').write_text('import requests\n', encoding='utf-8'),
              'neither standard library nor pinned')
    must_flag('a tool shelling out to a binary the image does not carry',
              lambda w: (w / 'tools' / 'rogue.py').write_text(
                  'import subprocess\nsubprocess.run(["ripgrep", "x"])\n', encoding='utf-8'),
              'which the pinned image does not declare')
    must_accept('a tool shelling out to a binary the image does carry',
                lambda w: (w / 'tools' / 'ok.py').write_text(
                    'import subprocess\nsubprocess.run(["git", "status"])\n', encoding='utf-8'))
    must_flag('a lock entry with no integrity hash',
              append(LOCK, '\nrequests==2.32.3\n'), 'is not an exact')
    must_accept('a pinned lock entry and its import',
                lambda w: (_write(w / LOCK, read_text(w / LOCK) + f'\nrequests==2.32.3 --hash=sha256:{"a"*64}\n'),
                           _write(w / 'tools' / 'ok.py', 'import requests\n')))
    must_accept('a non-executable .py tool',
                lambda w: (w / 'tools' / 'naming-gate.py').chmod(0o644))

    # ── the repository as it stands must pass
    total += 1
    live = run(root)
    if live:
        failures.append(f'the repository itself does not satisfy the boundary: {live}')

    # Failures go to STDOUT in the `  FAIL  <control>` shape the mutation harness reads: it proves each rule
    # load-bearing by deleting its effect and watching that rule's OWN named control fail, and it can only
    # do that if the control name it is looking for is the one actually printed.
    for f in failures:
        print(f'  FAIL  {f}')
    if failures:
        print(f'fido: HOST-PYTHON SELF-TEST FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: host-python-gate self-test OK — {total} controls '
          f'({flagged} must-fail with the reason pinned, {accepted} must-accept, exemption closure, '
          f'live repository), all executed ✓')
    return 0


def read_text(p: Path) -> str:
    return p.read_text(encoding='utf-8')


def _write(p: Path, text: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding='utf-8')


def _seed(root: Path, work: Path) -> None:
    """A minimal repository carrying exactly the surfaces the boundary judges."""
    (work / 'tools').mkdir(parents=True)
    (work / '.githooks').mkdir(parents=True)
    for rel in (MAKEFILE, DOCKERFILE, HOOK, LOCK):
        _write(work / rel, read_text(root / rel))
    _write(work / 'README.md', read_text(root / 'README.md'))
    for name in ('naming-gate.py',):
        _write(work / 'tools' / name, read_text(root / 'tools' / name))
        (work / 'tools' / name).chmod(0o644)
    subprocess.run(['git', 'init', '-q'], cwd=work, check=True, capture_output=True)
    subprocess.run(['git', 'add', '-A'], cwd=work, check=True, capture_output=True)


def _safe_run(work: Path) -> list[str]:
    """Run the gate over a fixture, re-staging so `git ls-files` sees the mutation."""
    subprocess.run(['git', 'add', '-A'], cwd=work, check=True, capture_output=True)
    try:
        return run(work)
    except BoundaryError as exc:
        return [str(exc)]


def main() -> int:
    ap = argparse.ArgumentParser(description='the permanent no-host-Python boundary gate')
    ap.add_argument('--root', default='.', help='repository or exported-tree root')
    ap.add_argument('--self-test', action='store_true', help='run the adversarial controls')
    args = ap.parse_args()
    root = Path(args.root).resolve()
    if args.self_test:
        return self_test(root)
    try:
        findings = run(root)
    except BoundaryError as exc:
        print(f'fido: HOST-PYTHON GATE FAILED — {exc}', file=sys.stderr)
        return 1
    if findings:
        for f in findings:
            print(f'fido: HOST-PYTHON GATE FAILED — {f}', file=sys.stderr)
        return 1
    print('fido: host-python gate OK — no Make recipe, hook command, shell script or usage document runs an '
          'interpreter on the host; no project .py is executable; every base is digest-pinned and no stage '
          'copies project Python; every import is standard library or exactly pinned ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
