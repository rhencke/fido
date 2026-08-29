#!/usr/bin/env python3
"""Mutation tests for the policy gates: prove every root helper is load-bearing.

A gate's own self-test proves its controls PASS. It cannot prove they would FAIL if the rule they protect were
removed — and a control that survives the deletion of its rule is not evidence, it is decoration. A rule
can be real while the control protecting it has never been watched failing in the shape that matters.

So each mutant below deletes exactly one root helper's effect, reruns that gate's own self-test in a copy of
the tree, and asserts BOTH that the self-test fails AND that the specific controls which depend on that rule
are among the failures. Naming the expected controls is the point: a mutation that breaks the tool in some
unrelated way would otherwise look like a passing mutation test.

Every anchor is asserted to occur EXACTLY ONCE before any replacement, so a refactor that moves a helper makes
this fail loudly instead of silently testing nothing.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

DIET = 'tools/source-diet.py'
HOSTPY = 'tools/host-python-gate.py'
WORKTREE = 'tools/worktree-list.py'
PERFEV = 'tools/perf-evidence-validate.py'

# (tool, label, anchor, replacement, controls that MUST appear among the failures)
MUTANTS = (
    (PERFEV, 'the incomplete-path rejection, so complete=no cannot satisfy required coverage',
     "        if row['complete'] == 'no' and row['relation'] in RELATIONS:",
     "        if False:",
     ('incomplete path cannot satisfy required scenario coverage',)),

    (PERFEV, 'the published-basis binding, so new evidence cannot claim a foreign basis',
     "        elif evidence_changed:",
     "        elif False:",
     ('published final-candidate rows bound to a basis other than the one measured',)),

    (PERFEV, 'the final-candidate coverage requirement, so a baseline-only file is not current evidence',
     "    if not any(rl == 'final-candidate' for (_, rl) in seen):",
     "    if False:",
     ('baseline-only file passes as current evidence',)),

    (HOSTPY, 'the host-interpreter classification itself',
     "            if INTERPRETER_RE.match(bare) or bare.endswith('.py'):",
     "            if False:",
     ('a gate restored to host python3', 'host Python in the pre-commit hook')),

    (HOSTPY, 'the container-entry resolution, so a launcher cannot be forged',
     "                if 'docker run' in '\\n'.join(body):",
     "                if True:",
     ('a wrapper function that never enters a container',)),

    (HOSTPY, 'folding continuations, so a launcher and its interpreter stay one command',
     "        if stripped.endswith('\\\\'):",
     "        if False:",
     ('a recipe using the container launcher',)),

    (HOSTPY, 'the executable-mode rule',
     "        if os.access(root / rel, os.X_OK):",
     "        if False:",
     ('an executable project .py',)),

    (HOSTPY, 'the digest-pin rule for external bases',
     "            if '@sha256:' not in ref and not local and ref != 'scratch':",
     "            if False:",
     ('an unpinned Python base image',)),

    (HOSTPY, 'the no-project-Python-in-an-image rule',
     "        if stripped.startswith('COPY ') and re.search(r'(^|[\\s/])tools/\\S*\\.py|\\btools/\\*', stripped):",
     "        if False:",
     ('project Python copied into an image',)),

    (HOSTPY, 'the external-binary closure, so a tool cannot need a binary the image lacks',
     "            if binary not in IMAGE_BINARIES:",
     "            if False:",
     ('a tool shelling out to a binary the image does not carry',)),

    (HOSTPY, 'the standard-library-or-pinned import closure',
     "                if not top or top in stdlib or top in pinned:",
     "                if True:",
     ('an unpinned third-party package',)),

    (WORKTREE, 'the on-disk filter, so a staged deletion is not resurrected',
     "    return [name for name in tracked_and_untracked(root)\n"
     "            if os.path.lexists(os.path.join(os.fsencode(root), name))]",
     "    return tracked_and_untracked(root)",
     ('a tracked file deleted on disk is not resurrected from the index',)),

    (DIET, 'the default-comment law',
     "            is_default = lines == 1 and len(block) == 1 and not over",
     "            is_default = True",
     ('a two-line default comment', 'a 121-character comment', 'an exception over four lines')),

    (DIET, 'whitespace adjacency merging',
     "        if current and text[current[-1].end:tok.start].strip() == '':",
     "        if False:",
     ('two adjacent one-line comments', 'two comments on one line separated only by whitespace')),

    (DIET, 'the sentence counter',
     "        if j >= n or body[j].isspace():\n            count += 1",
     "        if False:\n            count += 1",
     ('two sentences in one comment',)),

    (DIET, 'archaeology rejection',
     "            hit = ARCHAEOLOGY_RE.search(body)",
     "            hit = None",
     ('repair archaeology',)),

    (DIET, 'the exception hash',
     "            if row['comment_sha256'] != entry['sha256']:",
     "            if False:",
     ('a changed comment hash',)),

    (DIET, 'the orphan half of the exception relation',
     "    orphans = sorted(set(seen) - matched)",
     "    orphans = []",
     ('an orphan ledger row',)),

    (DIET, 'refusing a diet over nothing',
     "    if not blocks_by_file:",
     "    if False:",
     ('a snapshot containing no .v files',)),

    (DIET, 'the plain comment form',
     "            if DOC_MARKER.search(raw):",
     "            if False:",
     ('a documentation marker comment',)),

    (DIET, 'banner rejection',
     "            hit = BANNER_RUN.search(body)",
     "            hit = None",
     ('a decorative banner',)),

    (DIET, 'section-label rejection',
     "            hit = SECTION_LABEL.search(body)",
     "            hit = None",
     ('a section label', 'a lettered label', 'a shouted multi-word label')),

    (DIET, 'identifier-only rejection',
     "            if IDENTIFIER_ONLY.match(stripped):",
     "            if False:",
     ('an identifier-only comment', 'a constructor-only comment',
      'a bracketed identifier-only comment')),

    (DIET, 'proof-case label rejection',
     "            if PROOF_CASE_LABEL.match(stripped):",
     "            if False:",
     ('a proof-case label',)),

    (DIET, 'bullet label rejection',
     "            if BULLET_LABEL.match(stripped):",
     "            if False:",
     ('a bullet label',)),

    (DIET, 'decorative-glyph rejection',
     "            hit = DECORATIVE_GLYPH.search(body)",
     "            hit = None",
     ('a two-character box-drawing banner', 'a star decoration')),
)

DOCKERFILE = 'Dockerfile'
LAYER_BEGIN = 'LAYER-GATE-LIB BEGIN'
LAYER_END = 'LAYER-GATE-LIB END'

# The layer-dependency gate needs pinned `rocq dep`, so it lives as a decision block in the Dockerfile prover
# stage rather than a host Python tool. Its decision is a single AWK pass over the Dune module universe, this
# run's rocq dep output, and the sole ARCHITECTURE policy, guarded by two shell status checks (the rocq dep
# extractor and the awk verdict pass). It is mutation-tested under this same authority: extract the block,
# neuter one root decision (a shell status check or an awk predicate), run its self-test with `sh`, and require
# the named control(s) among the failures — exactly the shape used for the Python gates.
LAYER_MUTANTS = (
    ('the dependency-extractor success check', '[ "$la_status" = 0 ]', 'true',
     ('a forced extractor failure',)),
    ('the verdict-operation success check', '[ "$la_ast" = 0 ]', 'true',
     ('a verdict operation that emitted pass-looking output then failed',)),
    ('the module-universe premise', 'if (nm==0)', 'if (0)',
     ('an empty module universe',)),
    ('the dependency-output read premise', 'if (rr<0)', 'if (0)',
     ('an unreadable dependency output',)),
    ('the policy-file read premise', 'if (ra<0)', 'if (0)',
     ('an unreadable policy file',)),
    ('the policy-block discovery/uniqueness', 'if (nb!=1 || ne!=1)', 'if (0)',
     ('a non-unique policy block',)),
    ('the policy-row decode premise', 'if (nrows<1 || badrow)', 'if (0)',
     ('a malformed policy row',)),
    ('the extraction-coverage premise', 'for (m in mod) if (!(m in heads))', 'for (m in mod) if (0)',
     ('an incomplete extraction',)),
    ('the module-row coverage decision', 'for (m in mod) if (rowseen[m]!=1)', 'for (m in mod) if (0)',
     ('a missing module row',)),
    ('the unknown-module rejection', 'for (rm in rowseen) if (!(rm in mod))', 'for (rm in rowseen) if (0)',
     ('an unknown policy module',)),
    ('the unknown-dependency rejection', 'for (e in unkdep)', 'for (e in unkdep_x)',
     ('an unknown policy dependency',)),
    ('the actual-minus-policy rejection', 'for (e in actual) if (!(e in pedge))', 'for (e in actual) if (0)',
     ('a forbidden actual edge',)),
    ('the policy-minus-actual rejection', 'for (e in pedge) if (!(e in actual))', 'for (e in pedge) if (0)',
     ('a dormant policy edge',)),
)


def extract_layer_block(root: Path):
    text = (root / DOCKERFILE).read_text(encoding='utf-8')
    ib, ie = text.find(LAYER_BEGIN), text.find(LAYER_END)
    if ib < 0 or ie < 0:
        return None
    start = text.rfind('\n', 0, ib) + 1
    end = text.find('\n', ie)
    return text[start:(end + 1 if end >= 0 else len(text))]


def run_layer_mutant(block: str, old: str, new: str):
    n = block.count(old)
    if n != 1:
        return None, f'anchor occurs {n} time(s), expected exactly 1'
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / 'layer.sh'
        p.write_text(block.replace(old, new, 1), encoding='utf-8')
        proc = subprocess.run(['sh', str(p), '--self-test'], capture_output=True, text=True)
        return proc, None


def run_mutant(root: Path, tool: str, old: str, new: str, mode: str = '--self-test'):
    src = (root / tool).read_text(encoding='utf-8')
    n = src.count(old)
    if n != 1:
        return None, f'anchor occurs {n} time(s), expected exactly 1'
    with tempfile.TemporaryDirectory() as d:
        work = Path(d) / 'tree'
        # `.claude` is assistant OUTPUT, not repository input.
        shutil.copytree(root, work, symlinks=True,
                        ignore=shutil.ignore_patterns('.git', '_build', '*.vo', '*.glob', '__pycache__',
                                                      '.claude'))
        (work / tool).write_text(src.replace(old, new, 1), encoding='utf-8')
        proc = subprocess.run([sys.executable, str(work / tool), '--root', str(work), mode],
                              capture_output=True, text=True, cwd=work)
        return proc, None


def main() -> int:
    ap = argparse.ArgumentParser(description='mutation tests for the surviving policy gates')
    ap.add_argument('--root', default='.')

    args = ap.parse_args()
    root = Path(args.root).resolve()

    wanted = '--self-test'
    selected = list(MUTANTS)
    failures = []
    # Every mutant is an independent subprocess against its own private copy of the tree, so they run in
    # parallel. Nothing about the evidence changes: each mutant still deletes exactly one rule and runs the
    # whole self-test against it, and results are collected in the declared order, so the report reads
    # identically however the work was scheduled.
    workers = max(1, min(len(selected), (os.cpu_count() or 1)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        ran = list(pool.map(lambda m: run_mutant(root, m[0], m[2], m[3], wanted), selected))
    for (tool, label, old, new, expected), (proc, err) in zip(selected, ran):
        if err is not None or proc is None:
            failures.append(f'{tool}: {label}: {err}')
            continue
        if proc.returncode == 0:
            failures.append(f'{tool}: {label}: the self-test still PASSED — the rule is not load-bearing, '
                            f'or no control depends on it')
            continue
        # capture to END OF LINE: a control label may itself contain a colon, and stopping at the first one
        # silently truncates the name so the match below can never succeed.
        failed = set(re.findall(r'FAIL  (?:gate (?:flags|accepts): )?(.+)', proc.stdout))
        missing = [c for c in expected if not any(c in f for f in failed)]
        if missing:
            # Name what DID fire. Without it the operator knows only that the wrong thing broke, and has to
            # reproduce the mutation by hand to find out what — which is the slow half of every repair that
            # refactors a rule this harness watches.
            failures.append(f'{tool}: {label}: the self-test failed, but not through the control(s) that '
                            f'depend on this rule: {", ".join(missing)}; what did fail: '
                            f'{", ".join(sorted(failed)[:4]) or "(no control label in the output)"}')
        else:
            print(f'  detected  {label}  ({tool}) — {len(expected)} named control(s) fired')

    # The layer-dependency gate (a POSIX-sh decision block in the Dockerfile), under the same authority.
    layer_selected = list(LAYER_MUTANTS)
    block = extract_layer_block(root)
    if block is None:
        failures.append(f'{DOCKERFILE}: LAYER-GATE-LIB block not found')
    else:
        base = subprocess.run(['sh', '-c', block + '\nlayer_selftest'], capture_output=True, text=True)
        if base.returncode != 0:
            failures.append(f'{DOCKERFILE} layer gate: the unmutated self-test did not pass — '
                            f'{base.stdout.strip() or base.stderr.strip() or "(no output)"}')
        for label, old, new, expected in layer_selected:
            proc, err = run_layer_mutant(block, old, new)
            if err is not None or proc is None:
                failures.append(f'{DOCKERFILE} layer gate: {label}: {err}')
                continue
            if proc.returncode == 0:
                failures.append(f'{DOCKERFILE} layer gate: {label}: the self-test still PASSED — '
                                f'the decision is not load-bearing')
                continue
            failed = set(re.findall(r'FAIL  (.+)', proc.stdout))
            missing = [c for c in expected if not any(c in f for f in failed)]
            if missing:
                failures.append(f'{DOCKERFILE} layer gate: {label}: the self-test failed, but not through the '
                                f'control(s) that depend on this decision: {", ".join(missing)}; what did '
                                f'fail: {", ".join(sorted(failed)) or "(no control label)"}')
            else:
                print(f'  detected  {label}  ({DOCKERFILE} layer gate) — {len(expected)} named control(s) fired')

    checked = len(selected) + len(layer_selected)
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: GATE-MUTATION TEST FAILED — {len(failures)} finding(s) across {checked} checked mutants '
              f'({len(selected)} permanent-policy Python helpers + {len(layer_selected)} layer-gate root decisions)')
        return 1
    print(f'fido: gate-mutation test OK — {checked} checked mutants ({len(selected)} permanent-policy Python '
          f'helpers + {len(layer_selected)} layer-gate root decisions), each proved load-bearing by deleting its '
          f'effect and watching its own named controls fail ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
