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
GRAPH = 'tools/build-graph-gate.py'
WORKSPAN = 'tools/perf-work-span.py'

# (tool, label, anchor, replacement, controls that MUST appear among the failures)
MUTANTS = (
    (WORKSPAN, 'the leaf-partition law, so a parent and its child cannot both be counted as work',
     "                    if a['role'] == 'WORK_LEAF':",
     "                    if False:",
     ('a work leaf nested under another work leaf',)),

    (WORKSPAN, 'the elapsed-consistency law, so a false elapsed value cannot enter the totals',
     "                if abs((en - s) - el) > TOL:",
     "                if False:",
     ('false elapsed value',)),

    (WORKSPAN, 'the unclassified ceiling, so unattributed wall time stays visible',
     "    if wall and uncl / wall > 0.05:",
     "    if False:",
     ('unclassified complete-path above 5% rejected',)),

    (WORKSPAN, 'the leaf-class multiset law, so an event set cannot carry more or fewer required leaves',
     "            if not lo <= counts.get(cls, 0) <= hi:",
     "            if False:",
     ('duplicated proof leaf beyond the topology count',)),

    (WORKSPAN, 'the solve-operation count, so a hidden extra solve is caught',
     "        if solves != spec['solve_ops']:",
     "        if False:",
     ('extra unexpected solve',)),

    (WORKSPAN, 'the predecessor accumulation in the longest path, so it cannot degrade to max-single-leaf',
     "        dist[eid] = best + int(e['elapsed_ms'])",
     "        dist[eid] = int(e['elapsed_ms'])",
     ('final PV critical path is the longest predecessor path',
      'entry serial: work equals critical path')),

    (GRAPH, 'the helper-one-solve law, so a hidden second solve inside the canonical helper is caught',
     "        builds = body.count('docker buildx build')",
     "        builds = 1",
     ('hidden second solve inside the canonical helper',)),

    (GRAPH, 'the one-dune-builder rule, so a second certified build cannot creep back',
     "    if dune_stages != ['theory-built']:",
     "    if False:",
     ('second dune build inserted in emit',)),

    (GRAPH, 'the marker-join rule, so the final artifact cannot stop requiring a branch',
     "    if '--from=prover /workspace/proof-ok' not in join:",
     "    if False:",
     ('proof marker dependency removed from the join',)),

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

    (PERFEV, 'the second-opportunity-projection rejection, so a peer opportunity table cannot come back',
     "    if os.path.exists(peer):",
     "    if False:",
     ('restored second opportunity projection',)),

    (PERFEV, 'the attribution-purity scan, so the raw classifier cannot regain a derived judgment',
     "            if tok in src:",
     "            if False:",
     ('attribution tool regained a derived judgment',)),

    (PERFEV, 'the one-longest-path census, so a second arithmetic implementation is caught',
     "        if n != 1:",
     "        if False:",
     ('a second longest-path implementation',)),

    (PERFEV, 'the one-DAG reduction floor, so an IMPLEMENTED claim cannot stand under 15%',
     "            if v < ONEDAG_MIN_PCT:",
     "            if False:",
     ('one-DAG IMPLEMENTED below its lower-bound reduction',)),

    (PERFEV, 'the gain-deferral rejection, so one gain field cannot point at the other',
     "            if 'see work_gain' in v or 'see span_gain' in v:",
     "            if False:",
     ('gain deferring to the other gain field',)),

    (PERFEV, 'the evidence-form grammar, so a bare number cannot stand as a gain claim',
     "            elif not re.match(r'^(DERIVED:|MEASURED:|QUALITATIVE:|UNKNOWN_NOT_MEASURED:|NOT_APPLICABLE:)', v):",
     "            elif False:",
     ('gain without an explicit evidence form',)),

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

# ---- generated-summary mutations (contract: every hand edit, stale regeneration, deleted row, stronger
# header, raw-input drift or generator drift must fail the byte-compare law). Each transform mutates the
# COMMITTED evidence (or the generator itself) in a private copy and the harness requires
# `perf-work-span.py --check-generated` — the exact mode make perf-evidence and the staged hook run — to
# fail through the named summary. Transforms assert their expected content before writing, so a schema
# change here fails loudly instead of silently testing nothing.
WS_SUM = '.review/perf/verification-dag-work-span.tsv'
REACH_SUM = '.review/perf/verification-dag-reachability.tsv'
EVENTS_RAW = '.review/perf/verification-dag-events.tsv'


def _mut_reduction_999(work: Path):
    p = work / WS_SUM
    text = p.read_text(encoding='utf-8')
    if 'work_reduction_pct' in text:
        out, n = re.subn(r'(work_reduction_pct\t)-?[\d.]+', r'\g<1>99.9', text, count=1)
        if n != 1:
            return 'work_reduction_pct row present but its value did not match'
        text = out
    else:
        text += 'DELTA\tPROJECT_VERIFICATION_work_reduction_pct\t99.9\t\t\t\t\t\n'
    p.write_text(text, encoding='utf-8')


def _mut_saving_99(work: Path):
    p = work / REACH_SUM
    if p.exists():
        text = p.read_text(encoding='utf-8')
        out, n = re.subn(r'(max_complete_path_wall_saving_ms\t)-?[\d.]+', r'\g<1>99', text, count=1)
        if n != 1:
            return 'reachability summary lacks a max_complete_path_wall_saving_ms value'
        p.write_text(out, encoding='utf-8')
    else:
        p.write_text('run\tmetric\tvalue_ms\nfinal-1\tmax_complete_path_wall_saving_ms\t99\n',
                     encoding='utf-8')


def _mut_delete_row(work: Path):
    p = work / WS_SUM
    lines = p.read_text(encoding='utf-8').splitlines(keepends=True)
    data = [i for i, ln in enumerate(lines) if ln.strip() and not ln.startswith(('#', 'run\t'))]
    if not data:
        return 'no data row to delete'
    del lines[data[-1]]
    p.write_text(''.join(lines), encoding='utf-8')


def _mut_stronger_header(work: Path):
    p = work / WS_SUM
    text = p.read_text(encoding='utf-8')
    anchor = 'byte-compared by the gates; a hand edit fails validation.'
    if text.count(anchor) != 1:
        return f'header anchor occurs {text.count(anchor)} time(s), expected exactly 1'
    p.write_text(text.replace(anchor, 'PROVEN OPTIMAL; no further work reduction exists.'),
                 encoding='utf-8')


def _mut_raw_without_regen(work: Path):
    p = work / EVENTS_RAW
    lines = p.read_text(encoding='utf-8').splitlines(keepends=True)
    hits = [i for i, ln in enumerate(lines)
            if not ln.startswith('#') and '\tentry-cold-1\te-go\t' in ln]
    if len(hits) != 1:
        return f'entry-cold-1 e-go row occurs {len(hits)} time(s), expected exactly 1'
    f = lines[hits[0]].rstrip('\n').split('\t')
    f[8], f[9] = str(int(f[8]) - 2000), str(int(f[9]) - 2000)
    lines[hits[0]] = '\t'.join(f) + '\n'
    p.write_text(''.join(lines), encoding='utf-8')


def _mut_generator_drift(work: Path):
    p = work / WORKSPAN
    src = p.read_text(encoding='utf-8')
    anchor = '{t["wall"]/1000:.1f}'
    if src.count(anchor) != 1:
        return f'generator anchor occurs {src.count(anchor)} time(s), expected exactly 1'
    p.write_text(src.replace(anchor, '{t["wall"]/1000:.2f}'), encoding='utf-8')


def _mut_hand_recalculation(work: Path):
    p = work / WS_SUM
    lines = p.read_text(encoding='utf-8').splitlines(keepends=True)
    for i, ln in enumerate(lines):
        f = ln.rstrip('\n').split('\t')
        if len(f) == 8 and f[1] == 'PROJECT_VERIFICATION' and f[3] != f[4]:
            f[3] = f[4]
            lines[i] = '\t'.join(f) + '\n'
            p.write_text(''.join(lines), encoding='utf-8')
            return
    return 'no PROJECT_VERIFICATION row where aggregate work differs from the critical path'


EVIDENCE_MUTANTS = (
    ('a hand-set 99.9 work reduction in the committed summary', _mut_reduction_999,
     'verification-dag-work-span.tsv'),
    ('a hand-set 99 maximum complete-path saving', _mut_saving_99,
     'verification-dag-reachability.tsv'),
    ('a deleted generated row', _mut_delete_row, 'verification-dag-work-span.tsv'),
    ('a generated header edited to a stronger claim', _mut_stronger_header,
     'verification-dag-work-span.tsv'),
    ('raw events modified without regenerating the summary', _mut_raw_without_regen,
     'verification-dag-work-span.tsv'),
    ('a modified generator kept with stale committed output', _mut_generator_drift,
     'verification-dag-work-span.tsv'),
    ('committed output replaced by a second hand calculation', _mut_hand_recalculation,
     'verification-dag-work-span.tsv'),
)


def run_evidence_mutant(root: Path, transform):
    with tempfile.TemporaryDirectory() as d:
        work = Path(d) / 'tree'
        shutil.copytree(root, work, symlinks=True,
                        ignore=shutil.ignore_patterns('.git', '_build', '*.vo', '*.glob', '__pycache__',
                                                      '.claude'))
        err = transform(work)
        if err is not None:
            return None, err
        proc = subprocess.run([sys.executable, str(work / WORKSPAN), '--root', str(work),
                               '--check-generated'], capture_output=True, text=True, cwd=work)
        return proc, None


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

    # Generated-summary mutations: each mutated committed summary / raw input / generator copy must fail
    # the --check-generated law through its named summary file (the mode make perf-evidence and the
    # staged hook both run, so the same detection holds in the ordinary and staged gates).
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        eran = list(pool.map(lambda m: run_evidence_mutant(root, m[1]), EVIDENCE_MUTANTS))
    for (label, _fn, expected_file), (proc, err) in zip(EVIDENCE_MUTANTS, eran):
        if err is not None or proc is None:
            failures.append(f'evidence mutation: {label}: {err}')
            continue
        blob = proc.stdout + proc.stderr
        if proc.returncode == 0:
            failures.append(f'evidence mutation: {label}: --check-generated still PASSED — the '
                            f'byte-compare law did not detect it')
        elif f'generated-summary law: {expected_file}' not in blob:
            failures.append(f'evidence mutation: {label}: failed, but not through the generated-summary '
                            f'law on {expected_file}; output: {blob.strip().splitlines()[:3]}')
        else:
            print(f'  detected  {label}  (generated-summary byte-compare)')

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

    checked = len(selected) + len(layer_selected) + len(EVIDENCE_MUTANTS)
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: GATE-MUTATION TEST FAILED — {len(failures)} finding(s) across {checked} checked mutants '
              f'({len(selected)} permanent-policy Python helpers + {len(layer_selected)} layer-gate root '
              f'decisions + {len(EVIDENCE_MUTANTS)} generated-summary mutations)')
        return 1
    print(f'fido: gate-mutation test OK — {checked} checked mutants ({len(selected)} permanent-policy Python '
          f'helpers + {len(layer_selected)} layer-gate root decisions + {len(EVIDENCE_MUTANTS)} '
          f'generated-summary mutations), each proved load-bearing by deleting its effect and watching its '
          f'own named controls fail ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
