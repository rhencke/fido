#!/usr/bin/env python3
"""Mutation tests for the document gates: prove every root helper is load-bearing.

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
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

FCB = 'tools/fcb-reference-gate.py'
ACTS = 'tools/human-review-index.py'
NAMES = 'tools/naming-gate.py'
DIET = 'tools/source-diet.py'

# (tool, label, anchor, replacement, controls that MUST appear among the failures)
MUTANTS = (
    (FCB, 'repository inventory derivation',
     "    if not files:\n        raise ReferenceError_(",
     "    files = {'CLAUDE.md'}  # neutered: a fixed list, not the exact snapshot\n"
     "    if not files:\n        raise ReferenceError_(",
     ('authority names an existing but unmanifested root .v file',
      'authority names an existing but unmanifested dotfile')),

    (FCB, 'canonical path parsing',
     "    for seg in text.split('/'):\n        if seg == '':",
     "    for seg in []:\n        if seg == '':",
     ('a manifest target with a doubled separator', 'a manifest target with a "." segment',
      'manifest owner escapes the repository by traversal')),

    (FCB, 'owner and target root containment',
     "        if here.is_symlink():",
     "        if False:",
     ('manifest owner reached through a symlink', 'a symlinked declared target')),

    (FCB, 'external / repository separation',
     "    if not text.startswith(EXTERNAL_PREFIX):",
     "    if False:",
     ('a missing repository path typed as external evidence',)),

    (FCB, 'live-set entry-kind checking',
     "        if entry.is_symlink():",
     "        if False:",
     ('the live FCB set contains a symlinked directory', 'the live FCB set contains a symlinked file')),

    (FCB, 'live-set declaration closure',
     "    missing = [p for p in present if p not in declared]",
     "    missing = []",
     ('the live FCB set contains an undeclared regular file',)),

    (FCB, 'exact marker token binding',
     "        if before not in TOKEN_CHARS and after not in TOKEN_CHARS:\n            return True",
     "        return True",
     ('an owner marker bound to dune-project instead of dune',)),

    (FCB, 'duplicate target identity',
     "        if len(owners) > 1:",
     "        if False:",
     ('two rows resolving to the same target',)),

    (FCB, 'duplicate Index table rows',
     "        if path in declared:",
     "        if False:",
     ('the FCB Index repeats one live-set path with the same role',
      'the FCB Index repeats one live-set path with a different role')),

    (FCB, 'structural declarations must name an authority',
     "        if row['corpus_role'] != 'authority':",
     "        if False:",
     ('the ACTIVE REPAIR row marked reference', 'the FUNCTIONAL CONTRACT row marked reference')),

    (ACTS, 'the candidate-state rule',
     "        check_no_mutable_candidate_state(row, n)\n",
     "\n",
     ('a candidate SHA copied into an act', 'a short candidate SHA copied into an act')),

    (ACTS, 'the boundary protecting content digests',
     r"GIT_OBJECT_ID = re.compile(r'(?<![0-9a-fA-F])[0-9a-f]{7,40}(?![0-9a-fA-F])')",
     r"GIT_OBJECT_ID = re.compile(r'[0-9a-f]{7,40}')",
     ('a SHA-256 content digest stays accepted',)),

    (NAMES, 'statement-level local-notation parsing',
     "    for line, name in local_notations(code):",
     "    for line, name in [(i, m.group(1)) for i, l in enumerate(code.splitlines(), 1)\n"
     "                       for m in [re.match(r\"\\s*Local\\s+Notation\\s+([A-Za-z_][A-Za-z0-9_']*)\\s*:=\","
     " l)] if m]:",
     ('multiline: break before the name', 'multiline: break after Local',
      'snapshot mode, mutated tracked module')),

    (NAMES, 'general identifier extraction before judgement',
     r"""    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*:=")""",
     r"""    r"(?P<name>Hidden[A-Za-z0-9_']*)\s*:=")""",
     ('local alias Resolve', 'indented local alias')),

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

    (DIET, 'the baseline seal',
     "    if actual != by['baseline_sha256']:",
     "    if False:",
     ('a baseline metric changed after capture',)),

    (DIET, 'file-disposition coverage',
     "    missing = sorted(present - seen)",
     "    missing = []",
     ('a current file absent from the file-disposition ledger',)),

    (DIET, 'refusing a diet over nothing',
     "    if not blocks_by_file:",
     "    if False:",
     ('a snapshot containing no .v files',)),

    (DIET, 'the required-direction comparison',
     "        if float(now[k]) >= float(base[k]):",
     "        if False:",
     ('a required metric that increased from baseline',)),

    (DIET, 'the required-zero counts',
     "        if float(now[k]) != 0:",
     "        if False:",
     ('a required count that is not zero',)),

    (DIET, 'surviving-declaration command equality',
     "        if expect == actual:\n            continue",
     "        if True:\n            continue",
     ('one tactic removed from a surviving proof',
      'one type annotation removed from a surviving definition',
      'a declaration partially removed')),

    (DIET, 'the new and removed .v file rules',
     "    added = sorted(cand_v - base_v)",
     "    added = []",
     ('a new .v file since the baseline',)),

    (DIET, 'the ledger declaration-kind match',
     "        if hits[0][0] != r['kind']:",
     "        if False:",
     ('a ledger row naming the wrong kind',)),

    (DIET, 'the ledger reason set',
     "        if r['reason'] not in DELETION_REASONS:",
     "        if False:",
     ('a ledger row with an unknown reason',)),

    (DIET, 'the still-declared check',
     "        if still:",
     "        if False:",
     ('a ledger row for a declaration still present',)),

    (DIET, 'the ledger placeholder rule',
     "            if cell.lower() in PLACEHOLDER_CELLS:",
     "            if False:",
     ('a ledger row whose consumer search is a placeholder',)),

    (DIET, 'the strictly-superseded replacement rule',
     "            if not everywhere:",
     "            if False:",
     ('a superseded row naming a replacement nothing declares',)),

    (DIET, 'the disposition byte comparison',
     "            if b != wb or c != wc:",
     "            if False:",
     ('a false baseline byte count', 'a false candidate byte count',
      'a candidate byte count bumped after the ledger was written')),

    (DIET, 'the disposition membership relation',
     "    missing, phantom = sorted(union - seen), sorted(seen - union)",
     "    missing, phantom = [], []",
     ('an omitted baseline file row', 'a phantom deleted file')),

    (DIET, 'the disposition action relation',
     "        if not want:",
     "        if False:",
     ('keep used for a baseline-only file', 'm1-created used for a baseline file')),

    (DIET, 'metric equality with recomputation',
     "        if got != w:",
     "        if False:",
     ('a tampered metrics candidate value', 'a tampered delta', 'a tampered percentage')),

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

    (DIET, 'decorative-glyph rejection',
     "            hit = DECORATIVE_GLYPH.search(body)",
     "            hit = None",
     ('a two-character box-drawing banner', 'a star decoration')),
)


def run_mutant(root: Path, tool: str, old: str, new: str):
    src = (root / tool).read_text(encoding='utf-8')
    n = src.count(old)
    if n != 1:
        return None, f'anchor occurs {n} time(s), expected exactly 1'
    with tempfile.TemporaryDirectory() as d:
        work = Path(d) / 'tree'
        shutil.copytree(root, work, symlinks=True,
                        ignore=shutil.ignore_patterns('.git', '_build', '*.vo', '*.glob', '__pycache__'))
        (work / tool).write_text(src.replace(old, new, 1), encoding='utf-8')
        proc = subprocess.run([sys.executable, str(work / tool), '--root', str(work), '--self-test'],
                              capture_output=True, text=True, cwd=work)
        return proc, None


def main() -> int:
    ap = argparse.ArgumentParser(description='mutation tests for the document gates')
    ap.add_argument('--root', default='.')
    args = ap.parse_args()
    root = Path(args.root).resolve()

    failures = []
    for tool, label, old, new, expected in MUTANTS:
        proc, err = run_mutant(root, tool, old, new)
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
            failures.append(f'{tool}: {label}: the self-test failed, but not through the control(s) that '
                            f'depend on this rule: {", ".join(missing)}')
        else:
            print(f'  detected  {label}  ({tool}) — {len(expected)} named control(s) fired')

    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: GATE-MUTATION TEST FAILED — {len(failures)} of {len(MUTANTS)} mutants wrong')
        return 1
    print(f'fido: gate-mutation test OK — {len(MUTANTS)} root helpers, each proved load-bearing by deleting '
          f'its effect and watching its own named controls fail ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
