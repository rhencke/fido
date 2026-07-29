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
OBS = 'tools/build-observatory.py'

# (tool, label, anchor, replacement, controls that MUST appear among the failures)
MUTANTS = (
    (OBS, 'live command-surface discovery',
     "    if not names:\n"
     "        raise ObservatoryError(f'{MAKEFILE_REL}: the .PHONY declaration is empty')",
     "    names = {'diet', 'observatory', 'observe'}  # neutered: fixed, not the live .PHONY closure\n"
     "    if not names:\n"
     "        raise ObservatoryError(f'{MAKEFILE_REL}: the .PHONY declaration is empty')",
     ('the canonical registry classifies the whole live surface',)),

    (OBS, 'the surface-to-registry direction',
     "        for missing in sorted(live[kind] - declared[kind]):",
     "        for missing in []:",
     ('a public Make target absent from the registry', 'a Docker stage absent from the registry')),

    (OBS, 'the registry-to-surface direction',
     "        for stale in sorted(declared[kind] - live[kind]):",
     "        for stale in []:",
     ('a stale registry Make target', 'a stale registry Docker stage')),

    (OBS, 'the anchor-to-registry direction',
     "    for missing in sorted(anchors - hook_declared):",
     "    for missing in []:",
     ('a pre-commit anchor absent from the registry',)),

    (OBS, 'the registry-to-anchor direction',
     "    for stale in sorted(hook_declared - anchors):",
     "    for stale in []:",
     ('a registry pre-commit stage with no anchor pair',)),

    (OBS, 'the selection dependency closure',
     "        for dep in commands[cid]['dependencies']:",
     "        for dep in []:",
     ('a derived child is measured through the live parent',
      'a docker stage names its live parent build')),

    (OBS, 'cache provenance',
     "    needs_prime = any(v == 'reused' for v in declared.values())",
     "    needs_prime = False",
     ('an unknown cache accepted as primed', 'a cached run with no priming run recorded',
      'a cache primed on another builder', 'a cache primed under a different BuildKit')),

    (OBS, 'comparison compatibility',
     "        if not same_host:",
     "        if False:",
     ('an incomparable host class must not be reported as an ordinary percentage delta',)),

    (OBS, 'the overlapping-range refusal',
     "        elif not single and overlap:",
     "        elif False:",
     ('overlapping sample ranges refuse a verdict',)),

    (OBS, 'the resource-scope compatibility check',
     "        if b_scope != c_scope:",
     "        if False:",
     ('a changed resource scope must be incomparable, not a delta',)),

    (OBS, 'record eligibility',
     "    if sel.partial:",
     "    if False:",
     ('a partial run with RECORD',)),

    (OBS, 'the summary recomputation',
     "    if stored != recomputed:",
     "    if False:",
     ('a tampered stored summary',)),

    (OBS, 'the recording blast radius',
     "    unexpected = [p for p in dirty if p != OBSERVATION_REL]",
     "    unexpected = []",
     ('recording which changes a second tracked file',)),

    (OBS, 'the builder guard',
     "    if name != OBSERVATORY_BUILDER:",
     "    if False:",
     ("the developer's builder is never modified",)),

    (OBS, 'edit restoration',
     "    if after != before_digest:",
     "    if False:",
     ('an incremental edit that is not restored',)),

    (OBS, 'the anchor pairing relation',
     "            if anchor in seen:",
     "            if False:",
     ('a duplicate anchor pair in the hook',)),

    (OBS, 'anchor nesting',
     "            if stack[-1] != anchor:",
     "            if False:",
     ('interleaved anchor pairs',)),

    (OBS, 'the owner-token resolution',
     "        elif token not in read_text(target, f'{c[\"id\"]} owner'):",
     "        elif False:",
     ('an owner token that does not occur in its file',)),

    (FCB, 'repository inventory derivation',
     "    if not files:\n        raise ReferenceError_(",
     "    files = {'CLAUDE.md'}  # neutered: a fixed list, not the exact snapshot\n"
     "    if not files:\n        raise ReferenceError_(",
     ('authority names an existing but unmanifested root .v file',
      'authority names an existing but unmanifested dotfile')),

    (FCB, 'the residue exemption in the token scan',
     "        if _residue(t):\n            continue",
     "        if False:\n            continue",
     ('an authority naming an ignored residue namespace',)),

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

    (DIET, 'the permanent wiring scan',
     "        found += [f'{rel} invokes {mode}' for mode in M1_ONLY_MODES if mode in text]",
     "        found += []",
     ('a diet target that regained the code-identity check',
      'a staged hook that regained the disposition check')),

    (DIET, 'the diet recipe boundary',
     "        if seen and line and not line[0].isspace():\n            break",
     "        if seen and line and not line[0].isspace():\n            pass",
     ('a later Make target that runs the M1 verifier, which the diet recipe must not absorb',)),

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

    (DIET, 'the candidate-owned immutability rule',
     "        elif a.is_file() and a.read_bytes() != b.read_bytes():",
     "        elif False:",
     ('the freeze changing one candidate disposition byte',
      'candidate_bytes rewritten to the freeze size',
      'the freeze changing one declaration-deletion row',
      'the freeze changing one baseline row',
      'the post-freeze gate rejects a freeze edit to candidate evidence')),

    (DIET, 'the freeze overlay closure',
     "        if same or rel in FREEZE_OVERLAY:",
     "        if True:",
     ('a freeze-only change outside the closed overlay',)),

    (DIET, 'the pending-metrics rule',
     "    if len(lines) > 1:",
     "    if False:",
     ("a candidate carrying another candidate's completed metric table",)),

    (DIET, 'the candidate ref the review state names',
     "    return m.group(1) if m else None",
     "    return None",
     ('the disposition gate runs in post-freeze mode once a candidate is named',
      'the post-freeze gate rejects a freeze edit to candidate evidence')),

    (DIET, 'declaration ownership of the following commands',
     "        if opens_proof(nxt):",
     "        if True:",
     ('a deleted declaration beside a Hint \u2014 the declaration alone',
      'a deleted declaration beside an Opaque \u2014 the declaration alone',
      'a deleted declaration beside an End \u2014 the declaration alone')),

    (DIET, 'the proof-opener test',
     "    return cmd is not None and (cmd == 'Proof.' or cmd.startswith('Proof '))",
     "    return False",
     ('a terminator carrying a closing brace',
      'a proof-bearing definition removed with its own proof')),

    (DIET, 'the terminator test',
     "    return bool(parts) and parts[-1] in PROOF_TERMINATORS",
     "    return False",
     ('a terminator carrying a closing brace',
      'a statement carrying := that still opens a proof')),

    (DIET, 'the undecidable-shape refusal',
     "        if ':=' in cmds[i] or kind in SELF_CONTAINED_KINDS:",
     "        if True:",
     ('a declaration with neither a body nor a proof',)),

    (DIET, 'the self-contained kind set',
     "                                  'axiom', 'parameter', 'ltac'})",
     "                                  })",
     ('an assumption with no body and no proof',)),

    (DIET, 'the refusal to run a proof into the next declaration',
     "                other = command_declaration(cmds[j])",
     "                other = None",
     ('a proof that runs into the next declaration',)),

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


# The source-diet mutants below split by LIFETIME, not by subject.  A mutant listed here protects one
# checkpoint's exit evidence, so it exercises `--m1-self-test` and runs only in the explicit M1 review run.
# Everything else protects the permanent source-comment policy and runs in the ordinary gate.  A new M1
# mutant that is not listed fails loudly in the permanent run rather than silently weakening it.
M1_ONLY_MUTANTS = frozenset({
    'the baseline seal',
    'file-disposition coverage',
    'the required-direction comparison',
    'the required-zero counts',
    'surviving-declaration command equality',
    'the new and removed .v file rules',
    'the ledger declaration-kind match',
    'the ledger reason set',
    'the still-declared check',
    'the ledger placeholder rule',
    'the strictly-superseded replacement rule',
    'the disposition byte comparison',
    'the disposition membership relation',
    'the disposition action relation',
    'metric equality with recomputation',
    'declaration ownership of the following commands',
    'the proof-opener test',
    'the terminator test',
    'the undecidable-shape refusal',
    'the self-contained kind set',
    'the refusal to run a proof into the next declaration',
    'the candidate-owned immutability rule',
    'the freeze overlay closure',
    'the pending-metrics rule',
    'the candidate ref the review state names',
})


def mutant_mode(label: str) -> str:
    """Which self-test a mutant must break: the permanent policy one, or the M1 evidence one."""
    return '--m1-self-test' if label in M1_ONLY_MUTANTS else '--self-test'


def run_mutant(root: Path, tool: str, old: str, new: str, mode: str = '--self-test'):
    src = (root / tool).read_text(encoding='utf-8')
    n = src.count(old)
    if n != 1:
        return None, f'anchor occurs {n} time(s), expected exactly 1'
    with tempfile.TemporaryDirectory() as d:
        work = Path(d) / 'tree'
        shutil.copytree(root, work, symlinks=True,
                        ignore=shutil.ignore_patterns('.git', '_build', '*.vo', '*.glob', '__pycache__'))
        (work / tool).write_text(src.replace(old, new, 1), encoding='utf-8')
        proc = subprocess.run([sys.executable, str(work / tool), '--root', str(work), mode],
                              capture_output=True, text=True, cwd=work)
        return proc, None


def main() -> int:
    ap = argparse.ArgumentParser(description='mutation tests for the document gates')
    ap.add_argument('--root', default='.')
    ap.add_argument('--m1', action='store_true',
                    help='run the M1 exit-evidence mutants instead of the permanent policy mutants')
    args = ap.parse_args()
    root = Path(args.root).resolve()

    wanted = '--m1-self-test' if args.m1 else '--self-test'
    selected = [m for m in MUTANTS if mutant_mode(m[1]) == wanted]
    failures = []
    for tool, label, old, new, expected in selected:
        proc, err = run_mutant(root, tool, old, new, wanted)
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
        print(f'fido: GATE-MUTATION TEST FAILED — {len(failures)} of {len(selected)} mutants wrong')
        return 1
    group = 'M1 exit-evidence' if args.m1 else 'permanent-policy'
    print(f'fido: gate-mutation test OK — {len(selected)} {group} root helpers, each proved load-bearing by '
          f'deleting '
          f'its effect and watching its own named controls fail ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
