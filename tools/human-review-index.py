#!/usr/bin/env python3
"""Governance D-07 — open human acts are GENERATED from canonical rows, never hand-copied.

One data authority: `.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv`.
One generated view:  `.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md`.

There is one implementation.  `--write` regenerates the view; `--check` compares exact bytes and never
writes.  Both share every validation, so a checker cannot drift from the writer.

Everything fails closed.  A read error, decode error, malformed row, duplicate id, unknown status, missing or
duplicated ownership anchor, unresolvable path, path traversal, symlink, or any byte of difference between the
tracked view and the regenerated one is an error naming the exact input and reason.  Nothing is skipped and
nothing is inferred from prose or Git history.

The list of open acts lives ONLY in the TSV.  This tool must never contain one.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

TSV_REL   = '.review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv'
INDEX_REL = '.review/fcb/current/FIDO_FCB_HUMAN_REVIEW_INDEX.md'
FIELDS    = ('id', 'status', 'required_human_act', 'source_path', 'source_anchor', 'source_owner', 'effect')

# Closed vocabulary, declared once.  A status outside it is a data error, not a new state.
STATUSES = ('BLOCKED', 'PENDING', 'OPEN', 'DEFERRED')

BANNER = """# Fido FCB Human Review Index

<!-- GENERATED FILE — do not edit by hand.
     Data authority: .review/fcb/current/FIDO_FCB_HUMAN_ACTS.tsv
     Generator:      tools/human-review-index.py  (make human-acts-write; verified by make human-acts)
     Governance D-07: open human acts are generated from canonical rows, never hand-copied. -->

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  \n\
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  \n\
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`;
> `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`.  \n\
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  \n\
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  \n\
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.

This index is the generated view of the current open human acts. Each row is owned by one source file
carrying exactly one `FIDO-HUMAN-ACT` anchor, which the generator validates. A closed act is removed from the
data authority; Git history and the owning ADR, governance row, fixed-point record or accepted review commit
preserve its disposition.

| ID | Status | Required human act | Source / owner | Effect |
|---|---|---|---|---|
"""


class DataError(Exception):
    """Any failure to read, parse, validate, or match. Always carries the exact input and reason."""


def read_text(path: Path, label: str) -> str:
    try:
        return path.read_text(encoding='utf-8')
    except FileNotFoundError:
        raise DataError(f'{label}: {path} does not exist')
    except UnicodeDecodeError as exc:
        raise DataError(f'{label}: {path} is not valid UTF-8 ({exc})')
    except OSError as exc:
        raise DataError(f'{label}: {path} could not be read ({exc.__class__.__name__}: {exc})')


def load_rows(root: Path):
    tsv = root / TSV_REL
    text = read_text(tsv, 'human-acts data authority')
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    if not lines:
        raise DataError(f'{TSV_REL}: empty; refusing to generate an index from nothing')
    header = lines[0].split('\t')
    if tuple(header) != FIELDS:
        raise DataError(f'{TSV_REL}: header must be exactly {chr(9).join(FIELDS)!r}, found {chr(9).join(header)!r}')
    rows, seen = [], set()
    for n, line in enumerate(lines[1:], start=2):
        cells = line.split('\t')
        if len(cells) != len(FIELDS):
            raise DataError(f'{TSV_REL}:{n}: expected {len(FIELDS)} fields, found {len(cells)}')
        row = dict(zip(FIELDS, cells))
        for k, v in row.items():
            if not v.strip():
                raise DataError(f'{TSV_REL}:{n}: field {k!r} is blank')
            if '\r' in v:
                raise DataError(f'{TSV_REL}:{n}: field {k!r} contains a carriage return')
        if row['id'] in seen:
            raise DataError(f'{TSV_REL}:{n}: duplicate id {row["id"]!r}')
        seen.add(row['id'])
        if row['status'] not in STATUSES:
            raise DataError(f'{TSV_REL}:{n}: status {row["status"]!r} is not one of {", ".join(STATUSES)}')
        rows.append(row)
    if not rows:
        raise DataError(f'{TSV_REL}: no rows; an empty act list must be stated deliberately, not implied')
    ordered = sorted(rows, key=lambda r: r['id'])
    if [r['id'] for r in rows] != [r['id'] for r in ordered]:
        raise DataError(f'{TSV_REL}: rows are not in canonical id order; expected '
                        + ', '.join(r['id'] for r in ordered))
    return rows


def validate_anchor(root: Path, row: dict):
    """Ownership is proved by exactly one anchor in exactly one owning file."""
    rel = row['source_path']
    if rel.startswith('/') or '..' in Path(rel).parts:
        raise DataError(f'{TSV_REL}: {row["id"]}: source_path {rel!r} escapes the repository root')
    target = root / rel
    if target.is_symlink():
        raise DataError(f'{TSV_REL}: {row["id"]}: source_path {rel!r} is a symlink')
    if not target.is_file():
        raise DataError(f'{TSV_REL}: {row["id"]}: source_path {rel!r} is not a regular file in this tree')
    text = read_text(target, f'{row["id"]} owning source')
    anchor = f'<!-- {row["source_anchor"]} -->'
    count = text.count(anchor)
    if count == 0:
        raise DataError(f'{rel}: missing ownership anchor {anchor!r} for {row["id"]}')
    if count > 1:
        raise DataError(f'{rel}: ownership anchor {anchor!r} for {row["id"]} occurs {count} times, expected once')


def render(rows) -> str:
    def cell(s: str) -> str:
        return s.replace('|', '\\|')
    body = ''.join(
        f'| `{cell(r["id"])}` | **{cell(r["status"])}** | {cell(r["required_human_act"])} '
        f'| {cell(r["source_owner"])} | {cell(r["effect"])} |\n'
        for r in rows)
    return BANNER + body


def run(root: Path, write: bool) -> str:
    rows = load_rows(root)
    for row in rows:
        validate_anchor(root, row)
    generated = render(rows)
    index = root / INDEX_REL
    if write:
        index.write_text(generated, encoding='utf-8')
        return f'wrote {INDEX_REL} from {len(rows)} canonical row(s)'
    current = read_text(index, 'generated human review index')
    if current != generated:
        cur, gen = current.split('\n'), generated.split('\n')
        for i in range(max(len(cur), len(gen))):
            a = cur[i] if i < len(cur) else '<missing line>'
            b = gen[i] if i < len(gen) else '<extra line>'
            if a != b:
                raise DataError(
                    f'{INDEX_REL} is not the generated view of {TSV_REL} — first difference at line {i + 1}\n'
                    f'    tracked:   {a[:160]}\n    generated: {b[:160]}')
        raise DataError(f'{INDEX_REL} differs from the generated view')
    return f'{INDEX_REL} matches {len(rows)} canonical row(s)'


# ───────────────────────────────────────────────────────────── adversarial controls
def self_test(root: Path) -> int:
    import shutil, tempfile
    failures = []
    counts = {'total': 0, 'must_fail': 0}

    def scenario(label: str, mutate, expect=None):
        """`expect` is the substring the failure reason MUST contain; None means the control must PASS.

        Pinning the reason is the point. A must-fail control that fails for an unrelated reason is a
        vacuous pass — it proves the tool broke, not that it caught the defect.
        """
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with tempfile.TemporaryDirectory() as d:
            work = Path(d) / 'tree'
            shutil.copytree(root, work, symlinks=True,
                            ignore=shutil.ignore_patterns('.git', '_build', '*.vo', '*.glob'))
            try:
                mutate(work)
            except Exception as exc:                       # a control that cannot be set up is a failure
                failures.append(f'{label}: could not construct the scenario ({exc})'); return
            try:
                run(work, write=False)
                if expect is not None:
                    failures.append(f'{label}: expected failure containing {expect!r}, but the gate passed')
            except DataError as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — '
                                    f'wanted {expect!r}, got: {exc}')

    def tsv(work: Path) -> Path:
        return work / TSV_REL

    def edit(work: Path, fn):
        p = tsv(work); lines = p.read_text(encoding='utf-8').split('\n')
        p.write_text(fn(lines), encoding='utf-8')

    scenario('canonical fixture passes', lambda _w: None)
    # the two core false-green classes: the view must track the rows in BOTH directions
    scenario('a live row omitted from the generated view',
             lambda w: edit(w, lambda L: '\n'.join(L[:1] + L[2:])),
             expect='is not the generated view')
    scenario('a removed row retained in the generated view',
             lambda w: edit(w, lambda L: '\n'.join(L[:2] + L[3:])),
             expect='is not the generated view')
    scenario('duplicate id',
             lambda w: edit(w, lambda L: '\n'.join(L[:2] + [L[1]] + L[2:])),
             expect='duplicate id')
    scenario('malformed field count',
             lambda w: edit(w, lambda L: '\n'.join([L[0], L[1].rsplit('\t', 1)[0]] + L[2:])),
             expect='expected 7 fields, found 6')
    scenario('invalid status',
             lambda w: edit(w, lambda L: '\n'.join([L[0], '\t'.join(
                 [c if i != 1 else 'MAYBE' for i, c in enumerate(L[1].split('\t'))])] + L[2:])),
             expect="status 'MAYBE' is not one of")
    scenario('blank required act',
             lambda w: edit(w, lambda L: '\n'.join([L[0], '\t'.join(
                 [c if i != 2 else '' for i, c in enumerate(L[1].split('\t'))])] + L[2:])),
             expect="field 'required_human_act' is blank")
    scenario('missing source file',
             lambda w: (w / L1_path(w)).unlink(),
             expect='is not a regular file in this tree')
    scenario('path traversal in source_path',
             lambda w: edit(w, lambda L: '\n'.join([L[0], '\t'.join(
                 [c if i != 3 else '../outside.md' for i, c in enumerate(L[1].split('\t'))])] + L[2:])),
             expect='escapes the repository root')
    scenario('symlink source path',
             lambda w: symlink_source(w),
             expect='is a symlink')
    scenario('non-regular source path',
             lambda w: replace_source_with_dir(w),
             expect='is not a regular file in this tree')
    scenario('missing anchor',
             lambda w: strip_anchor(w),
             expect='missing ownership anchor')
    scenario('duplicate anchor',
             lambda w: duplicate_anchor(w),
             expect='occurs 2 times, expected once')
    scenario('invalid UTF-8 in the TSV',
             lambda w: tsv(w).write_bytes(tsv(w).read_bytes() + b'\xff'),
             expect='is not valid UTF-8')
    scenario('invalid UTF-8 in a selected source file',
             lambda w: (w / L1_path(w)).write_bytes(b'# doc\n\xff'),
             expect='is not valid UTF-8')
    scenario('rows out of canonical order',
             lambda w: edit(w, lambda L: '\n'.join([L[0], L[2], L[1]] + L[3:])),
             expect='not in canonical id order')
    scenario('stale extra prose in the generated view',
             lambda w: (w / INDEX_REL).write_text(
                 (w / INDEX_REL).read_text(encoding='utf-8') + '\nstale trailing prose\n', encoding='utf-8'),
             expect='is not the generated view')

    total, must_fail = counts['total'], counts['must_fail']
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: HUMAN-ACTS SELF-TEST FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: human-acts self-test OK — {total} controls '
          f'({must_fail} must-fail with the reason pinned, {total - must_fail} must-accept) ✓')
    return 0


def L1_path(work: Path) -> str:
    """The owning source of the first data row, used by several controls."""
    lines = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    return lines[1].split('\t')[3]


def symlink_source(work: Path):
    rel = L1_path(work); p = work / rel
    body = p.read_bytes(); p.unlink()
    other = p.with_suffix('.real.md'); other.write_bytes(body)
    p.symlink_to(other.name)


def replace_source_with_dir(work: Path):
    rel = L1_path(work); p = work / rel
    p.unlink(); p.mkdir()


def strip_anchor(work: Path):
    lines = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    rel, anchor = lines[1].split('\t')[3], lines[1].split('\t')[4]
    p = work / rel
    p.write_text(p.read_text(encoding='utf-8').replace(f'<!-- {anchor} -->', ''), encoding='utf-8')


def duplicate_anchor(work: Path):
    lines = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    rel, anchor = lines[1].split('\t')[3], lines[1].split('\t')[4]
    p = work / rel
    p.write_text(p.read_text(encoding='utf-8') + f'\n<!-- {anchor} -->\n', encoding='utf-8')


def main() -> int:
    ap = argparse.ArgumentParser(description='D-07 human-acts index generator and checker')
    ap.add_argument('--root', default='.', help='repository or exported-tree root')
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true', help='regenerate the tracked index')
    mode.add_argument('--check', action='store_true', help='verify exact generated bytes; never writes')
    mode.add_argument('--self-test', action='store_true', help='run the adversarial controls')
    args = ap.parse_args()
    if args.self_test:
        return self_test(Path(args.root).resolve())
    try:
        msg = run(Path(args.root).resolve(), write=args.write)
    except DataError as exc:
        print(f'fido: HUMAN-ACTS GATE FAILED — {exc}', file=sys.stderr)
        return 1
    print(f'fido: human-acts index OK — {msg} ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
