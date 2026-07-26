#!/usr/bin/env python3
"""Governance D-24 — every operational path the live FCB names must resolve at the SAME exact Git ref,
unless it is explicitly TYPED as external evidence or ephemeral with a stated availability.

One data authority: `.review/fcb/current/FIDO_FCB_REFERENCES.tsv` — id, kind, path, availability, owner.

Why a manifest and not a scanner: the corpus is full of backticked strings that merely LOOK like paths
(`.go`, `linux/amd64`, `gc.go`, `/=`). A scanner over them needs an ad-hoc exception list, and an exception
list is where a genuinely dangling path hides. So the FCB declares its operational references explicitly and
this gate checks THOSE. One root object owns the list; there is no second, untyped path authority.

Everything fails closed. A missing file, a renamed target, a directory where a file was declared (or the
reverse), a symlink, a path escaping the tree, an unknown kind or availability, a duplicate id, a malformed
row, an owner that is not itself a readable file, a repository path dressed up as external evidence, a
read/decode error — each is an error naming the exact row and reason.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

TSV_REL = '.review/fcb/current/FIDO_FCB_REFERENCES.tsv'
FIELDS = ('id', 'kind', 'path', 'availability', 'owner')

# Closed vocabularies, declared once.
REPO_KINDS = ('repository-file', 'repository-directory')
OFF_TREE_KINDS = ('external-evidence', 'ephemeral')
KINDS = REPO_KINDS + OFF_TREE_KINDS
# A repository kind must be `present` — it is IN the ref by definition. Off-tree kinds must NOT claim it.
REPO_AVAILABILITY = ('present',)
OFF_TREE_AVAILABILITY = ('not-in-repository', 'r1-bundle-provenance-pending')


class ReferenceError_(Exception):
    """Any failure to read, parse, validate, or resolve. Always names the exact row and reason."""


def read_text(path: Path, label: str) -> str:
    try:
        return path.read_text(encoding='utf-8')
    except FileNotFoundError:
        raise ReferenceError_(f'{label}: {path} does not exist')
    except UnicodeDecodeError as exc:
        raise ReferenceError_(f'{label}: {path} is not valid UTF-8 ({exc})')
    except OSError as exc:
        raise ReferenceError_(f'{label}: {path} could not be read ({exc.__class__.__name__}: {exc})')


def load_rows(root: Path):
    text = read_text(root / TSV_REL, 'FCB reference manifest')
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    if not lines:
        raise ReferenceError_(f'{TSV_REL}: empty; refusing to pass a corpus with no declared references')
    if tuple(lines[0].split('\t')) != FIELDS:
        raise ReferenceError_(f'{TSV_REL}: header must be exactly {chr(9).join(FIELDS)!r}')
    rows, seen = [], set()
    for n, line in enumerate(lines[1:], start=2):
        cells = line.split('\t')
        if len(cells) != len(FIELDS):
            raise ReferenceError_(f'{TSV_REL}:{n}: expected {len(FIELDS)} fields, found {len(cells)}')
        row = dict(zip(FIELDS, cells))
        for k in FIELDS:
            if not row[k].strip():
                raise ReferenceError_(f'{TSV_REL}:{n}: field {k!r} is blank')
        row['line'] = str(n)
        if row['id'] in seen:
            raise ReferenceError_(f'{TSV_REL}:{n}: duplicate id {row["id"]!r}')
        seen.add(row['id'])
        if row['kind'] not in KINDS:
            raise ReferenceError_(f'{TSV_REL}:{n}: kind {row["kind"]!r} is not one of {", ".join(KINDS)}')
        allowed = REPO_AVAILABILITY if row['kind'] in REPO_KINDS else OFF_TREE_AVAILABILITY
        if row['availability'] not in allowed:
            raise ReferenceError_(
                f'{TSV_REL}:{n}: kind {row["kind"]!r} may not have availability {row["availability"]!r} '
                f'(allowed: {", ".join(allowed)})')
        rows.append(row)
    if not rows:
        raise ReferenceError_(f'{TSV_REL}: no rows')
    ordered = sorted(rows, key=lambda r: r['id'])
    if [r['id'] for r in rows] != [r['id'] for r in ordered]:
        raise ReferenceError_(f'{TSV_REL}: rows are not in canonical id order; expected '
                              + ', '.join(r['id'] for r in ordered))
    return rows


def resolve(root: Path, row: dict):
    rel, kind, n = row['path'], row['kind'], row['line']

    if kind in OFF_TREE_KINDS:
        # An off-tree reference must not be a live repository path wearing a costume: if it resolves in the
        # tree, it is a repository reference and must be typed as one.
        if not rel.startswith('{') and (root / rel).exists() and '..' not in Path(rel).parts:
            raise ReferenceError_(
                f'{TSV_REL}:{n}: {row["id"]} is typed {kind!r} but {rel!r} EXISTS in this tree — '
                f'type it as a repository reference instead of externalizing a live path')
        return

    if rel.startswith('/') or '..' in Path(rel).parts:
        raise ReferenceError_(f'{TSV_REL}:{n}: {row["id"]}: path {rel!r} escapes the repository root')
    target = root / rel
    if target.is_symlink():
        raise ReferenceError_(f'{TSV_REL}:{n}: {row["id"]}: path {rel!r} is a symlink')
    if not target.exists():
        raise ReferenceError_(f'{TSV_REL}:{n}: {row["id"]}: path {rel!r} does not exist in this tree')
    if kind == 'repository-file' and not target.is_file():
        raise ReferenceError_(f'{TSV_REL}:{n}: {row["id"]}: {rel!r} is declared a file but is not one')
    if kind == 'repository-directory' and not target.is_dir():
        raise ReferenceError_(f'{TSV_REL}:{n}: {row["id"]}: {rel!r} is declared a directory but is not one')


def check_owner(root: Path, row: dict):
    """The owner names the document that DIRECTS work to this path; it must itself be readable here."""
    owner = row['owner']
    candidates = [root / owner, root / '.review/fcb/current' / owner]
    for c in candidates:
        if c.is_file() and not c.is_symlink():
            return
    raise ReferenceError_(
        f'{TSV_REL}:{row["line"]}: {row["id"]}: owner {owner!r} is not a readable file in this tree')


def run(root: Path) -> str:
    rows = load_rows(root)
    for row in rows:
        resolve(root, row)
        check_owner(root, row)
    repo = sum(1 for r in rows if r['kind'] in REPO_KINDS)
    return (f'{len(rows)} declared reference(s): {repo} resolve in this tree, '
            f'{len(rows) - repo} explicitly typed off-tree')


# ───────────────────────────────────────────────────────────── adversarial controls
def self_test(root: Path) -> int:
    import shutil, tempfile
    failures = []
    counts = {'total': 0, 'must_fail': 0}

    def scenario(label: str, mutate, expect=None):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with tempfile.TemporaryDirectory() as d:
            work = Path(d) / 'tree'
            shutil.copytree(root, work, symlinks=True,
                            ignore=shutil.ignore_patterns('.git', '_build', '*.vo', '*.glob'))
            try:
                mutate(work)
            except Exception as exc:
                failures.append(f'{label}: could not construct the scenario ({exc})'); return
            try:
                run(work)
                if expect is not None:
                    failures.append(f'{label}: expected failure containing {expect!r}, but the gate passed')
            except ReferenceError_ as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')

    def tsv(work: Path) -> Path:
        return work / TSV_REL

    def rows_of(work: Path):
        return tsv(work).read_text(encoding='utf-8').split('\n')

    def first_repo_row(work: Path):
        for i, l in enumerate(rows_of(work)[1:], start=1):
            c = l.split('\t')
            if len(c) == 5 and c[1] == 'repository-file':
                return i, c
        raise AssertionError('no repository-file row in the fixture')

    def set_field(work: Path, idx: int, field: int, value: str):
        L = rows_of(work); c = L[idx].split('\t'); c[field] = value
        L[idx] = '\t'.join(c); tsv(work).write_text('\n'.join(L), encoding='utf-8')

    scenario('canonical fixture passes', lambda w: w)
    scenario('a declared path is missing',
             lambda w: (w / first_repo_row(w)[1][2]).unlink(),
             expect='does not exist in this tree')
    scenario('a declared path was renamed',
             lambda w: rename_target(w),
             expect='does not exist in this tree')
    scenario('the manifest itself is deleted',
             lambda w: tsv(w).unlink(),
             expect='does not exist')
    scenario('path traversal',
             lambda w: set_field(w, first_repo_row(w)[0], 2, '../outside.md'),
             expect='escapes the repository root')
    scenario('symlinked target',
             lambda w: symlink_target(w, *first_repo_row(w)),
             expect='is a symlink')
    scenario('a repository path falsely typed as external evidence',
             lambda w: falsely_externalize(w),
             expect='EXISTS in this tree')
    scenario('a file declared as a directory',
             lambda w: set_field(w, first_repo_row(w)[0], 1, 'repository-directory'),
             expect='declared a directory but is not one')
    scenario('a directory declared as a file',
             lambda w: set_field(w, dir_row(w)[0], 1, 'repository-file'),
             expect='declared a file but is not one')
    scenario('unknown kind',
             lambda w: set_field(w, first_repo_row(w)[0], 1, 'wishful-thinking'),
             expect='is not one of')
    scenario('repository kind claiming an off-tree availability',
             lambda w: set_field(w, first_repo_row(w)[0], 3, 'not-in-repository'),
             expect='may not have availability')
    scenario('duplicate id',
             lambda w: dup_row(w),
             expect='duplicate id')
    scenario('malformed field count',
             lambda w: trunc_row(w),
             expect='expected 5 fields')
    scenario('rows out of canonical order',
             lambda w: swap_rows(w),
             expect='not in canonical id order')
    scenario('an owner that is not a readable file',
             lambda w: set_field(w, first_repo_row(w)[0], 4, 'NO_SUCH_OWNER.md'),
             expect='is not a readable file in this tree')
    scenario('invalid UTF-8 in the manifest',
             lambda w: tsv(w).write_bytes(tsv(w).read_bytes() + b'\xff'),
             expect='is not valid UTF-8')

    total, must_fail = counts['total'], counts['must_fail']
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: FCB-REFERENCE SELF-TEST FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: fcb-reference self-test OK — {total} controls '
          f'({must_fail} must-fail with the reason pinned, {total - must_fail} must-accept) ✓')
    return 0


def dir_row(work: Path):
    lines = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    for i, l in enumerate(lines[1:], start=1):
        c = l.split('\t')
        if len(c) == 5 and c[1] == 'repository-directory':
            return i, c
    raise AssertionError('no repository-directory row in the fixture')


def rename_target(work: Path):
    lines = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    for l in lines[1:]:
        c = l.split('\t')
        if len(c) == 5 and c[1] == 'repository-file':
            p = work / c[2]
            p.rename(p.with_name(p.name + '.renamed')); return
    raise AssertionError('no repository-file row in the fixture')


def falsely_externalize(work: Path):
    """Retype ONE row, resolved once — a second lookup after the first edit finds a different row."""
    p = work / TSV_REL; L = p.read_text(encoding='utf-8').split('\n')
    for i, l in enumerate(L[1:], start=1):
        c = l.split('\t')
        if len(c) == 5 and c[1] == 'repository-file':
            c[1], c[3] = 'external-evidence', 'not-in-repository'
            L[i] = '\t'.join(c)
            p.write_text('\n'.join(L), encoding='utf-8'); return
    raise AssertionError('no repository-file row in the fixture')


def symlink_target(work: Path, idx: int, cells):
    p = work / cells[2]
    body = p.read_bytes(); p.unlink()
    other = p.with_suffix(p.suffix + '.real'); other.write_bytes(body)
    p.symlink_to(other.name)


def dup_row(work: Path):
    p = work / TSV_REL; L = p.read_text(encoding='utf-8').split('\n')
    p.write_text('\n'.join(L[:2] + [L[1]] + L[2:]), encoding='utf-8')


def trunc_row(work: Path):
    p = work / TSV_REL; L = p.read_text(encoding='utf-8').split('\n')
    L[1] = L[1].rsplit('\t', 1)[0]
    p.write_text('\n'.join(L), encoding='utf-8')


def swap_rows(work: Path):
    p = work / TSV_REL; L = p.read_text(encoding='utf-8').split('\n')
    p.write_text('\n'.join([L[0], L[2], L[1]] + L[3:]), encoding='utf-8')


def main() -> int:
    ap = argparse.ArgumentParser(description='D-24 FCB operational-reference gate')
    ap.add_argument('--root', default='.', help='repository or exported-tree root')
    ap.add_argument('--self-test', action='store_true', help='run the adversarial controls')
    args = ap.parse_args()
    root = Path(args.root).resolve()
    if args.self_test:
        return self_test(root)
    try:
        msg = run(root)
    except ReferenceError_ as exc:
        print(f'fido: FCB-REFERENCE GATE FAILED — {exc}', file=sys.stderr)
        return 1
    print(f'fido: fcb-reference gate OK — {msg} ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
