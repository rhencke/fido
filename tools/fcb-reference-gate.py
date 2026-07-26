#!/usr/bin/env python3
"""Governance D-24 — a COMPLETE two-way relation between the live authority corpus and its typed references.

One data authority: `.review/fcb/current/FIDO_FCB_REFERENCES.tsv` —
`id, kind, path, availability, owner, owner_anchor`.

Validating the declared rows is not enough, and that gap was real: a corpus can name a path that has no row
at all, and a gate that only checks its own chosen rows reports green while the FCB directs a reader at a
file that does not exist. So both directions are proved.

  MANIFEST -> CORPUS   every row's path resolves in this tree (or is explicitly typed off-tree with a stated
                       availability), and its owner document carries EXACTLY ONE `<!-- FIDO-FCB-REF:<ID> -->`
                       marker on a line that also contains that row's exact path.
  CORPUS -> MANIFEST   every repository-rooted operational path form appearing anywhere in the live authority
                       corpus is declared by exactly one row.

The corpus scan is fail-closed and has no exception list: a string shaped like a repository-rooted
operational path is either a typed reference or a blocking untyped one. It recognises paths by their ROOT
(`.review/`, `tools/`, `gate/`, `e2e/`, `plugin/`) and the exact root operational files, which is why it does
not trip over `.go`, `linux/amd64` or `gc.go` the way a backtick scanner would — the earlier version avoided
an exception list by giving up on completeness instead.

Everything fails closed. A missing file, a renamed target, a directory where a file was declared (or the
reverse), a symlink, a path escaping the tree, an unknown kind or availability, a duplicate id, a duplicate
or missing marker, a marker whose line does not contain its path, two rows claiming one path, a malformed
row, an owner that is not a readable file, a repository path dressed up as external evidence, an undeclared
corpus path, a read/decode error — each is an error naming the exact row or document and the reason.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

TSV_REL = '.review/fcb/current/FIDO_FCB_REFERENCES.tsv'
FIELDS = ('id', 'kind', 'path', 'availability', 'owner', 'owner_anchor')

# The live authority corpus: the documents whose text DIRECTS work. A path named here is operational.
CORPUS_GLOBS = ('.review/fcb/current/*.md',)
CORPUS_FILES = ('.review/NEXT_STEPS.md', '.review/OPEN_QUESTIONS.md', '.review/REVIEW_REQUEST.md',
                'CLAUDE.md')
# Repository-rooted operational path forms. Recognised by ROOT, not by backticks, so there is no exception
# list to hide a dangling path in.
PATH_ROOTS = ('.review/', 'tools/', 'gate/', 'e2e/', 'plugin/')
ROOT_FILES = ('CLAUDE.md', 'ARCHITECTURE.md', 'PROGRESS.md', 'Makefile', 'Dockerfile', 'dune')
MARKER = 'FIDO-FCB-REF'

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
    # exactly one row owns a path — otherwise the corpus->manifest relation is not a function
    by_path = {}
    for r in rows:
        by_path.setdefault(r['path'], []).append(r)
    for path, owners in by_path.items():
        if len(owners) > 1:
            raise ReferenceError_(
                f'{TSV_REL}: path {path!r} is claimed by {len(owners)} rows '
                f'({", ".join(o["id"] for o in owners)}) — exactly one row owns a path')
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


def owner_path(root: Path, row: dict) -> Path:
    """The owner names the document that DIRECTS work to this path; it must itself be readable here."""
    owner = row['owner']
    for c in (root / owner, root / '.review/fcb/current' / owner):
        if c.is_file() and not c.is_symlink():
            return c
    raise ReferenceError_(
        f'{TSV_REL}:{row["line"]}: {row["id"]}: owner {owner!r} is not a readable file in this tree')


def check_owner_marker(root: Path, row: dict):
    """EXACTLY ONE `<!-- FIDO-FCB-REF:<ID> -->` in the owner, on a line carrying this row's exact path.

    Naming an owner is not the same as that owner owning the reference. The marker makes ownership a fact in
    the document rather than a claim in the manifest, and binding it to the path's own line stops a marker
    drifting onto some unrelated sentence."""
    if row['owner_anchor'] != f'{MARKER}:{row["id"]}':
        raise ReferenceError_(
            f'{TSV_REL}:{row["line"]}: {row["id"]}: owner_anchor must be '
            f'{MARKER}:{row["id"]!r}, found {row["owner_anchor"]!r}')
    doc = owner_path(root, row)
    text = read_text(doc, f'{row["id"]} owner document')
    marker = f'<!-- {row["owner_anchor"]} -->'
    hits = [l for l in text.split('\n') if marker in l]
    if len(hits) == 0:
        raise ReferenceError_(f'{row["owner"]}: missing owner marker {marker!r} for {row["id"]}')
    if len(hits) > 1:
        raise ReferenceError_(
            f'{row["owner"]}: owner marker {marker!r} for {row["id"]} occurs {len(hits)} times, expected once')
    if row['path'] not in hits[0]:
        raise ReferenceError_(
            f'{row["owner"]}: the marker for {row["id"]} is not on a line carrying its declared path '
            f'{row["path"]!r} — the marker must bind the exact path it claims to own')


def corpus_documents(root: Path):
    docs = []
    for pattern in CORPUS_GLOBS:
        docs.extend(sorted(root.glob(pattern)))
    for rel in CORPUS_FILES:
        p = root / rel
        if p.is_file():
            docs.append(p)
    if not docs:
        raise ReferenceError_('the live authority corpus is empty — refusing to report a complete relation '
                              'over nothing')
    return docs


def operational_paths(text: str):
    """Every repository-rooted operational path FORM in a document, normalized."""
    roots = '|'.join(re.escape(r) for r in PATH_ROOTS)
    files = '|'.join(re.escape(f) for f in ROOT_FILES)
    pat = re.compile(rf'(?:{roots})[A-Za-z0-9._/-]*' rf'|(?<![\w./-])(?:{files})(?![\w./-])')
    out = set()
    for m in pat.finditer(text):
        s = m.group(0).rstrip('/.,;:)`')          # normalize a trailing slash and sentence punctuation
        if s:
            out.add(s)
    return out


def check_corpus_declared(root: Path, rows, docs):
    """CORPUS -> MANIFEST: every operational path the live authority names is declared by exactly one row."""
    by_path = {r['path']: r for r in rows}
    undeclared = []
    for doc in docs:
        rel = str(doc.relative_to(root))
        text = read_text(doc, 'live authority document')
        for s in sorted(operational_paths(text)):
            if s not in by_path:
                undeclared.append((rel, s))
    if undeclared:
        shown = '; '.join(f'{d} names {s!r}' for d, s in undeclared[:8])
        raise ReferenceError_(
            f'{len(undeclared)} UNDECLARED operational reference(s) in the live authority corpus — every '
            f'repository-rooted path a current authority names must have a typed row in {TSV_REL}: {shown}'
            + ('' if len(undeclared) <= 8 else f' … and {len(undeclared) - 8} more'))


def run(root: Path) -> str:
    rows = load_rows(root)
    docs = corpus_documents(root)          # resolved first: an empty corpus is its own reported failure
    for row in rows:
        resolve(root, row)
        check_owner_marker(root, row)
    check_corpus_declared(root, rows, docs)
    repo = sum(1 for r in rows if r['kind'] in REPO_KINDS)
    return (f'{len(rows)} declared reference(s): {repo} resolve in this tree, '
            f'{len(rows) - repo} explicitly typed off-tree; every row has one bound owner marker; '
            f'{len(docs)} live authority document(s) name no undeclared operational path')


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
            if len(c) == len(FIELDS) and c[1] == 'repository-file':
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
             expect='expected 6 fields')
    scenario('rows out of canonical order',
             lambda w: swap_rows(w),
             expect='not in canonical id order')
    scenario('an owner that is not a readable file',
             lambda w: set_field(w, first_repo_row(w)[0], 4, 'NO_SUCH_OWNER.md'),
             expect='is not a readable file in this tree')
    scenario('invalid UTF-8 in the manifest',
             lambda w: tsv(w).write_bytes(tsv(w).read_bytes() + b'\xff'),
             expect='is not valid UTF-8')
    # ── the CORPUS -> MANIFEST direction. The first of these is the reviewer's exact mutation, which the
    #    row-validating gate passed.
    scenario('an unmanifested NONEXISTENT .review path in a live authority document',
             lambda w: append_to_index(w, '**Operational review:** read `.review/NO_SUCH_OPERATIONAL_FILE.md`.'),
             expect='UNDECLARED operational reference')
    scenario('an unmanifested EXISTING tools path in a live authority document',
             lambda w: append_to_index(w, 'Run `tools/rocq-profile.py` before review.'),
             expect='UNDECLARED operational reference')
    scenario('one operational path claimed by two rows',
             lambda w: duplicate_path_row(w),
             expect='is claimed by 2 rows')
    scenario('the live authority corpus is empty',
             lambda w: strip_corpus(w),
             expect='corpus is empty')
    # ── owner markers
    scenario('a manifest row whose owner has no marker',
             lambda w: strip_marker(w),
             expect='missing owner marker')
    scenario('a duplicate owner marker',
             lambda w: duplicate_marker(w),
             expect='occurs 2 times, expected once')
    scenario('a marker whose line does not carry its declared path',
             lambda w: unbind_marker(w),
             expect='is not on a line carrying its declared path')
    scenario('an owner_anchor that does not match its row id',
             lambda w: set_field(w, first_repo_row(w)[0], 5, 'FIDO-FCB-REF:SOMETHING-ELSE'),
             expect='owner_anchor must be')
    scenario('an owner document that cannot be decoded',
             lambda w: (w / '.review/fcb/current/FIDO_FCB_INDEX.md').write_bytes(b'# x\n\xff'),
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
        if len(c) == len(FIELDS) and c[1] == 'repository-directory':
            return i, c
    raise AssertionError('no repository-directory row in the fixture')


def append_to_index(work: Path, line: str):
    p = work / '.review/fcb/current/FIDO_FCB_INDEX.md'
    p.write_text(p.read_text(encoding='utf-8') + '\n' + line + '\n', encoding='utf-8')


def duplicate_path_row(work: Path):
    """Two rows claiming one path: the relation stops being a function."""
    p = work / TSV_REL; L = p.read_text(encoding='utf-8').split('\n')
    c = L[1].split('\t'); c[0] = 'AAA-' + c[0]; c[5] = f'FIDO-FCB-REF:{c[0]}'
    p.write_text('\n'.join([L[0], '\t'.join(c)] + L[1:]), encoding='utf-8')


def strip_corpus(work: Path):
    for f in list((work / '.review/fcb/current').glob('*.md')):
        f.unlink()
    for rel in CORPUS_FILES:
        q = work / rel
        if q.is_file():
            q.unlink()


def _first_row_with_marker(work: Path):
    L = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    for l in L[1:]:
        c = l.split('\t')
        if len(c) == len(FIELDS):
            for cand in (work / c[4], work / '.review/fcb/current' / c[4]):
                if cand.is_file() and f'<!-- {c[5]} -->' in cand.read_text(encoding='utf-8'):
                    return c, cand
    raise AssertionError('no row with a placed marker in the fixture')


def strip_marker(work: Path):
    c, doc = _first_row_with_marker(work)
    doc.write_text(doc.read_text(encoding='utf-8').replace(f' <!-- {c[5]} -->', '', 1), encoding='utf-8')


def duplicate_marker(work: Path):
    c, doc = _first_row_with_marker(work)
    doc.write_text(doc.read_text(encoding='utf-8') + f'\n<!-- {c[5]} --> {c[2]}\n', encoding='utf-8')


def unbind_marker(work: Path):
    """Move the marker to a line that does not name its path — ownership must bind the exact path."""
    c, doc = _first_row_with_marker(work)
    t = doc.read_text(encoding='utf-8').replace(f' <!-- {c[5]} -->', '', 1)
    doc.write_text(t + f'\nA sentence with no path at all. <!-- {c[5]} -->\n', encoding='utf-8')


def rename_target(work: Path):
    lines = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    for l in lines[1:]:
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[1] == 'repository-file':
            p = work / c[2]
            p.rename(p.with_name(p.name + '.renamed')); return
    raise AssertionError('no repository-file row in the fixture')


def falsely_externalize(work: Path):
    """Retype ONE row, resolved once — a second lookup after the first edit finds a different row."""
    p = work / TSV_REL; L = p.read_text(encoding='utf-8').split('\n')
    for i, l in enumerate(L[1:], start=1):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[1] == 'repository-file':
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
