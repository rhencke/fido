#!/usr/bin/env python3
"""Governance D-24 — a COMPLETE two-way relation between the live authority corpus and its typed references.

One data authority: `.review/fcb/current/FIDO_FCB_REFERENCES.tsv` —
`id, kind, path, availability, owner, owner_anchor, corpus_role`.

That manifest owns BOTH halves of the relation:

  MANIFEST -> TARGET   every row's path resolves in this tree (or is explicitly typed off-tree with a stated
                       availability), and its owner document carries EXACTLY ONE `<!-- FIDO-FCB-REF:<ID> -->`
                       marker on a line that also contains that row's exact path.
  AUTHORITY -> MANIFEST  every repository-rooted operational path form appearing in a CURRENT AUTHORITY is
                       declared by exactly one row.

`corpus_role` decides which documents make up the live authority corpus. An `authority` is a current normative
source: it must be a present, readable, UTF-8 repository FILE, and its own operational references are scanned.
A `reference` resolves and is owned, but naming it does not make it a current authority — a generated view is
a `reference` because its canonical data source carries the authority.

Corpus membership was previously a Python constant, and that was a real false green: the active repair
directive, the functional contract and the accepted review basis were never read at all, so a dangling
operational path appended to the active directive left the gate reporting a complete relation. A typed row
proves a path EXISTS; it says nothing about whether that document's own references are complete. Deriving the
scanned set from the manifest means a new authority is scanned by adding a row, never by editing this file.

Four structural declarations assign authority, and each is checked rather than assumed:

  * the live-file table in the FCB Index states a role for every file beside the manifest, and the manifest
    must agree with it — in both directions, so neither a downgraded row nor a deleted table line passes;
  * the document `NEXT_STEPS` names after `Authority:` is the active repair, and must be an authority;
  * the `contract:` and `review_basis:` paths in `REVIEW_REQUEST` must be authorities;
  * the M-series plan the FCB Index names must be an authority.

The corpus scan is fail-closed and has no exception list: a string shaped like a repository-rooted operational
path is either a typed reference or a blocking untyped one. It recognises paths by their ROOT (`.review/`,
`tools/`, `gate/`, `e2e/`, `plugin/`) and the exact root operational files, which is why it does not trip over
`.go`, `linux/amd64` or `gc.go` the way a backtick scanner would.

Everything fails closed. A missing file, a renamed target, a directory where a file was declared (or the
reverse), a symlink, a path escaping the tree, an unknown kind, availability or corpus role, a duplicate id, a
duplicate or missing marker, a marker whose line does not carry its path, two rows claiming one path, a
malformed row, an owner that is not a readable file, a repository path dressed up as external evidence, an
authority that is a directory or off-tree or undecodable or unreadable, a structural declaration pointing at a
non-authority, an undeclared corpus path, a read/decode error — each is an error naming the exact row or
document and the reason.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# The ONE hard-coded path: the bootstrap needed to load the manifest that owns everything else.
TSV_REL = '.review/fcb/current/FIDO_FCB_REFERENCES.tsv'
FIELDS = ('id', 'kind', 'path', 'availability', 'owner', 'owner_anchor', 'corpus_role')

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
CORPUS_ROLES = ('authority', 'reference')

# The FIXED POINTS of the governance structure, named by MANIFEST ID — never by path. §4.4 of the repair-20
# directive requires each of these declarations to be checked, so the checker must be able to find the
# document that makes it. Resolving through the manifest means this file holds no list of authority documents
# and no second copy of any path: rename a document and its row carries the check with it. A missing id is a
# gate failure, not a skipped check.
INDEX_ID = 'REVIEW-FCB-CURRENT-FIDO-FCB-INDEX-MD'
NEXT_STEPS_ID = 'REVIEW-NEXT-STEPS-MD'
REVIEW_REQUEST_ID = 'REVIEW-REVIEW-REQUEST-MD'

# One live-file table row: a backticked path, then its declared corpus role.
INDEX_TABLE_ROW = re.compile(r'^\|\s*`([^`]+)`\s*\|\s*([A-Za-z-]+)\s*\|')

# Structural declarations: (id of the naming document, pattern capturing the named path, what it declares).
DECLARATION_SITES = (
    (NEXT_STEPS_ID, re.compile(r'(?m)^\s*Authority:\s*`([^`]+)`'),
     'the active repair directive named after `Authority:`'),
    (REVIEW_REQUEST_ID, re.compile(r'(?m)^\s*contract:[ \t]*(\S+)[ \t]*$'),
     'the functional contract named after `contract:`'),
    (REVIEW_REQUEST_ID, re.compile(r'(?m)^\s*review_basis:[ \t]*(\S+)[ \t]*$'),
     'the accepted review basis named after `review_basis:`'),
    (INDEX_ID, re.compile(r'(?m)^\s*\*\*M-series authority:\*\*\s*`([^`]+)`'),
     'the accepted M-series plan the FCB Index names'),
)


class ReferenceError_(Exception):
    """Any failure to read, parse, validate, or resolve. Always names the exact row and reason."""


def read_text(path: Path, label: str, reader=None) -> str:
    """The one read of a corpus surface. Injectable so the read-failure control is DETERMINISTIC: `chmod 000`
    is not a control on a tree that builds as root — the file stays readable and the control silently skips."""
    try:
        return (reader or _plain_read)(path)
    except FileNotFoundError:
        raise ReferenceError_(f'{label}: {path} does not exist')
    except UnicodeDecodeError as exc:
        raise ReferenceError_(f'{label}: {path} is not valid UTF-8 ({exc})')
    except OSError as exc:
        raise ReferenceError_(f'{label}: {path} could not be read ({exc.__class__.__name__}: {exc})')


def _plain_read(path: Path) -> str:
    return path.read_text(encoding='utf-8')


def load_rows(root: Path, reader=None):
    text = read_text(root / TSV_REL, 'FCB reference manifest', reader)
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
        if row['corpus_role'] not in CORPUS_ROLES:
            raise ReferenceError_(f'{TSV_REL}:{n}: corpus_role {row["corpus_role"]!r} is not one of '
                                  f'{", ".join(CORPUS_ROLES)}')
        # Only a real, present repository FILE can be a current authority: a directory has no text to scan,
        # and an off-tree reference is by definition not in this ref, so neither can carry authority here.
        if row['corpus_role'] == 'authority' and row['kind'] != 'repository-file':
            raise ReferenceError_(
                f'{TSV_REL}:{n}: {row["id"]} is kind {row["kind"]!r} and may not be a current authority — '
                f'only a present repository file can be scanned as one')
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


def row_by_id(rows, wanted: str, why: str):
    for r in rows:
        if r['id'] == wanted:
            return r
    raise ReferenceError_(f'{TSV_REL}: no row {wanted!r} — {why} cannot be located, so its declarations '
                          f'cannot be checked; the gate refuses to report a complete relation')


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
    for c in (root / owner, root / Path(TSV_REL).parent / owner):
        if c.is_file() and not c.is_symlink():
            return c
    raise ReferenceError_(
        f'{TSV_REL}:{row["line"]}: {row["id"]}: owner {owner!r} is not a readable file in this tree')


def check_owner_marker(root: Path, row: dict, reader=None):
    """EXACTLY ONE `<!-- FIDO-FCB-REF:<ID> -->` in the owner, on a line carrying this row's exact path.

    Naming an owner is not the same as that owner owning the reference. The marker makes ownership a fact in
    the document rather than a claim in the manifest, and binding it to the path's own line stops a marker
    drifting onto some unrelated sentence."""
    if row['owner_anchor'] != f'{MARKER}:{row["id"]}':
        raise ReferenceError_(
            f'{TSV_REL}:{row["line"]}: {row["id"]}: owner_anchor must be '
            f'{MARKER}:{row["id"]!r}, found {row["owner_anchor"]!r}')
    doc = owner_path(root, row)
    text = read_text(doc, f'{row["id"]} owner document', reader)
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


# ───────────────────────────────────────────────────────── the authority set, derived from the manifest
def authority_rows(rows):
    """The live authority corpus IS the set of `authority` rows. No parallel list, no Python constant."""
    authorities = [r for r in rows if r['corpus_role'] == 'authority']
    if not authorities:
        raise ReferenceError_('the live authority corpus is empty — no row declares corpus_role=authority, '
                              'so there is nothing to prove complete')
    return authorities


def check_authority_readable(root: Path, row: dict, reader=None) -> str:
    """An authority must be a present, readable, UTF-8 file. Read it HERE so the failure names the row."""
    target = root / row['path']
    if target.is_symlink():
        raise ReferenceError_(f'{TSV_REL}:{row["line"]}: {row["id"]}: an authority may not be a symlink')
    if target.is_dir():
        raise ReferenceError_(f'{TSV_REL}:{row["line"]}: {row["id"]}: an authority may not be a directory')
    return read_text(target, f'{row["id"]} authority document', reader)


def check_index_table_roles(root: Path, rows, reader=None) -> int:
    """The FCB Index live-file table DECLARES a role for every file beside the manifest; the manifest must
    agree, in both directions.

    Checking only the table would let a deleted line pass; checking only the manifest would let a downgraded
    row pass while the Index still called the file an authority. The corpus has to say one thing."""
    index_row = row_by_id(rows, INDEX_ID, 'the FCB Index')
    text = read_text(root / index_row['path'], 'FCB Index', reader)
    by_path = {r['path']: r for r in rows}

    declared = {}
    for line in text.split('\n'):
        m = INDEX_TABLE_ROW.match(line)
        if not m:
            continue
        path, role = m.group(1), m.group(2)
        if role not in CORPUS_ROLES:
            continue                       # some other two-column table; only role-bearing rows are declarations
        if path in declared and declared[path] != role:
            raise ReferenceError_(f'{index_row["path"]}: the live-file table gives {path!r} two different '
                                  f'roles ({declared[path]!r} and {role!r})')
        declared[path] = role

    live_dir = Path(TSV_REL).parent
    expected = {r['path'] for r in rows
                if r['kind'] == 'repository-file' and Path(r['path']).parent == live_dir}

    missing = sorted(expected - set(declared))
    if missing:
        raise ReferenceError_(
            f'{index_row["path"]}: the live-file table does not state a corpus role for '
            f'{len(missing)} file(s) beside the manifest: ' + ', '.join(missing))
    extra = sorted(set(declared) - {r['path'] for r in rows})
    if extra:
        raise ReferenceError_(
            f'{index_row["path"]}: the live-file table names {len(extra)} path(s) with no manifest row: '
            + ', '.join(extra))
    for path in sorted(declared):
        if declared[path] != by_path[path]['corpus_role']:
            raise ReferenceError_(
                f'{index_row["path"]}: the live-file table calls {path!r} a {declared[path]!r} but '
                f'{TSV_REL} declares corpus_role {by_path[path]["corpus_role"]!r} — the corpus must state '
                f'one truth about what is current authority')
    return len(declared)


def check_live_set_complete(root: Path, rows) -> int:
    """Every file sitting IN the canonical live FCB directory is declared by a row.

    A document's LOCATION is a claim. Dropped into the live set it reads as current authority to any human
    browsing the directory — but without a row it has no role, therefore no scan, which is the same
    unscanned-authority shape this repair exists to remove, one level further out. Checking the table against
    the manifest is not enough when both can simply omit the same file."""
    live_dir = root / Path(TSV_REL).parent
    if not live_dir.is_dir():
        raise ReferenceError_(f'{Path(TSV_REL).parent}: the canonical live FCB directory is not a directory')
    declared = {r['path'] for r in rows}
    present = sorted(str(p.relative_to(root)) for p in live_dir.iterdir() if not p.is_dir())
    if not present:
        raise ReferenceError_(f'{Path(TSV_REL).parent}: the canonical live FCB directory is empty')
    missing = [p for p in present if p not in declared]
    if missing:
        raise ReferenceError_(
            f'{len(missing)} file(s) sit in the canonical live FCB directory with NO row in {TSV_REL}, so '
            f'they carry no corpus role and are never scanned: ' + ', '.join(missing))
    return len(present)


def check_declaration_sites(root: Path, rows, reader=None) -> int:
    """Every structural declaration that ASSIGNS authority must point at a row that carries it.

    A typed row proves a path exists. These four declarations are what make a document current, and each one
    is exactly where a downgrade would hide: mark the active repair a `reference` and it silently stops being
    read while every other check stays green."""
    by_path = {r['path']: r for r in rows}
    checked = 0
    for doc_id, pattern, what in DECLARATION_SITES:
        doc_row = row_by_id(rows, doc_id, f'the document declaring {what}')
        text = read_text(root / doc_row['path'], f'{doc_row["id"]} declaration site', reader)
        hits = pattern.findall(text)
        if not hits:
            raise ReferenceError_(
                f'{doc_row["path"]}: does not declare {what} — the declaration is required, and a gate that '
                f'skips a missing declaration is how an unscanned authority hides')
        if len(hits) > 1:
            raise ReferenceError_(
                f'{doc_row["path"]}: declares {what} {len(hits)} times ({", ".join(sorted(set(hits)))}) — '
                f'exactly one declaration, or the corpus has two answers')
        named = hits[0].strip().strip('`')
        row = by_path.get(named)
        if row is None:
            raise ReferenceError_(
                f'{doc_row["path"]}: {what} is {named!r}, which has no row in {TSV_REL}')
        if row['corpus_role'] != 'authority':
            raise ReferenceError_(
                f'{doc_row["path"]}: {what} is {named!r}, but {TSV_REL} declares it a '
                f'{row["corpus_role"]!r} — a document that assigns current work is an authority and must be '
                f'scanned as one')
        checked += 1
    return checked


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


def check_corpus_declared(root: Path, rows, authorities, reader=None):
    """AUTHORITY -> MANIFEST: every operational path a current authority names is declared by one row."""
    by_path = {r['path']: r for r in rows}
    undeclared = []
    for row in authorities:
        text = check_authority_readable(root, row, reader)
        for s in sorted(operational_paths(text)):
            if s not in by_path:
                undeclared.append((row['path'], s))
    if undeclared:
        shown = '; '.join(f'{d} names {s!r}' for d, s in undeclared[:8])
        raise ReferenceError_(
            f'{len(undeclared)} UNDECLARED operational reference(s) in the live authority corpus — every '
            f'repository-rooted path a current authority names must have a typed row in {TSV_REL}: {shown}'
            + ('' if len(undeclared) <= 8 else f' … and {len(undeclared) - 8} more'))


def run(root: Path, reader=None) -> str:
    rows = load_rows(root, reader)
    authorities = authority_rows(rows)     # resolved first: an empty corpus is its own reported failure
    for row in rows:
        resolve(root, row)
        check_owner_marker(root, row, reader)
    live = check_live_set_complete(root, rows)
    declared_roles = check_index_table_roles(root, rows, reader)
    sites = check_declaration_sites(root, rows, reader)
    check_corpus_declared(root, rows, authorities, reader)
    repo = sum(1 for r in rows if r['kind'] in REPO_KINDS)
    return (f'{len(rows)} declared reference(s): {repo} resolve in this tree, '
            f'{len(rows) - repo} explicitly typed off-tree; every row has one bound owner marker; '
            f'all {live} file(s) in the canonical live set are declared and {declared_roles} role(s) agree '
            f'with the FCB Index table; {sites} structural declaration(s) point at an authority; '
            f'{len(authorities)} current authority document(s) name no undeclared operational path')


# ───────────────────────────────────────────────────────────── adversarial controls
def self_test(root: Path) -> int:
    import shutil, tempfile
    failures = []
    counts = {'total': 0, 'must_fail': 0}

    def scenario(label: str, mutate, expect=None, reader=None):
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
                run(work, reader)
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
             expect='may not be a current authority')
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
             expect='expected 7 fields')
    scenario('rows out of canonical order',
             lambda w: swap_rows(w),
             expect='not in canonical id order')
    scenario('an owner that is not a readable file',
             lambda w: set_field(w, first_repo_row(w)[0], 4, 'NO_SUCH_OWNER.md'),
             expect='is not a readable file in this tree')
    scenario('invalid UTF-8 in the manifest',
             lambda w: tsv(w).write_bytes(tsv(w).read_bytes() + b'\xff'),
             expect='is not valid UTF-8')
    # ── the AUTHORITY -> MANIFEST direction. The first of these is the reviewer's original mutation, which
    #    the row-validating gate passed.
    scenario('an unmanifested NONEXISTENT .review path in a live authority document',
             lambda w: append_to(w, INDEX_ID, '**Operational review:** read `.review/NO_SUCH_FILE_A.md`.'),
             expect='UNDECLARED operational reference')
    scenario('an unmanifested EXISTING tools path in a live authority document',
             lambda w: append_to(w, INDEX_ID, 'Run `tools/rocq-profile.py` before review.'),
             expect='UNDECLARED operational reference')
    scenario('one operational path claimed by two rows',
             lambda w: duplicate_path_row(w),
             expect='is claimed by 2 rows')
    scenario('no row declares an authority role',
             lambda w: demote_every_row(w),
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
             lambda w: corrupt(w, INDEX_ID),
             expect='is not valid UTF-8')

    # ── repair 20 §4.5: the corpus_role relation itself.
    #
    # 1-3: a dangling path injected into each document the OLD gate never read at all.
    scenario('a dangling path injected into the ACTIVE REPAIR authority',
             lambda w: append_to(w, declared_path(w, 'Authority:'),
                                 'See `.review/NO_SUCH_REPAIR_ANNEX.md` for the annex.'),
             expect='UNDECLARED operational reference')
    scenario('a dangling path injected into the FUNCTIONAL CONTRACT',
             lambda w: append_to(w, declared_path(w, 'contract:'),
                                 'See `.review/NO_SUCH_CONTRACT_ANNEX.md` for the annex.'),
             expect='UNDECLARED operational reference')
    scenario('a dangling path injected into the ACCEPTED REVIEW BASIS',
             lambda w: append_to(w, declared_path(w, 'review_basis:'),
                                 'See `.review/NO_SUCH_BASIS_ANNEX.md` for the annex.'),
             expect='UNDECLARED operational reference')
    # 4-6: downgrading one of those three to `reference` silently unscans it, so it must fail loudly.
    scenario('the ACTIVE REPAIR row marked reference',
             lambda w: set_role_of_path(w, declared_path(w, 'Authority:'), 'reference'),
             expect='a document that assigns current work is an authority')
    scenario('the FUNCTIONAL CONTRACT row marked reference',
             lambda w: set_role_of_path(w, declared_path(w, 'contract:'), 'reference'),
             expect='a document that assigns current work is an authority')
    scenario('the ACCEPTED REVIEW BASIS row marked reference',
             lambda w: set_role_of_path(w, declared_path(w, 'review_basis:'), 'reference'),
             expect='a document that assigns current work is an authority')
    scenario('the M-SERIES PLAN row marked reference',
             lambda w: set_role_of_path(w, declared_path(w, '**M-series authority:**'), 'reference'),
             expect='a document that assigns current work is an authority')
    # 7-9: what an authority target may not be.
    scenario('an authority row whose target is a directory',
             lambda w: set_role_of_path(w, dir_row(w)[1][2], 'authority'),
             expect='may not be a current authority')
    scenario('an authority row whose target cannot be decoded',
             lambda w: corrupt(w, 'REVIEW-M-SERIES-PLAN-MD'),
             expect='is not valid UTF-8')
    scenario('an authority row whose target cannot be read', lambda w: w,
             expect='could not be read', reader=unreadable_m_series)
    # 10 + the must-accept twin: DYNAMIC discovery, with no edit to this file.
    scenario('a newly added authority file containing an undeclared path',
             lambda w: add_authority(w, 'Consult `.review/NO_SUCH_NEW_TARGET.md` next.'),
             expect='UNDECLARED operational reference')
    scenario('a newly added CLEAN authority file is discovered and scanned',
             lambda w: add_authority(w, 'Consult `.review/NEXT_STEPS.md` next.'))
    # …and the mutation that proves the twin above is not passing by never being read: the same new file, the
    # same clean text, but with the row left at `reference`. If the undeclared path in the dirty variant were
    # being caught by something other than authority discovery, this would fail too.
    scenario('the same new file left as a reference is NOT scanned',
             lambda w: add_authority(w, 'Consult `.review/NO_SUCH_NEW_TARGET.md` next.', role='reference'))
    # ── the Index live-file table, in both directions.
    scenario('the Index table role disagrees with the manifest',
             lambda w: set_role_of_path(w, live_set_authority(w), 'reference'),
             expect='the corpus must state one truth')
    scenario('a live-set role cell no longer states a role',
             lambda w: blank_table_role(w),
             expect='does not state a corpus role')
    scenario('a live-set file dropped from the Index table entirely',
             lambda w: drop_table_line(w),
             expect='does not state a corpus role')
    scenario('the Index table names a path with no manifest row',
             lambda w: append_to(w, INDEX_ID, '| `.review/fcb/current/NO_SUCH_LIVE_FILE.md` | authority | x |'),
             expect='no manifest row')
    # …and the direction neither the table nor the manifest can catch on its own: a file dropped into the
    # canonical live set that BOTH of them omit.  Its location claims current authority; without a row it has
    # no role and is never scanned.
    scenario('an undeclared file sitting in the canonical live set',
             lambda w: (w / Path(TSV_REL).parent / 'FIDO_FCB_STOWAWAY.md').write_text(
                 '# Stowaway\n\nConsult `.review/NO_SUCH_STOWAWAY_TARGET.md`.\n', encoding='utf-8'),
             expect='carry no corpus role and are never scanned')
    # ── the structural declarations themselves.  Each mutation keeps the path and the owner marker intact,
    #    so the failure is attributable to the declaration check and not to a marker the mutation broke.
    scenario('NEXT_STEPS names no active repair',
             lambda w: rekey_declaration(w, NEXT_STEPS_ID, 'Authority:', 'Background reading:'),
             expect='does not declare the active repair directive')
    scenario('REVIEW_REQUEST names no functional contract',
             lambda w: rekey_declaration(w, REVIEW_REQUEST_ID, 'contract:', 'former_contract:'),
             expect='does not declare the functional contract')
    scenario('the FCB Index names no M-series plan',
             lambda w: rekey_declaration(w, INDEX_ID, '**M-series authority:**', '**M-series note:**'),
             expect='does not declare the accepted M-series plan')
    scenario('NEXT_STEPS names an active repair with no row',
             lambda w: retarget_active_repair(w),
             expect='which has no row in')
    scenario('an unknown corpus_role',
             lambda w: set_field(w, first_repo_row(w)[0], 6, 'sort-of-binding'),
             expect='is not one of authority, reference')
    scenario('the manifest row for NEXT_STEPS is deleted',
             lambda w: delete_row(w, NEXT_STEPS_ID),
             expect=f'no row {NEXT_STEPS_ID!r}')

    total, must_fail = counts['total'], counts['must_fail']
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: FCB-REFERENCE SELF-TEST FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: fcb-reference self-test OK — {total} controls '
          f'({must_fail} must-fail with the reason pinned, {total - must_fail} must-accept) ✓')
    return 0


# ───────────────────────────────────────────────────────────── control helpers
def _rows(work: Path):
    return (work / TSV_REL).read_text(encoding='utf-8').split('\n')


def _write_rows(work: Path, L):
    (work / TSV_REL).write_text('\n'.join(L), encoding='utf-8')


def _cells(work: Path):
    return [(i, l.split('\t')) for i, l in enumerate(_rows(work)) if len(l.split('\t')) == len(FIELDS)][1:]


def path_of_id(work: Path, wanted: str) -> str:
    for _, c in _cells(work):
        if c[0] == wanted:
            return c[2]
    raise AssertionError(f'no row {wanted} in the fixture')


def declared_path(work: Path, label: str) -> str:
    """Resolve a structural declaration IN THE FIXTURE, exactly as the gate does — never a literal path."""
    site = {'Authority:': NEXT_STEPS_ID, 'contract:': REVIEW_REQUEST_ID,
            'review_basis:': REVIEW_REQUEST_ID, '**M-series authority:**': INDEX_ID}[label]
    doc = work / path_of_id(work, site)
    for doc_id, pattern, _what in DECLARATION_SITES:
        if doc_id == site and label.strip('*') in pattern.pattern.replace('\\', ''):
            hits = pattern.findall(doc.read_text(encoding='utf-8'))
            assert len(hits) == 1, f'{label}: expected one declaration, found {len(hits)}'
            return hits[0].strip().strip('`')
    raise AssertionError(f'no declaration site for {label}')


def live_set_authority(work: Path) -> str:
    """A file beside the manifest whose declared role is `authority` — the Index table must agree about it."""
    live_dir = str(Path(TSV_REL).parent)
    for _, c in _cells(work):
        if c[6] == 'authority' and str(Path(c[2]).parent) == live_dir and c[0] != INDEX_ID:
            return c[2]
    raise AssertionError('no live-set authority row in the fixture')


def set_role_of_path(work: Path, rel: str, role: str):
    L = _rows(work)
    for i, l in enumerate(L):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[2] == rel:
            c[6] = role; L[i] = '\t'.join(c); _write_rows(work, L); return
    raise AssertionError(f'no row for path {rel}')


def delete_row(work: Path, wanted: str):
    L = [l for l in _rows(work) if l.split('\t')[0] != wanted]
    _write_rows(work, L)


def demote_every_row(work: Path):
    L = _rows(work)
    for i, l in enumerate(L):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[0] != 'id':
            c[6] = 'reference'; L[i] = '\t'.join(c)
    _write_rows(work, L)


def append_to(work: Path, target: str, line: str):
    """Append a line to a document named by manifest id, or by relative path if the id is unknown."""
    try:
        rel = path_of_id(work, target)
    except AssertionError:
        rel = target
    p = work / rel
    p.write_text(p.read_text(encoding='utf-8') + '\n' + line + '\n', encoding='utf-8')


def corrupt(work: Path, wanted: str):
    p = work / path_of_id(work, wanted)
    p.write_bytes(b'# x\n\xff')


def unreadable_m_series(path: Path) -> str:
    """A reader that fails for exactly one authority target, so the read-failure control is deterministic."""
    if path.name == 'M_SERIES_PLAN.md':
        raise OSError(5, 'Input/output error')
    return path.read_text(encoding='utf-8')


def rekey_declaration(work: Path, doc_id: str, key: str, replacement: str):
    """Remove a structural DECLARATION by changing its key, leaving the path and its owner marker in place.

    Deleting the whole line would also delete the marker, and the marker check runs first — the control would
    then pass for a reason that has nothing to do with the declaration it exists to test."""
    p = work / path_of_id(work, doc_id)
    t = p.read_text(encoding='utf-8')
    assert t.count(key) == 1, f'{doc_id}: expected exactly one {key!r}, found {t.count(key)}'
    p.write_text(t.replace(key, replacement, 1), encoding='utf-8')


def retarget_active_repair(work: Path):
    """Point `Authority:` at a path with no row, keeping the old path on the line so the marker stays bound."""
    p = work / path_of_id(work, NEXT_STEPS_ID)
    t = p.read_text(encoding='utf-8')
    m = re.search(r'(?m)^(\s*Authority:\s*)`([^`]+)`', t)
    assert m, 'no Authority: declaration in the fixture'
    t2 = t[:m.start()] + f'{m.group(1)}`.review/NO_SUCH_DIRECTIVE.md` (was `{m.group(2)}`)' + t[m.end():]
    p.write_text(t2, encoding='utf-8')


def _table_line(work: Path, rel: str):
    p = work / path_of_id(work, INDEX_ID)
    L = p.read_text(encoding='utf-8').split('\n')
    hits = [i for i, l in enumerate(L)
            for m in [INDEX_TABLE_ROW.match(l)] if m and m.group(1) == rel]
    assert len(hits) == 1, f'expected exactly one table line for {rel}, found {len(hits)}'
    return p, L, hits[0]


def blank_table_role(work: Path):
    """The table still lists the file but no longer states a role — the commonest way this drifts."""
    rel = live_set_authority(work)
    p, L, i = _table_line(work, rel)
    L[i] = re.sub(r'^(\|\s*`[^`]+`\s*\|\s*)(authority|reference)(\s*\|)', r'\1(unstated)\3', L[i], count=1)
    p.write_text('\n'.join(L), encoding='utf-8')


def drop_table_line(work: Path):
    """Delete the whole table row, re-binding its owner marker elsewhere so the DECLARATION is what is gone."""
    rel = live_set_authority(work)
    p, L, i = _table_line(work, rel)
    marker = re.search(r'<!--\s*(FIDO-FCB-REF:[A-Z0-9-]+)\s*-->', L[i])
    dropped = L.pop(i)
    assert rel in dropped
    if marker:
        L.append(f'A note about `{rel}`. <!-- {marker.group(1)} -->')
    p.write_text('\n'.join(L), encoding='utf-8')


NEW_AUTHORITY_ID = 'ZZZ-SELF-TEST-NEW-AUTHORITY'
NEW_AUTHORITY_PATH = '.review/ZZZ_SELF_TEST_NEW_AUTHORITY.md'


def add_authority(work: Path, body: str, role: str = 'authority'):
    """Add a brand-new document and one manifest row for it — NO edit to this file.

    That is the whole point of the repair: corpus membership is data. The row sorts last, so canonical order
    holds, and its owner marker is bound in the document that names it."""
    (work / NEW_AUTHORITY_PATH).write_text(f'# Self-test authority\n\n{body}\n', encoding='utf-8')
    owner_id = NEXT_STEPS_ID
    owner_rel = path_of_id(work, owner_id)
    owner = work / owner_rel
    owner.write_text(owner.read_text(encoding='utf-8')
                     + f'\n- Self-test authority: `{NEW_AUTHORITY_PATH}`. '
                       f'<!-- {MARKER}:{NEW_AUTHORITY_ID} -->\n', encoding='utf-8')
    L = _rows(work)
    tail = L.pop() if L and L[-1] == '' else None
    L.append('\t'.join([NEW_AUTHORITY_ID, 'repository-file', NEW_AUTHORITY_PATH, 'present',
                        owner_rel, f'{MARKER}:{NEW_AUTHORITY_ID}', role]))
    if tail is not None:
        L.append(tail)
    _write_rows(work, L)


def dir_row(work: Path):
    for i, c in _cells(work):
        if c[1] == 'repository-directory':
            return i, c
    raise AssertionError('no repository-directory row in the fixture')


def duplicate_path_row(work: Path):
    """Two rows claiming one path: the relation stops being a function."""
    L = _rows(work)
    c = L[1].split('\t'); c[0] = 'AAA-' + c[0]; c[5] = f'{MARKER}:{c[0]}'
    _write_rows(work, [L[0], '\t'.join(c)] + L[1:])


def _first_row_with_marker(work: Path):
    for _, c in _cells(work):
        for cand in (work / c[4], work / Path(TSV_REL).parent / c[4]):
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
    for _, c in _cells(work):
        if c[1] == 'repository-file':
            p = work / c[2]
            p.rename(p.with_name(p.name + '.renamed')); return
    raise AssertionError('no repository-file row in the fixture')


def falsely_externalize(work: Path):
    """Retype ONE row, resolved once — a second lookup after the first edit finds a different row."""
    L = _rows(work)
    for i, l in enumerate(L[1:], start=1):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[1] == 'repository-file':
            c[1], c[3], c[6] = 'external-evidence', 'not-in-repository', 'reference'
            L[i] = '\t'.join(c)
            _write_rows(work, L); return
    raise AssertionError('no repository-file row in the fixture')


def symlink_target(work: Path, idx: int, cells):
    p = work / cells[2]
    body = p.read_bytes(); p.unlink()
    other = p.with_suffix(p.suffix + '.real'); other.write_bytes(body)
    p.symlink_to(other.name)


def dup_row(work: Path):
    L = _rows(work)
    _write_rows(work, L[:2] + [L[1]] + L[2:])


def trunc_row(work: Path):
    L = _rows(work)
    L[1] = L[1].rsplit('\t', 1)[0]
    _write_rows(work, L)


def swap_rows(work: Path):
    L = _rows(work)
    _write_rows(work, [L[0], L[2], L[1]] + L[3:])


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
