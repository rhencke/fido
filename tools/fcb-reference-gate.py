#!/usr/bin/env python3
"""Governance D-24 — a COMPLETE relation between the live authority corpus and its typed references.

One data authority: `.review/fcb/current/FIDO_FCB_REFERENCES.tsv` —
`id, kind, path, availability, owner, owner_anchor, corpus_role`.

The manifest owns BOTH halves of the relation AND corpus membership:

  MANIFEST -> REPOSITORY   every repository row has a CANONICAL target path that resolves to the declared
                           kind, one canonical in-repository owner, one exact owner marker bound to the exact
                           path token on one line, and one valid corpus role.
  AUTHORITY -> MANIFEST    every operational repository path named anywhere in a CURRENT AUTHORITY has
                           exactly one row, in the canonical spelling.

`corpus_role` decides membership. An `authority` is a current normative source: a present, readable, UTF-8
repository FILE whose own operational references are scanned. A `reference` resolves and is owned without
becoming one, so a generated view is a `reference` and its canonical data source carries the authority.

WHAT THIS FILE MUST NOT CONTAIN is the point of the whole design. It holds no list of repository namespaces,
no list of root files, no list of authority documents. Corpus membership comes from manifest rows; the PATH
UNIVERSE comes from the repository inventory of the exact snapshot being checked. A gate that decides which
namespaces exist cannot prove that every operational path is declared — it can only prove that the subset it
recognised is. Both defects were real, in that order.

A repository path is one canonical POSIX repository-relative spelling, and there is exactly one parser for
manifest targets, manifest owners, live-set entries, Index table cells, and paths found in authority prose. Two
spellings that resolve to one file are one path and get one row.

External evidence lives in a DISTINCT namespace (`external:`) that cannot parse as a repository path, so
retyping a missing repository file as external evidence can never make it pass.

Everything fails closed and names the exact row, document and reason.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

# The ONE hard-coded repository path: the bootstrap needed to load the manifest that owns everything else.
TSV_REL = '.review/fcb/current/FIDO_FCB_REFERENCES.tsv'
FIELDS = ('id', 'kind', 'path', 'availability', 'owner', 'owner_anchor', 'corpus_role')
MARKER = 'FIDO-FCB-REF'
EXTERNAL_PREFIX = 'external:'

# Closed vocabularies, declared once.
REPO_KINDS = ('repository-file', 'repository-directory')
OFF_TREE_KINDS = ('external-evidence', 'ephemeral')
KINDS = REPO_KINDS + OFF_TREE_KINDS
REPO_AVAILABILITY = ('present',)
OFF_TREE_AVAILABILITY = ('not-in-repository', 'r1-bundle-provenance-pending')
CORPUS_ROLES = ('authority', 'reference')

# Residue that cannot be part of a committed snapshot, so its absence from the inventory is not a subset
# choice about namespaces — it is a statement about what Git tracks.
RESIDUE_DIRS = {'.git', '_build', '__pycache__', '.fido'}
RESIDUE_SUFFIXES = ('.vo', '.vok', '.vos', '.vio', '.glob', '.pyc', '.aux', '.fido-tmp-v1')

# Characters that may appear in a repository path token. Used for BOUNDARY tests, never to decide membership.
TOKEN_CHARS = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._/-')
TOKEN = re.compile(r'[A-Za-z0-9._/-]+')

# The FIXED POINTS of the governance structure, named by MANIFEST ID — never by path. Resolving through the
# manifest means this file holds no path list and a rename moves the check with its row.
INDEX_ID = 'REVIEW-FCB-CURRENT-FIDO-FCB-INDEX-MD'
NEXT_STEPS_ID = 'REVIEW-NEXT-STEPS-MD'
REVIEW_REQUEST_ID = 'REVIEW-REVIEW-REQUEST-MD'

INDEX_TABLE_ROW = re.compile(r'^\|\s*`([^`]+)`\s*\|\s*([A-Za-z-]+)\s*\|')

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


# ───────────────────────────────────────────────────────── the one canonical repository path parser
def parse_repo_path(text: str, what: str) -> str:
    """One canonical POSIX repository-relative path, or an error naming why it is not one.

    Malformed input is REJECTED, never normalized and accepted: normalizing would let two spellings name one
    target, and target identity is what makes "exactly one row per path" mean anything."""
    if not text:
        raise ReferenceError_(f'{what}: empty repository path')
    if '\x00' in text:
        raise ReferenceError_(f'{what}: repository path contains NUL')
    if '\\' in text:
        raise ReferenceError_(f'{what}: {text!r} uses a backslash; repository paths are POSIX')
    if text.startswith('/'):
        raise ReferenceError_(f'{what}: {text!r} is absolute; repository paths are relative to the root')
    if text.startswith('./'):
        raise ReferenceError_(
            f'{what}: {text!r} is stored with a leading "./"; the canonical spelling omits it')
    # These segment rules, with the prefix rules above, ARE "the text equals its canonical spelling" for a
    # POSIX relative path: split-then-join is the identity, so once no segment is empty, `.` or `..`, and no
    # absolute or `./` prefix survives, there is nothing left for a separate normalized comparison to catch.
    # Writing one anyway would be a check that can never fire, which is worse than no check: it reads as
    # protection.
    for seg in text.split('/'):
        if seg == '':
            raise ReferenceError_(f'{what}: {text!r} has an empty path segment')
        if seg == '.':
            raise ReferenceError_(f'{what}: {text!r} has a "." segment')
        if seg == '..':
            raise ReferenceError_(f'{what}: {text!r} has a ".." segment and may leave the repository')
    return text


def resolve_in_root(root: Path, rel: str, what: str) -> Path:
    """Resolve a canonical path inside the exact review root, refusing any symlinked component."""
    base = root.resolve()
    here = root
    for seg in rel.split('/'):
        here = here / seg
        if here.is_symlink():
            raise ReferenceError_(f'{what}: {rel!r} is reached through a symlink at {seg!r}')
    try:
        here.resolve().relative_to(base)
    except ValueError:
        raise ReferenceError_(f'{what}: {rel!r} resolves outside the repository root')
    return here


def parse_external_id(text: str, what: str, root: Path, top_level: set) -> str:
    """External evidence lives in its own namespace and can never be a repository obligation in disguise."""
    if not text.startswith(EXTERNAL_PREFIX):
        raise ReferenceError_(
            f'{what}: off-tree evidence {text!r} must use the {EXTERNAL_PREFIX!r} identity form, so a missing '
            f'repository file can never be exempted from resolution by changing its kind')
    body = text[len(EXTERNAL_PREFIX):]
    if not body:
        raise ReferenceError_(f'{what}: {text!r} has an empty external identity')
    # Resolution first, because it is the specific failure: an identity that names a real repository object is
    # a repository obligation whatever it calls itself. The namespace test then catches the MISSING ones,
    # which is the escape this separation exists to close.
    try:
        rel = parse_repo_path(body, what)
    except ReferenceError_:
        return text                       # cannot even parse as a repository path: correctly external
    if (root / rel).exists():
        raise ReferenceError_(
            f'{what}: external identity {text!r} resolves inside the repository; it is a repository '
            f'reference and must be typed as one')
    head = body.split('/')[0]
    if head in top_level:
        raise ReferenceError_(
            f'{what}: external identity {text!r} begins with the repository namespace {head!r}')
    return text


# ───────────────────────────────────────────────────────── the repository inventory of the exact snapshot
def _residue(rel: str) -> bool:
    parts = rel.split('/')
    return (any(p in RESIDUE_DIRS for p in parts)
            or any(rel.endswith(s) for s in RESIDUE_SUFFIXES))


def repository_inventory(root: Path):
    """Every repository file in the exact snapshot being checked. The PATH UNIVERSE, never a Python list.

    working tree   tracked plus untracked-nonignored, straight from Git, fail-closed on any Git failure.
    snapshot       the exported tree itself, minus residue that cannot be in a committed snapshot."""
    if (root / '.git').exists():
        proc = subprocess.run(['git', 'ls-files', '--cached', '--others', '--exclude-standard'],
                              cwd=root, capture_output=True, text=True)
        if proc.returncode != 0:
            raise ReferenceError_(
                f'repository inventory: git ls-files failed (rc={proc.returncode}): {proc.stderr.strip()}')
        files = {f for f in proc.stdout.split('\n') if f and not _residue(f)}
        mode = 'working tree'
    else:
        files = set()
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in RESIDUE_DIRS]
            for name in filenames:
                rel = str(Path(dirpath, name).relative_to(root)).replace(os.sep, '/')
                if not _residue(rel):
                    files.add(rel)
        mode = 'exported snapshot'
    if not files:
        raise ReferenceError_(
            f'repository inventory ({mode}): no files found — refusing to prove a complete relation over '
            f'an empty repository')
    directories = set()
    for f in files:
        parts = f.split('/')
        for i in range(1, len(parts)):
            directories.add('/'.join(parts[:i]))
    # Two different questions. `top` is every top-level ENTRY, and answers "is this external identity really a
    # repository obligation?". `namespaces` is only the top-level DIRECTORIES, and answers "could a path with
    # this head exist?" — a root FILE is not a namespace, so `Dockerfile/hooks` is English, not a path.
    top = {f.split('/')[0] for f in files}
    namespaces = {f.split('/')[0] for f in files if '/' in f}
    return files, directories, top, namespaces, mode


# ───────────────────────────────────────────────────────── reading
def read_text(path: Path, label: str, reader=None) -> str:
    """The one read of a corpus surface. Injectable so the read-failure control is DETERMINISTIC: `chmod 000`
    is not a control on a tree that builds as root — the file stays readable and the control silently skips."""
    try:
        return (reader or _plain_read)(path)
    except FileNotFoundError:
        raise ReferenceError_(f'{label}: {path} does not exist')
    except IsADirectoryError:
        raise ReferenceError_(f'{label}: {path} is a directory')
    except UnicodeDecodeError as exc:
        raise ReferenceError_(f'{label}: {path} is not valid UTF-8 ({exc})')
    except OSError as exc:
        raise ReferenceError_(f'{label}: {path} could not be read ({exc.__class__.__name__}: {exc})')


def _plain_read(path: Path) -> str:
    return path.read_text(encoding='utf-8')


def load_rows(root: Path, top_level: set, reader=None):
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
        where = f'{TSV_REL}:{n}: {row["id"]}'
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
        if row['kind'] in REPO_KINDS:
            if row['path'].startswith(EXTERNAL_PREFIX):
                raise ReferenceError_(f'{where}: a repository row may not use the external identity form')
            row['path'] = parse_repo_path(row['path'], f'{where} target')
        else:
            row['path'] = parse_external_id(row['path'], f'{where} target', root, top_level)
        # Only a real, present repository FILE can be a current authority: a directory has no text to scan,
        # and an off-tree reference is by definition not in this ref.
        if row['corpus_role'] == 'authority' and row['kind'] != 'repository-file':
            raise ReferenceError_(
                f'{where}: kind {row["kind"]!r} may not be a current authority — only a present repository '
                f'file can be scanned as one')
        row['owner'] = parse_repo_path(row['owner'], f'{where} owner')
        rows.append(row)
    if not rows:
        raise ReferenceError_(f'{TSV_REL}: no rows')
    ordered = sorted(rows, key=lambda r: r['id'])
    if [r['id'] for r in rows] != [r['id'] for r in ordered]:
        raise ReferenceError_(f'{TSV_REL}: rows are not in canonical id order; expected '
                              + ', '.join(r['id'] for r in ordered))
    by_path = {}
    for r in rows:
        by_path.setdefault(r['path'], []).append(r)
    for path, owners in by_path.items():
        if len(owners) > 1:
            raise ReferenceError_(
                f'{TSV_REL}: path {path!r} is claimed by {len(owners)} rows '
                f'({", ".join(o["id"] for o in owners)}) — exactly one row owns a target')
    return rows


def row_by_id(rows, wanted: str, why: str):
    for r in rows:
        if r['id'] == wanted:
            return r
    raise ReferenceError_(f'{TSV_REL}: no row {wanted!r} — {why} cannot be located, so its declarations '
                          f'cannot be checked; the gate refuses to report a complete relation')


def resolve(root: Path, row: dict):
    if row['kind'] in OFF_TREE_KINDS:
        return
    where = f'{TSV_REL}:{row["line"]}: {row["id"]}'
    target = resolve_in_root(root, row['path'], where)
    if not target.exists():
        raise ReferenceError_(f'{where}: path {row["path"]!r} does not exist in this tree')
    if row['kind'] == 'repository-file' and not target.is_file():
        raise ReferenceError_(f'{where}: {row["path"]!r} is declared a file but is not one')
    if row['kind'] == 'repository-directory' and not target.is_dir():
        raise ReferenceError_(f'{where}: {row["path"]!r} is declared a directory but is not one')


def owner_path(root: Path, row: dict) -> Path:
    """One canonical regular file INSIDE the exact tree. No fallback search, no outside-root resolution."""
    where = f'{TSV_REL}:{row["line"]}: {row["id"]} owner'
    target = resolve_in_root(root, row['owner'], where)
    if not target.is_file():
        raise ReferenceError_(f'{where}: {row["owner"]!r} is not a readable regular file in this tree')
    return target


def line_binds_path(line: str, path: str) -> bool:
    """The exact canonical path as a DELIMITED token. `dune` is not proved by `dune-project`."""
    for m in re.finditer(re.escape(path), line):
        before = line[m.start() - 1] if m.start() else ''
        after = line[m.end()] if m.end() < len(line) else ''
        if before not in TOKEN_CHARS and after not in TOKEN_CHARS:
            return True
    return False


def check_owner_marker(root: Path, row: dict, reader=None):
    """EXACTLY ONE `<!-- FIDO-FCB-REF:<ID> -->` in the owner, on a line binding this row's exact path token.

    Naming an owner is not the same as owning the reference; the marker makes ownership a fact in the
    document. Binding it to the exact token, not a substring, is what stops one path standing in for another."""
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
    if not line_binds_path(hits[0], row['path']):
        raise ReferenceError_(
            f'{row["owner"]}: the marker for {row["id"]} is not on a line binding its declared path '
            f'{row["path"]!r} as an exact token — a substring of a longer path does not prove it')


# ───────────────────────────────────────────────────────── membership and discovery
def authority_rows(rows):
    """The live authority corpus IS the set of `authority` rows. No parallel list, no Python constant."""
    authorities = [r for r in rows if r['corpus_role'] == 'authority']
    if not authorities:
        raise ReferenceError_('the live authority corpus is empty — no row declares corpus_role=authority, '
                              'so there is nothing to prove complete')
    return authorities


def check_authority_readable(root: Path, row: dict, reader=None) -> str:
    where = f'{TSV_REL}:{row["line"]}: {row["id"]}'
    target = resolve_in_root(root, row['path'], where)
    if target.is_dir():
        raise ReferenceError_(f'{where}: an authority may not be a directory')
    return read_text(target, f'{row["id"]} authority document', reader)


def operational_references(text: str, inventory: set, directories: set, top_dirs: set):
    """Every operational repository reference a document makes, with the raw spelling that produced it.

    Four exact forms, all derived from the snapshot rather than from a namespace list:
      1. a token that IS an existing repository path;
      2. a token rooted at a discovered top-level directory (this finds MISSING paths);
      3. a dot-prefixed repository name carrying a directory part or an extension;
      4. the explicit root-relative `./name` form, which is how the corpus names a MISSING root path.
    A bare word is never a path. That is why rule 4 exists: without an explicit form, a missing root file
    would be indistinguishable from ordinary prose, and the rule must be exact rather than greedy."""
    found = {}
    for m in TOKEN.finditer(text):
        raw = m.group(0)
        is_dir_spelling = raw.endswith('/')
        t = raw.rstrip('/.,;:)')
        if not t:
            continue
        if raw.startswith('./'):
            t = t[2:]
            if not t:
                continue
        elif t in inventory:
            pass
        elif is_dir_spelling and t in directories:
            pass
        elif '/' in t and t.split('/')[0] in top_dirs:
            pass
        elif t.startswith('.') and ('/' in t or '.' in t[1:]):
            pass
        else:
            continue
        found.setdefault(t, raw)
    return found


def check_corpus_declared(root: Path, rows, authorities, inventory, directories, top_dirs, reader=None):
    """AUTHORITY -> MANIFEST: every operational path a current authority names has exactly one row."""
    by_path = {r['path']: r for r in rows}
    undeclared, malformed = [], []
    for row in authorities:
        text = check_authority_readable(root, row, reader)
        for token, raw in sorted(operational_references(text, inventory, directories, top_dirs).items()):
            try:
                canonical = parse_repo_path(token, f'{row["path"]} names {raw!r}')
            except ReferenceError_ as exc:
                malformed.append(str(exc))
                continue
            if canonical not in by_path:
                undeclared.append((row['path'], canonical))
    if malformed:
        raise ReferenceError_(
            f'{len(malformed)} MALFORMED operational reference(s) in the live authority corpus — a current '
            f'authority must name a canonical repository path: ' + '; '.join(malformed[:6]))
    if undeclared:
        shown = '; '.join(f'{d} names {s!r}' for d, s in undeclared[:8])
        raise ReferenceError_(
            f'{len(undeclared)} UNDECLARED operational reference(s) in the live authority corpus — every '
            f'repository path a current authority names must have a typed row in {TSV_REL}: {shown}'
            + ('' if len(undeclared) <= 8 else f' … and {len(undeclared) - 8} more'))


# ───────────────────────────────────────────────────────── the declared live set
def check_live_set_closed(root: Path, rows, reader=None) -> int:
    """`.review/fcb/current/` is FLAT and fully declared: every immediate entry is a regular non-symlink file
    with exactly one manifest row and exactly one FCB Index table line.

    A directory or symlink there is not a smaller problem than an undeclared file — it is an undeclared
    subtree, and admitting one silently would be an FCB change made by accident rather than by amendment."""
    live_rel = str(Path(TSV_REL).parent)
    live_dir = resolve_in_root(root, live_rel, 'the canonical live FCB set')
    if not live_dir.is_dir():
        raise ReferenceError_(f'{live_rel}: the canonical live FCB set is not a directory')
    declared = {r['path'] for r in rows}
    present = []
    for entry in sorted(os.scandir(live_dir), key=lambda e: e.name):
        rel = f'{live_rel}/{entry.name}'
        if entry.is_symlink():
            raise ReferenceError_(
                f'{rel}: the live FCB set contains a SYMLINK; every entry must be a regular file')
        if entry.is_dir():
            raise ReferenceError_(
                f'{rel}: the live FCB set contains a DIRECTORY; the live set is flat, and a subdirectory '
                f'needs an accepted FCB change that defines its role before it may exist')
        if not entry.is_file():
            raise ReferenceError_(f'{rel}: the live FCB set contains an entry that is not a regular file')
        present.append(rel)
    if not present:
        raise ReferenceError_(f'{live_rel}: the canonical live FCB set is empty')
    missing = [p for p in present if p not in declared]
    if missing:
        raise ReferenceError_(
            f'{len(missing)} file(s) sit in the canonical live FCB set with NO row in {TSV_REL}, so they '
            f'carry no corpus role and are never scanned: ' + ', '.join(missing))
    return len(present)


def check_index_table_roles(root: Path, rows, live_count: int, reader=None) -> int:
    """The FCB Index live-file table declares a role for every live-set file, and the manifest must agree.

    Each path appears EXACTLY ONCE. A repeated row is a duplicate whether or not its role agrees: two lines
    describing one file is two authorities describing one fact, which is the defect, not the disagreement."""
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
            continue                       # some other two-column table; only role-bearing rows declare
        if path in declared:
            raise ReferenceError_(
                f'{index_row["path"]}: the live-file table names {path!r} more than once — one file, one '
                f'row, whether or not the repeated roles agree')
        declared[path] = role

    live_rel = str(Path(TSV_REL).parent)
    expected = {r['path'] for r in rows
                if r['kind'] == 'repository-file' and str(Path(r['path']).parent) == live_rel}
    missing = sorted(expected - set(declared))
    if missing:
        raise ReferenceError_(
            f'{index_row["path"]}: the live-file table does not state a corpus role for '
            f'{len(missing)} file(s) in the live set: ' + ', '.join(missing))
    extra = sorted(set(declared) - {r['path'] for r in rows})
    if extra:
        raise ReferenceError_(
            f'{index_row["path"]}: the live-file table names {len(extra)} path(s) with no manifest row: '
            + ', '.join(extra))
    if len(declared) != live_count:
        raise ReferenceError_(
            f'{index_row["path"]}: the live-file table declares {len(declared)} path(s) but the live set '
            f'holds {live_count} file(s) — the table and the directory must be one-to-one')
    for path in sorted(declared):
        if declared[path] != by_path[path]['corpus_role']:
            raise ReferenceError_(
                f'{index_row["path"]}: the live-file table calls {path!r} a {declared[path]!r} but '
                f'{TSV_REL} declares corpus_role {by_path[path]["corpus_role"]!r} — the corpus must state '
                f'one truth about what is current authority')
    return len(declared)


def check_declaration_sites(root: Path, rows, reader=None) -> int:
    """Every structural declaration that ASSIGNS authority must point at a row that carries it."""
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
        named = parse_repo_path(hits[0].strip().strip('`'), f'{doc_row["path"]}: {what}')
        row = by_path.get(named)
        if row is None:
            raise ReferenceError_(f'{doc_row["path"]}: {what} is {named!r}, which has no row in {TSV_REL}')
        if row['corpus_role'] != 'authority':
            raise ReferenceError_(
                f'{doc_row["path"]}: {what} is {named!r}, but {TSV_REL} declares it a '
                f'{row["corpus_role"]!r} — a document that assigns current work is an authority and must be '
                f'scanned as one')
        checked += 1
    return checked


def run(root: Path, reader=None) -> str:
    inventory, directories, top_level, namespaces, mode = repository_inventory(root)
    rows = load_rows(root, top_level, reader)
    authorities = authority_rows(rows)
    for row in rows:
        resolve(root, row)
        check_owner_marker(root, row, reader)
    live = check_live_set_closed(root, rows, reader)
    declared_roles = check_index_table_roles(root, rows, live, reader)
    sites = check_declaration_sites(root, rows, reader)
    check_corpus_declared(root, rows, authorities, inventory, directories, namespaces, reader)
    repo = sum(1 for r in rows if r['kind'] in REPO_KINDS)
    return (f'{mode} inventory {len(inventory)} file(s), {len(top_level)} top-level entries, '
            f'{len(namespaces)} namespace(s); '
            f'{len(rows)} declared reference(s): {repo} in-repository, {len(rows) - repo} external; '
            f'every row canonical with one bound owner marker; live set {live} declared regular file(s) and '
            f'{declared_roles} role(s) agreeing with the FCB Index table; {sites} structural declaration(s) '
            f'point at an authority; {len(authorities)} current authority document(s) name no undeclared '
            f'operational path')


# ───────────────────────────────────────────────────────── adversarial controls
def self_test(root: Path) -> int:
    import shutil, tempfile
    failures = []
    counts = {'total': 0, 'must_fail': 0}

    def scenario(label: str, mutate, expect=None, reader=None, git=False):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with tempfile.TemporaryDirectory() as d:
            work = Path(d) / 'tree'
            shutil.copytree(root, work, symlinks=True,
                            ignore=shutil.ignore_patterns('.git', '_build', '*.vo', '*.glob'))
            try:
                if git:
                    for cmd in (['git', 'init', '-q'], ['git', 'add', '-A']):
                        p = subprocess.run(cmd, cwd=work, capture_output=True, text=True)
                        assert p.returncode == 0, f'git failed: {p.stderr.strip()}'
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

    def rows_of(work: Path):
        return (work / TSV_REL).read_text(encoding='utf-8').split('\n')

    def first_repo_row(work: Path):
        for i, l in enumerate(rows_of(work)[1:], start=1):
            c = l.split('\t')
            if len(c) == len(FIELDS) and c[1] == 'repository-file':
                return i, c
        raise AssertionError('no repository-file row in the fixture')

    def set_field(work: Path, idx: int, field: int, value: str):
        L = rows_of(work); c = L[idx].split('\t'); c[field] = value
        L[idx] = '\t'.join(c); (work / TSV_REL).write_text('\n'.join(L), encoding='utf-8')

    # ── both input modes must pass on the canonical tree, or every control below proves nothing
    scenario('canonical fixture passes (exported snapshot mode)', lambda w: w)
    scenario('canonical fixture passes (working-tree mode)', lambda w: w, git=True)

    # ── §5.1-5.5 : discovery of operational references the old path grammar could not see
    scenario('active repair names a dangling path under a dot namespace',
             lambda w: append_to(w, active_repair(w), 'See `.githooks/NO_SUCH_HOOK` for the hook.'),
             expect='UNDECLARED operational reference')
    scenario('active repair names a dangling dot-prefixed root path',
             lambda w: append_to(w, active_repair(w), 'See `.dockerignore.NO_SUCH` for the exclusions.'),
             expect='UNDECLARED operational reference')
    scenario('active repair names a dangling root path in ./ form',
             lambda w: append_to(w, active_repair(w), 'See `./NO_SUCH_ROOT.v` for the module.'),
             expect='UNDECLARED operational reference')
    scenario('authority names an existing but unmanifested root .v file',
             lambda w: (undeclare(w, 'Compilable.v'),
                        append_to(w, active_repair(w), 'Read `Compilable.v` first.')),
             expect='UNDECLARED operational reference')
    scenario('authority names an existing but unmanifested dotfile',
             lambda w: (undeclare(w, '.editorconfig'),
                        append_to(w, active_repair(w), 'Byte rules live in `.editorconfig`.')),
             expect='UNDECLARED operational reference')
    scenario('active repair names a malformed parent-traversal path',
             lambda w: append_to(w, active_repair(w), 'See `.review/../outside.md` for the annex.'),
             expect='MALFORMED operational reference')

    # ── §5.6-5.7 : owner containment
    scenario('manifest owner escapes the repository by traversal',
             lambda w: owner_escape(w),
             expect='has a ".." segment')
    scenario('manifest owner is absolute',
             lambda w: set_field(w, first_repo_row(w)[0], 4, '/etc/passwd'),
             expect='is absolute')
    scenario('manifest owner is a directory, not a file',
             lambda w: set_field(w, first_repo_row(w)[0], 4, '.review'),
             expect='is not a readable regular file')
    scenario('manifest owner reached through a symlink',
             lambda w: symlink_owner(w),
             expect='is reached through a symlink')

    # ── §5.8-5.9 : external evidence cannot absorb a repository obligation
    scenario('a missing repository path typed as external evidence',
             lambda w: externalize(w, '.review/NO_SUCH.md'),
             expect='must use the \'external:\' identity form')
    scenario('an external identity that resolves inside the repository',
             lambda w: retarget_external(w, EXTERNAL_PREFIX + 'ARCHITECTURE.md'),
             expect='resolves inside the repository')
    scenario('an external identity inside a repository namespace',
             lambda w: retarget_external(w, EXTERNAL_PREFIX + '.review/elsewhere.md'),
             expect='begins with the repository namespace')
    scenario('a repository row wearing the external identity form',
             lambda w: set_field(w, first_repo_row(w)[0], 2, EXTERNAL_PREFIX + 'thing.md'),
             expect='may not use the external identity form')

    # ── §5.10-5.12 : the live FCB set is closed
    scenario('the live FCB set contains an undeclared regular file',
             lambda w: (w / Path(TSV_REL).parent / 'FIDO_FCB_STOWAWAY.md').write_text('# x\n',
                                                                                      encoding='utf-8'),
             expect='carry no corpus role and are never scanned')
    scenario('the live FCB set contains a directory',
             lambda w: (w / Path(TSV_REL).parent / 'rogue').mkdir(),
             expect='contains a DIRECTORY')
    scenario('the live FCB set contains a symlinked directory',
             lambda w: (w / Path(TSV_REL).parent / 'rogue').symlink_to(w / '.review', True),
             expect='contains a SYMLINK')
    scenario('the live FCB set contains a symlinked file',
             lambda w: (w / Path(TSV_REL).parent / 'ALIAS.md').symlink_to(w / 'ARCHITECTURE.md'),
             expect='contains a SYMLINK')

    # ── §5.13-5.14 : one canonical target has one row
    scenario('a manifest target written as ./ARCHITECTURE.md',
             lambda w: set_field(w, first_repo_row(w)[0], 2, './ARCHITECTURE.md'),
             expect='is stored with a leading "./"')
    scenario('a manifest target with a doubled separator',
             lambda w: set_field(w, first_repo_row(w)[0], 2, 'a//b'),
             expect='has an empty path segment')
    scenario('a manifest target with a "." segment',
             lambda w: set_field(w, first_repo_row(w)[0], 2, 'a/./b'),
             expect='has a "." segment')
    scenario('a manifest target with a backslash',
             lambda w: set_field(w, first_repo_row(w)[0], 2, 'a\\b'),
             expect='uses a backslash')
    scenario('two rows resolving to the same target',
             lambda w: duplicate_path_row(w),
             expect='is claimed by 2 rows')

    # ── §5.15 : the marker binds an exact token
    scenario('an owner marker bound to dune-project instead of dune',
             lambda w: rebind_marker_to_longer_path(w),
             expect='as an exact token')

    # ── §5.16-5.17 : the FCB Index table is one-to-one
    scenario('the FCB Index repeats one live-set path with the same role',
             lambda w: repeat_table_row(w, same_role=True),
             expect='more than once')
    scenario('the FCB Index repeats one live-set path with a different role',
             lambda w: repeat_table_row(w, same_role=False),
             expect='more than once')
    scenario('the Index table role disagrees with the manifest',
             lambda w: set_role_of_path(w, live_set_authority(w), 'reference'),
             expect='the corpus must state one truth')
    scenario('a live-set file dropped from the Index table',
             lambda w: drop_table_line(w),
             expect='does not state a corpus role')
    scenario('the Index table names a path with no manifest row',
             lambda w: append_to(w, path_of_id(w, INDEX_ID),
                                 '| `.review/fcb/current/NO_SUCH_LIVE_FILE.md` | authority | x |'),
             expect='no manifest row')

    # ── §5.18-5.20 : discovery is data, and clean rows stay accepted
    scenario('a newly added authority row scans its target with no Python change',
             lambda w: add_authority(w, 'Consult `.review/NO_SUCH_NEW_TARGET.md` next.'),
             expect='UNDECLARED operational reference')
    scenario('a newly added CLEAN authority is discovered and accepted',
             lambda w: add_authority(w, 'Consult `.review/NEXT_STEPS.md` next.'))
    scenario('the same new file left as a reference is NOT scanned',
             lambda w: add_authority(w, 'Consult `.review/NO_SUCH_NEW_TARGET.md` next.', role='reference'))

    # ── structural declarations and corpus membership
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
    scenario('no row declares an authority role',
             lambda w: demote_every_row(w),
             expect='corpus is empty')
    scenario('the manifest row for NEXT_STEPS is deleted',
             lambda w: delete_row(w, NEXT_STEPS_ID),
             expect=f'no row {NEXT_STEPS_ID!r}')

    # ── manifest hygiene
    scenario('a declared path is missing',
             lambda w: (w / first_repo_row(w)[1][2]).unlink(),
             expect='does not exist in this tree')
    scenario('the manifest itself is deleted',
             lambda w: (w / TSV_REL).unlink(),
             expect='does not exist')
    scenario('a symlinked declared target',
             lambda w: symlink_target(w, *first_repo_row(w)),
             expect='is reached through a symlink')
    scenario('a file declared as a directory',
             lambda w: set_field(w, first_repo_row(w)[0], 1, 'repository-directory'),
             expect='may not be a current authority')
    scenario('a directory declared as a file',
             lambda w: set_field(w, dir_row(w)[0], 1, 'repository-file'),
             expect='declared a file but is not one')
    scenario('unknown kind',
             lambda w: set_field(w, first_repo_row(w)[0], 1, 'wishful-thinking'),
             expect='is not one of')
    scenario('unknown corpus_role',
             lambda w: set_field(w, first_repo_row(w)[0], 6, 'sort-of-binding'),
             expect='is not one of authority, reference')
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
    scenario('invalid UTF-8 in the manifest',
             lambda w: (w / TSV_REL).write_bytes((w / TSV_REL).read_bytes() + b'\xff'),
             expect='is not valid UTF-8')
    scenario('a manifest row whose owner has no marker',
             lambda w: strip_marker(w),
             expect='missing owner marker')
    scenario('a duplicate owner marker',
             lambda w: duplicate_marker(w),
             expect='occurs 2 times, expected once')
    scenario('a marker whose line does not carry its declared path',
             lambda w: unbind_marker(w),
             expect='as an exact token')
    scenario('an owner_anchor that does not match its row id',
             lambda w: set_field(w, first_repo_row(w)[0], 5, 'FIDO-FCB-REF:SOMETHING-ELSE'),
             expect='owner_anchor must be')
    scenario('an authority that cannot be decoded',
             lambda w: corrupt(w, 'REVIEW-M-SERIES-PLAN-MD'),
             expect='is not valid UTF-8')
    scenario('an authority that cannot be read', lambda w: w,
             expect='could not be read', reader=unreadable_m_series)

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


def id_of_path(work: Path, rel: str) -> str:
    for _, c in _cells(work):
        if c[2] == rel:
            return c[0]
    raise AssertionError(f'no row for path {rel} in the fixture')


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


def active_repair(work: Path) -> str:
    return declared_path(work, 'Authority:')


def live_set_authority(work: Path) -> str:
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


def undeclare(work: Path, rel: str):
    """Delete the row for an EXISTING repository file, leaving the file in place."""
    rid = id_of_path(work, rel)
    delete_row(work, rid)
    doc = work / 'CLAUDE.md'
    if doc.is_file():
        doc.write_text(doc.read_text(encoding='utf-8').replace(f'<!-- {MARKER}:{rid} -->', ''),
                       encoding='utf-8')
    for p in sorted((work / '.review').rglob('*.md')) + [work / 'ARCHITECTURE.md']:
        if p.is_file():
            t = p.read_text(encoding='utf-8')
            if f'{MARKER}:{rid} -->' in t:
                p.write_text(t.replace(f'<!-- {MARKER}:{rid} -->', ''), encoding='utf-8')


def delete_row(work: Path, wanted: str):
    _write_rows(work, [l for l in _rows(work) if l.split('\t')[0] != wanted])


def demote_every_row(work: Path):
    L = _rows(work)
    for i, l in enumerate(L):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[0] != 'id':
            c[6] = 'reference'; L[i] = '\t'.join(c)
    _write_rows(work, L)


def append_to(work: Path, target: str, line: str):
    p = work / target
    p.write_text(p.read_text(encoding='utf-8') + '\n' + line + '\n', encoding='utf-8')


def corrupt(work: Path, wanted: str):
    (work / path_of_id(work, wanted)).write_bytes(b'# x\n\xff')


def unreadable_m_series(path: Path) -> str:
    """A reader that fails for exactly one authority target, so the read-failure control is deterministic."""
    if path.name == 'M_SERIES_PLAN.md':
        raise OSError(5, 'Input/output error')
    return path.read_text(encoding='utf-8')


def owner_escape(work: Path):
    """Point an owner outside the tree AND create the file it would resolve to, so only containment can fail."""
    outside = work.parent / 'outside.md'
    L = _rows(work)
    for i, l in enumerate(L[1:], start=1):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[1] == 'repository-file':
            outside.write_text(f'A line naming {c[2]} <!-- {c[5]} -->\n', encoding='utf-8')
            c[4] = '../outside.md'
            L[i] = '\t'.join(c); _write_rows(work, L); return
    raise AssertionError('no repository-file row in the fixture')


def symlink_owner(work: Path):
    """Replace an owner file with a symlink to an identical copy: the content still satisfies every other
    check, so only root containment can reject it."""
    L = _rows(work)
    for i, l in enumerate(L[1:], start=1):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[1] == 'repository-file' and c[4] == 'CLAUDE.md':
            p = work / c[4]
            body = p.read_bytes(); p.unlink()
            real = work / 'CLAUDE.md.real'; real.write_bytes(body)
            p.symlink_to(real.name)
            return
    raise AssertionError('no CLAUDE.md-owned row in the fixture')


def externalize(work: Path, rel: str):
    """Retype ONE row as external evidence for a path that does not exist — the classic escape."""
    L = _rows(work)
    for i, l in enumerate(L[1:], start=1):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[1] == 'repository-file':
            c[1], c[2], c[3] = 'external-evidence', rel, 'not-in-repository'
            L[i] = '\t'.join(c); _write_rows(work, L); return
    raise AssertionError('no repository-file row in the fixture')


def retarget_external(work: Path, value: str):
    L = _rows(work)
    for i, l in enumerate(L[1:], start=1):
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[1] in OFF_TREE_KINDS:
            c[2] = value
            L[i] = '\t'.join(c); _write_rows(work, L); return
    raise AssertionError('no off-tree row in the fixture')


def rebind_marker_to_longer_path(work: Path):
    """Move the `dune` marker onto a line that names `dune-project` and nothing else.

    A substring check calls that proof. It is not: one file is not evidence for another whose name merely
    contains it."""
    rid = id_of_path(work, 'dune')
    owner = work / [c[4] for _, c in _cells(work) if c[0] == rid][0]
    t = owner.read_text(encoding='utf-8')
    marker = f'<!-- {MARKER}:{rid} -->'
    assert t.count(marker) == 1, f'expected one {marker} in {owner}'
    t = t.replace(f' {marker}', '', 1)
    owner.write_text(t + f'\nThe dune-project stanza pins the language version. {marker}\n', encoding='utf-8')


def repeat_table_row(work: Path, same_role: bool):
    rel = live_set_authority(work)
    p, L, i = _table_line(work, rel)
    line = L[i]
    if not same_role:
        line = re.sub(r'^(\|\s*`[^`]+`\s*\|\s*)authority(\s*\|)', r'\1reference\2', line, count=1)
    # drop the marker from the copy so the duplicate is a TABLE defect, not a marker defect
    line = re.sub(r'\s*<!--[^>]*-->', '', line)
    L.insert(i + 1, line)
    p.write_text('\n'.join(L), encoding='utf-8')


def _table_line(work: Path, rel: str):
    p = work / path_of_id(work, INDEX_ID)
    L = p.read_text(encoding='utf-8').split('\n')
    hits = [i for i, l in enumerate(L)
            for m in [INDEX_TABLE_ROW.match(l)] if m and m.group(1) == rel]
    assert len(hits) == 1, f'expected exactly one table line for {rel}, found {len(hits)}'
    return p, L, hits[0]


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


def rekey_declaration(work: Path, doc_id: str, key: str, replacement: str):
    """Remove a structural DECLARATION by changing its key, leaving the path and its owner marker in place."""
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
    p.write_text(t[:m.start()] + f'{m.group(1)}`.review/NO_SUCH_DIRECTIVE.md` (was `{m.group(2)}`)'
                 + t[m.end():], encoding='utf-8')


NEW_AUTHORITY_ID = 'ZZZ-SELF-TEST-NEW-AUTHORITY'
NEW_AUTHORITY_PATH = '.review/ZZZ_SELF_TEST_NEW_AUTHORITY.md'


def add_authority(work: Path, body: str, role: str = 'authority'):
    """Add a brand-new document and one manifest row for it — NO edit to this file.

    That is the whole point: corpus membership is data. The row sorts last, so canonical order holds, and its
    owner marker is bound in the document that names it."""
    (work / NEW_AUTHORITY_PATH).write_text(f'# Self-test authority\n\n{body}\n', encoding='utf-8')
    owner_rel = path_of_id(work, NEXT_STEPS_ID)
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
    L = _rows(work)
    c = L[1].split('\t'); c[0] = 'AAA-' + c[0]; c[5] = f'{MARKER}:{c[0]}'
    _write_rows(work, [L[0], '\t'.join(c)] + L[1:])


def _first_row_with_marker(work: Path):
    for _, c in _cells(work):
        cand = work / c[4]
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
    c, doc = _first_row_with_marker(work)
    t = doc.read_text(encoding='utf-8').replace(f' <!-- {c[5]} -->', '', 1)
    doc.write_text(t + f'\nA sentence with no path at all. <!-- {c[5]} -->\n', encoding='utf-8')


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
