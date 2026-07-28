#!/usr/bin/env python3
"""M1 source diet — the comment law, the file-disposition relation, and the measurement.

Current source states what is true now. It does not explain what used to exist, which repair introduced a
form, which candidate failed, or how a name changed. Git owns archaeology.

A DEFAULT `.v` comment is one logical block, one physical line, at most 120 characters including both
delimiters, at most one sentence, one current local fact, no archaeology. Anything longer needs one exact row
in the exception ledger, and the relation is bidirectional: a long comment without a row fails, and a row
without its exact comment fails. The goal is zero exceptions; a large ledger is evidence the diet failed even
when the parser reports green.

Adjacency matters. Comment tokens separated only by whitespace are ONE logical block, so splitting a paragraph
into a stack of one-liners does not evade the rule. Only real code separates blocks.

The comment scanner is a Rocq lexer, not a regular expression: comments nest, strings may contain comment
delimiters, and comments may contain strings. A regex would mis-slice all three and then measure its own
mistake.

Everything fails closed. An unreadable file, invalid UTF-8, an unterminated comment or string, a failed Git
enumeration, an empty scan, a ledger row with no comment, a comment with no row, a hash mismatch, an ambiguous
owner, a file missing from the disposition ledger, or a baseline whose recorded metrics no longer agree with
their own seal — each is an error naming the exact file and reason.
"""
from __future__ import annotations

import argparse
import gzip
import difflib
import hashlib
import io
import os
import re
import subprocess
import sys
import tarfile
from pathlib import Path

# ───────────────────────────────────────────────────────────── canonical data
BASELINE_REL = '.review/M1_BASELINE.tsv'
METRICS_REL = '.review/M1_METRICS.tsv'
DISPOSITION_REL = '.review/M1_FILE_DISPOSITION.tsv'
DELETIONS_REL = '.review/M1_DECLARATION_DELETIONS.tsv'
EXCEPTIONS_REL = '.review/M1_COMMENT_EXCEPTIONS.tsv'

EXCEPTION_FIELDS = ('path', 'owner_kind', 'owner_name', 'category', 'line_count', 'comment_sha256', 'reason')
DISPOSITION_FIELDS = ('path', 'baseline_bytes', 'action', 'purpose', 'owner_or_consumer', 'evidence',
                      'candidate_bytes')
DELETION_FIELDS = ('path', 'kind', 'name', 'reason', 'replacement', 'current_consumers', 'contract_search',
                   'evidence')

OWNER_KINDS = ('file-module', 'definition', 'fixpoint', 'cofixpoint', 'inductive', 'record', 'theorem',
               'lemma', 'corollary', 'example', 'instance', 'class', 'module', 'module-type', 'notation')
CATEGORIES = ('invariant-not-expressed-by-type', 'trust-or-effect-boundary', 'non-obvious-proof-plan',
              'rocq-limitation-forcing-shape')
ACTIONS = ('keep', 'delete', 'm1-created')
PURPOSES = ('certified-correctness', 'proved-restriction', 'unsupported-boundary', 'current-contract-evidence',
            'live-governance', 'generated-artifact', 'character-continuity', 'm1-enforcement')
DELETION_REASONS = ('no-current-consumer', 'strictly-superseded', 'duplicate-authority', 'compatibility-only',
                    'fixture-duplicate', 'history-only')

DECL_NAME = re.compile(
    r'^(?:Global\s+|Local\s+|Program\s+|#\[[^\]]*\]\s*)*'
    r'(?:Definition|Fixpoint|CoFixpoint|Theorem|Lemma|Corollary|Example|Record|Inductive|'
    r'Instance|Notation|Module|Class)\s+([A-Za-z_][A-Za-z0-9_\']*)', re.M)

# A documentation marker with no documentation consumer is extra syntax claiming a role nothing plays.
DOC_MARKER = re.compile(r'^\(\*\*(?!\))')
# Decoration at either end of a body: three or more rule characters whose only work is visual grouping.
BANNER_RUN = re.compile(r'(?:^\s*|\s)[-=~#*_\u2500-\u257f\u2550-\u2570\u2014\u2015]{3,}(?:\s|\s*$)')
# A label announcing what the next declaration already announces.
SECTION_LABEL = re.compile(
    r'^\s*(?:\u00a7\s*)?(?:'
    r'THEOREM|LEMMA|DEFINITION|COROLLARY|RECORD|INDUCTIVE|FIXPOINT|EXAMPLE|NOTATION|MODULE|'
    r'SOUNDNESS|COMPLETENESS|EXACTNESS|DETERMINISM|INVARIANT|CONTRACT|PILLAR|PHASE|SECTION|STEP|PART|'
    r'GOAL|CLAIM|NOTE|SUMMARY|OVERVIEW|TABLE OF CONTENTS'
    r')\b\s*[:.\u2014-]|^\s*\u00a7?\s*\d+(?:\.\d+)*\s*[:.\u2014-]\s'
    # a lettered or shouted label is the same move in different clothes: `A:`, `KEY:`, `ROUND TRIP:`
    r'|^\s*(?:[A-Z]{1,4}|[A-Z][A-Z]+(?:\s+[A-Z]+)+)\s*[:.](?:\s|$)')

# One box-drawing or star glyph is already decoration, so this needs no run length to be sure.
DECORATIVE_GLYPH = re.compile(r'[\u2500-\u257f\u2605\u2606\u25a0-\u25ff\u2022\u25cf]')

PLACEHOLDER_CELLS = {'n/a', 'na', 'tbd', 'todo', 'pending', 'unknown', 'various', 'see above',
                     '-', '--', '?', '.', 'x'}

METRIC_FIELDS = ('metric', 'baseline', 'candidate', 'delta', 'delta_percent')

MAX_COMMENT_CHARS = 120
MAX_EXCEPTION_LINES = 4

# Residue that cannot be part of a committed snapshot.
RESIDUE_DIRS = {'.git', '_build', '__pycache__', '.fido'}
RESIDUE_SUFFIXES = ('.vo', '.vok', '.vos', '.vio', '.glob', '.pyc', '.aux', '.fido-tmp-v1')

# Project archaeology. These describe the repository's own past, which Git already owns.
ARCHAEOLOGY = (
    r'repair\s+\d+', r'\bcandidate\b', r'commit\s+[0-9a-f]{7,40}', r'\bformerly\b', r'\bpreviously\b',
    r'\bused to\b', r'\brenamed\b', r'\bmigration\b', r'\blegacy\b', r'\bdeprecated\b', r'\bsuperseded\b',
    r'\bold name\b', r'\bhistorical\b', r'\bintroduced in\b', r'\bremoved in\b', r'\bretired in\b',
    r'\bbefore this change\b', r'\bafter this change\b',
)
PLACEHOLDER = (r'\bTODO\b', r'\bFIXME\b', r'\bXXX\b', r'\btemporary\b', r'\bplaceholder\b',
               r'\bcompatibility\b', r'\bfuture use\b')
ARCHAEOLOGY_RE = re.compile('|'.join(ARCHAEOLOGY), re.IGNORECASE)
PLACEHOLDER_RE = re.compile('|'.join(PLACEHOLDER), re.IGNORECASE)

DECL_KEYWORDS = (
    ('Module Type', 'module-type'), ('CoFixpoint', 'cofixpoint'), ('Definition', 'definition'),
    ('Fixpoint', 'fixpoint'), ('Inductive', 'inductive'), ('Variant', 'inductive'), ('Record', 'record'),
    ('Theorem', 'theorem'), ('Lemma', 'lemma'), ('Corollary', 'corollary'), ('Example', 'example'),
    ('Instance', 'instance'), ('Class', 'class'), ('Module', 'module'), ('Notation', 'notation'),
)
DECL_PREFIX_RE = re.compile(r'(?:Global\s+|Local\s+|Program\s+|#\[[^\]]*\]\s*)*')


class DietError(Exception):
    """Any failure to read, lex, validate, or resolve. Always names the exact file and reason."""


# ───────────────────────────────────────────────────────────── the Rocq lexer
class CommentToken:
    __slots__ = ('text', 'start', 'end', 'line')

    def __init__(self, text: str, start: int, end: int, line: int):
        self.text, self.start, self.end, self.line = text, start, end, line


def lex_comments(text: str, label: str):
    """Every comment token, with nesting and strings handled the way Rocq handles them.

    Rocq lexes string literals INSIDE comments, so `(* "*)" *)` is one comment rather than a truncated one.
    A regex scanner gets that wrong in both directions, and then every count built on it is wrong too."""
    tokens, i, n, line = [], 0, len(text), 1
    while i < n:
        ch = text[i]
        if ch == '\n':
            line += 1
            i += 1
            continue
        if text.startswith('(*', i):
            start, start_line, depth, i = i, line, 1, i + 2
            while i < n and depth:
                if text.startswith('(*', i):
                    depth += 1
                    i += 2
                elif text.startswith('*)', i):
                    depth -= 1
                    i += 2
                elif text[i] == '"':
                    i = _skip_string(text, i, label, line)
                else:
                    if text[i] == '\n':
                        line += 1
                    i += 1
            if depth:
                raise DietError(f'{label}: unterminated comment opened at line {start_line}')
            tokens.append(CommentToken(text[start:i], start, i, start_line))
            continue
        if ch == '"':
            i = _skip_string(text, i, label, line)
            continue
        i += 1
    return tokens


def _skip_string(text: str, i: int, label: str, line: int) -> int:
    """Rocq escapes a quote by doubling it."""
    n, j = len(text), i + 1
    while j < n:
        if text[j] == '"':
            if j + 1 < n and text[j + 1] == '"':
                j += 2
                continue
            return j + 1
        j += 1
    raise DietError(f'{label}: unterminated string opened at line {line}')


def logical_blocks(text: str, tokens):
    """Group comment tokens separated only by whitespace into one logical block."""
    blocks, current = [], []
    for tok in tokens:
        if current and text[current[-1].end:tok.start].strip() == '':
            current.append(tok)
        else:
            if current:
                blocks.append(current)
            current = [tok]
    if current:
        blocks.append(current)
    return blocks


def block_text(text: str, block) -> str:
    return text[block[0].start:block[-1].end]


def block_body(block) -> str:
    return ' '.join(t.text[2:-2] for t in block)


def count_sentences(body: str) -> int:
    """A `.`, `?` or `!` ends a sentence only before whitespace or the end, so `Compilable.Program` is safe."""
    count, n = 0, len(body)
    for i, ch in enumerate(body):
        if ch not in '.?!':
            continue
        j = i + 1
        while j < n and body[j] in ')]"`\'':
            j += 1
        if j >= n or body[j].isspace():
            count += 1
    return count


def owner_after(text: str, block, path: str, is_first: bool):
    """The declaration a comment belongs to, found structurally rather than by line number.

    A following declaration wins over the file module. A comment sitting directly above a declaration belongs
    to that declaration even when it is also the first thing in the file; `file-module` is for a header with
    no declaration after it, which is the only case where the file itself is the nearest owner."""
    stripped = text[block[-1].end:].lstrip()
    if stripped:
        m = DECL_PREFIX_RE.match(stripped)
        tail = stripped[m.end() if m else 0:]
        for keyword, kind in DECL_KEYWORDS:
            if tail.startswith(keyword) and (len(tail) == len(keyword) or not tail[len(keyword)].isalnum()):
                after = tail[len(keyword):].lstrip()
                name = re.match(r'"?([A-Za-z_][A-Za-z0-9_\']*)"?', after)
                return kind, (name.group(1) if name else None)
    if is_first:
        return 'file-module', Path(path).stem
    return None, None


# ───────────────────────────────────────────────────────────── inventory
def _residue(rel: str) -> bool:
    parts = rel.split('/')
    return any(p in RESIDUE_DIRS for p in parts) or any(rel.endswith(s) for s in RESIDUE_SUFFIXES)


def inventory(root: Path, snapshot: bool):
    """The exact file set of the snapshot being measured. Never a silent empty scan."""
    if not snapshot:
        if not (root / '.git').exists():
            raise DietError(f'{root} is not a Git worktree; use --snapshot for an exported tree')
        proc = subprocess.run(['git', 'ls-files', '--cached', '--others', '--exclude-standard'],
                              cwd=root, capture_output=True, text=True)
        if proc.returncode != 0:
            raise DietError(f'git ls-files failed (rc={proc.returncode}): {proc.stderr.strip()}')
        files = sorted(f for f in proc.stdout.split('\n') if f and not _residue(f)
                       and (root / f).is_file())
    else:
        found = []
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in RESIDUE_DIRS]
            for name in filenames:
                rel = str(Path(dirpath, name).relative_to(root)).replace(os.sep, '/')
                if not _residue(rel):
                    found.append(rel)
        files = sorted(found)
    if not files:
        raise DietError(f'{root}: no files found — refusing to measure or pass on nothing')
    return files


def read_v(root: Path, rel: str) -> str:
    p = root / rel
    try:
        return p.read_text(encoding='utf-8')
    except UnicodeDecodeError as exc:
        raise DietError(f'{rel}: not valid UTF-8 ({exc})')
    except OSError as exc:
        raise DietError(f'{rel}: could not be read ({exc.__class__.__name__}: {exc})')


# ───────────────────────────────────────────────────────────── ledgers
def load_tsv(root: Path, rel: str, fields, label: str, allow_missing: bool = False):
    p = root / rel
    if not p.is_file():
        if allow_missing:
            return None
        raise DietError(f'{label}: {rel} does not exist')
    try:
        text = p.read_text(encoding='utf-8')
    except UnicodeDecodeError as exc:
        raise DietError(f'{label}: {rel} is not valid UTF-8 ({exc})')
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    if not lines:
        raise DietError(f'{label}: {rel} is empty')
    if tuple(lines[0].split('\t')) != fields:
        raise DietError(f'{label}: {rel} header must be exactly {chr(9).join(fields)!r}')
    rows = []
    for n, line in enumerate(lines[1:], start=2):
        cells = line.split('\t')
        if len(cells) != len(fields):
            raise DietError(f'{label}: {rel}:{n} expected {len(fields)} fields, found {len(cells)}')
        row = dict(zip(fields, cells))
        row['line'] = str(n)
        rows.append(row)
    return rows


def check_exceptions(rows, blocks_by_file):
    """Bidirectional: every long comment has one row, every row has its exact comment."""
    seen = {}
    for r in rows:
        for k in EXCEPTION_FIELDS:
            if not r[k].strip():
                raise DietError(f'{EXCEPTIONS_REL}:{r["line"]}: field {k!r} is blank')
        if r['owner_kind'] not in OWNER_KINDS:
            raise DietError(f'{EXCEPTIONS_REL}:{r["line"]}: owner_kind {r["owner_kind"]!r} is not allowed')
        if r['category'] not in CATEGORIES:
            raise DietError(f'{EXCEPTIONS_REL}:{r["line"]}: category {r["category"]!r} is not allowed')
        key = (r['path'], r['owner_kind'], r['owner_name'])
        if key in seen:
            raise DietError(f'{EXCEPTIONS_REL}:{r["line"]}: duplicate ownership for {key}')
        seen[key] = r
    ordered = sorted(rows, key=lambda r: (r['path'], r['owner_kind'], r['owner_name']))
    if [id(r) for r in rows] != [id(r) for r in ordered]:
        raise DietError(f'{EXCEPTIONS_REL}: rows are not sorted by path, owner kind and owner name')

    matched = set()
    for rel, entries in blocks_by_file.items():
        for entry in entries:
            if entry['is_default']:
                continue
            key = (rel, entry['owner_kind'], entry['owner_name'])
            row = seen.get(key)
            if row is None:
                raise DietError(
                    f'{rel}: a comment on {entry["owner_kind"]} {entry["owner_name"]!r} is longer than one '
                    f'line or exceeds {MAX_COMMENT_CHARS} characters and has no exception row')
            if row['comment_sha256'] != entry['sha256']:
                raise DietError(
                    f'{EXCEPTIONS_REL}: the comment for {key} does not match its recorded hash — the ledger '
                    f'describes a comment that is no longer there')
            if entry['lines'] > MAX_EXCEPTION_LINES:
                raise DietError(f'{rel}: the exception on {entry["owner_name"]!r} uses {entry["lines"]} '
                                f'lines, over the {MAX_EXCEPTION_LINES}-line limit')
            if entry['over_120']:
                raise DietError(f'{rel}: the exception on {entry["owner_name"]!r} has a line over '
                                f'{MAX_COMMENT_CHARS} characters')
            if str(entry['lines']) != row['line_count']:
                raise DietError(f'{EXCEPTIONS_REL}: {key} records {row["line_count"]} line(s) but the comment '
                                f'has {entry["lines"]}')
            matched.add(key)
    orphans = sorted(set(seen) - matched)
    if orphans:
        raise DietError(f'{EXCEPTIONS_REL}: {len(orphans)} row(s) describe no current comment: '
                        + ', '.join(f'{p}:{k}:{n}' for p, k, n in orphans[:6]))
    return len(rows)


def check_disposition(rows, files):
    present = set(files)
    seen = set()
    for r in rows:
        for k in DISPOSITION_FIELDS:
            if not r[k].strip():
                raise DietError(f'{DISPOSITION_REL}:{r["line"]}: field {k!r} is blank')
        if r['action'] not in ACTIONS:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: action {r["action"]!r} is not allowed')
        if r['purpose'] not in PURPOSES and r['action'] != 'delete':
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: purpose {r["purpose"]!r} is not one of the '
                            f'allowed present purposes')
        if r['path'] in seen:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: duplicate path {r["path"]!r}')
        seen.add(r['path'])
        if r['action'] == 'delete' and r['path'] in present:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: {r["path"]!r} is recorded deleted but is still '
                            f'in the tree')
        if r['action'] in ('keep', 'm1-created') and r['path'] not in present:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: {r["path"]!r} is recorded present but is absent')
    missing = sorted(present - seen)
    if missing:
        raise DietError(f'{DISPOSITION_REL}: {len(missing)} current file(s) have no disposition row: '
                        + ', '.join(missing[:8]))
    return len(rows)


def baseline_seal(rows) -> str:
    payload = '\n'.join(f'{r["metric"]}\t{r["value"]}' for r in rows if r['metric'] != 'baseline_sha256')
    return hashlib.sha256(payload.encode('utf-8')).hexdigest()


def check_baseline(root: Path):
    rows = load_tsv(root, BASELINE_REL, ('metric', 'value'), 'M1 baseline')
    by = {r['metric']: r['value'] for r in rows}
    if 'baseline_ref' not in by:
        raise DietError(f'{BASELINE_REL}: no baseline_ref')
    if 'baseline_sha256' not in by:
        raise DietError(f'{BASELINE_REL}: no baseline_sha256 seal')
    actual = baseline_seal(rows)
    if actual != by['baseline_sha256']:
        raise DietError(f'{BASELINE_REL}: the recorded metrics no longer match their own seal — a baseline '
                        f'value changed after capture (seal {by["baseline_sha256"]}, actual {actual})')
    return by


# ───────────────────────────────────────────────────────────── scanning
def scan_v(root: Path, files):
    """Every `.v` comment block, classified. The one place comment facts are computed."""
    blocks_by_file, findings = {}, []
    for rel in [f for f in files if f.endswith('.v')]:
        text = read_v(root, rel)
        tokens = lex_comments(text, rel)
        entries = []
        first_code = text.lstrip()
        for block in logical_blocks(text, tokens):
            raw = block_text(text, block)
            body = block_body(block)
            lines = raw.count('\n') + 1
            longest = max(len(l) for l in raw.split('\n'))
            over = longest > MAX_COMMENT_CHARS
            sentences = count_sentences(body)
            is_first = text[:block[0].start].strip() == '' and bool(first_code)
            kind, name = owner_after(text, block, rel, is_first)
            is_default = lines == 1 and len(block) == 1 and not over
            entry = {
                'raw': raw, 'body': body, 'lines': lines, 'over_120': over, 'tokens': len(block),
                'sentences': sentences, 'is_default': is_default, 'line': block[0].line,
                'owner_kind': kind, 'owner_name': name,
                'sha256': hashlib.sha256(raw.encode('utf-8')).hexdigest(),
            }
            entries.append(entry)
            if not body.strip():
                findings.append(f'{rel}:{entry["line"]}: empty comment')
            hit = ARCHAEOLOGY_RE.search(body)
            if hit:
                findings.append(f'{rel}:{entry["line"]}: archaeology — {hit.group(0)!r}')
            hit = PLACEHOLDER_RE.search(body)
            if hit:
                findings.append(f'{rel}:{entry["line"]}: placeholder or compatibility prose — '
                                f'{hit.group(0)!r}')
            if is_default and sentences > 1:
                findings.append(f'{rel}:{entry["line"]}: {sentences} sentences in a default comment')
            if DOC_MARKER.search(raw):
                findings.append(f'{rel}:{entry["line"]}: a (** documentation marker with no documentation '
                                f'consumer; plain (* is the comment form')
            hit = BANNER_RUN.search(body)
            if hit:
                findings.append(f'{rel}:{entry["line"]}: decorative banner run {hit.group(0).strip()!r}')
            hit = SECTION_LABEL.search(body)
            if hit:
                findings.append(f'{rel}:{entry["line"]}: section label {hit.group(0).strip()!r} announcing '
                                f'what the declaration already announces')
            hit = DECORATIVE_GLYPH.search(body)
            if hit:
                findings.append(f'{rel}:{entry["line"]}: decorative glyph {hit.group(0)!r}')
            if not is_default and kind is None:
                findings.append(f'{rel}:{entry["line"]}: a comment needing an exception has no resolvable '
                                f'owner declaration')
            if not is_default and name is None and kind is not None:
                findings.append(f'{rel}:{entry["line"]}: ambiguous owner for an exception comment')
        blocks_by_file[rel] = entries
    return blocks_by_file, findings


# ───────────────────────────────────────────────────────────── metrics
def deterministic_archive_bytes(root: Path, files) -> int:
    """Path-sorted, fixed timestamp, fixed owner, gzip with no embedded mtime."""
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode='w') as tar:
        for rel in sorted(files):
            p = root / rel
            data = p.read_bytes()
            info = tarfile.TarInfo(name=rel)
            info.size = len(data)
            info.mtime = 0
            info.uid = info.gid = 0
            info.uname = info.gname = ''
            info.mode = 0o755 if os.access(p, os.X_OK) else 0o644
            tar.addfile(info, io.BytesIO(data))
    out = io.BytesIO()
    with gzip.GzipFile(fileobj=out, mode='wb', mtime=0) as gz:
        gz.write(raw.getvalue())
    return len(out.getvalue())


def measure(root: Path, files, blocks_by_file):
    m = {}
    sizes = {rel: (root / rel).stat().st_size for rel in files}
    m['repository_file_count'] = len(files)
    m['repository_total_bytes'] = sum(sizes.values())
    m['deterministic_compressed_archive_bytes'] = deterministic_archive_bytes(root, files)

    vs = [f for f in files if f.endswith('.v')]
    m['v_file_count'] = len(vs)
    m['v_total_bytes'] = sum(sizes[f] for f in vs)
    comment_bytes = block_count = physical = default_n = exception_n = multiline = over120 = arch = 0
    for rel in vs:
        for e in blocks_by_file[rel]:
            comment_bytes += len(e['raw'].encode('utf-8'))
            block_count += 1
            physical += e['lines']
            if e['is_default']:
                default_n += 1
            else:
                exception_n += 1
            if e['lines'] > 1 or e['tokens'] > 1:
                multiline += 1
            if e['over_120']:
                over120 += 1
            if ARCHAEOLOGY_RE.search(e['body']) or PLACEHOLDER_RE.search(e['body']):
                arch += 1
    m['v_comment_bytes'] = comment_bytes
    m['v_noncomment_bytes'] = m['v_total_bytes'] - comment_bytes
    m['v_comment_percent'] = round(100.0 * comment_bytes / m['v_total_bytes'], 2) if m['v_total_bytes'] else 0
    m['v_comment_block_count'] = block_count
    m['v_comment_physical_lines'] = physical
    m['v_default_comment_count'] = default_n
    m['v_exception_comment_count'] = exception_n
    m['v_multiline_comment_count'] = multiline
    m['v_over_120_block_count'] = over120
    m['v_archaeology_block_count'] = arch

    m['root_v_bytes'] = sum(sizes[f] for f in vs if '/' not in f)
    m['gate_v_bytes'] = sum(sizes[f] for f in vs if f.startswith('gate/'))
    m['e2e_v_bytes'] = sum(sizes[f] for f in vs if f.startswith('e2e/'))

    fcb = '.review/fcb/current/'
    m['current_fcb_bytes'] = sum(sizes[f] for f in files if f.startswith(fcb))
    m['other_review_bytes'] = sum(sizes[f] for f in files
                                  if f.startswith('.review/') and not f.startswith(fcb))
    m['root_markdown_bytes'] = sum(sizes[f] for f in files if '/' not in f and f.endswith('.md'))
    m['tool_bytes'] = sum(sizes[f] for f in files if f.startswith('tools/'))
    build = {'Makefile', 'Dockerfile', 'dune', 'dune-project', '.dockerignore', '.editorconfig', '.gitignore'}
    m['build_file_bytes'] = sum(sizes[f] for f in files if f in build or f.startswith('.githooks/'))
    m['plugin_bytes'] = sum(sizes[f] for f in files if f.startswith('plugin/'))
    m['generated_artifact_bytes'] = sum(sizes[f] for f in files if f == 'go.mod' or f.endswith('.go'))

    counts = {'rocq_definition_count': 0, 'rocq_theorem_lemma_corollary_count': 0, 'rocq_example_count': 0,
              'rocq_instance_count': 0, 'rocq_module_count': 0}
    kind_metric = {'definition': 'rocq_definition_count', 'fixpoint': 'rocq_definition_count',
                   'cofixpoint': 'rocq_definition_count',
                   'theorem': 'rocq_theorem_lemma_corollary_count',
                   'lemma': 'rocq_theorem_lemma_corollary_count',
                   'corollary': 'rocq_theorem_lemma_corollary_count',
                   'example': 'rocq_example_count', 'instance': 'rocq_instance_count',
                   'module': 'rocq_module_count', 'module-type': 'rocq_module_count'}
    for rel in vs:
        text = read_v(root, rel)
        for line in text.split('\n'):
            s = line.lstrip()
            mm = DECL_PREFIX_RE.match(s)
            tail = s[mm.end():]
            for keyword, kind in DECL_KEYWORDS:
                if tail.startswith(keyword) and (len(tail) == len(keyword)
                                                 or not tail[len(keyword)].isalnum()):
                    if kind in kind_metric:
                        counts[kind_metric[kind]] += 1
                    break
    m.update(counts)

    disp = load_tsv(root, DISPOSITION_REL, DISPOSITION_FIELDS, 'M1 file disposition', allow_missing=True)
    m['deleted_file_count'] = sum(1 for r in (disp or []) if r['action'] == 'delete')
    dels = load_tsv(root, DELETIONS_REL, DELETION_FIELDS, 'M1 declaration deletions', allow_missing=True)
    m['deleted_declaration_count'] = len(dels or [])
    return m


METRIC_ORDER = (
    'repository_file_count', 'repository_total_bytes', 'deterministic_compressed_archive_bytes',
    'v_file_count', 'v_total_bytes', 'v_comment_bytes', 'v_noncomment_bytes', 'v_comment_percent',
    'v_comment_block_count', 'v_comment_physical_lines', 'v_default_comment_count',
    'v_exception_comment_count', 'v_multiline_comment_count', 'v_over_120_block_count',
    'v_archaeology_block_count', 'root_v_bytes', 'gate_v_bytes', 'e2e_v_bytes', 'current_fcb_bytes',
    'other_review_bytes', 'root_markdown_bytes', 'tool_bytes', 'build_file_bytes', 'plugin_bytes',
    'generated_artifact_bytes', 'rocq_definition_count', 'rocq_theorem_lemma_corollary_count',
    'rocq_example_count', 'rocq_instance_count', 'rocq_module_count', 'deleted_file_count',
    'deleted_declaration_count',
)

# Metrics that must not increase from baseline before M1 may request review.
MUST_DECREASE = ('repository_total_bytes', 'v_comment_bytes', 'v_comment_physical_lines',
                 'deterministic_compressed_archive_bytes')
MUST_BE_ZERO = ('v_multiline_comment_count', 'v_over_120_block_count', 'v_archaeology_block_count')


# ───────────────────────────────────────────────────── the Rocq vernacular scanner
DECL_KEYWORDS_ORDERED = (
    'Module Type', 'CoFixpoint', 'Definition', 'Fixpoint', 'Inductive', 'Variant', 'Record',
    'Theorem', 'Lemma', 'Corollary', 'Remark', 'Fact', 'Proposition', 'Example', 'Instance',
    'Class', 'Notation', 'Module', 'Ltac', 'Let', 'Axiom', 'Parameter', 'Conjecture',
)
DECL_KIND_OF = {
    'Module Type': 'module-type', 'CoFixpoint': 'cofixpoint', 'Definition': 'definition',
    'Fixpoint': 'fixpoint', 'Inductive': 'inductive', 'Variant': 'inductive', 'Record': 'record',
    'Theorem': 'theorem', 'Lemma': 'lemma', 'Corollary': 'corollary', 'Remark': 'lemma',
    'Fact': 'lemma', 'Proposition': 'lemma', 'Example': 'example', 'Instance': 'instance',
    'Class': 'class', 'Notation': 'notation', 'Module': 'module', 'Ltac': 'ltac', 'Let': 'definition',
    'Axiom': 'axiom', 'Parameter': 'parameter', 'Conjecture': 'axiom',
}
PROOF_TERMINATORS = ('Qed.', 'Defined.', 'Admitted.', 'Abort.', 'Save.')
DECL_PREFIX = re.compile(r"^(?:Global\s+|Local\s+|Program\s+|Private\s+|#\[[^\]]*\]\s*)*")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def strip_comments(text: str, label: str) -> str:
    """Every comment span replaced by ONE space, so removal never fuses two tokens into one."""
    out, last = [], 0
    for tok in lex_comments(text, label):
        out.append(text[last:tok.start])
        out.append(' ')
        last = tok.end
    out.append(text[last:])
    return ''.join(out)


def vernac_commands(text: str, label: str):
    """Split comment-free Rocq into top-level commands.

    A `.` ends a command only before whitespace or the end, so a qualified name such as `Compilable.Program`
    and a decimal literal both stay inside their command.  Strings are skipped whole."""
    cmds, i, n, start = [], 0, len(text), 0
    while i < n:
        ch = text[i]
        if ch == '"':
            i = _skip_string(text, i, label, 0)
            continue
        if ch == '.' and (i + 1 >= n or text[i + 1].isspace()):
            piece = text[start:i + 1].strip()
            if piece:
                cmds.append(' '.join(piece.split()))
            start = i + 1
        i += 1
    tail = text[start:].strip()
    if tail:
        cmds.append(' '.join(tail.split()))
    return cmds


def command_declaration(cmd: str):
    """The (kind, name) a command declares, or None when it declares nothing."""
    body = DECL_PREFIX.sub('', cmd, count=1)
    for kw in DECL_KEYWORDS_ORDERED:
        if body.startswith(kw) and (len(body) == len(kw) or not body[len(kw)].isalnum()):
            rest = body[len(kw):].lstrip()
            m = IDENT.match(rest)
            if not m:
                return None
            return DECL_KIND_OF[kw], m.group(0)
    return None


def declaration_blocks(text: str, label: str):
    """Every top-level unit of a comment-free file, as (kind, name, [commands]).

    A proof-bearing declaration absorbs the commands after it up to and including its terminator, so a whole
    theorem is one unit and a tactic inside it is part of that unit rather than a free-standing command.
    A non-declaration command is its own unit with kind None."""
    cmds = vernac_commands(text, label)
    units, i = [], 0
    while i < len(cmds):
        decl = command_declaration(cmds[i])
        if decl is None:
            units.append((None, None, [cmds[i]]))
            i += 1
            continue
        group, j = [cmds[i]], i + 1
        while j < len(cmds):
            if command_declaration(cmds[j]) is not None:
                break
            group.append(cmds[j])
            if cmds[j] in PROOF_TERMINATORS:
                j += 1
                break
            j += 1
        units.append((decl[0], decl[1], group))
        i = j
    return units


def check_declaration_ledger(rows, baseline_units, candidate_units):
    """Every deletion row names one exact baseline declaration that is absent from the candidate.

    `baseline_units`/`candidate_units` map a path to its declaration units.  A row is checked field by field,
    because a row whose name happens to match can still carry the wrong path, kind, reason or replacement."""
    seen = set()
    for r in rows:
        for k in DELETION_FIELDS:
            if not r[k].strip():
                raise DietError(f'{DELETIONS_REL}:{r["line"]}: field {k!r} is blank')
        key = (r['path'], r['kind'], r['name'])
        if key in seen:
            raise DietError(f'{DELETIONS_REL}:{r["line"]}: duplicate row for {key}')
        seen.add(key)
        if r['reason'] not in DELETION_REASONS:
            raise DietError(f'{DELETIONS_REL}:{r["line"]}: reason {r["reason"]!r} is not one of the '
                            f'allowed deletion reasons')
        if r['path'] not in baseline_units:
            raise DietError(f'{DELETIONS_REL}:{r["line"]}: path {r["path"]!r} is not a baseline .v file')
        hits = [u for u in baseline_units[r['path']] if u[1] == r['name']]
        if len(hits) != 1:
            raise DietError(f'{DELETIONS_REL}:{r["line"]}: {r["name"]!r} is declared {len(hits)} time(s) in '
                            f'the baseline {r["path"]}, expected exactly one')
        if hits[0][0] != r['kind']:
            raise DietError(f'{DELETIONS_REL}:{r["line"]}: {r["name"]!r} is a {hits[0][0]!r} in the baseline '
                            f'{r["path"]}, not a {r["kind"]!r}')
        still = [u for u in candidate_units.get(r['path'], []) if u[1] == r['name']]
        if still:
            raise DietError(f'{DELETIONS_REL}:{r["line"]}: {r["name"]!r} is recorded deleted but still '
                            f'declared in {r["path"]}')
        if r['reason'] == 'no-current-consumer':
            if not r['replacement'].strip().lower().startswith('none'):
                raise DietError(f'{DELETIONS_REL}:{r["line"]}: a no-current-consumer row must record no '
                                f'replacement, found {r["replacement"]!r}')
        if r['reason'] == 'strictly-superseded':
            named = r['replacement'].strip()
            everywhere = [u for us in candidate_units.values() for u in us if u[1] == named]
            if not everywhere:
                raise DietError(f'{DELETIONS_REL}:{r["line"]}: strictly-superseded names replacement '
                                f'{named!r}, which no candidate .v file declares')
        for k in ('current_consumers', 'contract_search', 'evidence'):
            cell = r[k].strip()
            if cell.lower() in PLACEHOLDER_CELLS:
                raise DietError(f'{DELETIONS_REL}:{r["line"]}: field {k!r} is the placeholder '
                                f'{cell!r} rather than a stated finding')
            if k == 'current_consumers':
                # `none` is the finding a consumer search can legitimately return; the other two fields
                # describe HOW it was searched and what was observed, so neither can be that word.
                if cell.lower() != 'none' and len(cell) < 8:
                    raise DietError(f'{DELETIONS_REL}:{r["line"]}: consumers {cell!r} states neither `none` '
                                    f'nor a consumer')
            elif cell.lower() == 'none':
                raise DietError(f'{DELETIONS_REL}:{r["line"]}: field {k!r} is `none`, which describes no '
                                f'search and no observation')
    return len(rows)


def units_of_tree(root: Path, files):
    """Declaration units for every .v file of a tree, keyed by path."""
    out = {}
    for rel in sorted(f for f in files if f.endswith('.v')):
        out[rel] = declaration_blocks(strip_comments(read_v(root, rel), rel), rel)
    return out


def check_code_exact(base_root: Path, base_files, cand_root: Path, cand_files, ledger_rows):
    """The only Rocq code difference is the complete removal of exactly the ledgered baseline declarations.

    Removing whole declarations is permitted; editing one that survives is not.  Comparing the remaining
    COMMAND streams rather than a token multiset is what makes a deleted tactic inside a surviving proof
    fail, which a set-of-vanished-names check cannot see."""
    base_v = {f for f in base_files if f.endswith('.v')}
    cand_v = {f for f in cand_files if f.endswith('.v')}
    if not base_v:
        raise DietError('the baseline tree holds no .v files — refusing to report code identity over nothing')
    added = sorted(cand_v - base_v)
    if added:
        raise DietError(f'{len(added)} new .v file(s) since the baseline: {added[:6]} — a comment diet adds none')
    gone = sorted(base_v - cand_v)
    if gone:
        raise DietError(f'{len(gone)} .v file(s) removed since the baseline: {gone[:6]} — deleting a whole '
                        f'certified module is not a source-diet change')
    base_units = units_of_tree(base_root, base_v)
    cand_units = units_of_tree(cand_root, cand_v)
    n_rows = check_declaration_ledger(ledger_rows, base_units, cand_units)

    by_path = {}
    for r in ledger_rows:
        by_path.setdefault(r['path'], set()).add((r['kind'], r['name']))
    removed = 0
    for rel in sorted(base_v):
        drop = by_path.get(rel, set())
        kept = [u for u in base_units[rel] if (u[0], u[1]) not in drop]
        removed += len(base_units[rel]) - len(kept)
        expect = [c for u in kept for c in u[2]]
        actual = [c for u in cand_units[rel] for c in u[2]]
        if expect == actual:
            continue
        for k, (a, b) in enumerate(zip(expect, actual)):
            if a != b:
                raise DietError(f'{rel}: command {k + 1} differs after removing the ledgered declarations — '
                                f'baseline {a[:90]!r} versus candidate {b[:90]!r}')
        raise DietError(f'{rel}: {len(expect)} command(s) expected after removing the ledgered declarations, '
                        f'{len(actual)} found — a declaration was partially removed or partially added')
    return (f'{len(base_v)} .v file(s): every surviving declaration identical, '
            f'{removed} complete ledgered removal(s)')


# ───────────────────────────────────────────── exact-ref evidence
def export_tree(root: Path, ref: str, dest: Path):
    """The exact Git tree at [ref], on disk, with no working-tree influence."""
    dest.mkdir(parents=True, exist_ok=True)
    ar = subprocess.run(['git', 'archive', '--format=tar', ref], cwd=root, capture_output=True)
    if ar.returncode != 0:
        raise DietError(f'cannot export {ref}: {ar.stderr.decode("utf-8", "replace").strip()}')
    ex = subprocess.run(['tar', '-x', '-C', str(dest)], input=ar.stdout, capture_output=True)
    if ex.returncode != 0:
        raise DietError(f'cannot unpack {ref}: {ex.stderr.decode("utf-8", "replace").strip()}')
    return dest


def tree_sizes(root: Path, files):
    return {rel: (root / rel).stat().st_size for rel in files}


def check_disposition_exact(base_sizes, cand_sizes, rows):
    """The disposition relation over two EXACT trees: every path, every action, every byte count.

    The ledger contains its own row, so its recorded size is a fixed point of writing it; the generator
    iterates to that fixed point and this proves the fixed point was reached rather than asserted."""
    if not rows:
        raise DietError(f'{DISPOSITION_REL}: no rows — refusing to report a disposition over nothing')
    seen, bad = set(), []
    for r in rows:
        for k in DISPOSITION_FIELDS:
            if not r[k].strip():
                raise DietError(f'{DISPOSITION_REL}:{r["line"]}: field {k!r} is blank')
        if r['action'] not in ACTIONS:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: action {r["action"]!r} is not allowed')
        if r['action'] != 'delete' and r['purpose'] not in PURPOSES:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: purpose {r["purpose"]!r} is not one of the '
                            f'allowed present purposes')
        for k in ('owner_or_consumer', 'evidence'):
            if r[k].strip().lower() in PLACEHOLDER_CELLS:
                raise DietError(f'{DISPOSITION_REL}:{r["line"]}: field {k!r} is the placeholder '
                                f'{r[k].strip()!r} rather than a stated consumer')
        p = r['path']
        if p in seen:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: duplicate path {p!r}')
        seen.add(p)
        try:
            b, c = int(r['baseline_bytes']), int(r['candidate_bytes'])
        except ValueError:
            raise DietError(f'{DISPOSITION_REL}:{r["line"]}: byte fields must be integers')
        in_b, in_c = p in base_sizes, p in cand_sizes
        want = {'keep': (in_b and in_c), 'delete': (in_b and not in_c),
                'm1-created': (in_c and not in_b)}[r['action']]
        if not want:
            bad.append(f'{p}: {r["action"]}, but present in baseline={in_b} candidate={in_c}')
        if want:
            wb = base_sizes[p] if in_b else 0
            wc = cand_sizes[p] if in_c else 0
            if b != wb or c != wc:
                bad.append(f'{p}: {r["action"]} records {b}/{c} bytes, the trees hold {wb}/{wc}')
    union = set(base_sizes) | set(cand_sizes)
    missing, phantom = sorted(union - seen), sorted(seen - union)
    if missing:
        bad.append(f'{len(missing)} file(s) of the two trees have no row: {missing[:6]}')
    if phantom:
        bad.append(f'{len(phantom)} row(s) name a path in neither tree: {phantom[:6]}')
    if bad:
        raise DietError(f'{DISPOSITION_REL}: {len(bad)} disposition defect(s): ' + '; '.join(bad[:6]))
    return len(rows)


def metric_rows(base_m, cand_m):
    """The exact metric table both sides must agree on, computed once here and never transcribed."""
    out = []
    for k in METRIC_ORDER:
        b, c = float(base_m[k]), float(cand_m[k])
        d = c - b
        pct = (d / b * 100.0) if b else 0.0
        if k == 'v_comment_percent':
            out.append((k, f'{b:.2f}', f'{c:.2f}', f'{d:+.2f}', f'{pct:+.2f}'))
        else:
            out.append((k, str(int(b)), str(int(c)), f'{int(d):+d}', f'{pct:+.2f}'))
    return out


def check_metrics_exact(rows, base_m, cand_m):
    """`M1_METRICS.tsv` must EQUAL recomputation — every value, delta, percentage, row and row order."""
    want = metric_rows(base_m, cand_m)
    if len(rows) != len(want):
        raise DietError(f'{METRICS_REL}: {len(rows)} row(s), recomputation gives {len(want)}')
    for i, (r, w) in enumerate(zip(rows, want), start=2):
        got = (r['metric'], r['baseline'], r['candidate'], r['delta'], r['delta_percent'])
        if got != w:
            raise DietError(f'{METRICS_REL}:{i}: recorded {got}, recomputation gives {w}')
    return len(rows)


def verify_m1_evidence(root: Path, baseline_ref: str, candidate_ref: str):
    """The one exit check: every M1 evidence artifact, against the two exact Git refs it describes."""
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        base = export_tree(root, baseline_ref, Path(tmp) / 'baseline')
        cand = export_tree(root, candidate_ref, Path(tmp) / 'candidate')
        base_files, cand_files = inventory(base, snapshot=True), inventory(cand, snapshot=True)
        base_sizes, cand_sizes = tree_sizes(base, base_files), tree_sizes(cand, cand_files)

        sealed = check_baseline(cand)
        if sealed['baseline_ref'] != baseline_ref:
            raise DietError(f'{BASELINE_REL} seals ref {sealed["baseline_ref"]}, not {baseline_ref}')
        base_blocks, _ = scan_v(base, base_files)
        cand_blocks, findings = scan_v(cand, cand_files)
        if findings:
            raise DietError(f'the candidate tree breaks the comment law in {len(findings)} place(s): '
                            + '; '.join(findings[:6]))
        base_m, cand_m = measure(base, base_files, base_blocks), measure(cand, cand_files, cand_blocks)
        for k, v in sealed.items():
            if k in ('baseline_ref', 'baseline_sha256'):
                continue
            if str(base_m[k]) != v:
                raise DietError(f'{BASELINE_REL}: {k} records {v}, the baseline tree measures {base_m[k]}')

        # the metrics describe the candidate but are added by the later documentation-only freeze,
        # so they are read from the repository while both measurements come from the exact trees
        n_met = check_metrics_exact(load_tsv(root, METRICS_REL, METRIC_FIELDS, 'M1 metrics'),
                                    base_m, cand_m)
        n_dis = check_disposition_exact(base_sizes, cand_sizes,
                                        load_tsv(cand, DISPOSITION_REL, DISPOSITION_FIELDS, 'M1 disposition'))
        dels = load_tsv(cand, DELETIONS_REL, DELETION_FIELDS, 'M1 declaration deletions', allow_missing=True)
        code = check_code_exact(base, base_files, cand, cand_files, dels or [])
        bad = [k for k in MUST_DECREASE if float(cand_m[k]) >= float(base_m[k])]
        bad += [f'{k} is {cand_m[k]}' for k in MUST_BE_ZERO if float(cand_m[k]) != 0]
        if bad:
            raise DietError('required direction not met: ' + '; '.join(map(str, bad)))
    return (f'baseline {baseline_ref[:7]} -> candidate {candidate_ref[:7]}: baseline seal and every sealed '
            f'metric reproduce; {n_met} metric row(s) equal recomputation; {n_dis} disposition row(s) exact '
            f'in both trees; {code}; every required metric moved the right way')


# ───────────────────────────────────────────────────────────── modes

def write_disposition(root: Path, baseline_ref: str):
    """Rewrite the mechanical disposition fields from two exact trees, keeping every recorded judgement.

    The ledger contains its own row, so writing it changes the size it must record.  The loop runs to that
    fixed point and fails rather than shipping a row that was true one write ago."""
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        base = export_tree(root, baseline_ref, Path(tmp) / 'baseline')
        base_sizes = tree_sizes(base, inventory(base, snapshot=True))
    old = {r['path']: r for r in
           (load_tsv(root, DISPOSITION_REL, DISPOSITION_FIELDS, 'M1 disposition', allow_missing=True) or [])}
    target = root / DISPOSITION_REL
    for _ in range(12):
        cand_sizes = tree_sizes(root, inventory(root, snapshot=False))
        rows, missing = [], []
        for path in sorted(set(base_sizes) | set(cand_sizes)):
            in_b, in_c = path in base_sizes, path in cand_sizes
            action = 'keep' if (in_b and in_c) else ('delete' if in_b else 'm1-created')
            prev = old.get(path)
            if prev is None:
                missing.append(path)
                continue
            rows.append((path, str(base_sizes[path]) if in_b else '0', action, prev['purpose'],
                         prev['owner_or_consumer'], prev['evidence'],
                         str(cand_sizes[path]) if in_c else '0'))
        if missing:
            raise DietError(f'{DISPOSITION_REL}: {len(missing)} path(s) have no recorded purpose, and a '
                            f'purpose is a judgement this tool will not invent: {missing[:6]}')
        body = '\t'.join(DISPOSITION_FIELDS) + '\n' + '\n'.join('\t'.join(r) for r in rows) + '\n'
        if target.exists() and target.read_text(encoding='utf-8') == body:
            return len(rows)
        target.write_text(body, encoding='utf-8')
    raise DietError(f'{DISPOSITION_REL}: no byte fixed point after 12 writes')


def check_code_against_ref(root: Path, ref: str):
    """The exact declaration comparison between an exported [ref] and the working tree."""
    import tempfile
    if ref == 'baseline':
        ref = check_baseline(root)['baseline_ref']
    with tempfile.TemporaryDirectory() as tmp:
        base = export_tree(root, ref, Path(tmp) / 'baseline')
        base_files = inventory(base, snapshot=True)
        cand_files = inventory(root, snapshot=False)
        dels = load_tsv(root, DELETIONS_REL, DELETION_FIELDS, 'M1 declaration deletions', allow_missing=True)
        return f'{ref[:7]}: ' + check_code_exact(base, base_files, root, cand_files, dels or [])


def check_direction(root: Path, snapshot: bool):
    """The required metrics must move the right way before M1 may request review (contract section 8)."""
    base = check_baseline(root)
    now = run_measure(root, snapshot, None)
    bad = []
    for k in MUST_DECREASE:
        if k not in base:
            raise DietError(f'{BASELINE_REL}: no baseline value for {k}')
        if float(now[k]) >= float(base[k]):
            bad.append(f'{k} must decrease: baseline {base[k]}, candidate {now[k]}')
    for k in MUST_BE_ZERO:
        if float(now[k]) != 0:
            bad.append(f'{k} must be zero, is {now[k]}')
    if bad:
        raise DietError('required direction not met: ' + '; '.join(bad))
    return len(MUST_DECREASE) + len(MUST_BE_ZERO)


def run_check(root: Path, snapshot: bool):
    files = inventory(root, snapshot)
    blocks_by_file, findings = scan_v(root, files)
    if not blocks_by_file:
        raise DietError(f'{root}: no .v files found — refusing to report a clean diet over nothing')
    if findings:
        raise DietError(f'{len(findings)} comment-law violation(s): ' + '; '.join(findings[:10])
                        + ('' if len(findings) <= 10 else f' … and {len(findings) - 10} more'))
    ex_rows = load_tsv(root, EXCEPTIONS_REL, EXCEPTION_FIELDS, 'M1 comment exceptions')
    n_ex = check_exceptions(ex_rows, blocks_by_file)
    disp = load_tsv(root, DISPOSITION_REL, DISPOSITION_FIELDS, 'M1 file disposition', allow_missing=True)
    n_disp = check_disposition(disp, files) if disp is not None else 0
    if (root / BASELINE_REL).is_file():
        check_baseline(root)
    n_blocks = sum(len(v) for v in blocks_by_file.values())
    return (f'{len(files)} file(s), {len(blocks_by_file)} .v file(s), {n_blocks} comment block(s) all obeying '
            f'the one-line 120-character one-sentence current-fact law; {n_ex} ledgered exception(s) matched '
            f'both ways; {n_disp} file disposition(s)')


def run_measure(root: Path, snapshot: bool, out: Path | None, baseline_ref: str | None = None):
    """Measure, and optionally write a sealed metric file. The ref row is written HERE, under the same seal.

    A baseline whose ref was pasted in afterwards is a baseline whose seal never covered its own identity."""
    files = inventory(root, snapshot)
    blocks_by_file, _ = scan_v(root, files)
    m = measure(root, files, blocks_by_file)
    if out:
        pairs = ([('baseline_ref', baseline_ref)] if baseline_ref else []) + \
                [(k, str(m[k])) for k in METRIC_ORDER]
        seal = baseline_seal([{'metric': k, 'value': v} for k, v in pairs])
        body = 'metric\tvalue\n' + ''.join(f'{k}\t{v}\n' for k, v in pairs)
        out.write_text(body + f'baseline_sha256\t{seal}\n', encoding='utf-8')
    return m


def print_measure(m):
    for k in METRIC_ORDER:
        print(f'{k}\t{m[k]}')


# ───────────────────────────────────────────────────────────── controls
CLEAN_V = '(* the one integer authority *)\nDefinition kind := 0.\n'


def self_test() -> int:
    import tempfile
    failures, counts = [], {'total': 0, 'must_fail': 0}

    def fixture(d: Path, v_text: str, exceptions: str | None = None, extra=None):
        (d / 'Root.v').write_text(v_text, encoding='utf-8')
        (d / '.review').mkdir(parents=True, exist_ok=True)
        (d / EXCEPTIONS_REL).write_text(
            '\t'.join(EXCEPTION_FIELDS) + '\n' + (exceptions or ''), encoding='utf-8')
        for rel, body in (extra or {}).items():
            p = d / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(body, encoding='utf-8')
        return d

    def scenario(label, build, expect=None, snapshot=True):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            try:
                build(d)
            except Exception as exc:
                failures.append(f'{label}: could not construct the scenario ({exc})'); return
            try:
                run_check(d, snapshot=snapshot)
                if expect is not None:
                    failures.append(f'{label}: expected failure containing {expect!r}, but the check passed')
            except DietError as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')

    def scenario_run(label, build, action, expect=None):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            try:
                build(d)
            except Exception as exc:
                failures.append(f'{label}: could not construct the scenario ({exc})'); return
            try:
                action(d)
                if expect is not None:
                    failures.append(f'{label}: expected failure containing {expect!r}, but the check passed')
            except DietError as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')

    long_line = '(* ' + 'x' * 130 + ' *)\n'
    # ── must fail: the default comment law
    scenario('a two-line default comment',
             lambda d: fixture(d, '(* first line\n   second line *)\nDefinition k := 0.\n'),
             expect='has no exception row')
    scenario('a 121-character comment',
             lambda d: fixture(d, long_line + 'Definition k := 0.\n'),
             expect='has no exception row')
    scenario('two adjacent one-line comments',
             lambda d: fixture(d, '(* one *)\n(* two *)\nDefinition k := 0.\n'),
             expect='has no exception row')
    scenario('two comments on one line separated only by whitespace',
             lambda d: fixture(d, '(* one *)  (* two *)\nDefinition k := 0.\n'),
             expect='has no exception row')
    scenario('two sentences in one comment',
             lambda d: fixture(d, '(* One fact. Another fact. *)\nDefinition k := 0.\n'),
             expect='2 sentences in a default comment')
    scenario('repair archaeology',
             lambda d: fixture(d, '(* kept for repair 19 *)\nDefinition k := 0.\n'),
             expect='archaeology')
    scenario('a documentation marker comment',
             lambda d: fixture(d, '(** the one integer authority *)\nDefinition k := 0.\n'),
             expect='documentation marker')
    scenario('a decorative banner',
             lambda d: fixture(d, '(* ---- the integer section ---- *)\nDefinition k := 0.\n'),
             expect='decorative banner')
    scenario('a section label',
             lambda d: fixture(d, '(* THEOREM: the endpoints are representable. *)\nDefinition k := 0.\n'),
             expect='section label')
    scenario('a lettered label',
             lambda d: fixture(d, '(* A: the first field. *)\nDefinition k := 0.\n'),
             expect='section label')
    scenario('a shouted multi-word label',
             lambda d: fixture(d, '(* ROUND TRIP: the decoder inverts the encoder. *)\nDefinition k := 0.\n'),
             expect='section label')
    scenario('a two-character box-drawing banner',
             lambda d: fixture(d, '(* \u2500\u2500 the retained core \u2500\u2500 *)\nDefinition k := 0.\n'),
             expect='decorative glyph')
    scenario('a star decoration',
             lambda d: fixture(d, '(* \u2605 the exact round trip. *)\nDefinition k := 0.\n'),
             expect='decorative glyph')
    scenario('a TODO',
             lambda d: fixture(d, '(* TODO tighten this *)\nDefinition k := 0.\n'),
             expect='placeholder')
    scenario('an empty comment',
             lambda d: fixture(d, '(*  *)\nDefinition k := 0.\n'),
             expect='empty comment')
    # ── must fail: the exception relation
    scenario('an unledgered exception',
             lambda d: fixture(d, '(* line one\n   line two *)\nDefinition k := 0.\n'),
             expect='has no exception row')
    scenario('an orphan ledger row',
             lambda d: fixture(d, CLEAN_V, 'Root.v\tdefinition\tghost\ttrust-or-effect-boundary\t2\t'
                                           + '0' * 64 + '\tno such comment\n'),
             expect='describe no current comment')
    scenario('a changed comment hash',
             lambda d: fixture(d, '(* line one\n   line two *)\nDefinition k := 0.\n',
                               'Root.v\tdefinition\tk\ttrust-or-effect-boundary\t2\t' + '0' * 64
                               + '\tstale hash\n'),
             expect='no longer there')
    scenario('a missing owner',
             lambda d: fixture(d, 'Definition k := 0.\n(* trailing block\n   with no owner after it *)\n'),
             expect='no resolvable owner')
    scenario('duplicate exception rows', lambda d: dup_rows(d, fixture),
             expect='duplicate ownership')
    scenario('an exception over four lines', lambda d: over_four(d, fixture),
             expect='over the 4-line limit')
    scenario('an exception line over 120 characters', lambda d: over_120_exception(d, fixture),
             expect='over 120 characters')
    scenario('an unknown category',
             lambda d: fixture(d, '(* line one\n   line two *)\nDefinition k := 0.\n',
                               'Root.v\tdefinition\tk\twishful-thinking\t2\t' + '0' * 64 + '\tbad\n'),
             expect='is not allowed')
    # ── must fail: lexer and enumeration
    scenario('invalid UTF-8 in a .v file', lambda d: bad_utf8(d, fixture), expect='not valid UTF-8')
    scenario('an unterminated nested comment',
             lambda d: fixture(d, '(* outer (* inner *)\nDefinition k := 0.\n'),
             expect='unterminated comment')
    scenario('an unterminated string',
             lambda d: fixture(d, 'Definition s := "oops.\n'), expect='unterminated string')
    scenario('a snapshot containing no .v files', lambda d: no_v_files(d, fixture),
             expect='no .v files found')
    scenario('working-tree mode outside Git', lambda d: fixture(d, CLEAN_V),
             expect='is not a Git worktree', snapshot=False)
    # ── must fail: the ledgers
    scenario('a baseline metric changed after capture', lambda d: tampered_baseline(d, fixture),
             expect='no longer match their own seal')
    scenario('a current file absent from the file-disposition ledger',
             lambda d: disposition(d, fixture, omit=True), expect='have no disposition row')
    scenario('a deleted file still present', lambda d: disposition(d, fixture, phantom_delete=True),
             expect='is still')
    scenario('an M1-created file with no purpose', lambda d: disposition(d, fixture, bad_purpose=True),
             expect='allowed present purposes')
    # ── must accept
    scenario('a terse one-line comment', lambda d: fixture(d, CLEAN_V))
    scenario('a qualified Rocq name containing a period',
             lambda d: fixture(d, '(* resolves through Compilable.Program only *)\nDefinition k := 0.\n'))
    scenario('comment delimiters inside a string',
             lambda d: fixture(d, 'Definition s := "(* not a comment *)".\n'))
    scenario('a nested one-line comment',
             lambda d: fixture(d, '(* outer (* inner *) tail *)\nDefinition k := 0.\n'))
    scenario('one valid ledgered exception', lambda d: valid_exception(d, fixture))
    scenario('a clean exported-snapshot fixture', lambda d: fixture(d, CLEAN_V))
    scenario('a clean working-tree fixture', lambda d: git_fixture(d, fixture), snapshot=False)

    # ── the required direction (contract section 8)
    scenario_run('a required metric that increased from baseline',
                 lambda d: direction_fixture(d, fixture, bump='v_comment_bytes'),
                 lambda d: check_direction(d, snapshot=True), expect='must decrease')
    scenario_run('a required count that is not zero',
                 lambda d: direction_fixture(d, fixture, archaeology=True),
                 lambda d: check_direction(d, snapshot=True), expect='must be zero')
    scenario_run('a baseline whose metrics moved the right way',
                 lambda d: direction_fixture(d, fixture),
                 lambda d: check_direction(d, snapshot=True))

    # ── surviving-code identity, over two exact trees (contract sections 3.5.A and 11)
    def trees(label, mutate, ledger=(), expect=None):
        """Build a baseline and a candidate tree, mutate the candidate, and run the exact comparison."""
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        with tempfile.TemporaryDirectory() as tmp:
            b, c = Path(tmp) / 'b', Path(tmp) / 'c'
            try:
                for d in (b, c):
                    (d / '.review').mkdir(parents=True)
                    (d / 'Root.v').write_text(BASE_V, encoding='utf-8')
                    (d / DELETIONS_REL).write_text('\t'.join(DELETION_FIELDS) + '\n', encoding='utf-8')
                mutate(c)
                if ledger:
                    (c / DELETIONS_REL).write_text(
                        '\t'.join(DELETION_FIELDS) + '\n' + ''.join('\t'.join(r) + '\n' for r in ledger),
                        encoding='utf-8')
                rows = load_tsv(c, DELETIONS_REL, DELETION_FIELDS, 'deletions', allow_missing=True) or []
                bf, cf = inventory(b, snapshot=True), inventory(c, snapshot=True)
            except Exception as exc:
                failures.append(f'{label}: could not construct the scenario ({exc})'); return
            try:
                check_code_exact(b, bf, c, cf, rows)
                if expect is not None:
                    failures.append(f'{label}: expected failure containing {expect!r}, but the check passed')
            except DietError as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')

    def rewrite(body):
        return lambda c: (c / 'Root.v').write_text(body, encoding='utf-8')

    trees('one tactic removed from a surviving proof',
          rewrite(BASE_V.replace('simpl.\n', '')), expect='command 3 differs')
    trees('one type annotation removed from a surviving definition',
          rewrite(BASE_V.replace('Definition j : nat := 0.', 'Definition j := 0.')), expect='differs')
    trees('one body token removed',
          rewrite(BASE_V.replace('Definition j : nat := 0.', 'Definition j : nat := .')), expect='differs')
    trees('a declaration partially removed',
          rewrite(BASE_V.replace('exact I.\n', '')), expect='differs')
    trees('a new .v file since the baseline',
          lambda c: (c / 'Other.v').write_text('(* a fact *)\nDefinition m := 0.\n', encoding='utf-8'),
          expect='new .v file')
    trees('a whole .v file removed since the baseline',
          lambda c: (c / 'Root.v').unlink(), expect='removed since the baseline')
    trees('an unledgered declaration removed',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')), expect='command(s) expected')
    trees('a ledger row naming the wrong file',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')),
          ledger=[DEL_ROW('Other.v', 'definition', 'j')], expect='is not a baseline .v file')
    trees('a ledger row naming the wrong kind',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')),
          ledger=[DEL_ROW('Root.v', 'lemma', 'j')], expect='not a')
    trees('a ledger row with an unknown reason',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')),
          ledger=[DEL_ROW('Root.v', 'definition', 'j', reason='felt-like-it')],
          expect='not one of the allowed deletion reasons')
    trees('a ledger row for a declaration still present',
          lambda c: None, ledger=[DEL_ROW('Root.v', 'definition', 'j')], expect='still')
    trees('a ledger row whose consumer search is a placeholder',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')),
          ledger=[DEL_ROW('Root.v', 'definition', 'j', search='n/a')], expect='placeholder')
    trees('a ledger row whose evidence says only none',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')),
          ledger=[DEL_ROW('Root.v', 'definition', 'j', evidence='none')], expect='`none`')
    trees('a superseded row naming a replacement nothing declares',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')),
          ledger=[DEL_ROW('Root.v', 'definition', 'j', reason='strictly-superseded', repl='ghost')],
          expect='which no candidate .v file declares')
    trees('a comment-only change', rewrite(BASE_V.replace('(* a fact *)', '(* shorter *)')))
    trees('the exact complete removal of one ledgered definition',
          rewrite(BASE_V.replace('Definition j : nat := 0.\n', '')),
          ledger=[DEL_ROW('Root.v', 'definition', 'j')])
    trees('the exact complete removal of one ledgered proof-bearing theorem',
          rewrite('(* a fact *)\nDefinition j : nat := 0.\n'),
          ledger=[DEL_ROW('Root.v', 'lemma', 'k')])

    # ── the exact disposition relation (contract section 3.5.D)
    def disp(label, rows, base=None, cand=None, expect=None):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        b = {'a.md': 10, 'gone.md': 20} if base is None else base
        c = {'a.md': 11, 'new.md': 30} if cand is None else cand
        parsed = [dict(zip(DISPOSITION_FIELDS, r), line=str(i + 2)) for i, r in enumerate(rows)]
        try:
            check_disposition_exact(b, c, parsed)
            if expect is not None:
                failures.append(f'{label}: expected failure containing {expect!r}, but the check passed')
        except DietError as exc:
            if expect is None:
                failures.append(f'{label}: expected success, failed with: {exc}')
            elif expect not in str(exc):
                failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')

    KEEP = ('a.md', '10', 'keep', 'live-governance', 'owner', 'evidence', '11')
    DEL = ('gone.md', '20', 'delete', 'history-only', 'owner', 'evidence', '0')
    NEWF = ('new.md', '0', 'm1-created', 'm1-enforcement', 'owner', 'evidence', '30')

    disp('an exact disposition over two trees', [KEEP, DEL, NEWF])
    disp('a false baseline byte count', [(*KEEP[:1], '99', *KEEP[2:]), DEL, NEWF], expect='trees hold')
    disp('a false candidate byte count', [(*KEEP[:6], '99'), DEL, NEWF], expect='trees hold')
    disp('an omitted baseline file row', [KEEP, NEWF], expect='have no row')
    disp('a phantom deleted file', [KEEP, DEL, NEWF, ('ghost.md', '5', 'delete', 'history-only', 'o', 'e', '0')],
         expect='in neither tree')
    disp('keep used for a baseline-only file', [KEEP, (*DEL[:2], 'keep', 'live-governance', 'o', 'e', '0'), NEWF],
         expect='present in baseline=True candidate=False')
    disp('m1-created used for a baseline file', [(*KEEP[:2], 'm1-created', *KEEP[3:]), DEL, NEWF],
         expect='present in baseline=True')
    disp('a duplicate disposition path', [KEEP, KEEP, DEL, NEWF], expect='duplicate path')
    disp('an undeclared purpose class', [(*KEEP[:3], 'because-i-said-so', *KEEP[4:]), DEL, NEWF],
         expect='not one of the allowed present purposes')
    disp('a disposition owner which is a placeholder', [(*KEEP[:4], 'tbd', *KEEP[5:]), DEL, NEWF],
         expect='placeholder')

    # ── the metric table must equal recomputation (contract section 3.5.C)
    def met(label, mutate, expect=None):
        counts['total'] += 1
        counts['must_fail'] += (expect is not None)
        bm = {k: (100 if k != 'v_comment_percent' else 20.0) for k in METRIC_ORDER}
        cm = {k: (50 if k != 'v_comment_percent' else 10.0) for k in METRIC_ORDER}
        rows = [dict(zip(METRIC_FIELDS, r)) for r in metric_rows(bm, cm)]
        mutate(rows)
        try:
            check_metrics_exact(rows, bm, cm)
            if expect is not None:
                failures.append(f'{label}: expected failure containing {expect!r}, but the check passed')
        except DietError as exc:
            if expect is None:
                failures.append(f'{label}: expected success, failed with: {exc}')
            elif expect not in str(exc):
                failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')

    met('a metric table equal to recomputation', lambda rows: None)
    met('a tampered metrics candidate value',
        lambda rows: rows[0].__setitem__('candidate', '49'), expect='recomputation gives')
    met('a tampered delta', lambda rows: rows[1].__setitem__('delta', '-1'), expect='recomputation gives')
    met('a tampered percentage',
        lambda rows: rows[2].__setitem__('delta_percent', '-99.00'), expect='recomputation gives')
    met('a metric row dropped', lambda rows: rows.pop(), expect='recomputation gives')
    met('a reordered metric table',
        lambda rows: rows.insert(0, rows.pop()), expect='recomputation gives')

    total, must_fail = counts['total'], counts['must_fail']
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: SOURCE-DIET SELF-TEST FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: source-diet self-test OK — {total} controls '
          f'({must_fail} must-fail with the reason pinned, {total - must_fail} must-accept, all executed) ✓')
    return 0


def _exception_row(d: Path, owner_kind='definition', owner_name='k',
                   category='trust-or-effect-boundary'):
    text = (d / 'Root.v').read_text(encoding='utf-8')
    blocks = logical_blocks(text, lex_comments(text, 'Root.v'))
    raw = block_text(text, blocks[0])
    sha = hashlib.sha256(raw.encode('utf-8')).hexdigest()
    lines = raw.count('\n') + 1
    return f'Root.v\t{owner_kind}\t{owner_name}\t{category}\t{lines}\t{sha}\twhy code cannot carry it\n'


def valid_exception(d: Path, fixture):
    v = '(* the sink stages every file before installing any, so a crash leaves no partial tree\n' \
        '   and the caller sees either the whole image or none of it *)\nDefinition k := 0.\n'
    fixture(d, v)
    (d / EXCEPTIONS_REL).write_text('\t'.join(EXCEPTION_FIELDS) + '\n' + _exception_row(d), encoding='utf-8')


def dup_rows(d: Path, fixture):
    v = '(* line one\n   line two *)\nDefinition k := 0.\n'
    fixture(d, v)
    row = _exception_row(d)
    (d / EXCEPTIONS_REL).write_text('\t'.join(EXCEPTION_FIELDS) + '\n' + row + row, encoding='utf-8')


def over_four(d: Path, fixture):
    v = '(* a\n   b\n   c\n   d\n   e *)\nDefinition k := 0.\n'
    fixture(d, v)
    (d / EXCEPTIONS_REL).write_text('\t'.join(EXCEPTION_FIELDS) + '\n' + _exception_row(d), encoding='utf-8')


def over_120_exception(d: Path, fixture):
    v = '(* short first line\n   ' + 'y' * 130 + ' *)\nDefinition k := 0.\n'
    fixture(d, v)
    (d / EXCEPTIONS_REL).write_text('\t'.join(EXCEPTION_FIELDS) + '\n' + _exception_row(d), encoding='utf-8')


def no_v_files(d: Path, fixture):
    fixture(d, CLEAN_V)
    (d / 'Root.v').unlink()


def bad_utf8(d: Path, fixture):
    fixture(d, CLEAN_V)
    (d / 'Bad.v').write_bytes(b'(* ok *)\nDefinition k := 0.\n\xff')


def tampered_baseline(d: Path, fixture):
    fixture(d, CLEAN_V)
    rows = [{'metric': 'baseline_ref', 'value': 'deadbeef'}, {'metric': 'v_total_bytes', 'value': '10'}]
    seal = baseline_seal(rows)
    body = 'metric\tvalue\nbaseline_ref\tdeadbeef\nv_total_bytes\t99\nbaseline_sha256\t' + seal + '\n'
    (d / BASELINE_REL).write_text(body, encoding='utf-8')


def disposition(d: Path, fixture, omit=False, phantom_delete=False, bad_purpose=False):
    fixture(d, CLEAN_V)
    files = inventory(d, snapshot=True)
    rows = []
    for rel in files:
        if omit and rel == 'Root.v':
            continue
        purpose = 'nonsense' if (bad_purpose and rel == 'Root.v') else 'certified-correctness'
        rows.append(f'{rel}\t1\tkeep\t{purpose}\towner\tevidence\t1')
    if phantom_delete:
        rows.append('Root.v\t1\tdelete\tcertified-correctness\towner\tevidence\t0')
        rows = [r for r in rows if not (r.startswith('Root.v\t1\tkeep'))]
    (d / DISPOSITION_REL).write_text('\t'.join(DISPOSITION_FIELDS) + '\n' + '\n'.join(sorted(rows)) + '\n',
                                     encoding='utf-8')


BASE_V = ('(* a fact *)\n'
          'Lemma k : True.\n'
          'Proof.\n'
          'simpl.\n'
          'exact I.\n'
          'Qed.\n'
          'Definition j : nat := 0.\n')


def DEL_ROW(path, kind, name, reason='no-current-consumer', repl='none',
            consumers='none', search='searched every tracked source for the bare name',
            evidence='the exact declaration comparison passes with this row'):
    return (path, kind, name, reason, repl, consumers, search, evidence)


def direction_fixture(d: Path, fixture, bump: str | None = None, archaeology: bool = False):
    """A tree whose sealed baseline is generous, so the candidate legitimately improves on it."""
    body = '(* the one integer authority, in a repair 3 shape *)\n' if archaeology else CLEAN_V
    fixture(d, body)
    m = run_measure(d, snapshot=True, out=None)
    pairs = [('baseline_ref', 'deadbeef')]
    for k in METRIC_ORDER:
        v = float(m[k])
        if k in MUST_DECREASE:
            v = v + 1000            # a generous baseline the candidate beats
        if bump and k == bump:
            v = v - 1000            # …except the one we want to have gone the wrong way
        pairs.append((k, str(int(v)) if float(v) == int(v) else str(v)))
    seal = baseline_seal([{'metric': k, 'value': v} for k, v in pairs])
    (d / BASELINE_REL).write_text('metric\tvalue\n' + ''.join(f'{k}\t{v}\n' for k, v in pairs)
                                  + f'baseline_sha256\t{seal}\n', encoding='utf-8')


def git_fixture(d: Path, fixture):
    fixture(d, CLEAN_V)
    for cmd in (['git', 'init', '-q'], ['git', 'add', '-A']):
        p = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
        assert p.returncode == 0, f'git failed: {p.stderr.strip()}'


def main() -> int:
    ap = argparse.ArgumentParser(description='M1 source-diet comment law, ledgers and measurement')
    ap.add_argument('--root', default='.')
    ap.add_argument('--snapshot', action='store_true')
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--measure', action='store_true')
    ap.add_argument('--write-metrics', default=None)
    ap.add_argument('--baseline-ref', default=None,
                    help='record this exact ref in the written metric file, under the same seal')
    ap.add_argument('--against-baseline', action='store_true',
                    help='the required metrics must decrease, and the required counts must be zero')
    ap.add_argument('--code-identical', default=None, metavar='REF',
                    help='every surviving Rocq declaration is identical to REF (or `baseline` for the sealed '
                         'ref) after removing exactly the ledgered declarations')
    ap.add_argument('--write-disposition', action='store_true',
                    help='rewrite the mechanical disposition fields from --baseline-ref and the working tree')
    ap.add_argument('--verify-m1-evidence', action='store_true',
                    help='the exit check: every M1 evidence artifact against two exact Git refs')
    ap.add_argument('--candidate-ref', dest='verify_candidate', default=None, metavar='REF',
                    help='the candidate ref for --verify-m1-evidence; --baseline-ref names the other side')
    args = ap.parse_args()
    root = Path(args.root).resolve()
    if args.self_test:
        rc = self_test()
        if rc or not (args.check or args.measure or args.write_metrics
                      or args.against_baseline or args.code_identical
                      or args.verify_m1_evidence or args.write_disposition):
            return rc
    try:
        if args.measure or args.write_metrics:
            out = Path(args.write_metrics) if args.write_metrics else None
            m = run_measure(root, args.snapshot, out, args.baseline_ref)
            if args.measure:
                print_measure(m)
            if args.write_metrics:
                ref = f' at {args.baseline_ref}' if args.baseline_ref else ''
                print(f'fido: source-diet wrote {len(METRIC_ORDER)} sealed metrics{ref} '
                      f'to {args.write_metrics} ✓')
        if args.write_disposition:
            ref = args.baseline_ref or 'baseline'
            if ref == 'baseline':
                ref = check_baseline(root)['baseline_ref']
            n = write_disposition(root, ref)
            print(f'fido: source-diet wrote {n} disposition row(s) against {ref[:7]} ✓')
        if args.check:
            print(f'fido: source-diet OK — {run_check(root, args.snapshot)} ✓')
        if args.against_baseline:
            n = check_direction(root, args.snapshot)
            print(f'fido: source-diet direction OK — {n} required metric(s) moved the right way ✓')
        if args.code_identical:
            print(f'fido: source-diet code identity OK — {check_code_against_ref(root, args.code_identical)} ✓')
        if args.verify_m1_evidence:
            if not (args.baseline_ref and args.verify_candidate):
                print('fido: SOURCE-DIET FAILED — --verify-m1-evidence needs both --baseline-ref and '
                      '--candidate-ref', file=sys.stderr)
                return 1
            print('fido: source-diet M1 evidence OK — '
                  f'{verify_m1_evidence(root, args.baseline_ref, args.verify_candidate)} ✓')
    except DietError as exc:
        print(f'fido: SOURCE-DIET FAILED — {exc}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
