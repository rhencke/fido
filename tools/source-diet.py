#!/usr/bin/env python3
"""The permanent `.v` comment law, and nothing else.

Current source states what is true now. It does not explain what used to exist, which repair introduced a
form, which candidate failed, or how a name changed. Git owns archaeology.

A DEFAULT `.v` comment is one logical block, one physical line, at most 120 characters including both
delimiters, at most one sentence, one current local fact, no archaeology. Anything longer needs one exact row
in `.review/M1_COMMENT_EXCEPTIONS.tsv`, and the relation is bidirectional: a long comment without a row
fails, and a row without its exact comment fails. The goal is zero exceptions; a large ledger is evidence the
diet failed even when the parser reports green.

Adjacency matters. Comment tokens separated only by whitespace are ONE logical block, so splitting a
paragraph into a stack of one-liners does not evade the rule. Only real code separates blocks.

The comment scanner is a Rocq lexer, not a regular expression: comments nest, strings may contain comment
delimiters, and comments may contain strings. A regex would mis-slice all three and then measure its own
mistake.

Everything fails closed. An unreadable file, invalid UTF-8, an unterminated comment or string, a failed Git
enumeration, an empty scan, a ledger row with no comment, a comment with no row, a hash mismatch, or an
ambiguous owner — each is an error naming the exact file and reason.
"""
from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

EXCEPTIONS_REL = '.review/M1_COMMENT_EXCEPTIONS.tsv'

EXCEPTION_FIELDS = ('path', 'owner_kind', 'owner_name', 'category', 'line_count', 'comment_sha256', 'reason')

OWNER_KINDS = ('file-module', 'definition', 'fixpoint', 'cofixpoint', 'inductive', 'record', 'theorem',
               'lemma', 'corollary', 'example', 'instance', 'class', 'module', 'module-type', 'notation')

CATEGORIES = ('invariant-not-expressed-by-type', 'trust-or-effect-boundary', 'non-obvious-proof-plan',
              'rocq-limitation-forcing-shape')

DECL_NAME = re.compile(
    r'^(?:Global\s+|Local\s+|Program\s+|#\[[^\]]*\]\s*)*'
    r'(?:Definition|Fixpoint|CoFixpoint|Theorem|Lemma|Corollary|Example|Record|Inductive|'
    r'Instance|Notation|Module|Class)\s+([A-Za-z_][A-Za-z0-9_\']*)', re.M)

DOC_MARKER = re.compile(r'^\(\*\*(?!\))')

BANNER_RUN = re.compile(r'(?:^\s*|\s)[-=~#*_\u2500-\u257f\u2550-\u2570\u2014\u2015]{3,}(?:\s|\s*$)')

SECTION_LABEL = re.compile(
    r'^\s*(?:\u00a7\s*)?(?:'
    r'THEOREM|LEMMA|DEFINITION|COROLLARY|RECORD|INDUCTIVE|FIXPOINT|EXAMPLE|NOTATION|MODULE|'
    r'SOUNDNESS|COMPLETENESS|EXACTNESS|DETERMINISM|INVARIANT|CONTRACT|PILLAR|PHASE|SECTION|STEP|PART|'
    r'GOAL|CLAIM|NOTE|SUMMARY|OVERVIEW|TABLE OF CONTENTS'
    r')\b\s*[:.\u2014-]|^\s*\u00a7?\s*\d+(?:\.\d+)*\s*[:.\u2014-]\s'
    # a lettered or shouted label is the same move in different clothes: `A:`, `KEY:`, `ROUND TRIP:`
    r'|^\s*(?:[A-Z]{1,4}|[A-Z][A-Z]+(?:\s+[A-Z]+)+)\s*[:.](?:\s|$)')

DECORATIVE_GLYPH = re.compile(r'[\u2500-\u257f\u2605\u2606\u25a0-\u25ff\u2022\u25cf]')

IDENTIFIER_ONLY = re.compile(r"^\[?[A-Za-z_][A-Za-z0-9_'.]*\]?$")

PROOF_CASE_LABEL = re.compile(r'^H\d+\s*=')

BULLET_LABEL = re.compile(r'^this\s+(?:member|case|branch|goal|conjunct|one)\b', re.I)

MAX_COMMENT_CHARS = 120

MAX_EXCEPTION_LINES = 4

RESIDUE_DIRS = {'.git', '_build', '__pycache__', '.fido'}

RESIDUE_SUFFIXES = ('.vo', '.vok', '.vos', '.vio', '.glob', '.pyc', '.aux', '.fido-tmp-v1')

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
            stripped = body.strip()
            if IDENTIFIER_ONLY.match(stripped):
                findings.append(f'{rel}:{entry["line"]}: the whole comment is the name {stripped!r}')
            if PROOF_CASE_LABEL.match(stripped):
                findings.append(f'{rel}:{entry["line"]}: proof-case label {stripped[:40]!r}')
            if BULLET_LABEL.match(stripped):
                findings.append(f'{rel}:{entry["line"]}: bullet label {stripped[:40]!r}')
            if not is_default and kind is None:
                findings.append(f'{rel}:{entry["line"]}: a comment needing an exception has no resolvable '
                                f'owner declaration')
            if not is_default and name is None and kind is not None:
                findings.append(f'{rel}:{entry["line"]}: ambiguous owner for an exception comment')
        blocks_by_file[rel] = entries
    return blocks_by_file, findings

def run_check(root: Path, snapshot: bool):
    """The PERMANENT policy: the comment law over the current tree, and the exception relation both ways.

    It reads the `.v` files and `M1_COMMENT_EXCEPTIONS.tsv`, and nothing else.  It does NOT consult the M1
    baseline, metric table, file disposition, deletion ledger, obligation matrix, candidate ref or freeze
    state: those are one checkpoint's exit evidence, and a permanent gate that enforced them would freeze the
    repository at that checkpoint forever — no later file, no later declaration, no larger tree."""
    files = inventory(root, snapshot)
    blocks_by_file, findings = scan_v(root, files)
    if not blocks_by_file:
        raise DietError(f'{root}: no .v files found — refusing to report a clean diet over nothing')
    if findings:
        raise DietError(f'{len(findings)} comment-law violation(s): ' + '; '.join(findings[:10])
                        + ('' if len(findings) <= 10 else f' … and {len(findings) - 10} more'))
    ex_rows = load_tsv(root, EXCEPTIONS_REL, EXCEPTION_FIELDS, 'M1 comment exceptions')
    n_ex = check_exceptions(ex_rows, blocks_by_file)
    n_blocks = sum(len(v) for v in blocks_by_file.values())
    return (f'{len(files)} file(s), {len(blocks_by_file)} .v file(s), {n_blocks} comment block(s) all obeying '
            f'the one-line 120-character one-sentence current-fact law; {n_ex} ledgered exception(s) matched '
            f'both ways')

CLEAN_V = '(* the one integer authority *)\nDefinition kind := 0.\n'

def _control_harness():
    """The shared scenario machinery, so the permanent and M1 control groups build fixtures alike."""
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

    return failures, counts, fixture, scenario, scenario_run

def _verdict(failures, counts, what: str) -> int:
    total, must_fail = counts['total'], counts['must_fail']
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: SOURCE-DIET {what.upper()} FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: source-diet {what} OK — {total} controls '
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

def _git_env(d: Path):
    return {'GIT_AUTHOR_NAME': 'fido', 'GIT_AUTHOR_EMAIL': 'f@example.com',
            'GIT_COMMITTER_NAME': 'fido', 'GIT_COMMITTER_EMAIL': 'f@example.com',
            'PATH': os.environ.get('PATH', ''), 'HOME': str(d)}

def git_fixture(d: Path, fixture):
    fixture(d, CLEAN_V)
    for cmd in (['git', 'init', '-q'], ['git', 'add', '-A']):
        p = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
        assert p.returncode == 0, f'git failed: {p.stderr.strip()}'

def self_test() -> int:
    """The permanent source-comment controls.

    They judge comments and the exception relation, and nothing about a baseline, a candidate or a freeze.
    A repository that has grown far past the diet that produced them must still pass every one."""
    failures, counts, fixture, scenario, scenario_run = _control_harness()

    long_line = '(* ' + 'a fact that runs on ' * 6 + 'and on past the limit *)\n'
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
             lambda d: fixture(d, '(* ── the retained core ── *)\nDefinition k := 0.\n'),
             expect='decorative glyph')
    scenario('an identifier-only comment',
             lambda d: fixture(d, '(* forest_reverse *)\nDefinition k := 0.\n'),
             expect='the whole comment is the name')
    scenario('a constructor-only comment',
             lambda d: fixture(d, '(* ConversionFailureCause *)\nDefinition k := 0.\n'),
             expect='the whole comment is the name')
    scenario('a bracketed identifier-only comment',
             lambda d: fixture(d, '(* [subtree_end] *)\nDefinition k := 0.\n'),
             expect='the whole comment is the name')
    scenario('a proof-case label',
             lambda d: fixture(d, '(* H1 = BoolDenotes : the concrete spelling *)\nDefinition k := 0.\n'),
             expect='proof-case label')
    scenario('a bullet label',
             lambda d: fixture(d, '(* this member IS the current one *)\nDefinition k := 0.\n'),
             expect='bullet label')
    scenario('a sentence that merely begins with the member',
             lambda d: fixture(d, '(* the member carries its own key, which is why no scan is needed *)\n'
                                  'Definition k := 0.\n'))
    scenario('a star decoration',
             lambda d: fixture(d, '(* ★ the exact round trip. *)\nDefinition k := 0.\n'),
             expect='decorative glyph')
    scenario('a TODO',
             lambda d: fixture(d, '(* TODO tighten this *)\nDefinition k := 0.\n'),
             expect='placeholder')
    scenario('an empty comment',
             lambda d: fixture(d, '(*  *)\nDefinition k := 0.\n'),
             expect='empty comment')
    # ── must fail: the exception relation, both ways
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
    # ── must accept: the law judges comments and lets the repository grow
    LATER_V = '(* a later module states one current fact *)\nDefinition later : nat := 1.\n'
    scenario('a new .v module with a compliant comment',
             lambda d: fixture(d, CLEAN_V, extra={'Later.v': LATER_V}))
    scenario('a new declaration added to an existing .v file',
             lambda d: fixture(d, CLEAN_V + '(* a later fact that earns its place *)\n'
                                            'Definition added : nat := 2.\n'))
    scenario('a repository far larger than the one the law was written for',
             lambda d: fixture(d, CLEAN_V, extra={'Later.v': LATER_V,
                                                  'Bulk.v': LATER_V.replace('later', 'bulk'),
                                                  'docs/notes.md': 'x' * 4096}))
    scenario('a new .v comment that breaks the law',
             lambda d: fixture(d, CLEAN_V, extra={'Later.v': '(* THEOREM: the label the law rejects *)\n'
                                                             'Definition later : nat := 1.\n'}),
             expect='section label')
    scenario('a .v under .review/scratch is inspected, not skipped',
             lambda d: fixture(d, CLEAN_V, extra={'.review/scratch/shadow.v':
                                                  '(* THEOREM: a scratch directory hides no .v *)\n'
                                                  'Definition shadow : nat := 0.\n'}),
             expect='section label')
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

    return _verdict(failures, counts, 'self-test')


def main() -> int:
    ap = argparse.ArgumentParser(description='the permanent .v comment law')
    ap.add_argument('--root', default='.')
    ap.add_argument('--snapshot', action='store_true', help='scan an exported tree with no .git')
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    try:
        print('fido: source-diet OK — ' + run_check(Path(args.root).resolve(), args.snapshot) + ' ✓')
    except DietError as exc:
        print(f'fido: SOURCE-DIET FAILED — {exc}')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
