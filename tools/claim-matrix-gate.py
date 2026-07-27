#!/usr/bin/env python3
"""Repair-20 obligation matrix checker.

A freeze report is prose. Prose is not gated by anything, so it can quietly claim more than any theorem
states — which is exactly how the previous candidate blocked: green proofs and a completion narrative that
had drifted past what the public statements carried. Green proofs cannot upgrade a weaker statement.

So every load-bearing completion claim gets a row naming the exact public surface that establishes it, the
fixture or client test that exercises it, and the gate that keeps it honest. This tool does not read Rocq
types and does not judge whether a theorem is strong enough — a human does that. It enforces the part a
human reviewer cannot do reliably by eye: that every named surface, fixture and gate actually EXISTS under
that exact name, and that no claim is marked closed while any evidence cell is empty or dangling.

That is a narrow guarantee, and stating it narrowly is the point. A gate that promised to verify claim
strength would be the same overclaim one layer up.

Matrix: `.review/C4_REPAIR_20_OBLIGATION_MATRIX.tsv`
  claim_id  claim_text  owner_file  public_surface  fixture_or_client_test  gate  status

`status` is `closed` or `open`. A CLOSED row must resolve every cell. An OPEN row is an obligation whose
evidence does not exist yet; its evidence cells must say `pending: <what will establish it>` — never blank,
never `N/A`. Review cannot be requested while any obligation is open: if `.review/REVIEW_REQUEST.md` says
`state: requested`, every row must be closed. That is the executable form of "do not freeze early".

`public_surface` is `;`-separated declaration names, each of which must be declared at top level in
`owner_file`. `fixture_or_client_test` and `gate` are `;`-separated `path:literal-token` pairs; the token
must occur literally in that file. A load-bearing claim with no fixture must say so as
`unsupported-boundary: <reason>` — never a bare `N/A`.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

TSV_REL = '.review/C4_REPAIR_20_OBLIGATION_MATRIX.tsv'
REVIEW_REQUEST_REL = '.review/REVIEW_REQUEST.md'
PENDING = 'pending: '
FIELDS = ('claim_id', 'claim_text', 'owner_file', 'public_surface',
          'fixture_or_client_test', 'gate', 'status')
STATUSES = ('closed', 'open')
DECL_KINDS = ('Definition', 'Lemma', 'Theorem', 'Corollary', 'Record', 'Inductive', 'Fixpoint',
              'Module', 'Parameter', 'Axiom', 'Notation', 'Class', 'Instance')
UNSUPPORTED = 'unsupported-boundary: '

# A row whose `gate` cell names this runs an EXECUTABLE check instead of merely pointing at evidence: no
# prohibited builder may appear in that row's named surfaces, statement or proof.  After a capability or a
# failure is returned, recovering its evidence by re-running a builder is the exact defect A001 exists to
# prevent — so the claim that the roots do not do it is checked, not asserted.
BUILDER_PROHIBITION = 'tools/claim-matrix-gate.py:BUILDER_PROHIBITION'
BANNED_BUILDERS = ('build_elaboration_core', 'build_compilation_input', 'build_expression_phase',
                   'Index.index_program', 'elaborate', 'program_visit', 'program_package_refs')


class MatrixError(Exception):
    """Any failure to read, parse, validate, or resolve. Always names the exact row and reason."""


def read_text(path: Path, label: str) -> str:
    try:
        return path.read_text(encoding='utf-8')
    except FileNotFoundError:
        raise MatrixError(f'{label}: {path} does not exist')
    except UnicodeDecodeError as exc:
        raise MatrixError(f'{label}: {path} is not valid UTF-8 ({exc})')
    except OSError as exc:
        raise MatrixError(f'{label}: {path} could not be read ({exc.__class__.__name__}: {exc})')


def load_rows(root: Path):
    text = read_text(root / TSV_REL, 'claim matrix')
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    if not lines:
        raise MatrixError(f'{TSV_REL}: empty')
    if tuple(lines[0].split('\t')) != FIELDS:
        raise MatrixError(f'{TSV_REL}: header must be exactly {chr(9).join(FIELDS)!r}')
    rows, seen = [], set()
    for n, line in enumerate(lines[1:], start=2):
        cells = line.split('\t')
        if len(cells) != len(FIELDS):
            raise MatrixError(f'{TSV_REL}:{n}: expected {len(FIELDS)} fields, found {len(cells)}')
        row = {**dict(zip(FIELDS, cells)), 'line': str(n)}
        for k in FIELDS:
            if not row[k].strip():
                raise MatrixError(f'{TSV_REL}:{n}: claim {row["claim_id"] or "<blank>"}: '
                                  f'field {k!r} is EMPTY — a load-bearing claim may not have a blank '
                                  f'evidence cell')
        if row['claim_id'] in seen:
            raise MatrixError(f'{TSV_REL}:{n}: duplicate claim_id {row["claim_id"]!r}')
        seen.add(row['claim_id'])
        if row['status'] not in STATUSES:
            raise MatrixError(f'{TSV_REL}:{n}: status {row["status"]!r} is not one of {", ".join(STATUSES)}')
        for k in ('public_surface', 'fixture_or_client_test', 'gate'):
            if row[k].strip().upper() in ('N/A', 'NA', '-', '—', 'NONE', 'TBD'):
                raise MatrixError(
                    f'{TSV_REL}:{n}: claim {row["claim_id"]}: {k!r} is {row[k]!r} — a load-bearing claim '
                    f'needs a real surface, or an explicit "{UNSUPPORTED}<reason>"')
            # an OPEN obligation has no evidence yet and must say so in words; a CLOSED one may not.
            pending = row[k].strip().startswith(PENDING)
            if row['status'] == 'open' and not pending:
                raise MatrixError(
                    f'{TSV_REL}:{n}: {row["claim_id"]} is open, so {k!r} must be '
                    f'"{PENDING}<what will establish it>" — an open obligation may not cite evidence it '
                    f'does not have')
            if row['status'] == 'closed' and pending:
                raise MatrixError(
                    f'{TSV_REL}:{n}: {row["claim_id"]} is closed but {k!r} is still {PENDING.strip()!r} — '
                    f'a closed obligation must name the evidence that establishes it')
            if pending and not row[k].strip()[len(PENDING):].strip():
                raise MatrixError(f'{TSV_REL}:{n}: {row["claim_id"]}: {k!r} is pending with no written reason')
        rows.append(row)
    if not rows:
        raise MatrixError(f'{TSV_REL}: no claim rows')
    ordered = sorted(rows, key=lambda r: r['claim_id'])
    if [r['claim_id'] for r in rows] != [r['claim_id'] for r in ordered]:
        raise MatrixError(f'{TSV_REL}: rows are not in canonical claim_id order')
    return rows


def file_of(root: Path, rel: str, row: dict, field: str) -> str:
    if rel.startswith('/') or '..' in Path(rel).parts:
        raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: {field} path {rel!r} escapes the tree')
    p = root / rel
    if p.is_symlink() or not p.is_file():
        raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: {field} names {rel!r}, '
                          f'which is not a regular file in this tree')
    return read_text(p, f'{row["claim_id"]} {field}')


def declaration_patterns(owner: str, name: str):
    """How a surface is DECLARED, per language — never a bare mention, which any comment could satisfy."""
    esc = re.escape(name)
    if owner.endswith('.v'):
        return [rf'(?m)^\s*(?:{"|".join(DECL_KINDS)})\s+{esc}\b']
    if owner.endswith('.py'):
        return [rf'(?m)^\s*(?:def|class)\s+{esc}\b', rf'(?m)^{esc}\s*=']
    if owner.endswith('.sh'):
        return [rf'(?m)^{esc}\s*\(\)', rf'(?m)^{esc}=']
    if owner in ('Makefile',):
        return [rf'(?m)^{esc}:']
    if owner.endswith(('.ml', '.mlg')):
        return [rf'(?m)^\s*(?:let|and|type|module|exception)\s+(?:rec\s+)?{esc}\b']
    # anything else (Dockerfile, hooks): a shell function or an assignment, still a DEFINITION site
    return [rf'(?m)^\s*{esc}\s*\(\)', rf'(?m)^\s*{esc}=']


def check_surfaces(root: Path, row: dict):
    """Every named surface must be DECLARED in the owner file, under that exact name."""
    text = file_of(root, row['owner_file'], row, 'owner_file')
    for name in [s.strip() for s in row['public_surface'].split(';') if s.strip()]:
        if name.startswith(UNSUPPORTED):
            continue
        if not any(re.search(pat, text) for pat in declaration_patterns(row['owner_file'], name)):
            raise MatrixError(
                f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: public_surface names {name!r}, but '
                f'{row["owner_file"]} declares no such top-level surface — deleted, renamed, or never existed')


def check_builder_prohibition(root: Path, row: dict):
    """No prohibited builder may appear in the row's named surfaces — statement or proof."""
    text = file_of(root, row['owner_file'], row, 'owner_file')
    for name in [s.strip() for s in row['public_surface'].split(';') if s.strip()]:
        for pat in declaration_patterns(row['owner_file'], name):
            m = re.search(pat, text)
            if not m:
                continue
            end = text.find('\nQed.', m.start())
            if end < 0:
                end = text.find('\n}.', m.start())
            if end < 0:
                raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: cannot delimit {name!r} '
                                  f'in {row["owner_file"]} to check the builder prohibition')
            block = text[m.start():end]
            for banned in BANNED_BUILDERS:
                if re.search(rf'(?<![\w.]){re.escape(banned)}\b', block):
                    raise MatrixError(
                        f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: {name!r} names the PROHIBITED builder '
                        f'{banned!r} in its statement or proof — a returned-object guarantee may not recover '
                        f'its evidence by re-running a builder')
            break


def check_tokens(root: Path, row: dict, field: str):
    """Each `path:literal-token` must occur literally in that file."""
    raw = row[field].strip()
    if raw.startswith(UNSUPPORTED.rstrip()):
        # a declared boundary is allowed, but it has to SAY something — the sentinel alone is a blank cell
        # wearing a label.
        if not raw[len(UNSUPPORTED.rstrip()):].strip():
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: {field} declares an unsupported '
                              f'boundary with no written reason')
        return
    for entry in [s.strip() for s in raw.split(';') if s.strip()]:
        if ':' not in entry:
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: {field} entry {entry!r} is not '
                              f'"path:token"')
        rel, token = entry.split(':', 1)
        rel, token = rel.strip(), token.strip()
        if not token:
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: {field} entry {entry!r} has an '
                              f'empty token')
        text = file_of(root, rel, row, field)
        if token not in text:
            raise MatrixError(
                f'{TSV_REL}:{row["line"]}: {row["claim_id"]}: {field} points at {rel} for {token!r}, '
                f'which does not occur there — dangling evidence')


def run(root: Path) -> str:
    rows = load_rows(root)
    for row in rows:
        if row['status'] == 'open':
            continue                      # nothing to resolve yet; its cells already said so in words
        check_surfaces(root, row)
        check_tokens(root, row, 'fixture_or_client_test')
        if BUILDER_PROHIBITION in row['gate']:
            check_builder_prohibition(root, row)
        check_tokens(root, row, 'gate')
    closed = sum(1 for r in rows if r['status'] == 'closed')
    still_open = [r['claim_id'] for r in rows if r['status'] == 'open']
    # Review cannot be requested while an obligation is open. This is the executable form of the standing
    # rule not to freeze when the first findings turn green — prose alone has not held that line before.
    if still_open:
        rr = root / REVIEW_REQUEST_REL
        if rr.is_file() and 'state: requested' in read_text(rr, 'review request'):
            raise MatrixError(
                f'{REVIEW_REQUEST_REL} requests review, but {len(still_open)} obligation(s) are still open: '
                + ', '.join(still_open))
    return (f'{len(rows)} obligation(s): {closed} closed, {len(still_open)} open; '
            f'every closed row resolves its surface, fixture and gate')


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
            except MatrixError as exc:
                if expect is None:
                    failures.append(f'{label}: expected success, failed with: {exc}')
                elif expect not in str(exc):
                    failures.append(f'{label}: failed for the WRONG reason — wanted {expect!r}, got: {exc}')

    def lines(work: Path):
        return (work / TSV_REL).read_text(encoding='utf-8').split('\n')

    def write(work: Path, L):
        (work / TSV_REL).write_text('\n'.join(L), encoding='utf-8')

    def closed_idx(work: Path) -> int:
        ensure_closed_row(work)          # the controls own their subject; they never need one to exist
        for i, l in enumerate(lines(work)[1:], start=1):
            c = l.split('\t')
            if len(c) == len(FIELDS) and c[FIELDS.index('status')] == 'closed':
                return i
        raise AssertionError('no closed row in the fixture to mutate')

    def set_field(work: Path, field: str, value: str):
        i = closed_idx(work)
        L = lines(work); c = L[i].split('\t'); c[FIELDS.index(field)] = value
        L[i] = '\t'.join(c); write(work, L)

    def rename_named_surface(work: Path):
        """Rename the declaration the first CLOSED row points at — the matrix must notice."""
        ensure_closed_row(work)
        c = None
        for l in lines(work)[1:]:
            cells = l.split('\t')
            if (len(cells) == len(FIELDS) and cells[FIELDS.index('status')] == 'closed'
                    and cells[FIELDS.index('owner_file')].endswith('.v')):
                c = cells; break
        assert c is not None, 'no closed row with a Rocq owner to mutate'
        owner, name = c[FIELDS.index('owner_file')], c[FIELDS.index('public_surface')].split(';')[0].strip()
        p = work / owner
        t = p.read_text(encoding='utf-8')
        kinds = '|'.join(DECL_KINDS)
        t2 = re.sub(rf'(?m)^(\s*(?:{kinds})\s+){re.escape(name)}\b', rf'\1{name}_renamed', t, count=1)
        assert t2 != t, 'could not rename the declaration'
        p.write_text(t2, encoding='utf-8')

    scenario('canonical matrix passes', lambda w: w)
    scenario('a named public surface was renamed', rename_named_surface,
             expect='declares no such top-level surface')
    scenario('a named public surface never existed',
             lambda w: set_field(w, 'public_surface', 'no_such_theorem_anywhere'),
             expect='declares no such top-level surface')
    scenario('an owner file that does not exist',
             lambda w: set_field(w, 'owner_file', 'NoSuchFile.v'),
             expect='not a regular file in this tree')
    scenario('a dangling gate token',
             lambda w: set_field(w, 'gate', 'gate/Assumptions.v:Print Assumptions Compilable.no_such.'),
             expect='dangling evidence')
    scenario('a dangling fixture token',
             lambda w: set_field(w, 'fixture_or_client_test', 'Dockerfile:sealed ZZ Nonexistent.Thing'),
             expect='dangling evidence')
    scenario('an empty evidence cell',
             lambda w: set_field(w, 'gate', ' '),
             expect="is EMPTY")
    scenario('a bare N/A instead of a stated boundary',
             lambda w: set_field(w, 'fixture_or_client_test', 'N/A'),
             expect='needs a real surface')
    scenario('an unsupported boundary with no written reason',
             lambda w: set_field(w, 'fixture_or_client_test', UNSUPPORTED.strip()),
             expect='unsupported boundary with no written reason')
    scenario('duplicate claim id',
             lambda w: write(w, lines(w)[:2] + [lines(w)[1]] + lines(w)[2:]),
             expect='duplicate claim_id')
    scenario('unknown status',
             lambda w: set_field(w, 'status', 'mostly'),
             expect='is not one of')
    scenario('malformed field count',
             lambda w: write(w, [lines(w)[0], lines(w)[1].rsplit('\t', 1)[0]] + lines(w)[2:]),
             expect='expected 7 fields')
    scenario('rows out of canonical order',
             lambda w: write(w, [lines(w)[0], lines(w)[2], lines(w)[1]] + lines(w)[3:]),
             expect='not in canonical claim_id order')
    scenario('the matrix itself is deleted',
             lambda w: (w / TSV_REL).unlink(),
             expect='does not exist')
    scenario('a gate path escaping the tree',
             lambda w: set_field(w, 'gate', '../elsewhere.v:token'),
             expect='escapes the tree')
    scenario('an open obligation citing evidence it does not have',
             lambda w: open_row_cites_evidence(w),
             expect='an open obligation may not cite evidence it does not have')
    scenario('review requested while an obligation is still open',
             lambda w: request_review(w),
             expect='requests review, but')
    # the BUILDER_PROHIBITION check must actually fire.  Without this the rows that cite it would pass
    # whether or not the check does anything — a gate nobody has seen fail is not evidence.
    scenario('a prohibited builder injected into a root fixture proof',
             inject_banned_builder,
             expect='names the PROHIBITED builder')

    total, must_fail = counts['total'], counts['must_fail']
    if failures:
        for f in failures:
            print(f'  FAIL  {f}')
        print(f'fido: CLAIM-MATRIX SELF-TEST FAILED — {len(failures)} of {total} controls wrong')
        return 1
    print(f'fido: claim-matrix self-test OK — {total} controls '
          f'({must_fail} must-fail with the reason pinned, {total - must_fail} must-accept) ✓')
    return 0


# A closed row the mutation controls own outright.  Its id sorts after every real obligation id, so appending
# it preserves canonical order, and its evidence is real — Compilable.v really declares that root fixture.
# The controls build their own subject rather than needing the live matrix to be in a particular state: a
# control that can only run while some obligation happens to be closed silently stops being a control the day
# the matrix changes shape.
SYNTHETIC_CLOSED = (
    'ZZZ-SELF-TEST-CLOSED-ROW',
    'A synthetic closed row the adversarial controls mutate, independent of the live obligation statuses.',
    'Compilable.v', 'deep_nested_compile_fixture', 'Compilable.v:deep_nested_program',
    BUILDER_PROHIBITION, 'closed')


def ensure_closed_row(work: Path):
    """Guarantee one CLOSED row with a Rocq owner, appending the synthetic one only if none exists."""
    p = work / TSV_REL
    L = p.read_text(encoding='utf-8').split('\n')
    for l in L[1:]:
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[FIELDS.index('status')] == 'closed':
            return
    tail = L.pop() if L and L[-1] == '' else None      # keep the file's trailing newline exactly as it was
    L.append('\t'.join(SYNTHETIC_CLOSED))
    if tail is not None:
        L.append(tail)
    p.write_text('\n'.join(L), encoding='utf-8')


def _reopen_first_row(work: Path, pending: bool):
    """Flip the first row to `open`. With `pending=False` it is given REAL evidence, which an open row may not
    have; with `pending=True` it becomes a well-formed open row. Both controls set the cells they depend on
    rather than inheriting whatever the live matrix happens to hold, so neither is vacuous in either
    direction — an already-open row with pending cells would otherwise make the first control test nothing."""
    p = work / TSV_REL; L = p.read_text(encoding='utf-8').split('\n')
    c = L[1].split('\t')
    assert len(c) == len(FIELDS), 'malformed first row in the fixture'
    c[FIELDS.index('status')] = 'open'
    for k in ('public_surface', 'fixture_or_client_test', 'gate'):
        c[FIELDS.index(k)] = (PENDING + 'a deliberately reopened obligation') if pending \
            else SYNTHETIC_CLOSED[FIELDS.index(k)]
    L[1] = '\t'.join(c)
    p.write_text('\n'.join(L), encoding='utf-8')


def open_row_cites_evidence(work: Path):
    """An OPEN row naming real evidence must be rejected: it cannot have evidence it has not produced."""
    _reopen_first_row(work, pending=False)


def request_review(work: Path):
    """Ask for review while an obligation is open — the executable form of "do not freeze early"."""
    _reopen_first_row(work, pending=True)
    p = work / REVIEW_REQUEST_REL
    p.write_text(p.read_text(encoding='utf-8').replace('state: closed', 'state: requested', 1),
                 encoding='utf-8')


def inject_banned_builder(work: Path):
    """Put a banned builder inside the proof of the first surface a CLOSED BUILDER_PROHIBITION row names."""
    ensure_closed_row(work)
    L = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    for line in L[1:]:
        c = line.split('\t')
        if (len(c) == len(FIELDS) and c[FIELDS.index('status')] == 'closed'
                and BUILDER_PROHIBITION in c[FIELDS.index('gate')]):
            owner = c[FIELDS.index('owner_file')]
            name = c[FIELDS.index('public_surface')].split(';')[0].strip()
            p = work / owner
            text = p.read_text(encoding='utf-8')
            for pat in declaration_patterns(owner, name):
                m = re.search(pat, text)
                if m:
                    cut = text.index('\nProof.', m.start()) + len('\nProof.')
                    p.write_text(text[:cut] + '\n  pose proof (build_expression_phase) as _injected.'
                                 + text[cut:], encoding='utf-8')
                    return
    raise AssertionError('no BUILDER_PROHIBITION row with a locatable surface')


def main() -> int:
    ap = argparse.ArgumentParser(description='repair-20 claim-to-theorem matrix gate')
    ap.add_argument('--root', default='.')
    ap.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    root = Path(args.root).resolve()
    if args.self_test:
        return self_test(root)
    try:
        msg = run(root)
    except MatrixError as exc:
        print(f'fido: CLAIM-MATRIX GATE FAILED — {exc}', file=sys.stderr)
        return 1
    print(f'fido: claim-matrix gate OK — {msg} ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
