#!/usr/bin/env python3
"""Obligation matrix checker for the active checkpoint.

A freeze report is prose. Prose is not gated by anything, so it can quietly claim more than any theorem or
control carries — which is how candidates have blocked before: green gates and a completion narrative that had
drifted past the evidence. Green gates cannot upgrade a weaker statement.

So every accepted obligation gets a row naming the authority that owns it, the implementation that satisfies
it, the positive evidence, the adversarial control that must fail without it, the mutation that proves that
control is load-bearing, and the gate that runs them. This tool does not read Rocq types and does not judge
whether an implementation is strong enough — a human does that. It enforces the part a human reviewer cannot
do reliably by eye: that every named surface, token and gate EXISTS under that exact name, that the required
obligations are all present exactly once, and that no row is marked closed while any cell is empty, dangling
or still pending.

That is a narrow guarantee, and stating it narrowly is the point. A gate that promised to verify claim
strength would be the same overclaim one layer up. The matrix is a checked map from obligations to evidence;
it is not itself authority.

Matrix: `.review/M0_OBLIGATION_MATRIX.tsv`. `TSV_REL` and `REQUIRED_OBLIGATIONS` follow the ACTIVE checkpoint;
they are its subject, not its design, and they move when the active work moves.
  obligation_id  claim  owning_authority  implementation
  positive_evidence  negative_control  mutation_control  gate  status

`status` is `closed` or `open`. A CLOSED row must resolve every cell. An OPEN row is an obligation whose
evidence does not exist yet; its evidence cells must say `pending: <what will establish it>` — never blank,
never `N/A`. Review cannot be requested while any required obligation is absent, duplicated, malformed or
open: if `.review/REVIEW_REQUEST.md` says `state: requested`, the matrix must be complete and every row
closed. That is the executable form of "do not freeze early".

`owning_authority` is one repository path that must exist. `implementation` is `;`-separated `path:symbol`
pairs, each of which must be DECLARED at top level in that file. `positive_evidence`, `negative_control`,
`mutation_control` and `gate` are `;`-separated `path:literal-token` pairs; the token must occur literally in
that file. A cell with no applicable artifact must say so as `unsupported-boundary: <reason>` — never a bare
`N/A`.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

TSV_REL = '.review/M0_OBLIGATION_MATRIX.tsv'
REVIEW_REQUEST_REL = '.review/REVIEW_REQUEST.md'
PENDING = 'pending: '
UNSUPPORTED = 'unsupported-boundary: '
FIELDS = ('obligation_id', 'claim', 'owning_authority', 'implementation',
          'positive_evidence', 'negative_control', 'mutation_control', 'gate', 'status')
EVIDENCE_FIELDS = ('implementation', 'positive_evidence', 'negative_control', 'mutation_control', 'gate')
STATUSES = ('closed', 'open')
DECL_KINDS = ('Definition', 'Lemma', 'Theorem', 'Corollary', 'Record', 'Inductive', 'Fixpoint',
              'Module', 'Parameter', 'Axiom', 'Notation', 'Class', 'Instance')

# The obligations the accepted repair directive enumerates. This is a list of OBLIGATIONS, not of paths or
# namespaces: it is what the directive says must be answered, and a matrix missing one is not a matrix with a
# gap — it is a matrix that has quietly dropped an accepted requirement.
REQUIRED_OBLIGATIONS = (
    'M0-01', 'M0-02', 'M0-03', 'M0-04', 'M0-05',
    'M0-06', 'M0-07', 'M0-08', 'M0-09', 'M0-10',
)

# A row whose `gate` cell names this runs an EXECUTABLE check instead of merely pointing at evidence: no
# prohibited builder may appear in that row's named surfaces, statement or proof. After a capability or a
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
                raise MatrixError(f'{TSV_REL}:{n}: obligation {row["obligation_id"] or "<blank>"}: '
                                  f'field {k!r} is EMPTY — an accepted obligation may not have a blank cell')
        if row['obligation_id'] in seen:
            raise MatrixError(f'{TSV_REL}:{n}: duplicate obligation_id {row["obligation_id"]!r}')
        seen.add(row['obligation_id'])
        if row['status'] not in STATUSES:
            raise MatrixError(f'{TSV_REL}:{n}: status {row["status"]!r} is not one of {", ".join(STATUSES)}')
        for k in EVIDENCE_FIELDS:
            if row[k].strip().upper() in ('N/A', 'NA', '-', '—', 'NONE', 'TBD'):
                raise MatrixError(
                    f'{TSV_REL}:{n}: {row["obligation_id"]}: {k!r} is {row[k]!r} — an accepted obligation '
                    f'needs a real artifact, or an explicit "{UNSUPPORTED}<reason>"')
            pending = row[k].strip().startswith(PENDING)
            if row['status'] == 'open' and not pending:
                raise MatrixError(
                    f'{TSV_REL}:{n}: {row["obligation_id"]} is open, so {k!r} must be '
                    f'"{PENDING}<what will establish it>" — an open obligation may not cite evidence it '
                    f'does not have')
            if row['status'] == 'closed' and pending:
                raise MatrixError(
                    f'{TSV_REL}:{n}: {row["obligation_id"]} is closed but {k!r} is still '
                    f'{PENDING.strip()!r} — a closed obligation must name the evidence that establishes it')
            if pending and not row[k].strip()[len(PENDING):].strip():
                raise MatrixError(f'{TSV_REL}:{n}: {row["obligation_id"]}: {k!r} is pending with no reason')
        rows.append(row)
    if not rows:
        raise MatrixError(f'{TSV_REL}: no obligation rows')
    ordered = sorted(rows, key=lambda r: r['obligation_id'])
    if [r['obligation_id'] for r in rows] != [r['obligation_id'] for r in ordered]:
        raise MatrixError(f'{TSV_REL}: rows are not in canonical obligation_id order')
    missing = [o for o in REQUIRED_OBLIGATIONS if o not in seen]
    if missing:
        raise MatrixError(
            f'{TSV_REL}: {len(missing)} accepted obligation(s) have NO row: ' + ', '.join(missing))
    return rows


def file_of(root: Path, rel: str, row: dict, field: str) -> str:
    if rel.startswith('/') or '..' in Path(rel).parts:
        raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: {field} path {rel!r} '
                          f'escapes the tree')
    p = root / rel
    if p.is_symlink() or not p.is_file():
        raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: {field} names {rel!r}, '
                          f'which is not a regular file in this tree')
    return read_text(p, f'{row["obligation_id"]} {field}')


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
    return [rf'(?m)^\s*{esc}\s*\(\)', rf'(?m)^\s*{esc}=']


def check_owning_authority(root: Path, row: dict):
    file_of(root, row['owning_authority'].strip(), row, 'owning_authority')


def check_implementation(root: Path, row: dict):
    """Every named surface must be DECLARED in the named file, under that exact name."""
    raw = row['implementation'].strip()
    if raw.startswith(UNSUPPORTED.rstrip()):
        if not raw[len(UNSUPPORTED.rstrip()):].strip():
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: implementation declares an '
                              f'unsupported boundary with no written reason')
        return
    for entry in [s.strip() for s in raw.split(';') if s.strip()]:
        if ':' not in entry:
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: implementation entry '
                              f'{entry!r} is not "path:symbol"')
        rel, name = (x.strip() for x in entry.split(':', 1))
        text = file_of(root, rel, row, 'implementation')
        if not any(re.search(pat, text) for pat in declaration_patterns(rel, name)):
            raise MatrixError(
                f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: implementation names {name!r}, but '
                f'{rel} declares no such top-level surface — deleted, renamed, or never existed')


def check_builder_prohibition(root: Path, row: dict):
    """No prohibited builder may appear in the row's named surfaces — statement or proof."""
    for entry in [s.strip() for s in row['implementation'].split(';') if s.strip()]:
        if ':' not in entry:
            continue
        rel, name = (x.strip() for x in entry.split(':', 1))
        if not rel.endswith('.v'):
            continue
        text = file_of(root, rel, row, 'implementation')
        for pat in declaration_patterns(rel, name):
            m = re.search(pat, text)
            if not m:
                continue
            end = text.find('\nQed.', m.start())
            if end < 0:
                end = text.find('\n}.', m.start())
            if end < 0:
                raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: cannot delimit {name!r} '
                                  f'in {rel} to check the builder prohibition')
            block = text[m.start():end]
            for banned in BANNED_BUILDERS:
                if re.search(rf'(?<![\w.]){re.escape(banned)}\b', block):
                    raise MatrixError(
                        f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: {name!r} names the PROHIBITED '
                        f'builder {banned!r} in its statement or proof — a returned-object guarantee may not '
                        f'recover its evidence by re-running a builder')
            break


def check_tokens(root: Path, row: dict, field: str):
    """Each `path:literal-token` must occur literally in that file."""
    raw = row[field].strip()
    if raw.startswith(UNSUPPORTED.rstrip()):
        if not raw[len(UNSUPPORTED.rstrip()):].strip():
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: {field} declares an '
                              f'unsupported boundary with no written reason')
        return
    for entry in [s.strip() for s in raw.split(';') if s.strip()]:
        if ':' not in entry:
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: {field} entry {entry!r} is '
                              f'not "path:token"')
        rel, token = (x.strip() for x in entry.split(':', 1))
        if not token:
            raise MatrixError(f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: {field} entry {entry!r} '
                              f'has an empty token')
        text = file_of(root, rel, row, field)
        if token not in text:
            raise MatrixError(
                f'{TSV_REL}:{row["line"]}: {row["obligation_id"]}: {field} points at {rel} for {token!r}, '
                f'which does not occur there — dangling evidence')


def run(root: Path) -> str:
    rows = load_rows(root)
    for row in rows:
        if row['status'] == 'open':
            continue                      # nothing to resolve yet; its cells already said so in words
        check_owning_authority(root, row)
        check_implementation(root, row)
        for field in ('positive_evidence', 'negative_control', 'mutation_control'):
            check_tokens(root, row, field)
        if BUILDER_PROHIBITION in row['gate']:
            check_builder_prohibition(root, row)
        check_tokens(root, row, 'gate')
    closed = sum(1 for r in rows if r['status'] == 'closed')
    still_open = [r['obligation_id'] for r in rows if r['status'] == 'open']
    # Review cannot be requested while an obligation is open. This is the executable form of the standing
    # rule not to freeze when the first findings turn green — prose alone has not held that line before.
    if still_open:
        rr = root / REVIEW_REQUEST_REL
        if rr.is_file() and 'state: requested' in read_text(rr, 'review request'):
            raise MatrixError(
                f'{REVIEW_REQUEST_REL} requests review, but {len(still_open)} obligation(s) are still open: '
                + ', '.join(still_open))
    return (f'{len(rows)} obligation(s), all {len(REQUIRED_OBLIGATIONS)} required present: {closed} closed, '
            f'{len(still_open)} open; every closed row resolves its authority, implementation, evidence, '
            f'controls and gate')


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

    scenario('canonical matrix passes', lambda w: w)
    scenario('a named implementation surface was renamed', rename_named_surface,
             expect='declares no such top-level surface')
    scenario('a named implementation surface never existed',
             lambda w: set_field(w, 'implementation', 'tools/naming-gate.py:no_such_function'),
             expect='declares no such top-level surface')
    scenario('an owning authority that does not exist',
             lambda w: set_field(w, 'owning_authority', '.review/NoSuchAuthority.md'),
             expect='not a regular file in this tree')
    scenario('a dangling gate token',
             lambda w: set_field(w, 'gate', 'Makefile:no_such_target_anywhere'),
             expect='dangling evidence')
    scenario('a dangling positive-evidence token',
             lambda w: set_field(w, 'positive_evidence', 'Dockerfile:no such stage exists'),
             expect='dangling evidence')
    scenario('a dangling negative control',
             lambda w: set_field(w, 'negative_control', 'tools/fcb-reference-gate.py:no such control'),
             expect='dangling evidence')
    scenario('a dangling mutation control',
             lambda w: set_field(w, 'mutation_control', 'tools/fcb-reference-gate.py:no such mutation'),
             expect='dangling evidence')
    scenario('an empty evidence cell',
             lambda w: set_field(w, 'gate', ' '),
             expect='is EMPTY')
    scenario('a bare N/A instead of a stated boundary',
             lambda w: set_field(w, 'negative_control', 'N/A'),
             expect='needs a real artifact')
    scenario('an unsupported boundary with no written reason',
             lambda w: set_field(w, 'mutation_control', UNSUPPORTED.strip()),
             expect='unsupported boundary with no written reason')
    scenario('duplicate obligation id',
             lambda w: write(w, lines(w)[:2] + [lines(w)[1]] + lines(w)[2:]),
             expect='duplicate obligation_id')
    scenario('a required obligation has no row',
             lambda w: drop_required_row(w),
             expect='accepted obligation(s) have NO row')
    scenario('unknown status',
             lambda w: set_field(w, 'status', 'mostly'),
             expect='is not one of')
    scenario('malformed field count',
             lambda w: write(w, [lines(w)[0], lines(w)[1].rsplit('\t', 1)[0]] + lines(w)[2:]),
             expect='expected 9 fields')
    scenario('rows out of canonical order',
             lambda w: write(w, [lines(w)[0], lines(w)[2], lines(w)[1]] + lines(w)[3:]),
             expect='not in canonical obligation_id order')
    scenario('the matrix itself is deleted',
             lambda w: (w / TSV_REL).unlink(),
             expect='does not exist')
    scenario('a gate path escaping the tree',
             lambda w: set_field(w, 'gate', '../elsewhere.v:token'),
             expect='escapes the tree')
    scenario('an open obligation citing evidence it does not have',
             lambda w: _reopen_first_row(w, pending=False),
             expect='an open obligation may not cite evidence it does not have')
    scenario('review requested while an obligation is still open',
             lambda w: request_review(w),
             expect='requests review, but')
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


# A closed row the mutation controls own outright. Its id sorts after every real obligation id, so appending
# it preserves canonical order, and its evidence is real. The controls build their own subject rather than
# needing the live matrix to be in a particular state: a control that can only run while some obligation
# happens to be closed silently stops being a control the day the matrix changes shape.
SYNTHETIC_CLOSED = (
    'ZZZ-SELF-TEST-CLOSED-ROW',
    'A synthetic closed row the adversarial controls mutate, independent of the live obligation statuses.',
    '.review/NEXT_STEPS.md',
    'Compilable.v:deep_nested_compile_fixture',
    'Compilable.v:deep_nested_program',
    'tools/fcb-reference-gate.py:canonical fixture passes (exported snapshot mode)',
    'tools/naming-gate.py:the read control passes for an unrelated reason',
    BUILDER_PROHIBITION,
    'closed')


def ensure_closed_row(work: Path, require_builder: bool = False):
    """Guarantee a CLOSED row the controls can mutate, appending the synthetic one only if none serves.

    `require_builder` additionally demands a row carrying the builder prohibition over a Rocq surface. A
    documentation checkpoint legitimately has neither, so without this the builder control would degrade into
    "could not construct the scenario" — a control that stops testing whenever the active work is not Rocq."""
    p = work / TSV_REL
    L = p.read_text(encoding='utf-8').split('\n')
    for l in L[1:]:
        c = l.split('\t')
        if len(c) == len(FIELDS) and c[FIELDS.index('status')] == 'closed':
            if not require_builder or BUILDER_PROHIBITION in c[FIELDS.index('gate')]:
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
    for k in EVIDENCE_FIELDS:
        c[FIELDS.index(k)] = (PENDING + 'a deliberately reopened obligation') if pending \
            else SYNTHETIC_CLOSED[FIELDS.index(k)]
    L[1] = '\t'.join(c)
    p.write_text('\n'.join(L), encoding='utf-8')


def drop_required_row(work: Path):
    """Delete the row for one accepted obligation — the matrix must notice the absence, not just bad cells."""
    p = work / TSV_REL
    L = p.read_text(encoding='utf-8').split('\n')
    keep = [l for l in L if l.split('\t')[0] != REQUIRED_OBLIGATIONS[0]]
    assert len(keep) == len(L) - 1, f'expected exactly one {REQUIRED_OBLIGATIONS[0]} row'
    p.write_text('\n'.join(keep), encoding='utf-8')


def request_review(work: Path):
    """Ask for review while an obligation is open — the executable form of "do not freeze early"."""
    _reopen_first_row(work, pending=True)
    p = work / REVIEW_REQUEST_REL
    p.write_text(p.read_text(encoding='utf-8').replace('state: closed', 'state: requested', 1),
                 encoding='utf-8')


def rename_named_surface(work: Path):
    """Rename the declaration the first CLOSED row points at — the matrix must notice."""
    ensure_closed_row(work)
    p = work / TSV_REL
    for l in p.read_text(encoding='utf-8').split('\n')[1:]:
        c = l.split('\t')
        if len(c) != len(FIELDS) or c[FIELDS.index('status')] != 'closed':
            continue
        entry = c[FIELDS.index('implementation')].split(';')[0].strip()
        if ':' not in entry:
            continue
        rel, name = (x.strip() for x in entry.split(':', 1))
        target = work / rel
        if not target.is_file():
            continue
        t = target.read_text(encoding='utf-8')
        kinds = '|'.join(DECL_KINDS)
        if rel.endswith('.v'):
            t2 = re.sub(rf'(?m)^(\s*(?:{kinds})\s+){re.escape(name)}\b', rf'\1{name}_renamed', t, count=1)
        else:
            t2 = re.sub(rf'(?m)^(\s*(?:def|class)\s+){re.escape(name)}\b', rf'\1{name}_renamed', t, count=1)
        if t2 != t:
            target.write_text(t2, encoding='utf-8')
            return
    raise AssertionError('no closed row with a locatable declaration to rename')


def inject_banned_builder(work: Path):
    """Put a banned builder inside the proof of the first surface a CLOSED BUILDER_PROHIBITION row names."""
    ensure_closed_row(work, require_builder=True)
    L = (work / TSV_REL).read_text(encoding='utf-8').split('\n')
    for line in L[1:]:
        c = line.split('\t')
        if (len(c) != len(FIELDS) or c[FIELDS.index('status')] != 'closed'
                or BUILDER_PROHIBITION not in c[FIELDS.index('gate')]):
            continue
        for entry in c[FIELDS.index('implementation')].split(';'):
            entry = entry.strip()
            if ':' not in entry:
                continue
            rel, name = (x.strip() for x in entry.split(':', 1))
            if not rel.endswith('.v'):
                continue
            p = work / rel
            text = p.read_text(encoding='utf-8')
            for pat in declaration_patterns(rel, name):
                m = re.search(pat, text)
                if m:
                    cut = text.index('\nProof.', m.start()) + len('\nProof.')
                    p.write_text(text[:cut] + '\n  pose proof (build_expression_phase) as _injected.'
                                 + text[cut:], encoding='utf-8')
                    return
    raise AssertionError('no BUILDER_PROHIBITION row with a locatable Rocq surface')


def main() -> int:
    ap = argparse.ArgumentParser(description='active-checkpoint obligation matrix gate')
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
