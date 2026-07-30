#!/usr/bin/env python3
"""Generate and verify the human view of the spec-closure ledger.

`FIDO_FCB_CLOSURE_LEDGER.csv` is the canonical 491-row table. `FIDO_FCB_CLOSURE_LEDGER.md` says of itself
that it is "generated from" that CSV, and this tool is what makes that true. A view that merely claims to
be derived is the defect Governance D-07 names for the human-acts list: the claim carries no weight, and
the two can drift while both look authoritative.

`--write` regenerates the view; `--check` compares exact bytes and never writes. One implementation does
both, so the checker cannot drift from the writer. Everything fails closed and names the exact input.

The view is a projection: sections grouped by `source`, rows carrying id, anchor, construct, disposition,
owner, test and price. The CSV keeps columns the view does not show (`representation`, `public`,
`template`); those are still canonical, they are simply not part of the human table.
"""
from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

CSV_REL = '.review/fcb/current/FIDO_FCB_CLOSURE_LEDGER.csv'
MD_REL = '.review/fcb/current/FIDO_FCB_CLOSURE_LEDGER.md'
CSV_FIELDS = ('id', 'source', 'anchor', 'construct', 'disposition', 'representation',
              'owner', 'test', 'price', 'public', 'template')
VIEW_COLUMNS = (('ID', 'id'), ('Anchor', 'anchor'), ('Construct', 'construct'),
                ('Disposition', 'disposition'), ('One owner', 'owner'),
                ('Contract', 'test'), ('Future inclusion price', 'price'))


class LedgerError(Exception):
    """Any failure to read, parse, validate, or match. Always names the exact input and reason."""


def read_text(path: Path, label: str) -> str:
    try:
        return path.read_text(encoding='utf-8')
    except FileNotFoundError:
        raise LedgerError(f'{label}: {path} does not exist')
    except UnicodeDecodeError as exc:
        raise LedgerError(f'{label}: {path} is not valid UTF-8 ({exc})')
    except OSError as exc:
        raise LedgerError(f'{label}: {path} could not be read ({exc.__class__.__name__}: {exc})')


def load(root: Path):
    """Return (preamble_comment_lines, rows). The CSV's leading `#` lines are its own provenance banner."""
    text = read_text(root / CSV_REL, 'closure ledger')
    lines = text.split('\n')
    banner = []
    i = 0
    while i < len(lines) and lines[i].startswith('#'):
        banner.append(lines[i]); i += 1
    if i >= len(lines):
        raise LedgerError(f'{CSV_REL}: no header row after the comment banner')
    reader = csv.DictReader(lines[i:])
    if tuple(reader.fieldnames or ()) != CSV_FIELDS:
        raise LedgerError(f'{CSV_REL}: header must be exactly {",".join(CSV_FIELDS)}, '
                          f'found {",".join(reader.fieldnames or [])}')
    rows, seen = [], set()
    for n, row in enumerate(reader, start=i + 2):
        if row['id'] is None or not row['id'].strip():
            raise LedgerError(f'{CSV_REL}:{n}: blank id')
        if None in row.values() or any(v is None for v in row.values()):
            raise LedgerError(f'{CSV_REL}:{n}: row {row["id"]!r} has the wrong number of fields')
        if row['id'] in seen:
            raise LedgerError(f'{CSV_REL}:{n}: duplicate id {row["id"]!r}')
        seen.add(row['id'])
        for k in ('source', 'disposition'):
            if not row[k].strip():
                raise LedgerError(f'{CSV_REL}:{n}: row {row["id"]!r} has a blank {k!r}')
        rows.append(row)
    if not rows:
        raise LedgerError(f'{CSV_REL}: no data rows')
    return banner, rows


def render(rows, header: str) -> str:
    def cell(s: str) -> str:
        return s.replace('|', '\\|')
    out = [header, f'**Rows:** {len(rows)}', '']
    for source in sorted({r['source'] for r in rows}):
        out.append(f'## {source}')
        out.append('')
        out.append('| ' + ' | '.join(name for name, _ in VIEW_COLUMNS) + ' |')
        out.append('|' + '---|' * len(VIEW_COLUMNS))
        for r in [x for x in rows if x['source'] == source]:
            out.append('| ' + ' | '.join(cell(r[key]) for _, key in VIEW_COLUMNS) + ' |')
        out.append('')
    return '\n'.join(out)


def split_header(current: str) -> str:
    """The view's hand-authored preamble ends at the generated `**Rows:**` line; everything after is derived."""
    marker = '\n**Rows:** '
    i = current.find(marker)
    if i < 0:
        raise LedgerError(f'{MD_REL}: no "**Rows:**" line — cannot locate the generated section boundary')
    return current[:i]


def run(root: Path, write: bool, out: Path | None = None) -> str:
    _banner, rows = load(root)
    md = root / MD_REL
    current = read_text(md, 'closure ledger view')
    generated = render(rows, split_header(current))
    if write:
        # `--out` sends the view to an isolated directory so a caller can validate the complete output set
        # before publishing any of it; without it the writer still updates the tracked view in place.
        dest = ((out / MD_REL) if out else md)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(generated, encoding='utf-8')
        return f'wrote {MD_REL} from {len(rows)} canonical row(s)'
    if current != generated:
        cur, gen = current.split('\n'), generated.split('\n')
        for i in range(max(len(cur), len(gen))):
            a = cur[i] if i < len(cur) else '<missing line>'
            b = gen[i] if i < len(gen) else '<extra line>'
            if a != b:
                raise LedgerError(
                    f'{MD_REL} is not the generated view of {CSV_REL} — first difference at line {i + 1}\n'
                    f'    tracked:   {a[:160]}\n    generated: {b[:160]}')
        raise LedgerError(f'{MD_REL} differs from the generated view')
    return f'{MD_REL} matches {len(rows)} canonical row(s)'


def main() -> int:
    ap = argparse.ArgumentParser(description='spec-closure ledger view generator and checker')
    ap.add_argument('--root', default='.')
    ap.add_argument('--out', default=None, help='write the view into this directory instead of the tree')
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = ap.parse_args()
    try:
        msg = run(Path(args.root).resolve(), write=args.write,
                  out=Path(args.out).resolve() if args.out else None)
    except LedgerError as exc:
        print(f'fido: CLOSURE-LEDGER VIEW FAILED — {exc}', file=sys.stderr)
        return 1
    print(f'fido: closure-ledger view OK — {msg} ✓')
    return 0


if __name__ == '__main__':
    sys.exit(main())
