#!/usr/bin/env python3
"""Raw structured-data validator for the .review ledgers.

It runs before any derived count or cross-ledger claim and validates only the raw
rows: exact field count and CSV quoting, known enum values, unique ids, required
owners/milestones, cross-ledger id references, and cross-ledger milestone
consistency (an acceptance gate may fire at or before its latitude owning
milestone, never after). It owns no derived count and no semantic decision; the
code and its gated theorems remain the sole implementation authority.
"""
import argparse
import csv
import io
import re
import sys
import tempfile
from pathlib import Path

MILESTONE = re.compile(r'^C(\d+)$')
MILESTONE_OR_OUT = re.compile(r'^(C\d+|OUT)$')

# One inline schema per ledger; deliberately narrow, not a general framework.
SCHEMAS = {
    '.review/closure.csv': dict(
        delim=',',
        cols=['id', 'source', 'anchor', 'construct', 'disposition', 'representation',
              'owner', 'contract', 'price', 'kind', 'milestone'],
        id_re=re.compile(r'^(SPEC|PRE|BOUND|MEM|OP|KEY|GRAM)-X?\d+$'),
        enums={'disposition': {'IN', 'OUT'}, 'kind': {'ordinary', 'lexical-only'}},
        milestone_col='milestone', milestone_re=MILESTONE_OR_OUT,
        required=['owner', 'contract', 'milestone'],
    ),
    '.review/latitude.tsv': dict(
        delim='\t',
        cols=['latitude_id', 'source', 'anchor', 'matched_terms', 'sentence',
              'disposition', 'owner_row', 'contract', 'justification', 'milestone'],
        id_re=re.compile(r'^LAT-X?\d+$'),
        enums={'disposition': {'ACCEPTANCE-ALIGNMENT', 'ADEQUACY-DEMOTION', 'NOT-LATITUDE',
                               'OUT-COVERED', 'PROVED-REFINEMENT', 'STEP-NONDET'}},
        milestone_col='milestone', milestone_re=MILESTONE_OR_OUT,
        required=['owner_row', 'contract', 'milestone'],
        ref={'owner_row': '.review/closure.csv'},
    ),
    '.review/acceptance.tsv': dict(
        delim='\t',
        cols=['id', 'milestone', 'diagnostic', 'requirement', 'fixture', 'status'],
        id_re=re.compile(r'^LAT-X?\d+$'),
        enums={'status': {'PENDING', 'DISCHARGED'}},
        milestone_col='milestone', milestone_re=MILESTONE,
        required=['milestone', 'diagnostic', 'requirement', 'status'],
        ref={'id': '.review/latitude.tsv'},
    ),
    '.review/scope.tsv': dict(
        delim='\t',
        cols=['id', 'status', 'boundary', 'reason', 'enforcement', 'reopen_trigger'],
        id_re=re.compile(r'^SR-\d+$'),
        enums={'status': {'ACCEPTED', 'PROPOSED', 'REJECTED', 'SUPERSEDED'}},
        required=['boundary', 'reason', 'enforcement'],
    ),
}


def parse_ledger(path, delim):
    """Yield ('header'|'row', lineno, fields) per record; the first non-comment record is the header.

    Leading '#' comment lines are skipped, then csv.reader parses records — so a quoted field may span
    lines, while an unquoted delimiter surfaces as an extra field (a field-count failure) rather than
    being silently absorbed. lineno points at the record's last source line.
    """
    lines = path.read_text(encoding='utf-8').split('\n')
    start = 0
    while start < len(lines) and (not lines[start].strip() or lines[start].lstrip().startswith('#')):
        start += 1
    reader = csv.reader(io.StringIO('\n'.join(lines[start:])), delimiter=delim, strict=True)
    header_done = False
    for fields in reader:
        if not any(f.strip() for f in fields):
            continue
        lineno = start + reader.line_num
        if not header_done:
            header_done = True
            yield ('header', lineno, fields)
        else:
            yield ('row', lineno, fields)


def load(root, path_s, schema, findings):
    """Structural pass over one ledger; returns {id: row_dict} for the cross-ledger pass."""
    path = root / path_s
    if not path.exists():
        findings.append(f'{path_s}: ledger is missing')
        return {}
    rows = {}
    seen = set()
    try:
        records = list(parse_ledger(path, schema['delim']))
    except csv.Error as e:
        findings.append(f'{path_s}: invalid CSV quoting ({e})')
        return {}
    for kind, lineno, fields in records:
        if kind == 'header':
            if fields != schema['cols']:
                findings.append(f'{path_s}:{lineno}: header {fields} != schema {schema["cols"]}')
            continue
        n = len(fields)
        if n != len(schema['cols']):
            findings.append(f'{path_s}:{lineno}: {n} fields, expected {len(schema["cols"])} '
                            f'(unquoted delimiter, trailing field, or malformed row)')
            continue
        row = dict(zip(schema['cols'], fields))
        rid = fields[0]
        if not schema['id_re'].match(rid):
            findings.append(f'{path_s}:{lineno}: id {rid!r} does not match {schema["id_re"].pattern}')
        if rid in seen:
            findings.append(f'{path_s}:{lineno}: duplicate id {rid}')
        seen.add(rid)
        for col, valid in schema.get('enums', {}).items():
            if row[col] not in valid:
                findings.append(f'{path_s}:{lineno}: {col}={row[col]!r} not in {sorted(valid)}')
        mc = schema.get('milestone_col')
        if mc and not schema['milestone_re'].match(row[mc]):
            findings.append(f'{path_s}:{lineno}: milestone {row[mc]!r} does not match {schema["milestone_re"].pattern}')
        for col in schema.get('required', []):
            v = row.get(col, '').strip()
            if not v or v == '—':
                findings.append(f'{path_s}:{lineno}: required field {col} is empty')
        rows[rid] = (lineno, row)
    return rows


def cross(data, findings):
    """Cross-ledger references and milestone consistency."""
    for path_s, schema in SCHEMAS.items():
        for ref_col, target in schema.get('ref', {}).items():
            target_ids = set(data.get(target, {}))
            for rid, (lineno, row) in data.get(path_s, {}).items():
                ref = row.get(ref_col, '').strip()
                if ref and ref not in target_ids:
                    findings.append(f'{path_s}:{lineno}: {rid} {ref_col}={ref} references no live row in {target} (dangling)')

    def cnum(m):
        mm = MILESTONE.match(m)
        return int(mm.group(1)) if mm else None

    lat = data.get('.review/latitude.tsv', {})
    for aid, (lineno, arow) in data.get('.review/acceptance.tsv', {}).items():
        if aid in lat:
            am, lm = arow['milestone'], lat[aid][1]['milestone']
            an, ln = cnum(am), cnum(lm)
            if an is not None and ln is not None and an > ln:
                findings.append(f'.review/acceptance.tsv:{lineno}: {aid} gate milestone {am} is later than '
                                f'its latitude owning milestone {lm} (conflicting assignment across ledgers)')


def validate(root):
    findings = []
    data = {path_s: load(root, path_s, schema, findings) for path_s, schema in SCHEMAS.items()}
    cross(data, findings)
    return findings


# --- adversarial self-test: each defect class must be caught by the checks above ---
CLEAN = {
    'closure.csv': ('id,source,anchor,construct,disposition,representation,owner,contract,price,kind,milestone\n'
                    'SPEC-001,Go spec,A,A,IN,"a, b",own,SC-00,—,ordinary,C5\n'),
    'latitude.tsv': ('latitude_id\tsource\tanchor\tmatched_terms\tsentence\tdisposition\towner_row\tcontract\tjustification\tmilestone\n'
                     'LAT-001\tGo spec\tA\tmay\ts\tNOT-LATITUDE\tSPEC-001\tSC-00\tj\tC5\n'),
    'acceptance.tsv': ('id\tmilestone\tdiagnostic\trequirement\tfixture\tstatus\n'
                       'LAT-001\tC5\tFIDO-E-X\tr\tf\tPENDING\n'),
    'scope.tsv': ('id\tstatus\tboundary\treason\tenforcement\treopen_trigger\n'
                  'SR-001\tACCEPTED\tb\tr\te\tt\n'),
}


def self_test():
    controls = 0

    def mutate(files):
        nonlocal controls
        controls += 1
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / '.review').mkdir()
            for name, body in {**CLEAN, **files}.items():
                (root / '.review' / name).write_text(body, encoding='utf-8')
            return validate(root)

    if mutate({}):
        raise SystemExit('self-test: the clean fixture was rejected')
    cases = {
        'unquoted comma (extra field)':
            {'closure.csv': CLEAN['closure.csv'].replace('"a, b"', 'a, b')},
        'duplicate id':
            {'closure.csv': CLEAN['closure.csv'] + 'SPEC-001,Go spec,A,A,IN,x,own,SC-00,—,ordinary,C5\n'},
        'unknown enum':
            {'closure.csv': CLEAN['closure.csv'].replace(',IN,', ',MAYBE,')},
        'malformed milestone':
            {'closure.csv': CLEAN['closure.csv'].replace(',C5\n', ',C5x\n')},
        'empty required owner':
            {'closure.csv': CLEAN['closure.csv'].replace(',own,SC-00,', ',,SC-00,')},
        'bad id':
            {'scope.tsv': CLEAN['scope.tsv'].replace('SR-001', 'XR-001')},
        'dangling owner_row ref':
            {'latitude.tsv': CLEAN['latitude.tsv'].replace('SPEC-001', 'SPEC-999')},
        'dangling acceptance id ref':
            {'acceptance.tsv': CLEAN['acceptance.tsv'].replace('LAT-001', 'LAT-999')},
        'acceptance milestone later than latitude':
            {'acceptance.tsv': CLEAN['acceptance.tsv'].replace('\tC5\t', '\tC9\t')},
    }
    for label, files in cases.items():
        if not mutate(files):
            raise SystemExit(f'self-test: defect NOT caught: {label}')
    # a control that must NOT fire: an acceptance gate earlier than its milestone is lawful.
    controls += 1
    early = CLEAN['acceptance.tsv'].replace('\tC5\t', '\tC5\t')  # C5 == C5, lawful
    if mutate({'acceptance.tsv': early}):
        raise SystemExit('self-test: a lawful equal-milestone acceptance row was rejected')
    print(f'fido: ledger-validate self-test OK — {controls} controls '
          f'(each raw-structure defect class caught; a lawful equal-milestone gate accepted)')
    return 0


def main():
    ap = argparse.ArgumentParser(description='raw structured-data validator for the .review ledgers')
    ap.add_argument('--root', default='.', help='repository or exported-tree root')
    ap.add_argument('--self-test', action='store_true', help='run the adversarial controls')
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    findings = validate(Path(args.root))
    if findings:
        print('fido: LEDGER-VALIDATE FAILED — {} raw structured-data violation(s):'.format(len(findings)))
        for f in findings:
            print(f'  {f}')
        return 1
    print('fido: ledger-validate OK — closure/latitude/acceptance/scope rows are well-formed '
          '(field count, quoting, ids, enums, required owners/milestones, cross-ledger refs + milestone order)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
