#!/usr/bin/env python3
"""Deterministic full-population attribution of a WitnessReject `rocq c -time` log.

Parses every timed sentence, rolls sentences up into their owning declarations, classifies each
declaration into a fixture population by fixed priority rules over its exact source text, extracts the
exact program each fixture analyzes, and writes ONE retained raw measurement product:

    witnessreject-sentences.tsv      every profiled declaration (never a top-N selection)

The two descriptive views are deterministic generated projections of that committed table alone —
never independent measurement authorities — and the gates regenerate + byte-compare them:

    witnessreject-programs.tsv       fixtures grouped by the exact program they analyze
    witnessreject-populations.tsv    population attribution

RAW CLASSIFICATION ONLY: every derived judgment — reachability, maximum savings, critical paths,
optimization recommendations — is owned by the one accounting engine (tools/perf-work-span.py).

Fail-closed checks: the parsed sentence count must meet --expect-sentences (so a top-N log cannot pose
as the full population), population totals must reconcile with the full sentence total within rounding
tolerance, and UNCLASSIFIED time above 2%% is an error.
"""
import argparse
import csv
import hashlib
import re
import sys
from collections import defaultdict
from pathlib import Path

SENT_NAME = 'witnessreject-sentences.tsv'
PROG_NAME = 'witnessreject-programs.tsv'
POP_NAME = 'witnessreject-populations.tsv'
SENT_COLS = ['basis', 'file', 'line_start', 'line_end', 'name', 'kind', 'secs', 'tactic',
             'goal_head', 'program_key', 'population', 'notes']

TIMED = re.compile(r'^Chars\s+(\d+)\s+-\s+(\d+)\s+\[[^\]]*\]\s+([0-9]+\.?[0-9]*)\s+secs', re.M)
DECL = re.compile(r'^\s*(?:Global\s+|Local\s+|Program\s+|#\[[^\]]*\]\s*)*'
                  r'(Theorem|Lemma|Corollary|Remark|Fact|Proposition|Example|Definition|Fixpoint|'
                  r'CoFixpoint|Inductive|CoInductive|Variant|Record|Instance|Module\s+Type|Module|'
                  r'Print\s+Assumptions|Compute|Goal|Axiom|Parameter|Notation|Arguments|Ltac|'
                  r'Import|From|Require|Opaque|Transparent)\b\s*([A-Za-z0-9_\'.]*)')

POPULATIONS = ('VERDICT_ONLY', 'ISSUE_TABLE', 'CAUSE_VIEW', 'REQ_VIEW', 'GROUP_VIEW',
               'RAW_FACT_READER', 'EXACT_PROVENANCE', 'EXACT_READER', 'COEXISTENCE',
               'SHARED_PROGRAM_OR_HELPER', 'OTHER', 'UNCLASSIFIED')

def line_starts(data):
    starts, pos = [0], data.find(b'\n')
    while pos != -1:
        starts.append(pos + 1)
        pos = data.find(b'\n', pos + 1)
    return starts


def line_of(starts, off):
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= off:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


def parse_records(log_text):
    return sorted((int(a), int(b), float(s)) for a, b, s in TIMED.findall(log_text))


class Decl:
    def __init__(self, name, kind, line):
        self.name, self.kind, self.line = name, kind, line
        self.end_line = line
        self.secs = 0.0
        self.sentences = []   # (ordinal, line, secs, text)
        self.text = []        # every owned sentence's text, in order


def attribute(src_bytes, records):
    """Roll every timed sentence into its owning declaration, in file order."""
    starts = line_starts(src_bytes)

    def text_of(a, b):
        return ' '.join(src_bytes[a:b].decode('utf-8', 'replace').split())

    decls, order = {}, []
    owner = Decl('(file preamble)', 'preamble', 0)
    decls[owner.name] = owner
    order.append(owner.name)
    for ordinal, (a, b, secs) in enumerate(records):
        body = text_of(a, b)
        ln = line_of(starts, a)
        m = DECL.match(body)
        if m and m.group(1) not in ('Opaque', 'Transparent'):
            name = (m.group(2) or '').strip() or m.group(1)
            if name not in decls:
                decls[name] = Decl(name, m.group(1), ln)
                order.append(name)
            owner = decls[name]
        owner.secs += secs
        owner.end_line = max(owner.end_line, ln)
        owner.sentences.append((ordinal, ln, secs, body))
        owner.text.append(body)
    return [decls[n] for n in order]


def named_programs(src_text):
    """Every named Syntax.Program definition in the file."""
    return set(re.findall(r'Definition\s+([A-Za-z0-9_\']+)\s*(?::\s*Syntax\.Program|\s*:=\s*prog\b)',
                          src_text))


def program_key(decl, prog_names):
    """The exact program(s) a fixture analyzes: named references, else a digest of the inline term."""
    body = ' '.join(decl.text)
    named = sorted(n for n in prog_names
                   if re.search(r'\b' + re.escape(n) + r'\b', body) and n != decl.name)
    if named:
        return ','.join(named)
    m = re.search(r'\(prog\s*\[.*?\]\s*\)', body)
    if m:
        norm = ' '.join(m.group(0).split())
        return 'inline:' + hashlib.sha256(norm.encode()).hexdigest()[:12]
    return ''


def classify(decl):
    """Fixed-priority population rules over the declaration's exact owned text."""
    body = ' '.join(decl.text)
    if decl.kind == 'preamble' or decl.kind in ('Notation', 'Ltac', 'Module', 'Import', 'From',
                                                'Require', 'Arguments'):
        return 'SHARED_PROGRAM_OR_HELPER'
    has_proof = any(t.startswith('Proof') or t in ('Qed.', 'Defined.') for t in decl.text)
    if not has_proof:
        return 'SHARED_PROGRAM_OR_HELPER'
    if re.search(r':\s*Compilable\.(rejects|outsides|compiles)\b', body) \
       and all(re.fullmatch(r'(Proof\.|Qed\.|Defined\.|reject\.|outside\.|compileok\.|'
                            r'Proof\. (reject|outside|compileok)\.)', t)
               for t in decl.text if not DECL.match(t)):
        return 'VERDICT_ONLY'
    if 'result_issues' in body or 'issue_class' in body:
        return 'ISSUE_TABLE'
    if 'diag_group' in body:
        return 'GROUP_VIEW'
    if 'result_cause_views' in body:
        return 'CAUSE_VIEW'
    if 'result_req_views' in body:
        return 'REQ_VIEW'
    if 'result_fact_list' in body or 'fact_rows' in body:
        return 'RAW_FACT_READER'
    if decl.name.startswith('reader_') or 'AN.analyze' in body or 'outcome_result' in body:
        return 'EXACT_PROVENANCE'
    if re.search(r'\b(AN|RP)\.', body):
        return 'EXACT_READER'
    if re.search(r':\s*Compilable\.(rejects|outsides|compiles)\b', body):
        return 'OTHER'  # a verdict claim with a non-standard proof body
    return 'UNCLASSIFIED'


def tactic_shape(decl):
    tac = [t for t in decl.text if not DECL.match(t) and t not in ('Proof.', 'Qed.', 'Defined.')]
    return (' '.join(tac))[:80]


def goal_head(decl):
    header = decl.text[0] if decl.text else ''
    m = re.search(r':\s*([A-Za-z0-9_.\']+)', header)
    return m.group(1) if m else ''


def build_rows(src_path, log_path, basis, expect_sentences):
    src_bytes = Path(src_path).read_bytes()
    src_text = src_bytes.decode('utf-8', 'replace')
    records = parse_records(Path(log_path).read_text(encoding='utf-8', errors='replace'))
    if not records:
        raise SystemExit(f'attribution: no timed sentences parsed from {log_path}')
    if expect_sentences and len(records) < expect_sentences:
        raise SystemExit(f'attribution: only {len(records)} sentences parsed but --expect-sentences '
                         f'{expect_sentences} — a truncated/top-N log cannot pose as the full population')
    decls = attribute(src_bytes, records)
    prog_names = named_programs(src_text)
    rows = []
    for d in decls:
        pop = classify(d)
        pk = program_key(d, prog_names) if pop not in ('SHARED_PROGRAM_OR_HELPER',) else ''
        rows.append({'basis': basis, 'file': str(src_path), 'line_start': str(d.line),
                     'line_end': str(d.end_line), 'name': d.name, 'kind': d.kind,
                     'secs': str(round(d.secs, 3)), 'tactic': tactic_shape(d),
                     'goal_head': goal_head(d), 'program_key': pk, 'population': pop,
                     'notes': ('also result_req_views' if pop == 'CAUSE_VIEW'
                               and 'result_req_views' in ' '.join(d.text) else '')})
    return records, rows


def gen_sentences(rows):
    lines = ['# CLASS: RAW_MEASUREMENT — full declaration-rolled sentence profile (every profiled '
             'sentence attributed, never top-N); the retained raw product the generated program and '
             'population views derive from.',
             '\t'.join(SENT_COLS)]
    for r in rows:
        lines.append('\t'.join(r[c] for c in SENT_COLS))
    return '\n'.join(lines) + '\n'


def derive_views(rows):
    """The two descriptive views, derived deterministically from sentence-table rows ALONE."""
    if not rows:
        raise SystemExit('attribution: cannot derive views from an empty sentence table')
    bases = sorted({r['basis'] for r in rows})
    if len(bases) != 1:
        raise SystemExit(f'attribution: sentence table carries {len(bases)} bases — one exact basis '
                         f'per retained profile')
    basis = bases[0]
    total = sum(float(r['secs']) for r in rows)

    progs = {}
    for r in rows:
        k = r['program_key']
        if not k:
            continue
        g = progs.setdefault(k, {'count': 0, 'secs': 0.0, 'families': set(), 'largest': ('', 0.0)})
        g['count'] += 1
        g['secs'] += float(r['secs'])
        g['families'].add(r['population'])
        if float(r['secs']) > g['largest'][1]:
            g['largest'] = (r['name'], float(r['secs']))
    plines = ['# CLASS: GENERATED_VIEW — fixtures grouped by the exact program they analyze; derived '
              'deterministically from witnessreject-sentences.tsv alone and byte-compared by the '
              'gates; raw attribution only, no derived judgment.',
              'basis\tprogram_key\tdecl_count\ttotal_secs\tclaim_families\tlargest_decl\tlargest_secs']
    for k in sorted(progs, key=lambda k: (-progs[k]['secs'], k)):
        g = progs[k]
        plines.append(f"{basis}\t{k}\t{g['count']}\t{g['secs']:.3f}\t"
                      f"{','.join(sorted(g['families']))}\t{g['largest'][0]}\t{g['largest'][1]:.3f}")

    pops = defaultdict(lambda: {'count': 0, 'secs': 0.0, 'largest': ('', 0.0)})
    for r in rows:
        p = pops[r['population']]
        p['count'] += 1
        p['secs'] += float(r['secs'])
        if float(r['secs']) > p['largest'][1]:
            p['largest'] = (r['name'], float(r['secs']))
    olines = ['# CLASS: GENERATED_VIEW — population attribution; derived deterministically from '
              'witnessreject-sentences.tsv alone and byte-compared by the gates; no opportunity id, '
              'recommendation, saving, or reachability claim.',
              'basis\tpopulation\tdecl_count\ttotal_secs\tshare_pct\tlargest_decl\tlargest_secs']
    for name in POPULATIONS:
        if name not in pops:
            continue
        p = pops[name]
        olines.append(f"{basis}\t{name}\t{p['count']}\t{p['secs']:.3f}\t"
                      f"{100 * p['secs'] / total:.1f}\t{p['largest'][0]}\t{p['largest'][1]:.3f}")
    return '\n'.join(plines) + '\n', '\n'.join(olines) + '\n'


def reconcile(rows, parse_total, tolerance=0.05):
    s = sum(float(r['secs']) for r in rows)
    if abs(s - parse_total) > tolerance:
        raise SystemExit(f'attribution: table total {s:.3f}s does not reconcile with the parsed '
                         f'sentence total {parse_total:.3f}s (tolerance {tolerance}s)')
    uncl = sum(float(r['secs']) for r in rows if r['population'] == 'UNCLASSIFIED')
    if s and uncl / s > 0.02:
        raise SystemExit(f'attribution: {100 * uncl / s:.1f}% of file time is UNCLASSIFIED '
                         f'(limit 2%) — extend the mechanical rules, do not guess')


def read_sentence_table(path):
    with open(path, encoding='utf-8') as f:
        body = [ln for ln in f if ln.strip() and not ln.lstrip().startswith('#')]
    return list(csv.DictReader(body, delimiter='\t'))


def check_generated(perf_dir, current_digest):
    """Regenerate both views from the committed sentence table and byte-compare the committed files."""
    sent_path = Path(perf_dir) / SENT_NAME
    if not sent_path.exists():
        raise SystemExit(f'attribution: missing committed {sent_path}')
    rows = read_sentence_table(sent_path)
    if current_digest:
        bad = sorted({r['basis'] for r in rows if r['basis'] != current_digest})
        if bad:
            raise SystemExit(f'attribution: sentence rows carry basis {bad[0][:12]} but the current '
                             f'candidate digest is {current_digest[:12]} — the raw profile must use '
                             f'the one CURRENT basis')
    reconcile(rows, sum(float(r['secs']) for r in rows))
    prog_text, pop_text = derive_views(rows)
    problems = []
    for name, text in ((PROG_NAME, prog_text), (POP_NAME, pop_text)):
        p = Path(perf_dir) / name
        if not p.exists():
            problems.append(f'generated-view law: {name}: the committed file is missing')
        elif p.read_text(encoding='utf-8') != text:
            problems.append(f'generated-view law: {name}: the committed file differs from the '
                            f'projection of the sentence table — hand edits and stale regeneration '
                            f'are rejected')
    if problems:
        for pr in problems:
            print('attribution: ' + pr, file=sys.stderr)
        raise SystemExit(f'fido: WITNESS-PROFILE-ATTRIBUTION FAILED — {len(problems)} generated-view '
                         f'violation(s)')
    print('fido: attribution generated views byte-identical to the committed projections of the '
          'sentence table')


def self_test():
    sentences = ['From Fido Require Import X.',
                 'Definition p_one : Syntax.Program := prog [ PL [ ILIT 1 ] ].',
                 'Definition v_fast : Compilable.rejects p_one.', 'Proof.', 'reject.', 'Qed.',
                 'Definition ev_table : map AN.issue_class (AN.result_issues (rres p_one)) = [].',
                 'Proof.', 'vm_compute; reflexivity.', 'Qed.',
                 'Definition ev_view : RP.result_cause_views (rres p_one) = [].',
                 'Proof.', 'vm_compute; reflexivity.', 'Qed.']
    times = ('0.1', '0.05', '0.02', '0.', '0.01', '0.01',
             '0.02', '0.', '1.0', '1.0', '0.02', '0.', '0.5', '0.5')
    src = ('\n'.join(sentences) + '\n').encode()
    off, offs = 0, []
    for s in sentences:
        offs.append((off, off + len(s)))
        off += len(s) + 1
    log = ''.join(f'Chars {a} - {b} [x] {t} secs (0.u,0.s)\n'
                  for (a, b), t in zip(offs, times))
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        sp, lp = Path(td) / 's.v', Path(td) / 't.log'
        sp.write_bytes(src)
        lp.write_text(log)
        records, rows = build_rows(sp, lp, 'a' * 64, 0)
        total = sum(s for _, _, s in records)
        byname = {r['name']: r for r in rows}
        prog_text, pop_text = derive_views(rows)
        checks = [
            ('verdict-only classified', byname['v_fast']['population'] == 'VERDICT_ONLY'),
            ('issue table classified', byname['ev_table']['population'] == 'ISSUE_TABLE'),
            ('cause view classified', byname['ev_view']['population'] == 'CAUSE_VIEW'),
            ('program helper classified',
             byname['p_one']['population'] == 'SHARED_PROGRAM_OR_HELPER'),
            ('program key extracted', byname['ev_table']['program_key'] == 'p_one'),
            ('program cluster grouped in the derived view',
             '\ta' * 0 + 'p_one\t3\t' in prog_text),
            ('derivation is deterministic', derive_views(rows) == (prog_text, pop_text)),
            ('views derive from the written table alone',
             derive_views(read_sentence_table_text(gen_sentences(rows))) == (prog_text, pop_text)),
        ]
        # adversary: a truncated log cannot pose as the full population
        try:
            build_rows(sp, lp, 'a' * 64, 100)
            checks.append(('truncated log rejected', False))
        except SystemExit:
            checks.append(('truncated log rejected', True))
        # adversary: table totals that do not reconcile with the parsed total are rejected
        try:
            reconcile(rows, total + 1.0)
            checks.append(('non-reconciling totals rejected', False))
        except SystemExit:
            checks.append(('non-reconciling totals rejected', True))
        # adversary: >2% unclassified time is rejected
        try:
            reconcile([{'secs': '0.5', 'population': 'UNCLASSIFIED'},
                       {'secs': '9.5', 'population': 'OTHER'}], 10.0)
            checks.append(('excess unclassified rejected', False))
        except SystemExit:
            checks.append(('excess unclassified rejected', True))
        # adversary: a sentence table carrying two bases cannot derive one view set
        try:
            derive_views(rows + [dict(rows[0], basis='b' * 64)])
            checks.append(('mixed-basis sentence table rejected', False))
        except SystemExit:
            checks.append(('mixed-basis sentence table rejected', True))
        # adversary: a hand-edited committed view fails the byte comparison
        (Path(td) / SENT_NAME).write_text(gen_sentences(rows), encoding='utf-8')
        (Path(td) / PROG_NAME).write_text(prog_text.replace('\t3\t', '\t9\t'), encoding='utf-8')
        (Path(td) / POP_NAME).write_text(pop_text, encoding='utf-8')
        try:
            check_generated(td, 'a' * 64)
            checks.append(('hand-edited program total rejected', False))
        except SystemExit:
            checks.append(('hand-edited program total rejected', True))
        # adversary: a foreign-basis sentence table fails the currency law
        (Path(td) / PROG_NAME).write_text(prog_text, encoding='utf-8')
        try:
            check_generated(td, 'f' * 64)
            checks.append(('foreign-basis sentence table rejected', False))
        except SystemExit:
            checks.append(('foreign-basis sentence table rejected', True))
        # the clean committed set passes
        try:
            check_generated(td, 'a' * 64)
            checks.append(('clean committed views accepted', True))
        except SystemExit:
            checks.append(('clean committed views accepted', False))
    bad = [n for n, ok in checks if not ok]
    if bad:
        print(f'fido: witness-profile-attribution self-test FAILED — {", ".join(bad)}')
        return 1
    print(f'fido: witness-profile-attribution self-test OK — {len(checks)} controls '
          f'(classification, deterministic table-derived views, reconciliation, truncation/tamper/'
          f'unclassified/mixed-basis/hand-edit adversaries)')
    return 0


def read_sentence_table_text(text):
    body = [ln for ln in text.splitlines(keepends=True)
            if ln.strip() and not ln.lstrip().startswith('#')]
    return list(csv.DictReader(body, delimiter='\t'))


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--check-generated', action='store_true',
                    help='regenerate the program/population views from the committed sentence table '
                         'and byte-compare the committed files (the gates run this; no profiling)')
    ap.add_argument('--perf-dir', default='.review/perf')
    ap.add_argument('--current-digest', default='',
                    help='with --check-generated: every sentence row must carry this exact basis')
    ap.add_argument('--source', action='append', default=[])
    ap.add_argument('--time-log', action='append', default=[])
    ap.add_argument('--basis')
    ap.add_argument('--outdir')
    ap.add_argument('--expect-sentences', type=int, default=500)
    a = ap.parse_args(argv[1:])
    if a.self_test:
        return self_test()
    if a.check_generated:
        check_generated(a.perf_dir, a.current_digest)
        return 0
    if not (a.source and a.time_log and a.basis and a.outdir):
        ap.error('--source, --time-log, --basis, --outdir are required (or --self-test / '
                 '--check-generated)')
    if len(a.source) != len(a.time_log):
        ap.error('each --source needs exactly one --time-log, in order')
    if not re.fullmatch(r'[0-9a-f]{64}', a.basis):
        raise SystemExit('attribution: --basis must be the 64-hex performance-input digest')
    all_records, all_rows = [], []
    for src, log in zip(a.source, a.time_log):
        records, rows = build_rows(src, log, a.basis, 0)
        all_records += records
        all_rows += rows
    if a.expect_sentences and len(all_records) < a.expect_sentences:
        raise SystemExit(f'attribution: only {len(all_records)} sentences parsed across '
                         f'{len(a.source)} file(s) but --expect-sentences {a.expect_sentences} — a '
                         f'truncated log set cannot pose as the full population')
    total = sum(s for _, _, s in all_records)
    reconcile(all_rows, total)
    out = Path(a.outdir)
    out.mkdir(parents=True, exist_ok=True)
    (out / SENT_NAME).write_text(gen_sentences(all_rows), encoding='utf-8')
    # the views derive from the table as WRITTEN, so the committed product chain is table -> views
    written = read_sentence_table(out / SENT_NAME)
    prog_text, pop_text = derive_views(written)
    (out / PROG_NAME).write_text(prog_text, encoding='utf-8')
    (out / POP_NAME).write_text(pop_text, encoding='utf-8')
    uncl = sum(float(r['secs']) for r in all_rows if r['population'] == 'UNCLASSIFIED')
    print(f'fido: witness-profile-attribution OK — {len(all_records)} sentences / {total:.2f}s fully '
          f'attributed across {len(all_rows)} declarations; totals reconcile; UNCLASSIFIED '
          f'{uncl:.2f}s within the 2% law; program/population views derived from the written table')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
