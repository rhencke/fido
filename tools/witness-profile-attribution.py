#!/usr/bin/env python3
"""Deterministic full-population attribution of a WitnessReject `rocq c -time` log.

Parses every timed sentence (same record grammar as rocq-profile.py), rolls sentences up
into their owning declarations, classifies each declaration into a fixture population by
fixed priority rules over its exact source text, extracts the exact program each fixture
analyzes, and writes four TSV evidence tables:

    witnessreject-sentences.tsv      every profiled sentence (never a top-N selection)
    witnessreject-programs.tsv       fixtures grouped by the exact program they analyze
    witnessreject-populations.tsv    population attribution

RAW CLASSIFICATION ONLY: every derived judgment — reachability, maximum savings, critical paths,
optimization recommendations — is owned by the one accounting engine (tools/perf-work-span.py)

Fail-closed checks: the parsed sentence count must meet --expect-sentences (so a top-N
log cannot pose as the full population), population totals must reconcile with the full
sentence total within rounding tolerance, and UNCLASSIFIED time above 2%% is an error.
"""
import argparse
import hashlib
import re
import sys
from collections import defaultdict
from pathlib import Path

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


def build_tables(src_path, log_path, basis, expect_sentences):
    src_bytes = Path(src_path).read_bytes()
    src_text = src_bytes.decode('utf-8', 'replace')
    records = parse_records(Path(log_path).read_text(encoding='utf-8', errors='replace'))
    if not records:
        raise SystemExit(f'attribution: no timed sentences parsed from {log_path}')
    if expect_sentences and len(records) < expect_sentences:
        raise SystemExit(f'attribution: only {len(records)} sentences parsed but --expect-sentences '
                         f'{expect_sentences} — a truncated/top-N log cannot pose as the full population')
    total = sum(s for _, _, s in records)
    decls = attribute(src_bytes, records)
    prog_names = named_programs(src_text)

    rows = []
    for d in decls:
        pop = classify(d)
        pk = program_key(d, prog_names) if pop not in ('SHARED_PROGRAM_OR_HELPER',) else ''
        rows.append({'basis': basis, 'file': str(src_path), 'line_start': d.line,
                     'line_end': d.end_line, 'name': d.name, 'kind': d.kind,
                     'secs': round(d.secs, 3), 'tactic': tactic_shape(d),
                     'goal_head': goal_head(d), 'program_key': pk, 'population': pop,
                     'notes': ('also result_req_views' if pop == 'CAUSE_VIEW'
                               and 'result_req_views' in ' '.join(d.text) else '')})

    pops = defaultdict(lambda: {'count': 0, 'secs': 0.0, 'largest': ('', 0.0)})
    for r in rows:
        p = pops[r['population']]
        p['count'] += 1
        p['secs'] += r['secs']
        if r['secs'] > p['largest'][1]:
            p['largest'] = (r['name'], r['secs'])

    progs = defaultdict(lambda: {'count': 0, 'secs': 0.0, 'families': set(),
                                 'vm_pairs': 0, 'largest': ('', 0.0)})
    for d, r in zip(decls, rows):
        if not r['program_key']:
            continue
        g = progs[r['program_key']]
        g['count'] += 1
        g['secs'] += r['secs']
        g['families'].add(r['population'])
        g['vm_pairs'] += sum(1 for _, _, _, t in d.sentences if 'vm_compute' in t)
        if r['secs'] > g['largest'][1]:
            g['largest'] = (r['name'], r['secs'])

    return records, total, rows, pops, progs


def build_tables_multi(pairs, basis, expect_sentences):
    """Attribute several (source, time-log) pairs — the chunked fixture matrix — into one merged table set."""
    all_records, all_rows = [], []
    pops = defaultdict(lambda: {'count': 0, 'secs': 0.0, 'largest': ('', 0.0)})
    progs = defaultdict(lambda: {'count': 0, 'secs': 0.0, 'families': set(),
                                 'vm_pairs': 0, 'largest': ('', 0.0)})
    for src, log in pairs:
        records, _, rows, p1, g1 = build_tables(src, log, basis, 0)
        all_records += records
        all_rows += rows
        for k, v in p1.items():
            pops[k]['count'] += v['count']
            pops[k]['secs'] += v['secs']
            if v['largest'][1] > pops[k]['largest'][1]:
                pops[k]['largest'] = v['largest']
        for k, v in g1.items():
            progs[k]['count'] += v['count']
            progs[k]['secs'] += v['secs']
            progs[k]['families'] |= v['families']
            progs[k]['vm_pairs'] += v['vm_pairs']
            if v['largest'][1] > progs[k]['largest'][1]:
                progs[k]['largest'] = v['largest']
    if expect_sentences and len(all_records) < expect_sentences:
        raise SystemExit(f'attribution: only {len(all_records)} sentences parsed across {len(pairs)} file(s) '
                         f'but --expect-sentences {expect_sentences} — a truncated log set cannot pose as '
                         'the full population')
    total = sum(s for _, _, s in all_records)
    return all_records, total, all_rows, pops, progs


def reconcile(total, pops, tolerance=0.05):
    s = sum(p['secs'] for p in pops.values())
    if abs(s - total) > tolerance:
        raise SystemExit(f'attribution: population totals {s:.3f}s do not reconcile with the '
                         f'full sentence total {total:.3f}s (tolerance {tolerance}s)')
    uncl = pops.get('UNCLASSIFIED', {'secs': 0.0})['secs']
    if total and uncl / total > 0.02:
        raise SystemExit(f'attribution: {100 * uncl / total:.1f}% of file time is UNCLASSIFIED '
                         f'(limit 2%) — extend the mechanical rules, do not guess')


def write_tables(outdir, basis, total, rows, pops, progs):
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=True)

    with open(out / 'witnessreject-sentences.tsv', 'w', encoding='utf-8') as f:
        cols = ['basis', 'file', 'line_start', 'line_end', 'name', 'kind', 'secs', 'tactic',
                'goal_head', 'program_key', 'population', 'notes']
        f.write('# full declaration-rolled sentence profile — every profiled sentence attributed, never top-N\n')
        f.write('\t'.join(cols) + '\n')
        for r in rows:
            f.write('\t'.join(str(r[c]) for c in cols) + '\n')

    with open(out / 'witnessreject-programs.tsv', 'w', encoding='utf-8') as f:
        f.write('# fixtures grouped by the exact program they analyze; vm_pairs counts vm_compute sentences '
                '(tactic and Qed sides both pay the reduction); raw attribution only, no derived judgment\n')
        f.write('basis\tprogram_key\tdecl_count\ttotal_secs\tclaim_families\tvm_pairs\tlargest_decl\t'
                'largest_secs\n')
        for k in sorted(progs, key=lambda k: -progs[k]['secs']):
            g = progs[k]
            f.write(f"{basis}\t{k}\t{g['count']}\t{g['secs']:.3f}\t{','.join(sorted(g['families']))}\t"
                    f"{g['vm_pairs']}\t{g['largest'][0]}\t{g['largest'][1]:.3f}\n")

    with open(out / 'witnessreject-populations.tsv', 'w', encoding='utf-8') as f:
        f.write(f'# population attribution; full sentence total {total:.2f}s; totals reconcile within 0.05s; '
                'raw attribution only — derived judgments live in the accounting owner\n')
        f.write('basis\tpopulation\tdecl_count\ttotal_secs\tshare_pct\tlargest_decl\tlargest_secs\n')
        for name in POPULATIONS:
            if name not in pops:
                continue
            p = pops[name]
            f.write(f"{basis}\t{name}\t{p['count']}\t{p['secs']:.3f}\t{100 * p['secs'] / total:.1f}\t"
                    f"{p['largest'][0]}\t{p['largest'][1]:.3f}\n")


def self_test():
    # sentence-per-record, the way `rocq c -time` actually reports (Proof./tactic/Qed. split out)
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
        _, total, rows, pops, progs = build_tables(sp, lp, 'a' * 64, 0)
        byname = {r['name']: r for r in rows}
        checks = [
            ('verdict-only classified', byname['v_fast']['population'] == 'VERDICT_ONLY'),
            ('issue table classified', byname['ev_table']['population'] == 'ISSUE_TABLE'),
            ('cause view classified', byname['ev_view']['population'] == 'CAUSE_VIEW'),
            ('program helper classified',
             byname['p_one']['population'] == 'SHARED_PROGRAM_OR_HELPER'),
            ('program key extracted', byname['ev_table']['program_key'] == 'p_one'),
            ('program cluster grouped', progs['p_one']['count'] == 3),
            ('totals reconcile', abs(sum(p['secs'] for p in pops.values()) - total) < 0.05),
        ]
        # adversary: a truncated log cannot pose as the full population
        try:
            build_tables(sp, lp, 'a' * 64, 100)
            checks.append(('truncated log rejected', False))
        except SystemExit:
            checks.append(('truncated log rejected', True))
        # adversary: population totals that do not reconcile are rejected
        try:
            bad = {k: dict(v) for k, v in pops.items()}
            bad['ISSUE_TABLE']['secs'] += 1.0
            reconcile(total, bad)
            checks.append(('non-reconciling totals rejected', False))
        except SystemExit:
            checks.append(('non-reconciling totals rejected', True))
        # adversary: >2% unclassified time is rejected
        try:
            reconcile(10.0, {'UNCLASSIFIED': {'secs': 0.5}, 'OTHER': {'secs': 9.5}})
            checks.append(('excess unclassified rejected', False))
        except SystemExit:
            checks.append(('excess unclassified rejected', True))
    bad = [n for n, ok in checks if not ok]
    if bad:
        print(f'fido: witness-profile-attribution self-test FAILED — {", ".join(bad)}')
        return 1
    print(f'fido: witness-profile-attribution self-test OK — {len(checks)} controls '
          f'(classification, program grouping, reconciliation, truncation/tamper/unclassified adversaries)')
    return 0


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--source', action='append', default=[])
    ap.add_argument('--time-log', action='append', default=[])
    ap.add_argument('--basis')
    ap.add_argument('--outdir')
    ap.add_argument('--expect-sentences', type=int, default=500)
    a = ap.parse_args(argv[1:])
    if a.self_test:
        return self_test()
    if not (a.source and a.time_log and a.basis and a.outdir):
        ap.error('--source, --time-log, --basis, --outdir are required (or --self-test)')
    if len(a.source) != len(a.time_log):
        ap.error('each --source needs exactly one --time-log, in order')
    if not re.fullmatch(r'[0-9a-f]{64}', a.basis):
        raise SystemExit('attribution: --basis must be the 64-hex performance-input digest')
    records, total, rows, pops, progs = build_tables_multi(
        list(zip(a.source, a.time_log)), a.basis, a.expect_sentences)
    reconcile(total, pops)
    write_tables(a.outdir, a.basis, total, rows, pops, progs)
    print(f'fido: witness-profile-attribution OK — {len(records)} sentences / {total:.2f}s fully '
          f'attributed across {sum(p["count"] for p in pops.values())} declarations; population totals '
          f'reconcile; UNCLASSIFIED {pops.get("UNCLASSIFIED", {"secs": 0.0})["secs"]:.2f}s within the 2% law')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
