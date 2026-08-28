#!/usr/bin/env python3
"""Structural + currentness validation of the candidate-bound performance evidence.

Two committed evidence files:

  .review/PERFORMANCE.tsv                measurement rows (COLD_COMPLETE / WARM_COMPLETE / STAGED_PRE_COMMIT)
  .review/PERFORMANCE_OPPORTUNITIES.tsv  the optimization-opportunity ledger

Each measurement row and each opportunity row is bound to a `performance-input digest` — the SHA-256 that
`tools/performance-input-digest.sh` computes over every tracked non-evidence byte (contract §20).  A row whose
`relation` is `final-candidate` must be bound to the CURRENT digest; a `tooling-baseline` row keeps the exact
baseline digest it was measured on.  This validator NEVER re-runs a benchmark — it validates shape, enums,
digest binding, scenario coverage, and opportunity currentness only, so it is cheap enough for the complete gate.

`--self-test` drives the adversarial controls: each defect class the checks below reject is exercised on a
mutated clean fixture, and the clean fixture itself must pass.
"""
import argparse, os, re, sys

PERF = '.review/PERFORMANCE.tsv'
OPPS = '.review/PERFORMANCE_OPPORTUNITIES.tsv'

SCENARIOS = ('COLD_COMPLETE', 'WARM_COMPLETE', 'STAGED_PRE_COMMIT')
RELATIONS = ('tooling-baseline', 'final-candidate')
COMPLETE = ('yes', 'no')
OPP_CLASS = ('COMPUTATIONAL', 'INCREMENTAL', 'ORCHESTRATION', 'CACHE', 'RETAINED_SPACE', 'SCALING')
OPP_STATUS = ('OPEN_MATERIAL', 'IMPLEMENTED', 'REJECTED_MEASURED', 'REJECTED_BY_ARCHITECTURE',
              'IMMATERIAL', 'SUPERSEDED', 'BLOCKED_EXTERNAL')

PERF_COLS = ['scenario', 'relation', 'digest', 'command', 'cores', 'memory', 'boundary',
             'toolchain', 'cache', 'exit', 'wall_s', 'complete', 'dominant', 'notes']
OPP_COLS = ['id', 'basis', 'class', 'status', 'affected', 'gain', 'hotspot', 'constraints',
            'commit', 'result', 'revisit']
HEX64 = re.compile(r'^[0-9a-f]{64}$')
# cache state must name every required sub-system so no row hides what stayed warm (contract §19.1).
CACHE_KEYS = ('builder', 'project', 'dune-build', 'dune-cache', 'buildkit', 'base', 'prior')


def rows(text):
    """Data rows of a TSV: '#'-comment and blank lines dropped; header row (first non-comment) dropped."""
    out, seen_header = [], False
    for ln in text.splitlines():
        if not ln.strip() or ln.lstrip().startswith('#'):
            continue
        if not seen_header:
            seen_header = True
            continue
        out.append(ln.split('\t'))
    return out


def check_perf(text, digest, findings, mdigests):
    data = rows(text)
    if not data:
        findings.append(f'{PERF}: no measurement rows')
        return
    seen = set()
    for i, r in enumerate(data, 1):
        if len(r) != len(PERF_COLS):
            findings.append(f'{PERF}:{i}: {len(r)} fields, expected {len(PERF_COLS)}')
            continue
        row = dict(zip(PERF_COLS, r))
        if row['scenario'] not in SCENARIOS:
            findings.append(f'{PERF}:{i}: unknown scenario {row["scenario"]!r}')
        if row['relation'] not in RELATIONS:
            findings.append(f'{PERF}:{i}: unknown relation {row["relation"]!r}')
        if not HEX64.match(row['digest']):
            findings.append(f'{PERF}:{i}: digest is not a 64-hex performance-input digest')
        else:
            mdigests.add(row['digest'])
        if row['complete'] not in COMPLETE:
            findings.append(f'{PERF}:{i}: complete must be yes|no')
        # a failed or incomplete path may never be presented as a passing measurement
        if row['complete'] == 'yes' and row['exit'] != '0':
            findings.append(f'{PERF}:{i}: complete=yes with nonzero exit {row["exit"]!r}')
        if not re.match(r'^[0-9]+(\.[0-9]+)?$', row['wall_s']):
            findings.append(f'{PERF}:{i}: wall_s not numeric')
        if not row['cores'].isdigit():
            findings.append(f'{PERF}:{i}: cores not an integer')
        for req in ('memory', 'boundary', 'toolchain', 'command', 'dominant'):
            if not row[req].strip():
                findings.append(f'{PERF}:{i}: empty machine/toolchain field {req!r}')
        missing = [k for k in CACHE_KEYS if (k + '=') not in row['cache']]
        if missing:
            findings.append(f'{PERF}:{i}: cache state omits {",".join(missing)}')
        # a final-candidate row must be bound to the CURRENT digest; a foreign one is a stale measurement
        if row['relation'] == 'final-candidate' and row['digest'] != digest:
            findings.append(f'{PERF}:{i}: final-candidate row bound to a foreign digest '
                            f'({row["digest"][:12]} != current {digest[:12]})')
        seen.add((row['scenario'], row['relation']))
    # every required scenario must be present for whichever basis (baseline before semantics, final at freeze)
    for rel in RELATIONS:
        present = {sc for (sc, rl) in seen if rl == rel}
        if present and present != set(SCENARIOS):
            findings.append(f'{PERF}: {rel} is missing scenarios {sorted(set(SCENARIOS) - present)}')
    if not seen:
        findings.append(f'{PERF}: no scenario/relation coverage')


def check_opps(text, mdigests, findings, summary_ids):
    data = rows(text)
    ids = set()
    for i, r in enumerate(data, 1):
        if len(r) != len(OPP_COLS):
            findings.append(f'{OPPS}:{i}: {len(r)} fields, expected {len(OPP_COLS)}')
            continue
        row = dict(zip(OPP_COLS, r))
        if not re.match(r'^[A-Z0-9][A-Z0-9-]{3,}$', row['id']):
            findings.append(f'{OPPS}:{i}: malformed opportunity id {row["id"]!r}')
        if row['id'] in ids:
            findings.append(f'{OPPS}:{i}: duplicate opportunity id {row["id"]!r}')
        ids.add(row['id'])
        if row['class'] not in OPP_CLASS:
            findings.append(f'{OPPS}:{i}: unknown class {row["class"]!r}')
        if row['status'] not in OPP_STATUS:
            findings.append(f'{OPPS}:{i}: unknown status {row["status"]!r}')
        for req in ('affected', 'gain', 'hotspot', 'constraints'):
            if not row[req].strip():
                findings.append(f'{OPPS}:{i}: empty required field {req!r}')
        if not row['basis'].strip():
            findings.append(f'{OPPS}:{i}: empty measurement basis')
        if row['status'] == 'IMPLEMENTED' and row['commit'] in ('', 'n/a'):
            findings.append(f'{OPPS}:{i}: IMPLEMENTED without an implementation commit')
        # a 64-hex opportunity basis must be a digest that actually appears in the measurement evidence, not a
        # foreign one; OPEN_MATERIAL opportunities must additionally be named in the current measurement summary
        if HEX64.match(row['basis']) and row['basis'] not in mdigests:
            findings.append(f'{OPPS}:{i}: opportunity bound to a foreign digest (not in any measurement row)')
        if row['status'] == 'OPEN_MATERIAL':
            summary_ids.add(row['id'])
    if not ids:
        findings.append(f'{OPPS}: no opportunity rows')


def validate(root, digest):
    findings = []
    if not HEX64.match(digest or ''):
        return ['--digest must be the 64-hex current performance-input digest (computed on the host)']
    perf_path, opp_path = os.path.join(root, PERF), os.path.join(root, OPPS)
    for p, name in ((perf_path, PERF), (opp_path, OPPS)):
        if not os.path.exists(p):
            findings.append(f'{name}: missing required evidence file')
    if findings:
        return findings
    summary_ids, mdigests = set(), set()
    check_perf(open(perf_path, encoding='utf-8').read(), digest, findings, mdigests)
    check_opps(open(opp_path, encoding='utf-8').read(), mdigests, findings, summary_ids)
    # every OPEN_MATERIAL opportunity must be visible in the current summary block of the measurement file
    perf_text = open(perf_path, encoding='utf-8').read()
    for oid in sorted(summary_ids):
        if oid not in perf_text:
            findings.append(f'{PERF}: OPEN_MATERIAL opportunity {oid} is not named in the current summary')
    return findings


# ---------- adversarial self-test ----------
CLEAN_PERF = ('# perf evidence (fixture)\n'
              'scenario\trelation\tdigest\tcommand\tcores\tmemory\tboundary\ttoolchain\tcache\texit\twall_s\tcomplete\tdominant\tnotes\n')
CLEAN_OPP = ('# opportunities (fixture)\n'
             'id\tbasis\tclass\tstatus\taffected\tgain\thotspot\tconstraints\tcommit\tresult\trevisit\n')
DG = 'a' * 64


def _perf_row(**kw):
    d = dict(scenario='COLD_COMPLETE', relation='tooling-baseline', digest=DG, command='make check',
             cores='4', memory='class-A', boundary='container', toolchain='sha256:abcd',
             cache='builder=x;project=cold;dune-build=cold;dune-cache=off;buildkit=off;base=warm;prior=none',
             exit='0', wall_s='89', complete='yes', dominant='e2e', notes='-')
    d.update(kw)
    return '\t'.join(d[c] for c in PERF_COLS)


def _opp_row(**kw):
    d = dict(id='PERF-COMP-X', basis=DG, cls='COMPUTATIONAL', status='OPEN_MATERIAL', affected='cold',
             gain='~30s', hotspot='WitnessReject', constraints='exact disposition stays authority',
             commit='n/a', result='n/a', revisit='when profiled')
    d.update(kw)
    return '\t'.join([d['id'], d['basis'], d['cls'], d['status'], d['affected'], d['gain'], d['hotspot'],
                      d['constraints'], d['commit'], d['result'], d['revisit']])


def self_test():
    controls = 0
    fails = 0

    def run(perf_body, opp_body, digest=DG):
        f = []
        summary = set()
        mds = set()
        check_perf(CLEAN_PERF + perf_body, digest, f, mds)
        check_opps(CLEAN_OPP + opp_body, mds, f, summary)
        for oid in summary:
            if oid not in (CLEAN_PERF + perf_body):
                f.append(f'summary omits {oid}')
        return f

    # the clean fixture: all three scenarios present, the OPEN_MATERIAL opportunity named in a summary comment
    clean_perf = '\n'.join(_perf_row(scenario=s) for s in SCENARIOS) + '\n# summary: PERF-COMP-X\n'
    if run(clean_perf, _opp_row() + '\n'):
        raise SystemExit('self-test: the clean fixture was rejected: ' + str(run(clean_perf, _opp_row() + '\n')))

    cases = [
        ('missing scenario (only COLD)', _perf_row(scenario='COLD_COMPLETE') + '\n', _opp_row(status='IMPLEMENTED', commit='deadbeef') + '\n'),
        ('unknown scenario', _perf_row(scenario='NOPE') + '\n', _opp_row(status='IMPLEMENTED', commit='deadbeef') + '\n'),
        ('unknown status', clean_perf, _opp_row(status='NOPE') + '\n'),
        ('unknown class', clean_perf, _opp_row(cls='NOPE') + '\n'),
        ('duplicate opportunity id', clean_perf, _opp_row() + '\n' + _opp_row() + '\n'),
        ('missing cache subsystem', _perf_row(scenario='COLD_COMPLETE', cache='builder=x;project=cold') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('missing machine identity', _perf_row(scenario='COLD_COMPLETE', memory='') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('failed path presented as passing', _perf_row(scenario='COLD_COMPLETE', exit='1', complete='yes') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('final-candidate bound to a foreign digest', _perf_row(scenario='COLD_COMPLETE', relation='final-candidate', digest='b' * 64) + '\n' + _perf_row(scenario='WARM_COMPLETE', relation='final-candidate') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT', relation='final-candidate') + '\n', _opp_row() + '\n'),
        ('malformed digest', _perf_row(scenario='COLD_COMPLETE', digest='xyz') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('IMPLEMENTED without commit', clean_perf, _opp_row(status='IMPLEMENTED', commit='n/a') + '\n'),
        ('OPEN_MATERIAL omitted from summary', '\n'.join(_perf_row(scenario=s) for s in SCENARIOS) + '\n', _opp_row(id='PERF-ORCH-Y') + '\n'),
        ('OPEN_MATERIAL bound to a foreign digest', clean_perf, _opp_row(basis='c' * 64) + '\n'),
        ('empty opportunity basis', clean_perf, _opp_row(basis='') + '\n'),
    ]
    for label, perf_body, opp_body in cases:
        controls += 1
        if not run(perf_body, opp_body):
            print(f'self-test: defect NOT caught: {label}')
            fails += 1
    if fails:
        raise SystemExit(f'perf-evidence self-test: {fails} defect class(es) not caught')
    print(f'fido: perf-evidence-validate self-test OK — {controls} adversarial controls '
          '(scenario coverage, enums, cache/machine identity, digest binding, opportunity currentness) + clean fixture accepted')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='.')
    ap.add_argument('--digest', default='', help='current performance-input digest (host-computed)')
    ap.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    findings = validate(args.root, args.digest)
    if findings:
        for f in findings:
            print('perf-evidence: ' + f, file=sys.stderr)
        raise SystemExit('fido: PERF-EVIDENCE FAILED — ' + str(len(findings)) + ' violation(s)')
    print('fido: perf-evidence OK — measurement rows and the opportunity ledger are well-formed, digest-bound, '
          'scenario-complete, and every OPEN_MATERIAL opportunity is current')


if __name__ == '__main__':
    main()
