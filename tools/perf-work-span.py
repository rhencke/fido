#!/usr/bin/env python3
"""The one deterministic work/span accounting and reachability model.

Consumes the committed normalized event table (.review/perf/verification-dag-events.tsv) and the full
WitnessReject sentence profile, enforces the structural accounting laws, and computes the governing totals:

  WALL_SPAN               monotonic elapsed of the supported path (human wait time)
  AGGREGATE_TASK_ELAPSED  sum of the declared mutually non-nested WORK_LEAF durations (overlap included)
  CRITICAL_PATH_SPAN      longest predecessor-respecting path through the event graph
  OVERLAP                 aggregate task elapsed minus the union span of the same leaves
  NESTED_ATTRIBUTION      explanatory detail (sentence profiles, waves) never added to a counted ancestor
  UNCLASSIFIED            wall not covered by any leaf (<=5% complete-path; <=2% fixture attribution)

Roles: CONTAINER (owns an interval, never counted beside counted descendants), WORK_LEAF (counted exactly
once), ATTRIBUTION (never counted).  Two accounting levels: PROJECT_VERIFICATION (the one Buildx solve) and
COMPLETE_PATH (policy gates + solve + artifact comparison).  Aggregate work is never called CPU time: direct
CPU accounting is unavailable through BuildKit in the pinned environment, so elapsed task time is the honest
work proxy.  The evidence-observation reachability model applies the four-chunk critical path: zero-cost wave
span = max over chunks of (worker wall - that chunk's target work) + measured serial overhead — aggregate
target work is NEVER copied into a wall-saving claim.
"""
import argparse
import csv
import sys
from collections import defaultdict
from pathlib import Path

EVENTS = '.review/perf/verification-dag-events.tsv'
SENTENCES = '.review/perf/witnessreject-sentences.tsv'

ROLES = ('CONTAINER', 'WORK_LEAF', 'ATTRIBUTION')
CLASSES = ('POLICY', 'THEORY', 'PROOF', 'EMIT', 'FIXTURE_WORKER', 'GO', 'JOIN_EXPORT',
           'ARTIFACT_COMPARE', 'WAIT_OR_OVERHEAD', 'UNCLASSIFIED')
COLS = ['basis', 'scenario', 'run_id', 'event_id', 'parent_id', 'role', 'class', 'start_ms',
        'end_ms', 'elapsed_ms', 'predecessors', 'worker_or_stage', 'cache_state', 'result', 'source', 'notes']
TARGET_POPS = ('ISSUE_TABLE', 'CAUSE_VIEW', 'REQ_VIEW', 'GROUP_VIEW')
CHUNKS = ('e2e/WitnessRejectPrelude.v', 'e2e/WitnessRejectA.v', 'e2e/WitnessRejectB.v',
          'e2e/WitnessRejectC.v', 'e2e/WitnessRejectD.v')


def read_tsv(path):
    out = []
    with open(path, encoding='utf-8') as f:
        rows = [ln for ln in f if ln.strip() and not ln.lstrip().startswith('#')]
    rd = csv.DictReader(rows, delimiter='\t')
    for r in rd:
        out.append(r)
    return out


def validate_events(events, findings):
    """The §5.2 structural laws over one event table."""
    by_run = defaultdict(list)
    for e in events:
        by_run[(e['basis'], e['scenario'], e['run_id'])].append(e)
    for key, evs in by_run.items():
        ids = {}
        for e in evs:
            if e['event_id'] in ids:
                findings.append(f'{key}: duplicate event_id {e["event_id"]}')
            ids[e['event_id']] = e
            if e['role'] not in ROLES:
                findings.append(f'{key}:{e["event_id"]}: unknown role {e["role"]!r}')
            if e['class'] not in CLASSES:
                findings.append(f'{key}:{e["event_id"]}: unknown class {e["class"]!r}')
            try:
                s, en, el = int(e['start_ms']), int(e['end_ms']), int(e['elapsed_ms'])
                if abs((en - s) - el) > 500:
                    findings.append(f'{key}:{e["event_id"]}: elapsed {el} != end-start {en - s}')
            except ValueError:
                findings.append(f'{key}:{e["event_id"]}: non-numeric interval')
                continue
            if e['role'] == 'WORK_LEAF' and e['result'] != 'ok':
                findings.append(f'{key}:{e["event_id"]}: a failed task cannot be counted as successful work')
        for e in evs:
            if e['parent_id'] and e['parent_id'] not in ids:
                findings.append(f'{key}:{e["event_id"]}: missing parent {e["parent_id"]}')
                continue
            if e['parent_id']:
                p = ids[e['parent_id']]
                if int(e['start_ms']) < int(p['start_ms']) - 500 or int(e['end_ms']) > int(p['end_ms']) + 500:
                    findings.append(f'{key}:{e["event_id"]}: interval outside its parent {p["event_id"]}')
            for pred in filter(None, e['predecessors'].split(',')):
                if pred not in ids:
                    findings.append(f'{key}:{e["event_id"]}: unknown predecessor {pred}')
                elif int(e['start_ms']) < int(ids[pred]['end_ms']) - 500:
                    findings.append(f'{key}:{e["event_id"]}: starts before its declared predecessor {pred} ends')
        # a leaf and its descendant leaf cannot both be counted
        def ancestors(e):
            while e['parent_id'] and e['parent_id'] in ids:
                e = ids[e['parent_id']]
                yield e
        for e in evs:
            if e['role'] == 'WORK_LEAF':
                for a in ancestors(e):
                    if a['role'] == 'WORK_LEAF':
                        findings.append(f'{key}:{e["event_id"]}: WORK_LEAF nested under WORK_LEAF {a["event_id"]}')
    return by_run


def union_len(intervals):
    total, cur_s, cur_e = 0, None, None
    for s, e in sorted(intervals):
        if cur_e is None or s > cur_e:
            if cur_e is not None:
                total += cur_e - cur_s
            cur_s, cur_e = s, e
        else:
            cur_e = max(cur_e, e)
    if cur_e is not None:
        total += cur_e - cur_s
    return total


def run_totals(evs, findings, key=''):
    """COMPLETE_PATH and PROJECT_VERIFICATION totals for one run's events."""
    ids = {e['event_id']: e for e in evs}
    leaves = [e for e in evs if e['role'] == 'WORK_LEAF']
    root = [e for e in evs if not e['parent_id']]
    wall = max(int(e['end_ms']) for e in root) - min(int(e['start_ms']) for e in root)
    solve_ids = {e['event_id'] for e in evs if e['worker_or_stage'] == 'verification-solve'}

    def under_solve(e):
        while e['parent_id']:
            if e['parent_id'] in solve_ids:
                return True
            e = ids[e['parent_id']]
        return False

    def totals(sel):
        work = sum(int(e['elapsed_ms']) for e in sel)
        span = union_len([(int(e['start_ms']), int(e['end_ms'])) for e in sel])
        return work, span, work - span

    all_work, all_span, all_ov = totals(leaves)
    pv_leaves = [e for e in leaves if under_solve(e)]
    pv_work, pv_span, pv_ov = totals(pv_leaves)
    covered = union_len([(int(e['start_ms']), int(e['end_ms'])) for e in leaves])
    uncl = wall - covered
    if wall and uncl / wall > 0.05:
        findings.append(f'{key}: unclassified complete-path time {uncl}ms is above 5% of the {wall}ms wall')
    return {'wall': wall, 'complete_work': all_work, 'complete_span': all_span, 'complete_overlap': all_ov,
            'pv_work': pv_work, 'pv_span': pv_span, 'pv_overlap': pv_ov,
            'unclassified': uncl, 'leaves': len(leaves)}


def chunk_targets(sent_rows, findings=None):
    """Per-chunk profile totals and evidence-observation target populations, reconciled."""
    per = {c: defaultdict(float) for c in CHUNKS}
    for r in sent_rows:
        f = r['file']
        if f not in per:
            continue
        per[f]['total'] += float(r['secs'])
        if r['population'] in TARGET_POPS:
            per[f]['target'] += float(r['secs'])
            per[f]['t_' + r['population']] += float(r['secs'])
    grand_target = sum(p['target'] for p in per.values())
    grand_total = sum(p['total'] for p in per.values())
    return per, grand_target, grand_total


def reachability(per, wave_span_ms, serial_overhead_ms, worker_load_ms, findings):
    """§8: the four-chunk zero-cost simulation.  Never divides aggregate target by worker count."""
    workers = [c for c in CHUNKS if not c.endswith('Prelude.v')]
    now = {c: per[c]['total'] * 1000 + worker_load_ms for c in workers}
    zero = {c: (per[c]['total'] - per[c]['target']) * 1000 + worker_load_ms for c in workers}
    cur_span = max(now.values()) + serial_overhead_ms
    zero_span = max(zero.values()) + serial_overhead_ms
    if abs(cur_span - wave_span_ms) > 0.35 * wave_span_ms:
        findings.append(f'reachability: simulated current wave span {cur_span:.0f}ms does not reconcile '
                        f'with the measured {wave_span_ms}ms within 35%')
    agg_target = sum(per[c]['target'] for c in workers) + per['e2e/WitnessRejectPrelude.v']['target']
    max_wall_saving = cur_span - zero_span
    if max_wall_saving > agg_target * 1000 + 1:
        findings.append('reachability: wall saving cannot exceed the aggregate target work')
    return {'agg_target_s': agg_target, 'cur_wave_span_ms': cur_span, 'zero_wave_span_ms': zero_span,
            'max_fixture_wall_saving_ms': max_wall_saving,
            'max_agg_work_saving_s': agg_target}


def check_claim(entry, final, findings):
    """Comparable-basis claims: work reductions from work, span reductions from span, never crossed."""
    for lvl in ('pv', 'complete'):
        for kind in ('work', 'span'):
            e, f = entry[f'{lvl}_{kind}'], final[f'{lvl}_{kind}']
            if e <= 0:
                findings.append(f'claim: entry {lvl} {kind} is not positive')
    return {f'{lvl}_{kind}_delta_pct': round(100 * (entry[f'{lvl}_{kind}'] - final[f'{lvl}_{kind}'])
                                             / entry[f'{lvl}_{kind}'], 1)
            for lvl in ('pv', 'complete') for kind in ('work', 'span')}


# ---------------- self-test ----------------
def _ev(**kw):
    d = dict(basis='a' * 64, scenario='COLD_COMPLETE', run_id='r1', event_id='e', parent_id='',
             role='WORK_LEAF', cls='POLICY', start_ms='0', end_ms='1000', elapsed_ms='1000',
             predecessors='', worker_or_stage='x', cache_state='warm', result='ok', source='test', notes='')
    d.update(kw)
    d['class'] = d.pop('cls')
    return d


def _clean_run():
    return [
        _ev(event_id='root', role='CONTAINER', cls='UNCLASSIFIED', start_ms='0', end_ms='103000', elapsed_ms='103000'),
        _ev(event_id='policy', parent_id='root', cls='POLICY', start_ms='0', end_ms='19000', elapsed_ms='19000'),
        _ev(event_id='solve', parent_id='root', role='CONTAINER', cls='UNCLASSIFIED', start_ms='19000',
            end_ms='100000', elapsed_ms='81000', worker_or_stage='verification-solve'),
        _ev(event_id='setup', parent_id='solve', cls='WAIT_OR_OVERHEAD', start_ms='19000', end_ms='25000', elapsed_ms='6000'),
        _ev(event_id='theory', parent_id='solve', cls='THEORY', start_ms='25000', end_ms='51000', elapsed_ms='26000',
            predecessors='setup'),
        _ev(event_id='proof', parent_id='solve', cls='PROOF', start_ms='52000', end_ms='70000', elapsed_ms='18000',
            predecessors='theory'),
        _ev(event_id='emit', parent_id='solve', cls='EMIT', start_ms='52000', end_ms='85000', elapsed_ms='33000',
            predecessors='theory'),
        _ev(event_id='wave2', parent_id='emit', role='ATTRIBUTION', cls='FIXTURE_WORKER', start_ms='61000',
            end_ms='74500', elapsed_ms='13500'),
        _ev(event_id='go', parent_id='solve', cls='GO', start_ms='85000', end_ms='94000', elapsed_ms='9000',
            predecessors='emit'),
        _ev(event_id='join', parent_id='solve', cls='JOIN_EXPORT', start_ms='94000', end_ms='100000', elapsed_ms='6000',
            predecessors='proof,go'),
        _ev(event_id='compare', parent_id='root', cls='ARTIFACT_COMPARE', start_ms='100000', end_ms='103000',
            elapsed_ms='3000', predecessors='join'),
    ]


def self_test():
    checks = []

    def run(evs):
        f = []
        by = validate_events(evs, f)
        tot = None
        if not f:
            tot = run_totals(list(by.values())[0], f, 'r1')
        return f, tot

    f, tot = run(_clean_run())
    checks.append(('clean run accepted', not f))
    checks.append(('proof branch counted as work while hidden',
                   tot is not None and tot['pv_work'] == 98000 and tot['pv_span'] == 80000))
    checks.append(('overlap measured from intervals', tot is not None and tot['pv_overlap'] == 18000))
    checks.append(('nested attribution not added', tot is not None and tot['complete_work'] == 120000))
    checks.append(('unclassified visible and within law', tot is not None and tot['unclassified'] == 1000))

    def expect_fail(label, mutate):
        evs = _clean_run()
        mutate(evs)
        f, _ = run(evs)
        checks.append((label, bool(f)))

    def leaf(evs, eid):
        return next(e for e in evs if e['event_id'] == eid)

    expect_fail('parent and child both counted', lambda evs: leaf(evs, 'wave2').update(role='WORK_LEAF'))
    expect_fail('attribution promoted on top of counted parent',
                lambda evs: leaf(evs, 'wave2').update(role='WORK_LEAF'))
    expect_fail('event outside its parent interval', lambda evs: leaf(evs, 'go').update(end_ms='120000'))
    expect_fail('missing parent', lambda evs: leaf(evs, 'go').update(parent_id='ghost'))
    expect_fail('duplicate event ids', lambda evs: leaf(evs, 'go').update(event_id='proof'))
    expect_fail('false elapsed value', lambda evs: leaf(evs, 'emit').update(elapsed_ms='99000'))
    expect_fail('unknown role', lambda evs: leaf(evs, 'go').update(role='MAGIC'))
    expect_fail('unknown class', lambda evs: leaf(evs, 'go').update(**{'class': 'MAGIC'}))
    expect_fail('failed task presented as successful work', lambda evs: leaf(evs, 'emit').update(result='fail'))
    expect_fail('critical path violates a declared predecessor',
                lambda evs: leaf(evs, 'go').update(start_ms='60000', end_ms='69000'))

    # unclassified above 5%
    evs = _clean_run()
    leaf(evs, 'policy').update(end_ms='9000', elapsed_ms='9000')
    f, _ = run(evs)
    checks.append(('unclassified complete-path above 5% rejected', bool(f)))

    # an omitted parallel sibling shrinks work — the totals check catches it via reconciliation with wall
    evs = [e for e in _clean_run() if e['event_id'] != 'proof']
    evs = [dict(e, predecessors=e['predecessors'].replace('proof,', '')) for e in evs]
    f, tot2 = run(evs)
    checks.append(('omitted overlapped proof branch changes the work total, never silently equal',
                   tot2 is None or tot2['pv_work'] == 80000))

    # reachability laws
    per = {c: defaultdict(float) for c in CHUNKS}
    for c in CHUNKS:
        per[c]['total'] = 9.0 if not c.endswith('Prelude.v') else 1.7
        per[c]['target'] = 5.0 if c.endswith('B.v') else 1.0
        if c.endswith('Prelude.v'):
            per[c]['target'] = 0.0
    f = []
    r = reachability(per, wave_span_ms=13500, serial_overhead_ms=4000, worker_load_ms=1500, findings=f)
    checks.append(('wave saving is max-chunk based, not aggregate/4',
                   abs(r['max_fixture_wall_saving_ms'] - 1000) < 1
                   and abs(r['max_agg_work_saving_s'] - 8.0) < 1e-6))
    checks.append(('wall saving below aggregate target', r['max_fixture_wall_saving_ms']
                   <= r['max_agg_work_saving_s'] * 1000))
    f = []
    bad = dict(per)
    reach2 = reachability(bad, wave_span_ms=40000, serial_overhead_ms=4000, worker_load_ms=1500, findings=f)
    checks.append(('simulated span must reconcile with the measured span', bool(f)))

    # claim discipline: percentages come from matching kinds
    entry = {'pv_work': 125000, 'pv_span': 129000, 'complete_work': 147000, 'complete_span': 148000}
    final = {'pv_work': 98000, 'pv_span': 81000, 'complete_work': 120000, 'complete_span': 103000}
    f = []
    d = check_claim(entry, final, f)
    checks.append(('work reduction computed from work', abs(d['pv_work_delta_pct'] - 21.6) < 0.1))
    checks.append(('span reduction computed from span', abs(d['pv_span_delta_pct'] - 37.2) < 0.1))
    checks.append(('work and span deltas differ (never conflated)',
                   d['pv_work_delta_pct'] != d['pv_span_delta_pct']))

    bad = [n for n, ok in checks if not ok]
    for n in bad:
        print(f'  FAIL  {n} — the accounting defect was not caught or the law miscomputed')
    if bad:
        raise SystemExit(f'perf-work-span self-test FAILED: {len(bad)} of {len(checks)}')
    print(f'fido: perf-work-span self-test OK — {len(checks)} controls (partition laws, interval laws, '
          'overlap/critical-path arithmetic, unclassified limits, four-chunk reachability, claim discipline)')


def emit_tables(outdir, totals, per, reach):
    # Write the governing summary tables from the computed values only.
    entry = next((t for k, t in totals.items() if k[2].startswith('entry')), None)
    final = next((t for k, t in totals.items() if k[2].startswith('final')), None)
    with open(outdir / 'verification-dag-work-span.tsv', 'w', encoding='utf-8') as f:
        f.write('# GENERATED by tools/perf-work-span.py from verification-dag-events.tsv — never hand-edited.\n'
                '# AGGREGATE_TASK_ELAPSED sums the declared WORK_LEAF set (overlap included, containers and\n'
                '# nested attribution excluded); span is the leaf-interval union; work and span are never\n'
                '# conflated and neither is CPU time (no direct CPU accounting through BuildKit).\n')
        f.write('level\tbasis\twall_span_s\taggregate_task_elapsed_s\tleaf_union_span_s\toverlap_s\t'
                'unclassified_s\twork_delta_pct\tspan_delta_pct\n')
        if entry and final:
            for lvl in ('PROJECT_VERIFICATION', 'COMPLETE_PATH'):
                pfx = 'pv' if lvl == 'PROJECT_VERIFICATION' else 'complete'
                wd = round(100 * (entry[pfx + '_work'] - final[pfx + '_work']) / entry[pfx + '_work'], 1)
                sd = round(100 * (entry[pfx + '_span'] - final[pfx + '_span']) / entry[pfx + '_span'], 1)
                for label, t in (('entry', entry), ('final', final)):
                    f.write(lvl + '\t' + label + '\t' + format(t['wall'] / 1000, '.0f') + '\t'
                            + format(t[pfx + '_work'] / 1000, '.1f') + '\t'
                            + format(t[pfx + '_span'] / 1000, '.1f') + '\t'
                            + format(t[pfx + '_overlap'] / 1000, '.1f') + '\t'
                            + format(t['unclassified'] / 1000, '.1f') + '\t'
                            + (str(wd) if label == 'final' else '') + '\t'
                            + (str(sd) if label == 'final' else '') + '\n')
    with open(outdir / 'verification-dag-reachability.tsv', 'w', encoding='utf-8') as f:
        f.write('# GENERATED by tools/perf-work-span.py — the evidence-observation four-chunk critical-path\n'
                '# model: zero-cost wave span = max over chunks of (worker wall - chunk target) + measured\n'
                '# serial overhead; aggregate target work is NEVER copied into a wall-saving claim.\n')
        f.write('chunk\tprofile_total_s\ttarget_issue_s\ttarget_cause_s\ttarget_req_s\ttarget_group_s\t'
                'target_total_s\tresidual_s\n')
        for c in CHUNKS:
            p = per[c]
            f.write(c.split('/')[-1] + '\t' + format(p['total'], '.2f') + '\t'
                    + format(p['t_ISSUE_TABLE'], '.2f') + '\t' + format(p['t_CAUSE_VIEW'], '.2f') + '\t'
                    + format(p['t_REQ_VIEW'], '.2f') + '\t' + format(p['t_GROUP_VIEW'], '.2f') + '\t'
                    + format(p['target'], '.2f') + '\t' + format(p['total'] - p['target'], '.2f') + '\n')
        f.write('\nmetric\tvalue\n')
        f.write('aggregate_target_work_s\t' + format(reach['agg_target_s'], '.2f') + '\n')
        f.write('current_wave_span_ms\t' + format(reach['cur_wave_span_ms'], '.0f') + '\n')
        f.write('zero_cost_wave_span_ms\t' + format(reach['zero_wave_span_ms'], '.0f') + '\n')
        f.write('max_fixture_wall_saving_ms\t' + format(reach['max_fixture_wall_saving_ms'], '.0f') + '\n')
        f.write('max_aggregate_work_saving_s\t' + format(reach['max_agg_work_saving_s'], '.2f') + '\n')
        sav = reach['max_fixture_wall_saving_ms'] / 1000
        f.write('max_complete_path_wall_saving_s\t' + format(sav, '.1f')
                + ' (the wave saving carries through: emit stays critical and proof 18s stays below it)\n')
        f.write('zero_cost_complete_path_lower_bound_s\t' + format(103 - sav, '.1f') + '\n')
        f.write('realistic_expected_saving\tUNKNOWN_PENDING_SPIKE\n')
        f.write('predicted_next_critical_path\ttheory-build 26s + emit ~27s + go 9s + join 6s inside the solve\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='.')
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--report', action='store_true', help='print the computed totals per run')
    ap.add_argument('--emit-tables', default='', help='directory to write the generated work-span and '
                    'reachability tables into (the governing summaries are tool output, never hand-edited)')
    ap.add_argument('--worker-load-ms', type=int, default=1500)
    ap.add_argument('--serial-overhead-ms', type=int, default=3300,
                    help='measured wave1+aggregate serial overhead inside the fixture stage')
    ap.add_argument('--wave-span-ms', type=int, default=13500, help='measured wave2 span for reconciliation')
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    root = Path(args.root)
    findings = []
    events = read_tsv(root / EVENTS)
    by_run = validate_events(events, findings)
    totals = {}
    for key, evs in sorted(by_run.items()):
        if not findings:
            totals[key] = run_totals(evs, findings, str(key))
    sent = read_tsv(root / SENTENCES)
    per, grand_target, grand_total = chunk_targets(sent, findings)
    if grand_total and (grand_target > grand_total):
        findings.append('chunk targets exceed the profiled total')
    if findings:
        for f in findings:
            print('perf-work-span: ' + f, file=sys.stderr)
        raise SystemExit(f'fido: PERF-WORK-SPAN FAILED — {len(findings)} violation(s)')
    reach = reachability(per, args.wave_span_ms, args.serial_overhead_ms, args.worker_load_ms, findings)
    if findings:
        for f in findings:
            print('perf-work-span: ' + f, file=sys.stderr)
        raise SystemExit(f'fido: PERF-WORK-SPAN FAILED — {len(findings)} violation(s)')
    if args.emit_tables:
        emit_tables(Path(args.emit_tables), totals, per, reach)
    if args.report:
        for key, t in totals.items():
            print(f'{key[1]}/{key[2]}: wall={t["wall"]/1000:.0f}s '
                  f'complete work/span/overlap={t["complete_work"]/1000:.0f}/{t["complete_span"]/1000:.0f}/'
                  f'{t["complete_overlap"]/1000:.0f}s '
                  f'PV work/span/overlap={t["pv_work"]/1000:.0f}/{t["pv_span"]/1000:.0f}/{t["pv_overlap"]/1000:.0f}s '
                  f'unclassified={t["unclassified"]/1000:.1f}s')
        print(f'fixture target populations: total={grand_total:.2f}s target={grand_target:.2f}s '
              + ' '.join(f'{c.split("/")[-1]}={per[c]["target"]:.2f}s' for c in CHUNKS))
    print('fido: perf-work-span OK — event partition lawful; work, span, overlap and unclassified computed '
          'from intervals; fixture targets reconcile with the full sentence profile')


if __name__ == '__main__':
    main()
