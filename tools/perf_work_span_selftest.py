#!/usr/bin/env python3
"""Adversarial self-tests for the accounting/series/reachability owner (imported by perf-work-span.py).

Each control writes a synthetic candidate tree (registry, status ledger, event graphs, sentences) and runs
the real validate() over it, mutating exactly one condition and requiring the exact owning rule to reject
it: the governed series is selected only from the status ledger's exact relation/scenario/basis (never a
run-name prefix); status rows and event graphs are in exact RunKey bijection; the current cold series needs
at least three uniform runs and uses the standard median; the historical comparison is the exact
comparison-baseline row; timing precision cannot exceed its declared source; attribution role/class is
exact.
"""
import tempfile
from pathlib import Path

DGC = 'c' * 64   # synthetic CURRENT basis (ONE_DAG_CHUNK_TIMED_V2 @ d2f9...)
DGH = 'h' * 64   # synthetic HISTORICAL comparison basis (THREE_SOLVE_POST_CHUNKING_V1)
SHA_H = 'a' * 40
SHA_C = 'b' * 40

EV_COLS = ['basis', 'scenario', 'run_id', 'event_id', 'parent_id', 'role', 'class', 'start_ms',
           'end_ms', 'elapsed_ms', 'predecessors', 'worker_or_stage', 'cache_state', 'result',
           'source', 'notes', 'clock', 'resolution_ms']
PERF_COLS = ['scenario', 'relation', 'digest', 'command', 'cores', 'memory', 'boundary', 'toolchain',
             'cache', 'exit', 'wall_s', 'complete', 'dominant', 'notes', 'run_id']
CACHE_COLD = ('builder=fido-builder;project=cold;dune-build=cold;dune-cache=off;'
              'buildkit=project-stages-invalidated;base=primed;prior=none')


def _e(basis, run, eid, parent, role, cls, s, en, preds='', stage='', result='ok',
       clock='DERIVED', res='1000'):
    return {'basis': basis, 'scenario': 'COLD_COMPLETE', 'run_id': run, 'event_id': eid,
            'parent_id': parent, 'role': role, 'class': cls, 'start_ms': str(s), 'end_ms': str(en),
            'elapsed_ms': str(en - s), 'predecessors': preds, 'worker_or_stage': stage,
            'cache_state': 'cold', 'result': result, 'source': 'stage-timer', 'notes': '',
            'clock': clock, 'resolution_ms': res}


def _one_dag(run, basis=DGC, wall=100000, worker_ends=None):
    we = worker_ends or {'chunk-A': 82330, 'chunk-B': 81990, 'chunk-C': 82340, 'chunk-D': 82840}
    evs = [
        _e(basis, run, 'root', '', 'CONTAINER', 'UNCLASSIFIED', 0, wall, clock='HOST_SECONDS'),
        _e(basis, run, 'policy', 'root', 'WORK_LEAF', 'POLICY', 0, 19000, clock='HOST_SECONDS'),
        _e(basis, run, 'solve', 'root', 'CONTAINER', 'UNCLASSIFIED', 19000, wall - 4000,
           preds='policy', stage='verification-solve'),
        _e(basis, run, 'setup', 'solve', 'WORK_LEAF', 'WAIT_OR_OVERHEAD', 19000, 28000, preds='policy'),
        _e(basis, run, 'theory', 'solve', 'WORK_LEAF', 'THEORY', 28000, 54000, preds='setup'),
        _e(basis, run, 'proof', 'solve', 'WORK_LEAF', 'PROOF', 55000, 73000, preds='theory'),
        _e(basis, run, 'emit', 'solve', 'WORK_LEAF', 'EMIT', 55000, 88000, preds='theory'),
        _e(basis, run, 'go', 'solve', 'WORK_LEAF', 'GO', 88000, wall - 6000, preds='emit'),
        _e(basis, run, 'join', 'solve', 'WORK_LEAF', 'JOIN_EXPORT', wall - 6000, wall - 4000,
           preds='proof,go'),
        _e(basis, run, 'compare', 'root', 'WORK_LEAF', 'ARTIFACT_COMPARE', wall - 4000, wall,
           preds='join', clock='HOST_SECONDS'),
    ]
    for tag, end in we.items():
        evs.append(_e(basis, run, tag, 'emit', 'ATTRIBUTION', 'FIXTURE_WORKER', 70000, end,
                      stage=tag, clock='PROC_UPTIME_10MS', res='10'))
    return evs


def _three_solve(run='entry-cold-1'):
    seq = [('policy', 'POLICY', 0, 19000, '', 'host', 'root'),
           ('p-context', 'WAIT_OR_OVERHEAD', 19000, 36000, 'policy', 'ctx', 's1'),
           ('p-dune', 'THEORY', 36000, 63500, 'p-context', 'dune', 's1'),
           ('p-gates', 'PROOF', 63500, 77200, 'p-dune', 'gates', 's1'),
           ('p-tail', 'WAIT_OR_OVERHEAD', 77200, 87000, 'p-gates', 'exp', 's1'),
           ('e-context', 'WAIT_OR_OVERHEAD', 87000, 95000, 'p-tail', 'ctx', 's2'),
           ('e-dune', 'THEORY', 95000, 99500, 'e-context', 'dune', 's2'),
           ('e-emit', 'EMIT', 99500, 136000, 'p-gates,e-dune', 'emit', 's2'),
           ('e-go', 'GO', 136000, 145000, 'e-emit', 'go', 's2')]
    evs = [_e(DGH, run, 'root', '', 'CONTAINER', 'UNCLASSIFIED', 0, 148000, clock='HOST_SECONDS'),
           _e(DGH, run, 's1', 'root', 'CONTAINER', 'UNCLASSIFIED', 19000, 87000, preds='policy',
              stage='verification-solve'),
           _e(DGH, run, 's2', 'root', 'CONTAINER', 'UNCLASSIFIED', 87000, 145000, preds='s1',
              stage='verification-solve'),
           _e(DGH, run, 'art', 'root', 'WORK_LEAF', 'JOIN_EXPORT', 145000, 148000, preds='e-go',
              stage='verification-solve', clock='HOST_SECONDS')]
    for eid, cls, s, en, preds, stage, parent in seq:
        role = 'WORK_LEAF'
        clk = 'HOST_SECONDS' if eid == 'policy' else 'DERIVED'
        evs.append(_e(DGH, run, eid, parent, role, cls, s, en, preds=preds, stage=stage, clock=clk))
    return evs


def _perf(scenario, relation, digest, run_id='-', wall='100', cores='4', memory='15GB',
          boundary='container', toolchain='sha256:tc', cache=CACHE_COLD, command='make check'):
    return {'scenario': scenario, 'relation': relation, 'digest': digest, 'command': command,
            'cores': cores, 'memory': memory, 'boundary': boundary, 'toolchain': toolchain,
            'cache': cache, 'exit': '0', 'wall_s': wall, 'complete': 'yes', 'dominant': 'emit',
            'notes': '-', 'run_id': run_id}


def _bases():
    return [{'basis_digest': DGH, 'source_commit': SHA_H,
             'topology_id': 'THREE_SOLVE_POST_CHUNKING_V1', 'status': 'HISTORICAL',
             'purpose': 'comparison', 'notes': ''},
            {'basis_digest': DGC, 'source_commit': SHA_C, 'topology_id': 'ONE_DAG_CHUNK_TIMED_V2',
             'status': 'CURRENT', 'purpose': 'final', 'notes': ''}]


def _sentences():
    rows = []
    for f, tot, targ in (('e2e/WitnessRejectPrelude.v', 1.8, 0.0), ('e2e/WitnessRejectA.v', 9.5, 8.1),
                         ('e2e/WitnessRejectB.v', 9.3, 5.6), ('e2e/WitnessRejectC.v', 9.3, 5.3),
                         ('e2e/WitnessRejectD.v', 10.4, 4.2)):
        rows.append({'basis': DGC, 'file': f, 'secs': f'{targ:.3f}', 'population': 'ISSUE_TABLE'})
        rows.append({'basis': DGC, 'file': f, 'secs': f'{tot - targ:.3f}', 'population': 'VERDICT_ONLY'})
    return rows


def _write(root, bases, perf, events, sents):
    perf_dir = root / '.review/perf'
    perf_dir.mkdir(parents=True, exist_ok=True)

    def tsv(path, cols, rows):
        with open(path, 'w', encoding='utf-8') as f:
            f.write('\t'.join(cols) + '\n')
            for r in rows:
                f.write('\t'.join(str(r[c]) for c in cols) + '\n')

    tsv(perf_dir / 'performance-bases.tsv',
        ['basis_digest', 'source_commit', 'topology_id', 'status', 'purpose', 'notes'], bases)
    tsv(root / '.review/PERFORMANCE.tsv', PERF_COLS, perf)
    tsv(perf_dir / 'verification-dag-events.tsv', EV_COLS, events)
    tsv(perf_dir / 'witnessreject-sentences.tsv',
        ['basis', 'file', 'secs', 'population'], sents)


def run_self_test():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'pws', str(Path(__file__).parent / 'perf-work-span.py'))
    assert spec is not None and spec.loader is not None
    pws = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pws)
    checks = []

    def clean_parts():
        cur = [_one_dag('final-cold-1', wall=100000),
               _one_dag('final-cold-2', wall=95000,
                        worker_ends={'chunk-A': 81200, 'chunk-B': 81800, 'chunk-C': 81400,
                                     'chunk-D': 82000}),
               _one_dag('final-cold-3', wall=96000,
                        worker_ends={'chunk-A': 81100, 'chunk-B': 81900, 'chunk-C': 81500,
                                     'chunk-D': 81700})]
        events = _three_solve() + [e for g in cur for e in g]
        perf = [_perf('COLD_COMPLETE', 'comparison-baseline', DGH, 'entry-cold-1', wall='148'),
                _perf('COLD_COMPLETE', 'final-candidate', DGC, 'final-cold-1', wall='100'),
                _perf('COLD_COMPLETE', 'final-candidate', DGC, 'final-cold-2', wall='95'),
                _perf('COLD_COMPLETE', 'final-candidate', DGC, 'final-cold-3', wall='96')]
        return _bases(), perf, events, _sentences()

    def run(bases=None, perf=None, events=None, sents=None, digest=DGC, changed=True):
        b, p, e, s = clean_parts()
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            _write(root, bases if bases is not None else b, perf if perf is not None else p,
                   events if events is not None else e, sents if sents is not None else s)
            f, notices, reg, cur, series, totals, per, reach, metrics = pws.validate(
                root, digest, changed)
            return f, series, totals, reach, metrics

    # clean acceptance + core truths
    f, series, totals, reach, metrics = run()
    checks.append(('clean series-driven measurement accepted', not f))
    if not f:
        mids = {m['metric_id']: m for m in metrics}
        checks.append(('historical comparison selected by relation, not prefix',
                       series['historical'] == [(DGH, 'COLD_COMPLETE', 'entry-cold-1')]))
        checks.append(('current cold series is the three final-candidate runs',
                       [k[2] for k in series['current']]
                       == ['final-cold-1', 'final-cold-2', 'final-cold-3']))
        checks.append(('current run count metric is 3',
                       mids['series.current_cold.run_count']['value'] == 3))
        checks.append(('historical run count metric is 1',
                       mids['series.historical_comparison.run_count']['value'] == 1))
        checks.append(('per-run metric is scenario+run_id keyed',
                       'run.COLD_COMPLETE.final-cold-1.complete_path.wall_span_ms' in mids))
        checks.append(('standard median of 100/95/96 walls is 96000',
                       mids['series.current_cold.complete_path.wall_median_ms']['value'] == 96000.0))
        checks.append(('one-DAG work reduction cites the historical representative',
                       'representative' in mids['onedag.project_verification.'
                                                'aggregate_work_reduction_pct']['statistic']))
        checks.append(('reachability computed for every current run', len(reach) == 3))

    def expect_fail(label, want=None, **kw):
        f, _, _, _, _ = run(**kw)
        checks.append((label, bool(f) and (want is None or any(want in x for x in f))))

    def ev_mut(fn):
        _, _, e, _ = clean_parts()
        for x in e:
            fn(x)
        return e

    # §15.1 scenario mismatch: graph WARM, status row cold
    def scen(x):
        if x['run_id'] == 'final-cold-1':
            x['scenario'] = 'WARM_COMPLETE'
    expect_fail('scenario mismatch: current graph relabelled WARM', want='no matching event graph',
                events=ev_mut(scen))

    # §15.2 hidden slow run: extra current-basis cold graph with no status row
    b, p, e, s = clean_parts()
    hidden = e + _one_dag('discarded-cold-4', wall=200000)
    expect_fail('hidden slow run: current cold graph without a status row',
                want='not a selected series run', events=hidden)
    # then add its status row -> included and accepted
    p4 = p + [_perf('COLD_COMPLETE', 'final-candidate', DGC, 'discarded-cold-4', wall='200')]
    f4, series4, totals4, _, metrics4 = run(perf=p4, events=hidden)
    mids4 = {m['metric_id']: m for m in metrics4} if not f4 else {}
    checks.append(('hidden run, once given a status row, joins the series and moves the median',
                   not f4 and len(series4['current']) == 4
                   and mids4['series.current_cold.complete_path.wall_median_ms']['value'] == 98000.0))

    # §15.3 sample thinning: two current runs
    p2 = [r for r in p if r['run_id'] not in ('final-cold-2', 'final-cold-3')]
    e2 = _three_solve() + _one_dag('final-cold-1', wall=100000)
    expect_fail('sample thinning below three current cold runs',
                want='at least three unique runs', perf=p2, events=e2)

    # §15.4 duplicate status link
    expect_fail('duplicate current-cold status RunKey', want='duplicate current-cold RunKey',
                perf=p + [_perf('COLD_COMPLETE', 'final-candidate', DGC, 'final-cold-1', wall='100')])

    # §15.5 machine/cache mismatch
    def mm(r):
        r = dict(r)
        if r['run_id'] == 'final-cold-1':
            r['cores'] = '8'; r['memory'] = '99GB'
            r['cache'] = r['cache'].replace('project=cold', 'project=warm').replace(
                'dune-build=cold', 'dune-build=warm')
        return r
    expect_fail('current cold machine/cache class not uniform', want='not uniform',
                perf=[mm(r) for r in p])

    # a SERIES_MATCH-only difference (command has no separate absolute check) isolates the uniformity law
    def cmd_mm(r):
        r = dict(r)
        if r['run_id'] == 'final-cold-1':
            r['command'] = 'a different make invocation'
        return r
    expect_fail('current cold command not uniform', want='command not uniform',
                perf=[cmd_mm(r) for r in p])

    # §15.6 baseline substitution: a current-basis graph named entry-* with no status row
    b, p, e, s = clean_parts()
    fake = e + _one_dag('entry-fake-current', wall=99000)
    expect_fail('current-basis entry-* cannot masquerade as the historical baseline',
                want='not a selected series run', events=fake)

    # §15.7 attribution class mutation
    def cls(x):
        if x['run_id'] == 'final-cold-1' and x['event_id'] == 'chunk-A':
            x['class'] = 'UNCLASSIFIED'
    expect_fail('attribution class chunk-A FIXTURE_WORKER->UNCLASSIFIED',
                want='attribution role/class', events=ev_mut(cls))

    # §15.8 run-name independence: rename every governed run consistently, metrics unchanged
    b, p, e, s = clean_parts()
    ren = {'entry-cold-1': 'historical-z', 'final-cold-1': 'alpha', 'final-cold-2': 'birch',
           'final-cold-3': 'seven'}
    pr = [dict(r, run_id=ren.get(r['run_id'], r['run_id'])) for r in p]
    er = [dict(x, run_id=ren.get(x['run_id'], x['run_id'])) for x in e]
    fr, sr, tr, _, mr = run(perf=pr, events=er)
    base_med = {m['metric_id']: m['value'] for m in metrics
                if m['metric_id'].startswith(('series.', 'onedag.', 'evidence_observation.'))}
    ren_med = {m['metric_id']: m['value'] for m in mr
               if m['metric_id'].startswith(('series.', 'onedag.', 'evidence_observation.'))} if not fr else {}
    checks.append(('arbitrary run names change no series/delta metric', not fr and base_med == ren_med))

    # §15.9 even-count median 90/100/110/200 -> 105
    checks.append(('standard even-count median is the mean of the two middle values',
                   pws.standard_median([90, 100, 110, 200]) == 105.0
                   and pws.standard_median([90, 100, 110, 200]) != 110))

    # §15.10 wrong comparison relation
    pw = [dict(r, relation='final-candidate') if r['relation'] == 'comparison-baseline' else r
          for r in p]
    expect_fail('historical row relabelled off comparison-baseline',
                want='exactly one run, found 0', perf=pw)

    # §15.11 event precision: a 10ms interval on a whole-second source
    def prec(x):
        if x['run_id'] == 'final-cold-1' and x['event_id'] == 'chunk-A':
            x['clock'] = 'HOST_SECONDS'
    expect_fail('claimed 10ms precision on a whole-second source', want='over-claimed',
                events=ev_mut(prec))

    # §15.12 unused evidence: an unconsumed historical basis row
    expect_fail('unused historical basis row with no selected consumer',
                want='exactly one CURRENT',   # a 2nd CURRENT would fail; an extra HISTORICAL w/o graph:
                bases=_bases())  # placeholder replaced below
    checks.pop()  # replace with the real unused-evidence control (extra graph without a row)
    b, p, e, s = clean_parts()
    orphan = e + _one_dag('final-cold-9', wall=97000)
    expect_fail('a retained event graph with no governing status row',
                want='not a selected series run', events=orphan)

    # retained topology grammar spot-checks (exact set / parent / predecessor / terminal)
    def drop_compare(x):
        return None if (x['run_id'] == 'final-cold-1' and x['event_id'] == 'compare') else x
    b, p, e, s = clean_parts()
    expect_fail('omitted terminal compare leaf', want='required event compare is missing',
                events=[x for x in e if not (x['run_id'] == 'final-cold-1'
                                             and x['event_id'] == 'compare')])
    expect_fail('proof moved outside the solve container', want='parent',
                events=ev_mut(lambda x: x.__setitem__('parent_id', 'root')
                              if x['run_id'] == 'final-cold-1' and x['event_id'] == 'proof' else None))
    expect_fail('emit predecessor set altered', want='predecessor set',
                events=ev_mut(lambda x: x.__setitem__('predecessors', 'theory,setup')
                              if x['run_id'] == 'final-cold-1' and x['event_id'] == 'emit' else None))

    # retained grammar adversaries (each proves one load-bearing check)
    _, _, e0, _ = clean_parts()
    extra = e0 + [_e(DGC, 'final-cold-1', 'pad', 'solve', 'WORK_LEAF', 'WAIT_OR_OVERHEAD', 55000,
                     57000, preds='theory')]
    expect_fail('extra work leaf beyond the topology set', want='unexpected', events=extra)
    expect_fail('false elapsed value beyond the source resolution', want='elapsed',
                events=ev_mut(lambda x: x.__setitem__('elapsed_ms', '5000')
                              if x['run_id'] == 'final-cold-1' and x['event_id'] == 'emit' else None))
    expect_fail('verification-solve tag on a non-solve event', want='non-solve event',
                events=ev_mut(lambda x: x.__setitem__('worker_or_stage', 'verification-solve')
                              if x['run_id'] == 'final-cold-1' and x['event_id'] == 'theory' else None))
    expect_fail('solve container lost its verification-solve tag', want='must carry the',
                events=ev_mut(lambda x: x.__setitem__('worker_or_stage', 'x')
                              if x['run_id'] == 'final-cold-1' and x['event_id'] == 'solve' else None))
    def _uncl(x):
        if x['run_id'] == 'final-cold-1' and x['event_id'] == 'compare':
            x['start_ms'] = '112000'; x['end_ms'] = '115000'   # a 14s gap after join, uncovered
        elif x['run_id'] == 'final-cold-1' and x['event_id'] == 'root':
            x['end_ms'] = '115000'; x['elapsed_ms'] = '115000'
    expect_fail('unclassified complete-path above 5% rejected', want='unclassified complete-path',
                events=ev_mut(_uncl))
    # a promoted/foreign CURRENT basis published as changed evidence
    expect_fail('CURRENT basis differing from the candidate digest at publication',
                want='promoted or foreign', digest='9' * 64, changed=True)
    # unit-level critical-path discriminators
    fdisc = []
    members = {'A': 10000, 'B': 20000, 'T': 1000}
    edges = {'A': set(), 'B': set(), 'T': {'A'}}
    cp = pws.terminal_path(members, edges, 'T', fdisc, 'disc')
    checks.append(('terminal-bound critical path is the path to the terminal, not the longest leaf',
                   cp == 11000 and 20000 not in (cp,) and not fdisc))
    acc = {'A': 5000, 'B': 3000, 'C': 4000}
    ed2 = {'A': set(), 'B': {'A'}, 'C': {'B'}}
    checks.append(('longest path accumulates predecessors (not a single leaf)',
                   pws.terminal_path(acc, ed2, 'C', [], 'disc2') == 12000))

    bad = [n for n, ok in checks if not ok]
    for n in bad:
        print(f'  FAIL  {n} — the accounting/series defect was not caught or a law miscomputed')
    if bad:
        raise SystemExit(f'perf-work-span self-test FAILED: {len(bad)} of {len(checks)}')
    print(f'fido: perf-work-span self-test OK — {len(checks)} controls (status-ledger series selection '
          'with no run-name prefix, RunKey status/event bijection, >=3 uniform current runs, standard '
          'even-count median, exact comparison relation, per-source timing precision, exact attribution '
          'role/class, run-name independence)')
    return 0
