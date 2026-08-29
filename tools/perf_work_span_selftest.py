#!/usr/bin/env python3
"""Adversarial self-tests for the sole accounting/reachability owner (imported by perf-work-span.py).

Each control mutates a clean synthetic measurement one condition at a time and requires the exact owning
rule to reject it — a required event cannot be omitted even when the remaining rows are self-consistent,
interval union can never stand in for the predecessor longest path, and reachability only exists over
measured per-worker intervals sharing one exact registered basis.
"""
DGC = 'c' * 64   # synthetic CURRENT basis
DGH = 'h' * 64   # synthetic HISTORICAL basis
SHA = 'a' * 40


def _base_rows():
    return [
        {'basis_digest': DGH, 'source_commit': SHA, 'topology_id': 'THREE_SOLVE_POST_CHUNKING_V1',
         'status': 'HISTORICAL', 'purpose': 'entry', 'notes': ''},
        {'basis_digest': DGC, 'source_commit': 'b' * 40, 'topology_id': 'ONE_DAG_V1',
         'status': 'CURRENT', 'purpose': 'final', 'notes': ''},
    ]


def _ev(**kw):
    d = dict(basis=DGC, scenario='COLD_COMPLETE', run_id='final-1', event_id='e', parent_id='',
             role='WORK_LEAF', cls='POLICY', start_ms='0', end_ms='1000', elapsed_ms='1000',
             predecessors='', worker_or_stage='x', cache_state='cold', result='ok', source='t', notes='')
    d.update(kw)
    d['class'] = d.pop('cls')
    return d


def _one_dag(run_id='final-1', basis=DGC):
    evs = [
        _ev(basis=basis, run_id=run_id, event_id='root', role='CONTAINER', cls='UNCLASSIFIED',
            start_ms='0', end_ms='103000', elapsed_ms='103000'),
        _ev(basis=basis, run_id=run_id, event_id='policy', parent_id='root', cls='POLICY',
            start_ms='0', end_ms='19000', elapsed_ms='19000'),
        _ev(basis=basis, run_id=run_id, event_id='solve', parent_id='root', role='CONTAINER',
            cls='UNCLASSIFIED', start_ms='19000', end_ms='100000', elapsed_ms='81000',
            worker_or_stage='verification-solve'),
        _ev(basis=basis, run_id=run_id, event_id='setup', parent_id='solve', cls='WAIT_OR_OVERHEAD',
            start_ms='19000', end_ms='25000', elapsed_ms='6000', predecessors='policy'),
        _ev(basis=basis, run_id=run_id, event_id='theory', parent_id='solve', cls='THEORY',
            start_ms='25000', end_ms='51000', elapsed_ms='26000', predecessors='setup'),
        _ev(basis=basis, run_id=run_id, event_id='proof', parent_id='solve', cls='PROOF',
            start_ms='52000', end_ms='70000', elapsed_ms='18000', predecessors='theory'),
        _ev(basis=basis, run_id=run_id, event_id='emit', parent_id='solve', cls='EMIT',
            start_ms='52000', end_ms='85000', elapsed_ms='33000', predecessors='theory'),
        _ev(basis=basis, run_id=run_id, event_id='go', parent_id='solve', cls='GO',
            start_ms='85000', end_ms='94000', elapsed_ms='9000', predecessors='emit'),
        _ev(basis=basis, run_id=run_id, event_id='join', parent_id='solve', cls='JOIN_EXPORT',
            start_ms='94000', end_ms='100000', elapsed_ms='6000', predecessors='proof,go'),
        _ev(basis=basis, run_id=run_id, event_id='compare', parent_id='root', cls='ARTIFACT_COMPARE',
            start_ms='100000', end_ms='103000', elapsed_ms='3000', predecessors='join'),
    ]
    for tag, (s, e) in {'chunk-A': (61000, 71500), 'chunk-B': (61000, 70500),
                        'chunk-C': (61000, 70400), 'chunk-D': (61000, 74500)}.items():
        evs.append(_ev(basis=basis, run_id=run_id, event_id=tag, parent_id='emit', role='ATTRIBUTION',
                       cls='FIXTURE_WORKER', start_ms=str(s), end_ms=str(e), elapsed_ms=str(e - s),
                       worker_or_stage=tag))
    return evs


def _three_solve():
    seq = [('policy', 'POLICY', 0, 19000, '', 'host'),
           ('p-context', 'WAIT_OR_OVERHEAD', 19000, 36000, 'policy', 'ctx'),
           ('p-dune', 'THEORY', 36000, 63500, 'p-context', 'dune'),
           ('p-gates', 'PROOF', 63500, 77200, 'p-dune', 'gates'),
           ('p-tail', 'WAIT_OR_OVERHEAD', 77200, 87000, 'p-gates', 'exp'),
           ('e-context', 'WAIT_OR_OVERHEAD', 87000, 95000, 'p-tail', 'ctx'),
           ('e-dune', 'THEORY', 95000, 99500, 'e-context', 'dune'),
           ('e-emit', 'EMIT', 99500, 136000, 'p-gates,e-dune', 'emit'),
           ('e-go', 'GO', 136000, 145000, 'e-emit', 'go'),
           ('art', 'JOIN_EXPORT', 145000, 148000, 'e-go', 'verification-solve')]
    evs = [_ev(basis=DGH, run_id='entry-1', event_id='root', role='CONTAINER', cls='UNCLASSIFIED',
               start_ms='0', end_ms='148000', elapsed_ms='148000'),
           _ev(basis=DGH, run_id='entry-1', event_id='s1', parent_id='root', role='CONTAINER',
               cls='UNCLASSIFIED', start_ms='19000', end_ms='87000', elapsed_ms='68000',
               worker_or_stage='verification-solve'),
           _ev(basis=DGH, run_id='entry-1', event_id='s2', parent_id='root', role='CONTAINER',
               cls='UNCLASSIFIED', start_ms='87000', end_ms='145000', elapsed_ms='58000',
               worker_or_stage='verification-solve')]
    parent_of = {'p-context': 's1', 'p-dune': 's1', 'p-gates': 's1', 'p-tail': 's1',
                 'e-context': 's2', 'e-dune': 's2', 'e-emit': 's2', 'e-go': 's2'}
    for eid, cls, s, e, preds, stage in seq:
        evs.append(_ev(basis=DGH, run_id='entry-1', event_id=eid,
                       parent_id=parent_of.get(eid, 'root'), cls=cls, start_ms=str(s), end_ms=str(e),
                       elapsed_ms=str(e - s), predecessors=preds, worker_or_stage=stage))
    return evs


def _sentences(basis=DGC):
    rows = []
    for f, tot, targ in (('e2e/WitnessRejectPrelude.v', 1.8, 0.0), ('e2e/WitnessRejectA.v', 9.5, 8.4),
                         ('e2e/WitnessRejectB.v', 9.3, 6.2), ('e2e/WitnessRejectC.v', 9.3, 5.3),
                         ('e2e/WitnessRejectD.v', 10.4, 4.2)):
        rows.append({'basis': basis, 'file': f, 'secs': f'{targ:.3f}', 'population': 'ISSUE_TABLE'})
        rows.append({'basis': basis, 'file': f, 'secs': f'{tot - targ:.3f}', 'population': 'VERDICT_ONLY'})
    return rows


def run_self_test():
    import importlib
    pws = importlib.import_module('perf-work-span'.replace('-', '_')) if False else None
    # import the engine by path (the module name carries dashes)
    import importlib.util
    from pathlib import Path
    spec = importlib.util.spec_from_file_location(
        'pws', str(Path(__file__).parent / 'perf-work-span.py'))
    pws = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pws)

    checks = []

    def run(bases=None, events=None, sents=None):
        findings = []
        reg, current = pws.check_bases(bases if bases is not None else _base_rows(), findings)
        evs = events if events is not None else (_one_dag() + _three_solve())
        by_run = pws.check_events(evs, reg, findings)
        totals = {}
        if not findings:
            for key, run_evs in sorted(by_run.items()):
                totals[key] = pws.run_totals(run_evs, findings, str(key))
        reach = None
        if not findings and sents is not None:
            per = pws.chunk_targets(sents, current, findings)
            key = (DGC, 'COLD_COMPLETE', 'final-1')
            workers = pws.worker_intervals(by_run[key])
            missing = sorted(set(pws.WORKER_CHUNKS) - set(workers))
            if missing:
                findings.append(f'missing worker intervals {missing}')
            elif not findings:
                reach = pws.reachability(per, workers, findings, 'final-1')
        return findings, totals, reach

    # clean acceptance + core numeric truths
    f, totals, reach = run(sents=_sentences())
    key = (DGC, 'COLD_COMPLETE', 'final-1')
    ekey = (DGH, 'COLD_COMPLETE', 'entry-1')
    checks.append(('clean two-topology measurement accepted', not f))
    if not f:
        t, e = totals[key], totals[ekey]
        checks.append(('final PV work counts the hidden proof branch', t['pv']['work'] == 101000))
        checks.append(('final PV critical path is the longest predecessor path',
                       t['pv']['critical'] == 83000 and t['pv']['union'] == 83000))
        checks.append(('final complete critical path', t['complete']['critical'] == 102000))
        checks.append(('overlap = work - critical path', t['pv']['overlap'] == 101000 - 83000))
        checks.append(('entry serial: work equals critical path',
                       e['pv']['work'] == e['pv']['critical'] == 129000))
        checks.append(('entry root-level artifact operation included in PV',
                       e['pv']['work'] == 129000))
        checks.append(('reachability from measured per-worker intervals',
                       reach is not None and abs(reach['max_agg_work_saving_ms'] - 24100) < 200))
        checks.append(('zero-cost wave is max worker residual, never aggregate/4',
                       reach is not None and reach['max_fixture_wall_saving_ms'] < 8000))

    def expect_fail(label, bases=None, events=None, sents=None):
        f, _, _ = run(bases=bases, events=events, sents=sents)
        checks.append((label, bool(f)))

    def drop(eid, redirect=None):
        evs = []
        for e in _one_dag() + _three_solve():
            if e['event_id'] == eid and e['run_id'] == 'final-1':
                continue
            if redirect and e['run_id'] == 'final-1' and eid in e['predecessors']:
                e = dict(e, predecessors=redirect(e['predecessors']))
            evs.append(e)
        return evs

    # §6.5 required-event omission — each rejected even with the remaining rows self-consistent
    expect_fail('omitted proof with join edited to require only go',
                events=drop('proof', lambda p: p.replace('proof,go', 'go')))
    expect_fail('omitted emit', events=drop('emit', lambda p: p.replace('emit', 'theory')))
    expect_fail('omitted go', events=drop('go', lambda p: p.replace('proof,go', 'proof')))
    expect_fail('omitted join', events=drop('join', lambda p: p.replace('join', 'go')))
    expect_fail('omitted compare', events=drop('compare'))
    expect_fail('omitted dune invocation', events=drop('theory', lambda p: p.replace('theory', 'setup')))
    expect_fail('duplicated proof leaf beyond the topology count', events=_one_dag() + _three_solve() + [
        _ev(event_id='proof2', parent_id='solve', cls='PROOF', start_ms='52000', end_ms='60000',
            elapsed_ms='8000', predecessors='theory')])
    expect_fail('a work leaf nested under another work leaf', events=_one_dag() + _three_solve() + [
        _ev(event_id='sub', parent_id='emit', cls='WAIT_OR_OVERHEAD', start_ms='52000',
            end_ms='54000', elapsed_ms='2000')])
    expect_fail('false elapsed value rejected', events=[
        dict(e, elapsed_ms='5000') if e['event_id'] == 'emit' else e
        for e in _one_dag() + _three_solve()])
    expect_fail('unclassified complete-path above 5% rejected', events=[
        dict(e, end_ms='120000', elapsed_ms='120000')
        if e['event_id'] == 'root' and e['run_id'] == 'final-1' else e
        for e in _one_dag() + _three_solve()])
    expect_fail('extra unexpected solve', events=_one_dag() + _three_solve() + [
        _ev(event_id='solve2', parent_id='root', role='CONTAINER', cls='UNCLASSIFIED',
            start_ms='0', end_ms='1000', elapsed_ms='1000', worker_or_stage='verification-solve')])
    expect_fail('unknown work leaf class rejected until the registry owns it',
                events=_one_dag() + _three_solve() + [
                    _ev(event_id='mystery', parent_id='root', cls='FIXTURE_WORKER',
                        start_ms='0', end_ms='500', elapsed_ms='500')])
    expect_fail('join missing one required predecessor', events=[
        dict(e, predecessors='go') if e['event_id'] == 'join' else e
        for e in _one_dag() + _three_solve()])
    expect_fail('role changed from the topology specification', events=[
        dict(e, role='ATTRIBUTION') if e['event_id'] == 'proof' else e
        for e in _one_dag() + _three_solve()])
    expect_fail('predecessor cycle', events=[
        dict(e, predecessors='compare') if e['event_id'] == 'setup' else e
        for e in _one_dag() + _three_solve()])
    expect_fail('failed task counted as work', events=[
        dict(e, result='fail') if e['event_id'] == 'emit' else e
        for e in _one_dag() + _three_solve()])

    # §5 basis laws
    expect_fail('unregistered basis', events=[
        dict(e, basis='f' * 64) if e['run_id'] == 'final-1' else e
        for e in _one_dag() + _three_solve()])
    expect_fail('duplicate CURRENT basis', bases=_base_rows() + [
        {'basis_digest': 'd' * 64, 'source_commit': 'e' * 40, 'topology_id': 'ONE_DAG_V1',
         'status': 'CURRENT', 'purpose': 'x', 'notes': ''}])
    expect_fail('malformed registry digest', bases=[
        dict(b, basis_digest='xyz') if b['status'] == 'CURRENT' else b for b in _base_rows()])
    expect_fail('current profile rows on a historical basis', sents=_sentences(basis=DGH))
    expect_fail('missing worker interval blocks reachability',
                events=[e for e in _one_dag() + _three_solve() if e['event_id'] != 'chunk-B'],
                sents=_sentences())

    # §7.4 discriminating synthetic: an independent late leaf extends the interval union beyond every
    # predecessor chain, so union (13s) and the true longest path (10s) differ materially
    syn = [
        _ev(event_id='A', cls='EMIT', start_ms='0', end_ms='10000', elapsed_ms='10000'),
        _ev(event_id='B', cls='GO', start_ms='12000', end_ms='15000', elapsed_ms='3000'),
    ]
    ids = {e['event_id']: e for e in syn}
    fdisc = []
    cp = pws.longest_path(syn, ids, fdisc, 'disc')
    un = pws.union_len([(0, 10000), (12000, 15000)])
    checks.append(('union and longest path materially different on the discriminating graph',
                   cp == 10000 and un == 13000 and not fdisc))
    checks.append(('the longest-path implementation is not the union implementation', cp != un))
    expect_fail('missing terminal compare leaf', events=drop('compare'))

    bad = [n for n, ok in checks if not ok]
    for n in bad:
        print(f'  FAIL  {n} — the accounting defect was not caught or the law miscomputed')
    if bad:
        raise SystemExit(f'perf-work-span self-test FAILED: {len(bad)} of {len(checks)}')
    print(f'fido: perf-work-span self-test OK — {len(checks)} controls (required-topology omission incl. '
          'the edited-join proof omission, basis registry laws, longest-path vs union discrimination, '
          'boundary inclusion, measured per-worker reachability)')
    return 0
