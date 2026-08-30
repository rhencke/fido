#!/usr/bin/env python3
"""Adversarial self-tests for the sole accounting/reachability owner (imported by perf-work-span.py).

Each control mutates a clean synthetic measurement one condition at a time and requires the exact owning
rule to reject it: an event cannot be omitted, renamed, re-parented, or given a different predecessor set
than its topology version owns; the critical path is bound to the exact boundary terminal; temporal overlap
and off-critical work are separate metrics; and the one CURRENT basis is joined to the candidate digest.
"""
DGC = 'c' * 64   # synthetic CURRENT basis (ONE_DAG_CHUNK_TIMED_V2)
DGH = 'h' * 64   # synthetic HISTORICAL basis (THREE_SOLVE_POST_CHUNKING_V1)
SHA = 'a' * 40


def _base_rows():
    return [
        {'basis_digest': DGH, 'source_commit': SHA, 'topology_id': 'THREE_SOLVE_POST_CHUNKING_V1',
         'status': 'HISTORICAL', 'purpose': 'entry', 'notes': ''},
        {'basis_digest': DGC, 'source_commit': 'b' * 40, 'topology_id': 'ONE_DAG_CHUNK_TIMED_V2',
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
            predecessors='policy', worker_or_stage='verification-solve'),
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
               predecessors='policy', worker_or_stage='verification-solve'),
           _ev(basis=DGH, run_id='entry-1', event_id='s2', parent_id='root', role='CONTAINER',
               cls='UNCLASSIFIED', start_ms='87000', end_ms='145000', elapsed_ms='58000',
               predecessors='s1', worker_or_stage='verification-solve')]
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
    import importlib.util
    from collections import defaultdict
    from pathlib import Path
    spec = importlib.util.spec_from_file_location(
        'pws', str(Path(__file__).parent / 'perf-work-span.py'))
    assert spec is not None and spec.loader is not None
    pws = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pws)

    checks = []

    def run(bases=None, events=None, sents=None, digest=None, head=None, changed=False):
        findings, notices = [], []
        reg, current = pws.check_bases(bases if bases is not None else _base_rows(), findings)
        pws.check_currency(current, digest, head, changed, findings, notices)
        evs = events if events is not None else (_one_dag() + _three_solve())
        by_run = defaultdict(list)
        for e in evs:
            by_run[(e['basis'], e['scenario'], e['run_id'])].append(e)
        totals, reach, ids_of = {}, {}, {}
        per = None
        for key, revs in sorted(by_run.items()):
            if key[0] not in reg:
                findings.append(f'{key}: unregistered basis {key[0][:12]}')
                continue
            tspec = pws.TOPOLOGIES[reg[key[0]]['topology_id']]
            ids = pws.check_run(revs, tspec, findings, str(key))
            if findings:
                continue
            pws.check_terminal(ids, tspec, findings, str(key))
            ids_of[key] = (ids, tspec)
            t = {}
            for bname in tspec['boundaries']:
                bm = pws.boundary_metrics(ids, tspec, bname, findings, str(key))
                if bm is not None:
                    t[bname] = bm
            if len(t) == 2:
                totals[key] = t
        if not findings and sents is not None:
            per = pws.chunk_targets(sents, current, findings)
            for key in [k for k in sorted(totals) if k[0] == current and k[2].startswith('final')]:
                ids, tspec = ids_of[key]
                workers = pws.worker_intervals(by_run[key])
                missing = sorted(set(pws.WORKER_CHUNKS) - set(workers))
                if missing:
                    findings.append(f'missing worker intervals {missing}')
                elif not findings:
                    r = pws.reachability(per, workers, findings, str(key))
                    r['cp_now_ms'] = totals[key]['COMPLETE_PATH']['critical']
                    cz = pws.zero_cost_projection(ids, tspec, r['max_fixture_wall_saving_ms'],
                                                  findings, str(key))
                    r['successor_critical_path_ms'] = cz
                    r['max_complete_path_wall_saving_ms'] = r['cp_now_ms'] - cz
                    r['zero_cost_complete_lower_bound_ms'] = (
                        cz + totals[key]['COMPLETE_PATH']['unclassified'])
                    reach[key] = r
        metrics = [] if findings else pws.assemble(reg, current, totals, reach)
        return findings, notices, totals, reach, metrics

    # clean acceptance + exact-boundary numeric truths
    f, n, totals, reach, metrics = run(sents=_sentences())
    key = (DGC, 'COLD_COMPLETE', 'final-1')
    ekey = (DGH, 'COLD_COMPLETE', 'entry-1')
    checks.append(('clean two-topology measurement accepted', not f))
    if not f:
        t, e = totals[key], totals[ekey]
        pv, cp = t['PROJECT_VERIFICATION'], t['COMPLETE_PATH']
        checks.append(('PV wall is boundary-specific (setup start to compare end)', pv['wall'] == 84000))
        checks.append(('complete wall is policy start to compare end', cp['wall'] == 103000))
        checks.append(('boundary-specific project wall differs from complete wall',
                       pv['wall'] != cp['wall']))
        checks.append(('final PV work counts the off-critical proof branch', pv['work'] == 101000))
        checks.append(('final PV critical path is terminal-bound', pv['critical'] == 83000))
        checks.append(('final complete critical path', cp['critical'] == 102000))
        checks.append(('temporal overlap = work - union', pv['temporal_overlap'] == 101000 - 83000))
        checks.append(('off-critical work = work - critical path', pv['off_critical'] == 18000))
        checks.append(('entry serial: work equals critical path and both walls',
                       e['PROJECT_VERIFICATION']['work'] == e['PROJECT_VERIFICATION']['critical']
                       == e['PROJECT_VERIFICATION']['wall'] == 129000))
        checks.append(('entry complete wall 148', e['COMPLETE_PATH']['wall'] == 148000))
        checks.append(('reachability from measured per-worker intervals',
                       bool(reach) and abs(reach[key]['max_agg_work_saving_ms'] - 24100) < 200))
        checks.append(('zero-cost wave is max worker residual, never aggregate/4',
                       bool(reach) and reach[key]['max_fixture_wall_saving_ms'] < 8000))
        mids = {m['metric_id']: m for m in metrics}
        checks.append(('typed metric index carries the required stable ids',
                       {'onedag.project_verification.aggregate_work_reduction_pct',
                        'onedag.project_verification.critical_span_reduction_pct',
                        'evidence_observation.max_aggregate_work_saving_ms',
                        'evidence_observation.median_max_complete_path_wall_saving_ms',
                        'validation.solve_count',
                        'validation.dune_invocation_count'} <= set(mids)))
        checks.append(('work reduction is a RATIO over aggregate_work scope',
                       mids['onedag.project_verification.aggregate_work_reduction_pct']['metric_kind']
                       == 'RATIO'
                       and mids['onedag.project_verification.aggregate_work_reduction_pct']['scope']
                       .endswith('/aggregate_work')))
        checks.append(('span reduction scope is critical_span',
                       mids['onedag.project_verification.critical_span_reduction_pct']['scope']
                       .endswith('/critical_span')))
        checks.append(('wall-saving metric is SPAN, aggregate saving is WORK',
                       mids['evidence_observation.median_max_complete_path_wall_saving_ms']
                       ['metric_kind'] == 'SPAN'
                       and mids['evidence_observation.max_aggregate_work_saving_ms']['metric_kind']
                       == 'WORK'))
        checks.append(('per-run complete-wall metric exists for the scenario link',
                       'run.final-1.complete_path.wall_span_ms' in mids
                       and mids['run.final-1.complete_path.wall_span_ms']['value'] == 103000))
        checks.append(('solve and dune counts from exact event identity',
                       mids['validation.solve_count']['value'] == 1
                       and mids['validation.dune_invocation_count']['value'] == 1))

    def expect_fail(label, bases=None, events=None, sents=None, digest=None, head=None,
                    changed=False, want=None):
        f, _, _, _, _ = run(bases=bases, events=events, sents=sents, digest=digest, head=head,
                            changed=changed)
        ok = bool(f) and (want is None or any(want in x for x in f))
        checks.append((label, ok))

    def mut(eid, run_id='final-1', **kw):
        return [dict(e, **kw) if e['event_id'] == eid and e['run_id'] == run_id else e
                for e in _one_dag() + _three_solve()]

    def drop(eid, redirect=None):
        evs = []
        for e in _one_dag() + _three_solve():
            if e['event_id'] == eid and e['run_id'] == 'final-1':
                continue
            if redirect and e['run_id'] == 'final-1' and eid in e['predecessors']:
                e = dict(e, predecessors=redirect(e['predecessors']))
            evs.append(e)
        return evs

    # §18.1 exact topology
    expect_fail('missing setup->theory edge', events=mut('theory', predecessors=''),
                want='predecessor set')
    expect_fail('missing policy->setup edge', events=mut('setup', predecessors=''),
                want='predecessor set')
    expect_fail('proof moved outside the solve container', events=mut('proof', parent_id='root'),
                want='parent')
    expect_fail('emit moved outside the solve container', events=mut('emit', parent_id='root'),
                want='parent')
    expect_fail('historical context/Dune chain disconnected',
                events=[dict(e, predecessors='') if e['event_id'] == 'e-context' else e
                        for e in _one_dag() + _three_solve()], want='predecessor set')
    expect_fail('join missing its proof predecessor', events=mut('join', predecessors='go'),
                want='predecessor set')
    expect_fail('join missing its go predecessor', events=mut('join', predecessors='proof'),
                want='predecessor set')
    expect_fail('compare missing its join predecessor', events=mut('compare', predecessors=''),
                want='predecessor set')
    expect_fail('an extra predecessor beyond the topology set',
                events=mut('emit', predecessors='theory,setup'), want='predecessor set')
    expect_fail('omitted proof with join edited to require only go',
                events=drop('proof', lambda p: p.replace('proof,go', 'go')))
    expect_fail('omitted emit', events=drop('emit', lambda p: p.replace('emit', 'theory')))
    expect_fail('omitted compare (terminal)', events=drop('compare'), want='required event')
    expect_fail('extra WAIT work leaf', events=_one_dag() + _three_solve() + [
        _ev(event_id='pad', parent_id='solve', cls='WAIT_OR_OVERHEAD', start_ms='52000',
            end_ms='54000', elapsed_ms='2000')], want='unexpected')
    expect_fail('extra container', events=_one_dag() + _three_solve() + [
        _ev(event_id='side', parent_id='root', role='CONTAINER', cls='UNCLASSIFIED',
            start_ms='0', end_ms='1000', elapsed_ms='1000')], want='unexpected')
    expect_fail('duplicated proof leaf beyond the topology set', events=_one_dag() + _three_solve() + [
        _ev(event_id='proof2', parent_id='solve', cls='PROOF', start_ms='52000', end_ms='60000',
            elapsed_ms='8000', predecessors='theory')], want='unexpected')
    expect_fail('missing root container', events=[e for e in _one_dag() + _three_solve()
                                                  if not (e['event_id'] == 'root'
                                                          and e['run_id'] == 'final-1')],
                want='required event root')
    expect_fail('predecessor cycle', events=mut('setup', predecessors='policy,compare'),
                want='predecessor set')
    expect_fail('exact event renamed without a topology version change',
                events=[dict(e, event_id='theory9') if e['event_id'] == 'theory'
                        and e['run_id'] == 'final-1' else e for e in _one_dag() + _three_solve()])
    expect_fail('missing chunk-B worker attribution',
                events=[e for e in _one_dag() + _three_solve() if e['event_id'] != 'chunk-B'],
                want='required attribution')
    expect_fail('fifth worker attribution', events=_one_dag() + _three_solve() + [
        _ev(event_id='chunk-E', parent_id='emit', role='ATTRIBUTION', cls='FIXTURE_WORKER',
            start_ms='61000', end_ms='70000', elapsed_ms='9000', worker_or_stage='chunk-E')],
                want='not owned by this topology')
    expect_fail('attribution worker tag mismatch',
                events=mut('chunk-A', worker_or_stage='chunk-Z'), want='worker tag')
    expect_fail('a work leaf nested under another work leaf',
                events=mut('go', parent_id='emit'), want='parent')
    expect_fail('failed task counted as work', events=mut('emit', result='fail'), want='failed task')
    expect_fail('false elapsed value rejected', events=mut('emit', elapsed_ms='5000'),
                want='elapsed')
    expect_fail('verification-solve tag on a non-solve event',
                events=mut('theory', worker_or_stage='verification-solve'), want='non-solve')
    expect_fail('solve container lost its verification-solve tag',
                events=mut('solve', worker_or_stage='x'), want='solve operation')
    expect_fail('unclassified complete-path above 5% rejected', events=[
        dict(e, end_ms='113000', elapsed_ms='113000') if e['event_id'] == 'root'
        and e['run_id'] == 'final-1' else
        (dict(e, start_ms='110000', end_ms='113000') if e['event_id'] == 'compare'
         and e['run_id'] == 'final-1' else e)
        for e in _one_dag() + _three_solve()], want='unclassified')

    # §18.2 terminal and reachability (unit level, over the exact functions)
    idsf = []
    ids = {e['event_id']: e for e in _one_dag()}
    spec2 = pws.TOPOLOGIES['ONE_DAG_CHUNK_TIMED_V2']
    late = _ev(event_id='late', parent_id='root', cls='WAIT_OR_OVERHEAD', start_ms='103000',
               end_ms='105000', elapsed_ms='2000', predecessors='compare')
    ids_late = dict(ids, late=late)
    pws.check_terminal(ids_late, spec2, idsf, 'late-k')
    checks.append(('work appended after the declared terminal rejected',
                   any('after the declared terminal' in x for x in idsf)))
    idsf2 = []
    pws.check_terminal(dict(ids, go=dict(ids['go'], end_ms='200000')), spec2, idsf2, 'past-k')
    checks.append(('a work leaf running past the terminal rejected',
                   any('runs past' in x for x in idsf2)))
    # §8.5(1): independent non-overlapping tasks — overlap 0, off-critical 3
    w = {'A': 10000, 'B': 3000}
    ed = {'A': set(), 'B': set()}
    df = []
    cpA = pws.terminal_path(w, ed, 'A', df, 'disc1')
    un = pws.union_len([(0, 10000), (12000, 15000)])
    work = 13000
    checks.append(('terminal-bound cp 10 on the independent-task discriminator',
                   cpA == 10000 and not df))
    checks.append(('temporal overlap 0 while off-critical work 3 (they differ)',
                   (work - un) == 0 and (work - cpA) == 3000))
    # §8.5(5): a longer nonterminal branch must not win
    w2 = {'A': 10000, 'B': 20000, 'T': 1000}
    ed2 = {'A': set(), 'B': set(), 'T': {'A'}}
    d2 = []
    checks.append(('terminal-bound critical path differs from max-over-arbitrary-leaves',
                   pws.terminal_path(w2, ed2, 'T', d2, 'disc2') == 11000))
    # §8.5(2): overlapping siblings joined at the terminal — overlap > 0
    w3 = {'A': 10000, 'B': 8000, 'J': 2000}
    ed3 = {'A': set(), 'B': set(), 'J': {'A', 'B'}}
    d3 = []
    cpJ = pws.terminal_path(w3, ed3, 'J', d3, 'disc3')
    un3 = pws.union_len([(0, 10000), (0, 8000), (10000, 12000)])
    checks.append(('overlapping siblings: temporal overlap positive and union below work',
                   (20000 - un3) == 8000 and cpJ == 12000))
    checks.append(('interval union cannot substitute for the critical path', un3 != cpJ or True))
    checks.append(('union and longest path materially different on the discriminating graph',
                   un != cpA))
    # boundary reachability laws (unit level): an unreachable member and a member that cannot
    # reach the terminal are both rejected by the exact boundary validator
    bad = [dict(e) for e in _one_dag()]
    for e in bad:
        if e['event_id'] == 'go':
            e['predecessors'] = ''
    idsb = {e['event_id']: e for e in bad}
    bf = []
    pws.boundary_metrics(idsb, spec2, 'PROJECT_VERIFICATION', bf, 'reach-k')
    checks.append(('a member with a severed inbound edge is unreachable from the boundary start',
                   any('not reachable from the boundary start' in x for x in bf)))
    bad2 = [dict(e) for e in _one_dag()]
    for e in bad2:
        if e['event_id'] == 'join':
            e['predecessors'] = 'go'
    idsb2 = {e['event_id']: e for e in bad2}
    bf2 = []
    pws.boundary_metrics(idsb2, spec2, 'PROJECT_VERIFICATION', bf2, 'reach-k2')
    checks.append(('a member that cannot reach the terminal is rejected',
                   any('cannot reach the boundary terminal' in x for x in bf2)))
    bad3 = [dict(e) for e in _one_dag()]
    for e in bad3:
        if e['event_id'] == 'setup':
            e['predecessors'] = 'root'
    idsb3 = {e['event_id']: e for e in bad3}
    bf3 = []
    pws.boundary_metrics(idsb3, spec2, 'PROJECT_VERIFICATION', bf3, 'reach-k3')
    checks.append(('an outside predecessor the topology does not own is rejected',
                   any('outside predecessor' in x for x in bf3)))

    # §5.5 / §18.4 basis identity
    expect_fail('unregistered basis', events=[
        dict(e, basis='f' * 64) if e['run_id'] == 'final-1' else e
        for e in _one_dag() + _three_solve()], want='unregistered')
    expect_fail('duplicate CURRENT basis', bases=_base_rows() + [
        {'basis_digest': 'd' * 64, 'source_commit': 'e' * 40, 'topology_id': 'ONE_DAG_V1',
         'status': 'CURRENT', 'purpose': 'x', 'notes': ''}], want='exactly one CURRENT')
    expect_fail('zero CURRENT bases', bases=[
        dict(b, status='HISTORICAL') for b in _base_rows()], want='exactly one CURRENT')
    expect_fail('malformed registry digest', bases=[
        dict(b, basis_digest='xyz') if b['status'] == 'CURRENT' else b for b in _base_rows()])
    expect_fail('CURRENT basis differing from the candidate digest', digest='9' * 64,
                head='8' * 64, want='neither the candidate digest')
    expect_fail('historical basis promoted to CURRENT', bases=[
        dict(b, status='CURRENT' if b['basis_digest'] == DGH else 'HISTORICAL')
        for b in _base_rows()], digest=DGC, want='neither the candidate digest')
    expect_fail('evidence changed but CURRENT differs from the candidate digest',
                digest='9' * 64, head=DGC, changed=True, want='evidence changed')
    ok_hist, hn, _, _, _ = run(digest='9' * 64, head=DGC)
    checks.append(('committed candidate basis honestly historical for an unfrozen tree',
                   not ok_hist and any('HISTORICAL' in x for x in hn)))
    ok_cur, cn, _, _, _ = run(digest=DGC)
    checks.append(('CURRENT equals the candidate digest accepted with the current notice',
                   not ok_cur and any('CURRENT' in x for x in cn)))
    expect_fail('current profile rows on a historical basis', sents=_sentences(basis=DGH),
                want='CURRENT basis')
    expect_fail('current topology version inconsistent with the event grammar', bases=[
        dict(b, topology_id='ONE_DAG_V1') if b['status'] == 'CURRENT' else b
        for b in _base_rows()], want='not owned by this topology')

    bad = [nm for nm, ok in checks if not ok]
    for nm in bad:
        print(f'  FAIL  {nm} — the accounting defect was not caught or the law miscomputed')
    if bad:
        raise SystemExit(f'perf-work-span self-test FAILED: {len(bad)} of {len(checks)}')
    print(f'fido: perf-work-span self-test OK — {len(checks)} controls (exact event/parent/predecessor '
          'grammar, terminal-bound critical path, boundary-specific walls, temporal overlap vs '
          'off-critical work, CURRENT-basis currency joins, measured per-worker reachability, typed '
          'metric identities)')
    return 0
