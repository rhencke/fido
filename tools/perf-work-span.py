#!/usr/bin/env python3
"""The sole performance accounting and successor-reachability authority.

Consumes the verified basis registry, the normalized event table, and the raw sentence attribution;
enforces the EXACT event grammar of each supported topology version (event identities, roles, classes,
parents, complete predecessor sets, boundary membership, and the terminal sink); computes every governing
metric from measured intervals; and deterministically generates the committed human summaries plus the one
typed machine metric index, all regenerated and byte-compared by the normal and staged gates.

Metrics per boundary (never conflated, none called CPU time — BuildKit exposes no CPU accounting, so
elapsed task time is the declared work proxy):

  wall_span_s                  boundary terminal end minus boundary start (boundary-specific, never the
                               whole-run root wall reused)
  aggregate_task_elapsed_s     sum of the boundary's required WORK_LEAF durations
  critical_path_span_s         longest predecessor path ENDING AT THE EXACT BOUNDARY TERMINAL
  interval_union_span_s        union of the boundary's leaf intervals
  temporal_overlap_s           aggregate work minus interval union (time two tasks truly coexist)
  work_outside_critical_path_s aggregate work minus the terminal-bound critical path
  unclassified_s               boundary wall minus interval union

Every boundary member must be reachable from the exact boundary start and reach the exact terminal; the
terminal has no successor and no work leaf runs past it.  The one CURRENT registry basis is joined to the
candidate digest under the same three-frame law the scenario validator uses (current / committed-historical
/ foreign).  Reachability (the evidence-observation ceiling) uses measured per-worker intervals and
same-basis sentence targets — no universal worker-load, serial-overhead, or wave constants.
"""
import argparse
import csv
import sys
from collections import defaultdict
from pathlib import Path

BASES = '.review/perf/performance-bases.tsv'
EVENTS = '.review/perf/verification-dag-events.tsv'
SENTENCES = '.review/perf/witnessreject-sentences.tsv'
GEN_WORK_SPAN = 'verification-dag-work-span.tsv'
GEN_REACH = 'verification-dag-reachability.tsv'
GEN_METRICS = 'performance-derived-metrics.tsv'

ROLES = ('CONTAINER', 'WORK_LEAF', 'ATTRIBUTION')
TARGET_POPS = ('ISSUE_TABLE', 'CAUSE_VIEW', 'REQ_VIEW', 'GROUP_VIEW')
WORKER_CHUNKS = {'chunk-A': 'e2e/WitnessRejectA.v', 'chunk-B': 'e2e/WitnessRejectB.v',
                 'chunk-C': 'e2e/WitnessRejectC.v', 'chunk-D': 'e2e/WitnessRejectD.v'}
TOL = 1500  # ms clock tolerance


def _ev(role, cls, parent, preds, solve=False):
    return {'role': role, 'class': cls, 'parent': parent, 'preds': frozenset(preds), 'solve': solve}


# each topology version owns one exact measured graph: exact event identities, roles, classes, parents,
# complete predecessor sets, the solve-operation events (by identity, never a string count), exact
# attribution events, and both boundary definitions (start / terminal / external source edge)
_ONE_DAG_EVENTS = {
    'root':    _ev('CONTAINER', 'UNCLASSIFIED', '', ()),
    'policy':  _ev('WORK_LEAF', 'POLICY', 'root', ()),
    'solve':   _ev('CONTAINER', 'UNCLASSIFIED', 'root', ('policy',), solve=True),
    'setup':   _ev('WORK_LEAF', 'WAIT_OR_OVERHEAD', 'solve', ('policy',)),
    'theory':  _ev('WORK_LEAF', 'THEORY', 'solve', ('setup',)),
    'proof':   _ev('WORK_LEAF', 'PROOF', 'solve', ('theory',)),
    'emit':    _ev('WORK_LEAF', 'EMIT', 'solve', ('theory',)),
    'go':      _ev('WORK_LEAF', 'GO', 'solve', ('emit',)),
    'join':    _ev('WORK_LEAF', 'JOIN_EXPORT', 'solve', ('proof', 'go')),
    'compare': _ev('WORK_LEAF', 'ARTIFACT_COMPARE', 'root', ('join',)),
}
_ONE_DAG_BOUNDS = {
    'COMPLETE_PATH': {'start': 'policy', 'terminal': 'compare', 'exclude': ()},
    'PROJECT_VERIFICATION': {'start': 'setup', 'terminal': 'compare', 'exclude': ('policy',),
                             'external_source': ('policy', 'setup')},
}
TOPOLOGIES = {
    'THREE_SOLVE_POST_CHUNKING_V1': {
        'events': {
            'root':      _ev('CONTAINER', 'UNCLASSIFIED', '', ()),
            'policy':    _ev('WORK_LEAF', 'POLICY', 'root', ()),
            's1':        _ev('CONTAINER', 'UNCLASSIFIED', 'root', ('policy',), solve=True),
            'p-context': _ev('WORK_LEAF', 'WAIT_OR_OVERHEAD', 's1', ('policy',)),
            'p-dune':    _ev('WORK_LEAF', 'THEORY', 's1', ('p-context',)),
            'p-gates':   _ev('WORK_LEAF', 'PROOF', 's1', ('p-dune',)),
            'p-tail':    _ev('WORK_LEAF', 'WAIT_OR_OVERHEAD', 's1', ('p-gates',)),
            's2':        _ev('CONTAINER', 'UNCLASSIFIED', 'root', ('s1',), solve=True),
            'e-context': _ev('WORK_LEAF', 'WAIT_OR_OVERHEAD', 's2', ('p-tail',)),
            'e-dune':    _ev('WORK_LEAF', 'THEORY', 's2', ('e-context',)),
            'e-emit':    _ev('WORK_LEAF', 'EMIT', 's2', ('p-gates', 'e-dune')),
            'e-go':      _ev('WORK_LEAF', 'GO', 's2', ('e-emit',)),
            'art':       _ev('WORK_LEAF', 'JOIN_EXPORT', 'root', ('e-go',), solve=True),
        },
        'attribution': {'e-wave2': {'parent': 'e-emit', 'worker': 'chunk-workers', 'required': False}},
        'boundaries': {
            'COMPLETE_PATH': {'start': 'policy', 'terminal': 'art', 'exclude': ()},
            'PROJECT_VERIFICATION': {'start': 'p-context', 'terminal': 'art', 'exclude': ('policy',),
                                     'external_source': ('policy', 'p-context')},
        },
        'dune': 2,
    },
    'ONE_DAG_V1': {
        'events': _ONE_DAG_EVENTS,
        'attribution': {'wave2': {'parent': 'emit', 'worker': 'chunk-workers', 'required': False}},
        'boundaries': _ONE_DAG_BOUNDS,
        'dune': 1,
    },
    'ONE_DAG_CHUNK_TIMED_V2': {
        'events': _ONE_DAG_EVENTS,
        'attribution': {tag: {'parent': 'emit', 'worker': tag, 'required': True}
                        for tag in WORKER_CHUNKS},
        'boundaries': _ONE_DAG_BOUNDS,
        'dune': 1,
    },
}


def read_tsv(path):
    with open(path, encoding='utf-8') as f:
        rows = [ln for ln in f if ln.strip() and not ln.lstrip().startswith('#')]
    return list(csv.DictReader(rows, delimiter='\t'))


# ---------------- basis registry ----------------
def check_bases(bases, findings):
    reg = {}
    current = []
    for i, b in enumerate(bases, 1):
        if len(b.get('basis_digest') or '') != 64:
            findings.append(f'{BASES}:{i}: basis_digest is not 64-hex')
            continue
        if len(b.get('source_commit') or '') != 40:
            findings.append(f'{BASES}:{i}: source_commit is not 40-hex')
        if b.get('status') not in ('CURRENT', 'HISTORICAL'):
            findings.append(f'{BASES}:{i}: status must be CURRENT|HISTORICAL')
        if b.get('topology_id') not in TOPOLOGIES:
            findings.append(f'{BASES}:{i}: unknown topology_id {b.get("topology_id")!r}')
        if b['basis_digest'] in reg:
            findings.append(f'{BASES}:{i}: duplicate basis {b["basis_digest"][:12]}')
        reg[b['basis_digest']] = b
        if b.get('status') == 'CURRENT':
            current.append(b['basis_digest'])
    if len(current) != 1:
        findings.append(f'{BASES}: exactly one CURRENT basis required, found {len(current)}')
    return reg, (current[0] if current else None)


def check_currency(current, current_digest, head_digest, evidence_changed, findings, notices):
    """Join the registry CURRENT basis to the candidate digest (three-frame, like the scenario law)."""
    if not current or not current_digest:
        return
    if current == current_digest:
        notices.append('registry CURRENT basis equals the candidate digest — evidence is CURRENT')
    elif evidence_changed:
        findings.append(f'{BASES}: performance evidence changed but the CURRENT basis '
                        f'{current[:12]} differs from the candidate digest {current_digest[:12]}')
    elif head_digest and current == head_digest:
        notices.append('registry CURRENT basis is the committed candidate digest; the proposed tree '
                       'has not re-frozen — evidence is HISTORICAL for this exact tree')
    else:
        findings.append(f'{BASES}: CURRENT basis {current[:12]} is neither the candidate digest '
                        f'{current_digest[:12]} nor the committed candidate digest — a promoted or '
                        f'foreign CURRENT basis is rejected')


# ---------------- exact event grammar ----------------
def check_run(evs, spec, findings, key):
    ids = {}
    for e in evs:
        if e['event_id'] in ids:
            findings.append(f'{key}: duplicate event_id {e["event_id"]}')
        ids[e['event_id']] = e
        try:
            s, en, el = int(e['start_ms']), int(e['end_ms']), int(e['elapsed_ms'])
            if abs((en - s) - el) > TOL:
                findings.append(f'{key}:{e["event_id"]}: elapsed {el} != end-start {en - s}')
        except ValueError:
            findings.append(f'{key}:{e["event_id"]}: non-numeric interval')
            return ids
    req = spec['events']
    attr = spec['attribution']
    actual_core = {i for i, e in ids.items() if e['role'] in ('CONTAINER', 'WORK_LEAF')}
    for missing in sorted(set(req) - actual_core):
        findings.append(f'{key}: required event {missing} is missing — the topology owns the exact set')
    for extra in sorted(actual_core - set(req)):
        findings.append(f'{key}: unexpected {ids[extra]["role"]} {extra} — no arbitrary extra work leaf '
                        f'or container is allowed')
    for i, e in ids.items():
        if e['role'] not in ROLES:
            findings.append(f'{key}:{i}: unknown role {e["role"]!r}')
        if e['role'] == 'ATTRIBUTION':
            if i not in attr:
                findings.append(f'{key}:{i}: attribution event not owned by this topology version')
                continue
            a = attr[i]
            if e['parent_id'] != a['parent']:
                findings.append(f'{key}:{i}: attribution parent {e["parent_id"]} != {a["parent"]}')
            if e['worker_or_stage'] != a['worker']:
                findings.append(f'{key}:{i}: attribution worker tag {e["worker_or_stage"]!r} != '
                                f'{a["worker"]!r}')
            if e['result'] != 'ok':
                findings.append(f'{key}:{i}: attribution result must be ok')
            if set(filter(None, e['predecessors'].split(','))):
                findings.append(f'{key}:{i}: attribution events declare no predecessors')
            continue
        if i not in req:
            continue
        r = req[i]
        if e['role'] != r['role'] or e['class'] != r['class']:
            findings.append(f'{key}:{i}: role/class {e["role"]}/{e["class"]} != required '
                            f'{r["role"]}/{r["class"]}')
        if e['parent_id'] != r['parent']:
            findings.append(f'{key}:{i}: parent {e["parent_id"]!r} != required {r["parent"]!r}')
        actual_preds = set(filter(None, e['predecessors'].split(',')))
        if actual_preds != set(r['preds']):
            findings.append(f'{key}:{i}: predecessor set {sorted(actual_preds)} != required '
                            f'{sorted(r["preds"])} — missing and extra predecessors both reject')
        want_solve = 'verification-solve' if r['solve'] else None
        if r['solve'] and e['worker_or_stage'] != 'verification-solve':
            findings.append(f'{key}:{i}: this event is a solve operation and must carry the '
                            f'verification-solve tag')
        if not r['solve'] and e['worker_or_stage'] == 'verification-solve':
            findings.append(f'{key}:{i}: verification-solve tag on a non-solve event')
        del want_solve
        if e['role'] == 'WORK_LEAF' and e['result'] != 'ok':
            findings.append(f'{key}:{i}: a failed task cannot be counted as work')
    for tag, a in attr.items():
        if a['required'] and tag not in ids:
            findings.append(f'{key}: required attribution event {tag} is missing')
    # containment + parent reachability to the one root
    roots = [i for i, e in ids.items() if e['role'] != 'ATTRIBUTION' and not e['parent_id']]
    if len(roots) != 1:
        findings.append(f'{key}: exactly one root container required, found {sorted(roots)}')
    for i, e in ids.items():
        if e['parent_id'] and e['parent_id'] not in ids:
            findings.append(f'{key}:{i}: missing parent {e["parent_id"]}')
            continue
        if e['parent_id']:
            p = ids[e['parent_id']]
            if int(e['start_ms']) < int(p['start_ms']) - TOL or int(e['end_ms']) > int(p['end_ms']) + TOL:
                findings.append(f'{key}:{i}: interval outside its parent {p["event_id"]}')
        seen, cur = set(), e
        while cur['parent_id']:
            if cur['parent_id'] in seen or cur['parent_id'] not in ids:
                findings.append(f'{key}:{i}: parent chain does not reach the root (cycle or missing)')
                break
            seen.add(cur['parent_id'])
            cur = ids[cur['parent_id']]
    # timing against declared predecessors
    for i, e in ids.items():
        for pr in filter(None, e['predecessors'].split(',')):
            if pr in ids and int(e['start_ms']) < int(ids[pr]['end_ms']) - TOL:
                findings.append(f'{key}:{i}: starts before predecessor {pr} ends')
    return ids


def check_terminal(ids, spec, findings, key):
    """The terminal has no successor and no work leaf runs past it."""
    for bname, b in spec['boundaries'].items():
        t = b['terminal']
        if t not in ids:
            continue
        for i, e in ids.items():
            if t in set(filter(None, e['predecessors'].split(','))) and i not in {
                    b2['terminal'] for b2 in spec['boundaries'].values()} - {t}:
                # the only lawful consumer of a boundary terminal is another boundary's identical terminal
                if i != t:
                    findings.append(f'{key}: terminal {t} has successor {i} — work after the declared '
                                    f'terminal is rejected')
        tend = int(ids[t]['end_ms'])
        for i, e in ids.items():
            if e['role'] == 'WORK_LEAF' and int(e['end_ms']) > tend + TOL:
                findings.append(f'{key}: work leaf {i} runs past the {bname} terminal {t}')


# ---------------- boundary metrics ----------------
def union_len(iv):
    total, cs, ce = 0, None, None
    for s, e in sorted(iv):
        if ce is None or s > ce:
            if ce is not None:
                total += ce - cs
            cs, ce = s, e
        else:
            ce = max(ce, e)
    if ce is not None:
        total += ce - cs
    return total


def terminal_path(members, edges, terminal, findings, key):
    """Longest predecessor path ending at the EXACT terminal (DP with cycle detection)."""
    dist, state = {}, {}

    def visit(m):
        if state.get(m) == 1:
            findings.append(f'{key}: predecessor cycle at {m}')
            return 0
        if m in dist:
            return dist[m]
        state[m] = 1
        best = 0
        for p in edges.get(m, ()):
            best = max(best, visit(p))
        dist[m] = best + members[m]
        state[m] = 2
        return dist[m]

    return visit(terminal)


def boundary_metrics(ids, spec, bname, findings, key):
    b = spec['boundaries'][bname]
    member_ids = [i for i, r in spec['events'].items()
                  if r['role'] == 'WORK_LEAF' and i not in b['exclude']]
    missing = [m for m in member_ids if m not in ids]
    if missing:
        return None
    start, terminal = b['start'], b['terminal']
    ext = b.get('external_source')
    weights, edges = {}, {}
    for m in member_ids:
        weights[m] = int(ids[m]['elapsed_ms'])
        preds = set(filter(None, ids[m]['predecessors'].split(',')))
        inside = preds & set(member_ids)
        outside = preds - set(member_ids)
        for o in sorted(outside):
            if not (ext and m == ext[1] and o == ext[0]):
                findings.append(f'{key}: {bname} member {m} has outside predecessor {o} the topology '
                                f'does not own as the boundary source')
        edges[m] = inside
    # every member reachable from the start; every member reaches the terminal
    fwd = {start}
    changed = True
    while changed:
        changed = False
        for m in member_ids:
            if m not in fwd and edges[m] & fwd:
                fwd.add(m)
                changed = True
    for m in sorted(set(member_ids) - fwd):
        findings.append(f'{key}: {bname} member {m} is not reachable from the boundary start {start}')
    back = {terminal}
    changed = True
    while changed:
        changed = False
        for m in member_ids:
            if m in back:
                for p in edges[m]:
                    if p not in back:
                        back.add(p)
                        changed = True
    for m in sorted(set(member_ids) - back):
        findings.append(f'{key}: {bname} member {m} cannot reach the boundary terminal {terminal}')
    cp = terminal_path(weights, edges, terminal, findings, key)
    wall = int(ids[terminal]['end_ms']) - int(ids[start]['start_ms'])
    work = sum(weights.values())
    un = union_len([(int(ids[m]['start_ms']), int(ids[m]['end_ms'])) for m in member_ids])
    t = {'wall': wall, 'work': work, 'critical': cp, 'union': un,
         'temporal_overlap': work - un, 'off_critical': work - cp, 'unclassified': wall - un}
    if not (0 <= cp <= work + TOL):
        findings.append(f'{key}: {bname} critical path {cp} outside [0, aggregate work {work}]')
    if cp > wall + TOL:
        findings.append(f'{key}: {bname} critical path {cp} exceeds the boundary wall {wall}')
    if un > wall + TOL:
        findings.append(f'{key}: {bname} interval union exceeds the boundary wall')
    if t['temporal_overlap'] < -TOL or t['off_critical'] < -TOL or t['unclassified'] < -TOL:
        findings.append(f'{key}: {bname} negative derived metric — inconsistent intervals')
    if bname == 'COMPLETE_PATH' and wall and t['unclassified'] / wall > 0.05:
        findings.append(f'{key}: unclassified complete-path time {t["unclassified"]}ms above 5% of '
                        f'the {wall}ms wall')
    return t


# ---------------- reachability (per-worker, measured) ----------------
def worker_intervals(evs):
    out = {}
    for e in evs:
        tag = e['worker_or_stage']
        if e['role'] == 'ATTRIBUTION' and tag in WORKER_CHUNKS:
            out[tag] = {'start': int(e['start_ms']), 'end': int(e['end_ms']),
                        'elapsed': int(e['elapsed_ms'])}
    return out


def chunk_targets(sent_rows, basis, findings):
    per = defaultdict(lambda: {'total': 0.0, 'target': 0.0,
                               **{f't_{t}': 0.0 for t in TARGET_POPS}})
    bad = {r['basis'] for r in sent_rows if r['basis'] != basis}
    if bad:
        findings.append(f'{SENTENCES}: rows carry bases {sorted(b[:12] for b in bad)} but every profile '
                        f'row must use the one CURRENT basis {basis[:12]}')
    for r in sent_rows:
        f = r['file']
        per[f]['total'] += float(r['secs'])
        if r['population'] in TARGET_POPS:
            per[f]['target'] += float(r['secs'])
            per[f][f't_{r["population"]}'] += float(r['secs'])
    return per


def reachability(per, workers, findings, key):
    """Zero-cost projection from measured per-worker intervals + same-basis sentence targets."""
    rows, zero_ends, cur_ends, starts = {}, [], [], []
    for tag, chunk in WORKER_CHUNKS.items():
        w = workers[tag]
        prof = per[chunk]['total'] * 1000
        targ = per[chunk]['target'] * 1000
        overhead = w['elapsed'] - prof
        if overhead < -TOL:
            findings.append(f'{key}: {tag} profile total {prof:.0f}ms exceeds its measured worker '
                            f'interval {w["elapsed"]}ms — unreconciled clocks')
        zero_dur = w['elapsed'] - targ
        rows[tag] = {'worker_wall_ms': w['elapsed'], 'profile_ms': prof, 'target_ms': targ,
                     'overhead_ms': max(0.0, overhead), 'zero_cost_ms': zero_dur, 'start': w['start']}
        cur_ends.append(w['end'])
        zero_ends.append(w['start'] + zero_dur)
        starts.append(w['start'])
    cur_span = max(cur_ends) - min(starts)
    zero_span = max(zero_ends) - min(starts)
    wave_saving = max(cur_ends) - max(zero_ends)
    agg_target = sum(r['target_ms'] for r in rows.values())
    if wave_saving > agg_target + TOL:
        findings.append(f'{key}: wall saving cannot exceed the aggregate target work')
    return {'rows': rows, 'cur_wave_span_ms': cur_span, 'zero_wave_span_ms': zero_span,
            'max_fixture_wall_saving_ms': wave_saving, 'max_agg_work_saving_ms': agg_target}


def zero_cost_projection(ids, spec, wave_saving_ms, findings, key):
    """Terminal-bound COMPLETE_PATH critical path with the EMIT leaf reduced by the wave saving."""
    b = spec['boundaries']['COMPLETE_PATH']
    member_ids = [i for i, r in spec['events'].items() if r['role'] == 'WORK_LEAF']
    weights, edges = {}, {}
    for m in member_ids:
        el = int(ids[m]['elapsed_ms'])
        if spec['events'][m]['class'] == 'EMIT':
            el = max(0, el - int(wave_saving_ms))
        weights[m] = el
        edges[m] = set(filter(None, ids[m]['predecessors'].split(','))) & set(member_ids)
    return terminal_path(weights, edges, b['terminal'], findings, key)


# ---------------- one metric assembly, three generated renderings ----------------
def assemble(reg, current, totals, reach):
    """Build the one in-memory metric list every generated product renders from."""
    metrics = []

    def add(mid, kind, basis, scope, statistic, unit, value, source):
        metrics.append({'metric_id': mid, 'metric_kind': kind, 'basis': basis, 'scope': scope,
                        'statistic': statistic, 'unit': unit, 'value': value, 'source': source})

    entry = [k for k in sorted(totals) if k[2].startswith('entry')]
    finals = [k for k in sorted(totals) if k[2].startswith('final') and k[0] == current]
    for key in finals:
        t = totals[key]
        add(f'run.{key[2]}.complete_path.wall_span_ms', 'SPAN', key[0],
            f'{key[1]}/{key[2]}/COMPLETE_PATH/wall', 'measured', 'ms',
            t['COMPLETE_PATH']['wall'], 'verification-dag-events.tsv')
    if entry and finals:
        e = totals[entry[0]]
        ebasis = entry[0][0]
        for bname, tag in (('PROJECT_VERIFICATION', 'project_verification'),
                           ('COMPLETE_PATH', 'complete_path')):
            works = sorted(totals[k][bname]['work'] for k in finals)
            crits = sorted(totals[k][bname]['critical'] for k in finals)
            med_w, med_c = works[len(works) // 2], crits[len(crits) // 2]
            add(f'onedag.{tag}.aggregate_work_reduction_pct', 'RATIO', current,
                f'{bname}/aggregate_work', 'median_vs_entry', 'pct',
                round(100 * (e[bname]['work'] - med_w) / e[bname]['work'], 1),
                f'current {current[:12]} vs historical {ebasis[:12]}')
            add(f'onedag.{tag}.critical_span_reduction_pct', 'RATIO', current,
                f'{bname}/critical_span', 'median_vs_entry', 'pct',
                round(100 * (e[bname]['critical'] - med_c) / e[bname]['critical'], 1),
                f'current {current[:12]} vs historical {ebasis[:12]}')
    if reach:
        savings = sorted(r['max_complete_path_wall_saving_ms'] for r in reach.values())
        aggs = sorted(r['max_agg_work_saving_ms'] for r in reach.values())
        lows = sorted(r['zero_cost_complete_lower_bound_ms'] for r in reach.values())
        add('evidence_observation.max_aggregate_work_saving_ms', 'WORK', current,
            'chunk-A..D/aggregate_work', 'median', 'ms', aggs[len(aggs) // 2],
            'measured worker intervals + sentence targets')
        add('evidence_observation.median_max_complete_path_wall_saving_ms', 'SPAN', current,
            'COMPLETE_PATH/wall', 'median', 'ms', savings[len(savings) // 2],
            'terminal-bound zero-cost projection')
        add('evidence_observation.conservative_max_complete_path_wall_saving_ms', 'SPAN', current,
            'COMPLETE_PATH/wall', 'min', 'ms', savings[0], 'terminal-bound zero-cost projection')
        add('evidence_observation.zero_cost_complete_path_lower_bound_ms', 'BOUND', current,
            'COMPLETE_PATH/wall', 'median', 'ms', lows[len(lows) // 2],
            'zero-cost critical path + unclassified')
    if current and reg.get(current):
        spec = TOPOLOGIES[reg[current]['topology_id']]
        add('validation.solve_count', 'COUNT', current, 'topology', 'exact', 'count',
            sum(1 for r in spec['events'].values() if r['solve']), reg[current]['topology_id'])
        add('validation.dune_invocation_count', 'COUNT', current, 'topology', 'exact', 'count',
            spec['dune'], reg[current]['topology_id'])
    seen = set()
    for m in metrics:
        if m['metric_id'] in seen:
            raise SystemExit(f'fido: PERF-WORK-SPAN INTERNAL — duplicate metric id {m["metric_id"]}')
        seen.add(m['metric_id'])
    return metrics


def gen_metrics(metrics):
    lines = ['# CLASS: GENERATED_VIEW — the one typed machine metric index, generated by',
             '# tools/perf-work-span.py from the same internal results as the human summaries;',
             '# regenerated and byte-compared by the gates.  DERIVED: ledger references resolve here',
             '# by exact metric_id; RATIO gain-compatibility is the scope suffix (/aggregate_work vs',
             '# /critical_span or /wall), never a substring search.',
             'metric_id\tmetric_kind\tbasis\tscope\tstatistic\tunit\tvalue\tsource']
    for m in sorted(metrics, key=lambda m: m['metric_id']):
        v = m['value']
        vs = f'{v:.1f}' if isinstance(v, float) else str(v)
        lines.append('\t'.join([m['metric_id'], m['metric_kind'], m['basis'], m['scope'],
                                m['statistic'], m['unit'], vs, m['source']]))
    return '\n'.join(lines) + '\n'


def gen_work_span(totals, metrics):
    lines = ['# CLASS: GENERATED_VIEW — human work/span summary generated by tools/perf-work-span.py',
             '# from verification-dag-events.tsv; regenerated and byte-compared by the gates.  Each',
             '# boundary has its own wall (terminal end minus boundary start); critical_path_span is',
             '# the longest predecessor path ending at the exact terminal; temporal_overlap is work',
             '# minus interval union; work_outside_critical_path is work minus the critical path.',
             'run\tboundary\twall_span_s\taggregate_task_elapsed_s\tcritical_path_span_s\t'
             'interval_union_span_s\ttemporal_overlap_s\twork_outside_critical_path_s\tunclassified_s']
    for key in sorted(totals):
        for bname in ('PROJECT_VERIFICATION', 'COMPLETE_PATH'):
            t = totals[key][bname]
            lines.append(f'{key[2]}\t{bname}\t{t["wall"]/1000:.1f}\t{t["work"]/1000:.1f}\t'
                         f'{t["critical"]/1000:.1f}\t{t["union"]/1000:.1f}\t'
                         f'{t["temporal_overlap"]/1000:.1f}\t{t["off_critical"]/1000:.1f}\t'
                         f'{t["unclassified"]/1000:.1f}')
    for m in sorted(metrics, key=lambda m: m['metric_id']):
        if m['metric_id'].startswith('onedag.'):
            lines.append(f'DELTA\t{m["metric_id"]}\t{m["value"]:.1f}\t\t\t\t\t\t')
    return '\n'.join(lines) + '\n'


def gen_reachability(per, reach, metrics):
    lines = ['# CLASS: GENERATED_VIEW — the evidence-observation ceiling, generated by',
             '# tools/perf-work-span.py from measured per-worker intervals + same-basis sentence',
             '# targets; regenerated and byte-compared by the gates.  Zero-cost wave end = max over',
             '# workers of (measured start + zero-cost residual); aggregate target work is never a',
             '# wall claim; the successor critical path is terminal-bound.',
             'chunk\tprofile_total_s\ttarget_issue_s\ttarget_cause_s\ttarget_req_s\ttarget_group_s\t'
             'target_total_s\tresidual_s']
    for tag in sorted(WORKER_CHUNKS):
        c = WORKER_CHUNKS[tag]
        p = per[c]
        lines.append(f'{c.split("/")[-1]}\t{p["total"]:.2f}\t{p["t_ISSUE_TABLE"]:.2f}\t'
                     f'{p["t_CAUSE_VIEW"]:.2f}\t{p["t_REQ_VIEW"]:.2f}\t{p["t_GROUP_VIEW"]:.2f}\t'
                     f'{p["target"]:.2f}\t{p["total"] - p["target"]:.2f}')
    lines.append('')
    lines.append('run\tmetric\tvalue_ms')
    for key in sorted(reach):
        r = reach[key]
        for tag in sorted(WORKER_CHUNKS):
            w = r['rows'][tag]
            lines.append(f'{key[2]}\tworker_{tag}_wall\t{w["worker_wall_ms"]:.0f}')
            lines.append(f'{key[2]}\tworker_{tag}_target\t{w["target_ms"]:.0f}')
            lines.append(f'{key[2]}\tworker_{tag}_overhead\t{w["overhead_ms"]:.0f}')
        for metric in ('cur_wave_span_ms', 'zero_wave_span_ms', 'max_fixture_wall_saving_ms',
                       'max_agg_work_saving_ms', 'cp_now_ms', 'successor_critical_path_ms',
                       'max_complete_path_wall_saving_ms', 'zero_cost_complete_lower_bound_ms'):
            if metric in r:
                lines.append(f'{key[2]}\t{metric}\t{r[metric]:.0f}')
    for m in sorted(metrics, key=lambda m: m['metric_id']):
        if m['metric_id'].startswith('evidence_observation.'):
            lines.append(f'ALL\t{m["metric_id"]}\t{m["value"]:.0f}')
    lines.append('ALL\trealistic_expected_saving\tUNKNOWN_PENDING_SPIKE')
    return '\n'.join(lines) + '\n'


# ---------------- validation entry ----------------
def validate(root, current_digest=None, head_digest=None, evidence_changed=False):
    findings, notices = [], []
    reg, current = check_bases(read_tsv(root / BASES), findings)
    check_currency(current, current_digest, head_digest, evidence_changed, findings, notices)
    events = read_tsv(root / EVENTS)
    by_run = defaultdict(list)
    for e in events:
        by_run[(e['basis'], e['scenario'], e['run_id'])].append(e)
    totals, reach, ids_of = {}, {}, {}
    per = None
    for key, evs in sorted(by_run.items()):
        basis = key[0]
        if basis not in reg:
            findings.append(f'{key}: unregistered basis {basis[:12]}')
            continue
        spec = TOPOLOGIES[reg[basis]['topology_id']]
        ids = check_run(evs, spec, findings, str(key))
        if findings:
            continue
        check_terminal(ids, spec, findings, str(key))
        ids_of[key] = (ids, spec)
        t = {}
        for bname in spec['boundaries']:
            bm = boundary_metrics(ids, spec, bname, findings, str(key))
            if bm is not None:
                t[bname] = bm
        if len(t) == 2:
            totals[key] = t
    if not findings:
        sent = read_tsv(root / SENTENCES)
        cur_finals = [k for k in sorted(totals) if k[0] == current and k[2].startswith('final')]
        if current and sent:
            per = chunk_targets(sent, current, findings)
        for key in cur_finals:
            ids, spec = ids_of[key]
            if not spec['attribution'] or not any(a['required'] for a in spec['attribution'].values()):
                continue
            workers = worker_intervals(by_run[key])
            missing = sorted(set(WORKER_CHUNKS) - set(workers))
            if missing:
                findings.append(f'{key}: reachability requires measured worker intervals; '
                                f'missing {missing}')
                continue
            if findings or per is None:
                continue
            r = reachability(per, workers, findings, str(key))
            r['cp_now_ms'] = totals[key]['COMPLETE_PATH']['critical']
            cp_zero = zero_cost_projection(ids, spec, r['max_fixture_wall_saving_ms'],
                                           findings, str(key))
            r['successor_critical_path_ms'] = cp_zero
            r['max_complete_path_wall_saving_ms'] = r['cp_now_ms'] - cp_zero
            r['zero_cost_complete_lower_bound_ms'] = (cp_zero
                                                      + totals[key]['COMPLETE_PATH']['unclassified'])
            reach[key] = r
    metrics = [] if findings else assemble(reg, current, totals, reach)
    return findings, notices, reg, current, totals, per, reach, metrics


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='.')
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--report', action='store_true')
    ap.add_argument('--current-digest', default='',
                    help='the candidate performance-input digest (index for make, staged index for the '
                         'hook); joined to the registry CURRENT basis under the three-frame law')
    ap.add_argument('--head-digest', default='',
                    help='digest of the committed HEAD tree — lets a committed candidate basis be '
                         'honestly historical for a proposed tree that has not re-frozen')
    ap.add_argument('--evidence-changed', choices=['yes', 'no'], default='no')
    ap.add_argument('--emit-tables', default='',
                    help='write the generated summaries + metric index here')
    ap.add_argument('--check-generated', action='store_true',
                    help='regenerate every generated product in memory and byte-compare the committed '
                         'files — the one generated-summary law shared by make perf-evidence, the '
                         'staged hook and the mutation harness')
    args = ap.parse_args()
    if args.self_test:
        sys.path.insert(0, str(Path(__file__).parent))
        from perf_work_span_selftest import run_self_test
        return run_self_test()
    root = Path(args.root)
    findings, notices, reg, current, totals, per, reach, metrics = validate(
        root, args.current_digest or None, args.head_digest or None,
        args.evidence_changed == 'yes')
    for n in notices:
        print('fido: perf-work-span — ' + n)
    if findings:
        for f in findings:
            print('perf-work-span: ' + f, file=sys.stderr)
        raise SystemExit(f'fido: PERF-WORK-SPAN FAILED — {len(findings)} violation(s)')
    expected = {GEN_WORK_SPAN: gen_work_span(totals, metrics),
                GEN_METRICS: gen_metrics(metrics)}
    if per is not None and reach:
        expected[GEN_REACH] = gen_reachability(per, reach, metrics)
    if args.emit_tables:
        out = Path(args.emit_tables)
        out.mkdir(parents=True, exist_ok=True)
        for name, text in expected.items():
            (out / name).write_text(text, encoding='utf-8')
    if args.check_generated:
        problems = []
        for name in (GEN_WORK_SPAN, GEN_REACH, GEN_METRICS):
            p = root / '.review/perf' / name
            if name in expected and not p.exists():
                problems.append(f'generated-summary law: {name}: the generator produces this summary '
                                f'but no committed file exists')
            elif name in expected and p.read_text(encoding='utf-8') != expected[name]:
                problems.append(f'generated-summary law: {name}: the committed file differs from the '
                                f'generator output — hand edits and stale regeneration are rejected')
            elif name not in expected and p.exists():
                problems.append(f'generated-summary law: {name}: a committed file exists but the '
                                f'current inputs generate no such summary')
        if problems:
            for pr in problems:
                print('perf-work-span: ' + pr, file=sys.stderr)
            raise SystemExit(f'fido: PERF-WORK-SPAN FAILED — {len(problems)} generated-summary '
                             f'violation(s)')
        print('fido: generated summaries + metric index byte-identical to the committed files')
    if args.report:
        for key in sorted(totals):
            t = totals[key]
            print(f'{key[2]}: COMPLETE wall={t["COMPLETE_PATH"]["wall"]/1000:.0f}s '
                  f'work/cp/union={t["COMPLETE_PATH"]["work"]/1000:.0f}/'
                  f'{t["COMPLETE_PATH"]["critical"]/1000:.0f}/'
                  f'{t["COMPLETE_PATH"]["union"]/1000:.0f}s  PV wall={t["PROJECT_VERIFICATION"]["wall"]/1000:.0f}s '
                  f'work/cp={t["PROJECT_VERIFICATION"]["work"]/1000:.0f}/'
                  f'{t["PROJECT_VERIFICATION"]["critical"]/1000:.0f}s '
                  f'overlap/offcp={t["PROJECT_VERIFICATION"]["temporal_overlap"]/1000:.1f}/'
                  f'{t["PROJECT_VERIFICATION"]["off_critical"]/1000:.1f}s')
    print('fido: perf-work-span OK — exact topology-owned event graphs, terminal-bound critical paths, '
          'boundary-specific walls, temporal overlap separated from off-critical work, one CURRENT '
          'basis joined to the candidate digest, reachability from measured per-worker intervals')
    return 0


if __name__ == '__main__':
    sys.exit(main())
