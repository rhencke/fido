#!/usr/bin/env python3
"""The sole performance accounting and successor-reachability authority.

Consumes the verified basis registry, the normalized event table, and the raw sentence attribution; enforces
the required-event grammar of each supported measurement topology; computes every governing metric from
measured intervals and declared predecessors; and deterministically generates the committed summaries, which
the gates regenerate into temporary output and byte-compare.

Metrics (never conflated, none called CPU time — no direct CPU accounting exists through BuildKit, so
elapsed task time is the declared work proxy):

  wall_span_s              measured start-to-finish wall of the boundary
  aggregate_task_elapsed_s sum of the required non-nested WORK_LEAF durations
  critical_path_span_s     LONGEST PREDECESSOR-RESPECTING PATH through the required leaf DAG
  interval_union_span_s    union of measured leaf intervals — descriptive only, never called critical path
  parallel_overlap_s       aggregate task elapsed minus critical-path span
  unclassified_s           wall not covered by the declared partition (<=5% complete-path law)

Topology grammar: a run declares its basis, whose registry row names one supported topology; the required
event classes, solve counts, Dune counts, predecessor edges, and terminal are enforced — omitting the proof
event (or any required event) is rejected even when the remaining rows are internally consistent, and
unexpected WORK_LEAF/CONTAINER classes are rejected until the registry owns them.

Boundaries are explicit per topology: PROJECT_VERIFICATION = every required work leaf after the policy gates
through the final generated-artifact byte comparison (the historical root-level artifact operation included);
COMPLETE_PATH adds the policy gates.  Entry/final comparisons are like-for-like by construction.

Reachability (the evidence-observation ceiling) uses measured per-worker intervals and same-basis sentence
targets — no universal worker-load or serial-overhead constants, no aggregate/worker-count division, and
aggregate removable work is never copied into a wall-saving claim.
"""
import argparse
import csv
import sys
from collections import defaultdict
from pathlib import Path

BASES = '.review/perf/performance-bases.tsv'
EVENTS = '.review/perf/verification-dag-events.tsv'
SENTENCES = '.review/perf/witnessreject-sentences.tsv'

ROLES = ('CONTAINER', 'WORK_LEAF', 'ATTRIBUTION')
CLASSES = ('POLICY', 'THEORY', 'PROOF', 'EMIT', 'FIXTURE_WORKER', 'GO', 'JOIN_EXPORT',
           'ARTIFACT_COMPARE', 'WAIT_OR_OVERHEAD', 'UNCLASSIFIED')
TARGET_POPS = ('ISSUE_TABLE', 'CAUSE_VIEW', 'REQ_VIEW', 'GROUP_VIEW')
WORKER_CHUNKS = {'chunk-A': 'e2e/WitnessRejectA.v', 'chunk-B': 'e2e/WitnessRejectB.v',
                 'chunk-C': 'e2e/WitnessRejectC.v', 'chunk-D': 'e2e/WitnessRejectD.v'}
TOL = 1500  # ms clock tolerance

# the fixed registry of supported measurement topologies: required WORK_LEAF class multiset, required
# verification-solve operation count, Dune (THEORY) count, terminal class, and required predecessor edges
# over classes (every target-class leaf must declare a source-class predecessor)
TOPOLOGIES = {
    'ONE_DAG_V1': {
        'leaf_classes': {'POLICY': 1, 'WAIT_OR_OVERHEAD': (0, 3), 'THEORY': 1, 'PROOF': 1,
                         'EMIT': 1, 'GO': 1, 'JOIN_EXPORT': 1, 'ARTIFACT_COMPARE': 1},
        'solve_ops': 1,
        'dune': 1,
        'terminal': 'ARTIFACT_COMPARE',
        'edges': [('THEORY', 'PROOF'), ('THEORY', 'EMIT'), ('EMIT', 'GO'),
                  ('PROOF', 'JOIN_EXPORT'), ('GO', 'JOIN_EXPORT'), ('JOIN_EXPORT', 'ARTIFACT_COMPARE')],
        'serial': False,
    },
    'THREE_SOLVE_POST_CHUNKING_V1': {
        'leaf_classes': {'POLICY': 1, 'WAIT_OR_OVERHEAD': (2, 4), 'THEORY': 2, 'PROOF': 1,
                         'EMIT': 1, 'GO': 1, 'JOIN_EXPORT': 1},
        'solve_ops': 3,
        'dune': 2,
        'terminal': 'JOIN_EXPORT',
        'edges': [('PROOF', 'EMIT'), ('EMIT', 'GO'), ('GO', 'JOIN_EXPORT')],
        'serial': True,
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


# ---------------- events: structure + grammar ----------------
def check_events(events, reg, findings):
    by_run = defaultdict(list)
    for e in events:
        by_run[(e['basis'], e['scenario'], e['run_id'])].append(e)
    for key, evs in by_run.items():
        basis = key[0]
        if basis not in reg:
            findings.append(f'{key}: unregistered basis {basis[:12]}')
            continue
        topo_id = reg[basis]['topology_id']
        spec = TOPOLOGIES[topo_id]
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
                if abs((en - s) - el) > TOL:
                    findings.append(f'{key}:{e["event_id"]}: elapsed {el} != end-start {en - s}')
            except ValueError:
                findings.append(f'{key}:{e["event_id"]}: non-numeric interval')
                continue
            if e['role'] == 'WORK_LEAF' and e['result'] != 'ok':
                findings.append(f'{key}:{e["event_id"]}: a failed task cannot be counted as work')
        for e in evs:
            if e['parent_id'] and e['parent_id'] not in ids:
                findings.append(f'{key}:{e["event_id"]}: missing parent {e["parent_id"]}')
                continue
            if e['parent_id']:
                p = ids[e['parent_id']]
                if int(e['start_ms']) < int(p['start_ms']) - TOL or int(e['end_ms']) > int(p['end_ms']) + TOL:
                    findings.append(f'{key}:{e["event_id"]}: interval outside its parent {p["event_id"]}')
            for pred in filter(None, e['predecessors'].split(',')):
                if pred not in ids:
                    findings.append(f'{key}:{e["event_id"]}: unknown predecessor {pred}')
                elif int(e['start_ms']) < int(ids[pred]['end_ms']) - TOL:
                    findings.append(f'{key}:{e["event_id"]}: starts before predecessor {pred} ends')

        def ancestors(e):
            seen = set()
            while e['parent_id'] and e['parent_id'] in ids and e['parent_id'] not in seen:
                seen.add(e['parent_id'])
                e = ids[e['parent_id']]
                yield e
        for e in evs:
            if e['role'] == 'WORK_LEAF':
                for a in ancestors(e):
                    if a['role'] == 'WORK_LEAF':
                        findings.append(f'{key}:{e["event_id"]}: WORK_LEAF nested under WORK_LEAF '
                                        f'{a["event_id"]}')

        # required-event grammar: the topology owns the complete leaf set
        leaves = [e for e in evs if e['role'] == 'WORK_LEAF']
        counts = defaultdict(int)
        for e in leaves:
            counts[e['class']] += 1
        for cls, want in spec['leaf_classes'].items():
            lo, hi = want if isinstance(want, tuple) else (want, want)
            if not lo <= counts.get(cls, 0) <= hi:
                findings.append(f'{key}: topology {topo_id} requires {want} {cls} work leaf/leaves, '
                                f'found {counts.get(cls, 0)}')
        for cls, n in counts.items():
            if cls not in spec['leaf_classes'] and n:
                findings.append(f'{key}: unexpected {cls} work leaf — the topology registry does not own it')
        solves = sum(1 for e in evs if e['worker_or_stage'] == 'verification-solve')
        if solves != spec['solve_ops']:
            findings.append(f'{key}: topology {topo_id} requires {spec["solve_ops"]} verification-solve '
                            f'operation(s), found {solves}')
        if counts.get('THEORY', 0) != spec['dune']:
            findings.append(f'{key}: topology {topo_id} requires {spec["dune"]} Dune invocation(s), '
                            f'found {counts.get("THEORY", 0)}')
        by_cls = defaultdict(list)
        for e in leaves:
            by_cls[e['class']].append(e)
        for src_cls, dst_cls in spec['edges']:
            for dst in by_cls.get(dst_cls, []):
                preds = [ids[p]['class'] for p in filter(None, dst['predecessors'].split(','))
                         if p in ids]
                if src_cls not in preds:
                    findings.append(f'{key}: {dst_cls} leaf {dst["event_id"]} must declare a {src_cls} '
                                    f'predecessor (topology {topo_id})')
        terms = by_cls.get(spec['terminal'], [])
        if len(terms) != 1:
            findings.append(f'{key}: topology {topo_id} requires exactly one terminal '
                            f'{spec["terminal"]} leaf')
        if spec['serial']:
            ordered = sorted(leaves, key=lambda e: int(e['start_ms']))
            for a, b in zip(ordered, ordered[1:]):
                if int(b['start_ms']) < int(a['end_ms']) - TOL:
                    findings.append(f'{key}: serial topology violated — {b["event_id"]} overlaps '
                                    f'{a["event_id"]}')
    return by_run


# ---------------- metrics ----------------
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


def longest_path(leaves, ids, findings, key):
    """The real predecessor-respecting longest path (DP over the declared WORK_LEAF DAG)."""
    dist, state = {}, {}
    leaf_ids = {e['event_id'] for e in leaves}

    def visit(e):
        eid = e['event_id']
        if state.get(eid) == 1:
            findings.append(f'{key}: predecessor cycle at {eid}')
            return 0
        if eid in dist:
            return dist[eid]
        state[eid] = 1
        best = 0
        for p in filter(None, e['predecessors'].split(',')):
            if p in ids and p in leaf_ids:
                best = max(best, visit(ids[p]))
        dist[eid] = best + int(e['elapsed_ms'])
        state[eid] = 2
        return dist[eid]

    return max((visit(e) for e in leaves), default=0)


def run_totals(evs, findings, key):
    ids = {e['event_id']: e for e in evs}
    leaves = [e for e in evs if e['role'] == 'WORK_LEAF']
    root = [e for e in evs if not e['parent_id']]
    wall = max(int(e['end_ms']) for e in root) - min(int(e['start_ms']) for e in root)
    # explicit topology-owned boundaries: PV = every required leaf except POLICY; COMPLETE = all leaves
    pv = [e for e in leaves if e['class'] != 'POLICY']

    def m(sel):
        work = sum(int(e['elapsed_ms']) for e in sel)
        cp = longest_path(sel, ids, findings, key)
        un = union_len([(int(e['start_ms']), int(e['end_ms'])) for e in sel])
        return {'work': work, 'critical': cp, 'union': un, 'overlap': work - cp}

    comp, pvm = m(leaves), m(pv)
    covered = union_len([(int(e['start_ms']), int(e['end_ms'])) for e in leaves])
    uncl = wall - covered
    if wall and uncl / wall > 0.05:
        findings.append(f'{key}: unclassified complete-path time {uncl}ms above 5% of the {wall}ms wall')
    for label, t in (('complete', comp), ('pv', pvm)):
        if t['critical'] > wall + TOL:
            findings.append(f'{key}: {label} critical path {t["critical"]} exceeds the wall {wall}')
        if t['critical'] > t['work'] + TOL:
            findings.append(f'{key}: {label} critical path exceeds aggregate work')
        if t['union'] > wall + TOL:
            findings.append(f'{key}: {label} interval union exceeds the wall')
    return {'wall': wall, 'complete': comp, 'pv': pvm, 'unclassified': uncl}


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
        findings.append(f'{SENTENCES}: rows carry bases {sorted(b[:12] for b in bad)} but the current '
                        f'projection requires {basis[:12]} — one projection uses one exact basis')
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


def complete_path_projection(evs, wave_saving_ms, findings, key):
    """Recompute the longest path with the EMIT leaf reduced by the fixture-wave saving."""
    reduced = []
    for e in evs:
        if e['role'] == 'WORK_LEAF' and e['class'] == 'EMIT':
            e = dict(e, elapsed_ms=str(max(0, int(e['elapsed_ms']) - int(wave_saving_ms))))
        reduced.append(e)
    rids = {e['event_id']: e for e in reduced}
    leaves = [e for e in reduced if e['role'] == 'WORK_LEAF']
    return longest_path(leaves, rids, findings, key)


# ---------------- deterministic generation ----------------
def gen_work_span(totals_by_run, current=None):
    lines = ['# GENERATED by tools/perf-work-span.py from verification-dag-events.tsv — regenerated and',
             '# byte-compared by the gates; a hand edit fails validation.  critical_path_span is the real',
             '# predecessor longest path; interval_union_span is a separate descriptive metric; work and',
             '# span are never conflated and neither is CPU time.',
             'run\tlevel\twall_span_s\taggregate_task_elapsed_s\tcritical_path_span_s\t'
             'interval_union_span_s\tparallel_overlap_s\tunclassified_s']
    for key in sorted(totals_by_run):
        t = totals_by_run[key]
        for lvl, name in (('pv', 'PROJECT_VERIFICATION'), ('complete', 'COMPLETE_PATH')):
            m = t[lvl]
            lines.append(f'{key[2]}\t{name}\t{t["wall"]/1000:.1f}\t{m["work"]/1000:.1f}\t'
                         f'{m["critical"]/1000:.1f}\t{m["union"]/1000:.1f}\t{m["overlap"]/1000:.1f}\t'
                         f'{t["unclassified"]/1000:.1f}')
    entry = [k for k in sorted(totals_by_run) if k[2].startswith('entry')]
    # the entry/final delta compares the verified historical entry against CURRENT-basis final runs only;
    # a historical one-DAG run informs its own rows but never the current claim
    final = [k for k in sorted(totals_by_run)
             if k[2].startswith('final') and (current is None or k[0] == current)]
    if entry and final:
        e = totals_by_run[entry[0]]
        for lvl, name in (('pv', 'PROJECT_VERIFICATION'), ('complete', 'COMPLETE_PATH')):
            works = sorted(totals_by_run[k][lvl]['work'] for k in final)
            crits = sorted(totals_by_run[k][lvl]['critical'] for k in final)
            med_w, med_c = works[len(works) // 2], crits[len(crits) // 2]
            lines.append(f'DELTA\t{name}_work_reduction_pct\t'
                         f'{100 * (e[lvl]["work"] - med_w) / e[lvl]["work"]:.1f}\t\t\t\t\t')
            lines.append(f'DELTA\t{name}_critical_span_reduction_pct\t'
                         f'{100 * (e[lvl]["critical"] - med_c) / e[lvl]["critical"]:.1f}\t\t\t\t\t')
    return '\n'.join(lines) + '\n'


def gen_reachability(per, reach_by_run):
    lines = ['# GENERATED by tools/perf-work-span.py — the evidence-observation ceiling from measured',
             '# per-worker intervals + same-basis sentence targets; zero-cost wave end = max over workers of',
             '# (measured start offset + zero-cost residual); aggregate target work is never a wall claim.',
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
    savings = []
    for key in sorted(reach_by_run):
        r = reach_by_run[key]
        for tag in sorted(WORKER_CHUNKS):
            w = r['rows'][tag]
            lines.append(f'{key[2]}\tworker_{tag}_wall\t{w["worker_wall_ms"]:.0f}')
            lines.append(f'{key[2]}\tworker_{tag}_target\t{w["target_ms"]:.0f}')
            lines.append(f'{key[2]}\tworker_{tag}_overhead\t{w["overhead_ms"]:.0f}')
        for metric in ('cur_wave_span_ms', 'zero_wave_span_ms', 'max_fixture_wall_saving_ms',
                       'max_agg_work_saving_ms', 'cp_now_ms', 'cp_zero_ms',
                       'max_complete_path_wall_saving_ms', 'zero_cost_complete_lower_bound_ms'):
            if metric in r:
                lines.append(f'{key[2]}\t{metric}\t{r[metric]:.0f}')
        if 'max_complete_path_wall_saving_ms' in r:
            savings.append(r['max_complete_path_wall_saving_ms'])
    if savings:
        s = sorted(savings)
        lines.append(f'ALL\tmedian_max_complete_path_wall_saving_ms\t{s[len(s) // 2]:.0f}')
        lines.append(f'ALL\tconservative_max_complete_path_wall_saving_ms\t{s[0]:.0f}')
    lines.append('ALL\trealistic_expected_saving\tUNKNOWN_PENDING_SPIKE')
    return '\n'.join(lines) + '\n'


# ---------------- validation entry ----------------
def validate(root):
    findings = []
    reg, current = check_bases(read_tsv(root / BASES), findings)
    by_run = check_events(read_tsv(root / EVENTS), reg, findings)
    totals, reach = {}, {}
    per = None
    if not findings:
        sent = read_tsv(root / SENTENCES)
        for key, evs in sorted(by_run.items()):
            totals[key] = run_totals(evs, findings, str(key))
        cur_finals = [k for k in sorted(by_run) if k[0] == current and k[2].startswith('final')]
        if cur_finals:
            per = chunk_targets(sent, current, findings)
        for key in cur_finals:
            workers = worker_intervals(by_run[key])
            missing = sorted(set(WORKER_CHUNKS) - set(workers))
            if missing:
                findings.append(f'{key}: reachability requires measured worker intervals; '
                                f'missing {missing}')
                continue
            if findings:
                continue
            r = reachability(per, workers, findings, str(key))
            r['cp_now_ms'] = totals[key]['complete']['critical']
            cp_zero = complete_path_projection(by_run[key], r['max_fixture_wall_saving_ms'],
                                               findings, str(key))
            r['cp_zero_ms'] = cp_zero
            r['max_complete_path_wall_saving_ms'] = r['cp_now_ms'] - cp_zero
            r['zero_cost_complete_lower_bound_ms'] = cp_zero + totals[key]['unclassified']
            reach[key] = r
    return findings, reg, current, totals, per, reach


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='.')
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--report', action='store_true')
    ap.add_argument('--emit-tables', default='',
                    help='write the generated summaries here (the gates generate to a temp dir and '
                         'byte-compare the committed files)')
    ap.add_argument('--check-generated', action='store_true',
                    help='regenerate every summary in memory and byte-compare the committed files — '
                         'the one generated-summary law shared by make perf-evidence, the staged hook '
                         'and the mutation harness')
    args = ap.parse_args()
    if args.self_test:
        sys.path.insert(0, str(Path(__file__).parent))
        from perf_work_span_selftest import run_self_test
        return run_self_test()
    root = Path(args.root)
    findings, reg, current, totals, per, reach = validate(root)
    if findings:
        for f in findings:
            print('perf-work-span: ' + f, file=sys.stderr)
        raise SystemExit(f'fido: PERF-WORK-SPAN FAILED — {len(findings)} violation(s)')
    expected = {'verification-dag-work-span.tsv': gen_work_span(totals, current)}
    if per is not None and reach:
        expected['verification-dag-reachability.tsv'] = gen_reachability(per, reach)
    if args.emit_tables:
        out = Path(args.emit_tables)
        out.mkdir(parents=True, exist_ok=True)
        for name, text in expected.items():
            (out / name).write_text(text, encoding='utf-8')
    if args.check_generated:
        problems = []
        for name in ('verification-dag-work-span.tsv', 'verification-dag-reachability.tsv'):
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
            raise SystemExit(f'fido: PERF-WORK-SPAN FAILED — {len(problems)} generated-summary violation(s)')
        print('fido: generated summaries byte-identical to the committed files')
    if args.report:
        for key in sorted(totals):
            t = totals[key]
            print(f'{key[2]}: wall={t["wall"]/1000:.0f}s '
                  f'PV work/cp/union/overlap={t["pv"]["work"]/1000:.0f}/{t["pv"]["critical"]/1000:.0f}/'
                  f'{t["pv"]["union"]/1000:.0f}/{t["pv"]["overlap"]/1000:.0f}s '
                  f'COMPLETE work/cp={t["complete"]["work"]/1000:.0f}/'
                  f'{t["complete"]["critical"]/1000:.0f}s uncl={t["unclassified"]/1000:.1f}s')
    print('fido: perf-work-span OK — bases registered, required topology complete for every run, critical '
          'path computed as the predecessor longest path (interval union reported separately), boundaries '
          'like-for-like, reachability from measured per-worker intervals')
    return 0


if __name__ == '__main__':
    sys.exit(main())
