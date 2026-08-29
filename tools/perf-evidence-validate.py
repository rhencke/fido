#!/usr/bin/env python3
"""Structural + currentness validation of the candidate-bound performance evidence.

Two committed evidence files:

  .review/PERFORMANCE.tsv                measurement rows (COLD_COMPLETE / WARM_COMPLETE / STAGED_PRE_COMMIT)
  .review/PERFORMANCE_OPPORTUNITIES.tsv  the optimization-opportunity ledger

Each measurement row and each opportunity row is bound to a `performance-input digest` — the SHA-256 that
`tools/performance-input-digest.sh` computes over every tracked non-evidence byte of the Git INDEX (`--head`
computes the same digest at the committed HEAD).  Required relations (`tooling-baseline`, `final-candidate`)
accept only successful complete rows (`complete=yes`, `exit=0`); an incomplete row never satisfies scenario
coverage, and a baseline-only file is not current evidence.  Final-candidate currentness is three-way: bound
to the digest under validation (a frozen candidate — CURRENT), bound to the committed HEAD digest (the
proposed tree moves the basis — reported HISTORICAL, never called current), or bound to neither (foreign,
rejected).  This validator NEVER re-runs a benchmark — shape, enums, basis binding, coverage, and opportunity
currentness only, so it is cheap enough for the complete gate and the staged pre-commit hook.

`--self-test` drives the adversarial controls: each defect class the checks below reject is exercised on a
mutated clean fixture, and the clean fixture itself must pass.
"""
import argparse, os, re, sys

PERF = '.review/PERFORMANCE.tsv'
OPPS = '.review/PERFORMANCE_OPPORTUNITIES.tsv'

# every valid scenario name; STAGED_PRE_COMMIT is the historical single staged scenario the tooling
# baseline was measured under, split since into the project-cold and immediate-warm staged scenarios
SCENARIOS = ('COLD_COMPLETE', 'WARM_COMPLETE', 'STAGED_PRE_COMMIT',
             'PROJECT_COLD_STAGED_PRE_COMMIT', 'IMMEDIATE_WARM_STAGED_PRE_COMMIT')
# required coverage per relation: the baseline keeps its historical trio; a final candidate must cover
# cold, warm, and BOTH staged scenarios
REQUIRED_OF = {'tooling-baseline': ('COLD_COMPLETE', 'WARM_COMPLETE', 'STAGED_PRE_COMMIT'),
               'final-candidate': ('COLD_COMPLETE', 'WARM_COMPLETE',
                                   'PROJECT_COLD_STAGED_PRE_COMMIT', 'IMMEDIATE_WARM_STAGED_PRE_COMMIT')}
RELATIONS = ('tooling-baseline', 'final-candidate')
COMPLETE = ('yes', 'no')
OPP_CLASS = ('COMPUTATIONAL', 'INCREMENTAL', 'ORCHESTRATION', 'CACHE', 'RETAINED_SPACE', 'SCALING')
OPP_STATUS = ('OPEN_MATERIAL', 'IMPLEMENTED', 'REJECTED_MEASURED', 'REJECTED_BY_ARCHITECTURE',
              'IMMATERIAL', 'SUPERSEDED', 'BLOCKED_EXTERNAL')

PERF_COLS = ['scenario', 'relation', 'digest', 'command', 'cores', 'memory', 'boundary',
             'toolchain', 'cache', 'exit', 'wall_s', 'complete', 'dominant', 'notes']
OPP_COLS = ['id', 'basis', 'class', 'status', 'affected', 'work_gain', 'span_gain', 'hotspot',
            'constraints', 'commit', 'result', 'revisit']
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


def check_perf(text, digest, findings, mdigests, head_digest='', notices=None, evidence_changed=False):
    data = rows(text)
    notices = notices if notices is not None else []
    if not data:
        findings.append(f'{PERF}: no measurement rows')
        return
    seen = set()
    final_bases = set()
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
        # a failed or incomplete path may never be presented as a passing measurement, and an incomplete
        # path can neither satisfy a required relation nor count toward required scenario coverage
        if row['complete'] == 'yes' and row['exit'] != '0':
            findings.append(f'{PERF}:{i}: complete=yes with nonzero exit {row["exit"]!r}')
        if row['complete'] == 'no' and row['relation'] in RELATIONS:
            findings.append(f'{PERF}:{i}: complete=no row in required relation {row["relation"]!r} — '
                            'an incomplete path is not current evidence')
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
        if row['relation'] == 'final-candidate' and HEX64.match(row['digest']):
            final_bases.add(row['digest'])
        # only a successful complete row counts toward required scenario coverage
        if row['complete'] == 'yes' and row['exit'] == '0':
            seen.add((row['scenario'], row['relation']))
    # every scenario must be covered by a successful complete row for every present relation, and the
    # final-candidate relation is REQUIRED: a baseline-only file cannot pass as current evidence
    for rel in RELATIONS:
        present = {sc for (sc, rl) in seen if rl == rel}
        required = set(REQUIRED_OF[rel])
        # inherited HISTORICAL final rows are judged by the coverage model they were measured under (the
        # legacy trio); current or newly published final rows must cover the full split-scenario set
        if rel == 'final-candidate' and present and not (evidence_changed or (final_bases == {digest})):
            if not {'COLD_COMPLETE', 'WARM_COMPLETE'} <= present or not any('STAGED' in sc for sc in present):
                findings.append(f'{PERF}: historical final-candidate rows are missing basic scenario coverage')
            continue
        if present and not required <= present:
            findings.append(f'{PERF}: {rel} is missing scenarios {sorted(required - present)}')
    if not any(rl == 'final-candidate' for (_, rl) in seen):
        findings.append(f'{PERF}: no successful complete final-candidate rows — '
                        'a baseline-only file cannot pass as current evidence')
    # final-candidate currentness: NEW OR CHANGED evidence may only be published for the exact basis it was
    # measured on (basis == the digest under validation), so fabrication is rejected where it enters; evidence
    # INHERITED unchanged from the committed history is either current (a clean frozen candidate) or reported
    # HISTORICAL exactly, never described as current for a moved basis
    if len(final_bases) > 1:
        findings.append(f'{PERF}: final-candidate rows carry {len(final_bases)} different bases — '
                        'one candidate has one basis')
    elif len(final_bases) == 1:
        basis = next(iter(final_bases))
        if basis == digest:
            notices.append('final-candidate evidence is CURRENT for this exact basis')
        elif evidence_changed:
            findings.append(f'{PERF}: the proposed change publishes final-candidate rows bound to '
                            f'{basis[:12]}, not the exact basis under validation {digest[:12]} — '
                            'evidence may only be published for the tree it was measured on')
        elif head_digest and basis == head_digest:
            notices.append('basis-moved: this proposed tree changes performance-relevant bytes; the '
                           'inherited final-candidate evidence is HISTORICAL (bound to the committed '
                           'basis, not current for this tree) — freeze and re-measure before candidacy')
        else:
            notices.append(f'inherited final-candidate evidence is HISTORICAL (bound to the earlier '
                           f'frozen basis {basis[:12]}, not current for this tree) — freeze and '
                           're-measure before candidacy')
    if not seen:
        findings.append(f'{PERF}: no scenario/relation coverage')


def check_opps(text, mdigests, findings, summary_ids, derived_refs=None):
    data = rows(text)
    derived_refs = derived_refs if derived_refs is not None else []
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
        for req in ('affected', 'work_gain', 'span_gain', 'hotspot', 'constraints'):
            if not row[req].strip():
                findings.append(f'{OPPS}:{i}: empty required field {req!r}')
        # work and span are semantically distinct claims: each must carry one explicit evidence form,
        # and a machine-derived current value is a DERIVED reference into a generated file, never a copy
        for gf in ('work_gain', 'span_gain'):
            v = row[gf].strip()
            if 'see work_gain' in v or 'see span_gain' in v:
                findings.append(f'{OPPS}:{i}: {gf} defers to the other gain field — state its own evidence')
            elif not re.match(r'^(DERIVED:|MEASURED:|QUALITATIVE:|UNKNOWN_NOT_MEASURED:|NOT_APPLICABLE:)', v):
                findings.append(f'{OPPS}:{i}: {gf} must use an explicit evidence form '
                                '(DERIVED:/MEASURED:/QUALITATIVE:/UNKNOWN_NOT_MEASURED:/NOT_APPLICABLE:)')
            elif v.startswith('DERIVED:'):
                parts = v.split(':', 2)
                if len(parts) < 3 or not parts[1].strip() or not parts[2].strip():
                    findings.append(f'{OPPS}:{i}: {gf} DERIVED reference needs DERIVED:<file>:<metric>')
                else:
                    derived_refs.append((i, gf, parts[1].strip(), parts[2].strip()))
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


# single-arithmetic-owner law: raw attribution derives nothing, no second opportunity projection, and
# exactly one longest-path implementation exists (the accounting engine's).
FORBIDDEN_ATTRIBUTION_TOKENS = ('OPPS_OF', 'bundle_reachable', 'candidate_optimization', 'max_saving',
                                'chunk_wall_target')


def check_single_owner(root, findings):
    peer = os.path.join(root, '.review/perf/witnessreject-opportunities.tsv')
    if os.path.exists(peer):
        findings.append('.review/perf/witnessreject-opportunities.tsv: a second opportunity projection '
                        'is forbidden — the ledger and the generated summaries are the only routes')
    attr = os.path.join(root, 'tools/witness-profile-attribution.py')
    if os.path.exists(attr):
        src = open(attr, encoding='utf-8').read()
        for tok in FORBIDDEN_ATTRIBUTION_TOKENS:
            if tok in src:
                findings.append(f'tools/witness-profile-attribution.py: forbidden derived-judgment '
                                f'token {tok} — the attribution tool is raw classification only')
    tools_dir = os.path.join(root, 'tools')
    if os.path.isdir(tools_dir):
        needle = 'def longest' + '_path'
        n = sum(open(os.path.join(tools_dir, f), encoding='utf-8').read().count(needle)
                for f in os.listdir(tools_dir) if f.endswith('.py'))
        if n != 1:
            findings.append(f'tools: {n} longest-path implementation(s), expected exactly the one in '
                            f'the accounting engine')


# the one-DAG IMPLEMENTED claim stands only while the generated comparable lower-bound work reduction
# holds its required floor (§ one-DAG status: below it the claim is a false success, not a smaller one)
ONEDAG_ID = 'PERF-ORCH-ONE-VERIFICATION-DAG'
ONEDAG_MIN_PCT = 15.0
WS_SUMMARY = '.review/perf/verification-dag-work-span.tsv'


def check_onedag_bound(root, opp_text, findings):
    implemented = any(
        (f := ln.split('\t'))[0] == ONEDAG_ID and len(f) > 3 and f[3] == 'IMPLEMENTED'
        for ln in opp_text.splitlines() if ln and not ln.startswith('#'))
    ws = os.path.join(root, WS_SUMMARY)
    if not implemented or not os.path.exists(ws):
        return
    for ln in open(ws, encoding='utf-8'):
        f = ln.rstrip('\n').split('\t')
        if len(f) >= 3 and f[0] == 'DELTA' and f[1] == 'PROJECT_VERIFICATION_work_reduction_pct':
            try:
                v = float(f[2])
            except ValueError:
                findings.append(f'{WS_SUMMARY}: non-numeric PROJECT_VERIFICATION_work_reduction_pct')
                return
            if v < ONEDAG_MIN_PCT:
                findings.append(f'{OPPS}: {ONEDAG_ID} claims IMPLEMENTED but the generated '
                                f'PROJECT_VERIFICATION work reduction is {v}% — below the required '
                                f'{ONEDAG_MIN_PCT}% lower bound (a false success claim)')


def validate(root, digest, head_digest='', evidence_changed=False):
    findings, notices = [], []
    if not HEX64.match(digest or ''):
        return ['--digest must be the 64-hex current performance-input digest (computed on the host)'], notices
    if head_digest and not HEX64.match(head_digest):
        return ['--head-digest must be a 64-hex performance-input digest when given'], notices
    perf_path, opp_path = os.path.join(root, PERF), os.path.join(root, OPPS)
    for p, name in ((perf_path, PERF), (opp_path, OPPS)):
        if not os.path.exists(p):
            findings.append(f'{name}: missing required evidence file')
    if findings:
        return findings, notices
    summary_ids, mdigests = set(), set()
    check_single_owner(root, findings)
    check_perf(open(perf_path, encoding='utf-8').read(), digest, findings, mdigests, head_digest, notices,
               evidence_changed)
    derived_refs = []
    opp_text = open(opp_path, encoding='utf-8').read()
    check_opps(opp_text, mdigests, findings, summary_ids, derived_refs)
    check_onedag_bound(root, opp_text, findings)
    # every DERIVED reference must resolve: the generated file exists and carries the named metric/row
    for i, gf, fname, metric in derived_refs:
        gp = os.path.join(root, '.review/perf', fname)
        if not os.path.exists(gp):
            findings.append(f'{OPPS}:{i}: {gf} DERIVED reference names a missing generated file {fname}')
        elif metric not in open(gp, encoding='utf-8').read():
            findings.append(f'{OPPS}:{i}: {gf} DERIVED metric {metric!r} not found in {fname}')
    # every OPEN_MATERIAL opportunity must be visible in the current summary block of the measurement file
    perf_text = open(perf_path, encoding='utf-8').read()
    for oid in sorted(summary_ids):
        if oid not in perf_text:
            findings.append(f'{PERF}: OPEN_MATERIAL opportunity {oid} is not named in the current summary')
    return findings, notices


# ---------- adversarial self-test ----------
CLEAN_PERF = ('# perf evidence (fixture)\n'
              'scenario\trelation\tdigest\tcommand\tcores\tmemory\tboundary\ttoolchain\tcache\texit\twall_s\tcomplete\tdominant\tnotes\n')
CLEAN_OPP = ('# opportunities (fixture)\n'
             'id\tbasis\tclass\tstatus\taffected\twork_gain\tspan_gain\thotspot\tconstraints\tcommit\tresult\trevisit\n')
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
             work_gain='MEASURED:~24s aggregate target at basis ' + DG,
             span_gain='MEASURED:~5s wall ceiling at basis ' + DG, hotspot='WitnessReject',
             constraints='exact disposition stays authority', commit='n/a', result='n/a',
             revisit='when profiled')
    d.update(kw)
    return '\t'.join([d['id'], d['basis'], d['cls'], d['status'], d['affected'], d['work_gain'],
                      d['span_gain'], d['hotspot'], d['constraints'], d['commit'], d['result'],
                      d['revisit']])


def self_test():
    controls = 0
    fails = 0

    def run(perf_body, opp_body, digest=DG, head='', changed=False):
        f = []
        notices = []
        summary = set()
        mds = set()
        check_perf(CLEAN_PERF + perf_body, digest, f, mds, head, notices, changed)
        check_opps(CLEAN_OPP + opp_body, mds, f, summary)
        for oid in summary:
            if oid not in (CLEAN_PERF + perf_body):
                f.append(f'summary omits {oid}')
        return f, notices

    # the clean fixture: all three scenarios present for BOTH required relations (a baseline-only file is
    # itself a defect), the OPEN_MATERIAL opportunity named in a summary comment
    clean_perf = ('\n'.join(_perf_row(scenario=s) for s in REQUIRED_OF['tooling-baseline']) + '\n'
                  + '\n'.join(_perf_row(scenario=s, relation='final-candidate')
                               for s in REQUIRED_OF['final-candidate'])
                  + '\n# summary: PERF-COMP-X\n')
    cf, cn = run(clean_perf, _opp_row() + '\n')
    if cf:
        raise SystemExit('self-test: the clean fixture was rejected: ' + str(cf))
    if not any('CURRENT' in n for n in cn):
        raise SystemExit('self-test: the clean current fixture did not report candidate-currentness')
    # basis-moved: final rows bound to the committed HEAD basis pass with the historical notice and are
    # never described as current for the proposed tree
    mf, mn = run(clean_perf, _opp_row() + '\n', digest='d' * 64, head=DG)
    of, on = run(clean_perf, _opp_row() + '\n', digest='d' * 64, head='e' * 64)
    if of or not any('HISTORICAL' in n for n in on):
        raise SystemExit('self-test: inherited earlier-basis evidence was not honestly historical')
    if mf:
        raise SystemExit('self-test: the basis-moved fixture was rejected: ' + str(mf))
    if not any('HISTORICAL' in n for n in mn) or any('is CURRENT' in n for n in mn):
        raise SystemExit('self-test: the basis-moved fixture was not honestly reported as historical')

    cases = [
        ('incomplete path cannot satisfy required scenario coverage',
         '\n'.join(_perf_row(scenario=x, relation='final-candidate') for x in REQUIRED_OF['final-candidate'])
         + '\n' + _perf_row(scenario='COLD_COMPLETE', relation='final-candidate', exit='0', complete='no')
         + '\n' + '\n'.join(_perf_row(scenario=x) for x in REQUIRED_OF['tooling-baseline']) + '\n# summary: PERF-COMP-X\n',
         _opp_row() + '\n'),
        ('baseline-only file passes as current evidence',
         '\n'.join(_perf_row(scenario=s) for s in REQUIRED_OF['tooling-baseline']) + '\n# summary: PERF-COMP-X\n',
         _opp_row() + '\n'),
        ('missing scenario (only COLD)', _perf_row(scenario='COLD_COMPLETE') + '\n', _opp_row(status='IMPLEMENTED', commit='deadbeef') + '\n'),
        ('unknown scenario', _perf_row(scenario='NOPE') + '\n', _opp_row(status='IMPLEMENTED', commit='deadbeef') + '\n'),
        ('unknown status', clean_perf, _opp_row(status='NOPE') + '\n'),
        ('unknown class', clean_perf, _opp_row(cls='NOPE') + '\n'),
        ('duplicate opportunity id', clean_perf, _opp_row() + '\n' + _opp_row() + '\n'),
        ('missing cache subsystem', _perf_row(scenario='COLD_COMPLETE', cache='builder=x;project=cold') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('missing machine identity', _perf_row(scenario='COLD_COMPLETE', memory='') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('failed path presented as passing', _perf_row(scenario='COLD_COMPLETE', exit='1', complete='yes') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('published final-candidate rows bound to a basis other than the one measured',
         '\n'.join(_perf_row(scenario=x, relation='final-candidate', digest='b' * 64)
                    for x in REQUIRED_OF['final-candidate'])
         + '\n' + '\n'.join(_perf_row(scenario=x) for x in REQUIRED_OF['tooling-baseline']) + '\n# summary: PERF-COMP-X\n',
         _opp_row(basis='b' * 64) + '\n', dict(changed=True)),
        ('malformed digest', _perf_row(scenario='COLD_COMPLETE', digest='xyz') + '\n' + _perf_row(scenario='WARM_COMPLETE') + '\n' + _perf_row(scenario='STAGED_PRE_COMMIT') + '\n', _opp_row() + '\n'),
        ('IMPLEMENTED without commit', clean_perf, _opp_row(status='IMPLEMENTED', commit='n/a') + '\n'),
        ('OPEN_MATERIAL omitted from summary', '\n'.join(_perf_row(scenario=s) for s in SCENARIOS) + '\n', _opp_row(id='PERF-ORCH-Y') + '\n'),
        ('OPEN_MATERIAL bound to a foreign digest', clean_perf, _opp_row(basis='c' * 64) + '\n'),
        ('empty opportunity basis', clean_perf, _opp_row(basis='') + '\n'),
        ('gain deferring to the other gain field', clean_perf,
         _opp_row(span_gain='QUALITATIVE:see work_gain; span not separately claimed') + '\n'),
        ('gain without an explicit evidence form', clean_perf,
         _opp_row(work_gain='30s faster') + '\n'),
        ('DERIVED reference without file and metric', clean_perf,
         _opp_row(work_gain='DERIVED:only-a-file') + '\n'),
    ]
    for case in cases:
        label, perf_body, opp_body = case[0], case[1], case[2]
        kw = case[3] if len(case) > 3 else {}
        controls += 1
        f, _ = run(perf_body, opp_body, **kw)
        if not f:
            print(f'  FAIL  {label} — the defect was not caught')
            fails += 1

    # single-arithmetic-owner adversaries over a filesystem fixture
    import tempfile

    def owner_case(label, build, want):
        nonlocal controls, fails
        controls += 1
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, '.review/perf'))
            os.makedirs(os.path.join(d, 'tools'))
            # the clean baseline: exactly one engine implementation, nothing else
            open(os.path.join(d, 'tools/perf-work-span.py'), 'w').write(
                'def longest' + '_path():\n    pass\n')
            clean = []
            check_single_owner(d, clean)
            if clean:
                print(f'  FAIL  {label} — the clean single-owner fixture was rejected: {clean}')
                fails += 1
                return
            build(d)
            f = []
            check_single_owner(d, f)
            if not any(want in x for x in f):
                print(f'  FAIL  {label} — the defect was not caught through its own rule (got {f})')
                fails += 1

    owner_case('restored second opportunity projection', lambda d: open(
        os.path.join(d, '.review/perf/witnessreject-opportunities.tsv'), 'w').write('x\n'),
        'second opportunity projection')
    owner_case('attribution tool regained a derived judgment', lambda d: open(
        os.path.join(d, 'tools/witness-profile-attribution.py'), 'w').write('OPPS_OF = {}\n'),
        'forbidden derived-judgment token')
    owner_case('a second longest-path implementation', lambda d: open(
        os.path.join(d, 'tools/peer.py'), 'w').write('def longest' + '_path():\n    pass\n'),
        'longest-path implementation')

    # the one-DAG floor: an IMPLEMENTED claim over a generated reduction below 15% is a false success
    controls += 1
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, '.review/perf'))
        open(os.path.join(d, WS_SUMMARY), 'w').write(
            'run\tlevel\twall_span_s\nDELTA\tPROJECT_VERIFICATION_work_reduction_pct\t12.0\n')
        opp = (ONEDAG_ID + '\t' + DG + '\tORCHESTRATION\tIMPLEMENTED\tcold\tDERIVED:x:y\t'
               'DERIVED:x:y\th\tc\tabc123\tr\tn/a\n')
        f = []
        check_onedag_bound(d, opp, f)
        good = []
        check_onedag_bound(d, opp.replace('\tIMPLEMENTED\t', '\tREJECTED_MEASURED\t'), good)
        if not any('below the required' in x for x in f) or good:
            print('  FAIL  one-DAG IMPLEMENTED below its lower-bound reduction — not caught through '
                  f'its own rule (got {f}; non-implemented control got {good})')
            fails += 1
    if fails:
        raise SystemExit(f'perf-evidence self-test: {fails} defect class(es) not caught')
    print(f'fido: perf-evidence-validate self-test OK — {controls} adversarial controls '
          '(successful-complete coverage incl. the complete=no and baseline-only adversaries, enums, '
          'cache/machine identity, three-way basis binding, opportunity currentness) '
          '+ clean current and basis-moved fixtures accepted with honest wording')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='.')
    ap.add_argument('--digest', default='', help='performance-input digest of the basis under validation '
                    '(the Git index: the staged/proposed tree)')
    ap.add_argument('--head-digest', default='', help='performance-input digest of the committed HEAD tree; '
                    'lets evidence bound to the last committed basis be reported as historical, never current')
    ap.add_argument('--evidence-changed', choices=['yes', 'no'], default='no',
                    help='whether the proposed change modifies the measurement file itself; new or '
                         'changed measurements must be bound to the exact basis under validation')
    ap.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    findings, notices = validate(args.root, args.digest, args.head_digest, args.evidence_changed == 'yes')
    for n in notices:
        print('fido: perf-evidence — ' + n)
    if findings:
        for f in findings:
            print('perf-evidence: ' + f, file=sys.stderr)
        raise SystemExit('fido: PERF-EVIDENCE FAILED — ' + str(len(findings)) + ' violation(s)')
    print('fido: perf-evidence OK — rows and the opportunity ledger are well-formed; every required scenario '
          'has a successful complete row in both required relations; the final-candidate basis is stated '
          'above exactly (current or historical)')


if __name__ == '__main__':
    main()
