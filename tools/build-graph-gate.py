#!/usr/bin/env python3
"""The one-build verification-DAG structural gate.

Proves, over the retained Dockerfile/Makefile/hook text, that the single-solve verification graph holds:
exactly one production `dune build @install @all` and it lives in the shared theory-built stage; the
proof/audit, emit, and profile stages descend from theory-built (never re-rooted at rocq-base) and the
emit-controls branch descends from emit; the final artifact routes through the verified join that requires
ALL THREE branch markers (proof-audit, fresh-build, emit-controls); the exported artifact copies only the
generated module; theory-built snapshots the cache-assisted build into an ordinary layer; and each complete
path (make check, the staged hook) issues exactly one project-verification solve through the one canonical
helper, never a separate prover/emit/emit-controls/go-e2e/generated-artifact solve.

`--self-test` mutates a clean synthetic topology one condition at a time (a second Dune build in emit, a
re-rooted branch, a dropped marker edge, an extra solve, an impure artifact, a cache-only _build) and
requires each mutation to be caught by the exact rule that owns it.
"""
import argparse
import re
import sys
from pathlib import Path

DUNE = 'dune build @install @all'


def stages(dockerfile_text):
    """[(stage_name, parent, body_text)] in order."""
    out = []
    cur_name, cur_parent, cur = None, None, []
    for ln in dockerfile_text.split('\n'):
        m = re.match(r'^FROM\s+(\S+)\s+AS\s+(\S+)', ln)
        if m:
            if cur_name is not None:
                out.append((cur_name, cur_parent, '\n'.join(cur)))
            cur_name, cur_parent, cur = m.group(2), m.group(1), []
        else:
            cur.append(ln)
    if cur_name is not None:
        out.append((cur_name, cur_parent, '\n'.join(cur)))
    return out


def recipe_of(makefile_text, target):
    """The tab-indented recipe block of one Make target."""
    lines = makefile_text.split('\n')
    out, inside = [], False
    for ln in lines:
        if re.match(rf'^{re.escape(target)}:', ln):
            inside = True
            continue
        if inside:
            if ln.startswith('\t') or ln.strip() == '':
                out.append(ln)
                if ln.strip() == '' and out and not any(x.startswith('\t') for x in out[-3:]):
                    break
            else:
                break
    return '\n'.join(out)


def check_graph(dockerfile, makefile, hook, findings, helper=''):
    st = {name: (parent, body) for name, parent, body in stages(dockerfile)}

    # 17.1 one Dune builder, owned by theory-built (executable lines only — a comment is not a builder)
    def executable(body):
        return '\n'.join(ln for ln in body.split('\n') if not ln.lstrip().startswith('#'))
    dune_stages = [name for name, _, body in stages(dockerfile) if DUNE in executable(body)]
    if dune_stages != ['theory-built']:
        findings.append(f'one-dune-builder: `{DUNE}` must appear in exactly the theory-built stage; '
                        f'found in {dune_stages or "no stage"}')

    # 17.2 shared ancestry
    for branch in ('prover', 'emit', 'profile'):
        parent = st.get(branch, (None, ''))[0]
        if parent != 'theory-built':
            findings.append(f'shared-ancestry: stage {branch} must descend from theory-built, not {parent!r}')
    controls_parent = st.get('emit-controls', (None, ''))[0]
    if controls_parent != 'emit':
        findings.append(f'shared-ancestry: stage emit-controls must descend from emit (its inputs are the materialized '
                        f'trees and the wave-1 .vo), not {controls_parent!r}')
    if 'generated-module' not in st.get('go-e2e', ('', ''))[1]:
        findings.append('shared-ancestry: go-e2e must consume the generated-module layer')
    join = st.get('verified-join', (None, ''))[1]
    if '--from=prover /workspace/proof-ok' not in join:
        findings.append('join: verified-join must require the proof-audit marker (--from=prover /workspace/proof-ok)')
    if '--from=go-e2e /fresh-build-ok' not in join:
        findings.append('join: verified-join must require the fresh-build marker (--from=go-e2e /fresh-build-ok)')
    if '--from=emit-controls /workspace/emit-controls-ok' not in join:
        findings.append('join: verified-join must require the emit-controls marker '
                        '(--from=emit-controls /workspace/emit-controls-ok)')

    # 17.4 artifact purity: the final export stage copies exactly the generated module from the join
    art = st.get('generated-artifact', (None, ''))
    if art[0] != 'scratch':
        findings.append('artifact-purity: generated-artifact must be a scratch stage')
    copies = [ln for ln in art[1].split('\n') if ln.strip().startswith('COPY')]
    if copies != ['COPY --from=verified-join /generated/ /']:
        findings.append(f'artifact-purity: generated-artifact must contain exactly one COPY of the generated '
                        f'module from the verified join; found {copies}')

    # 5.3 ordinary snapshot: the cache-assisted build is snapshotted out of the mount and restored
    tb = st.get('theory-built', (None, ''))[1]
    if 'cp -a /workspace/_build /workspace/_build_snapshot' not in tb:
        findings.append('snapshot: theory-built must snapshot the cache-assisted _build out of the mount')
    if 'mv /workspace/_build_snapshot /workspace/_build' not in tb:
        findings.append('snapshot: theory-built must restore the snapshot as an ordinary layer _build')

    # 11.1 the architecture policy is proof-branch-only input: theory-built must not copy it (a prose edit
    # must never rebuild the shared theory or emit), the prover must, and emit/emit-controls/go-e2e must not
    # consume it
    if 'ARCHITECTURE.md' in st.get('theory-built', (None, ''))[1]:
        findings.append('policy-locality: theory-built copies ARCHITECTURE.md — a policy edit would rebuild '
                        'the shared theory and every branch')
    if 'ARCHITECTURE.md' not in st.get('prover', (None, ''))[1]:
        findings.append('policy-locality: the prover branch must copy ARCHITECTURE.md for the layer gate')
    for other in ('emit', 'emit-controls', 'go-e2e'):
        if 'ARCHITECTURE.md' in st.get(other, (None, ''))[1]:
            findings.append(f'policy-locality: {other} must not consume the architecture policy input')

    # 10.1 the canonical helper itself: exactly one project-verification Buildx construction targeting the
    # final artifact, and nothing capable of issuing a second solve (no second build, no bake, no recursion,
    # no eval/source) — the helper is deliberately boring and this enforces its actual grammar
    if helper:
        body = '\n'.join(ln for ln in helper.split('\n') if not ln.lstrip().startswith('#'))
        builds = body.count('docker buildx build')
        if builds != 1:
            findings.append(f'helper-one-solve: the canonical helper must construct exactly one '
                            f'`docker buildx build`, found {builds}')
        if '--target generated-artifact' not in body:
            findings.append('helper-one-solve: the helper must target the final generated-artifact')
        for bad, why in (('docker buildx bake', 'bake'), ('build-verified-artifact.sh', 'recursion'),
                         ('eval ', 'eval'), ('. /', 'sourced shell'), ('source ', 'sourced shell')):
            if bad in body:
                findings.append(f'helper-one-solve: the helper contains {why} capable of a second solve')
        execs = len([ln for ln in body.split('\n') if ln.strip().startswith('"$@"')])
        if execs < 1 or execs > 2:
            findings.append(f'helper-one-solve: the constructed command must execute in one or two mutually '
                            f'exclusive logging branches, found {execs} execution sites')

    # 9.3 no supported command may overwrite committed performance evidence: the destructive legacy
    # publisher stays deleted and no recipe writes the evidence files
    for ln in makefile.split('\n'):
        if ln.startswith('\t') and ('perf.sh' in ln or '.review/PERFORMANCE' in ln.split('#')[0]
                                    and ('>' in ln.split('#')[0] or 'cp ' in ln.split('#')[0])):
            findings.append(f'perf-route: a Makefile recipe can write committed performance evidence: {ln.strip()!r}')

    # 17.3 one complete solve per path, through the canonical helper
    for label, text in (('make check', recipe_of(makefile, 'check')), ('staged hook', hook)):
        n = text.count('build-verified-artifact.sh')
        if n != 1:
            findings.append(f'one-solve: {label} must call the canonical helper exactly once, found {n}')
        for tgt in ('--target prover', '--target emit-controls', '--target emit ', '--target go-e2e',
                    '--target generated-artifact'):   # 'emit ' keeps the space so it cannot shadow emit-controls
            if tgt in text:
                findings.append(f'one-solve: {label} still issues a separate project solve ({tgt})')


CLEAN_DOCKER = '''FROM x AS rocq-base
FROM rocq-base AS theory-built
RUN --mount=type=cache,target=/workspace/_build dune build @install @all && cp -a /workspace/_build /workspace/_build_snapshot
RUN mv /workspace/_build_snapshot /workspace/_build
FROM theory-built AS prover
COPY ARCHITECTURE.md ./
RUN gates && touch /workspace/proof-ok
FROM theory-built AS profile
RUN profile
FROM theory-built AS emit
RUN emitwork
FROM emit AS emit-controls
RUN controls && touch /workspace/emit-controls-ok
FROM scratch AS generated-module
COPY --from=emit /workspace/generated/ /generated/
FROM go AS go-e2e
COPY --from=generated-module /generated/ ./tree/
RUN gocheck && : > /fresh-build-ok
FROM scratch AS verified-join
COPY --from=prover /workspace/proof-ok /proof-ok
COPY --from=go-e2e /fresh-build-ok /fresh-build-ok
COPY --from=emit-controls /workspace/emit-controls-ok /emit-controls-ok
COPY --from=generated-module /generated/ /generated/
FROM scratch AS generated-artifact
COPY --from=verified-join /generated/ /
'''
CLEAN_MAKE = 'check:\n\tsh tools/build-verified-artifact.sh --output x\n'
CLEAN_HOOK = 'sh "$ctx/tools/build-verified-artifact.sh" --output "$tmp/pristine"\n'
CLEAN_HELPER = ('set -- docker buildx build --builder "$BUILDER" --target generated-artifact --output "x"\n'
                'if [ -n "$PLAIN" ]; then\n'
                '  "$@" --progress=plain "$CONTEXT" > "$PLAIN" 2>&1\n'
                'else\n'
                '  "$@" "$CONTEXT"\n'
                'fi\n')


def self_test():
    def run(d=CLEAN_DOCKER, m=CLEAN_MAKE, h=CLEAN_HOOK, hb=CLEAN_HELPER):
        f = []
        check_graph(d, m, h, f, hb)
        return f

    if run():
        raise SystemExit('graph-gate self-test: the clean topology was rejected: ' + str(run()))
    cases = [
        ('second dune build inserted in emit', 'one-dune-builder',
         dict(d=CLEAN_DOCKER.replace('RUN emitwork', f'RUN {DUNE}\nRUN emitwork'))),
        ('prover re-rooted at rocq-base', 'shared-ancestry',
         dict(d=CLEAN_DOCKER.replace('FROM theory-built AS prover', 'FROM rocq-base AS prover'))),
        ('emit re-rooted at rocq-base', 'shared-ancestry',
         dict(d=CLEAN_DOCKER.replace('FROM theory-built AS emit', 'FROM rocq-base AS emit'))),
        ('proof marker dependency removed from the join', 'join',
         dict(d=CLEAN_DOCKER.replace('COPY --from=prover /workspace/proof-ok /proof-ok\n', ''))),
        ('fresh-build marker dependency removed from the join', 'join',
         dict(d=CLEAN_DOCKER.replace('COPY --from=go-e2e /fresh-build-ok /fresh-build-ok\n', ''))),
        ('emit-controls marker dependency removed from the join', 'join',
         dict(d=CLEAN_DOCKER.replace('COPY --from=emit-controls /workspace/emit-controls-ok /emit-controls-ok\n', ''))),
        ('emit-controls re-rooted at theory-built (the materialized trees it audits would be absent)', 'shared-ancestry',
         dict(d=CLEAN_DOCKER.replace('FROM emit AS emit-controls', 'FROM theory-built AS emit-controls'))),
        ('emit-controls consumes the architecture policy', 'policy-locality',
         dict(d=CLEAN_DOCKER.replace('RUN controls &&', 'COPY ARCHITECTURE.md ./\nRUN controls &&'))),
        ('make check adds a separate prover solve', 'one-solve',
         dict(m=CLEAN_MAKE + '\tdocker buildx build --target prover .\n')),
        ('hook adds a separate go-e2e solve', 'one-solve',
         dict(h=CLEAN_HOOK + 'docker buildx build --target go-e2e .\n')),
        ('final artifact copies proof metadata', 'artifact-purity',
         dict(d=CLEAN_DOCKER.replace('COPY --from=verified-join /generated/ /\n',
                                     'COPY --from=verified-join /generated/ /\nCOPY --from=prover /workspace/proof-ok /\n'))),
        ('destructive legacy perf writer reintroduced', 'perf-route',
         dict(m=CLEAN_MAKE + 'perf:\n\t@sh tools/perf.sh\n')),
        ('architecture policy moved back into the shared theory stage', 'policy-locality',
         dict(d=CLEAN_DOCKER.replace('FROM theory-built AS prover',
                                     'COPY ARCHITECTURE.md ./\nFROM theory-built AS prover'))),
        ('architecture policy removed from the prover', 'policy-locality',
         dict(d=CLEAN_DOCKER.replace('COPY ARCHITECTURE.md ./\nRUN gates', 'RUN gates'))),
        ('hidden second solve inside the canonical helper', 'helper-one-solve',
         dict(hb=CLEAN_HELPER + 'docker buildx build --target prover .\n')),
        ('helper switched to buildx bake', 'helper-one-solve',
         dict(hb=CLEAN_HELPER.replace('docker buildx build', 'docker buildx bake'))),
        ('helper recursion capable of a second solve', 'helper-one-solve',
         dict(hb=CLEAN_HELPER + 'sh tools/build-verified-artifact.sh --output y\n')),
        ('cache-only _build with no ordinary snapshot', 'snapshot',
         dict(d=CLEAN_DOCKER.replace(' && cp -a /workspace/_build /workspace/_build_snapshot', '')
                            .replace('RUN mv /workspace/_build_snapshot /workspace/_build\n', 'RUN true\n'))),
    ]
    bad = 0
    for label, rule, kw in cases:
        f = run(**kw)
        if not any(x.startswith(rule) for x in f):
            print(f'  FAIL  {label} — expected a {rule} finding, got {f}')
            bad += 1
    if bad:
        raise SystemExit(f'graph-gate self-test FAILED: {bad} mutation(s) not caught')
    print(f'fido: build-graph-gate self-test OK — {len(cases)} graph mutations each caught by the exact '
          'owning rule (one dune builder, shared ancestry, marker joins, one solve per path, artifact '
          'purity, ordinary snapshot) + clean topology accepted')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default='.')
    ap.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    root = Path(args.root)
    findings = []
    check_graph((root / 'Dockerfile').read_text(encoding='utf-8'),
                (root / 'Makefile').read_text(encoding='utf-8'),
                (root / '.githooks/pre-commit').read_text(encoding='utf-8'),
                findings,
                (root / 'tools/build-verified-artifact.sh').read_text(encoding='utf-8'))
    if findings:
        for f in findings:
            print('build-graph-gate: ' + f, file=sys.stderr)
        raise SystemExit(f'fido: BUILD-GRAPH GATE FAILED — {len(findings)} violation(s)')
    print('fido: build-graph gate OK — one dune builder in the shared theory stage; proof/emit/profile descend '
          'from it and emit-controls from emit; the final artifact requires all three branch markers through the '
          'verified join and exports only the generated module; make check and the staged hook each issue one '
          'project-verification solve through the canonical helper, whose own body constructs exactly one project solve')


if __name__ == '__main__':
    main()
