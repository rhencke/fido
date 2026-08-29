#!/usr/bin/env python3
"""The one-build verification-DAG structural gate.

Proves, over the retained Dockerfile/Makefile/hook text, that the single-solve verification graph holds:
exactly one production `dune build @install @all` and it lives in the shared theory-built stage; the
proof/audit, emit, and profile stages descend from theory-built (never re-rooted at rocq-base); the final
artifact routes through the verified join that requires BOTH branch markers; the exported artifact copies
only the generated module; theory-built snapshots the cache-assisted build into an ordinary layer; and each
complete path (make check, the staged hook) issues exactly one project-verification solve through the one
canonical helper, never a separate prover/go-e2e/generated-artifact solve.

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


def check_graph(dockerfile, makefile, hook, findings):
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
    if 'generated-module' not in st.get('go-e2e', ('', ''))[1]:
        findings.append('shared-ancestry: go-e2e must consume the generated-module layer')
    join = st.get('verified-join', (None, ''))[1]
    if '--from=prover /workspace/proof-ok' not in join:
        findings.append('join: verified-join must require the proof-audit marker (--from=prover /workspace/proof-ok)')
    if '--from=go-e2e /fresh-build-ok' not in join:
        findings.append('join: verified-join must require the fresh-build marker (--from=go-e2e /fresh-build-ok)')

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

    # 17.3 one complete solve per path, through the canonical helper
    for label, text in (('make check', recipe_of(makefile, 'check')), ('staged hook', hook)):
        n = text.count('build-verified-artifact.sh')
        if n != 1:
            findings.append(f'one-solve: {label} must call the canonical helper exactly once, found {n}')
        for tgt in ('--target prover', '--target go-e2e', '--target generated-artifact'):
            if tgt in text:
                findings.append(f'one-solve: {label} still issues a separate project solve ({tgt})')


CLEAN_DOCKER = '''FROM x AS rocq-base
FROM rocq-base AS theory-built
RUN --mount=type=cache,target=/workspace/_build dune build @install @all && cp -a /workspace/_build /workspace/_build_snapshot
RUN mv /workspace/_build_snapshot /workspace/_build
FROM theory-built AS prover
RUN gates && touch /workspace/proof-ok
FROM theory-built AS profile
RUN profile
FROM theory-built AS emit
RUN emitwork
FROM scratch AS generated-module
COPY --from=emit /workspace/generated/ /generated/
FROM go AS go-e2e
COPY --from=generated-module /generated/ ./tree/
RUN gocheck && : > /fresh-build-ok
FROM scratch AS verified-join
COPY --from=prover /workspace/proof-ok /proof-ok
COPY --from=go-e2e /fresh-build-ok /fresh-build-ok
COPY --from=generated-module /generated/ /generated/
FROM scratch AS generated-artifact
COPY --from=verified-join /generated/ /
'''
CLEAN_MAKE = 'check:\n\tsh tools/build-verified-artifact.sh --output x\n'
CLEAN_HOOK = 'sh "$ctx/tools/build-verified-artifact.sh" --output "$tmp/pristine"\n'


def self_test():
    def run(d=CLEAN_DOCKER, m=CLEAN_MAKE, h=CLEAN_HOOK):
        f = []
        check_graph(d, m, h, f)
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
        ('make check adds a separate prover solve', 'one-solve',
         dict(m=CLEAN_MAKE + '\tdocker buildx build --target prover .\n')),
        ('hook adds a separate go-e2e solve', 'one-solve',
         dict(h=CLEAN_HOOK + 'docker buildx build --target go-e2e .\n')),
        ('final artifact copies proof metadata', 'artifact-purity',
         dict(d=CLEAN_DOCKER.replace('COPY --from=verified-join /generated/ /\n',
                                     'COPY --from=verified-join /generated/ /\nCOPY --from=prover /workspace/proof-ok /\n'))),
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
                findings)
    if findings:
        for f in findings:
            print('build-graph-gate: ' + f, file=sys.stderr)
        raise SystemExit(f'fido: BUILD-GRAPH GATE FAILED — {len(findings)} violation(s)')
    print('fido: build-graph gate OK — one dune builder in the shared theory stage; proof/emit/profile descend '
          'from it; the final artifact requires both branch markers through the verified join and exports only '
          'the generated module; make check and the staged hook each issue one project-verification solve '
          'through the canonical helper')


if __name__ == '__main__':
    main()
