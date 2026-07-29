#!/usr/bin/env python3
"""The Build Observatory — one runner, validator, writer and comparator for Fido's timing evidence.

Fido has no measured account of what its build costs. Full acceptance approaches minutes, and nobody can say
which part is proof, extraction, transport, Go validation, policy gates or publication, which Rocq modules are
slow, what rebuild set an edit implies, or where the Make path repeats work Buildx already did. Opinions about
build cost are cheap and have been wrong before; M2 exists to replace them with one reproducible observation.

The permanent shape is five parts, and this file is one of them:

    .review/BUILD_OBSERVATORY_SUITE.json   the sole command and scenario registry
    .review/BUILD_OBSERVATION.json         one tracked canonical observation
    tools/build-observatory.py             this runner, validator, writer and comparator
    .build-observatory/                    ignored local run bundles and raw logs
    make observe                           the single public entry point

Git history is the historical observation database. Each accepted replacement of the tracked observation
becomes history through Git, so no growing tracked ledger is appended to.

THIS FILE IS A STUB. The M1 acceptance closeout installs the path relation — the registry, the canonical
observation, the recommendations ledger, the contract and the obligation matrix — so that every typed
reference resolves and the D-24 manifest is complete from the first commit. Measurement, selection,
recording and comparison are M2 implementation work and are not here yet.

An execution mode therefore FAILS rather than returning. A measurement facility that answered an unimplemented
request with an empty result would report "no regression" for a suite it never ran, which is the one answer a
timing tool must never be able to give by accident.
"""

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONTRACT_REL = '.review/M2_BUILD_OBSERVATORY.md'
MATRIX_REL = '.review/M2_OBLIGATION_MATRIX.tsv'
SUITE_REL = '.review/BUILD_OBSERVATORY_SUITE.json'
OBSERVATION_REL = '.review/BUILD_OBSERVATION.json'
RECOMMENDATIONS_REL = '.review/M2_RECOMMENDATIONS.tsv'
DECLARED = (CONTRACT_REL, MATRIX_REL, SUITE_REL, OBSERVATION_REL, RECOMMENDATIONS_REL)

PENDING = ('M2 implementation is pending: the Build Observatory registry, runner, recorder and comparator '
           'are not implemented yet, and this tool will not report a measurement it did not take.')


class ObservatoryError(Exception):
    """A defect in the observatory's own inputs, distinct from a slow or failing measured command."""


def resolve(root: Path) -> list[Path]:
    """Every path this tool owns must exist, because a dangling one silently disarms a later gate."""
    missing = [rel for rel in DECLARED if not (root / rel).is_file()]
    if missing:
        raise ObservatoryError(f'{len(missing)} declared observatory path(s) do not resolve: {missing}')
    return [root / rel for rel in DECLARED]


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description='Fido Build Observatory (M2 implementation pending)')
    p.add_argument('--root', default=str(ROOT))
    p.add_argument('--paths', action='store_true',
                   help='verify that every declared observatory path resolves')
    p.add_argument('--only', help='command or group IDs to select (M2)')
    p.add_argument('--scenario', help='scenario IDs to select (M2)')
    p.add_argument('--base', help='observation to compare against (M2)')
    p.add_argument('--compare', help='observation to compare (M2)')
    p.add_argument('--record', action='store_true', help='replace the canonical observation (M2)')
    p.add_argument('--list', action='store_true', help='print every stable command ID (M2)')
    p.add_argument('--usage', action='store_true', help='print the generated usage text (M2)')
    p.add_argument('--self-test', action='store_true', help='the deterministic control fixtures (M2)')
    args = p.parse_args(argv)
    root = Path(args.root).resolve()

    try:
        paths = resolve(root)
    except ObservatoryError as e:
        print(f'fido: BUILD-OBSERVATORY FAILED — {e}', file=sys.stderr)
        return 1

    if args.paths:
        print(f'fido: build-observatory paths OK — {len(paths)} declared path(s) resolve under {root}; '
              f'{PENDING} ✓')
        return 0

    print(f'fido: BUILD-OBSERVATORY UNAVAILABLE — {PENDING}', file=sys.stderr)
    return 1


if __name__ == '__main__':
    sys.exit(main())
