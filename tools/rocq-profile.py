#!/usr/bin/env python3
"""Rank a `rocq c -time` log by cost, per sentence and per declaration.

Rocq prints one record per sentence, keyed by BYTE OFFSETS into the source and
with the sentence text mangled (spaces to `~`) and truncated:

    Chars 1579 - 1653 [From~Stdlib~Require~Import~NAr...] 0.262 secs (0.238u,0.024s)

Byte offsets are useless to a human and the truncated echo is worse, so this
slices the real sentence back out of the file, maps the offset to a line, and
attributes each sentence to the declaration it belongs to — a `Proof`/`Qed` pair
rolls up into the `Theorem` above it, which is the number that actually answers
"what is slow".

Reports only.  Changes nothing, gates nothing.
"""
import re
import sys
from pathlib import Path

TIMED = re.compile(r'^Chars\s+(\d+)\s+-\s+(\d+)\s+\[[^\]]*\]\s+([0-9]+\.?[0-9]*)\s+secs', re.M)

# a top-level Rocq declaration — what a slow sentence should be blamed on
DECL = re.compile(r'^\s*(?:Global\s+|Local\s+|Program\s+|#\[[^\]]*\]\s*)*'
                  r'(Theorem|Lemma|Corollary|Remark|Fact|Proposition|Example|Definition|Fixpoint|'
                  r'CoFixpoint|Inductive|CoInductive|Variant|Record|Instance|Module\s+Type|Module|'
                  r'Print\s+Assumptions|Compute|Goal|Axiom|Parameter|Notation|Arguments)\b'
                  r'\s*([A-Za-z0-9_\'.]*)')


def line_starts(data: bytes):
    starts, pos = [0], data.find(b'\n')
    while pos != -1:
        starts.append(pos + 1)
        pos = data.find(b'\n', pos + 1)
    return starts


def line_of(starts, off):
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= off:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


def main(argv):
    if len(argv) < 3:
        print('usage: rocq-profile.py <source.v> <time-log> [top-n]', file=sys.stderr)
        return 2
    src, log = Path(argv[1]), Path(argv[2])
    top = int(argv[3]) if len(argv) > 3 else 40

    data = src.read_bytes()
    starts = line_starts(data)
    records = [(int(a), int(b), float(s)) for a, b, s in TIMED.findall(
        log.read_text(encoding='utf-8', errors='replace'))]
    if not records:
        print(f'fido: profile — no timed sentences parsed from {log}', file=sys.stderr)
        return 1
    records.sort()

    def text_of(a, b):
        return ' '.join(data[a:b].decode('utf-8', 'replace').split())

    # attribute in file order: a declaration claims itself and everything after it
    # until the next declaration, so Proof/Qed rolls into its Theorem
    owner, per_decl, rows = '(file preamble)', {}, []
    for a, b, secs in records:
        body = text_of(a, b)
        m = DECL.match(body)
        if m:
            owner = (m.group(2) or '').strip() or m.group(1)
        per_decl[owner] = per_decl.get(owner, 0.0) + secs
        rows.append((line_of(starts, a), secs, body, owner))

    total = sum(r[1] for r in rows)
    print(f'fido: rocq profile — {src}')
    print(f'  {len(rows)} sentences, {total:.2f} s of measured elaboration\n')

    print(f'  slowest {top} sentences')
    print(f'  {"line":>7}  {"secs":>7}  {"%":>5}  sentence')
    for line, secs, body, _ in sorted(rows, key=lambda r: -r[1])[:top]:
        print(f'  {line:>7}  {secs:>7.3f}  {100.0 * secs / total if total else 0:>5.1f}  {body[:100]}')

    print(f'\n  slowest {top} declarations (their sentences rolled up)')
    print(f'  {"secs":>7}  {"%":>5}  {"cum%":>5}  declaration')
    cum = 0.0
    for name, secs in sorted(per_decl.items(), key=lambda kv: -kv[1])[:top]:
        cum += secs
        print(f'  {secs:>7.3f}  {100.0 * secs / total if total else 0:>5.1f}'
              f'  {100.0 * cum / total if total else 0:>5.1f}  {name}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
