#!/usr/bin/env python3
"""The working-tree inventory `make check` archives, NUL-separated on stdout.

Three properties are load-bearing and none of them survives a naive replacement:

`git ls-files --cached --others --exclude-standard` catches a rogue untracked `.go`/`.ml` that `find` would
miss and skips the gitignored residue that `find` would wrongly flag; the on-disk filter keeps only paths
that exist, so a tracked file deleted in the working tree is not reintroduced from the index — its absence
surfaces in the byte-compare instead; and the filter uses `lexists`, so a dangling symlink is retained as a
symlink rather than dropped for having no target.

Emitting names is all this does.  Reading them is `tar`'s job, without `--ignore-failed-read`, so an
existing-but-unreadable file still fails loudly.
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path


class InventoryError(Exception):
    """A defect in the inventory itself; never a finding about the tree's contents."""


def tracked_and_untracked(root: Path) -> list[bytes]:
    """Every path Git considers part of the working tree, ignored residue excluded."""
    proc = subprocess.run(
        ['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'],
        cwd=root, capture_output=True)
    if proc.returncode != 0:
        raise InventoryError(f'git ls-files failed in {root}: {proc.stderr.decode("utf-8", "replace").strip()}')
    return [name for name in proc.stdout.split(b'\0') if name]


def inventory(root: Path) -> list[bytes]:
    """The enumerated paths that are actually present on disk, in Git's order."""
    return [name for name in tracked_and_untracked(root)
            if os.path.lexists(os.path.join(os.fsencode(root), name))]


# ───────────────────────────────────────────────────────────── adversarial controls
def _git(cwd: Path, *args: str) -> None:
    subprocess.run(['git', *args], cwd=cwd, check=True, capture_output=True)


def self_test(_root: Path) -> int:
    """Prove each retained property fails when the tree exercises it, not merely that a clean tree passes."""
    failures: list[str] = []

    def check(label: str, condition: bool) -> None:
        if not condition:
            failures.append(label)

    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / 'work'
        work.mkdir()
        _git(work, 'init', '-q')
        _git(work, 'config', 'user.email', 'fido@example.invalid')
        _git(work, 'config', 'user.name', 'Fido')
        (work / '.gitignore').write_text('ignored/\n', encoding='utf-8')
        (work / 'kept.v').write_text('tracked\n', encoding='utf-8')
        (work / 'gone.v').write_text('deleted later\n', encoding='utf-8')
        _git(work, 'add', '-A')
        _git(work, 'commit', '-qm', 'base')

        (work / 'untracked.go').write_text('rogue\n', encoding='utf-8')
        (work / 'ignored').mkdir()
        (work / 'ignored' / 'residue.txt').write_text('residue\n', encoding='utf-8')
        (work / 'gone.v').unlink()
        (work / 'dangling').symlink_to('nowhere-at-all')

        names = {name.decode() for name in inventory(work)}
        check('a tracked file present on disk is retained', 'kept.v' in names)
        check('a rogue untracked file is caught', 'untracked.go' in names)
        check('gitignored residue is skipped', 'ignored/residue.txt' not in names)
        check('a tracked file deleted on disk is not resurrected from the index', 'gone.v' not in names)
        check('a dangling symlink is retained as a symlink', 'dangling' in names)

        enumerated = {name.decode() for name in tracked_and_untracked(work)}
        check('the deletion is present in the enumeration it is filtered out of', 'gone.v' in enumerated)

        missing = Path(tmp) / 'not-a-repository'
        missing.mkdir()
        try:
            inventory(missing)
            check('enumeration outside a repository fails closed', False)
        except InventoryError:
            check('enumeration outside a repository fails closed', True)

    # Failures go to STDOUT in the `  FAIL  <control>` shape the mutation harness reads, so deleting a rule
    # here makes that rule's own named control fail where the harness can see it.
    for label in failures:
        print(f'  FAIL  {label}')
    if failures:
        print(f'fido: WORKTREE-LIST SELF-TEST FAILED — {len(failures)} control(s) wrong')
        return 1
    print('fido: worktree-list self-test OK — 7 controls (retention, rogue, ignored, deletion, symlink, '
          'enumeration, fail-closed read), all executed ✓')
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description='working-tree inventory for the make check archive')
    ap.add_argument('--root', default='.', help='repository or exported-tree root')
    ap.add_argument('--self-test', action='store_true', help='run the adversarial controls')
    args = ap.parse_args()
    root = Path(args.root).resolve()
    if args.self_test:
        return self_test(root)
    try:
        names = inventory(root)
    except InventoryError as exc:
        print(f'fido: WORKTREE-LIST FAILED — {exc}', file=sys.stderr)
        return 1
    sys.stdout.buffer.write(b'\0'.join(names))
    sys.stdout.buffer.flush()
    return 0


if __name__ == '__main__':
    sys.exit(main())
