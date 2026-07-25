#!/usr/bin/env python3
"""Whitespace/format check against .editorconfig.

Property resolution is delegated ENTIRELY to the EditorConfig reference implementation (the `editorconfig` C
core, apt-pinned), so glob matching, nesting and inheritance are the spec's, not ours.  This script only reads
the resolved properties and reports files that contradict them.

It REPORTS; it never rewrites.  This repository is full of byte-exact artifacts — generated Go compared against
a pristine build, reviewed goldens pinning control characters, frozen evidence whose bytes are cited by hash
elsewhere — so silently editing files here is exactly the wrong reflex.

Deliberately NOT a gate: `make check` and the pre-commit hook stay code-level.  Run it when you want it.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(subprocess.run(["git", "rev-parse", "--show-toplevel"],
                           capture_output=True, text=True, check=True).stdout.strip())


def tracked_files() -> list[Path]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout
    return [ROOT / n for n in out.split("\0") if n]


def resolve(paths: list[Path]) -> dict[Path, dict[str, str]]:
    """Ask the reference implementation for each path's properties (batched)."""
    props: dict[Path, dict[str, str]] = {}
    for i in range(0, len(paths), 200):
        chunk = [str(p) for p in paths[i:i + 200]]
        out = subprocess.run(["editorconfig", *chunk],
                             capture_output=True, text=True, check=True).stdout
        cur: Path | None = None
        for line in out.splitlines():
            if line.startswith("[") and line.endswith("]"):
                cur = Path(line[1:-1])
                props[cur] = {}
            elif cur is not None and "=" in line:
                k, _, v = line.partition("=")
                props[cur][k.strip()] = v.strip()
    return props


def main() -> int:
    paths = tracked_files()
    props = resolve(paths)
    problems: list[str] = []

    for p in paths:
        pr = props.get(p, {})
        try:
            raw = p.read_bytes()
        except OSError as e:
            problems.append(f"{p.relative_to(ROOT)}: unreadable ({e})")
            continue
        if not raw:
            continue
        rel = p.relative_to(ROOT)

        if pr.get("end_of_line") == "lf" and b"\r\n" in raw:
            problems.append(f"{rel}: CRLF line endings (end_of_line=lf)")

        if pr.get("charset") == "utf-8":
            try:
                raw.decode("utf-8")
            except UnicodeDecodeError:
                problems.append(f"{rel}: not valid UTF-8 (charset=utf-8)")

        if pr.get("insert_final_newline") == "true" and not raw.endswith(b"\n"):
            problems.append(f"{rel}: missing final newline (insert_final_newline=true)")

        lines = raw.split(b"\n")
        body = lines[:-1] if raw.endswith(b"\n") else lines

        if pr.get("trim_trailing_whitespace") == "true":
            hits = [i for i, l in enumerate(body, 1) if l.rstrip(b" \t") != l]
            if hits:
                shown = ", ".join(str(h) for h in hits[:5]) + ("…" if len(hits) > 5 else "")
                problems.append(f"{rel}: trailing whitespace on line(s) {shown} "
                                f"({len(hits)} total; trim_trailing_whitespace=true)")

        # Only the unambiguous direction: a space-indented file must not indent with hard tabs.
        # The reverse (tab-indented files containing leading spaces) has too many legitimate
        # cases — continuations, aligned comments, Markdown — to flag without noise.
        if pr.get("indent_style") == "space":
            hits = [i for i, l in enumerate(body, 1) if l.startswith(b"\t")]
            if hits:
                shown = ", ".join(str(h) for h in hits[:5]) + ("…" if len(hits) > 5 else "")
                problems.append(f"{rel}: tab indentation on line(s) {shown} "
                                f"({len(hits)} total; indent_style=space)")

    if problems:
        print(f"fido: fmt FAILED — {len(problems)} finding(s) over {len(paths)} tracked files\n")
        for pb in problems:
            print(f"  {pb}")
        return 1

    print(f"fido: fmt OK — {len(paths)} tracked files conform to .editorconfig "
          f"(properties resolved by the EditorConfig reference implementation) ✓")
    return 0


if __name__ == "__main__":
    sys.exit(main())
