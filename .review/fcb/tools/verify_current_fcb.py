#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import sys

ROOT = Path(__file__).resolve().parents[3]
CURRENT = ROOT / ".review" / "fcb" / "current"
BOOTSTRAP = CURRENT / "INDEX.md"
MANIFEST = CURRENT / "FIDO_FCB_MANIFEST.sha256"


def fail(message: str) -> None:
    print(f"FCB VERIFY FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


if not BOOTSTRAP.is_file():
    fail(f"missing stable bootstrap: {BOOTSTRAP.relative_to(ROOT)}")
if not MANIFEST.is_file():
    fail(f"missing manifest: {MANIFEST.relative_to(ROOT)}")

expected: dict[str, str] = {}
for lineno, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), 1):
    if not raw.strip():
        continue
    try:
        digest, name = raw.split("  ", 1)
    except ValueError:
        fail(f"manifest line {lineno} is not '<sha256><two spaces><name>'")
    if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
        fail(f"manifest line {lineno} has invalid lowercase SHA-256")
    if name in expected:
        fail(f"duplicate manifest path: {name}")
    if Path(name).name != name or name in {".", ".."}:
        fail(f"manifest path must be one local filename: {name}")
    expected[name] = digest

actual_names = {p.name for p in CURRENT.iterdir() if p.is_file() and p.name != MANIFEST.name}
if set(expected) != actual_names:
    missing = sorted(set(expected) - actual_names)
    extra = sorted(actual_names - set(expected))
    fail(f"file-set mismatch; missing={missing}, extra={extra}")

for name in sorted(expected):
    actual = hashlib.sha256((CURRENT / name).read_bytes()).hexdigest()
    if actual != expected[name]:
        fail(f"hash mismatch for {name}: {actual} != {expected[name]}")

bootstrap = BOOTSTRAP.read_text(encoding="utf-8")
if "FIDO_FCB_INDEX_v3.md" not in bootstrap:
    fail("stable bootstrap does not name FIDO_FCB_INDEX_v3.md")
if "FIDO_FCB_MANIFEST.sha256" not in bootstrap:
    fail("stable bootstrap does not name the manifest")

print(f"FCB VERIFY OK: {len(expected)} files; manifest {hashlib.sha256(MANIFEST.read_bytes()).hexdigest()}")
