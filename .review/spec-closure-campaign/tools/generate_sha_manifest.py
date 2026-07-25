#!/usr/bin/env python3
"""SHA-manifest generator — directive v12, step 12 [LIVE]. Hashes every in-bundle file except itself."""
import hashlib, sys
from pathlib import Path
root, out = Path(sys.argv[1]), Path(sys.argv[2])
lines = [f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(root).as_posix()}"
         for p in sorted(root.rglob("*")) if p.is_file() and p.resolve() != out.resolve()]
out.write_text("\n".join(lines) + "\n"); print(f"{len(lines)} entries")
