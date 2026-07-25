#!/usr/bin/env python3
"""External sidecar writer — pinned format: <lowercase-sha256><two spaces><zip-filename><LF> (directive v12)."""
import hashlib, sys
from pathlib import Path
z = Path(sys.argv[1]); h = hashlib.sha256(z.read_bytes()).hexdigest()
Path(str(z) + ".sha256").write_text(f"{h}  {z.name}\n"); print(h)
