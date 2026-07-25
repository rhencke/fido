#!/usr/bin/env python3
"""Canonical archive builder+inspector — directive v12 profile. One root dir; regular files only; no symlinks,
absolute paths, dot components, or duplicate names; ASCII POSIX paths; bytewise-sorted entries; NO directory
entries; timestamp 1980-01-01; ZIP_STORED (compressed==uncompressed); creator system 3; versions 20/20;
flags 0; internal attrs 0; external attrs 0o100644<<16; empty comments and extra fields; ZIP64 forbidden."""
import sys, zipfile, posixpath
from pathlib import Path
TS = (1980, 1, 1, 0, 0, 0); EXT = 0o100644 << 16
def build(root: Path, out: Path):
    root = root.resolve(); base = root.name
    files = sorted(p for p in root.rglob("*") if p.is_file() and not p.is_symlink())
    with zipfile.ZipFile(out, "w", zipfile.ZIP_STORED, allowZip64=False) as z:
        for p in files:
            arc = posixpath.join(base, p.relative_to(root).as_posix())
            arc.encode("ascii")
            zi = zipfile.ZipInfo(arc, date_time=TS); zi.external_attr = EXT; zi.create_system = 3
            z.writestr(zi, p.read_bytes())
def inspect(path: Path) -> list[str]:
    errs, names = [], set()
    with zipfile.ZipFile(path) as z:
        infos = z.infolist()
        roots = {i.filename.split("/", 1)[0] for i in infos}
        if len(roots) != 1: errs.append(f"roots: {sorted(roots)}")
        prev = ""
        for i in infos:
            n = i.filename
            if n.endswith("/"): errs.append(f"directory entry: {n}")
            if n.startswith("/") or ".." in n.split("/") or "." in [s for s in n.split("/") if s == "."]: errs.append(f"path: {n}")
            if n in names: errs.append(f"duplicate: {n}")
            names.add(n)
            if n < prev: errs.append(f"unsorted at: {n}")
            prev = n
            if i.compress_type != zipfile.ZIP_STORED or i.compress_size != i.file_size: errs.append(f"not STORED: {n}")
            if i.date_time != TS: errs.append(f"timestamp: {n} {i.date_time}")
            if i.external_attr != EXT: errs.append(f"attrs: {n} {hex(i.external_attr)}")
            if i.comment or i.extra: errs.append(f"comment/extra: {n}")
            if i.create_system != 3 or i.create_version != 20 or i.extract_version != 20 or i.flag_bits != 0:
                errs.append(f"header fields: {n}")
        if z.comment: errs.append("archive comment")
    return errs
if __name__ == "__main__":
    if sys.argv[1] == "build": build(Path(sys.argv[2]), Path(sys.argv[3]))
    else:
        e = inspect(Path(sys.argv[2])); print("\n".join(e) or "ARCHIVE CANONICAL"); sys.exit(1 if e else 0)
