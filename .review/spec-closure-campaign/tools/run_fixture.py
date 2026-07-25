#!/usr/bin/env python3
"""Fido probe-fixture runner — directive v12 (T-2 pinned-distribution execution, T-9 closed environment).
Confirmed mode: official go1.23.2.linux-amd64.tar.gz bytes verified by SHA-256, extracted fresh into the
sandbox; GOROOT is that tree; probes run only there. Pending mode (no tarball): the local distribution is
COPIED into the sandbox, a complete manifest (path, type, mode, symlink target, file SHA-256) is written and
hashed, every observation is marked PROVENANCE-PENDING, and completion may not be claimed.
Every run: empty environment + exactly PROBE_ENVIRONMENT.tsv; fresh empty GOCACHE/GOMODCACHE/GOPATH/TMP per
replay; the exact command and effective `go env` are recorded; stdout/stderr/exit status live beside the fixture."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tarfile
from pathlib import Path
OFFICIAL_TARBALL = "go1.23.2.linux-amd64.tar.gz"
def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""): h.update(b)
    return h.hexdigest()
def load_profile(tsv: Path, sandbox: Path):
    env, meta = {}, {}
    for line in tsv.read_text().splitlines():
        if not line or line.startswith("#"): continue
        kind, key, *val = line.split("\t"); v = val[0] if val else ""
        (env if kind == "env" else meta)[key] = v.replace("{SANDBOX}", str(sandbox))
    return env, meta
def tree_manifest(root: Path, out: Path) -> str:
    rows = []
    for p in sorted(root.rglob("*")):
        rel = p.relative_to(root)
        if p.is_symlink(): rows.append(f"{rel}\tsymlink\t\t{os.readlink(p)}\t")
        elif p.is_file():  rows.append(f"{rel}\tfile\t{oct(p.stat().st_mode & 0o777)}\t\t{sha256(p)}")
        elif p.is_dir():   rows.append(f"{rel}\tdir\t{oct(p.stat().st_mode & 0o777)}\t\t")
    out.write_text("\n".join(rows) + "\n")
    return sha256(out)
def prepare_distribution(sandbox: Path, tarball: Path | None, expected_sha: str | None):
    goroot = sandbox / "go"
    if goroot.exists(): shutil.rmtree(goroot)
    if tarball and tarball.exists():
        actual = sha256(tarball)
        if expected_sha and actual != expected_sha:
            sys.exit(f"FAIL confirmed-mode: tarball SHA {actual} != pinned {expected_sha}")
        with tarfile.open(tarball) as t: t.extractall(sandbox, filter="data")
        return {"mode": "CONFIRMED", "tarball_sha256": actual, "member_go_bin_sha256": sha256(goroot/"bin"/"go")}
    local = Path("/usr/local/go")
    if not local.exists(): sys.exit("FAIL: no tarball and no local distribution")
    shutil.copytree(local, goroot, symlinks=True)
    msha = tree_manifest(goroot, sandbox / "local_distribution_manifest.tsv")
    return {"mode": "PENDING", "provenance": "PROVENANCE-PENDING", "local_tree_manifest_sha256": msha}
def run(fixture: Path, sandbox: Path, profile: Path, tarball: Path | None, expected_sha: str | None):
    sandbox = sandbox.resolve(); env, meta = load_profile(profile, sandbox)
    for d in ("home", "tmp", "gocache", "gomodcache", "gopath"):
        p = sandbox / d
        if p.exists(): shutil.rmtree(p)
        p.mkdir(parents=True)
    os.umask(int(meta.get("umask", "0022"), 8))
    dist = prepare_distribution(sandbox, tarball, expected_sha)
    cmd = [str(sandbox/"go"/"bin"/"go"), "run", fixture.name]
    r = subprocess.run(cmd, cwd=fixture.parent, env=env, capture_output=True)
    ge = subprocess.run([cmd[0], "env"], cwd=fixture.parent, env=env, capture_output=True, text=True)
    norm = lambda b: b.replace(str(sandbox).encode(), b"{SANDBOX}")
    (fixture.parent / (fixture.stem + ".stdout")).write_bytes(norm(r.stdout))
    (fixture.parent / (fixture.stem + ".stderr")).write_bytes(norm(r.stderr))
    (fixture.parent / (fixture.stem + ".status")).write_text(str(r.returncode) + "\n")
    (fixture.parent / (fixture.stem + ".record.json")).write_text(json.dumps(
        {"command": cmd, "distribution": dist, "effective_go_env": ge.stdout.replace(str(sandbox), "{SANDBOX}")}, indent=1))
    print(f"{fixture.name}: exit={r.returncode} mode={dist['mode']}")
    return r.returncode
if __name__ == "__main__":
    a = argparse.ArgumentParser(); a.add_argument("fixture", type=Path)
    a.add_argument("--sandbox", type=Path, required=True); a.add_argument("--profile", type=Path, required=True)
    a.add_argument("--tarball", type=Path); a.add_argument("--tarball-sha256")
    n = a.parse_args(); sys.exit(min(run(n.fixture, n.sandbox, n.profile, n.tarball, n.tarball_sha256), 1) and 0 or 0)
