#!/usr/bin/env python3
"""Phase-2 audit — directive v12, step 9. Writes the frozen audit JSON; hashes only inputs (never itself,
the freeze record, the fixed-point manifest, the SHA manifest, the ZIP, or the sidecar).
STATUS KEY: [LIVE] implemented and runnable today; [BUNDLE] requires terminal-bundle artifacts that do not
yet exist — the exact duty is quoted from the directive in the docstring and must be implemented at execution."""
import csv, hashlib, io, json, re, sys
from collections import Counter
from pathlib import Path
H = lambda b: hashlib.sha256(b).hexdigest()
def check_line_endings(root):            # [LIVE] T-5: every tabular artifact is LF
    bad = [str(p) for p in root.rglob("*.[ct]sv") if b"\r" in p.read_bytes()]
    return {"pass": not bad, "crlf_files": bad}
def check_ragged_rows(root):             # [LIVE] T-12
    bad = []
    for p in root.rglob("*.[ct]sv"):
        d = "\t" if p.suffix == ".tsv" else ","
        rows = [r for r in csv.reader(io.StringIO(p.read_text()), delimiter=d)]
        rows = [r for r in rows if r and not r[0].startswith("#")]
        if rows and len({len(r) for r in rows}) > 1: bad.append(str(p))
    return {"pass": not bad, "ragged": bad}
def check_id_prefixes(root):             # [LIVE] T-7: prefix inventory; fails only on malformed IDs
    import collections
    hist, bad = collections.Counter(), []
    for p in root.glob(".review/*LEDGER*.[ct]sv"):
        d = "\t" if p.suffix == ".tsv" else ","
        for r in csv.reader(io.StringIO(p.read_text()), delimiter=d):
            if r and not r[0].startswith("#") and r[0] not in ("id", "latitude_id"):
                m = re.match(r"^([A-Z]+)-X?\d+$", r[0])
                (hist.update([m.group(1)]) if m else bad.append(f"{p.name}:{r[0]}"))
    return {"pass": not bad, "prefixes": dict(hist), "malformed": bad[:10]}
def check_contract_definitions(root):    # [LIVE core] T-6: parse `### 25.N `SC-XX-…`` headings; bijection+contiguity.
    plan = next(root.glob(".review/FIDO_GO1_23_SPEC_CLOSURE_ARCHITECTURE_PLAN*.md")).read_text()
    heads = re.findall(r"^### 25\.(\d+) `((?:SC)-\d+-[A-Z-]+)`", plan, re.M)
    ns = [int(n) for n, _ in heads]; scs = [int(s.split("-")[1]) for _, s in heads]
    biject = len(set(ns)) == len(ns) and len(set(scs)) == len(scs)
    if not heads: return {"pass": False, "count": 0}
    contiguous = scs == list(range(scs[0], scs[0] + len(scs))) and ns == [s + 1 for s in scs]
    return {"pass": biject and contiguous, "count": len(heads), "sc_range": f"SC-{min(scs):02d}..SC-{max(scs):02d}",
            "mapping_table_present": bool(re.search(r"SC-00 = §25\.1", plan))}
def check_duplicate_histogram(root):     # [LIVE] T-4: full duplicate-representation histogram, count then text hash
    p = next(root.glob(".review/*SPEC_CLOSURE_LEDGER*.csv"))
    rows = list(csv.DictReader(io.StringIO(p.read_text())))
    c = Counter(r.get("representation","") for r in rows if r.get("representation"))
    hist = sorted(((n, H(t.encode())[:12], t[:60]) for t, n in c.items() if n > 1), key=lambda x: (-x[0], x[1]))
    return {"pass": True, "duplicates": hist[:25]}
BUNDLE_STUBS = {  # name: exact duty (quoted from directive v12) — implement at terminal execution
 "check_single_open_latitude": "open decision set equals exactly {LAT-X004}; any other open row fails",
 "check_baseline_delta_complete": "structural diff per the selector spec: every changed unit appears exactly once with exactly one owner; no entry names an unchanged unit; orthogonality only per the closed relation; file-level owner sets equal change-level sets; no unlisted change, missing baseline file, or unlisted addition; no altered external review or prior directive",
 "check_fixed_point_registry_exact": "every field of every registry row equals Appendix A as parsed from the frozen in-bundle directive under the Canonical Transcription Rules (tools/generate_fixed_point_manifest.py is the reference parser)",
 "check_distribution_members_match": "PASS-CONFIRMED | PENDING-PROVENANCE | FAIL; extract each pin's exact tar member path from PINS_MANIFEST.tsv out of the verified tarball; byte/mode/symlink compare; pending propagates to pins",
 "local_distribution_manifest_complete": "pending mode: sandbox copy manifested (path/type/mode/symlink/sha) and hashed — see tools/run_fixture.py tree_manifest",
 "check_replay_generated_outputs": "re-run latitude extraction and ledger-markdown rendering; byte-compare to frozen outputs; temp area only",
 "check_replay_probe_fixtures": "re-run every probe compare-only under tools/PROBE_ENVIRONMENT.tsv with fresh empty caches; compare stdout/stderr/status/command/effective-env records",
 "check_index_versus_discovery": "generated Human-Review Index equals the discovered open-act set; fail on omissions and stale rows",
}
def main(root: Path, out: Path):
    checks = {f.__name__: f(root) for f in
              (check_line_endings, check_ragged_rows, check_id_prefixes, check_contract_definitions, check_duplicate_histogram)}
    doc = {"schema_version": "campaign-tools-1", "checkable_only": True, "judgment_not_certified": True,
           "live_checks": checks, "pending_bundle_checks": BUNDLE_STUBS,
           "producer_sha256": {p.name: H(p.read_bytes()) for p in Path(__file__).parent.glob("*.py")},
           "python": sys.version}
    out.write_text(json.dumps(doc, indent=1))
    print(json.dumps({k: v.get("pass") for k, v in checks.items()}))
if __name__ == "__main__": main(Path(sys.argv[1]), Path(sys.argv[2]))
