#!/usr/bin/env python3
"""Fixed-point registry + manifest generator — directive v12, T-0.C.
Parses Appendix A OF THE FROZEN DIRECTIVE ITSELF (sole source; D-13) under the Canonical Transcription Rules,
emits the registry TSV, resolves every component in the baseline tree (and terminal tree when given), and
emits the manifest TSV with recomputed projection hashes. Never trusts a written hash (D-01/D-15: run AFTER
the audit JSON and freeze record exist so their components resolve; the manifest is a late governance file)."""
import argparse, ast, hashlib, json, re, sys
from pathlib import Path
ALIASES = {
 "PLAN": ".review/FIDO_GO1_23_SPEC_CLOSURE_ARCHITECTURE_PLAN_2026-07-23.md",
 "LTSV": ".review/FIDO_GO1_23_LATITUDE_LEDGER_2026-07-23.tsv",
 "CCSV": ".review/FIDO_GO1_23_SPEC_CLOSURE_LEDGER_2026-07-23.csv",
 "EVD":  ".review/FIDO_GO1_23_PINNED_TOOLCHAIN_EVIDENCE_R1_2026-07-23.md",
 "FRZ":  ".review/FIDO_GO1_23_SPEC_CLOSURE_FREEZE_R1_2026-07-23.md",
 "AJSON":".review/FIDO_GO1_23_SPEC_CLOSURE_AUDIT_R1_2026-07-23.json",
}
TERMINAL = {"FRZ": ".review/FIDO_GO1_23_SPEC_CLOSURE_FREEZE_TERMINAL_2026-07-23.md",
            "AJSON": ".review/FIDO_GO1_23_SPEC_CLOSURE_AUDIT_TERMINAL_2026-07-23.json"}
KEYCOL = {"LTSV": "latitude_id", "CCSV": "id"}
H = lambda b: hashlib.sha256(b).hexdigest()
LF = lambda s: s.replace("\r\n", "\n").replace("\r", "\n")
def unesc(s):
    s = s.replace("\\`", "\x00").strip()          # protect escaped (literal) backticks
    if len(s) >= 2 and s[0] == "`" and s[-1] == "`":  # plain enclosing backticks are Markdown formatting
        s = s[1:-1]
    return s.replace("\x00", "`")
def parse_appendix(directive_text: str):
    rows = []
    for m in re.finditer(r"^\| ((?:ARCH|EVID)-\d+)/([\w-]+) \| (.+?) \| ([\w-]+) \| (.*?) \| (.+?) \|$",
                         directive_text, re.M):
        fp, comp, paths, kind, sel, proj = m.groups()
        paths = unesc(paths)
        if "→" in paths: b, t = [p.strip(" `") for p in paths.split("→")]
        else: b = t = paths.strip(" `")
        rows.append(dict(fixed_point_id=fp, component_id=comp,
                         baseline_path=ALIASES.get(b, b), terminal_path=TERMINAL.get(b, ALIASES.get(t, t)),
                         alias=b, selector_kind=kind, selector=sel.strip(), protected_projection=proj.strip()))
    return rows
def md_section(text, prefix):
    prefix = unesc(prefix)
    lines = LF(text).split("\n"); level = prefix.split(" ")[0].count("#")
    hits = [i for i, l in enumerate(lines) if l.startswith(prefix)]
    if len(hits) != 1: raise ValueError(f"markdown-section '{prefix}': {len(hits)} matches")
    out = [lines[hits[0]]]
    for l in lines[hits[0]+1:]:
        if re.match(r"^#{1,%d} " % level, l): break
        out.append(l)
    return "\n".join(out).rstrip() + "\n"
def anchored(text, sel):
    start, end = [unesc(x) for x in sel.split(" … ")]  # per-marker cleaning
    t = LF(text); i = [m.start() for m in re.finditer(re.escape(start), t)]
    j = [m.end() for m in re.finditer(re.escape(end), t)]
    if len(i) != 1 or len(j) != 1: raise ValueError(f"anchored-region markers not unique ({len(i)},{len(j)})")
    if j[0] <= i[0]: raise ValueError("anchored-region end before start")
    return t[i[0]:j[0]] + "\n"
def table_row(text, path, key, fields):
    delim = "\t" if path.endswith(".tsv") else ","
    lines = [l for l in LF(text).split("\n") if l and not l.startswith("#")]
    hdr = lines[0].split(delim); kc = hdr.index(KEYCOL["LTSV" if path.endswith(".tsv") else "CCSV"])
    import csv, io
    rows = list(csv.reader(io.StringIO("\n".join(lines)), delimiter=delim))
    hdr = rows[0]; key = unesc(key)
    hit = [r for r in rows[1:] if len(r) > kc and r[kc] == key]
    if len(hit) != 1: raise ValueError(f"table-row {key}: {len(hit)} matches")
    r = hit[0]
    return "\n".join(f"{f}={r[hdr.index(f)]}" for f in fields) + "\n"
def resolve(root: Path, path: str, kind: str, sel: str, proj: str) -> bytes:
    p = root / path
    if kind == "whole-file": return p.read_bytes()
    if kind == "json-pointer":
        obj = json.loads(p.read_text()); key = unesc(sel).lstrip("/")
        if key not in obj: raise ValueError(f"json key {sel} absent")
        return f"key-present:{key}\n".encode()
    text = p.read_text(encoding="utf-8")
    if kind == "markdown-section": return md_section(text, sel).encode()
    if kind == "anchored-region": return anchored(text, sel).encode()
    if kind == "table-row":
        m = re.match(r"named-fields \{(.+)\}", proj)
        return table_row(text, path, sel, [f.strip() for f in m.group(1).split(",")]).encode()
    if kind == "python-symbol":
        tree = ast.parse(text)
        for node in tree.body:
            names = [getattr(node, "name", None)] + [t.id for t in getattr(node, "targets", []) if isinstance(t, ast.Name)]
            if unesc(sel) in names: return ast.get_source_segment(text, node).encode()
        raise ValueError(f"python-symbol {sel} absent")
    raise ValueError(f"unknown selector kind {kind}")
def main():
    a = argparse.ArgumentParser(); a.add_argument("--directive", type=Path, required=True)
    a.add_argument("--baseline-root", type=Path, required=True); a.add_argument("--terminal-root", type=Path)
    a.add_argument("--out-registry", type=Path); a.add_argument("--out-manifest", type=Path)
    n = a.parse_args(); rows = parse_appendix(n.directive.read_text())
    ok = bad = 0
    man = []
    for r in rows:
        rec = dict(r)
        try:
            b = resolve(n.baseline_root, r["baseline_path"], r["selector_kind"], r["selector"], r["protected_projection"])
            rec["baseline_projection_sha256"] = H(b); ok += 1
        except Exception as e:
            rec["baseline_projection_sha256"] = f"UNRESOLVED: {e}"; bad += 1
        if n.terminal_root:
            try:
                t = resolve(n.terminal_root, r["terminal_path"], r["selector_kind"], r["selector"], r["protected_projection"])
                rec["terminal_projection_sha256"] = H(t)
            except Exception as e:
                rec["terminal_projection_sha256"] = f"UNRESOLVED: {e}"
        man.append(rec)
    cols = ["fixed_point_id","component_id","baseline_path","terminal_path","selector_kind","selector","protected_projection"]
    if n.out_registry:
        n.out_registry.write_text("\t".join(cols) + "\n" + "\n".join("\t".join(r[c] for c in cols) for r in man) + "\n")
    if n.out_manifest:
        mc = cols + ["baseline_projection_sha256"] + (["terminal_projection_sha256"] if n.terminal_root else [])
        n.out_manifest.write_text("\t".join(mc) + "\n" + "\n".join("\t".join(r.get(c,"") for c in mc) for r in man) + "\n")
    print(f"components parsed: {len(rows)}  baseline resolved: {ok}  unresolved: {bad}")
    for r in man:
        if r["baseline_projection_sha256"].startswith("UNRESOLVED"):
            print(f"  {r['fixed_point_id']}/{r['component_id']}: {r['baseline_projection_sha256'][:110]}")
    return 1 if bad else 0
if __name__ == "__main__": sys.exit(main())
