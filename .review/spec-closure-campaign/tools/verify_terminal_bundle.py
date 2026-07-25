#!/usr/bin/env python3
"""Terminal verifier — directive v12, steps 13/15-16. Writes nothing; exits nonzero on failure.
[LIVE]: canonical archive inspection (delegates to build_deterministic_bundle.inspect) and manifest byte-check.
[BUNDLE] duties quoted for execution-time implementation: freeze_claims_match (freeze counts read from audit
JSON only); inventory-drift rejection; the final_in_bundle equation with the meta-file exclusions;
T-0 owner-by-rule for all six derived governance files (check_derived_governance_ownership); the realized
containment DAG (check_artifact_graph_acyclic); check_fixed_point_manifest_complete + fixed_points_preserved
(recompute every projection from bytes — tools/generate_fixed_point_manifest.py is the reference resolver)."""
import hashlib, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from build_deterministic_bundle import inspect as inspect_zip
def verify_manifest(tree: Path, manifest: Path) -> list[str]:
    errs = []
    for line in manifest.read_text().splitlines():
        sha, name = line.split(None, 1)
        p = tree / name.strip()
        if not p.exists(): errs.append(f"missing {name}")
        elif hashlib.sha256(p.read_bytes()).hexdigest() != sha: errs.append(f"hash {name}")
    return errs
if __name__ == "__main__":
    errs = inspect_zip(Path(sys.argv[1])) if sys.argv[1].endswith(".zip") else verify_manifest(Path(sys.argv[1]), Path(sys.argv[2]))
    print("\n".join(errs) or "VERIFY OK"); sys.exit(1 if errs else 0)
