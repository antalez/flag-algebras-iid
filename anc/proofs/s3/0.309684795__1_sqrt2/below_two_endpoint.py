"""Exact four-point cover at sqrt(2), reusing the algebraic cover builder."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from anc.proofs.paths import source_path
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("s3_below_two_cover", source_path("graph_experiment/three_against_one/endpoint_cover.py"))
cover_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cover_module)
cover_module.POLYNOMIAL = [-2, 0, 1]
cover_module.ROOT_INTERVAL = (1, 2)
cover_module.Endpoint = cover_module.make_field(
    cover_module.POLYNOMIAL, root_interval=cover_module.ROOT_INTERVAL)
cover_module.C = cover_module.Endpoint([0, 1])
cover_module.CUTS = [cover_module.C]

C, Endpoint = cover_module.C, cover_module.Endpoint
verify_cover = cover_module.verify_cover
PATH = HERE / "below_two_sqrt2_cover.json"


if __name__ == "__main__":
    if PATH.exists():
        cover = json.loads(PATH.read_text())
        verify_cover(cover)
    else:
        cover = cover_module.generate(cuts=[C])
        PATH.write_text(json.dumps(cover, separators=(",", ":")) + "\n")
    print(json.dumps(dict(patterns=len(cover["patterns"]),
                          exclusions=len(cover["pruned"]), exact_cover_verified=True)))
