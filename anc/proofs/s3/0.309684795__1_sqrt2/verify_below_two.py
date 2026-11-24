"""Standard-library verification of the candidate S3 plateau ending at sqrt(2)."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
from anc.proofs.paths import source_path
import argparse
import importlib.util
import json
from pathlib import Path

from below_two_endpoint import C, PATH, verify_cover
from below_two_field import Value, B, Z, POLYNOMIAL, ROOT_INTERVAL, positive_definite

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "s3_below_two_verifier", source_path("graph_experiment/three_against_one/verify_endpoint.py"))
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
verifier.C, verifier.verify_cover = C, verify_cover
verifier.Value, verifier.B, verifier.Z = Value, B, Z
verifier.positive_definite = positive_definite
verifier.VALUE_POLYNOMIAL = POLYNOMIAL
verifier.VALUE_ROOT_INTERVAL = ROOT_INTERVAL
verifier.ENDPOINT_POLYNOMIAL = [-2, 0, 1]
verifier.INTERVAL = "1<c<=sqrt(2)"


def check_lower_value():
    assert 0 < Z < 1 and 5 * Z ** 3 + 4 * Z ** 2 + 3 * Z - 6 == 0
    assert B == (1 - Z) * (Z ** 3 + 3 * Z ** 2 * (1 - Z)) / (1 - Z ** 4)


verifier.check_lower_value = check_lower_value
verify = verifier.verify

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", default="below_two_sqrt2_field_certificate.json")
    args = parser.parse_args()
    cover = json.loads(PATH.read_text())
    certificate = json.loads((HERE / args.certificate).read_text())
    result = verify(cover, certificate)
    stem = Path(args.certificate).name
    for suffix in ("_field_candidate.json", "_field_certificate.json"):
        if stem.endswith(suffix):
            stem = stem[:-len(suffix)]
            break
    else:
        raise ValueError("Unexpected certificate filename")
    (HERE / (stem + "_verification.json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
