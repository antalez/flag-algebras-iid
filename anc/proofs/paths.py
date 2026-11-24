"""Resolve historical names to proof inputs; search fallback is repository-only."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
PROOFS = Path(__file__).resolve().parent


def manifest():
    return json.loads((ROOT / "anc/results.json").read_text())


def source_path(previous_path):
    """Return the canonical location of a file, including unmigrated inputs."""
    index = manifest()
    if previous_path in index["moves"]:
        return ROOT / index["moves"][previous_path]
    if previous_path.startswith("graph_experiment/"):
        # Historical research scripts may still use unmigrated search files.
        # Submission proof inputs must have explicit entries in "moves".
        return ROOT / index["search"] / previous_path.removeprefix("graph_experiment/")
    return ROOT / previous_path


def data_path(filename, family="s2"):
    prefix = "graph_experiment/"
    if family == "s3":
        prefix += "three_against_one/"
    return source_path(prefix + filename)


def setup(filename):
    """Expose shared arithmetic and the modules for one probability problem."""
    path = Path(filename).resolve()
    parts = path.relative_to(PROOFS).parts
    if parts[0] == "common" and "tests" not in parts:
        # Arithmetic imports must preserve the caller's S2 or S3 module paths.
        if str(PROOFS / "common") not in sys.path:
            sys.path.insert(0, str(PROOFS / "common"))
        return
    family = "s3" if "s3" in parts else "s2"
    directories = [PROOFS / "common", PROOFS / family / "common"]
    # Cross-bundle imports reuse lower-value fields and the exact SDP verifier.
    # C=C_BF keeps its own, independently implemented verifier separate.
    directories.extend(
        ROOT / row["directory"]
        for row in manifest()["results"]
        if row["family"] == family and row["status"] != "exact_endpoint"
    )
    for directory in reversed(directories):
        if str(directory) not in sys.path:
            sys.path.insert(0, str(directory))
