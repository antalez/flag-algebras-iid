"""Run the relocated Python proof checks, without invoking a solver."""
import argparse
import json
from pathlib import Path
import shlex
import subprocess
import sys

ANC = Path(__file__).resolve().parent
ROOT = ANC.parent


def commands():
    index = json.loads((ANC / "results.json").read_text())
    for row in index["results"]:
        group = "cbf" if row["status"] == "exact_endpoint" else row["family"]
        # S3's shared runner checks its rational bounds, witnesses, and all
        # three exact plateaus, including comparisons with the saved reports.
        if group == "s3":
            continue
        directory = ROOT / row["directory"]
        for args in row["commands"]:
            yield group, directory, [sys.executable, *args]
    directory = ANC / "proofs/s2/common"
    yield "s2", directory, [
        sys.executable, "verify_family_discontinuities.py",
        "branch1", "branch2", "branch3",
    ]
    yield "s2", directory, [
        sys.executable, "verify_ladder_discontinuities.py", "4", "5", "6",
    ]
    directory = ANC / "proofs/s3/common"
    yield "s3", directory, [sys.executable, "verify_all.py"]
    directory = ANC / "proofs/s3/silver_ratio_lower"
    yield "s3", directory, [sys.executable, "verify_lower.py"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", choices=("s2", "s3", "cbf"))
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    for group, directory, command in commands():
        if args.only and args.only != group:
            continue
        display = f"cd {directory.relative_to(ROOT)} && {shlex.join(command)}"
        print(display, flush=True)
        if not args.list:
            subprocess.run(command, cwd=directory, check=True)


if __name__ == "__main__":
    main()
