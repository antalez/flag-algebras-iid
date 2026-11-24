# Reproducing the certificates and the Lean proofs

This archive contains what is needed to recompute the certificates that the Lean proofs use, to
turn them into the inputs of the Lean project, and to compile the Lean project. The Lean
toolchain and Mathlib are not included; they are fetched from the versions pinned in
`formal/proof/lean-toolchain` and `formal/proof/lake-manifest.json`.

The directory layout is the one of the original working directory, so that the relative paths
used by the scripts keep working. Run every command from the directory named in the note.

| What | Note | Directory |
|---|---|---|
| Seven-point flag certificate (`C ≤ 0.4007544385`) | `ORDER7.md` | `work/`, `results/order7/` |
| Exact eight-point certificate (`C ≤ B*`) | `ORDER8_EXACT.md` | `work/`, `results/order8_exact/` |
| Six-point flag certificate (`C ≤ 0.40255`) | `SIX_POINT.md` | `starting_point/` |
| From the certificates to the inputs of Lean | `LEAN_DATA.md` | `indep_check/`, `formal/proof/data/` |
| The Lean project | `formal/proof/README.md` | `formal/proof/` |
| The Lean proof with no `native_decide` (separate archive, `make_kernel_bundle.py`) | `KERNEL.md` | `formal/proof/` |
| Written proofs and history | | `results/theorem_D_proof.md`, `results/C_equals_Bstar.md`, `formal/proof/THEOREM_D_EXPLAINED.md`, `summary.md` |

## What is reproducible, and how far it was re-run

Re-run in a scratch copy, with the C libraries rebuilt from the sources here:

| Step | Result |
|---|---|
| Patterns of 5, 6, 7 points (`patterns.py 7`) | files identical to the originals |
| First round of the seven-point solver | same row set; value `0.4007374118` against `0.4007374099` in the original log |
| Rounding and export of the seven-point certificate from the saved solver state `sol7.pkl` | `cert7_full.json` identical (with the recorded thread setting, see `ORDER7.md`) |
| Verification of the seven-point certificate (`verify7_full.py`) | accepted, bound matches |
| Exclusion certificates for seven points (`farkas.py`) | `farkas7_excluded.json` identical |
| Forced patterns, exact solve and export of the eight-point certificate from the saved states | `forced_all.npz` and `cert8_exact.json` identical |
| Independent verifier from scratch, then export of the three Lean data files | identical |
| Six-point verification (`verify_cert.py`); start of the eight-point verifier (`verify8k.py`, first 16,666 patterns) | accepted |
| Generators of the Lean files (`gen_cert8_data.py`, `gen_static8.py`, `gen_six.py`) | identical |
| Lean project built from scratch from the extracted archive, in the three stages of `LEAN_DATA.md` | all 3,570 jobs succeed in 96 minutes on 192 threads; `Check.lean` reports the expected axioms. Mathlib was taken from an existing download, not fetched again |

Not re-run: the remaining rounds of the seven-point solver, and the search that led to the saved
states of the eight-point certificate. That search was interactive (many runs with hand-picked
restarts) and is not a script; see `ORDER8_EXACT.md`.

## Not included

Arrays that the scripts regenerate, some of them large: the pattern lists (`pat8.npy` 1.7 GB,
`cover8_extra.npy` 1.5 GB, `pat8_K.npz` 4.7 GB), `forced_all.npz.coords.npz` (228 MB), and the
intermediate files of the independent verifier. The notes say which command writes each of them.
The scripts of the interactive eight-point search are not included either.

The copies of the working notes in this archive (`summary.md`, `results/*.md`) have had dates and
some details of the machine removed; the scripts `work/qipm2.py` and `work/forced_all.py` differ
from the originals in one line each, which names the device used by PyTorch.

## Requirements

* Certificates: Python 3 with numpy and scipy (used here: Python 3.11, numpy 2.2, scipy 1.13),
  gcc with OpenMP. `forced_all.py` also needs PyTorch.
  The scripts start up to 96 worker processes.
* Lean: elan, then `lake` fetches Lean 4.34.1 and Mathlib v4.34.1. A full build needs about
  270 CPU-hours and, for some modules, 30 to 80 GB of memory.

Wrong or different certificate data cannot make the Lean theorems false: the checks would fail.
