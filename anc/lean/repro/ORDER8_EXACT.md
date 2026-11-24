# The exact eight-point certificate

Output: `results/order8_exact/cert8_exact.json`. Run in `work/`.

Only the last stage is a replayable computation. The search that produced the floating-point
starting point was done interactively, with restarts chosen by hand. Its scripts are not in the
archive; its history is in `summary.md` (sections 5e to 5i). What is saved from it:

| File | Content |
|---|---|
| `fcentre_x7.pkl` | the floating-point solution used to identify the forced equalities |
| `fcentre_int.pkl` | a floating-point solution in the interior of the optimal face |
| `face300.npz` | the subspace on which `Q` may be nonzero |
| `kcert_face.pkl` | the same subspace with exact entries in `Q(r)` |
| `forced_all.npz` | the 138,141 patterns on which equality is forced (from `forced_all.py`) |
| `kfull_viol_cover8_extra.npy` | the 243 patterns that need a certificate of non-realizability (from `kfull_float_check.py`) |

## 1. Build the C kernels

    gcc -O3 -march=native -fopenmp -shared -fPIC -o libflag82.so flag8.c
    gcc -O3 -march=native -fopenmp -shared -fPIC -o libdeg.so deg.c
    gcc -O3 -march=native -fopenmp -shared -fPIC -o libqk4.so qk4.c

## 2. Regenerate the pattern arrays (not included, about 8 GB)

    python patterns.py 7
    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python enumerate8.py full enum8 110     # 13 minutes
    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python prep8.py      # pat8.npy, cover8_extra.npy
    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python prep8k.py     # pat8_K.npz, cover8_extra_K.npz

## 3. Coordinates of the forced patterns (needs PyTorch)

    OPENBLAS_NUM_THREADS=32 python -u forced_all.py fcentre_x7.pkl 1e-4 forced_all.npz

Writes `forced_all.npz` (included) and `forced_all.npz.coords.npz` (228 MB, not included).
PyTorch runs on the device named by the environment variable `QIPM_DEVICE` (default `cpu`).

## 4. Exact solve over `Q(r)`

    OPENBLAS_NUM_THREADS=16 python -u kfull_solve.py fcentre_int.pkl

Rounds the solution to multiples of `2^-44` and corrects 204 unknowns by an exact linear solve
so that the forced equations hold exactly. 80 seconds. Writes `kfull_cert.pkl`. Expected log:
`kfull_solve.log`.

## 5. Patterns that need an exclusion

    OPENBLAS_NUM_THREADS=48 python -u kfull_float_check.py 0.4007545

Floating-point evaluation on all patterns; writes `kfull_viol_cover8_extra.npy` (included).
Expected log: `kfull_float_check2.log`.

## 6. Export

    python kfull_export.py kfull_cert.json

Finds the 243 certificates of non-realizability and writes the certificate. The result is
`results/order8_exact/cert8_exact.json`.

## 7. Verify

See `results/order8_exact/README.md`. The link `farkas7_excluded.json` of the original directory
is not in the archive, so pass the file explicitly:

    cd ../results/order8_exact
    python verify8k.py --certificate cert8_exact.json --exclusions7 ../order7/farkas7_excluded.json --slice 0/12

and likewise for slices 1 to 11 (add `--skip-matrix-check` for those).

## What was re-run

Steps 1, 3, 4 and 6 were re-run, steps 4 and 6 with the existing arrays of steps 2 and 3. Step 3
(20 minutes on the default device) gave a `forced_all.npz` identical to the saved one; step 4 gave
the same log as the original; step 6 gave a certificate identical to the published one. Steps 2
and 5 were not re-run.
