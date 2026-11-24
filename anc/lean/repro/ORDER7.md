# The seven-point flag certificate

Run in `work/`. Output: `results/order7/cert7_full.json` and `farkas7_excluded.json`.

## 1. Build the C kernels

    gcc -O3 -march=native -fopenmp -shared -fPIC -o libkern2.so kern.c
    gcc -O3 -march=native -fopenmp -shared -fPIC -o libflag82.so flag8.c

`ipm.py` loads both by these names.

## 2. Enumerate the patterns

    python patterns.py 7

Writes `pat5.npy`, `pat6.npy`, `pat7.npy` (30, 1,290 and 136,800 realizable patterns) and
`cover5.npy`, `cover6.npy`, `cover7.npy`. A few seconds on 96 processes. Realizability is decided
by linear programming here; the exact proof of it is step 4.

## 3. Solve the semidefinite program

    python cutplane.py --s 7 --out sol7.pkl --init 8000 --add 12000 --trace 2000

The driver solves over a growing set of patterns and stops when no pattern is violated. Rounds
take 5 to 10 minutes on 192 threads. The recorded run was stopped after two rounds and resumed:

    cp sol7.pkl sol7_r1.pkl
    python cutplane.py --s 7 --out sol7.pkl --resume sol7_r1.pkl --add 12000 --trace 2000

Logs of the recorded run: `cut7.log`, `cut7b.log` (last line: value `0.4007544385`, 0 violators).

`sol7.pkl` in this directory is the saved result of that run. Steps 5 and 6 applied to it give
the published certificate byte for byte. A new solve gives a slightly different floating-point
solution, hence a different certificate, valid if step 7 accepts it.

## 4. Certificates for the excluded patterns

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python farkas.py

Reads `cover7.npy` and `pat7.npy`; writes `farkas7_excluded.json` (207,293 exact certificates).
About 15 seconds.

## 5. Round to an exact certificate

    OPENBLAS_NUM_THREADS=16 python certify7.py

Reads `sol7.pkl`; writes `cert7_full_factors.npz` and `cert7_full_meta.json`, and prints the
exact bound `26045773183190596756749048383 / 64991852062482464432204021760`.

The rounding starts from a floating-point factorisation, whose last digits depend on the number
of BLAS threads and on the machine. With 16 threads, as in the recorded run, the result on this
machine is the published certificate. With another setting the bound changed in its 17th digit
(`0.400754438543319`); such a certificate is equally valid if step 7 accepts it, and the Lean
check only needs the bound to be at most `0.4007545`.

## 6. Export

    OPENBLAS_NUM_THREADS=8 python export7.py

Writes `cert7_full.json`. Copy it and `farkas7_excluded.json` to `results/order7/`.

## 7. Verify

    cd ../results/order7
    python verify7_full.py --starting-point ../../starting_point

Integer arithmetic only, no code shared with the solver, about 80 seconds. Expected output:
`verification_output.txt`.
