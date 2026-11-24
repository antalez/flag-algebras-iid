# From the certificates to the inputs of the Lean project

The Lean project reads three text files in `formal/proof/data/` and several generated Lean files.
All of them are in the archive already. This note says how each is produced.

## 1. The independent verifier (`indep_check/`)

It re-checks both certificates with its own code, and its by-products are what Lean uses for the
patterns that cannot occur.

    cd indep_check
    gcc -O2 -fopenmp -shared -fPIC -o libkern.so kern.c
    python kfield.py
    OMP_NUM_THREADS=1 python enum567.py          # writes R567.pkl
    python cert.py                               # writes cert_loaded.pkl
    OMP_NUM_THREADS=96 python verify_indep.py    # writes own_exclusions8.pkl

`run_all.sh` runs these and the remaining tests (15 minutes on 96 cores). `REPORT.md` describes
what is checked.

## 2. The three data files

    python export_lean.py   ../formal/proof/data/cert8.txt     # from cert_loaded.pkl
    python export_cert7.py  ../results/order7/cert7_full.json ../formal/proof/data/cert7.txt
    python export_farkas.py ../formal/proof/data/farkas.txt    # from R567.pkl, own_exclusions8.pkl

| File | Content |
|---|---|
| `cert8.txt` | the eight-point certificate, plus an integer factor `G` of `Y`, an enclosure of `r`, a common denominator and a bound on the multipliers |
| `cert7.txt` | the seven-point certificate: one line per flag with its key, block and integer row |
| `farkas.txt` | 210,600 certificates of non-realizability for 5, 6, 7 and 8 points |

Steps 1 and 2, run from this archive, reproduced the three files byte for byte.
On other library versions the certificates of non-realizability and the factor `G` may differ;
any valid ones will do, since Lean checks them.

## 3. The generated Lean files

    cd formal/proof
    python data/gen_cert8_data.py data/cert8.txt Fast/Cert8Data.lean
    python data/gen_static8.py        # BeatAvg/Cert/S8/*.lean, BeatAvg/Cert/Static8.lean
    python data/gen_six.py            # BeatAvg/Six/Data.lean, Six/Chk/*.lean, Six/Checks.lean

`gen_six.py` reads `starting_point/cert_6_json.txt` (three directories up) and `data/farkas.txt`.

## 4. Build

    cd formal/proof
    lake update && lake exe cache get      # fetches Mathlib and its prebuilt files
    lake build BeatAvg.Cert.Static8        # 50 modules evaluated by the kernel, 30 to 40 GB each
    lake build BeatAvg.Six.Main            # 43 modules of 33 GB, one of 81 GB
    lake build                             # everything else, including the 87-minute check
    lake env lean Check.lean               # statements and axioms

`lake build` alone does the same. The first two commands only keep the memory-hungry groups from
running at the same time, since lake starts as many modules in parallel as there are cores.
See `formal/proof/README.md` for times and for what the result depends on.
