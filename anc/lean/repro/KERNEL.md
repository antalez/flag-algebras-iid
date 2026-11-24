# `C = B*` in Lean with no `native_decide`

    theorem BeatAvg.K8.C_eq_Bstar_kernel : C = Bstar      -- formal/proof/BeatAvg/K8/Final.lean
    'BeatAvg.K8.C_eq_Bstar_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]

This archive contains the Lean project of `formal/proof` and everything generated for this
theorem. The main theorem of the project, `BeatAvg.C_eq_Bstar` (`BeatAvg/Cert/Final.lean`), is the
same statement proved with one `native_decide` (`main8`); it builds in about an hour and a half and
is the one to build first. `C_eq_Bstar_kernel` replaces that one computation by kernel evaluation:
the kernel checks every finite fact itself, so the proof depends only on the three standard axioms,
not on the Lean compiler. The price is about twelve times the computing time.

## Cost of the two builds

Measured on one machine with 2 × AMD EPYC 7643 (96 cores, 192 hardware threads) and 2 TB of RAM.

| | `BeatAvg.C_eq_Bstar` (with `native_decide`) | `BeatAvg.K8.C_eq_Bstar_kernel` (kernel only) |
|---|---|---|
| Axioms | the three standard ones and `main8` | the three standard ones |
| What is built | `lake build`: 3,570 jobs | `lake build` of the modules of step 2, then 154,374 generated modules with `gen/run_k8.py` (step 4) |
| Wall time | 92 minutes | 63 minutes for the lake stages of step 2, then 18.8 hours |
| CPU time | 285 CPU-hours | 3.6 CPU-hours for the lake stages, then 3,480 CPU-hours |
| Memory per module | up to 81 GB (`Six/Cover`); 30 to 40 GB for each of the 50 `Cert/S8/*` | up to 26 GB for the order-8 pieces, 57 GB for one table check (`F/S/tb_flag`) |
| Memory of the whole machine | not recorded (lake runs up to 192 modules at a time) | 0.8 to 1.2 TB in use at the times it was looked at, with at most 190 jobs and an estimated-peak budget of 2,000 GB |
| Of which the long computation | `main8`: 87 minutes on 192 threads, about 270 CPU-hours | the order-8 pieces: 3,464 CPU-hours |

CPU time for the kernel run is the sum over the modules of the wall time of each `lean` process;
each is single-threaded and ran at full load, with about 180 of them on the 192 hardware threads.
For `lake build` it is the `user` time reported by `time`.

The kernel route uses parts of the native one that are themselves checked by the kernel
(`Cert/Static8`, the 50 modules `Cert/S8/*`, and `Six/Cover`), but not `Cert/Native8` and not the
order-7 bound.

## What the kernel checks

`BeatAvg/K8/Main8K.lean` proves `C_le_Bstar_of_facts : Facts → C ≤ Bstar` with the standard axioms.
`Facts` collects finite statements, each proved by `decide +kernel` in its own module:

| Facts | Modules | CPU time |
|---|---|---|
| the packed tables agree with the certificate of `Fast/Cert8Data.lean` (`TbOk`, `TfOk`, `RepsOk`) | `F/S/*` (44), `F/Row/r0..r299` (one row of `Dn · Q` each) | 4.4 hours |
| levels 5, 6 and 7 of the enumeration of patterns, with 207,828 certificates of non-realizability | `F/S/lev5`, `F/S/lev6`, `F/L7/p0..p257` | 6 hours |
| for each of the 136,800 patterns of seven points, every pattern of eight points found by the search passes the two inequalities of the certificate or carries a certificate of non-realizability (150 of them) | `P8/D/d0..d152433` | 3,464 hours |
| combination of the pieces | `P8/G/g*` (1,290), `P8/B/b*` (43), `P8/All`, `F/Rows`, `F/L7`, `F/All` | 3 hours |

The proofs behind `C_le_Bstar_of_facts`: `Search`, `SearchSound`, `TrieSound` (a search over
patterns stored as numbers, with a trie per stage, and its completeness), `Eval`, `EvalSound`,
`EvalF`, `EvalFSound` (the functional evaluated with operations on large numbers, and its
equality with `LamR`), `FarkasK`, `LevelK`, `Level7Sound` (levels from the checks), `Combine` (from
the pieces to all patterns). Kernel evaluation is slow per step (about 7 µs) but does arithmetic on
natural numbers with GMP; the data are packed into large numbers so that one step handles many
fields, and each module holds a single kernel declaration because the memory of a declaration is
only partly released.

## How to build it

All commands run in `formal/proof`. The order-8 pieces need about 9 GB of RAM per job on average
and up to 26 GB; choose `--jobs` and `--mem` (in GB) of `gen/run_k8.py` for
the machine. The total work is about 3,500 CPU-hours whatever the parallelism, so the wall time is
about 3,500 hours divided by the number of jobs that run at once (19 hours with 180; about 12 days
with 12).

**1. Lean and Mathlib.** Install elan, then

    lake update && lake exe cache get

**2. The modules that lake builds** (63 minutes on 192 threads, 3.6 CPU-hours; 8, 9 and 46 minutes
for the three commands, the last one mostly for the 33 MB module `BeatAvg/K8/TablesQ.lean`):

    lake build BeatAvg.Cert.Static8                  # 50 modules of 30 to 40 GB each
    lake build BeatAvg.Six.Cover                     # one module of 81 GB
    lake build BeatAvg.K8.Main8K BeatAvg.K8.Level7Sound BeatAvg.K8.Combine BeatAvg.K8.Check7K \
      BeatAvg.K8.TbSpec BeatAvg.K8.TbF BeatAvg.K8.Check8K BeatAvg.K8.EvalFSound

This includes the compiled library `Fast`, but not `Cert/Native8` (`main8`). If the native proof
has been built already (`lake build`, as in `LEAN_DATA.md`), the first two commands do nothing.

**3. The list of modules.**

    python3 gen/gen_k8.py

It writes `BeatAvg/K8/F/**`, `BeatAvg/K8/P8/**` and `BeatAvg/K8/Final.lean` (identical to the files
of the archive; files whose content does not change keep their date) and `scratch/k8_jobs.txt`:
one line per module with its phase, an estimate of its time in seconds, and of its peak memory in
GB. A few minutes.

**4. The kernel run.**

    setsid nohup python3 gen/run_k8.py --jobs 190 --mem 2000 > scratch/k8_run.log 2>&1 &

Phases: 1, the 153,036 independent modules (pieces of the order-8 check and the facts about
tables and levels); 2, the 1,292 modules that combine the pieces of a group; 3 to 5, the 46
modules that combine the rest, ending with `BeatAvg/K8/Final.lean`. Within a phase the most
expensive modules go first. A module starts only when the estimated peak memory of the running
ones stays below `--mem` and the system has that much memory available. The log gives the
progress; `scratch/k8_status.txt` has one line per module (status, seconds, peak GB) and
`scratch/k8_logs/` the output of failed modules. If the run stops, start it again with the same
command: a module whose `.olean` is newer than its source is not built again.

Do not run `lake build BeatAvg.K8.Final`: lake has no limit on the number of parallel jobs and
would start all 150,000 modules at once.

**5. Check.**

    lake env lean CheckKernel.lean

prints the statement and `[propext, Classical.choice, Quot.sound]`.

## Regenerating the generated files

They are in this archive; the scripts below reproduce them. `gen/gen_k8.py` writes nothing new if
run on the archive.

| File | Command (after step 2, or the parts of it named) | Time |
|---|---|---|
| `BeatAvg/K8/Tables.lean`, `TablesQ.lean` | `lake env lean --load-dynlib=.lake/build/lib/libBeatAvg_Fast.so gen/GenTb.lean` | 1 minute |
| `BeatAvg/K8/TablesF.lean` | `lake build BeatAvg.K8.Tb`, then `lake env lean gen/GenTf.lean` | seconds |
| `BeatAvg/K8/L56.lean` | `lake env lean --load-dynlib=.lake/build/lib/libBeatAvg_Fast.so gen/GenL56.lean` | 20 seconds |
| `BeatAvg/K8/L7G.lean`, `L7X.lean` | `lake env lean --load-dynlib=.lake/build/lib/libBeatAvg_Fast.so gen/GenL7.lean` | 25 minutes |
| `data/k8_profile.txt` | `lake build BeatAvg.K8.Check8K`, then `gen/run_prof.sh` (144 processes) | 1.2 hours, 70 process-hours |
| `BeatAvg/K8/F/**`, `P8/**`, `Final.lean` | `python3 gen/gen_k8.py` | minutes |

The generators that need `--load-dynlib` read the certificate through the compiled library `Fast`
(`lake build Fast BeatAvg.K8.Eval BeatAvg.K8.Excl` first). The inputs are the files of `data/`
(`cert8.txt`, `farkas.txt`, see `LEAN_DATA.md`). `data/k8_profile.txt` gives, for each pattern of
seven points and each candidate of the first stage of its search, the number of leaves and a
measure of the work of the search; `gen/gen_k8.py` uses it, with the constants of `gen/k8_fit.txt`
(time and memory per module, measured on this machine), to cut the order-8 check into pieces of
at most 11.5 GB estimated peak memory. Other cuts are equally valid: any set of pieces whose
combination modules compile proves the theorem.

## What was re-run

The build described here was done once, in the working directory, with the modules generated as
above (the run of step 4: 18.8 hours, no failure). From this archive, extracted into a new
directory with an existing download of Mathlib, the following were re-run:

| Step | Result |
|---|---|
| Step 2 (the three `lake build` commands) | all modules built; the times above come from this run |
| Every generator of the table above | `Tables`, `TablesQ`, `TablesF`, `L56`, `L7G`, `L7X`, `data/k8_profile.txt` identical to the archive (the profile in 73 minutes, 69 CPU-hours; `GenL7` in 33 minutes while sharing the machine) |
| `gen/gen_k8.py` | writes nothing new; `scratch/k8_jobs.txt` identical |
| `gen/run_k8.py` on 814 modules: the 602 modules of facts about tables and levels, the 11 pieces of group 851 and their combination `P8/G/g851`, and 200 pieces chosen at random | all succeed (56 minutes, the longest being `F/S/tf_thrG`) |

Not re-run from the archive: the other 152,000 pieces and the final combination, that is the run
of step 4.

Wrong or different generated data cannot make the theorem false: a check that does not hold makes
its module fail.
