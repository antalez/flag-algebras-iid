# Four-roll equality in Lean 4

This directory proves `C = Bstar`, where `C` is the supremum of
`P[X₁ + X₂ + X₃ < 2X₄]` over iid laws on `[0, ∞)` and `Bstar` is
`C_BF` in the manuscript.

## Reduced arXiv package

The submission zip includes `Fast/Cert8Data.lean` directly, with its content
checked against the pinned upstream artifact. This is the only ignored artifact
needed by the four/five-point colored proof runners. No archive restoration is
needed for those routes in the extracted submission (Mathlib setup is still
required). Use the explicit `check_four*.py` or `check_five*.py` commands below.

The full original archive and all repository files are retained in the
repository. The zip omits that archive and the old eight-point generated
tables and check modules. Reproducing the historical eight-point routes or
the original default `lake build` requires the full repository setup described
under "Source and artifact split" below.

| Route | Final theorem | Entry point | Finite checks |
| --- | --- | --- | --- |
| Direct four-point colored | `BeatAvg.Four.C_eq_Bstar` | `BeatAvg/Four/Final.lean` | Kernel-only (`decide +kernel`) |
| Five-point colored | `BeatAvg.Five.C_eq_Bstar` | `BeatAvg/Five/Final.lean` | Kernel-only (`decide +kernel`) |
| Original eight-point | `BeatAvg.C_eq_Bstar` | `BeatAvg/Cert/Final.lean` | Includes `native_decide` |
| Original eight-point kernel | `BeatAvg.K8.C_eq_Bstar_kernel` | `BeatAvg/K8/Final.lean` | Kernel-only (`decide +kernel`) |

The five-point equality theorem's axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. `CheckFive.lean` prints its statement
and audits the complete proof and its finite checks. The original routes
and their `Check.lean` / `CheckKernel.lean` entry points remain unchanged.
The definitions of `C` and `Bstar` are shared with the original proof.

## Reproduce the direct four-point proof

The certificate from commit `49cd49e`, in `anc/proofs/s3/0.400695372__c2/`, now has a complete
Lean proof. It records pair comparisons at `7/6`, `3/2`, and `2` on four
points. Ordinary flag positivity proves the upper bound directly, without
degree restrictions, sublaw inequalities, or the two-endpoint fixed-point
argument. The original Bellec–Fritz lower-bound theorem supplies equality.

With the pinned toolchain and Mathlib cache, and with `Fast/Cert8Data.lean`
present (already included in the submission, or restored from the original
LFS archive in a repository checkout), run from the repository root:

```bash
python3 anc/lean/tools/check_four.py --jobs 2
python3 anc/lean/tools/check_four_proof.py
```

The first command kernel-checks the cover of 259 retained patterns and 871
excluded prefixes, four PSD blocks, and every exact score inequality.
The second compiles the mathematical bridge and runs `CheckFour.lean`.
The final equality theorem's axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or native
computation axiom.

On this checkout, the finite run passed all 304 compiler invocations with
two check workers: 294.05 seconds of summed compiler time and a peak of
1.45 GiB per process. This sum is not the elapsed time of the parallel run.
The 16 new bridge modules compiled in 124.19 seconds. Including the 32
shared modules that needed rebuilding, the mathematical run took 301.31
seconds of compiler time, with peak RSS 3.46 GiB; the final audit passed.

These runners compile local modules directly, avoiding optional native
libraries left by other Lake builds. The finite stage imports no Mathlib and
requires no LFS data. The mathematical stage reuses the existing field,
matrix, sorting, iid integration, atomless approximation, and lower-bound
lemmas; their import closure still needs the original LFS definitions.
Existing proof routes and the default build target are unchanged.

Sources and generated four-point data are tracked directly in Git.
`anc/lean/tools/export_four.py` regenerates them from the two JSON files in
`anc/proofs/s3/0.400695372__c2/`; it needs NumPy only to propose rational Gram witnesses.
Lean proves the residual diagonal dominance exactly and recomputes the
scores, so the exporter and NumPy are outside the trusted proof.
See `BeatAvg/Four/README.md` for the proof organization.

## Reproduce the five-point proof

Use the pinned Lean 4.34.1 toolchain and Mathlib dependencies. Ensure
`Fast/Cert8Data.lean` is present, as above: the mathematical bridge reuses
existing modules which import the old packed certificate definitions,
although it does not run the eight-point pattern checks.

From the repository root:

```bash
python3 anc/lean/tools/check_five.py
python3 anc/lean/tools/check_five_assembly.py --jobs 2
python3 anc/lean/tools/check_five_proof.py
```

The first command checks the complete sign-space cover (307 retained
patterns, 1,049 excluded prefixes), all six matrix blocks, and the endpoint
bounds with margin `9 / 10000`. The second checks the exact identities
between the sample functional and the certificate scores. The third
compiles the mathematical bridge, reuses the original lower construction,
and audits the final equality theorem. Use these commands for the new
route; the default `lake build` retains the original targets.

The two computational stages use only Lean's kernel and run each small
check module in a separate compiler process. They do not import Mathlib
or the eight-point payload and require no LFS files themselves. The new
Lean sources and certificate data are small enough to track directly.
The scripts save module timings and peak RSS in
`.lake/five-check-report.json` and `.lake/five-assembly-report.json`, and
mathematical compilation times in `.lake/five-proof-report.json`.

The initial finite stage passed all 133 compiler invocations in 626.72
seconds of summed wall time, with peak RSS 1,852 MiB. The assembly stage
passed all 320 invocations in 2,523.95 seconds of summed wall time, with
peak RSS 1,236 MiB per process. Its 307 pattern checks ran with two workers;
`--jobs 1` reduces concurrent memory use. These are sums of individual
compiler-process times, not elapsed times of the parallel run. The 26
mathematical bridge modules, including the final theorem, rebuilt in 183.90
seconds after the existing dependencies were available. The final axiom
audit passed.
The original monolithic finite kernel run was killed with exit 137, which
is why both stages are split into small modules.

To regenerate the matrix data and initial check sources, run
`anc/lean/tools/export_five.py` in a Python environment containing NumPy. It
reads `anc/proofs/s3/0.400695372__c2/five_point/n5_field_certificate.json` and
`n5_cut2_exact_cover.json`. NumPy only proposes rational Gram witnesses;
Lean checks them exactly. The assembly-check script regenerates its own
small check modules using the retained-pattern count in the cover JSON.

## Five-point proof organization

- `Matrix.lean` and `Matrices.lean` interpret the verified PSD witnesses
  using the original Gram, diagonal-dominance, and sparse-congruence lemmas.
- `Cover.lean`, `SamplePattern.lean`, and `PatternConfig.lean` prove that
  real samples in general position have one of the retained colored
  patterns and that their comparisons match the recorded bits.
- `Families.lean` constructs the six actual colored flag families and
  proves their nonnegative expectations.
- `Probability.lean`, `ScalarExpectation.lean`, and `Sample.lean` reuse
  the original degree, sublaw, and atomless-approximation results. The
  near-optimal degree error is bounded by `48 * sqrt ε`.
- `Functional.lean` assembles the expectation bound and two-point criterion.
  `Evaluation.lean` identifies that sample functional with the finite
  certificate score, using the original permutation-counting machinery.
- `FinalCore.lean` and `Final.lean` discharge the endpoint hypotheses with
  the kernel checks, then invoke the unchanged lower bound.

## Source and artifact split

Ordinary Git tracks the proof sources, generators, build configuration, and
pinned dependency manifest. Certificate payloads are ignored, including
`Fast/Cert8Data.lean` and `BeatAvg/Six/Data.lean`: despite their extensions,
these are certificate data, not handwritten proofs. The generated `K8` tables
and over 154,000 kernel-check modules are also ignored. They are present in
the initial local import, but a fresh clone must restore them before building.

The complete upstream archive is tracked by Git LFS at
`anc/lean/artifacts/beat_the_average_kernel.zip`: approximately
101.4 MiB compressed and 243.7 MiB unpacked. Its SHA-256 is:

```
465728d4b8e3368e59f522f99b10a87a4d0577d1f35a70c6e7f1fb7e1650d4d6
```

After cloning, install Git LFS and run from the repository root:

```bash
git lfs install --local
git lfs pull
python3 anc/lean/tools/restore_artifacts.py anc/lean/artifacts/beat_the_average_kernel.zip
python3 anc/lean/tools/restore_artifacts.py anc/lean/artifacts/beat_the_average_kernel.zip --check
```

Restoration verifies the archive hash first and writes only ignored artifacts;
it does not overwrite the versioned proof sources. Ordinary Git stores only
the small LFS pointer; the archive is transferred through LFS. If LFS download
was skipped, run `git lfs pull` before restoring. The expanded artifacts remain
ignored to avoid tracking more than 154,000 generated files individually.

`README.upstream.md` and `repro/` retain the upstream explanation and measured
build results. Their paths `formal/proof` refer to this `anc/lean/` directory;
references to external search/verifier directories refer to the original
reproduction bundle, not files in this repository. In particular, regeneration
from scratch may need those external inputs; restoring the archive avoids that
requirement.

## Building

The project pins Lean and Mathlib to version 4.34.1. From `anc/lean/`, after
restoring the artifacts and installing elan:

```bash
lake exe cache get
```

The committed `lake-manifest.json` pins the dependencies; do not update it
merely to reproduce the build.

### Original eight-point route with native computation

```bash
lake build BeatAvg.Cert.Static8
lake build BeatAvg.Six.Main
lake build
lake env lean Check.lean
```

These commands follow the upstream build stages. This is still a substantial
computation: upstream reports 92 minutes on 192 hardware threads and individual
modules using up to 81 GB of RAM. Choose build parallelism for the available
memory; the upstream measurements are not measurements on this checkout.

### Original eight-point kernel-only route

After restoring all generated artifacts:

```bash
lake build BeatAvg.Cert.Static8
lake build BeatAvg.Six.Cover
lake build BeatAvg.K8.Main8K BeatAvg.K8.Level7Sound BeatAvg.K8.Combine BeatAvg.K8.Check7K BeatAvg.K8.TbSpec BeatAvg.K8.TbF BeatAvg.K8.Check8K BeatAvg.K8.EvalFSound
python3 gen/gen_k8.py
python3 gen/run_k8.py --jobs 1 --mem 96
lake env lean CheckKernel.lean
```

The last runner command is a conservative example, not a recommended runtime:
upstream reports roughly 3,480 CPU-hours for the kernel run. Adjust `--jobs`
and `--mem` (GiB in the runner) to the machine. Do not run
`lake build BeatAvg.K8.Final` directly: the upstream instructions warn that
this schedules the generated modules without the runner's memory budgeting.
See `repro/KERNEL.md` for measured costs and regeneration details.

## Import validation

The import was checked byte-for-byte against the pinned archive, with generated
artifacts excluded from Git. Both entry points and their local Lean import
closures were checked for missing files. A full Lean build was not run as part
of the import; the upstream build and axiom results are documented separately.
