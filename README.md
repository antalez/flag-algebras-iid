# Flag algebras and the exact largest probability of a linear inequality between iid random variables

Certificates, exact verifiers, lower-bound constructions and Lean proofs for

> Anton Zaytsev and Pierre C. Bellec, *Flag algebras and the exact largest probability of a linear inequality between iid random variables*, [arXiv:2611.29223](https://arxiv.org/abs/2611.29223) (2026).

The main result: for X1, ..., X4 independent with a common law on [0, ∞),

    sup P[X1 + X2 + X3 < 2 X4] = 0.4006953723...,

the value conjectured by Bellec and Fritz. The proof is a four-point flag-algebra certificate over an algebraic number field, formalized in Lean 4 (`BeatAvg.Four.C_eq_Bstar`). The paper also determines S2(c) = sup P[X1 + X2 < c X3] and S3(c) = sup P[X1 + X2 + X3 < c X4] exactly on several intervals of c, and certifies discontinuities of both (tables below).

## Contents

The files under `anc/` are the arXiv ancillary files (which omit the `anc/` prefix), plus one file the arXiv package leaves out for size: the seven-point silver-ratio certificate `anc/proofs/s3/silver_ratio_seven_point/cert7_full_k.json.gz` (about 44 MB). Nothing else is needed for the four-point Lean proof or the Python checks.

[`anc/README.md`](anc/README.md) explains the layout, every result directory has its own README with its claim and verification command, and [`anc/results.json`](anc/results.json) maps directories to the paper's notation. These READMEs were written in the authors' private working repository. Where they mention search programs, the Lean artifact archive, Git LFS, uncompressed JSON files, the `repository_c3_c4` submodule, compatibility links or `make arxiv-check`, they refer to that repository, which is not public; all proof inputs are here.

## Verifying

JSON inputs larger than 1 MB are stored compressed, as in the arXiv package. From the repository root, restore them once (Python 3.11 or later), then run the checks (exact arithmetic, no SDP solver):

```bash
python3 anc/prepare_data.py
python3 anc/verify.py --list
python3 anc/verify.py --only cbf
python3 anc/verify.py --only s2      # several minutes
python3 anc/verify.py --only s3
```

Please do not commit the restored JSON files.

The independently written verifier of the four-point certificate for C = C_BF needs NumPy and SciPy:

```bash
cd anc/proofs/s3/0.400695372__c2/independent && python3 verify_indep.py
```

The seven-point bound at the silver ratio needs NumPy, takes a few minutes and about 2.5 GB of memory; see [its README](anc/proofs/s3/silver_ratio_seven_point/README.md) for the command.

The Lean proof of the main theorem (requires the pinned Lean toolchain; see the build instructions in [`anc/lean/README.md`](anc/lean/README.md)):

```bash
python3 anc/lean/tools/check_four.py --jobs 2
python3 anc/lean/tools/check_four_proof.py
```

## Known bounds: contributions welcome

Most of S2 and S3 is still open. If you find a better lower bound (an explicit law), a better upper bound (a certificate), or an exact value on a new interval, please open a pull request. Add a directory under `anc/proofs/s2/` or `anc/proofs/s3/` with the certificate or construction, a README stating the claim, and a command that checks it in exact arithmetic. The existing directories show the formats: for example `anc/proofs/s3/rational/` for four-point upper certificates and `anc/proofs/s3/lower_constructions/` for rational lower witnesses, both checked by `anc/proofs/s3/common/verify_all.py`. Certificates in these formats are quick to check. Verified improvements are added to the tables with credit. Questions are welcome by email: anton.a.zaytsev@gmail.com.

S2 and S3 are nondecreasing and left-continuous in c, so an upper bound at b holds for all c ≤ b, and a lower construction valid for all c > a holds to the right of a.

### Two against one: S2(c) = sup P[X1 + X2 < c X3]

Thresholds (positive roots): c1 = √2; c2: c³ = c + 2; c3: c⁴ = c² + c + 2; τ0 = 4^(1/3); c4: c⁵ = c³ + c² + c + 2; τ1: c⁴ = c² + 4; c5: c⁶ = c⁴ + c³ + c² + c + 2; τ2: c⁵ = c³ + c² + 4; c6: c⁷ = c⁵ + c⁴ + c³ + c² + c + 2; τ3: c⁶ = c⁴ + c³ + c² + 4; φ = (1 + √5)/2; α1: c³ = c² + 2; α2: c⁴ = c³ + c + 2; α3: c⁵ = c⁴ + c² + c + 2; α4: c⁶ = c⁵ + c³ + c² + c + 2; β3′: c(c − 1)² = 1; β3: c³ = c² + c + 1.

Lower bounds are rounded down and upper bounds up; gaps are rounded to two significant digits (Table 2 of the paper).

| interval for c | S2(c) | gap |
|---|---|---|
| (0, 1] | exactly 1/3 | 0 |
| (1, c1] | exactly (2√7 − 4)/3 = 0.43050087... | 0 |
| (c1, c2] | exactly 0.44998962221368... | 0 |
| (c2, c3] | exactly 0.45736151856620... | 0 |
| (c3, τ0] | 0.4606036 to 0.4606037 | 4.6e-9 |
| (τ0, c4] | 0.4613898 to 0.4614455 | 5.6e-5 |
| (c4, τ1] | 0.4627479 to 0.4627493 | 1.2e-6 |
| (τ1, c5] | 0.4632210 to 0.4639491 | 7.3e-4 |
| (c5, τ2] | 0.4639503 to 0.4640382 | 8.8e-5 |
| (τ2, c6] | 0.4642668 to 0.4647187 | 4.5e-4 |
| (c6, τ3] | 0.4647195 to 0.4647946 | 7.5e-5 |
| (τ3, φ] | 0.4649467 to 0.4702903 | 5.3e-3 |
| (φ, α1] | exactly 0.50309840863532... | 0 |
| (α1, α2] | exactly 0.50707388333268... | 0 |
| (α2, α3] | exactly 0.50846036134736... | 0 |
| (α3, α4] | 0.5090541 to 0.5090544 | 2.3e-7 |
| (α4, β3′] | 0.5093764 to 0.5148734 | 5.5e-3 |
| (β3′, β3] | 0.5162682 to 0.5437506 | 2.7e-2 |
| (β3, 2) | at least 0.5441582 | open |

Every listed threshold is a proved discontinuity (Theorem 1.3 and Table 2 of the paper).

### Three against one: S3(c) = sup P[X1 + X2 + X3 < c X4]

Here γ = (1 + √13)/2.

| c | S3(c) |
|---|---|
| (0, 1] | exactly 1/4 |
| (1, √2] | exactly 0.3096847954174... |
| (√2, 2) | open; more than 0.321369982677 for every c > √2; less than 0.3221953 at 3/2, 0.3371723 at 8/5, 0.3532920 at 7/4, 0.3738948 at 37/20, 0.381302383 at 19/10 |
| 2 | exactly C_BF = 0.4006953723... |
| (2, γ] | exactly 0.4827817466286... |
| (γ, 47/20] | exactly 0.4911560818137... (47/20 is the proved extent of this plateau) |
| (47/20, 1 + √2) | open; at least 0.4911560818137...; less than 0.491302616 at 59/25 and 0.493552660 at 12/5; ladder constructions give more than 0.492838853 from 2.374423764, more than 0.493537310 from 2.398726488, and more than 0.494663204 from 2.414182765 |
| 1 + √2 | between 0.4952063 and 0.4952221 |
| (1 + √2, 3) | more than 0.503419372; less than 0.507948681 at 121/50 |

S3 jumps immediately after √2 (by more than 0.011685187), after 2, and after γ (by more than 0.008374335). No coefficient c gives S2(c) = 1/2 or S3(c) = 1/2 (for S3 this is Problem 5.3 of Bellec and Fritz); the thresholds sup{c : S2(c) ≤ 1/2} and sup{c : S3(c) ≤ 1/2} are the golden ratio and 1 + √2.

## License

MIT, see [LICENSE](LICENSE).
