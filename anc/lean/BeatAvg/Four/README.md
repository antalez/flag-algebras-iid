# Direct four-point equality

`Final.lean` proves `BeatAvg.Four.C_eq_Bstar : BeatAvg.C = BeatAvg.Bstar`.
The constants and the Bellec–Fritz lower construction are the same as in the
existing proof. The upper bound uses the certificate from commit `49cd49e`.

For four sorted nonnegative points, the pattern records 18 pair comparisons
at the three rational cutoffs `7/6`, `3/2`, and `2`, and the two possible
additive wins. There are 259 retained patterns and 871 excluded prefixes.
The certificate has four families with two roots and one extension per
side; reduced PSD dimensions are 9, 13, 14, and 8.

The finite checker evaluates the actual symmetrized square terms. It does
not use a Python-exported table of precomputed scores. Each family is
averaged over the 12 arrangements with increasing roots. `Arrangements.lean`
identifies this with the average over all 24 permutations of the real
sample. `Evaluation.lean` proves the complete score identity, including the
objective `(number of winning targets)/4`.

`Functional.lean` then proves

```
P μ ≤ ∫ sample, Lam sample ∂(iid 4 μ).
```

Flag squares have nonnegative expectation under every iid probability law.
The cover and score inequalities bound the integral by `Bstar` for
atomless nonnegative laws. The existing atomless approximation lemma
extends the result to the supremum over all nonnegative laws. Finally,
`BeatAvg.Bstar_le_C` gives equality.

No upper-bound step uses a near-optimal degree estimate, a sublaw
restriction, a strict second-endpoint inequality, or a fixed-point
argument. Atomless approximation still uses laws approaching the
supremum, as in the existing ordinary flag bound.

## Reused proof components

- `Fast.K`, `BeatAvg.Cert.KReal`, and the enclosure lemmas supply exact
  arithmetic and real interpretation in `Q(r)`.
- `BeatAvg.Five.Matrix` supplies the Gram, diagonal dominance, and sparse
  congruence proofs. The four-point wrapper changes only the matrix
  checker's sample-size metadata; all entries and witnesses are preserved.
- The existing colored flag, conditional independence, cover, and
  permutation proofs are adapted to three colors and four points.
- `cfgOf_eq_patG`, tuple sorting, iid integration, bounded measurability,
  and `exists_atomless_law_gt` are reused.
- `BeatAvg.Lower.Main` supplies the unchanged lower bound.

## Reproduction and audit

From the repository root, after the toolchain, Mathlib cache, and original
LFS definitions have been restored:

```bash
python3 anc/lean/tools/check_four.py --jobs 2
python3 anc/lean/tools/check_four_proof.py
```

The finite checks use `decide +kernel`. The runners compile shared local
dependencies directly and release each finite check's compiler process
separately. `--jobs 1` lowers concurrent memory use; `--resume` skips
successful finite modules whose source and imported source hashes match.

The complete equality theorem compiled successfully. `CheckFour.lean`
reported:

```
BeatAvg.Four.C_eq_Bstar : BeatAvg.C = BeatAvg.Bstar
'BeatAvg.Four.C_eq_Bstar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The runner also audits the upper bound, cover, pattern inequalities,
score identity, and expectation bound. Detailed timings, per-module logs,
and the full axiom audit are written to ignored `.lake/four-*` files.

`anc/lean/tools/export_four.py` regenerates the data and check modules. It
reads `anc/proofs/s3/0.400695372__c2/cover_n4.json` and `cert_exact.json`, rescales the
rational Gordan weights for the integer comparison forms, and proposes
rational Gram witnesses. Every relevant claim about these exported
objects is checked in Lean. NumPy and the original Python verifier are
not part of the trusted proof.
