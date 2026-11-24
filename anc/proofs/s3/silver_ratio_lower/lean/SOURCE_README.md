# Endpoint probability proofs in Lean

For four independent draws from a common nonnegative law, write

\[
S(c)=\sup_\mu\Pr(X_1+X_2+X_3<cX_4),\qquad c_*=1+\sqrt2.
\]

The probability lower bounds below and the **universal seven-point probability
upper bound** are formalized. In particular, Lean proves
S(c*) ≤ 0.4952220696189912522741… < 1/2 for all nonnegative probability laws,
not only finite or atomless laws. See
[EndpointBound.lean](LeanProofs/Upper/EndpointBound.lean) for the final upper
theorems. The upper-certificate modules are not used by the lower bounds.

## Reproducing from a checkout

The repository includes all Lean sources (including the adapted reference
framework), pinned dependency revisions, small certificate inputs, export code,
and data hashes. No files from `Anton/` or `beat_the_average_reproduce/`, solver
installation, Gurobi license, or Python virtual environment are needed to build
the proofs. Lake obtains the dependencies recorded in `lake-manifest.json`.

**Three required upper-certificate inputs are deliberately not committed.**
Their distribution is pending discussion; there is no download URL yet.
A checkout alone can reproduce the lower/jump proofs, but cannot reproduce the
upper proof until these exact files are restored under `UpperData/`:

| File | Bytes |
| --- | ---: |
| `factors.txt` | 86,331,703 |
| `exclusions7.txt` | 65,862,360 |
| `patterns7.txt` | 7,596,286 |

These files remain available in the original workspace; `.gitignore` prevents
accidental inclusion. They are mathematical certificate inputs, **not** build
caches. The committed `UpperData/SHA256SUMS` and JSON manifests identify them.
Once restored, check all seven inputs from this directory:

```sh
(cd UpperData && sha256sum -c SHA256SUMS)
```

With Elan available (for example, `source "$HOME/.elan/env"`), run:

```sh
cd lean_proofs  # from the new_question_c repository root
lake exe cache get           # obtain mathlib's cached build artifacts
lake build                  # independent lower/jump proofs
lake env lean LeanProofs/Audit.lean
# The next command requires the three restored certificate inputs.
lake build LeanProofs.Upper.EndpointBound LeanProofs.Upper.Audit LeanProofs.Upper.CheckerTests
```

Keep `lean-toolchain` and `lake-manifest.json` unchanged; do not run `lake update`
to reproduce this version. The first setup requires network access for Lean and
the pinned dependencies. `.lake/` is generated locally, not committed. The
upper native checks can take tens of minutes on a first build; subsequent
unchanged builds reuse Lake's results. No prebuilt local proof artifacts are
required or supplied as a substitute for checking the sources.

## Build and audit

Lean/mathlib are pinned to `v4.36.0-rc1`, with dependency revisions in
`lake-manifest.json`. From this directory:

```sh
lake build
lake env lean LeanProofs/Audit.lean
lake build LeanProofs.Upper.EndpointBound LeanProofs.Upper.Audit LeanProofs.Upper.CheckerTests
```

The second command prints the axioms of the lower-bound and jump theorems. They use only the
usual `propext`, `Classical.choice`, and `Quot.sound`: no `sorryAx`, extra
mathematical axioms, or native-evaluation axiom. In particular these probability
proofs do **not** use `native_decide`. The third command builds and audits the
upper certificate, which uses the explicitly authorized native checks.

`LeanProofs/Basic.lean` is an earlier, isolated setup test using `native_decide`.
It is not imported by the probability proofs or the default library entry point.

## Main probability theorems

See [Theorems.lean](LeanProofs/Theorems.lean).

- `Endpoint.ladder_probability_lower`: for every positive ε there is a
  finite-support nonnegative probability law with probability greater than
  `OptimizedLadder.value - ε` at c*.
- `Endpoint.ladder_probability_numerical`: a finite-support law has probability
  **strictly greater than 0.4952063382580596903** at c*. All displayed digits in
  this statement are certified by exact rational arithmetic.
- `Endpoint.above_endpoint_probability`: for every c>c*, there is a law supported
  on at most five points with probability at least
  \(6601/13122=1/2+20/6561>1/2\).

These statements use actual `PMF ℝ` laws and the measure of the strict event,
not just polynomial inequalities. `draws4` samples the same PMF independently
four times using mathlib's `PMF.bind`. `Probability.lean` proves that this agrees
with the fourfold product of atom weights and the finite event sum used in the
combinatorial proofs. A PMF's `toMeasure` is its probability measure.

The auxiliary `finiteSup` takes the supremum only over finite laws. This is
sufficient for lower bounds on S(c), because the main theorems exhibit such
laws as witnesses; no reduction of arbitrary laws to finite laws is assumed.

## The ladder construction

The formal proof uses the particularly simple strict ladder

\[
a_j=\sqrt2-(\sqrt2-1)4^{-j},\qquad
\nu_N=p\delta_0+q\delta_1+\frac rN\sum_{j=1}^N\delta_{a_j}.
\]

`LadderGeometry.lean` proves \(a_0=1\), \(a_j<\sqrt2\), strict monotonicity, and
\(2+a_j<c_*a_{j+1}\). Thus no equalities are accidentally counted as successes.
For any nonnegative p,q,r summing to one, `Ladder.law_lower` proves

\[
\Pr_{\nu_N^{\otimes4}}(X_1+X_2+X_3<c_*X_4)
\ge F(p,q,r)-\frac{3q^2r^2}{2N},
\]

where

\[
F=p^3(q+r)+3p^2(q+r)^2
 +3p(q^3+3q^2r+2qr^2+r^3)+q^3r+\tfrac32q^2r^2.
\]

Only the successful configurations needed for the lower bound are counted;
proving that every other configuration fails is unnecessary.

`Amplification.lean` proves that replacing zero by a sufficiently small copy of
another finite law preserves every old strict success. If the zero atom has
mass p and the two probabilities are A and B, the new probability is at least
\(A+p^4B\). In particular `finite_repetitions` constructs J repetitions of the
same block with probability at least \(A\sum_{k<J}p^{4k}\).

`LowerBound.lean` establishes the amplification bound \(A/(1-p^4)\) for the
finite-law supremum, then takes the N→∞ limit. Consequently, for **every**
admissible p,q,r with p<1,

\[
S(c_*)\ge \frac{F(p,q,r)}{1-p^4}.
\]

No infinite atomic measure or interchange of a limit with a strict-event
indicator is needed. Every approximate witness is a finite probability law.

## Algebraic candidate masses

`OptimizedLadder.lean` defines θ by a root of

\[
\begin{aligned}
P(T)={}&72T^{14}-132T^{13}-526T^{12}+207T^{11}+5374T^{10}-8269T^9\\
&-11547T^8+53262T^7-87309T^6+88506T^5-60318T^4\\
&+27243T^3-7695T^2+1215T-81
\end{aligned}
\]

in the closed interval [0.81558932228969, 0.81558932228970]. Existence is proved
by the intermediate value theorem with exact rational endpoint sign checks.
Set

\[
z=\frac{\theta(2\theta^2-6\theta+3)}{3(\theta-1)(3\theta-1)},\quad
p=\frac z{1+z},\quad q=\frac\theta{1+z},\quad r=\frac{1-\theta}{1+z}.
\]

The file proves these masses are admissible and proves the lower bound at
the exact algebraic value \(L=F(p,q,r)/(1-p^4)\). Numerically, this is the
previously proposed candidate \(L\approx0.495206338258059690326\).

The Lean proof does **not** assert uniqueness of the polynomial root, optimality
of these masses, irreducibility of P, or sharpness of L over all laws. None is
needed for this lower bound. The separately certified decimal theorem uses
rational masses

\[
(p,q,r)=\frac{(364616428198,518212056720,117171515082)}{10^{12}},
\]

so its digits do not rely on floating-point evaluation of the algebraic root.

## Above the endpoint

Start with masses (1/3,1/2,1/6) at \((0,a,1)\), where \(a=\sqrt2/2\).
For every c>c*, `AboveEndpoint.base_lower` proves probability at least 161/324.
Replacing its zero atom once by a small copy gives the law

\[
\mu=\tfrac19\delta_0+\tfrac16\delta_{\rho a}
 +\tfrac1{18}\delta_\rho+\tfrac12\delta_a+\tfrac16\delta_1.
\]

For a suitable positive ρ depending on c, the proved bound is

\[
\Pr_{\mu^{\otimes4}}(X_1+X_2+X_3<cX_4)
\ge\frac{161}{324}\left(1+\frac1{81}\right)=\frac{6601}{13122}>\frac12.
\]

The code represents this law with 3×3 labels, retaining duplicate labels for
the unchanged positive atoms. `above_endpoint_probability` explicitly proves
that its real-valued support lies in the five displayed locations.

The upper-certificate development now proves the complementary universal
bound below 1/2 at c*. The lower/jump statements here use PMF draws, whereas
the upper statement uses `Measure.pi`; there is not yet a single Lean theorem
packaging these developments as a discontinuity statement for a common S(c).

## Seven-point certificate: completed universal upper bound

The proved upper bound is the exact rational

\[
U=\frac{96556198460261613624314242853}
        {194975556187447393296612065280}
 =0.4952220696189912522741\ldots<\tfrac12.
\]

The decimal `0.4952220696` is a truncation **smaller** than U; it is not the
certified upper bound. `bound_lt_rounded_decimal` proves U<0.495222069619.

Build the upper proof and its audit separately:

```sh
lake build LeanProofs.Upper.EndpointBound LeanProofs.Upper.Audit LeanProofs.Upper.CheckerTests
```

The default `lake build` still builds the independent lower-bound development.
The large native computations are cached by Lake after a successful build.
On the development laptop, the seven-point exclusion batch took about three
minutes and the full score check about eleven minutes. These are observed
times, not performance guarantees.

Completed and checked:

- `Quadratic.lean`: exact arithmetic and sign tests for integers a+b√2,
  with a kernel-checked correspondence to real arithmetic.
- `Farkas.lean`, `ExclusionData.lean`, `Exclusions5/6/7.lean`: soundness of the
  exclusion checker and exact validation of all 972+1184+649718=651874 witnesses.
- `WeakFarkas.lean`, `WeakExclusions.lean`: every witness has a strict-success
  term, so its exclusion remains valid when failed comparisons are allowed
  to be equalities. No generic-position assumption is needed for this result.
- `GapGeometry.lean`: the cached coefficient rows equal the physical affine
  forms in nonnegative gap coordinates.
- `ScoreCheck.lean`, `ScoreData.lean`: integer Gram calculations and exact
  cross-multiplied score inequalities for all 383532 supplied seven-point rows.
  The 59 integer factor matrices use scale 2^44; their Gram denominator is 2^88.
- `ScoreSoundness.lean`, `ScoreAlgebra.lean`: the integer comparisons imply
  real inequalities, and the score decomposes as density plus corrections.
- `CertificateChecks.checked_score_bound`: packages the successful finite
  score check as real inequalities on the supplied list. Its statement does
  **not** claim list completeness or a probability bound.
- `ComputeSoundness.lean`, `Duality.lean`: the executable dot product agrees
  with a finite sum; matrices of these dot products are exactly PSD. General
  Gram PSD and conditional finite-duality statements are also proved.
- `FourPoint.lean`: for sorted nonnegative values the smallest target fails,
  and the other three success events form an initial segment, including ties.
- `UpperJoin.lean`, `JoinSoundness.lean`: an executable hash-join enumeration
  and a general kernel proof that every assignment satisfying its local
  restrictions survives the join. Hash collisions cannot lose assignments.
- `CoverageData.lean`: Lean recomputes all three exhaustive joins, using the
  52 five-point, 2815 six-point, and 383532 seven-point surviving codes, together
  with the verified exclusions. The lower-table parsers are checked explicitly.
- `Packing.lean`, `Deletion.lean`, `CoverageComplete.lean`: base-four
  restriction/scatter identities, exact preservation of affine forms by vertex
  deletion, and induction proving that every nonnegatively realizable
  seven-point code is in the supplied table. Failure equalities are allowed.
- `SampleCode.lean`, `SampleScores.lean`: actual sorted nonnegative seven-point
  samples have realizable codes; `checked_sample_scores` therefore bounds the
  executable score on every such sample, including repeated values and ties.
- `IntegralDuality.lean`: nonnegative Gram expectation on a genuine
  root/extension/extension product space; invariance of i.i.d. integrals under
  coordinate permutations; and the final integration inequality with its
  local-bound and moment assumptions explicit.
- `Reference/`: the probability and flag framework adapted from
  `beat_the_average_reproduce/formal/proof/`, with the event coefficient changed
  to **1+√2**. This includes atomless approximation, sorting, exchangeability,
  nonnegative expected squares, the general `Reference.flag_bound` theorem,
  the block Gram PSD lemma, and the permutation-sum normalization theorem.
  The source project's coefficient-2 pattern encoding is **not** reused.

- `GramSoundness.lean`, `ParserSoundness.lean`: the triangular Gram cache
  contains the exact dot products, and successful parsing guarantees common
  row lengths. `checked_matrices_psd` proves positivity for the actual matrices.
- `FlagFamilies.lean`, `FlagGram.lean`, `CacheInterpretation.lean`: the five
  mathematical flag families are PSD; every valid cache lookup agrees with
  their Gram forms. Missing keys contribute zero, as in the checker.
- `InducedSoundness.lean`, `FamilyComputeSoundness.lean`, `FlagSlots.lean`:
  the executable bit restriction, loops, and flattened lookup indices agree
  with their mathematical interpretations, retaining pair multiplicities.
- `PatternConfiguration.lean`, `SymbolicFlags.lean`: a sample's code
  determines its full configuration; finite symbolic key recipes establish
  the flag-key identities for arbitrary codes, including affine ties.
- `CanonicalSeven.lean`: checked enumeration, root masks, induced columns,
  pair multiplicities, and normalization for all five families, together with
  the objective's 140 canonical arrangements.
- `ObjectiveDensity.lean`, `FamilyRealization.lean`, `ScoreIdentity.lean`:
  the symmetrized objective equals the density with denominator 140, and the
  five averaged flag families equal the executable corrections. Consequently
  their full symmetrized expression is exactly the checked score.
- `PreparedCheck.lean`: the actual parsed certificate passes all layout,
  lookup-index, dimension, and Gram-cache validity checks.
- `EndpointBound.lean`: closes the probability proof, with **no remaining
  certificate, completeness, PSD, or score-identity assumptions**.

The final theorem `Endpoint.Upper.seven_point_upper_bound` states
`Reference.C ≤ bound`. The standalone `Endpoint.Upper.iid_probability_upper`
expands the event and exact rational U in its statement; its only hypotheses
are that μ is a probability measure and μ assigns zero mass to negative reals.
`probability_lt_half` and `probability_lt_rounded_decimal` give the corresponding
strict bounds by 1/2 and 0.495222069619. No optimality or sharpness is claimed.

Earlier lemmas such as `weighted_density_upper`, `integral_upper`, and
`universal_upper_of_flag_realization` remain conditional building blocks;
`EndpointBound.lean` is the unconditional conclusion.

### Data and trust boundary

`export_upper_data.py` only serializes the untrusted JSON/NumPy inputs in
`../sqrt2/r7/` into `UpperData/`. It does not load pickle. The Lean modules embed
the exported text with `include_str`, parse it with fail-closed parsers, and
perform the exact checks themselves. SHA-256 manifests record the source and
exported files; hashes are provenance information, not proofs.

Alternatively, recreate the text inputs from the original certificate source
files, which are also **not included in this commit**. Place
`farkas_k_excluded.json`, `cert7_full_k.json`, `pat5.npy`, `pat6.npy`, and `pat7.npy`
in `sqrt2/r7/`. Use Python 3 with NumPy for the pattern exports
(the exclusion export uses only the standard library). From the repository root:

```sh
python3 lean_proofs/export_upper_data.py
python3 lean_proofs/export_upper_data.py --scores
python3 lean_proofs/export_upper_data.py --lower-patterns
```

Verify the generated files against the committed `UpperData/SHA256SUMS` before
building. The exporter rewrites text inputs and JSON manifests, so matching
newly generated manifests alone is not a check against the committed data.
The original pickle, SDP-solver outputs, and numerical search scripts are not
needed for this reproduction route.

There are thirteen `native_decide` uses in the upper development: three exclusion
batches, the strict-term check, the coefficient-cache check, the full score
check, the three joins in one batch, the full-mask check, the deletion-coefficient
check, the four-subset index check, the arbitrary-target coefficient check,
the canonical-layout check, and the prepared-certificate check.
The pure Std-only `UpperCompute.lean`
and `UpperJoin.lean` libraries are precompiled for speed; they use no external
arithmetic implementation or unchecked casts.
`Upper/Audit.lean` prints the ordinary Lean axioms plus the explicitly authorized
native-evaluation axioms on the data-checking theorems. There are no `sorry`
proofs or manually introduced mathematical axioms. The logical soundness and
probability arguments use ordinary kernel-checked proofs; their concrete finite
metadata and certificate checks use the listed native-evaluation axioms.
