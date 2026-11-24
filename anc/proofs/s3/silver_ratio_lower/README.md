# Silver-ratio ladder lower bound

This bundle proves a lower bound for S3(1+sqrt(2)), approximately
0.495206338258059690326. It does not prove equality with the supremum
or global optimality of the mass parameters.

## Contents and provenance

The original sources were copied from `repository_c3_c4` at commit
`aa29fb659015952173fefc2d42631c621e3a6a52`:

- `ladder_number_field_certificate.md`: explicit ladder perturbation,
  margin and scale bounds, exact algebraic masses, and field calculations.
  Its upper-certificate discussion describes a research strategy. Only its
  final relative links were adjusted for this bundle.
- `SOURCE_README.md`: historical experiment notes, retained verbatim.
  Some status statements and relative links refer to the original repository.
- `python/{ladder,recursive,certificates}.py`: original search and rational
  certification programs, copied verbatim. These import NumPy and SciPy;
  neither optimizer output nor optimizer success is trusted by the verifier.
- `lean/`: the complete dependency closure of the lower-bound and
  above-endpoint probability theorems, with the original pinned toolchain
  and dependency manifest. The Lake configuration omits unrelated upper
  certificate libraries. `lean/SOURCE_README.md` is the original full-project
  documentation; references there to upper-certificate modules concern the
  original project, not this extracted bundle.
- `witnesses/`: verbatim copies of `../lower_constructions/lower_ladders.json`
  and `lower_thresholds.json`, containing rational finite witnesses below
  the silver ratio. The infinite-ladder optimum in the first JSON is only
  a numerical search record.
- `verify_lower.py` and `verify_field.py`: reproducible checks of the saved
  witnesses, endpoint ladder counts, and algebraic calculations.

The two geometric descriptions are alternatives. The note perturbs the
recurrence a[j+1]=(2+a[j])/c. Lean uses the simpler strict ladder
`a[j]=sqrt(2)-(sqrt(2)-1)/4**j`. Both give the same counted lower bound.
The note gives an explicit scale using the minimum positive margin;
Lean proves existence of a preserving scale by continuity and uses finite
repetitions, so no infinite-measure limit is needed.

## Verification

From the repository root, the standard-library check is:

```sh
python3 anc/proofs/s3/silver_ratio_lower/verify_lower.py
```

This enumerates endpoint ladders of lengths 1, 3, 4, 5 in exact Q(sqrt(2))
arithmetic and checks all copied rational witnesses, including their scale
ratios and threshold brackets. The all-length argument is in the note and Lean.

For exact root isolation, stationarity, and degree-14 irreducibility checks
(requires SymPy):

```sh
python3 anc/proofs/s3/silver_ratio_lower/verify_field.py
```

For the formal probability proofs, run from `lean/`:

```sh
lake build
lake env lean LeanProofs/Audit.lean
```

Lake restores the pinned mathlib dependencies; their compiled cache can be
obtained with `lake exe cache get`. The audit prints the axioms of the actual
probability theorems. The lower proofs use neither `sorry` nor `native_decide`.
`OptimizedLadder.lean` proves existence of the algebraic root and admissible
masses; root uniqueness and degree-14 irreducibility are separately checked
by `verify_field.py`, and are unnecessary for the probability lower bound.
