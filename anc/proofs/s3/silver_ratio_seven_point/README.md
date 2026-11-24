# Seven points at the silver ratio

This is the exact upper certificate used in the manuscript and Appendix C.4:

S3(1+sqrt(2)) <= 96556198460261613624314242853 /
194975556187447393296612065280 = 0.4952220696189912...

## Inputs and provenance

`verify7_k.py` was copied from `repository_c3_c4/sqrt2/r7/` at submodule
commit `aa29fb659015952173fefc2d42631c621e3a6a52`. Changes are limited to
reading plain or gzip JSON, defaulting to the compressed input filenames,
and failing if the exact computed fraction differs from the manuscript.

The original checkout of that submodule contains the verifier but omits its
two input files. The inputs were recovered from the existing original local
workspace, `X1plusX2plusX3less2X4/new_question_c/sqrt2/r7/`, using
`import_inputs.py`. The source files are not modified. Gzip compression is
lossless and deterministic; `INPUT_SHA256SUMS` records the hashes of the
original decompressed bytes and `SHA256SUMS` records the distributed files.

- `farkas_k_excluded.json.gz`: exact Q(sqrt(2)) exclusion witnesses for
  five, six, and seven points.
- `cert7_full_k.json.gz`: flag bases, integer Gram factors, normalization,
  and the exact claimed bound.

These mathematical certificate inputs are necessary for reproducing the
seven-point bound. Numerical solver checkpoints, pickles, NPY pattern caches,
and the rest of the old repository are unnecessary and are not copied here.

## Verification

The arXiv package omits `cert7_full_k.json.gz` (44.15 MB) to meet the
submission size limit. The file remains in this repository. To reproduce
the seven-point bound from the arXiv package, first copy that file from the
repository into this directory. The verifier, exclusion witnesses, and both
checksum lists remain included in the package.

Requires Python 3 and NumPy; no SDP solver is used. From the repository root:

```sh
OPENBLAS_NUM_THREADS=1 python3 anc/proofs/s3/silver_ratio_seven_point/verify7_k.py
```

The script rebuilds the covers from the four possible four-point states,
checks every exclusion in exact Q(sqrt(2)) arithmetic, forms integer Gram
matrices, and evaluates every retained pattern exactly. It prints the exact
maximum and checks equality with the fraction above. A full run takes several
minutes. It is separate from the fast checks in `make arxiv-check`, which
verify the retained input checksum and the expected package contents.

With both input files present, check their hashes before a full run:

```sh
cd anc/proofs/s3/silver_ratio_seven_point
sha256sum -c SHA256SUMS
```

`repository_c3_c4/` remains intact in the working repository and is excluded
from the arXiv package.
