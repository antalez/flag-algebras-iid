# S3(1+sqrt2) < 1/2 with four points

A four-point colored certificate at c = 1+sqrt2, in the format of the certificate at (1+sqrt13)/2:
cutoffs c/2, c-1, c/(c-1), c (in Q(sqrt2)), flag families (0,2) and (2,3).

- `silver_n4_cover.json`: 435 retained patterns, 2,278 excluded prefixes with exact Gordan weights over Q(sqrt2).
- `silver_n4_certificate.json`: rational Gram factors Q = W Y W^T (Y = I), six blocks.
- Bound: S3(1+sqrt2) <= 0.49885881... < 1/2. With S3(c) > 0.503419372 for every c > 1+sqrt2, no c gives S3(c) = 1/2.

Verify (standard library, under a minute): `python3 verify_silver.py`.

`nf.py`, `cover.py`, `cert.py` are an exact verifier written independently of the other code in anc/ (number fields with Sturm isolation, Gordan checks, M(P) from the definitions, exact LDL). The cover was also accepted by the (1+sqrt13)/2 endpoint cover checker with the field switched to Q(sqrt2). The sharper seven-point bound S3(1+sqrt2) < 0.4952221 is not needed for Problem 5.3.
