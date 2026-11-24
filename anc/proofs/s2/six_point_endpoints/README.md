# Six-point endpoint certificates at phi, beta3' and beta3 (two against one)

These are the upper certificates used in Table 2 at phi (S2(phi) <= 0.4702903), beta3' (root of c(c-1)^2=1,
S2 <= 0.5148734) and beta3 (root of c^3=c^2+c+1, S2 <= 0.5437506), with the uniform lower families to their right.
They were previously only in the pinned submodule `repository_c3_c4` (bellecp/FlagAlgebraLinearInequalities,
commit aa29fb659015952173fefc2d42631c621e3a6a52); the files below are copied unchanged from
`two_against_one/` and `anton_endpoint/` of that commit, keeping its layout so the scripts run as they are.

Requirements: Python 3 with numpy, clarabel and gurobipy importable (`pip install numpy clarabel gurobipy`;
gurobipy is imported by a shared module but no solver is run during verification).

Run from this directory (about 15-25 s each):

    OPENBLAS_NUM_THREADS=2 python two_against_one/verify_phi_discontinuity.py \
      --cover6 two_against_one/results/sdp6_phi_clean/c1618023988749_1000000000000/cover.json \
      --endpoint-proof two_against_one/results/phi_endpoint_cover.json \
      --upper-certificate two_against_one/results/sdp6_phi_refinement/certificate.json \
      --lower-witness two_against_one/results/phi_cplus_witness.json

    OPENBLAS_NUM_THREADS=2 python two_against_one/verify_family_discontinuity.py --family limit \
      --cover6 two_against_one/results/upper_intermediate_limit/cover6.json \
      --endpoint-proof two_against_one/results/upper_intermediate_limit/endpoint.json \
      --upper-certificate two_against_one/results/upper_intermediate_limit/refinement/certificate.json \
      --lower-families two_against_one/results/multinacci_families.json

    OPENBLAS_NUM_THREADS=2 python two_against_one/verify_family_discontinuity.py --family multinacci --index 3 \
      --cover6 two_against_one/results/upper_multinacci_3/cover6.json \
      --endpoint-proof two_against_one/results/upper_multinacci_3/endpoint.json \
      --upper-certificate two_against_one/results/upper_multinacci_3/refinement/certificate.json \
      --lower-families two_against_one/results/multinacci_families.json

Each prints `"right_discontinuity_proved": true` with the exact upper bound at the root.
Checked from a clean copy of this folder on 20 Nov 2026: all three pass.
