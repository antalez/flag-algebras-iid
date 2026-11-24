# S2: alpha1_alpha2

Status: exact. The directory prefix is the lower value truncated to nine decimal places.

The accepted certificate uses `near_alpha2_refined_cover.json` (six cuts,
1,774 patterns). `near_alpha2_exact_cover.json` is the older four-cut cover
and is retained for the search programs.

Run from the repository root (commands with `cd` run inside the bundle):

```bash
python3 anc/proofs/s2/0.507073883__alpha1_alpha2/verify_alpha2_plateau.py
```

Certificate inputs are the cover and certificate JSON files. Verification JSON files are saved outputs, recomputed by the verifier. Search checkpoints are not proof inputs.
