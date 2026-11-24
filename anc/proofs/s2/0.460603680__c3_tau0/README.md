# S2: c3_tau0

Status: band. The directory prefix is the lower value truncated to nine decimal places.

verify_fourth_plateau.py supplies the exact lower arithmetic; its candidate exact upper certificate has not been found. The ordinary cube-root certificate also checks the jump after tau0, with a weaker upper bound.

Run from the repository root (commands with `cd` run inside the bundle):

```bash
cd anc/proofs/s2/0.460603680__c3_tau0
python3 ../common/verify_near_small.py near_tau0_refined_cover.json near_tau0_full_near_certificate.json
```

Certificate inputs are the cover and certificate JSON files. Verification JSON files are saved outputs, recomputed by the verifier. Search checkpoints are not proof inputs.
