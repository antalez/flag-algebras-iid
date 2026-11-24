# S2: alpha3_alpha4

Status: band. The directory prefix is the lower value truncated to nine decimal places.

check_beta3prime_lower.py supplies the lower value despite its historical name. This is a certified band, not an exact plateau. The alpha4 discontinuity check also uses the right-hand lower construction in the next directory.

Run from the repository root (commands with `cd` run inside the bundle):

```bash
python3 anc/proofs/s2/0.509054132__alpha3_alpha4/verify_alpha4_band.py
```

Certificate inputs are the cover and certificate JSON files. Verification JSON files are saved outputs, recomputed by the verifier. Search checkpoints are not proof inputs.
