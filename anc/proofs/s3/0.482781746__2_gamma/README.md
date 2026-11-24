# S3: 2_gamma

Status: exact. The directory prefix is the lower value truncated to nine decimal places.

gamma=(1+sqrt(13))/2.

Run from the repository root (commands with `cd` run inside the bundle):

```bash
python3 anc/proofs/s3/0.482781746__2_gamma/verify_endpoint.py
```

Certificate inputs are the cover and certificate JSON files. Verification JSON files are saved outputs, recomputed by the verifier. Search checkpoints are not proof inputs.
