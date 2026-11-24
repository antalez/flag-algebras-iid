# S3: c2

Status: exact_endpoint. The directory prefix is the lower value truncated to nine decimal places.

C=C_BF. The independent verifier is preserved in independent/. Lean entry point: anc/lean/BeatAvg/Four/Final.lean. cert_stage2.json is the superseded rational approximation, not the exact proof input.

Run from the repository root (commands with `cd` run inside the bundle):

```bash
cd anc/proofs/s3/0.400695372__c2
python3 verify.py cover_n4.json cert_exact.json
python3 anc/proofs/s3/0.400695372__c2/redteam.py
```

Certificate inputs are the cover and certificate JSON files. Verification JSON files are saved outputs, recomputed by the verifier. Search checkpoints are not proof inputs.
