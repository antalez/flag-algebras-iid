# Ancillary proof files

The directory names follow the notation in Tables 1–2 and Figure 2.
For an interval `(a,b]`, the prefix is its lower bound, truncated toward
zero to nine decimal places. An exact endpoint uses its exact value instead.
The prefix orders the directories; the complete value is in the proof data.

```text
anc/
  proofs/
    common/              exact arithmetic shared by S2 and S3
    s2/
      common/            colored flags and near-optimal-law constraints
      0.430500874__1_c1/
      0.449989622__c1_c2/
      ...
      0.509376431__alpha4_beta3prime/
    s3/
      common/            ordinary colored flags and lower-witness checks
      0.309684795__1_sqrt2/
      0.400695372__c2/    C=C_BF, including the independent verifier
      0.482781746__2_gamma/
      0.491156081__gamma_47over20/
      rational/          upper bounds at rational sample coefficients
      lower_constructions/  rational witnesses for the Figure 2 curve
      silver_ratio_lower/   endpoint ladder notes, checks, and Lean lower proofs
      silver_ratio_seven_point/  seven-point endpoint verifier and compressed inputs
  lean/                  Lean project for C=C_BF and its shared dependencies
  results.json           result index and old-to-new file locations
  verify.py              Python verification commands
```

Here `gamma=(1+sqrt(13))/2`, as used for the first S3 endpoint above 2.
Each result directory has a README specifying its status and verification
command. A **band** has separate lower and upper bounds; its directory name
does not assert an exact plateau. The arithmetic in a candidate exact
verifier can supply the lower value even when its exact upper certificate
has not been found.

The elementary intervals `S2(c)=1/3` and `S3(c)=1/4` for `0<c<=1`
are proved in the manuscript and require no certificate files.

## Python verification

The arXiv package stores JSON files larger than 1 MB as `.json.gz`.
After extracting that package, restore the original JSON files once before
running any verifier:

```bash
python3 anc/prepare_data.py
```

This checks the restored bytes against the SHA-256 hashes in the packaged
`anc/compressed_inputs.json` manifest. It leaves the compressed copies in place
and requires additional disk space for the restored files. The repository keeps
the original JSON files, so this step is unnecessary in a repository checkout.
The seven-point verifier reads its original `.json.gz` inputs directly.

From the repository root:

```bash
python3 anc/verify.py --list
python3 anc/verify.py --only cbf
python3 anc/verify.py --only s2
python3 anc/verify.py --only s3
```

The runner invokes the existing verifiers in separate processes. Proof
checks use exact arithmetic, without an SDP solver. The independently
written C=C_BF verifier is a separate command and needs NumPy for one
cross-check:

```bash
cd anc/proofs/s3/0.400695372__c2/independent
python3 verify_indep.py
```

The large S2 covers at `c5,c6,tau1` use Git LFS. An unexpanded pointer must
be restored before verification. Saved verification JSON files are outputs;
the trusted inputs are the covers, certificates, and lower constructions.
Historical source filenames remain unchanged to preserve imports from the
search programs. `results.json` identifies their interval and current path.

The tau1 band in Table 2 requires `--ratios 31 --full-near-optimality`.
The certificate without the latter option gives a weaker bound.

## Lean equality proof

The complete Lean project is in [lean/](lean/README.md). Its direct
four-point theorem is `BeatAvg.Four.C_eq_Bstar`, in
`lean/BeatAvg/Four/Final.lean`. Run from the repository root:

```bash
python3 anc/lean/tools/check_four.py --jobs 2
python3 anc/lean/tools/check_four_proof.py
```

The project retains the older proof routes because the direct proof
imports their field, matrix, integration, approximation, and lower-bound
lemmas. The submission includes their required `Fast/Cert8Data.lean` definitions
directly and omits the large original eight-point archive, which remains in the
repository. The Lean README distinguishes the reduced submission from the full
historical proof setup.

## Files awaiting organization

Search programs, solver checkpoints, failed candidates, and research notes
remain in `anc/search/graph_experiment/` in the repository, but are excluded
from the arXiv package. Certificate checks use the migrated proof inputs.
The older five-point four-roll certificate and its exact verifier are in
`proofs/s3/0.400695372__c2/five_point/`; the Lean exporter and assembly checker
read their inputs there. S2 summary reports are in `proofs/s2/common/`.
Relative links at migrated paths
keep these programs and historical commands usable. The root
`graph_experiment/`, `lean/`, and `fourpoint_proof/` paths are compatibility
links.

The silver-ratio ladder lower-bound bundle is in
[proofs/s3/silver_ratio_lower/](proofs/s3/silver_ratio_lower/README.md).
It includes the original algebraic note, Python search code, copied rational
witnesses, and an extracted Lean project with pinned dependencies. Its README
distinguishes the standard-library witness checks, optional SymPy field
checks, and formal probability proofs.

The final six-point S2 certificates at `phi`, `beta3prime`, and `beta3`
are in `proofs/s2/six_point_endpoints/`, with their original verifiers.
The seven-point S3 upper certificate at `1+sqrt(2)` is in
`proofs/s3/silver_ratio_seven_point/`, including the original verifier and
the two required JSON inputs, stored losslessly as gzip files. See its README
for provenance, checksums, and the NumPy verification command.
The arXiv package omits the 44.15 MB `cert7_full_k.json.gz`; copy it from
the repository before running this seven-point verifier. The exclusion
witnesses and verifier remain packaged.
The pinned `repository_c3_c4` submodule retains the historical versions
and other original material in the repository, but is entirely excluded from
the submission. Other migrated proof inputs under `anc/` remain included.
