# The six-point flag certificate

Files in `starting_point/`: `cert_6_json.txt` (flags and rational factors) and
`farkas_6_json.txt` (the list of patterns, as a search tree with 6,961 pruning certificates).
They were supplied with the problem; they were not computed here.

## Verify (Python standard library only)

    cd starting_point
    python3 verify_cert.py

Expected: `CERTIFIED: C <= 201272564718335614989/500000000000000000000  ~= 0.40254513`.

## Search again for a certificate

Needs the packages of `requirements.txt` (Clarabel or SCS). Not re-run here.

    python reproduce_sdp.py --solver clarabel --output outputs/reproduction.json --certificate outputs/certificate.json
    python3 verify_cert.py --certificate outputs/certificate.json

## Use in Lean

`formal/proof/data/gen_six.py` reads `cert_6_json.txt` and `formal/proof/data/farkas.txt` and
writes the Lean files of the six-point bound; see `LEAN_DATA.md`. The Lean proof does not use
`farkas_6_json.txt`: it runs its own search for the patterns.
