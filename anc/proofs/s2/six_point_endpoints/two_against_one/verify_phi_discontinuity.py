"""Verify exact phi endpoint coverage, a six-point upper, and a uniform lower."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from sdp6 import verify, save
from endpoint_phi import verify_endpoint, POLY
from verify_lower_laws import verify_law
from ladder_witness import uniform_phi


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--endpoint-proof', type=Path, required=True)
    p.add_argument('--upper-certificate', type=Path, required=True)
    p.add_argument('--lower-witness', type=Path, required=True)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    data = json.loads(args.cover6.read_text())
    endpoint = verify_endpoint(data, json.loads(args.endpoint_proof.read_text()))
    upper = verify(data, json.loads(args.upper_certificate.read_text()))
    lower = json.loads(args.lower_witness.read_text())
    verify_law(Q(lower['c']), lower)
    uniform = uniform_phi(Q(data['coefficient'][0]), Q(lower['c']), lower)
    u, ell = Q(upper['exact_bound']), Q(uniform['value_exact'])
    if not u < ell:
        raise ValueError('No strict endpoint separation')
    result = dict(threshold='Golden ratio phi, unique positive root of c^2-c-1', polynomial=POLY,
        upper_at_phi_exact=str(u), upper_at_phi=float(u),
        uniform_right_lower_exact=str(ell), uniform_right_lower=float(ell),
        right_jump_lower_exact=str(ell-u), right_jump_lower=float(ell-u),
        right_discontinuity_proved=True, endpoint_coverage=endpoint,
        six_rows=len(data['patterns']), gram_bound_independently_verified=True,
        uniform_right_law_exactly_verified=True, uniform_right_lower_bound=uniform,
        proof_files=dict(cover6=str(args.cover6), endpoint=str(args.endpoint_proof),
                         upper=str(args.upper_certificate), lower=str(args.lower_witness)))
    if args.output:
        save(args.output, result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
