"""Verify a seven-point upper bound throughout 1<c<=c2 at the exact root."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from sdp7 import np, enumerate_seven, save
from endpoint_c2 import verify_endpoint, POLY
from verify_sdp7 import verify


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--cover7', type=Path, required=True)
    p.add_argument('--endpoint-proof', type=Path, required=True)
    p.add_argument('--upper-certificate', type=Path, required=True)
    p.add_argument('--target', type=Q)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    data = json.loads(args.cover6.read_text())
    endpoint = verify_endpoint(data, json.loads(args.endpoint_proof.read_text()))
    with np.load(args.cover7) as archive:
        states, restrictions, states6 = archive['states'], archive['restrictions'], archive['states6']
    rebuilt, rr, ss, meta = enumerate_seven(data, max_leaves=len(states)+1)
    if (not meta['complete'] or not np.array_equal(states, rebuilt)
            or not np.array_equal(restrictions, rr) or not np.array_equal(states6, ss)):
        raise ValueError('Seven-point cover failed complete regeneration')
    upper = verify(data, states, restrictions, json.loads(args.upper_certificate.read_text()))
    u = Q(upper['exact_bound'])
    if args.target is not None and u > args.target:
        raise ValueError('Verified upper bound exceeds the requested target')
    result = dict(threshold='Unique positive root c2 of c^3-c-2', polynomial=POLY,
        statement='S2(c) <= upper_at_c2_exact for every 1<c<=c2',
        upper_at_c2_exact=str(u), upper_at_c2=float(u),
        meets_04502080=u <= Q('0.4502080'), endpoint_coverage=endpoint,
        seven_rows=len(states), gram_bound_independently_verified=True,
        seven_cover_reenumerated=True,
        proof_files=dict(cover6=str(args.cover6), cover7=str(args.cover7),
            endpoint=str(args.endpoint_proof), upper=str(args.upper_certificate)))
    if args.output:
        save(args.output, result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
