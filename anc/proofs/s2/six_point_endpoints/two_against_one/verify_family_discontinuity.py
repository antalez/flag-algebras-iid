"""Verify an endpoint upper and uniform lower at a named analytic-family root."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from sdp6 import verify
from sdp7 import save
from endpoint_c4 import verify_endpoint
from multinacci_families import verify_uniform_family


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family', choices=['multinacci', 'intermediate', 'limit'], required=True)
    p.add_argument('--index', type=int)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--endpoint-proof', type=Path, required=True)
    p.add_argument('--cover7', type=Path, help='Optional complete seven-point archive')
    p.add_argument('--upper-certificate', type=Path, required=True)
    p.add_argument('--lower-families', type=Path,
                   default=Path(__file__).parent/'results/multinacci_families.json')
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    rows = json.loads(args.lower_families.read_text())['rows']
    matches = [row for row in rows if row['family'] == args.family and row['index'] == args.index]
    if len(matches) != 1:
        raise ValueError('Expected exactly one matching lower family')
    uniform = verify_uniform_family(matches[0])
    polynomial = uniform['polynomial']
    data = json.loads(args.cover6.read_text())
    endpoint = verify_endpoint(data, json.loads(args.endpoint_proof.read_text()), polynomial)
    certificate = json.loads(args.upper_certificate.read_text())
    seven_rows = None
    if args.cover7 is None:
        upper = verify(data, certificate)
    else:
        from sdp7 import np, enumerate_seven
        from verify_sdp7 import verify as verify_seven
        with np.load(args.cover7) as archive:
            states, restrictions, states6 = archive['states'], archive['restrictions'], archive['states6']
        rebuilt, rr, ss, meta = enumerate_seven(data, max_leaves=len(states)+1)
        if (not meta['complete'] or not np.array_equal(states, rebuilt)
                or not np.array_equal(restrictions, rr) or not np.array_equal(states6, ss)):
            raise ValueError('Seven-point cover failed complete regeneration')
        upper = verify_seven(data, states, restrictions, certificate)
        seven_rows = len(states)

    u, ell = Q(upper['exact_bound']), Q(uniform['value_exact'])
    result = dict(family=args.family, index=args.index, polynomial=polynomial,
        upper_at_root_exact=str(u), upper_at_root=float(u),
        uniform_right_lower_exact=str(ell), uniform_right_lower=float(ell),
        separation_exact=str(ell-u), separation=float(ell-u), right_discontinuity_proved=u < ell,
        endpoint_coverage=endpoint, six_rows=len(data['patterns']),
        gram_bound_independently_verified=True, uniform_right_lower_bound=uniform,
        proof_files=dict(cover6=str(args.cover6), endpoint=str(args.endpoint_proof),
                         upper=str(args.upper_certificate), lower_families=str(args.lower_families)))
    if args.cover7 is not None:
        result.update(seven_rows=seven_rows, complete_seven_cover_reenumerated=True)
        result['proof_files']['cover7'] = str(args.cover7)
    if args.output:
        save(args.output, result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
