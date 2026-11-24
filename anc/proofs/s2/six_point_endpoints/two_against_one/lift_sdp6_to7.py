"""Lift a six-point Gram certificate to a seven-point cover with zero root block."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from sdp7 import np, assemble, enumerate_seven, exact_certificate, save
from verify_sdp7 import verify


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover6', type=Path, required=True)
    p.add_argument('--cover7', type=Path, required=True)
    p.add_argument('--certificate', type=Path, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    args = p.parse_args()
    data = json.loads(args.cover6.read_text())
    with np.load(args.cover7) as archive:
        states, restrictions, states6 = archive['states'], archive['restrictions'], archive['states6']
    rebuilt, rr, ss, meta = enumerate_seven(data, max_leaves=len(states)+1)
    if (not meta['complete'] or not np.array_equal(states, rebuilt)
            or not np.array_equal(restrictions, rr) or not np.array_equal(states6, ss)):
        raise ValueError('Seven-point cover failed complete regeneration')
    seed = json.loads(args.certificate.read_text())
    if seed['s'] != 6 or seed.get('summands') != 2 or seed['coefficient'] != data['coefficient']:
        raise ValueError('Incompatible six-point seed')
    patterns, _, blocks = assemble(data)
    if len(blocks) != len(seed['blocks']) or any(
            json.loads(json.dumps(b['flags'])) != old['flags'] for b, old in zip(blocks, seed['blocks'])):
        raise ValueError('Seed flag basis mismatch')
    matrices = []
    for old in seed['blocks']:
        factor = np.array([[float(Q(v)) for v in row] for row in old['L']])
        matrices.append(factor @ factor.T)
    count = int(states6.max())+1
    matrices.append(np.zeros((4*count, 4*count)))
    bound, cert = exact_certificate(patterns, blocks, matrices, states, restrictions, count, digits=10)
    cert.update(coefficient=data['coefficient'], summands=2, tuples=data['tuples'],
                search='Six-point Gram lift; zero seven-point root block')
    checked = verify(data, states, restrictions, cert)
    checked.update(complete_cover_reenumerated=True)
    save(args.output_dir/'certificate.json', cert)
    save(args.output_dir/'verification.json', checked)
    print(json.dumps(checked), flush=True)


if __name__ == '__main__':
    main()
