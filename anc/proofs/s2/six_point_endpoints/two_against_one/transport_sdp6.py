"""Transfer six-point PSD factors to a new cover and recheck the bound exactly."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from sdp6 import np, assemble, certify, verify, save


def transport(data, source, digits=10):
    if source['s'] != 6 or source.get('summands') != 2:
        raise ValueError('Expected a two-summand six-point certificate')
    patterns, _, blocks = assemble(data)
    saved = {(b['t'], b['f'], tuple(b['type'] or [])): b for b in source['blocks']}
    matrices = []
    for b in blocks:
        old = saved.get((b['t'], b['f'], tuple(b['type'] or [])))
        if old is None:
            matrices.append(np.zeros((len(b['flags']), len(b['flags']))))
            continue
        flags = {(tuple(signs), tuple(marks)): i for i, (signs, marks) in enumerate(old['flags'])}
        original = np.array([[float(Q(v)) for v in row] for row in old['L']])
        factor = np.zeros((len(b['flags']), original.shape[1]))
        for i, (signs, marks) in enumerate(b['flags']):
            j = flags.get((tuple(signs), tuple(marks)))
            if j is not None:
                factor[i] = original[j]
        matrices.append(factor @ factor.T)
    bound, cert = certify(patterns.tolist(), blocks, matrices, digits)
    cert.update(summands=2, coefficient=data['coefficient'], tuples=data['tuples'],
                exact_bound=str(bound), search='Transported PSD factors; exact full-cover verification')
    return cert, verify(data, cert)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cover', type=Path, required=True)
    p.add_argument('--certificate', type=Path, required=True)
    p.add_argument('--output-dir', type=Path, required=True)
    args = p.parse_args()
    cert, checked = transport(json.loads(args.cover.read_text()), json.loads(args.certificate.read_text()))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    save(args.output_dir/'certificate.json', cert)
    save(args.output_dir/'verification.json', checked)
    print(json.dumps(checked), flush=True)


if __name__ == '__main__':
    main()
