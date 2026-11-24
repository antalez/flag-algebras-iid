"""Generate and exactly check a recursive iid family valid for every c>phi."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from ladder_witness import phi_support, uniform_phi
from search import optimize
from verify_lower_laws import verify_law


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--c', type=Q, default=Q('1.618043988749'))
    p.add_argument('--starts', type=int, default=16)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    if args.starts < 1:
        p.error('Require at least one mass-search start')
    law = optimize(phi_support(args.c), args.c, starts=args.starts)
    checked = verify_law(args.c, law)
    uniform = uniform_phi(Q('1.618023988749'), args.c, law)
    result = dict(c=str(args.c), event='X1+X2<c*X3',
                  construction='a=(1/c+c-1)/2', **law,
                  verification=checked, uniform_right_lower_bound=uniform)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(checked), flush=True)


if __name__ == '__main__':
    main()
