"""Enumerate all open event cells on support {0,a,b,1}, 0<a<b<1.

Exact rational polygon subdivision; local mass optimization in each cell.
Boundary patterns cannot add strict successes, so some neighboring open
cell contains all their successes. This covers supports with <=3 positive
atoms for lower-bound search, but local mass fits do not certify an upper bound.
"""
import argparse
from fractions import Fraction as Q
from itertools import combinations_with_replacement
import json
from pathlib import Path

from search import optimize


def clip(poly, line):
    def value(p):
        return line[0]*p[0]+line[1]*p[1]+line[2]
    out = []
    for p, q in zip(poly, poly[1:]+poly[:1]):
        vp, vq = value(p), value(q)
        if vp >= 0:
            out.append(p)
        if (vp > 0 and vq < 0) or (vp < 0 and vq > 0):
            t = vp/(vp-vq)
            out.append(tuple(u+t*(v-u) for u, v in zip(p, q)))
    out = list(dict.fromkeys(out))
    if len(out) < 3:
        return []
    area = sum(p[0]*q[1]-p[1]*q[0] for p, q in zip(out, out[1:]+out[:1]))
    return out if area else []


def cells(c):
    points = [(Q(0), Q(0), Q(0)), (Q(1), Q(0), Q(0)),
              (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1))]
    lines = set()
    for i, j in combinations_with_replacement(range(4), 2):
        for k in range(1, 4):
            line = tuple(c*v-u-w for u, w, v in zip(points[i], points[j], points[k]))
            if line[0] or line[1]:
                scale = next(v for v in line if v)
                lines.add(tuple(v/scale for v in line))
    polys = [[(Q(0), Q(0)), (Q(0), Q(1)), (Q(1), Q(1))]]
    for line in sorted(lines):
        polys = [part for poly in polys for part in
                 [clip(poly, line), clip(poly, tuple(-v for v in line))] if part]
    return [[Q(0), sum(p[0] for p in poly)/len(poly),
             sum(p[1] for p in poly)/len(poly), Q(1)] for poly in polys]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--c", required=True)
    p.add_argument("--starts", type=int, default=24)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    c = Q(args.c)
    supports = cells(c)
    print(f"Enumerated {len(supports)} open cells exactly", flush=True)
    laws = [optimize(s, c, args.starts) for s in supports]
    laws.sort(key=lambda r: r["value"], reverse=True)
    result = {"c": str(c), "cell_count": len(supports), "starts": args.starts,
              "interpretation": "Exhaustive support cells; local mass optimization, not a universal upper bound.",
              "laws": laws}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(laws[0]), flush=True)


if __name__ == "__main__":
    main()
