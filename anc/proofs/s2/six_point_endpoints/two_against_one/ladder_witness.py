"""Exact recursive lower-bound witnesses above the ladder thresholds.

The mass search is local; the resulting rational lower bound is exact.
"""
import argparse
from fractions import Fraction as Q
import json
from itertools import product
from pathlib import Path

from search import events, exact_value, optimize
from sdp6 import bracket, polynomial


def ladder(c, n):
    """Unnormalized atoms satisfy a0=1, c*a[j+1]=1+a[j]+delta."""
    if n < 1 or not 1 < c < 2 or polynomial(c, n) <= 0:
        raise ValueError("Require c strictly above the requested ladder root")
    r, t = [Q(1)], [Q(0)]
    for _ in range(n):
        r.append((1+r[-1])/c)
        t.append((1+t[-1])/c)
    delta = (c-r[-1])/(2*t[-1])
    a = [x+delta*y for x, y in zip(r, t)]
    if not all(x < y for x, y in zip(a, a[1:])) or not a[-1] < c:
        raise ValueError("Ladder order failed; choose c closer to the threshold")
    assert all(c*a[j+1] > 1+a[j] for j in range(n))
    return [Q(0)]+[x/a[-1] for x in a], delta


def verify(c, law):
    xs, masses = [list(map(Q, law[key])) for key in ("support_exact", "masses_exact")]
    if len(xs) != len(masses) or xs[0] != 0 or xs[-1] != 1:
        raise ValueError("Invalid support")
    if any(x >= y for x, y in zip(xs, xs[1:])) or any(p < 0 for p in masses) or sum(masses) != 1:
        raise ValueError("Invalid probability law")
    terms, slack = events(xs, c)
    f = exact_value(terms, masses)
    value = f/(1-masses[0]**3)
    rho = Q(law["rho_exact"])
    assert 0 < rho < xs[1] and 2*rho < slack and c*rho < xs[1]
    assert f == Q(law["base_exact"]) and value == Q(law["value_exact"])
    return {"exact": str(value), "decimal": float(value), "exact_checked": True}



def _uniform_ladder(cminus, cplus, law, n):
    """Uniform right-side proof for the two- and three-step ladder families.

    Each selected success follows from a_n<c*a0 or
    c*a[j+1]>a0+a[j]. The recursive scale may depend on c.
    """
    if n not in (2, 3):
        raise ValueError('This event family supports only n=2 or n=3')
    if not 1 < cminus < cplus < 2 or not polynomial(cminus, n) < 0 < polynomial(cplus, n):
        raise ValueError(f'Expected rational endpoints bracketing c{n}')

    def recurrence(c):
        r, t = [Q(1)], [Q(0)]
        for _ in range(n):
            r.append((1+r[-1])/c)
            t.append((1+t[-1])/c)
        return r, t

    rlo, tlo = recurrence(cminus)
    rhi, thi = recurrence(cplus)
    delta_hi = (cplus-rhi[-1])/(2*thi[-1])
    # r_j,t_j decrease in c. Above the root, delta=(c-r_n)/(2*t_n)
    # increases from zero, so these bounds hold on the entire interval.
    upper = [r+delta_hi*t for r, t in zip(rlo, tlo)]
    order_slacks = [rhi[j+1]-upper[j] for j in range(n)]
    if min(order_slacks) <= 0:
        raise ValueError('Could not prove uniform ladder ordering')
    masses = list(map(Q, law['masses_exact']))
    if len(masses) != n+2 or min(masses) < 0 or sum(masses) != 1 or masses[0] == 1:
        raise ValueError('Invalid ladder masses')
    terms = {}
    count = 0
    for i, j, k in product(range(n+2), repeat=3):
        success = (k > 0 and (i == 0 or j == 0)) or (min(i, j) == 1 and k > max(i, j))
        if success:
            powers = tuple((i, j, k).count(v) for v in range(n+2))
            terms[powers] = terms.get(powers, 0)+1
            count += 1
    f = exact_value(terms, masses)
    value = f/(1-masses[0]**3)
    claimed = law.get('value_exact', law.get('recursive_lower_bound_exact'))
    if value != Q(claimed):
        raise ValueError('Uniform ladder events do not attain the claimed lower bound')
    return dict(statement=f'S2(c) >= value_exact for every c > c{n}',
                root_polynomial={2: 'c^3-c-2', 3: 'c^4-c^2-c-2'}[n], root_bracket=list(map(str, (cminus, cplus))),
                masses_exact=list(map(str, masses)), order_slacks_lower=list(map(str, order_slacks)),
                selected_ordered_successes=count, base_exact=str(f), value_exact=str(value),
                decimal=float(value), exact_checked=True)


def uniform_c2(cminus, cplus, law):
    """Prove the saved four-atom masses give a lower bound for every c>c2."""
    return _uniform_ladder(cminus, cplus, law, 2)


def uniform_c3(cminus, cplus, law):
    """Prove the saved five-atom masses give a lower bound for every c>c3."""
    return _uniform_ladder(cminus, cplus, law, 3)



def phi_support(c):
    """Three base atoms enabling new successes exactly to the right of phi."""
    if not 1 < c < 2 or c*c-c-1 <= 0:
        raise ValueError('Require phi<c<2')
    return [Q(0), (1/c+c-1)/2, Q(1)]


def uniform_phi(cminus, cplus, law):
    """Prove a fixed-mass recursive lower bound for every c>phi.

    For phi<c<=cplus<2, a=(1/c+c-1)/2 satisfies
    c*a-1=(c*c-c-1)/2>0, c-a-1=(c*c-c-1)/(2*c)>0,
    and c-2*a=1-1/c>0. These establish every selected success.
    Extend to c>cplus by monotonicity, allowing the recursive scale
    to depend on c and shrink to zero at phi.
    """
    if not (1 < cminus < cplus < 2 and cminus*cminus-cminus-1 < 0
            and cplus*cplus-cplus-1 > 0):
        raise ValueError('Expected rational endpoints bracketing phi')
    masses = list(map(Q, law['masses_exact']))
    if len(masses) != 3 or min(masses) < 0 or sum(masses) != 1 or masses[0] == 1:
        raise ValueError('Invalid three-atom masses')
    terms, count = {}, 0
    for i, j, k in product(range(3), repeat=3):
        success = (k > 0 and (i == 0 or j == 0)) or (k == 2 and min(i, j) == 1)
        if success:
            powers = tuple((i, j, k).count(v) for v in range(3))
            terms[powers] = terms.get(powers, 0)+1
            count += 1
    f = exact_value(terms, masses)
    value = f/(1-masses[0]**3)
    if value != Q(law['value_exact']):
        raise ValueError('Uniform phi events do not attain the claimed lower bound')
    return dict(statement='S2(c) >= value_exact for every c > phi',
                root_polynomial='c^2-c-1', root_bracket=list(map(str, (cminus, cplus))),
                support_formula='[0, (1/c+c-1)/2, 1]', masses_exact=list(map(str, masses)),
                selected_ordered_successes=count, base_exact=str(f), value_exact=str(value),
                decimal=float(value), exact_checked=True)


def uniform_c4(cminus, cplus, law):
    """Certify a family for EVERY c>c4, using rational endpoint estimates.

    r_j and t_j decrease in c; delta increases and is zero at c4.
    The polynomial has one positive root by Descartes' rule of signs.
    """
    assert polynomial(cminus, 4) < 0 < polynomial(cplus, 4)

    def recurrence(c):
        r, t = [Q(1)], [Q(0)]
        for _ in range(4):
            r.append((1+r[-1])/c)
            t.append((1+t[-1])/c)
        return r, t

    rlo, tlo = recurrence(cminus)
    rhi, thi = recurrence(cplus)
    delta = (cplus-rhi[-1])/(2*thi[-1])
    lower = rhi
    upper = [r+delta*t for r, t in zip(rlo, tlo)]
    # Bounds hold throughout (c4,cplus]; a4<c holds identically by
    # construction, as do c*a[j+1]>a0+a[j].
    order_slacks = [lower[j+1]-upper[j] for j in range(4)]
    extra_slack = cminus*lower[4]-2*upper[1]
    assert min(order_slacks) > 0 and extra_slack > 0
    masses = list(map(Q, law["masses_exact"]))
    terms = {}
    for i, j, k in product(range(6), repeat=3):
        success = (k > 0 and (i == 0 or j == 0)) or (
            min(i, j) == 1 and k > max(i, j)) or (i == j == 2 and k == 5)
        if success:
            powers = tuple((i, j, k).count(v) for v in range(6))
            terms[powers] = terms.get(powers, 0)+1
    f = exact_value(terms, masses)
    value = f/(1-masses[0]**3)
    assert value == Q(law["value_exact"])
    return {"statement": "S2(c) >= value_exact for every c > c4",
            "root_polynomial": "c^5-c^3-c^2-c-2",
            "root_bracket": [str(cminus), str(cplus)],
            "order_slacks_lower": list(map(str, order_slacks)),
            "extra_event_slack_lower": str(extra_slack),
            "value_exact": str(value), "decimal": float(value),
            "exact_checked": True}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--N", type=int, default=4)
    p.add_argument("--c", type=Q)
    p.add_argument("--starts", type=int, default=64)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    cminus, cplus = bracket(args.N, Q(".00001"))
    c = args.c or cplus
    support, delta = ladder(c, args.N)
    # Short decimal atoms make the saved certificate easy to reproduce.
    support = [Q(round(x*10**14), 10**14) for x in support]
    assert c*support[1] > 1
    assert all(c*support[j+2] > support[1]+support[j+1] for j in range(args.N))
    law = optimize(support, c, starts=args.starts)
    checked = verify(c, law)
    result = {"c": str(c), "N": args.N, "cminus": str(cminus),
              "delta_exact": str(delta), "laws": [law], "verification": checked}
    if args.N in (2, 3, 4):
        checker = {2: uniform_c2, 3: uniform_c3, 4: uniform_c4}[args.N]
        result["uniform_right_lower_bound"] = checker(cminus, c, law)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"c": str(c), "support": law["support"],
                      "masses": law["masses"], **checked}), flush=True)


if __name__ == "__main__":
    main()
