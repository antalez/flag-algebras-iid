"""Check an exact uniform band on the candidate plateau (c4,tau1]."""

# Shared proof modules are located relative to anc/, independent of the cwd.
from pathlib import Path as _AncPath
import sys as _anc_sys
_anc_sys.path.insert(0, str(next(p.parent for p in _AncPath(__file__).resolve().parents if p.name == "anc")))
from anc.proofs.paths import setup as _anc_setup
_anc_setup(__file__)
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path
from algebraic_field import make_field
from verify_near_small import verify_near
from verify_tau1_plateau import B

HERE = Path(__file__).resolve().parent


def check(ratios=(), *, full_near_optimality=False):
    ratios = sorted(set(ratios))
    assert all(pair in ('31', '41', '32', '42', '43') for pair in ratios)
    stem = 'near_tau1_ratios_'+'_'.join(ratios) if ratios else 'near_tau1_refined'
    cover = json.loads((HERE/(stem+'_cover.json')).read_text())
    cert_stem=stem+'_full_near' if full_near_optimality else stem
    cert = json.loads((HERE/(cert_stem+'_certificate.json')).read_text())
    assert cert.get('full_near_optimality',False)==full_near_optimality
    polynomial = [-4, 0, -1, 0, 1]
    assert cover['n'] == 4 and cover['polynomial'] == polynomial
    endpoint = make_field(polynomial)
    c = endpoint([0, 1, 0, 0])
    assert cover['c'] == c.json()
    assert c**5-c**3-c**2-c-2 > 0
    r1 = 2/c
    r2 = (1+r1)/c
    r3 = (1+r2)/c
    r4 = (1+r3)/c
    ladder = [endpoint(1), r1, r2, r3, r4]
    extra = [ladder[int(pair[0])]/ladder[int(pair[1])] for pair in ratios]
    assert cover['cuts'] == [q.json() for q in sorted(set(
        [r1, r2, r3, r4, c, r2/r1]+extra))]
    result = verify_near(cover, cert)
    upper = Q(result['upper'])
    lower = Q('0.46274799646310')
    assert lower < B < upper
    # The lower construction holds for every c>c4. Monotonicity extends
    # the verified endpoint upper to every c<=tau1.
    denominator = 10**12
    rounded_upper = Q((upper.numerator*denominator)//upper.denominator+1,
                      denominator)
    gap = rounded_upper-lower
    width = Q((gap.numerator*10**7)//gap.denominator+1, 10**7)
    assert upper < rounded_upper and gap < width <= Q('0.000003')
    return dict(interval='(c4,tau1]', lower_algebraic=B.json(),
                lower_rounded_down=str(lower), upper=str(upper),
                upper_rounded_up=str(rounded_upper),
                upper_decimal=float(upper),
                maximum_interval_variation=str(width),
                cover=stem+'_cover.json', certificate=cert_stem+'_certificate.json',
                full_near_optimality=full_near_optimality,
                exact_plateau_proved=False, all_exact_checks_passed=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--ratios', nargs='+', choices=['31', '41', '32', '42', '43'])
    ap.add_argument('--full-near-optimality',action='store_true')
    args = ap.parse_args()
    result = check(args.ratios or (),full_near_optimality=args.full_near_optimality)
    stem = 'tau1_ratios_'+'_'.join(sorted(set(args.ratios))) if args.ratios else 'tau1'
    if args.full_near_optimality:stem+='_full_near'
    (HERE/(stem+'_plateau_band.json')).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
