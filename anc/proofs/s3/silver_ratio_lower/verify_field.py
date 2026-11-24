"""Reproduce the exact field calculations in ladder_number_field_certificate.md.

Requires SymPy. This checks algebraic identities, not global mass optimality.
"""
import sympy as s


def main():
    t, z, u = s.symbols('t z u')
    P = s.Poly(
        72*t**14 - 132*t**13 - 526*t**12 + 207*t**11
        + 5374*t**10 - 8269*t**9 - 11547*t**8 + 53262*t**7
        - 87309*t**6 + 88506*t**5 - 60318*t**4 + 27243*t**3
        - 7695*t**2 + 1215*t - 81, t)
    A = 1-t+2*t**2-t**3
    B = t**4/s.Integer(2)-2*t**3+3*t**2/s.Integer(2)
    num = z**3+3*z**2+3*z*A+B
    den = 1+4*z+6*z**2+4*z**3
    Z = t*(2*t**2-6*t+3)/(3*(t-1)*(3*t-1))
    assert s.cancel(s.diff(num, t).subs(z, Z)) == 0
    assert s.cancel((s.diff(num, z)*den-num*s.diff(den, z)).subs(z, Z)
                    + P.as_expr()/(27*(t-1)**4*(3*t-1)**4)) == 0
    lo, hi = s.Rational('0.81558932228969'), s.Rational('0.81558932228970')
    assert P.count_roots(lo, hi) == 1
    assert s.Poly(P, t, modulus=37).is_irreducible
    expressions = {'p': Z/(1+Z), 'q': t/(1+Z), 'r': (1-t)/(1+Z),
                   'L': (num/den).subs(z, Z)}
    p, q, r = (expressions[key] for key in ('p', 'q', 'r'))
    F = (p**3*(q+r)+3*p**2*(q+r)**2
         +3*p*(q**3+3*q**2*r+2*q*r**2+r**3)
         +q**3*r+s.Rational(3, 2)*q**2*r**2)
    assert s.cancel(p+q+r-1) == 0
    assert s.cancel(F/(1-p**4)-expressions['L']) == 0
    # Numerical printing is informational; isolation and irreducibility are exact.
    theta = s.nsolve(P.as_expr(), t, s.Rational(8156, 10000), prec=70)
    for name, expression in expressions.items():
        a, b = s.fraction(s.cancel(expression))
        assert s.gcd(P.as_expr(), b) == 1
        resultant = s.resultant(P.as_expr(), u*b-a, t)
        minimal = s.Poly(resultant, u).primitive()[1]
        assert minimal.degree() == 14
        assert s.Poly(minimal, u, modulus=37).is_irreducible
        print(name, s.N(expression.subs(t, theta), 55))
    # The decimal lower bound uses these exact rational masses, independently
    # of root approximation or stationarity.
    p, q, r = (s.Rational(v, 10**12)
               for v in (364616428198, 518212056720, 117171515082))
    F = (p**3*(q+r)+3*p**2*(q+r)**2
         +3*p*(q**3+3*q**2*r+2*q*r**2+r**3)
         +q**3*r+s.Rational(3, 2)*q**2*r**2)
    assert F/(1-p**4) > s.Rational(4952063382580596903, 10**19)
    print('Exact identities, root isolation, degree-14 fields, and decimal bound verified')


if __name__ == '__main__':
    main()
