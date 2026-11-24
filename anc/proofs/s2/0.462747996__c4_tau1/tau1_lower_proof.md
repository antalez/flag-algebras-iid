# Algebraic lower law above c4

This is a lower construction for the candidate plateau `(c4,tau1]`.
A matching upper certificate is still missing.
The independently verified near-optimal certificate gives the uniform band
`0.46274799646310<S_2(c)<0.462749332567` throughout this interval.
Run `python3 graph_experiment/verify_tau1_band.py --ratios 31` to check it exactly.

This extends the four-atom construction on `(c3,tau0]`. There, writing the
bottom mass as `a` and the three upper masses as `u1,u2,u3`, the guaranteed
success polynomial is

```
beta0 = a*(1-a) - a*(u1²+u2²+u3²).
```

For fixed `a`, equal upper masses maximize this polynomial. The five-atom
ladder here has the analogous polynomial

```
beta1 = a*(1-a) - a*(b²+2t²+d²) + b²*d.
```

The last term rewards the additional success `(x1,x1,x4)`. The two middle
upper masses remain equal: with their sum fixed, minimizing their sum of
squares gives equal masses. The first and last upper masses satisfy
`b*(a-d)=a*t` and `d-t=b²/(2a)` at the positive stationary point; the verifier
checks both relations exactly. Both intervals use the same recursive boost
from `beta` to `B`, described below. The comparison explains the lower
construction without asserting a matching unrestricted upper bound.

For `c>c4` sufficiently close to `c4`, start with the ladder

```
x0=1, x1=2/c, x2=(1+x1)/c, x3=(1+x2)/c, x4=(1+x3)/c.
```

The threshold equation `c4^5=c4^3+c4^2+c4+2` says `x4=c4`
at `c=c4`. Just to the right, `x4<c`. Add a small positive error
at each step of the recurrence, so `2<c*x1` and
`1+xj<c*x(j+1)` become strict while `x4<c` remains true.
The comparison `2*x1<c*x4` is already strict at `c4`, as checked
exactly in `verify_tau1_plateau.py`, and survives the perturbation.

Assign masses `(a,b,t,t,d)` to these five atoms. The guaranteed
ordered winning triples contribute

```
beta = a²(1-a) + 2ab(2t+d) + 2at(t+2d) + b²d,
d = 1-a-b-2t.
```

The stationary equations in `(a,b,t)` give the sextic

```
9909 a⁶ + 12492 a⁵ - 10848 a⁴ - 3776 a³
       + 3256 a² - 416 a - 16 = 0,
```

with `a` near `0.52738772214867`. The verifier isolates `2a` in
`(1,2)`; its polynomial is strictly increasing there, since all
coefficients of its derivative after shifting by `1` are positive.
The other masses are recorded as exact polynomials in `a`.
It checks all stationary equations, positive masses, and normalization.
Stationarity alone does not assert global optimality.

Writing `k=1-beta`, recursive replacement of zero uses scale mass

```
D = sqrt(1-3k+9k²),
w = (1+3k-D)/(3k),
B = (1-k*w²)/(3-3w+w²) = 2(D-3k+1)/3.
```

The standard-library check gives

```
0.46274799646310 < B < 0.46274799646312.
```

The strict single-scale construction is feasible arbitrarily close
to `c4` from the right. Scale separation and recursive zero replacement
give `S_2(c)>=B` there; monotonicity extends the lower bound to every
`c>c4`. Run `python3 graph_experiment/verify_tau1_plateau.py` to check
the exact identities. The current upper-certificate scaffold in that
file does not prove equality.
