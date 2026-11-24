# An algebraic lower bound above alpha3

This gives a lower bound throughout `(alpha3,beta3prime]`; the next ladder
threshold `alpha4` lies inside this interval, so it need not be a single
plateau. No matching upper certificate is claimed. Put `gamma=(-20+14*sqrt(7))/81`,
`s=(3-sqrt(3-6*gamma))/(3*(1+gamma))`,
`beta=2*s-3*s^2+(1+gamma)*s^3`, `k=1-beta`, and

```
B=(2/3)*(sqrt(1-3*k+9*k^2)-3*k+1).
```

Then `S_2(c)>=B` for every `alpha3<c<2`. Exact arithmetic in
`check_beta3prime_lower.py` proves
`0.50905413288916 < B < 0.50905413288917` and checks all mass and
recursive-boost identities below.

Choose `1<x<y<z<H<c` so that

```
2<c*x,  1+x<c*y,  1+y<c*z,  z<(c-1)*H.
```

For `1<c<2`, the limiting locations `x0=2/c`, `y0=(1+x0)/c`,
`z0=(1+y0)/c`, `H0=z0/(c-1)` are strictly increasing. The inequality
`H0<c` is equivalent to `c^5>c^4+c^2+c+2`, which holds for `c>alpha3`.
Small upward perturbations in order give the required strict inequalities.

Put masses `a=s*(sqrt(7)-1)/3`, `b=s*(4-sqrt(7))/9` at `1` and each of
`x,y,z`, respectively, and `h=1-s` at `H`. The displayed ladder successes
at the first four targets have total probability `3*a^2*b+6*a*b^2`,
equal to `gamma*s^3`. Every pair of summands with at least one below `H`
succeeds when the target is `H`, contributing `h-h^3`. Hence the
one-scale success probability is at least `beta`. All atoms are in one
`c`-window; recursive zero replacement with
`w=(1+3*k-sqrt(1-3*k+9*k^2))/(3*k)` gives the stated `B`.
