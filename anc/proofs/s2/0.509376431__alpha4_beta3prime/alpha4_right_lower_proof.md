# A uniform right-hand lower bound at alpha4

Let `alpha4` be the positive root of
`c^6=c^5+c^3+c^2+c+2`. Define `gamma=(-35+13*sqrt(13))/54`,
`s=(3-sqrt(3-6*gamma))/(3*(1+gamma))`,
`beta=2*s-3*s^2+(1+gamma)*s^3`, `k=1-beta`, and

```
B=(2/3)*(sqrt(1-3*k+9*k^2)-3*k+1).
```

Then `S_2(c)>=B>0.5093764319755` for every `alpha4<c<2`.
`check_alpha4_right_lower.py` verifies this rational bracket, the masses,
and the recursive boost identity exactly. This lower bound does **not** by
itself prove a jump: a certified upper bound at `alpha4` below `B` is also
required.

More generally, let `r0=1` and `r_{n+1}=(1+r_n)/c`. The analogous
threshold `alpha_n`, for `n>=1`, is determined by `r_n=c*(c-1)`, equivalently

```
c^(n+2)=c^(n+1)+c^(n-1)+...+c+2.
```

The sum between `c^(n-1)` and `c` is empty for `n=1`. For fixed
`1<c<2`, the `r_n` increase to `1/(c-1)`; each `r_n` with `n>=1` decreases as `c`
increases. Therefore the `alpha_n` increase to the unique root of
`c*(c-1)^2=1`, namely `beta3prime`. These are construction thresholds;
the recurrence alone does not prove that every one is a discontinuity.

For any `alpha4<c<2`, choose `1<x1<x2<x3<x4<H<c` with

```
2<c*x1,  1+x1<c*x2,  1+x2<c*x3,  1+x3<c*x4,
x4<(c-1)*H.
```

Starting with `r0=1`, `r_{j+1}=(1+r_j)/c` gives limiting ladder atoms
`r1,...,r4`, which are strictly increasing for `1<c<2`. The limiting
high atom is `r4/(c-1)`, and it is less than `c` exactly when
`c^6>c^5+c^3+c^2+c+2`, i.e. `c>alpha4`. Small upward perturbations in
order make all inequalities strict.

Place mass `a=s*(sqrt(13)-2)/3` at `1`, mass
`b=s*(5-sqrt(13))/12` at each `xj`, and mass `h=1-s` at `H`.
The guaranteed ladder successes contribute `4*a^2*b+12*a*b^2`, equal to
`gamma*s^3`. Every pair with at least one summand below `H` succeeds when
the target is `H`, contributing `h-h^3`. Thus the one-scale success
probability is at least `beta`. Since all atoms lie in one multiplicative
`c`-window, recursive zero replacement with
`w=(1+3*k-sqrt(1-3*k+9*k^2))/(3*k)` yields `B`.
