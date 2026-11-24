# The ladder lower bound and a strategy for exact algebraic certificates

## 1. The conjecture and its status

For independent, identically distributed nonnegative random variables, define

\[
S(c)=\sup_\mu\Pr_{\mu^{\otimes4}}(X_1+X_2+X_3<cX_4),
\qquad c_*=1+\sqrt2.
\]

The proposed sharp value at the endpoint is

\[
\boxed{S(c_*)=L},\qquad
L=0.495206338258059690326249498397770285233710263\ldots.
\]

The construction below establishes the **lower bound** \(S(c_*)\ge L\).
What is conjectural is **sharpness**, namely the reverse inequality over all
probability laws. The construction approaches L through a sequence of laws;
it does not assert that a single limiting atomic law attains L.

The reported seven-point upper bound near 0.49522 is about
\(1.37\times10^{-5}\) above L. That is consistent with sharpness but does not
prove it. The server certificate producing that reported bound has not been
independently checked as part of this note. A verified upper bound below 1/2
would settle the endpoint half-probability question without settling the exact
value L.

## 2. One finite ladder

Fix an integer \(N\ge1\). Before perturbation, set

\[
b_j=\sqrt2-(\sqrt2-1)c_*^{-j},\qquad 0\le j\le N.
\]

Then \(b_0=1\), \(b_{j+1}=(2+b_j)/c_*\), and \(b_N<\sqrt2\).
The unperturbed comparisons are equalities, which do not count in the strict
event. To make them successful, choose explicitly

\[
\varepsilon_N=\frac{(c_*-1)(\sqrt2-b_N)}4>0,
\qquad
a_0=1,\qquad
a_{j+1}=\frac{2+a_j+\varepsilon_N}{c_*}.
\]

Indeed,

\[
a_j=b_j+\frac{\varepsilon_N}{c_*-1}(1-c_*^{-j}),
\]

so \(1=a_0<a_1<\cdots<a_N<\sqrt2\). The useful comparisons are

\[
2+a_j<c_*a_{j+1},\qquad 1+a_j<c_*.
\]

Choose masses \(p,q,r\ge0\), with \(p+q+r=1\) and \(p<1\), and put

\[
\nu_N=p\delta_0+q\delta_1+\frac rN\sum_{j=1}^N\delta_{a_j}.
\]

Here p is the mass reserved for lower scales, q is the mass of the main
positive atom, and r is the total mass of the ladder tail. Each of the N tail
atoms has mass r/N.

### Counting successful events

The base probability is

\[
\begin{aligned}
F_N(p,q,r)={}&p^3(q+r)+3p^2(q+r)^2\\
&+3p(q^3+3q^2r+2qr^2+r^3)\\
&+q^3r+\frac32q^2r^2\left(1-\frac1N\right).
\end{aligned}
\]

The terms correspond respectively to three zero summands, two zero summands,
one zero summand, and no zero summands. In the last case, a tail target accepts
three main atoms, or two main atoms and an earlier tail atom. For example,
the latter contribution is

\[
3q^2\sum_{1\le j<k\le N}\frac rN\frac rN
=\frac32q^2r^2(1-1/N).
\]

There are no additional all-positive successes: three main atoms fail against
the main target, and a main atom plus two tail atoms already exceeds every
possible threshold, since
\(1+2a_1>1+6/c_*>c_*\sqrt2>c_*a_N\).
With two main atoms and one tail atom, the adjacent inequalities above and
\(a_j<\sqrt2=2/(c_*-1)\) distinguish earlier from later tail atoms.

For unequal tail masses \(w_j\) summing to r, the last term is
\(\frac32q^2(r^2-\sum_jw_j^2)\). Equal tail masses maximize it for a fixed N.

## 3. Repeating the block at smaller scales

Let \(M=a_N\), and let d be the minimum strictly positive success margin in
the finite base support:

\[
d=\min\{c_*x_4-x_1-x_2-x_3>0:
             x_i\in\{0,a_0,\ldots,a_N\}\}.
\]

Choose

\[
0<\rho\le\min\left\{\frac{d}{6M},\frac{1}{2c_*M},\frac12\right\}.
\]

Replacing a zero by a draw from a lower-scale copy adds at most \(\rho M\).
Thus any base success remains successful: its three summands increase by at
most \(3\rho M\le d/2\). A positive base summand cannot succeed against a
lower-scale target because \(c_*\rho M\le1/2<1\).

Replace the zero atom by a scaled copy repeatedly. The resulting law is

\[
\boxed{
\mu_N=\sum_{k=0}^{\infty}p^k
\left(q\delta_{\rho^k}
      +\frac rN\sum_{j=1}^N\delta_{\rho^ka_j}\right).
}
\]

Its total mass is \((q+r)/(1-p)=1\). There is no residual atom at zero.
Dividing all support locations by M puts the law on [0,1] without changing
the event probability.

When all four draws belong to the lower-scale copy, the same problem repeats,
with probability \(p^4\). Every other comparison has exactly its base-block
outcome. Hence

\[
\Pr_{\mu_N^{\otimes4}}(X_1+X_2+X_3<c_*X_4)
=\frac{F_N(p,q,r)}{1-p^4}.
\]

Keeping only J scales and placing the remaining mass \(p^J\) at zero instead
gives the finite-support probability
\(F_N(1-p^{4J})/(1-p^4)\).

The scale ratio is allowed to depend on N. One must not collapse the ladder
tail into a single atom at \(\sqrt2\): that creates equalities and changes the
strict-event probability.

## 4. The limiting mass parameters and exact lower-bound value

Let \(F_\infty\) be the preceding polynomial with \(1-1/N\) replaced by 1.
Introduce

\[
t=\frac{q}{q+r},\qquad z=\frac{p}{q+r};
\qquad
p=\frac z{1+z},\quad q=\frac t{1+z},\quad r=\frac{1-t}{1+z}.
\]

The limiting probability is

\[
R(t,z)=\frac{\mathcal N(t,z)}{\mathcal D(z)},
\]

where

\[
\begin{aligned}
A(t)&=1-t+2t^2-t^3,\\
B(t)&=\tfrac12t^4-2t^3+\tfrac32t^2,\\
\mathcal N(t,z)&=z^3+3z^2+3zA(t)+B(t),\\
\mathcal D(z)&=1+4z+6z^2+4z^3.
\end{aligned}
\]

Numerical optimization selects an interior stationary point. The equation
\(\partial_tR=0\) gives

\[
z=z(t)=\frac{t(2t^2-6t+3)}{3(t-1)(3t-1)}.
\]

Substituting this in the other stationarity equation gives

\[
\left(\partial_z\mathcal N\,\mathcal D
-\mathcal N\,\partial_z\mathcal D\right)(t,z(t))
=-\frac{P(t)}{27(t-1)^4(3t-1)^4},
\]

with the explicit polynomial

\[
\begin{aligned}
P(T)={}&72T^{14}-132T^{13}-526T^{12}+207T^{11}
       +5374T^{10}-8269T^9\\
&-11547T^8+53262T^7-87309T^6+88506T^5\\
&-60318T^4+27243T^3-7695T^2+1215T-81.
\end{aligned}
\]

Define \(\theta\) to be the unique real root of P in the rational interval

\[
I=(0.81558932228969,\;0.81558932228970).
\]

Set \(z_*=z(\theta)\) and define the masses and L exactly by

\[
p=\frac{z_*}{1+z_*},\qquad
q=\frac{\theta}{1+z_*},\qquad
r=\frac{1-\theta}{1+z_*},\qquad
\boxed{L=R(\theta,z_*)}.
\]

Their numerical values are

\[
\begin{aligned}
p&=0.36461642819828932451023403714972408913\ldots,\\
q&=0.51821205671976202807077997061197545327\ldots,\\
r&=0.11717151508194864741898599223830045759\ldots.
\end{aligned}
\]

These masses are positive and sum to one. For these fixed masses, every finite
ladder satisfies the exact identity

\[
\frac{F_N(p,q,r)}{1-p^4}
=L-\frac{3q^2r^2}{2N(1-p^4)}.
\]

Consequently \(S(c_*)\ge L\). This lower-bound proof does not require proving
that the chosen stationary point globally maximizes the ladder formula.
Numerical optimization supports that additional assertion; a stationary-point
calculation alone is not a proof of global optimality.

## 5. The number field and the chosen ordering

Define

\[
K=\mathbb Q(\theta)\cong\mathbb Q[T]/(P(T)).
\]

The polynomial P is irreducible over \(\mathbb Q\): its reduction modulo 37
is irreducible of degree 14. Thus \([K:\mathbb Q]=14\).

Eliminating \(\theta\) from each of the formulas for p, q, r, and L produces
a primitive degree-14 polynomial, also irreducible modulo 37. Therefore

\[
\mathbb Q(p)=\mathbb Q(q)=\mathbb Q(r)=\mathbb Q(L)=K.
\]

These irreducibility assertions, the stationarity identities, and uniqueness
of the root in I were checked in exact arithmetic while preparing this note.
They are reproducible by the SymPy snippet at the end.

Every field element has a unique representation

\[
u=u_0+u_1\theta+\cdots+u_{13}\theta^{13},\qquad u_i\in\mathbb Q.
\]

Store it as fourteen rational coefficients. Addition and multiplication are
exact polynomial arithmetic, with reduction modulo P. Inverses are obtained
by the polynomial extended Euclidean algorithm. The interval I selects the
real embedding used for **all** sign and PSD tests. Positivity at other
embeddings is neither required nor implied.

This is a complete exact representation; no expression in radicals is needed.
Degree 14 alone does not decide whether radical expressions exist. No
Galois-group determination is asserted here.

The geometric coefficient \(c_*\) belongs to \(\mathbb Q(\sqrt2)\). Its field
need not be used for the SDP matrix entries: once patterns are fixed, the
flag-product counts and objective coefficients are rational. Keep geometric
pruning in \(\mathbb Q(\sqrt2)\) and the proposed sharp SDP certificate in K.
If an implementation genuinely combines their elements, use the compositum
\(K(\sqrt2)\) with both real embeddings specified.

## 6. What an exact upper certificate must prove

Choose a point order n and a complete covering set \(\mathcal H_n\) of
realizable strict patterns at the exact coefficient \(c_*\). An outer cover
is sufficient; extra unrealizable patterns only strengthen the conditions
imposed on the certificate. Exclusions require exact geometric certificates,
not a floating-point feasibility tolerance.

Let \(d(H)\in\mathbb Q\) be the number of successful triple-target
comparisons divided by \(4\binom n4\). Let \(C_b(H)\) be the symmetric rational
flag-product matrix for block b. A block with t roots and flags of size f uses
two disjoint extensions, requires \(2f-t\le n\), and has normalization

\[
\binom nt\binom{n-t}{f-t}\binom{n-f}{f-t}.
\]

The desired certificate is a collection of symmetric matrices \(Q_b\) over K
such that, at the selected real embedding,

\[
Q_b\succeq0,
\qquad
s_H:=L-d(H)-\sum_b\operatorname{tr}(Q_bC_b(H))\ge0
\quad\text{for every }H\in\mathcal H_n.
\]

For iid sampling, \(\mathbb E[C_b(H)]\succeq0\): conditional on the root
values, the disjoint extensions are independent and their flag probabilities
form an outer product. Taking expectations therefore gives \(S(c_*)\le L\)
for absolutely continuous laws. Adding small independent nonnegative
continuous noise and applying Fatou's lemma to strict successes extends the
bound to arbitrary nonnegative laws. Combined with the ladder construction,
this would prove sharpness.

For seven points, the larger blocks (3,5) and (5,6) are important candidates,
in addition to (1,4) and inherited six-point constraints. Merely extending the
pattern cover without enlarging the available flag blocks may be insufficient.

## 7. Recovering candidate matrix entries in K

### 7.1 Obtain numerical evidence at adequate precision

Solve the intended SDP using the complete cover, or constraint generation with
separation over the complete cover. Record matrices, pattern slacks, numerical
ranks, and candidate kernel vectors. Increase arithmetic precision as needed
for algebraic reconstruction; a small solver residual is not a certificate.

If the true optimum of the chosen finite relaxation exceeds L, changing the
coefficient field will not close that mathematical gap. Numerical evidence
alone does not certify such an obstruction. Better geometric exclusions,
more flag blocks, or a larger point order may be needed first.

### 7.2 Recover the exact affine constraints before individual entries

Identify likely tight patterns and impose

\[
d(H)+\sum_b\operatorname{tr}(Q_bC_b(H))=L
\]

for them. Reconstruct candidate kernel vectors \(w\in K^{m_b}\), and impose
\(Q_bw=0\). If exact candidate limiting primal moment matrices \(M_b^*\) are
available, complementary slackness supplies \(Q_bM_b^*=0\).

All of these are linear equations in the matrix entries over K. Solve them
exactly to obtain an affine parametrization

\[
Q_b=Q_b^{(0)}+\sum_j\lambda_jQ_b^{(j)},\qquad \lambda_j\in K.
\]

Treat numerically guessed tight patterns and kernels as hypotheses. A wrong
guess may make the exact system infeasible or exclude the desired certificate.
Do not regard a tiny numerical eigenvalue as proof of an exact kernel.

### 7.3 Reconstruct the remaining parameters

For a numerical parameter \(\widehat\lambda\), search for a bounded-height
integer relation among

\[
1,\theta,\ldots,\theta^{13},\widehat\lambda.
\]

A candidate relation with nonzero last coefficient gives an element of K.
PSLQ or an LLL-based relation search can propose such relations. Recompute
them at increased precision and check the exact equations afterward.
Approximate agreement alone is insufficient: K contains the rationals and
is dense in the chosen real embedding, so many nearby candidates exist.

Alternatively, after the singular directions and tight equalities are imposed
exactly, choose rational approximations to the remaining free parameters in
the reduced affine space. If the remaining PSD and slack constraints have
strict margins there, sufficiently close approximations preserve them.
This can avoid reconstructing every matrix entry independently.

Use a better-conditioned field basis or a different primitive generator if
the power basis causes large coefficients or unstable relation searches.
Record exact changes of basis in the certificate.

## 8. Checking every certificate inequality exactly

For each retained pattern H, independently reconstruct \(d(H)\) and
\(C_b(H)\) from combinatorial counts and compute \(s_H\in K\).

1. Reduce \(s_H\) to its degree-at-most-13 representative \(g_H(T)\).
2. If all coefficients vanish, the slack is exactly zero.
3. Otherwise refine the rational isolating interval I for \(\theta\) and
   evaluate \(g_H(I)\) with certified interval arithmetic until its sign is
   separated from zero. A Sturm-based sign determination is another option.
4. Accept only zero or positive slacks. Check every pattern, not only those
   active in the numerical solve.

Since P is irreducible and \(\deg g_H<14\), a nonzero representative cannot
vanish at \(\theta\); interval refinement will eventually determine its sign.
Any rational-function representation must also have its denominators checked
as nonzero and their signs accounted for.

Sage provides exact number-field arithmetic and the real-algebraic field
`AA`, including algebraic numbers selected by isolating intervals and exact
comparisons. These are suitable tools for this verification layer; they do
not replace checking the certificate's combinatorial normalization and cover.
See the official [number-field documentation](https://doc.sagemath.org/html/en/reference/number_fields/sage/rings/number_field/number_field.html)
and [real-algebraic arithmetic documentation](https://doc.sagemath.org/html/en/reference/number_fields/sage/rings/qqbar.html).

## 9. Certifying positive semidefiniteness over K

Prefer an exact congruence factorization

\[
\Pi Q_b\Pi^{\mathsf T}=V_bD_bV_b^{\mathsf T},
\]

where \(\Pi\) is a permutation matrix, \(V_b\) is unit lower triangular over K,
and \(D_b\) is diagonal over K. Verify the matrix identity entry by entry in K
and verify each diagonal entry of D is nonnegative at the chosen embedding.
This is an exact PSD certificate, including singular matrices.

A constructive check uses symmetric pivoting:

1. Select a strictly positive diagonal pivot, permuting coordinates if needed.
2. Take its Schur complement using exact field arithmetic and continue.
3. A negative diagonal entry of a remaining Schur complement disproves PSD.
4. A zero diagonal entry in a PSD matrix must have an entirely zero row and
   column. Check this exactly before removing that coordinate. If no positive
   diagonal pivot remains, accept only an exactly zero residual matrix.

Thus no arbitrary positive tolerance is used to discard a residual block.
Alternatively, impose the exact kernel first, restrict by an invertible
congruence transformation, and certify positive definiteness of the remaining
block using exact positive LDL pivots.

It is unnecessary to express each positive D entry as a square in K. A
Cholesky factorization \(Q=UU^{\mathsf T}\) can require square roots outside K
even when Q itself is over K; the LDL certificate avoids this extension.
If two-by-two diagonal blocks are used instead, each such block requires its
own exact PSD check rather than just checks on its diagonal entries.

## 10. Deliverables and limits of the approach

A reproducible sharp certificate should contain:

- The polynomial P, the rational isolating interval I, and the exact formulas
  for p, q, r, and L.
- The complete pattern cover and exact pruning certificates at \(c_*\).
- Ordered flag bases and exact normalization conventions for every block.
- Matrix entries as rational coefficient vectors in the fixed basis of K.
- Exact congruence factorizations and certified signs of their pivots.
- An independent verifier recomputing all pattern slacks and checking every
  algebraic identity, sign, and covering obligation.

Neither \(L\in K\) nor the numerical proximity of an SDP bound proves that
a finite-order sharp certificate exists, or that its matrices can be chosen
over K. Those are research hypotheses to test. A certificate at some larger
algebraic field, or a sequence of nonsharp certificates tending to L, might
be necessary.

For the more modest goal \(S(c_*)<1/2\), a rational upper certificate with a
positive gap below 1/2 is sufficient. The number field is motivated by a
possible **exact sharp-value** proof, not by the half-probability threshold.

## 11. Reproducing the field calculations

The following uses Python with SymPy. It checks the stationarity identities,
the isolating interval, and the degree-14 irreducibility claims. It does not
verify an SDP certificate or prove global optimality of the mass search.

```python
import sympy as s

t, z, u = s.symbols('t z u')
P = s.Poly(
    72*t**14 - 132*t**13 - 526*t**12 + 207*t**11
    + 5374*t**10 - 8269*t**9 - 11547*t**8 + 53262*t**7
    - 87309*t**6 + 88506*t**5 - 60318*t**4 + 27243*t**3
    - 7695*t**2 + 1215*t - 81, t)
A = 1 - t + 2*t**2 - t**3
B = t**4/s.Integer(2) - 2*t**3 + 3*t**2/s.Integer(2)
num = z**3 + 3*z**2 + 3*z*A + B
den = 1 + 4*z + 6*z**2 + 4*z**3
Z = t*(2*t**2 - 6*t + 3)/(3*(t-1)*(3*t-1))

assert s.cancel(s.diff(num, t).subs(z, Z)) == 0
assert s.cancel(
    (s.diff(num, z)*den - num*s.diff(den, z)).subs(z, Z)
    + P.as_expr()/(27*(t-1)**4*(3*t-1)**4)
) == 0
lo = s.Rational('0.81558932228969')
hi = s.Rational('0.81558932228970')
assert P.count_roots(lo, hi) == 1
assert s.Poly(P, t, modulus=37).is_irreducible

expressions = {
    'p': Z/(1+Z),
    'q': t/(1+Z),
    'r': (1-t)/(1+Z),
    'L': (num/den).subs(z, Z),
}
theta = s.nsolve(P.as_expr(), t, s.Rational(8156, 10000), prec=70)
for name, expression in expressions.items():
    a, b = s.fraction(s.cancel(expression))
    assert s.gcd(P.as_expr(), b) == 1
    resultant = s.resultant(P.as_expr(), u*b-a, t)
    minimal = s.Poly(resultant, u).primitive()[1]
    assert minimal.degree() == 14
    assert s.Poly(minimal, u, modulus=37).is_irreducible
    print(name, s.N(expression.subs(t, theta), 55))
```

Related ancillary files: [ladder construction](python/ladder.py),
[recursive probability calculations](python/recursive.py),
[rational construction certificates](python/certificates.py), and
[the four-point endpoint upper certificate](../silver_ratio_four_point/README.md).
