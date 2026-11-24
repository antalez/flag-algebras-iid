# Variable-c experiments and recursive patterns

We study **nonnegative iid** random variables and

\[
S(c)=\sup_\mu\Pr(X_1+X_2+X_3<cX_4).
\]

The research target is the largest coefficient for which \(S(c)\le1/2\).
The original repository scripts are untouched. Everything here uses the
existing `guro_venv` for MILPs; the endpoint flag SDP uses the already-installed
Clarabel solver in `.venv`. Commands below run from the repository root.

## Main findings

The experiments suggest a block repeated at successively smaller scales.
Within each block, one atom has most of the mass; a finite increasing sequence
of smaller-mass atoms follows it. This differs from the c=2 geometric-spacing
pattern. A useful generalization is

\[
a_0=1,\qquad a_{j+1}\simeq\frac{2+a_j}{c},\qquad a_N<c-1.
\]

The recurrence needs a small positive perturbation to make event inequalities
strict. The entire positive block is then normalized to have maximum 1.
`ladder.py` constructs such blocks with exact rational perturbations.

The first block transitions are:

| Number N of tail atoms, after the main atom | Threshold for this block |
|---:|---:|
| 1 | \((1+\sqrt{13})/2=2.302775637732\) |
| 2 | 2.374423763209 |
| 3 | 2.398726487282 |
| 4 | 2.407974094085 |
| 5 | 2.411661492422 |
| 6 | 2.413162533108 |

These thresholds increase to \(1+\sqrt2\). They describe feasibility changes
of this family, not a proved phase diagram of all extremizers.

There are three rigorous conclusions, in addition to the numerical evidence:

1. This entire recursive ladder family, including its infinite-N formula,
   stays below 1/2 for every admissible choice of masses. Its numerically
   optimized limiting value is approximately **0.495206338258**.
2. For **every** \(c>1+\sqrt2\), a five-atom distribution gives
   \(S(c)\ge6601/13122=1/2+20/6561\). Thus the critical coefficient is
   **at most \(1+\sqrt2\)**.
3. The rebuilt six-point Anton SDP gives the exactly certified universal bound
   \(S(1+\sqrt2)\le0.502745283474302167919\). Combined with item 2, this
   **proves a right-hand discontinuity** at \(1+\sqrt2\), although it does
   not establish that this jump crosses 1/2. See
   [the endpoint certificate and proof](anton_endpoint/README.md).

We have **not** established \(S(c)\le1/2\) below or at that endpoint. A different
family could cross 1/2 earlier. The discontinuity conclusion uses the new
universal SDP upper bound, not merely a jump in constructive lower bounds.

## Repeating a block at different scales

Take a base law on \(0,a_0,\ldots,a_N\), with mass p at zero and positive
atom masses summing to 1-p. Let F be its strict-event probability. Replace
the zero atom by a scaled copy of the same law, and repeat. If the scale ratio
rho is sufficiently small, the resulting probability is exactly

\[
F+p^4F+p^8F+\cdots=\frac{F}{1-p^4}.
\]

The infinite law has atoms \(\rho^k a_j\), with masses \(p^k w_j\), for
\(k\ge0\). There is no atom at zero when p<1. Truncation after L blocks,
with remaining mass \(p^L\) at zero, gives
\(F(1-p^{4L})/(1-p^4)\).

This is an explicit construction, not an extrapolation from finite m.
For normalized positive support and minimum successful base slack d, the code
uses

\[
\rho=\min\{d/6,\ a_{\min}/(2c),\ 1/2\}.
\]

Replacing zero LHS slots adds at most 3rho, preserving every base success.
A nonzero LHS cannot become smaller than c times a scaled zero RHS, because
\(c\rho<a_{\min}\). Other failures remain failures. All-zero draws recurse.
The scripts store rational masses, a rational rho, and the exact achieved
probability. Numerical mass optimization is local; the achieved lower bound
is checked by exact arithmetic regardless of optimizer success.

At c=2.35, allowing all six support levels from the iid MILP in the mass
optimization returns the same 0.491156081814 as using a single two-positive-
atom block; the optimizer can concentrate on the rescaled lower copy.
This supports the repeating-block interpretation, without proving uniqueness.

## The ladder formula

Let p be the zero mass, q the mass at a0, and r the total tail mass,
with p+q+r=1. Write the tail masses as \(b_1,\ldots,b_N\).
For \(2<c\le1+\sqrt2\), the constructed ladder has the following events:

- With two zero LHS slots, every positive RHS succeeds.
- With one zero LHS slot and RHS a0, at least one of the other LHS slots
  must equal a0; a tail RHS accepts every pair of positive LHS slots.
- With no zero LHS slots, a tail RHS accepts three copies of a0, or two
  copies of a0 and an earlier tail atom. Other positive triples fail.

Consequently,

\[
F=p^3(q+r)+3p^2(q+r)^2
  +3p(q^3+3q^2r+2qr^2+r^3)
  +q^3r+\frac32q^2\left(r^2-\sum_jb_j^2\right).
\]

For fixed p,q,r, equal tail masses \(b_j=r/N\) maximize this expression.
Thus only two mass parameters need numerical optimization, however long the
ladder is. `ladder.py` checks the formula against independent exact enumeration
of all base events for every generated block.

The unperturbed recurrence has solution

\[
a_j=\frac{2}{c-1}+\left(1-\frac{2}{c-1}\right)c^{-j}.
\]

A finite N is allowed when \(a_N<c-1\). At the threshold,

\[
(c-1)c^N=1+2\sum_{j=0}^{N-1}c^j.
\]

For N=1 this gives \(c^2-c-3=0\), explaining the 2.302776 transition.
For N=2 it gives \(c^3-c^2-2c-3=0\). Arbitrarily long ladders become
possible as c approaches \(1+\sqrt2\) from below.

Numerically optimized, exactly achieved lower bounds from this family:

| c | N | Recursive probability |
|---:|---:|---:|
| 2.25 | 0 | 0.482781746629 |
| 2.303 | 1 | 0.491156081814 |
| 2.35 | 1 | 0.491156081814 |
| 2.38 | 2 | 0.492838853925 |
| 2.40 | 3 | 0.493537310202 |
| 2.41 | 4 | 0.493918195789 |
| 2.414 | 7 | 0.494442136963 |
| 2.4142 | 10 | 0.494663204737 |

Values are lower bounds on S(c), not its established values.

### Exact proof that the ladder family stays below 1/2

Replace \(\sum b_j^2\) by zero to obtain the larger infinite-N expression
\(F_\infty\). Put \(s=q+r>0\), \(t=q/s\), and \(z=p/s\). Then

\[
\frac{\frac12(1-p^4)-F_\infty}{s^4}
 =z^3-H(t)z+g(t),
\]

where

\[
H(t)=1-3t+6t^2-3t^3,\qquad
2g(t)=1-3t^2+4t^3-t^4.
\]

Both H and g are positive on [0,1]. The minimum over z>=0 is
\(g-2(H/3)^{3/2}\). Its positivity follows from
\(27(2g)^2-16H^3>0\). `certificates.py` verifies this last degree-nine
polynomial using exact positive Bernstein coefficients on [0,1/2] and [1/2,1].
All coefficients are saved in `results/recursive/exact_certificates.json`.
This proves the family cannot supply a counterexample below 1/2, even if its
numerical mass optimization missed a better point within the same family.
The degenerate p=1 law has probability zero and is excluded from the recursive
ratio with denominator zero.

### A five-atom counterexample for every c>1+sqrt(2)

Set \(a=1/\sqrt2\) and use a base law on (0,a,1) with masses
\((p,q,r)=(1/3,1/2,1/6)\). When \(c>1+\sqrt2\), both

\[
a+1<ca,\qquad 2a+1<c
\]

hold. The successful base events give at least

\[
F=p^3(q+r)+3p^2(q+r)^2
 +3p(q^3+3q^2r+2qr^2+r^3)+q^3r+3q^2r^2
 =\frac{161}{324}.
\]

Replace the zero atom once by a sufficiently small scaled copy. The resulting
five atoms and masses are

\[
\begin{array}{c|ccccc}
\text{atom}&0&\rho/\sqrt2&\rho&1/\sqrt2&1\\
\hline
\text{mass}&1/9&1/6&1/18&1/2&1/6.
\end{array}
\]

For sufficiently small rho>0 their probability is at least

\[
F(1+p^4)=\frac{6601}{13122}
=\frac12+\frac{20}{6561}>\frac12.
\]

All counted mixed events have strictly positive margins, so such a rho exists
for every c above the endpoint. For large c there may be further successful
events; the lower bound still applies. Infinite recursion gives 161/320.
The code independently enumerates an entirely rational five-atom example at
c=2.415 with a=0.7071 and rho=0.00001, obtaining exactly 6601/13122.

This construction alone proves only the upper restriction on the critical c.
Together with the new endpoint SDP certificate it proves a discontinuity,
but the endpoint assertion S <= 1/2 remains open.

## Correct changes to the MILP

In the default `distinct` mode, for 2<c<3,

\[
\mathcal T_c=\{(i,j,k,\ell):i<j<k,\ \ell\notin\{i,j,k\},\ i<\ell\}.
\]

Only the smallest RHS index is impossible. Thus there are
\(3\binom m4\) candidates, and the probability denominator is still
\(4\binom m4\). The old condition j<ell drops feasible events at c>2.
The c=2 option restores the old set for regression tests.

The new model keeps order implications and adds RHS-rank implications within
each four-set. It replaces the old hard-coded conflicts with pairs generated
for the requested rational c. For a row v, define its suffix sums s. A pair
has an exact conflict certificate when some rational w in [0,1] satisfies
\(w s(v)+(1-w)s(u)\ge0\) coordinatewise. Writing
\(x_i=\sum_{j\le i}d_j\), d_j>=0, proves the two strict inequalities cannot
both hold. Pairs are enumerated on eight ranks, reduced to templates and
lifted to m. A floating-point candidate filter is followed by exact rational
checks; omitted candidates could weaken the model but cannot invalidate it.
The c=2 triple cuts are not reused.

We fix x1=0 and xm=1: for c<3, subtracting the minimum increases every event
slack by (3-c) times that minimum, and normalizing the remaining range further
increases positive slacks. Both indicator and tight ordered-cube big-M
formulations are available.

`--mode iid` includes repeated indices, with the multiplicities of sorted LHS
triples, and denominator m^4. It maximizes the actual probability for an
equal-weight m-point empirical law. It does not optimize arbitrary atom
masses; `recursive.py` handles masses for a fixed block.

## Finite-m results and numerical limitations

All 17 distinct-index m=15 grid points reached solver optimality at margin
2e-5. Selected results:

| c | Optimal fixed-margin count / 5460 | Maximum-margin pattern |
|---:|---:|---|
| 2.15--2.301, sampled points | 2812 / 5460 | 2 zeros, 3 lower equal points, 10 upper equal points |
| 2.303 | 2896 / 5460 | margin-sensitive near the transition |
| 2.31--2.37, sampled points | 2897 / 5460 | 0, 3a, b, 9A, 1 |
| 2.38--2.414, sampled points | 2913 / 5460 | 0, 3a, b, 8A, B, 1 |

Here `3a` means three copies of a, not multiplication of the value. Raw
coordinates need not be unique and can split a plateau without changing the
selected inequality set. Maximum-margin representatives are alternative
witnesses for that set, not a preferred probability distribution.

For example, at c=2.35 the polished small block has a/b approximately 0.7701
and the top block has A approximately 0.7826. Both ratios lie in
\((1/(c-1),c/3)\), so they realize the same two-positive-atom event pattern
at different scales. At m=20, c=2.35, the seeded run found 10074/19380,
with bound 10104/19380 after 90 seconds: a useful witness, not a proved optimum.
The unseeded m=25 trials exhausted 90 seconds mostly in presolve/root work
and did not improve the initial two-level witness; do not interpret those as
worst-case configurations.

Five m=15 checks with seed 1 and margin 2e-6 reproduced the grid counts.
However, near c=2.303 even margin 2e-7 still gives 2896. Transporting the
2897 pattern from c=2.31 by an LP gives a common slack of about 5.069e-8.
Its exported decimal witness is verified exactly to satisfy all 2897 strict
inequalities. This is a concrete example of a fixed margin hiding a feasible
strict pattern.

The iid m=15 runs proved fixed-margin optima 24429/50625=0.482548148 at c=2.25
and 24806/50625=0.489995062 at c=2.35. At c=2.4 a 45-second indicator run and
a 60-second big-M retry retained 24806; the better bound was 24878/50625.
That case is unfinished. Recursive constructions give better distributional
lower bounds without requiring equal empirical masses.

MILP bounds apply to the finite fixed-margin problem; they are not certified
upper bounds on S(c). The exact checks certify the exported witnesses and
the cut validity. Tiny order/bound roundoff is corrected before checking;
the original `solver_x` is retained. In the first batch the largest correction
was 7.77e-16. No event test uses a tolerance: decimal coordinates and rational
c are compared by integer arithmetic, including ties and repeated draws.

## Running the experiments

```bash
# Single MILP and a coefficient sweep.
guro_venv/bin/python new_question_c/solve.py --m 15 --c 2.35 \
  --time-limit 60 --output new_question_c/results/example.json
guro_venv/bin/python new_question_c/sweep.py --m 15 --time-limit 60 \
  --output-dir new_question_c/results/new_grid --quiet

# Actual empirical iid objective.
guro_venv/bin/python new_question_c/solve.py --m 15 --c 2.35 --mode iid \
  --output new_question_c/results/example_iid.json

# Recursive block inferred from a saved solution, with masses optimized.
guro_venv/bin/python new_question_c/recursive.py \
  --source new_question_c/results/m15_grid/m15_c47_20_distinct_seed0.json \
  --output new_question_c/results/recursive/example.json

# Generalized ladder, including the transition sequence.
guro_venv/bin/python new_question_c/ladder.py \
  --c 2.303 2.35 2.38 2.4 2.41 2.414 2.4142 \
  --output new_question_c/results/recursive/ladder_grid.json

# Exact certificates; these do not need a Gurobi license.
guro_venv/bin/python new_question_c/certificates.py \
  --output new_question_c/results/recursive/exact_certificates.json

# Transport a pattern through a small-margin transition.
guro_venv/bin/python new_question_c/continue_pattern.py \
  new_question_c/results/m15_refined/m15_c231_100_distinct_seed0.json \
  --c 2.303 --output new_question_c/results/continuation/example.json

# Regression tests and independent exact witness audit.
guro_venv/bin/python -m unittest discover -s new_question_c -v
guro_venv/bin/python new_question_c/verify_results.py new_question_c/results
```

`solve.py` additionally supports `--start result.json`, `--seed`, `--threads`,
`--margin`, `--no-cuts`, and `--formulation bigm`. JSON outputs include the
incumbent, solver bound/status/gap, raw and polished coordinates, selected
events, exact empirical counts, conflict certificates and timings. Indices
are 1-based in exported files, without the original script's +1 display shift.

`summarize.py` makes comparison/coordinate CSVs from result directories.
`plot.R` uses base R to generate `results/analysis/patterns.pdf` and PNG.
The existing figures show m=15 distinct-index observations, not the global
function S. Source files and all time-limited results are retained for review.

The next mathematical issue is an upper bound covering *all* support patterns,
or a competing construction below the endpoint. Further large-m runs should
use the recursive construction as a start and report their gaps; exhaustive
pair lifting makes an unseeded m=25 search substantially slower than m=15.
