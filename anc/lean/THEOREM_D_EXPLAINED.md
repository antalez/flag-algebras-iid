# Theorem D explained

*An informal account of the upper bound `C ≤ B*`. The complete written proof is
`results/theorem_D_proof.md`; the formal one is `BeatAvg.C_le_of_certificate` in `BeatAvg/Main.lean`.*

## The problem

Draw four independent numbers `X1, X2, X3, X4` from the same law `μ` on `[0, ∞)`. Call it a
*success* when

    X1 + X2 + X3 < 2 X4.

Write `P(μ)` for the probability of success and `C = sup_μ P(μ)` for the best possible value.

Bellec and Fritz constructed laws with `P(μ)` as close as wanted to

    B* = max_p  p(2 - p) / (1 + p + p² + p³) = 0.4006953723...

and conjectured `C = B*`. Their best upper bound was `0.4167`. This note explains how `C ≤ B*` is
proved.

Two words used throughout:

* The **pattern** of `n` distinct points records, for every four of them, how many of the four are
  successful targets when the other three are the summands. The answer is 0, 1 or 2: only the
  largest or the second largest of four points can succeed, and if the second largest does, so does
  the largest.
* A law is **near-optimal** if `P(μ)` is close to `C`.

## 1. Why the ordinary method stops just short

The flag method takes `n` random points and uses one fact that holds for every law: certain
matrices of pattern frequencies are positive semidefinite (they are averages of squares). A
semidefinite program then gives an upper bound on `C`.

| Method | Bound | Gap to `B*` |
|---|---|---|
| Bellec–Fritz (integer programs) | 0.4167 | 1.6·10⁻² |
| Flags, 6 points | 0.40255 | 1.8·10⁻³ |
| Flags, 7 points, all families | 0.40075444 | 5.9·10⁻⁵ |

The gap shrinks, but it cannot close at any finite `n`. The reason is the shape of the extremal
construction:

* put mass `p` at `0` and spread the rest evenly over the points `1 - 2⁻¹, 1 - 2⁻², ...`;
* replace the atom at `0` by a tiny copy of the whole law;
* do the same inside the tiny copy, and so on.

This is an infinite recursion of scales. A relaxation that looks at `n` points admits
"pseudo-distributions": weights on patterns that satisfy every constraint but are not produced by
any law, and that gain a little by cheating inside one scale. Even restricted to the patterns that
the construction itself produces, the relaxation gives `0.4007374` at 7 points and `0.4006973` at
8 points, both above `B*`.

So more points alone will not do. A new kind of constraint is needed.

## 2. The idea: a near-optimal law constrains itself

`C` is a supremum, so it is enough to study laws with `P(μ)` close to `C`. Such laws satisfy
inequalities that arbitrary laws do not. Each one comes from the same trick:

> Modify `μ` a little. The modified law is still a law, so it cannot beat `C`.
> Write out what that says about `μ`.

Three modifications are used. Notation: `F(b) = μ[0, b)` is the mass below `b`, and `G(b)` is the
probability of a success in which all four points are below `b`.

### Fact 1: sub-law

    G(b) ≤ C · F(b)⁴

*Why.* Given that all four points fall below `b` (probability `F(b)⁴`), they are four independent
draws from `μ` restricted to `[0, b)`. That restricted law cannot beat `C`.

### Fact 2: substitution

    G(b) + BC(b) ≥ F(b)⁴ · P(μ) - (C - P(μ))

Here `BC(b)` is the probability of a "bad cross": a success whose target is below `b` while one
summand is at or above `b`.

*Why.* Build a new law: keep the part of `μ` above `b`, and replace the part below `b` by a copy of
*all* of `μ` shrunk by a tiny factor `ε`. Its successes include

* all four points in the shrunk copy: probability `F(b)⁴`, and then success has probability `P(μ)`,
  because success does not change when all four numbers are multiplied by `ε`;
* target above `b`: as `ε → 0` the shrunk summands stop mattering, so there are at least as many
  successes as `μ` had with target above `b`.

The new law cannot beat `C`. Subtracting from the decomposition
`P(μ) = G(b) + (successes with target above b) + BC(b)` gives the inequality.

Facts 1 and 2 squeeze `G(b)` from above and below. Together they say: *below any threshold, a
near-optimal law is again near-optimal*. That is exactly the recursion of the construction, now
written as two linear inequalities that involve a single level.

### Fact 3: degree regularity

Let `d(x)` be the probability of success when one of the four positions, chosen at random, is
pinned at the value `x` and the other three are drawn from `μ`. Its average over `x ~ μ` is `P(μ)`.

    d(x) ≤ C + O(√(C - P(μ)))        for every x ≥ 0

*Why.* Mix a small point mass at `x` into `μ`: `ν = (1 - t) μ + t δ_x`. Expanding `P(ν)` and keeping
the terms with at most one copy of `δ_x` gives
`C ≥ P(ν) ≥ (1 - t)⁴ P(μ) + 4t (1 - t)³ d(x)`. Choosing `t = √(C - P(μ))` gives the bound.

So in a near-optimal law no point is better than average, and therefore almost no point is worse.

## 3. Turning the facts into statements about eight points

The facts are about a law and a threshold. To put them in a finite optimisation they must be
expressed through pattern frequencies. Take eight independent points.

**Thresholds (facts 1 and 2).** Use four of the points as *roots* `z0 < z1 < z2 < z3` and the
other four as *fresh* points. From three roots `z_i < z_j < z_k` form

    a = 2 z_j - z_i - z_k,        b = max(z_k, (z_i + z_j + z_k) / 2).

The point of these particular thresholds is that "a fresh point `x` is below `a`" means
`x + z_i + z_k < 2 z_j`, which is again a comparison of three points with twice a fourth. So it can
be read off the pattern, and likewise for `b`. In the extremal construction these thresholds sit at
the two ends of one scale. Since the fresh points are independent of the roots, facts 1 and 2 apply
with the threshold computed from the roots, and their averages are linear expressions in pattern
frequencies. There are 8 thresholds and 2 inequalities for each.

**Degrees (fact 3).** Use one point as root, four others to describe its surroundings (150
classes), and the last three to measure its degree. This gives 2 inequalities per class.

**Squares.** The usual flag term, with one positive semidefinite matrix `Q` of size 300.

Now combine everything. For a pattern `P` and a number `x`:

    Λ_P(x) = objective(P) + ⟨Q, M(P)⟩
           + Σ over classes     (nonnegative multiplier) × (fact 3 in pattern form, at level x)
           + Σ over thresholds  (nonnegative multiplier) × (facts 1 and 2 in pattern form, at level x)

`objective(P)` is the fraction of successes in the pattern, so its average is `P(μ)`. Each bracket
is arranged so that, when `x = C`, its average over a near-optimal law is nonnegative up to an error
that vanishes as `P(μ) → C`. `Λ_P` is affine in `x`. Let

    ψ(x) = max over all patterns P that eight real numbers can produce of Λ_P(x).

## 4. Theorem D

> **Theorem D.** `C ≤ ψ(C)`.

*Proof.* Take laws `μ_n` with `P(μ_n) → C`. They may be assumed to have no atoms, so that eight
draws are distinct and tie-free. Average `Λ_P(C)` over eight independent points from `μ_n`:

* the objective averages to `P(μ_n)`, which tends to `C`;
* the square term averages to a nonnegative number, for every law;
* each bracket averages to a number whose limit is nonnegative, by facts 1 to 3.

So the average is at least `C` in the limit. An average never exceeds the maximum, which is `ψ(C)`. ∎

The theorem holds for every choice of `Q` and of the multipliers. A *certificate* is a choice that
makes `ψ` small.

## 5. From `C ≤ ψ(C)` to `C ≤ B*`

`ψ` is a maximum of affine functions, hence convex. Suppose that

* `C ≤ C̄` for some already known bound `C̄`,
* `ψ(C̄) < C̄`, and
* `ψ(B*) ≤ B*`.

By convexity `ψ(x) < x` for every `x` in `(B*, C̄]`. But `C ≤ ψ(C)` and `C ≤ C̄`, so `C` is not in
that interval. Hence `C ≤ B*`.

Two remarks.

* **The starting bound matters.** Here `C̄ = 0.4007545`, from the 7-point flag bound. For the actual
  certificate `ψ(x) < x` holds only up to about `0.40099`, so the published `0.4167`, or the 6-point
  bound `0.40255`, would not be enough.
* **The strict inequality matters.** There is a trivial choice of multipliers with `Λ_P(x) = x` for
  every pattern. It satisfies `ψ(B*) ≤ B*` and proves nothing. It is excluded because it fails
  `ψ(C̄) < C̄`.

## 6. The inexact match, and how it became exact

The first certificates were found by a floating-point solver and rounded to rational numbers. Each
one improved a known bound, so they were used in a chain: the 7-point bound, then six certificates,
the last of which gave

    C ≤ 0.4006953905 = B* + 1.8·10⁻⁸.

Eight matching digits made `C = B*` very plausible, but it is not a proof, and a rational
certificate cannot do better in principle:

* `B*` is irrational. It lies in the field `Q(r)`, where `r = 0.4743...` is the root of
  `x⁴ - 4x³ - 3x² - 2x + 2` at which `B(p)` is maximal.
* A certificate that proves exactly `B*` must satisfy `Λ_P(B*) = B*`, as an identity, on every
  pattern that the extremal construction produces with positive frequency in the limit. Any slack
  there would leave room above `B*`. For the final certificate there are 138,141 patterns on which
  equality holds.

The exact certificate was obtained in three steps.

1. Coefficients are allowed in `Q(r)`, and the constant in the brackets is `B*` itself. (The
   brackets need a constant that does not exceed `C`. In the written proof this is supplied by the
   lower bound `B* ≤ C`. The Lean proof avoids it: if `C ≤ B*` there is nothing to prove, and
   otherwise `B* < C`.)
2. The directions in which `Q` is forced to vanish are built into its shape: `Q = W Y Wᵀ`, with `W`
   fixed in advance and `Y` free. The forced equalities then hold identically.
3. The remaining forced equations (204 independent ones) are solved exactly in `Q(r)`. Everything
   else is rounded, which is harmless because every pattern that is not tight has slack at least
   `10⁻⁴`, the matrix `Y` is positive definite with room to spare, and no multiplier is near zero.

The result: among the 45,319,744 patterns of the list, `Λ_P(B*) < B*` on 45,181,360, equality on
138,141, and the remaining 243 violate the inequality but provably cannot be produced by eight real
numbers. At `C̄` the strict inequality holds with margin `1.2·10⁻⁵`.

## 7. What is proved how

| Step | Where | How it is checked |
|---|---|---|
| Facts 1–3, Theorem D, the criterion of section 5 | `BeatAvg/Sublaw`, `Substitution`, `Degree`, `Main` | Lean kernel, no computation |
| Laws without atoms suffice; averages of pattern functions | `BeatAvg/Atomless`, `Expect`, `ExpectDeg` | Lean kernel |
| The list contains every pattern of eight real numbers | `BeatAvg/Cert/Levels`, `CoverSound` | Lean kernel, given the compiled enumeration |
| `Q` positive semidefinite, multipliers nonnegative | `BeatAvg/Cert/Static8` | Lean kernel, by evaluation |
| `Λ_P(B*) ≤ B*` and `Λ_P(C̄) < C̄` on all patterns | `BeatAvg/Cert/Native8` (`main8`) | compiled code (`native_decide`) |
| `C ≤ C̄` (7 points) | `BeatAvg/Cert/Native7` (`check7_ok`) | compiled code (`native_decide`) |
| `B* ≤ C` | `BeatAvg/Lower` | Lean kernel |

In one sentence: the flag method fails by a hair because it cannot see the recursion; facts 1 and 2
state the recursion as an inequality at a single level; and convexity of `ψ` turns "the bound
improves itself" into "the bound is `B*`".
