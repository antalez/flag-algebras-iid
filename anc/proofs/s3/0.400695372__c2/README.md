# A four-point certificate for C = C_BF

C = sup P(X1+X2+X3 < 2X4) over laws on [0, inf), X iid.

C_BF = (r^3-6r^2+6r)/4 = 0.40069537232930136..., where r in (0,1) is the root of r^4-4r^3-3r^2-2r+2.

This folder holds an exact flag-algebra certificate on **four** sample points that proves C <= C_BF. With the construction of Bellec and Fritz, this gives C = C_BF. It uses no Theorem D terms.

## The idea: ratio colours (Pierre's, from `graph_experiment/`)

A pattern of four sorted points x1 < x2 < x3 < x4 records two things:
- the additive comparisons x1+x2+x3 < 2x4 and x1+x2+x4 < 2x3, which are the only ones that can hold;
- for every pair i < j and every cutoff q in {7/6, 3/2, 2}, whether x_j < q x_i.

The objective is (number of wins)/4. The flags are the family (t,f) = (2,3), with one block per colour of the root pair.

Why so few points suffice: in the Bellec-Fritz construction, points on the same scale have ratio below 2 and points on different scales have huge ratios. So the colours let three-point flags see the multiscale structure.

## The certificate

- **Cover** (`cover_n4.json`): 259 retained patterns and 871 excluded prefixes, each excluded with exact rational Gordan weights. The program checks that these partition the full 2^20 sign space.
- **Gram matrices** (`cert_exact.json`): Q = W Y W^T over Q(r). There are four blocks, with face dimensions 9, 13, 14 and 8.
- **Result**: every pattern satisfies obj(P) + sum <Q, M(P)> <= C_BF exactly. 57 patterns are exactly tight; every other pattern has slack at least 0.0224.

## Verify

These run in under a second.

    python3 verify.py cover_n4.json cert_exact.json      # standard library only (run without -O)
    python3 redteam.py                                    # corrupted certificates must be rejected
    cd independent && python3 verify_indep.py             # second verifier, written separately; needs numpy for one cross-check

`cert_stage2.json` is a purely rational certificate giving C <= C_BF + 8.2e-10.

## Independence

The certificate was found by an SDP search with exact facial reduction. The two verifiers were written separately; the second was written from the definitions without reading the first or the search code. Both recompute obj and M(P) from the patterns, check positive definiteness exactly, and decide signs in Q(r) with a rational enclosure of r.

The second verifier also checks:
- that the 871 exclusions are valid;
- that its own exact enumeration finds exactly the same 259 realizable patterns.

It also includes a Monte Carlo check: under ordinary laws the flag term averages positive; under the Bellec-Fritz construction it averages to about 0, and the win rate approaches C_BF. Its logs are in `independent/`.

## Status

The certificate has also been formalized in Lean 4: `BeatAvg.Four.C_eq_Bstar`
proves equality using kernel-only finite checks and the existing lower
construction. Its axiom audit contains only `propext`, `Classical.choice`,
and `Quot.sound`. See `../../../lean/BeatAvg/Four/README.md` for reproduction.
The certificate was verified twice in Python (AI-assisted, Claude); human
review of the mathematical presentation is still useful. The mathematical steps used are:
- the flag positivity lemma (Lemma 2.2 of the paper, with ratio comparisons as extra linear forms);
- the reduction to atomless laws by X + eps U and Fatou.
