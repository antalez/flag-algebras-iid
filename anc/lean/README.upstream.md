# Lean formalisation of `C = B*`

Lean 4.34.1, Mathlib v4.34.1.

## Statement

    theorem BeatAvg.C_le_Bstar : C ≤ Bstar          -- BeatAvg/Cert/Final.lean
    theorem BeatAvg.Bstar_le_C : Bstar ≤ C          -- BeatAvg/Lower/Main.lean
    theorem BeatAvg.C_eq_Bstar : C = Bstar          -- BeatAvg/Cert/Final.lean
    theorem BeatAvg.K8.C_eq_Bstar_kernel : C = Bstar   -- BeatAvg/K8/Final.lean, no native_decide

* `C` (`BeatAvg/Defs.lean`) is the supremum of `P μ = μ⁴ {x | x 0 + x 1 + x 2 < 2 * x 3}` over Borel
  probability measures `μ` on `ℝ` with `μ (Iio 0) = 0`.
* `Bstar = (r³ - 6r² + 6r)/4` (`BeatAvg/Cert/KReal.lean`), where `r` is the root of
  `x⁴ - 4x³ - 3x² - 2x + 2` in `[0, 1]`. `BeatAvg/Cert/BstarFacts.lean` proves that this root is
  unique, that `Bstar = r(2 - r)/(1 + r + r² + r³)`, and `0.40069537 < Bstar < 0.40069538`.

An informal account of the upper bound (why the flag method stops short, Theorem D, the exact
certificate) is in `THEOREM_D_EXPLAINED.md`.

The upper bound and the lower bound are independent of each other. The lower bound depends only on
the three standard axioms. The upper bound of `C_eq_Bstar`, and therefore the equality, also
depends on one `native_decide` (section "What the upper bound rests on"). `C_eq_Bstar_kernel` is
the same statement with the three standard axioms only (section "The proof with no
`native_decide`"); it costs about twelve times more computation and is not part of `lake build`.

## The lower bound

`Bstar_le_C` follows from `BeatAvg.lower_bound : p (2 - p) / (1 + p + p² + p³) ≤ C` for `0 < p < 1`,
which is the Proposition "Lower bound" of Bellec and Fritz (`starting_point/optimizing_iid.tex`),
with their law `ν = p δ_0 + (1 - p)/N ∑_{i ≤ N} δ_{1 - 2^{-i}}` and their three families of events.
The formal proof differs from the written one in three places:

* The paper builds `Y = ∑_j η^{j-1} X_j` and uses that `Y = X + η Y'` with `Y'` distributed like
  `Y`. The Lean proof does one step, `X + η Y'` with `Y'` of an arbitrary law `lam`, proves
  `P(law of X + η Y') ≥ p⁴ P(lam) + E[Ff] - 4δ` (`Lower.one_step`), and takes the supremum over
  `lam` on both sides: `C ≥ p⁴ C + E[Ff]` (`C_ge_step`). No infinite product is needed.
* Since `lam` need not be bounded, `η` is chosen after a level `A` with `lam [0, A] ≥ 1 - δ`; the
  margin `2^{-N}` of the events absorbs `3 η A`.
* For one summand at `0`, the paper counts distinct triples and uses symmetry. Here the event
  "another summand is below the target" is split by the value of the target, which gives
  `E[Ff] = p³(1-p) + 3p²(1-p)² + 3p(1-p)³ (N-1)(4N+1)/(6N²)` exactly (`Lower.int_Ff`).

| File | Content |
|---|---|
| `Lower/Grid` | the law of the index of the atom; integrals against it and its fourth power |
| `Lower/Count` | the events as products of indicators (`Ff`); they imply the inequality with margin `2^{-N}`; `E[Ff]` |
| `Lower/Construct` | the law of `X + η Y'`; the indicator inequality; `one_step` |
| `Lower/Main` | `C_ge_step`, `lower_bound`, `Bstar_le_C` |

## A weaker upper bound with no `native_decide`

    theorem BeatAvg.C_le_six : C ≤ 201272564718335614989 / 500000000000000000000   -- Six/Main.lean
    theorem BeatAvg.C_le_40255 : C ≤ 40255 / 100000

This is the six-point flag certificate of `starting_point/cert_6_json.txt` (bound `0.402545129...`),
with only the three standard axioms: the kernel runs both finite parts. It is independent of the
proof of `C = B*`, which uses no flag bound of lower order.

| File | Content | Kernel time |
|---|---|---|
| `Six/Data` (generated) | patterns of five and six points, certificates of non-realizability, flags and integer rows of the certificate | |
| `Six/Cover` | a search over the trits of the 15 quadruples, abandoned when five of the points get a pattern outside the list of 30; its result is the list of 1,290 patterns (`cover6`) | 7 minutes, 81 GB |
| `Six/Eval` | list-based evaluation of the certificate on a pattern (`eval6`) | |
| `Six/Sound` | `flag_bound` for the three families; `eval6` bounds the functional on sorted samples | |
| `Six/Chk/P00..P42`, `Six/Checks` (generated) | `eval6` on the 1,290 patterns, 30 per module | 3.5 minutes and 33 GB per module |
| `Six/Main` | `C_le_six` | |

`lake build BeatAvg.Six.Main` takes 8 minutes of wall time on 192 threads and 2.7 CPU-hours, about
6 seconds per pattern. `data/gen_six.py` writes `Six/Data.lean`, `Six/Chk/*` and `Six/Checks.lean`.

## What the upper bound rests on

`C_le_Bstar` depends on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on
1 use of `native_decide` (no `sorry`): a finite computation is run as compiled code and its result
is accepted by the kernel without being re-checked. This adds trust in the Lean compiler and runtime.
The computation is in `Cert/Native8.lean`:

| Theorem | What is computed | Time |
|---|---|---|
| `main8` | the two order-8 inequalities, at `B*` and at `1`, on the 45,319,744 patterns of the cover | 90 minutes on 192 threads (about 280 CPU-hours) |

The two-point criterion needs an upper bound `Cbar0` of `C` at which the certificate is strictly
below the diagonal. The certificate used here (`results/order8_exact/cert8_exact_cbar1.json`) has
this property at `Cbar0 = 1`, with margin `10⁻⁵` in the check, so the bound used is the trivial
`C ≤ 1` (`BeatAvg.C_le_one`). An earlier certificate had it only below `0.40099` and needed the
order-7 flag bound `C ≤ 0.4007545`. That bound (`C_le_order7`, `Cert/Main7.lean`, with a second
`native_decide`, `check7_ok`) is still built, but `C_le_Bstar` no longer depends on it.

Everything else is checked by the kernel: Theorem D and the two-point criterion, the flag bound, the
reduction from samples to patterns, the completeness of the pattern enumeration, the soundness of the
certificates of non-realizability, the soundness of the check above, and the static properties
of the order-8 certificate (`Y` positive semidefinite, multipliers in `[0, 100]`, integrality of the
scaled tables, enclosure of `r`).

Earlier versions used 67 `native_decide`. One went with the order-7 bound (above). The 65 others:

* 50 counting facts about the `8!` and `7!` orderings. They are replaced by a theorem
  (`Cert/Transversal.lean`: a function that is invariant under reordering inside disjoint blocks of
  sizes `k₁, k₂, k₃` sums to `k₁! k₂! k₃!` times its sum over the orderings that increase on each
  block) and by facts about the concrete lists of orderings used by the checker (no repetition,
  length, injective and increasing on the blocks), which the kernel checks by evaluation
  (`decide +kernel` in `Cert/IndexFacts.lean`, 18 minutes, and `Cert/Idx7.lean`, 5 minutes).
* 5 injectivity facts: `decide`.
* 2 index tables (`idx8_spec`, `idx7_spec`): proved.
* 2 constants (`cbar8`, `bound7_ok`): the checkers now use the literals `801509/2000000`.
* 4 consistency checks of the enumeration levels (`ok5`–`ok8`): they stated that the program
  `Fast.mkLevel` builds a level meeting its specification, which is now proved for every input
  (`Cert/LevelProof.lean`); the only finite fact left, that every quadruple of `n ≤ 8` points misses
  one of the points, is checked by the kernel.
* 1 shape check of the order-7 certificate (`static7_ok`): not needed. The Gram form is positive
  semidefinite for any block assignment, and the flag theory no longer assumes a positive number of
  flags (`Cert/FlagGen.lean`, `Cert/Order7.lean`).
* 1 static check of the order-8 certificate (`static8`): evaluated by the kernel
  (`Cert/Static8.lean`). For this the certificate is given as Lean numerals instead of a text file
  parsed at run time (`Fast/Cert8Data.lean`), `Y` is stored by rows and `G` by columns as lists, and
  the checks are structurally recursive and stated row by row: `Y` symmetric, each row of
  `Y - GᵀG/4^80` diagonally dominant, each row of `Dn · W Y Wᵀ` integral. The rows are distributed
  over 50 modules (`Cert/S8/*`), which lake builds in parallel: 13 minutes of wall time, about
  4 CPU-hours, 30 to 40 GB of memory per module. The same checks take 9 seconds as compiled code.

## The proof with no `native_decide`

    theorem BeatAvg.K8.C_eq_Bstar_kernel : C = Bstar      -- BeatAvg/K8/Final.lean
    'BeatAvg.K8.C_eq_Bstar_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]

The finite check of `main8` is replaced by kernel evaluation, split into 152,434 modules of one
declaration each. `BeatAvg/K8/Main8K.lean` proves `C ≤ B*` from a structure `Facts` of finite
statements with the standard axioms; the generated modules `BeatAvg/K8/F/**` (tables and levels)
and `BeatAvg/K8/P8/**` (the order-8 check, one piece per module) prove them by `decide +kernel`.
The search over patterns uses a trie per stage (`Search`, `TrieSound`); the functional is
evaluated on patterns packed into large numbers (`Eval`, `EvalF` and their soundness proofs).

| | `C_eq_Bstar` | `C_eq_Bstar_kernel` |
|---|---|---|
| Axioms | standard and `main8` | standard |
| Wall time on 192 threads (2 × AMD EPYC 7643), 2 TB RAM | 92 minutes | 18.8 hours, after 63 minutes of lake stages |
| CPU time | 285 CPU-hours | 3,480 CPU-hours |
| Largest module | 81 GB (`Six/Cover`) | 26 GB per order-8 piece, 57 GB for one table check |

The generated files are not under version control: they are in the separate archive made by
`repro/make_kernel_bundle.py`, and the generators in `gen/` reproduce them. `repro/KERNEL.md` has
the commands; the build goes through `gen/run_k8.py`, which bounds the number of parallel jobs and
their memory (`lake build BeatAvg.K8.Final` would start all modules at once).

## Kernel evaluation: what was measured

* `decide +kernel` (the kernel evaluates the `Decidable` instance; no axiom) did the full product
  `GᵀG` on lists of 85-bit integers (255³ = 16.6 million multiply-and-add steps) in 14 minutes,
  about 20,000 steps per second. Natural-number arithmetic is done by GMP inside the
  kernel, so the size of the numbers matters little; the cost is the traversal of the data.
* The kernel has no arrays: `a[i]` on a literal walks a list. Random access, hash maps, string
  parsing and functions defined by well-founded recursion (`List.mergeSort`, `Array` loops) are
  either very slow or do not reduce. Kernel-friendly code is structural recursion on lists.
* The kernel caches every intermediate result of one declaration, so memory grows with the length
  of the computation (10 GB per minute here). Splitting a check into many theorems bounds it.
* `decide_cbv` (Lean 4.34; evaluation by rewriting, with proof terms, standard axioms only) was
  12 times slower than the kernel on the same product. Its advantage is that it also evaluates
  functions defined by well-founded recursion. It was not needed.
* `norm_num`, `simp` and the matrix tactics of Mathlib build one proof step per arithmetic
  operation and are meant for small matrices. `bv_decide` relies on compiled code, like
  `native_decide`.

## Structure

**Analysis (Mathlib only).**

| File | Content |
|---|---|
| `PiLemmas`, `Defs`, `Bounded` | product measures; `P`, `C`; bounded measurable functions; general position holds almost surely |
| `Sublaw`, `Substitution`, `Degree`, `Atomless` | Lemmas 2.1, 3.1, 4.1/4.2, 1.1 of `results/theorem_D_proof.md` |
| `Sample`, `Expect`, `ExpectDeg`, `Main` | the eight-point functional `Lam`; **`C_le_of_certificate`**: Theorem D with the two-point criterion |
| `Cert/FlagGen`, `FlagGen2`, `FlagBound` | **`flag_bound`**: the flag bound for any list of square families on `n` points |

**Computable part (`Fast/`, no Mathlib, compiled to native code).** Arithmetic in `Q(r)` and `Z[r]`,
patterns and configurations, canonical orderings, the evaluation of the functional in integers, the
enumeration of patterns by joins, the checker of non-realizability certificates, the order-8
certificate as numerals (`Cert8Data`), parsers for the other data files, the checks themselves.

**Soundness of the computable part (`BeatAvg/Cert/`).**

| File | Content |
|---|---|
| `KReal`, `KSign` | `r`, evaluation `Q(r) → ℝ`, certified enclosure and signs |
| `Sort`, `CfgReal`, `MkD`, `Tab` | measurable sorting; the configuration of a tuple; certificate data from tables |
| `Thr*`, `ObjTerm`, `DegTerm`, `DegInv`, `SqTerm` | each term of the functional on a sorted sample, and its invariances |
| `Transversal`, `IndexFacts`, `Invariance`, `Assemble`, `Sorted` | `Lam_sorted`: on a sorted sample the functional is a sum over block-increasing orderings |
| `EvalZ`, `CheckSound` | the integer evaluation computes the functional; the per-pattern checks are sound |
| `PsdSound`, `PsdMain`, `QPsd`, `CertValid` | `Q = W Y Wᵀ` is positive semidefinite; the certificate data are valid |
| `PatReal`, `PatSb`, `PatSbG`, `Combos` | patterns of sorted samples |
| `Abel`, `FarkasSound` | a valid certificate of non-realizability contradicts realizability |
| `CoverSpec`, `LevelProof`, `CoverSound`, `Levels` | the pattern of every sorted sample is a leaf of the enumeration |
| `Native8` | the `native_decide` of the order-8 check |
| `S8/*`, `Static8` | the static checks of the order-8 certificate, by kernel evaluation |
| `Order8`, `Main8` | order 8: `C ≤ B*` |
| `FamSum`, `SortedN`, `Idx7`, `GramBlock`, `Order7`, `Order7b`, `Native7`, `Main7` | order 7: `C ≤ 0.4007545` (not used by `C ≤ B*`) |
| `Final` | `C ≤ B*` |

**The proof with no `native_decide` (`BeatAvg/K8/`).**

| File | Content |
|---|---|
| `Search`, `Bits`, `SearchSound`, `TrieSound` | patterns of `n` points in nested order, packed two bits per trit; the search by joins, with a trie per stage; its completeness |
| `Eval`, `Hot`, `Fields`, `Atoms`, `Flags`, `Acc`, `EvalSound` | the functional on a packed pattern (one-hot form, packed tables, sums of packed fields); equal to `LamR` |
| `EvalF`, `EvalFSound` | the same evaluation specialised to a pattern of seven points; equal to the first |
| `Excl`, `FarkasK`, `LevelK`, `Check7K`, `Level7Sound` | certificates of non-realizability; levels 5, 6 and 7 from the kernel checks |
| `TbSpec`, `Tb`, `TbF` | the checks of the packed tables against the certificate |
| `Check8K`, `Combine`, `Main8K`, `Final` | the order-8 pieces, their combination, `C_le_Bstar_of_facts`, `C_eq_Bstar_kernel` |
| `Tables`, `TablesQ`, `TablesF`, `L56`, `L7G`, `L7X`, `F/**`, `P8/**` (generated, `gen/`) | the packed tables, the levels, and the modules checked by the kernel |

**Data (`data/`).** `cert8.txt` (the certificate of `results/order8_exact/cert8_exact_cbar1.json` with a
rational factor of `Y`, an enclosure of `r` and a common denominator), `cert7.txt` (the certificate of
`results/order7/cert7_full.json`), `farkas.txt` (210,600 certificates of non-realizability). They are
produced by `indep_check/export_lean.py`, `export_cert7.py` and `export_farkas.py`. `cert7.txt` and
`farkas.txt` are read by `Fast` at run time. `cert8.txt` is not read by Lean: `data/gen_cert8_data.py`
turns it into `Fast/Cert8Data.lean`, and `data/gen_static8.py` writes `Cert/S8/*` and
`Cert/Static8.lean`. Wrong data cannot make the theorem false: the checks would fail.

## Building

    # with elan's `lake` on the PATH
    lake build                      # about 95 minutes on 192 threads, dominated by Cert/Native8
    lake env lean Check.lean        # statement and axioms

Mathlib was fetched on the host with `lake update` and `lake exe cache get`. Any change in `Fast/`
makes lake rebuild every module that depends on it, including `Native8`. Changes in `BeatAvg/` do
not: `Native8`, `Native7`, `Static8` and `S8/*` import only `Fast`. The kernel evaluations need
memory: 30 to 40 GB for each of the 50 modules `S8/*`, which lake builds in parallel.

## Reproducing everything

`repro/` holds short notes with the commands that recompute the certificates, export them to the
files of `data/`, and regenerate the generated Lean files; `repro/KERNEL.md` covers the proof with
no `native_decide`.

