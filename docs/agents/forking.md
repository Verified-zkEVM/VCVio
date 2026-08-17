# Forking Lemmas

Three forking lemmas live in this repository. They differ in what gets pre-sampled and in the
shape of the bound they deliver. See [crypto.md](crypto.md) for the surrounding primitive and
reduction machinery.

## Which one to reach for

| | Pre-samples | Bound shape | File |
|---|---|---|---|
| **Seeded** (Bellare–Neven) | every oracle answer, into a `QuerySeed` | `acc²/q − acc/h` | [`VCVio/CryptoFoundations/SeededFork.lean`](../../VCVio/CryptoFoundations/SeededFork.lean) |
| **Replay** (cursor-native) | only the forked oracle family | `acc²/q − acc/h` | [`VCVio/CryptoFoundations/ReplayFork.lean`](../../VCVio/CryptoFoundations/ReplayFork.lean) |
| **Coordinate-wise** | the whole acceptance table | `ε − ℓ(k−1)/N` | [`VCVio/CryptoFoundations/CoordinateFork.lean`](../../VCVio/CryptoFoundations/CoordinateFork.lean) |

Seeded and replay share a generic core in
[`VCVio/OracleComp/Constructions/Fork.lean`](../../VCVio/OracleComp/Constructions/Fork.lean): the
conditional-square step, the fact that completing a retained occurrence resamples the focused
answer as a fresh query, and the collision bound on the two focused answers. Both end in
`ENNReal.mul_tsub_inv_le_sum_sq_sub_div` from
[`ToMathlib/Data/ENNReal/SumSquares.lean`](../../ToMathlib/Data/ENNReal/SumSquares.lean).

**The coordinate-wise lemma uses none of that.** Its bound is *linear* in the accepting
probability, not quadratic, because the extractor of Fenzi–Moghaddas–Nguyen (eprint 2023/846 §7)
spends an *expected* rather than a fixed number of queries. No Cauchy–Schwarz step appears, and
nothing from `SumSquares` is used. If you are looking for a Jensen-style estimate in that
development, there isn't one and there shouldn't be.

## Quadratic forks: seeded vs replay

The distinction is what gets pre-sampled. Seeding is uniform — it pre-samples *every* oracle family
within the budget, which is clean when the adversary talks only to the forked oracle and awkward
when it also consumes ambient randomness. Replay pre-samples only the forked family and answers
ambient randomness live, which is the shape of a Fiat–Shamir EUF-CMA adversary (hash queries are
the forked family; signing queries are ambient randomness through the simulator). Hence the
Fiat–Shamir consumer in
[`VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean)
uses replay. A Hoare-triple wrapper for the seeded form is in
[`VCVio/ProgramLogic/SeededFork.lean`](../../VCVio/ProgramLogic/SeededFork.lean).

Replay's shared prefix is intrinsic: `PFunctor.FreeM.Cursor.ForkView` bundles one occurrence
context with two completions, so the prefix cannot drift — it is a field of the type both
completions are indexed by. Its one side condition, `PathCfReachable`, says that whenever the
selector fires it names a query the run actually made.

## Coordinate-wise forking

The setting is a challenge *vector* `c : ι → S` rather than a single challenge. A set of challenges
is coordinate-wise `k`-special sound when some central vector has, in every coordinate, `k − 1`
neighbours differing from it in that coordinate and only there — and the set has exactly
`ℓ(k−1)+1` members. That is `SS(S, ℓ, k)` of the paper, formalized in
[`ToMathlib/Combinatorics/CoordinateWise.lean`](../../ToMathlib/Combinatorics/CoordinateWise.lean):

```lean
def IsCoordSpecialSound (k : ℕ) (X : Finset (ι → S)) : Prop :=
  HasCoordNeighbours k X ∧ X.card = Fintype.card ι * (k - 1) + 1
```

The cardinality is not an extra assumption pulling its weight: `le_card_of_hasCoordNeighbours`
shows the neighbour condition already forces it as a lower bound, because a vector differing from
the centre in only one coordinate determines that coordinate.

### The organizing idea: acceptance tables

The extractor samples `c₀`, checks it accepts, then resamples each coordinate until `k − 1` further
accepting values are found. **Whether it succeeds does not depend on the order it tries them** — it
succeeds exactly when `c₀` accepts and every column of `c₀` holds at least `k` accepting values.
Success is therefore a deterministic predicate on `c₀` given the *acceptance table*
`ρ : (ι → S) → Bool`, and the whole probabilistic content collapses to a counting inequality
(`sub_div_le_div_card_filter`) with no probability monad in sight.

A randomized adversary is then a distribution over tables, and
[`VCVio/EvalDist/CoordinateFork.lean`](../../VCVio/EvalDist/CoordinateFork.lean) averages the
counting bound over an *arbitrary* such distribution:

```lean
theorem sub_div_le_tsum_probOutput_mul_goodSet [Nonempty S] (D : m ((ι → S) → Bool)) (k : ℕ)
    (hmass : Pr[⊥ | D] = 0) :
    acceptRatio D - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S ≤ forkSuccOf k D
```

Only the marginals of `D` appear on the left, so no independence hypothesis is needed. Note the
converse is *not* true: `forkSuccOf k D` depends on all of `D`, so choosing a particular coupling —
as the multi-round layer does, by instantiating at an independent Bernoulli table from
[`ToMathlib/Probability/BernoulliTable.lean`](../../ToMathlib/Probability/BernoulliTable.lean) — is
a modelling decision about the extractor's randomness, not a theorem.

### Transcripts

The core is `Bool`-valued, but the paper's extractor outputs *pairs* `(cᵢ, yᵢ)`. That is a layer on
top rather than a generalization: a response table `τ : (ι → S) → Y` and a verifier
`V : (ι → S) → Y → Bool` induce the acceptance table `fun c => V c (τ c)`, so `coordForkT` is
`coordFork` composed with `acceptTable`, `coordFork_acceptTable` exhibits the two as the same
computation up to relabelling, and `sub_div_le_probEvent_goodTranscripts_coordForkT` carries the
bound over to `GoodTranscripts` — `ℓ(k-1)+1` accepting transcripts whose challenges are
`SS(S, ℓ, k)`. The `ToMathlib` counting core never sees `Y`.

### What is and is not proved

Each paper lemma is a three-conjunct existential over *an oracle algorithm with oracle access to
the adversary*. The status is:

| Clause | Lemma 7.1 | Lemma 7.2 |
|---|---|---|
| expected query count | **not proved** | **not proved** |
| success probability | proved | proved |
| output structure (accepting transcripts) | proved | `μ = 1` only |

- `sub_div_le_probEvent_goodOutput_coordFork` carries the success bound and the output guarantee
  together, so it is sensitive to what the extractor returns.
- `sub_le_multiSucc` in
  [`VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean`](../../VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean)
  gives the `μ`-round bound `ε − μℓ(k−1)/N`, pinned to the extractor by
  `forkSucc_eq_probEvent_isSome_coordFork`.
- The object consumes a pre-sampled acceptance table rather than querying an adversary, so what is
  established is the information-theoretic content, not efficiency.
  [`ToMathlib/Probability/NegativeHypergeometric.lean`](../../ToMathlib/Probability/NegativeHypergeometric.lean)
  is the groundwork for the deferred query count, and
  [`ToMathlib/Combinatorics/ChallengeTree.lean`](../../ToMathlib/Combinatorics/ChallengeTree.lean)
  for the deferred multi-round output.

Non-vacuity and payload-sensitivity checks live in
`VCVioTest/Forking/CoordinateFork.lean` and run in CI.

## Rewinding primitives

Two distinct notions, easy to conflate:

- **By position** — go back to the `n`-th query to an oracle, change that answer, and keep every
  later answer. That is `PFunctor.Supply.setAt` in
  [`ToPolyFun/PFunctor/Supply.lean`](../../ToPolyFun/PFunctor/Supply.lean), instantiated as
  `OracleSpec.QuerySeed.setAtIndex`. Contrast `takeAtIndex`, which *truncates*, so a rerun draws
  fresh answers past the cut; `setAt_eq_addValues_drop` exhibits the restored tail as exactly what
  truncation throws away.
- **By value** — re-run on a different input. This is what coordinate-wise forking does
  (`Function.update c j x` on the challenge vector), and it needs no seed machinery at all.

Reaching for a seed when the resampling is by value is the most common way to over-engineer one of
these developments.
