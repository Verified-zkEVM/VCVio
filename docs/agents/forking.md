# Forking Lemmas

Three forking developments live in this repository. They differ in what gets pre-sampled and in
the shape of the bound they deliver. The coordinate-wise development is currently a table model,
not the paper's oracle extractor. See [crypto.md](crypto.md) for the surrounding primitive and
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

**The coordinate-wise table bound uses none of that.** Its loss is subtracted from the accepting
probability rather than from a quadratic expression. No Cauchy–Schwarz step and nothing from
`SumSquares` is used. Fenzi–Moghaddas–Nguyen (eprint 2023/846 §7) obtain this shape with an
expected-query oracle extractor; the present formalization proves the corresponding table-counting
inequality, not that algorithm or its expected cost.

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

The local computation samples an entire table and `c₀`, then selects `k − 1` accepting neighbours
per coordinate. It succeeds exactly when `c₀` accepts and every column of `c₀` holds at least `k`
accepting values. Success is therefore a deterministic predicate on `c₀` given the *acceptance table*
`ρ : (ι → S) → Bool`, and the table-model probability calculation collapses to a counting inequality
(`sub_div_le_div_card_filter`) with no probability monad in sight.

In this model, randomized behavior is represented by a distribution over complete tables, and
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

### Fixed-statement extraction

[`VCVio/CryptoFoundations/CoordinateFork/SpecialSoundness.lean`](../../VCVio/CryptoFoundations/CoordinateFork/SpecialSoundness.lean)
states the fixed-statement, extensional clause of Definition 2.29 against a `SigmaProtocol` whose
challenge type is `ι → S`:

```lean
def CoordSpeciallySoundAt (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) : Prop :=
  ∀ pc T, (∀ p ∈ T, σ.verify x pc p.1 p.2 = true) →
    IsCoordSpecialSound k (T.image Prod.fst) → ∀ w ∈ support (ext x pc T), rel x w = true
```

The extractor is a **parameter**, not a field: `SigmaProtocol.extract` is hardwired to arity two, so
a `k`-ary extractor cannot be one. `HVZK` takes `simTranscript` as a parameter for the same reason.
`coordSpeciallySoundAt_two_of_speciallySoundAt` is the bridge back for extractors that do factor
through a pair.

[`CoordinateFork/Extraction.lean`](../../VCVio/CryptoFoundations/CoordinateFork/Extraction.lean)
composes that with the table fork to prove the fixed-statement extraction-success inequality used
in **Lemma 2.31 at `μ = 1`**: `coordExtract` runs against the prover's response table, hands the
accepting transcripts to `ext`, and
`sub_div_le_probEvent_extracted_coordExtract` bounds the probability of the event
`Extracted rel x` — *a valid witness was returned* — below by `ε - ℓ(k-1)/|S|`. Aborting runs fail
that event, so it is not a termination bound. A full Definition 2.28/2.31 result would additionally
need the security-parameter experiment, the joint bad event, an oracle implementation, and an
expected-polynomial-time proof.

### What is and is not proved

Each paper lemma is a three-conjunct existential over *an oracle algorithm with oracle access to
the adversary*. The status is:

| Clause | Lemma 7.1 | Lemma 7.2 |
|---|---|---|
| expected query count | **not proved** | **not proved** |
| success probability | **table model only** | **analytic recurrence only** |
| output structure (accepting transcripts) | **table model only** | `μ = 1` only |

- `sub_div_le_probEvent_goodOutput_coordFork` carries the success bound and the output guarantee
  together, so it is sensitive to what the extractor returns.
- `sub_le_multiSucc` in
  [`VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean`](../../VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean)
  proves a recurrence with the numeric bound `ε − μℓ(k−1)/N`. `multiSucc` is not a computation;
  `forkSucc_eq_probEvent_isSome_coordFork` only identifies one recurrence step when an entire
  independent Bernoulli table distribution is supplied.
- The object consumes a pre-sampled acceptance table rather than querying an adversary, so what is
  established is a table-model inequality, not the oracle algorithm or efficiency. A future query
  proof must model sampling without replacement, including exhaustion when fewer than `k`
  accepting values exist, and connect that costed process to the table event. The challenge-only
  [`ToMathlib/Combinatorics/ChallengeTree.lean`](../../ToMathlib/Combinatorics/ChallengeTree.lean)
  supplies only the combinatorial projection needed by a future multi-round output theorem.

Non-vacuity, payload-sensitivity, coupling, boundary, and bad-extractor checks live in
`VCVioTest/Forking/CoordinateFork.lean` and
`VCVioTest/Forking/CoordSpecialSoundness.lean`; both run in CI.

## Why §7 introduces its own extractor

Coordinate-wise `k`-special soundness is a special case of Attema–Fehr–Rambaud's `Γ`-out-of-`C`
special soundness. Their Lemma 5 gives the generic extractor an expected-query upper bound
`2 * tᵧ - 1`. The local formalization proves that the relevant `tᵧ` can be exponential, so plugging
it into that published upper bound does not certify polynomial complexity:
[`ToMathlib/Combinatorics/MonotoneStructure.lean`](../../ToMathlib/Combinatorics/MonotoneStructure.lean)
formalizes the bound:

```lean
theorem pow_add_one_le_tValue [Nontrivial S] [Nonempty ι] :
    Fintype.card S ^ (Fintype.card ι - 1) + 1 ≤ tValue (coordStructure 2) (∅ : Finset (ι → S))
```

The argument is pure `Finset` combinatorics with no probability: the slice of challenges fixing one
coordinate contains no `SS(S, ℓ, 2)` set, because two challenges differing only in that coordinate
cannot both lie in it — but adjoining a single challenge off the slice creates one. So every
untaken slice element stays useful, and then one element off the slice is useful again. This is not
a lower bound on the extractor's actual running time. Neither the generic extractor nor its cost is
formalized here.

## Deferred oracle semantics

The table proof changes a challenge vector by value (`Function.update c j x`). The paper's
extractor instead needs an operational account of rerunning a prover, fixing a prefix, and varying
the selected challenge while preserving the appropriate surrounding randomness. No positional
rewind primitive in this PR is consumed by the proofs, so that machinery is deliberately deferred
until a concrete costed extractor specifies exactly which state must be retained.
