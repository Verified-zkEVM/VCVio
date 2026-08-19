# Forking Lemmas

Three forking developments live in this repository. They differ in what gets pre-sampled and in
the shape of the bound they deliver. The coordinate-wise development is a table model with a
realizability bridge to ordinary adversaries; it is not the paper's *costed* oracle extractor. See
[crypto.md](crypto.md) for the surrounding primitive and reduction machinery.

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
expected-query oracle extractor; the present formalization proves the corresponding counting
inequality and transfers it to an adversary, but not that algorithm's expected cost.

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

`coordExtractCommit` averages that over the prover's first message: the prover samples a pair
`(pc, τ)` — a commitment together with the response table its now-fixed coins commit it to — and
`sub_div_le_probEvent_extracted_coordExtractCommit` gives the same bound with `ε` read off the
whole experiment (`verifyProb`). The loss is unchanged, because averaging a pointwise bound over
the first message costs nothing.

### Realizing a table by an adversary

[`CoordinateFork/Realizability.lean`](../../VCVio/CryptoFoundations/CoordinateFork/Realizability.lean)
closes the gap between "a distribution of response tables" and "an adversary". For
`A : (ι → S) → ProbComp Y`, `indepTable A := Fintype.mPi A` runs `A` independently at every
challenge, and

```lean
theorem acceptRatio_acceptTable_indepTable (V) (A) :
    acceptRatio (acceptTable V (indepTable A)) = advSucc V A
```

identifies the accepting ratio the table bound consumes with `ε_V(A)`, the adversary's own success
probability on a uniform challenge. The transfer is cheap precisely because
`le_tsum_probOutput_mul_goodSet` reads only the *marginals* of the table distribution, so realizing
some distribution with the adversary's marginals is all it needs. No side condition appears: a
`ProbComp` never fails (`probFailure_of_liftM_PMF`), so the full-mass hypothesis the general
marginal lemma requires is automatic.

`probOutput_acceptTable_indepTable_eq_bernoulliTable` then computes the *whole* joint law, not just
the marginals, and finds the independent Bernoulli table at the adversary's per-challenge
acceptance probabilities — which is what makes the multi-round coupling realizable.

The independent-product machinery underneath is generic and lives below the crypto layer:
[`VCVio/EvalDist/IndepProduct.lean`](../../VCVio/EvalDist/IndepProduct.lean) gives `Fin.mOfFn` and
`Fintype.mPi` their joint law (`probOutput_mOfFn`, `probEvent_forall_coord_mOfFn`) and coordinate
marginals, and [`ToMathlib/Probability/ProbabilityMassFunction/Pi.lean`](../../ToMathlib/Probability/ProbabilityMassFunction/Pi.lean)
gives the corresponding `PMF.pi`, of which `PMF.bernoulliTable` is now the `Bool`-valued instance.
The marginal is an equality only under a full-mass hypothesis; `probEvent_coord_mOfFn_le` is what
survives without it, and `probEvent_coord_mOfFn_failFactor` in the test file is the negative
control showing the difference is real.

### What is and is not proved

Each paper lemma is a three-conjunct existential over *an oracle algorithm with oracle access to
the adversary*. The status is:

| Clause | Lemma 7.1 | Lemma 7.2 |
|---|---|---|
| expected query count | **not proved** | **not proved** |
| success probability | proved, for the paper's algorithm | analytic recurrence, one step anchored |
| output structure (accepting transcripts) | proved, for the paper's algorithm | `μ = 1` only |

- `sub_div_le_probEvent_goodOutput_coordFork` carries the success bound and the output guarantee
  together, so it is sensitive to what the extractor returns.
- *Fixed-coin adversary* is what
  [`CoordinateFork/Realizability.lean`](../../VCVio/CryptoFoundations/CoordinateFork/Realizability.lean)
  supplies, and it is not a weakening the paper avoids — §7.1's own proof needs it. FMN reason
  about `Xᵢ = |{x ∈ S : V (C x) (A (C x))}|` and use `Pr[V = 1 ∣ Xᵢ = l] = l/N`; both statements
  require `A` to be a *function* of the challenge, i.e. its coins fixed before any challenge is
  drawn. Such an `A` is exactly a response table.
- `sub_le_multiSucc` in
  [`VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean`](../../VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean)
  proves a recurrence with the numeric bound `ε − μℓ(k−1)/N`. `multiSucc` is still not a
  computation, but its single-step bridge is no longer conditional on a distribution nothing
  produces: `forkSucc_eq_probEvent_isSome_coordFork_indepTable` discharges the Bernoulli-table
  hypothesis outright, because the acceptance table an adversary induces *is* that Bernoulli table.
- *For the paper's algorithm* means
  [`CoordinateFork/Operational.lean`](../../VCVio/CryptoFoundations/CoordinateFork/Operational.lean)'s
  `coordForkOp`, which is Figure 11 itself — sample a challenge, and on acceptance resample each
  coordinate without replacement until `k − 1` further accepting values turn up or that coordinate
  is exhausted. See *The resampling loop* below.
- What remains missing is the cost. The analytic ingredient is in place (see *Draw counts* below)
  and `coordForkOp` returns its own lookup count, but nothing yet assembles those into the paper's
  `1 + ℓ(k−1)` bound. The challenge-only
  [`ToMathlib/Combinatorics/ChallengeTree.lean`](../../ToMathlib/Combinatorics/ChallengeTree.lean)
  supplies only the combinatorial projection needed by a future multi-round output theorem.

### The resampling loop

`coordForkCore` in [`CoordinateFork.lean`](../../VCVio/CryptoFoundations/CoordinateFork.lean) is a
*total lookup*: it reads a whole column and keeps the first `k − 1` accepting values in enumeration
order. That is not what Figure 11 does. `coordForkOp` is:

```lean
noncomputable def coordForkOpAt (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    ProbComp (Option (Finset (ι → S)) × ℕ) :=
  if ρ c₀ then do
    let d ← Fintype.mPi (coordDraws k ρ c₀)
    let cost : ℕ := 1 + ∑ j, (d j).length
    if ∀ j, (collected ρ c₀ d j).card = k - 1 then
      return (some (coordFamily c₀ (collected ρ c₀ d)), cost)
    else return (none, cost)
  else return (none, 1)
```

The two agree on everything the bound sees. `probEvent_isSome_coordForkOp` proves the loop succeeds
with exactly the core's probability — which column order it happened to draw is irrelevant, because
it stops only on success or on exhaustion (`countP_of_mem_support_drawUntil` is what pins that
down) — and `coordForkOp_success` proves a successful run returns a coordinate-wise `k`-special
sound set of accepting challenges. Both the core and the loop reach that conclusion through the
same `coordFamily_success`, which asks only for `k − 1` accepting replacements per coordinate and
does not care which ones.

So the success and output clauses of Lemma 7.1 hold for the paper's algorithm, against a fixed
acceptance table — which is the setting §7.1 needs, since its own analysis treats the adversary as
a function of the challenge.

### Draw counts

The inner loop of FMN's Figure 11 resamples one challenge coordinate *without replacement* until
`k − 1` further accepting values are found, or the coordinate is exhausted.
[`VCVio/OracleComp/Constructions/WithoutReplacement.lean`](../../VCVio/OracleComp/Constructions/WithoutReplacement.lean)
is that loop as a `ProbComp`, and

```lean
theorem expectedLength_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      expectedLength (drawUntil accept r l)
        = NegHypergeom.expectedDraws n (l.countP accept) r
```

identifies its expected number of draws with the negative hypergeometric recursion in
[`ToMathlib/Probability/NegativeHypergeometric.lean`](../../ToMathlib/Probability/NegativeHypergeometric.lean).
The pool is a `List` rather than a `Finset` so that a draw is an *index*: that keeps the loop in
`ProbComp` with no failure branch and lets it terminate on the pool's length.

Exhaustion needs no separate treatment. The classical closed form `r(M+1)/(G+1)` requires `r ≤ G`,
and below that it is not merely unproved but false — `expectedDraws_ne_closedForm_of_exhaustion`
in the test file exhibits a pool of one where the loop stops after one draw and the formula reads
two. What survives is `NegHypergeom.expectedDraws_le`, the same expression as an *upper* bound with
no hypothesis relating `r` to `G`; above the base cases its induction step is still the same
equality. That single inequality covers the finishing and the exhausting case at once, which is
exactly what the paper's `E[Tᵢ] ≤ k − 1` step needs: at `Xᵢ = l < k` the loop drains the coordinate,
and `(k−1)N/l` already exceeds the `N − 1` values available.

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
