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
| expected query count | proved, for the paper's algorithm | proved, for the paper's recursion |
| success probability | proved, for the paper's algorithm | proved, for the paper's recursion |
| output structure (accepting transcripts) | proved, for the paper's algorithm | proved, for the paper's recursion |

All three clauses hold against a fixed acceptance table — for `coordForkOp` at `μ = 1` and for
`multiForkOpW` at any `μ` — which is the setting §7 needs, since its own analysis treats the
adversary as a function of the challenge. What is *not* covered is a security-parameter experiment,
or an `OracleComp`-level identification of "table lookups" with "oracle queries": the count is
returned as data by the loop rather than measured by the cost model in
[`query-tracking.md`](query-tracking.md).

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
- The cost clause is `expectedValue_cost_coordForkOp_le`: the loop looks at one table entry for the
  sampled challenge and, averaged over that challenge, at most `k − 1` more per coordinate. Its
  counting step is `CoordinateWise.card_mul_sum_div_columnCount_le` — give every accepting challenge
  weight `w` divided by its own column count, and each column contributes at most `w` whatever its
  count, because a column with `l` accepting values gives each of them `w / l`. At `w = (k−1)|S|`
  the weight is exactly the expected number of draws that coordinate's resampling makes. The
  challenge-only
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

### The multi-round recursion

[`CoordinateFork/MultiRoundOp.lean`](../../VCVio/CryptoFoundations/CoordinateFork/MultiRoundOp.lean)
is §7.2's recursion: to extract from a `(2μ+1)`-round protocol, extract a level-`μ−1` tree at every
possible first challenge, then run Figure 11 against the table of which of those succeeded.

```lean
noncomputable def multiForkOp : (μ : ℕ) → (k : ℕ) → (ρ : Transcript ι S μ → Bool) →
    ProbComp (Option (Finset (Transcript ι S μ)))
  | 0, _, ρ => pure (if ρ PUnit.unit then some {PUnit.unit} else none)
  | μ + 1, k, ρ => do
      let tbl ← Fintype.mPi fun c => multiForkOp μ k fun t => ρ (c, t)
      let r ← coordForkOp k fun c => (tbl c).isSome
      return r.1.map fun X => X.biUnion fun c => ((tbl c).getD ∅).image fun t => (c, t)
```

`probEvent_isSome_multiForkOp` is the payoff: its success probability **is** `multiSucc`, the
analytic functional of [`MultiRound.lean`](../../VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean).
That functional is defined by instantiating an independent Bernoulli table, which used to be a
modelling decision with nothing producing it — the coupling is now *derived*, because running the
sub-extractor independently at each first challenge is what `Fintype.mPi` does, and
`probOutput_acceptTable_indepTable_eq_bernoulliTable` identifies the result. The
`ε − μℓ(k−1)/N` bound then reads off `sub_le_multiSucc`.

`multiForkOp_success` is the output clause: a successful run returns accepting transcripts whose
challenge sequences form a tree of challenges, which is exactly what
[`ChallengeTree.lean`](../../ToMathlib/Combinatorics/ChallengeTree.lean) defines and what Lemma 7.2
asks for. (Definition 2.30 also fixes the prover messages at the nodes; Lemma 7.2's *conclusion*
speaks only of the challenge tree, so that is what is delivered here.)

`expectedValue_cost_multiForkOp_le` bounds each *level*: one round looks at at most `1 + ℓ(k−1)` of
the level below, in expectation. The paper's `(ℓ(k−1)+1)^μ` is the product of these, and
`multiForkOpW` is the recursion that composes them:

```lean
theorem expectedValue_weight_multiForkOpW_le [Nonempty S] : ∀ (μ k : ℕ)
    (ρ : Transcript ι S μ → Bool),
    expectedValue (multiForkOpW μ k ρ) (fun r => r.2)
      ≤ (1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞)) ^ μ
```

`multiForkOpW` samples, at every first challenge, the level-below extractor with its coins fixed —
recording both what that extraction returned and what it cost — and the fork then examines entries
and is *charged* what each entry recorded. The charge is the running time of an implementation that
extracts only at the challenges the fork looks at, which is what `(ℓ(k−1)+1)^μ` counts; sampling the
table up front is the same modelling device as §7's fixed acceptance table.
`evalDist_map_fst_multiForkOpW` confirms the charging changes nothing about what the recursion
returns, so `probEvent_isSome_multiForkOpW` and `multiForkOpW_success` carry the other two clauses
across, and all three clauses of Lemma 7.2 hold of one computation.

What makes the levels multiply is the *weighted* single-round bound — §8.2's refinement at `T = 0`
— and not, as one might expect, Wald's identity or an oracle-based redesign. Charge each table
entry `c` a cost `Γ c : ℝ≥0∞` instead of one lookup, and

```
𝔼[Γ-weighted cost of coordForkOp] ≤ (1 + ℓ(k−1)) · 𝔼[Γ]
```

with `𝔼[Γ]` the average of `Γ` over a uniform challenge. Instantiating `Γ` at the level below and
applying `expectedValue_bind` (the tower property) multiplies the levels. The costs compose by the
tower property rather than by an independence argument, so nothing has to be "queried before read",
and the eager `Fintype.mPi` table the success proof relies on stays exactly as it is — only the
accounting changes.

The whole thing reduces to one fact about `ProbComp.drawUntil`, per column and per value `x` in it:

```
∑ over accepting centres c₀ ≠ x in the column, of Pr[x is drawn when the loop starts at c₀]  ≤  k − 1
```

which is tight (equality when `k − 1 ≤ H − 1`, for `H` the column's accepting count). Summing that
against `Γ` over the column, then over columns and coordinates, is the same column-counting shape
that already carries `expectedValue_cost_coordForkOp_le` and §8.1.

The per-element draw probabilities that needs are now available. Getting them meant proving the
loop exchangeable — relabelling a pool within its accept classes leaves the law alone, so all
accepting values are equally likely to be drawn, as are all rejecting ones — which in turn rests on
the loop being *uniform* over its outcomes:

```lean
theorem probOutput_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → l.Nodup →
      ∀ d ∈ support (drawUntil accept r l),
        Pr[= d | drawUntil accept r l] = ((n.descFactorial d.length : ℕ) : ℝ≥0∞)⁻¹
```

An outcome's weight depends only on how many draws it made — not on what was drawn, and not on the
order the pool was presented in. `support_drawUntil_congr` then says two nodup pools with the same
values admit the same runs, so `evalDist_drawUntil_congr` makes the whole law a function of the
pool's *set* of values, and `map_mem_support_drawUntil` carries runs across a relabelling.
`probEvent_mem_drawUntil_congr` is the payoff, and the two aggregate totals
(`sum_probEvent_mem_drawUntil`, `sum_probEvent_mem_drawUntil_accept`) pin the individual
probabilities down:

```lean
theorem probEvent_mem_drawUntil_mul_countP (accept : S → Bool) (r : ℕ) (l : List S)
    (hnd : l.Nodup) {x : S} (hx : x ∈ l) (hacc : accept x) :
    Pr[fun d => x ∈ d | drawUntil accept r l] * (l.countP accept : ℝ≥0∞)
      = ((min r (l.countP accept) : ℕ) : ℝ≥0∞)
```

with `probEvent_mem_drawUntil_mul_countP_not` the rejecting counterpart, sharing out what the
negative hypergeometric expectation leaves over.

The column bound itself is `sum_probEvent_mem_erase_le`, and its weighted form is what a cost bound
consumes:

```lean
theorem sum_expectedValue_sum_map_erase_le (a : S → Bool) (r : ℕ) (g : S → ℝ≥0∞) :
    ∑ v ∈ Finset.univ.filter (fun v => a v),
        expectedValue (drawUntil a r ((Finset.univ.erase v).toList))
          (fun d => (d.map g).sum)
      ≤ (r : ℝ≥0∞) * ∑ x : S, g x
```

Charge every drawn value a weight and a column's expected charge is at most `r` times the column's
total weight, whatever the weights are. The proof splits on whether the fixed value accepts: the
accepting ones share out the loop's accepting draws exactly, while for a rejecting one either the
budget binds — and `NegHypergeom.mul_expectedDraws` makes the accounting exact — or the column runs
out first and each centre draws it at most once.

The fork that consumes it is `coordForkOpW` in
[`CoordinateFork/Operational.lean`](../../VCVio/CryptoFoundations/CoordinateFork/Operational.lean)
— Figure 11 with each entry examined *charged* `Γ` instead of counted — and its bound is the one
the composition needs:

```lean
theorem expectedValue_weight_coordForkOpW_le (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞) :
    expectedValue (coordForkOpW k ρ Γ) (fun r => r.2)
      ≤ (1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞))
          * ((∑ c : ι → S, Γ c) / Fintype.card (ι → S))
```

Taking `Γ = 1` recovers `expectedValue_cost_coordForkOp_le`; the regressions check both that and a
skewed charge, where the bound tracks the average. `multiForkOpW` above is the recursion that
instantiates `Γ` at the level below and multiplies through with `expectedValue_bind`.

`evalDist_drawUntil_eq_map_drawAll` is the reformulation that made the uniformity statement natural
to find:

```lean
theorem evalDist_drawUntil_eq_map_drawAll (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      evalDist (drawUntil accept r l) = evalDist (takeUntil accept r <$> drawAll l)
```

`drawAll` draws the whole pool — it is `drawUntil` with an always-false `accept`, so the budget
never falls and the loop stops only on exhaustion — and `takeUntil` is the deterministic truncation
at the `r`-th accepting element. The recursive loop hides the fact that its law depends on the pool
only through the underlying multiset; a random *ordering* does not, so exchangeability is a
statement about `drawAll` alone, with `takeUntil` a fixed function applied afterwards. The identity
is distributional and not a program equality: at `r = 0` the loop samples nothing while the
right-hand side still draws an ordering and discards it.

### The abstract sampling game

[`CoordinateFork/SamplingGame.lean`](../../VCVio/CryptoFoundations/CoordinateFork/SamplingGame.lean)
is Figure 12, the game §8 analyses on the way to Fiat–Shamir knowledge soundness. An *array*
`M : (Q × ι → S) → Bool × Q` assigns a challenge value to every (random oracle query, coordinate)
pair and records whether the deterministic prover's forgery verifies and *which* query it uses. The
game draws an assignment uniformly, stops if the entry rejects, and otherwise resamples each
coordinate of the winning query's block until `k − 1` further hits for that same query turn up.

The only structural difference from §7's `coordForkOp` is that the block being resampled is named
by the entry rather than fixed in advance, so `ProbComp.drawUntil` and the negative hypergeometric
bound carry over unchanged. What changes is the counting: `blockCount M i j` is Equation (29)'s
`aᵢ(j)`, and `columnCount_le_blockCount` relaxes the per-coordinate count of
[`CoordinateWise.lean`](../../ToMathlib/Combinatorics/CoordinateWise.lean) to it. That relaxation is
strict in general — `columnCount_lt_blockCount_wide` in the test file exhibits a block whose column
through one coordinate is empty while the block still holds a hit.

`expectedValue_cost_samplingGame_le` is the first half of Lemma 8.1:

```lean
theorem expectedValue_cost_samplingGame_le [Nonempty S] [SampleableType (Q × ι → S)] (k : ℕ)
    (M : (Q × ι → S) → Bool × Q) :
    expectedValue (samplingGame k M) (fun r => (r.2 : ℝ≥0∞))
      ≤ 1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞) * blockHitTotal M
```

`blockHitTotal` is the paper's `P`, and despite the name it is not a probability: it sums, over the
query index, the chance that that query's block holds a hit, so it ranges up to the number of
queries (`blockHitTotal_le_card`, and `blockHitTotal_forkedArray` in the test file exhibits
`P = 9/5`). `expectedValue_cost_samplingGame_le_card` is the resulting `1 + Q·ℓ(k−1)`, which is the
budget §8.2's extractor works against. `expectedValue_cost_samplingGame_gatedArray_le` shows the
bound is attained, not merely valid.

`sub_le_probEvent_isSome_samplingGame` is the success bound:

```lean
theorem sub_le_probEvent_isSome_samplingGame [Nonempty S] [SampleableType (Q × ι → S)] (k : ℕ)
    (M : (Q × ι → S) → Bool × Q) :
    ((Finset.univ.filter fun j : Q × ι → S => (M j).1).card : ℝ≥0∞)
          / Fintype.card (Q × ι → S)
        - Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞) / Fintype.card S * blockHitTotal M
      ≤ Pr[fun r => r.1.isSome | samplingGame k M]
```

**The paper's version of this is the one place §8 is not self-contained, and it is avoidable.** FMN
state `Pr[⋀ₗ Xₗ = k] ≥ N/(N−k+1)·(Pr[V=1] − P·ℓ(k−1)/N)` and obtain the extra factor `N/(N−k+1)`
by reusing a per-coordinate bound of Attema–Fehr–Klooß rather than proving it. Dropping that factor
— it is `≥ 1`, so it only ever improves the bound, and nothing downstream depends on it — leaves
exactly what §7's column counting already gives, applied one query at a time. So the bound above
carries no citation.

Getting here needed the counting sharpened twice. `card_mul_sum_div_columnCount_le` used to bound
the weighted column sum by `w · |ι → S|`; it now bounds it by `w` times the number of assignments
whose column is *nonempty* (the cruder form survives as `card_mul_sum_div_columnCount_le_card` for
§7's use). Alongside it, `card_mul_card_filter_columnCount_lt_le` is the same refinement of the
union-bound step, and `card_mul_card_filter_accept_le_sum` runs that union bound over a *chosen*
`Finset` of coordinates rather than all of them, which is what lets §8 apply it to one block at a
time. Without these `P` would collapse to `1` in both halves, and Lemma 8.1 would say nothing
beyond `1 + ℓ(k−1)` and `Pr[V=1] − ℓ(k−1)/N`.

Lemma 8.2's weighted game, Figure 13's extractor, and Lemma 2.32's knowledge error are not
formalized. Lemma 8.2 is the same weighted accounting the §7 multi-round composition needs above,
with the `γ`-weighted term for entries belonging to a *different* query switched back on; both rest
on the same missing per-element draw probability.

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

[`VCVio/ProgramLogic/CoordinateFork.lean`](../../VCVio/ProgramLogic/CoordinateFork.lean) wraps the
single-round and multi-round success bounds as quantitative Hoare triples, matching what
[`VCVio/ProgramLogic/SeededFork.lean`](../../VCVio/ProgramLogic/SeededFork.lean) does for the
seeded fork.

Non-vacuity, payload-sensitivity, coupling, boundary, and bad-extractor checks live in
`VCVioTest/Forking/CoordinateFork.lean`,
`VCVioTest/Forking/CoordSpecialSoundness.lean`, and `VCVioTest/Forking/SamplingGame.lean`; all run
in CI.

## Downstream: ArkLib

[ArkLib](https://github.com/Verified-zkEVM/ArkLib) is a *downstream* consumer — its `lakefile.toml`
carries `require VCVio rev = "v4.30.0"`, on Lean 4.30 against this repo's 4.32.2 — so anything the
coordinate-wise material is to be used for has to be shaped for export, not imported back. A survey
of it in August 2026 found the following; none of it is acted on here beyond the code shape.

**There is a named consumer waiting.** `ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean`
proves the Greyhound/Hachi inner-outer Ajtai commitment's weak binding by reduction to Module-SIS,
and states its core theorem `outputToModuleSIS_valid_of_verified` — *two verified weak openings that
differ yield a Module-SIS witness* — explicitly "independent of how those facts were obtained ...
reused by the CWSS argument for the evaluation protocol, where the two weak openings are
reconstructed from special-soundness transcripts". ArkLib's own notes list the other half as an open
gap. Its openings carry one challenge per block, so the instantiation is `ι` the block index, `S`
the challenge set, `k = 2`.

That is why `IsCoordSpecialSoundTranscripts` mentions only a `Bool`-valued verifier, and why
`IsCoordSpecialSoundTranscripts.exists_pair` exists: the pair *is* the reduction's input. Two
things such an instantiation would still need are recorded in
[`CoordinateFork/SpecialSoundness.lean`](../../VCVio/CryptoFoundations/CoordinateFork/SpecialSoundness.lean)
— a `Fintype`/`SampleableType` on the challenge set (which must be the set actually sampled from,
so that `|S|` in the `ℓ(k−1)/|S|` loss is the right number), and a conversion at the `ℝ≥0∞` / `ℝ≥0`
boundary.

**ArkLib's rewinding layer is empty**, so none of this duplicates work there.
`OracleReduction/Security/SpecialSoundness.lean` is an `ArityTree` skeleton/data scaffolding with no
soundness predicate and no extractor; `Security/Rewinding.lean` is a stub. Its `ArityTree.Data` is
the natural meeting point for the challenge trees of
[`ChallengeTree.lean`](../../ToMathlib/Combinatorics/ChallengeTree.lean). What ArkLib does have is
the *straightline* side — completeness, soundness and knowledge soundness against straightline
extractors, round-by-round soundness with state functions, and state-restoration soundness — all
with `ℝ≥0` errors.

**Two upstreaming backlogs point here.** `ArkLib/ToVCVio/` is a handful of small `OracleComp` /
`EvalDist` / `SubSpec` / `simulateQ` / `Vector.mapM` support lemmas, sorry-free, staged by name for
this repo. `ArkLib/Data/Probability/Instances.lean` carries an explicit `TODO` to move most of its
contents here; its uniform-splitting and marginalization theorems overlap
[`EvalDist/IndepProduct.lean`](../../VCVio/EvalDist/IndepProduct.lean).

**Lattice overlap, noted only.** ArkLib carries a large, nearly sorry-free cyclotomic-ring library
— `Rq`, Lyubashevsky–Seiler and Micciancio–Young norm bounds, Galois trace, subfield packing,
`ModuleSIS` — overlapping `LatticeCrypto/Ring/`. This repo cannot import ArkLib without a cycle, and
the two libraries serve different ends (FIPS schemes here, proof systems there), so merging them is
a separate question.

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
