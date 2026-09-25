# Forking Lemmas

Three forking developments live in this repository. They differ in what gets pre-sampled and in
the shape of the bound they deliver. The coordinate-wise development is a table model with a
realizability bridge to ordinary adversaries; its extractor is the paper's own algorithm, but its
cost is a count of *table lookups* returned as data, not oracle queries measured by the cost model.
See [crypto.md](crypto.md) for the surrounding primitive and reduction machinery.

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
expected-query oracle extractor; the present formalization proves all three of its clauses — the
output, the success probability and the expected number of lookups — of the paper's own algorithm,
against a fixed acceptance table, and transfers the success bound to an adversary.

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

In this model, randomized behavior is represented by a distribution over complete tables, and the
`Averaging` section of
[`CoordinateFork.lean`](../../VCVio/CryptoFoundations/CoordinateFork.lean) averages the counting
bound over an *arbitrary* such distribution:

```lean
theorem sub_div_le_lintegral_card_goodSet [Nonempty S] (D : m ((ι → S) → Bool)) (k : ℕ)
    [IsProbabilityMeasure 𝒟[D]] :
    acceptRatio D - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S ≤ forkSuccOf k D
```

It is stated for a general monad, since nothing in the averaging argument is specific to
`ProbComp`. Only the marginals of `D` appear on the left, so no independence hypothesis is needed.
Note the converse is *not* true: `forkSuccOf k D` depends on all of `D`, so fixing a particular
coupling of the table entries is a modelling decision about the extractor's randomness, not a
theorem. `sum_goodSet_correlated` and `sum_goodSet_anticorrelated` in the test file exhibit two
couplings with equal marginals and different `forkSuccOf`.

### Transcripts

The core is `Bool`-valued, but the paper's extractor outputs *pairs* `(cᵢ, yᵢ)`. That is a layer on
top rather than a generalization: a response table `τ : (ι → S) → Y` and a verifier
`V : (ι → S) → Y → Bool` induce the acceptance table `fun c => V c (τ c)`, so `coordForkT` is
`coordFork` composed with `acceptTable`, `coordFork_acceptTable` exhibits the two as the same
computation up to relabelling, and `sub_div_le_prEvent_goodTranscripts_coordForkT` carries the
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
composes that with the fork to give **Lemma 2.31 at `μ = 1`**. The extractor it names is
`coordExtractOp`: run Figure 11 carrying the prover's responses (`OracleComp.coordForkOpT`), then
hand the accepting transcripts to `ext`. All three of Lemma 7.1's clauses are about that one
computation —

* `OracleComp.coordForkOpT_success`: the fork produced `ℓ(k−1)+1` verifier-accepting transcripts
  whose challenges form an `SS(S, ℓ, k)` set;
* `sub_div_le_prEvent_extracted_coordExtractOp`: the event `Extracted rel x` — *a valid witness was
  returned* — has probability at least `ε − ℓ(k−1)/|S|`. Aborting runs fail that event, so it is
  not a termination bound;
* `lintegral_cost_coordExtractOp_le`: at most `1 + ℓ(k−1)` table lookups in expectation.

`coordExtract` over the total-lookup core `coordForkT` is kept alongside: the counting argument is
proved about the core, and the averaging over the prover's first message is stated through it.
`coordExtractCommit` does that averaging — the prover samples a pair `(pc, τ)`, a commitment
together with the response table its now-fixed coins commit it to, and
`sub_div_le_prEvent_extracted_coordExtractCommit` gives the same bound with `ε` read off the whole
experiment (`verifyProb`). The loss is unchanged, because averaging a pointwise bound over the
first message costs nothing.

A full Definition 2.28/2.31 result would additionally need the security-parameter experiment, the
joint bad event, an oracle-query cost semantics, and an expected-polynomial-time proof.

### Realizing a table by an adversary

[`CoordinateFork/Realizability.lean`](../../VCVio/CryptoFoundations/CoordinateFork/Realizability.lean)
closes the gap between "a distribution of response tables" and "an adversary". For
`A : (ι → S) → ProbComp Y`, `indepTable A := Fintype.mPi A` pre-samples **independent** randomness
at every challenge, and

```lean
theorem acceptRatio_acceptTable_indepTable (V) (A) :
    acceptRatio (acceptTable V (indepTable A)) = advSucc V A
```

identifies the accepting ratio the table bound consumes with `ε_V(A)`, the adversary's own success
probability on a uniform challenge. The transfer is cheap precisely because
`le_lintegral_card_goodSet` reads only the *marginals* of the table distribution, so realizing some
distribution with the adversary's marginals is all it needs. No side condition appears: a
`ProbComp` always carries full mass (`prEvent_true_probComp`), so the hypothesis the general
marginal lemma requires is automatic.

**`indepTable` is not a rewound prover, and the file does not claim it is.** A prover holding one
coin tape answers two challenges with values that share those coins; `Fintype.mPi` gives the two
answers independent coins. The two constructions agree on every single-challenge marginal and
differ on the joint law — `coinFlipAdv` in
[`VCVioTest/Forking/CoordinateFork.lean`](../../VCVioTest/Forking/CoordinateFork.lean) ignores its
challenge and returns one fair bit, and two challenges accept together with probability `1/2` under
a shared tape against `1/4` here. Only the marginals feed the transfer above, which is why the
transfer holds and why it licenses nothing about rewinding.

The independent-product machinery underneath is generic and lives below the crypto layer:
[`VCVio/EvalDist/IndepProduct.lean`](../../VCVio/EvalDist/IndepProduct.lean) gives `Fin.mOfFn` and
`Fintype.mPi` their joint events (`prEvent_forall_coord_mPi`) and coordinate marginals, and
[`VCVio/EvalDist/IndepProductMeasure.lean`](../../VCVio/EvalDist/IndepProductMeasure.lean)
identifies their denotation with Mathlib's `Measure.pi`. The marginal is an equality only under a
full-mass hypothesis; `prEvent_coord_mOfFn_le` is what survives without it, and
`prEvent_coord_mOfFn_failFactor` in the test file is the negative control showing the difference is
real.

### What is and is not proved

Lemma 7.1 is a three-conjunct existential over *an oracle algorithm with oracle access to the
adversary*. Against a fixed acceptance table all three conjuncts are proved, of the paper's own
algorithm:

| Clause | Status | Theorem |
|---|---|---|
| output structure | proved | `coordForkOp_success`, `coordForkOpT_success` |
| success probability | proved | `sub_div_le_prEvent_isSome_coordForkOp` |
| expected lookups | proved | `lintegral_cost_coordForkOp_le` |

A fixed acceptance table is the setting §7.1 needs: its own analysis reasons about
`Xᵢ = |{x ∈ S : V (C x) (A (C x))}|` and uses `Pr[V = 1 ∣ Xᵢ = l] = l/N`, and both presuppose that
`A` is a *function* of the challenge, so that "how many values of coordinate `i` would have been
accepted" is well defined at all. Such an `A` is exactly a response table.

What is **not** covered:

- **No oracle-query semantics.** The count is of table lookups, returned as data by the loop, not
  oracle queries measured by the cost model in [`query-tracking.md`](query-tracking.md). Bridging
  the two means running the loop against an instrumented handler.
- **No security parameter.** `CoordSpeciallySoundAt` is the extensional, fixed-statement clause of
  Definition 2.29 — no polynomial-time requirement, no joint bad event, no asymptotics. So this is
  not Definition 2.28.
- **`indepTable` is not a rewind coupling**, as above.
- **Multi-round is deferred**, see below.

One place the formalization is *stronger* than the source. FMN's union bound reads
`Pr[Γ=1] − Σᵢ Σⱼ j/N`, dropping the weights `Pr[Xᵢ = j]`; as printed that sums to `ℓk(k−1)/2N`,
which does not give the claimed `ℓ(k−1)/N` for `k > 2`. Keeping the weights does, since
`Σⱼ Pr[Xᵢ = j]·(j/N) ≤ (k−1)/N`, and that is what `CoordinateWise.sub_div_le_div_card_filter`
proves. The Lean statement is the paper's; the proof repairs the printed step.

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

The two agree on everything the bound sees. `prEvent_isSome_coordForkOp` proves the loop succeeds
with exactly the core's probability — which column order it happened to draw is irrelevant, because
it stops only on success or on exhaustion (`countP_of_mem_support_drawUntil` is what pins that
down) — and `coordForkOp_success` proves a successful run returns a coordinate-wise `k`-special
sound set of accepting challenges. Both the core and the loop reach that conclusion through the
same `coordFamily_success`, which asks only for `k − 1` accepting replacements per coordinate and
does not care which ones.

`coordForkOpT` is the same loop carrying the prover's responses, so its output clause is about
*transcripts*; it is what `CoordinateFork/Extraction.lean` names as the extractor.

The cost clause is `lintegral_cost_coordForkOp_le`: the loop looks at one table entry for the
sampled challenge and, averaged over that challenge, at most `k − 1` more per coordinate. Its
counting step is `CoordinateWise.card_mul_sum_div_columnCount_le` — give every accepting challenge
weight `w` divided by its own column count, and each column contributes at most `w` whatever its
count, because a column with `l` accepting values gives each of them `w / l`. At `w = (k−1)|S|` the
weight is exactly the expected number of draws that coordinate's resampling makes.

`coordForkOpW` is the same loop with each entry examined *charged* `Γ` rather than counted, and
`lintegral_weight_coordForkOpW_le` bounds the expected charge by `(1 + ℓ(k−1))` times the average
charge of one entry. That is the form the multi-round recursion consumes.

### Multi-round, and §8.1: deferred

§7.2's `μ`-round recursion and §8.1's abstract sampling game are **not** in this development. They
exist, finished, on `dtumad/coordinate-fork-multiround`, and land separately. What they contain,
so that nobody re-derives it:

- `multiForkOp` / `multiForkOpW` recurse Figure 11 over `μ` rounds, with the success clause
  `ε − μℓ(k−1)/N`, an output clause producing a level-`μ` challenge tree
  (`ToMathlib/Combinatorics/ChallengeTree.lean` is its combinatorial projection, kept here), and a
  weighted bound `(1 + ℓ(k−1))^μ`. That last one is the paper's `(ℓ(k−1)+1)^μ`, and it comes from
  the weighted single-round bound plus the tower property — **not** from Wald's identity, which is
  what one expects to need and does not.
- It is nonetheless a **charge on an eagerly pre-sampled table**, not an oracle-query count.
  `multiForkOpW` runs a recursive extraction at *every* first challenge through `Fintype.mPi` and
  returns only the charges of the entries the outer fork selects; at `ℓ = 1`, four challenge
  values, depth two and an always-rejecting table, the eager recursion performs sixteen base-level
  calls while the returned charge is one. Identifying the charge with the paper's query count needs
  a lazy extractor and a joint output/cost correspondence, and that is the reason the multi-round
  material is not being landed as "Lemma 7.2".
- Worth recording: FMN's own Lemma 7.2 derives `(ℓ(k−1)+1)^μ` by multiplying two expectations in
  one sentence, with no justification. The formalized bound is about a different object than the
  paper's, but it is *proved*, where the paper's is asserted.
- §8.1's sampling game proves both halves of Lemma 8.1 and, unlike the paper, without the
  `N/(N−k+1)` factor that FMN import from Attema–Fehr–Klooß — that factor is `≥ 1`, so dropping it
  strengthens the bound, and what remains follows from §7's own column counting.

### Draw counts

The inner loop of FMN's Figure 11 resamples one challenge coordinate *without replacement* until
`k − 1` further accepting values are found, or the coordinate is exhausted.
[`VCVio/OracleComp/Constructions/WithoutReplacement.lean`](../../VCVio/OracleComp/Constructions/WithoutReplacement.lean)
is that loop as a `ProbComp`, and

```lean
theorem lintegral_evalDist_length_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      (∫⁻ n, (n : ENNReal) ∂𝒟[List.length <$> drawUntil accept r l])
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

Hoare-triple wrappers for these bounds, matching what
[`VCVio/ProgramLogic/SeededFork.lean`](../../VCVio/ProgramLogic/SeededFork.lean) does for the
seeded fork, are deferred with the multi-round material.

Non-vacuity, payload-sensitivity, coupling, boundary, shared-tape and bad-extractor checks live in
[`VCVioTest/Forking/CoordinateFork.lean`](../../VCVioTest/Forking/CoordinateFork.lean) and
[`VCVioTest/Forking/CoordSpecialSoundness.lean`](../../VCVioTest/Forking/CoordSpecialSoundness.lean);
both are built by `lake test`.

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

Coordinate-wise `k`-special soundness is a special case of Attema–Fehr–Resch's `Γ`-out-of-`C`
special soundness ([AFR23], eprint 2023/818). Their Lemma 5 gives the generic extractor an
expected-query **upper** bound `2 * tᵧ - 1` — linear in `tᵧ`, and the only bound on extraction cost
that paper states in either direction. The local formalization proves that the relevant `tᵧ` is
exponential in `ℓ`, so the hypothesis of their knowledge-soundness theorem, that `tᵧ` is polynomial
in the statement size, fails here and their result does not apply:
[`ToMathlib/Combinatorics/MonotoneStructure.lean`](../../ToMathlib/Combinatorics/MonotoneStructure.lean)
formalizes the bound:

```lean
theorem pow_add_one_le_tValue [Nontrivial S] [Nonempty ι] :
    Fintype.card S ^ (Fintype.card ι - 1) + 1 ≤ tValue (coordStructure 2) (∅ : Finset (ι → S))
```

The argument is pure `Finset` combinatorics with no probability: the slice of challenges fixing one
coordinate contains no `SS(S, ℓ, 2)` set, because two challenges differing only in that coordinate
cannot both lie in it — but adjoining a single challenge off the slice creates one. So every
untaken slice element stays useful, and then one element off the slice is useful again.

This is a statement about the *guarantee*, not about the generic extractor's actual running time:
substituting a lower bound on `tᵧ` into an upper bound on runtime bounds nothing, and neither the
generic extractor nor its cost is formalized here. FMN's §7.3 states the conclusion the stronger
way; the defensible reading, and the one these docstrings take, is that the route through
`Γ`-out-of-`C` special soundness is closed rather than that the generic extractor is slow.

## Deferred oracle semantics

The table proof changes a challenge vector by value (`Function.update c j x`). The paper's
extractor instead needs an operational account of rerunning a prover, fixing a prefix, and varying
the selected challenge while preserving the appropriate surrounding randomness. No positional
rewind primitive in this PR is consumed by the proofs, so that machinery is deliberately deferred
until a concrete costed extractor specifies exactly which state must be retained.
