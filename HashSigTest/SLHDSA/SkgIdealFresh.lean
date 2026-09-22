/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SkgIdealFresh

/-!
# The hidden-value event has no joint-cache over-approximation

`HashSig.SLHDSA.Security.SkgIdealFresh` transports the nested-oracle fresh-answer engine to the
ideal secret-value experiment: a predicate `P` of the joint cache that fails at the empty cache
and whose fresh-answer mass is at most `ε` costs `q * ε`.  The obvious candidate for the
hidden-value disjunct of a random-oracle bridge in that lane is a *cache-only* predicate, since
the joint cache is the only thing the engine's run hands back.  This file exhibits the candidate
and shows it is useless: its fresh-answer mass is **one**, so no `ε < 1` satisfies the engine's
hypothesis, and conjoining the engine's own cache-size conjunct does not repair it.

`HiddenHitCache` is that candidate, and it is the one the campaign's device produces.  Verification
happens inside the run, so a forger's claimed secret value is always hashed; `PublicHashQuery.thash`
carries `xs : List core.Y`, so values of the node type really do occur in query *domains*; and the
resulting cache predicate — some settled secret value occurs among the inputs of some settled `T_l`
query — is therefore expressible and is false at the empty cache.

## Why it fails, and what the failure is about

**The obstruction is not probabilistic.**  `evalDist_hiddenHitCache_fresh_eq_one` exhibits a cache
holding one secret entry and no `T_l` entry at which the event flips from false to true on a
*public-hash* step.  The sampled value at that step is the hash *answer*, while the colliding value
sits in the query's *domain*, which is fixed before sampling.  So the firing set is literally
`Set.univ`: the event holds whatever is drawn, and the mass is one rather than small.
`evalDist_hiddenHitCache_and_size_fresh_eq_one` conjoins the size conjunct the engine's event
carries, at the same two-entry cache, and the mass is still one for every `q ≥ 2`.

**The root cause is that the cache is a function**, so it records neither order nor provenance.
"A settled secret occurs in a settled hash input" has two temporal readings: the forger guessing a
secret that has not yet been sampled, which is small; and an honest signature hashing a secret it
legitimately revealed, which is *certain* — every WOTS+ chain step hashes its own secret.  A
predicate that reads only the final cache cannot separate the two, so it is either mass-one or not
an over-approximation of the bad event.  This is the same root as two earlier failures on this
lane: the per-step coverage formulation cannot see order symmetry, and the collision term's
retroactive case cannot express attribution.

**What is refuted is the cache-only route, not every route.**  An order-aware or provenance-aware
instrumentation of the run — a logged transcript, with the bad event read off the log rather than
the cache — or a fresh-answer engine whose predicate may depend on which query is being answered
would not be touched by any of this.  Neither exists yet.

## Why this is a test module and not library content

`HiddenHitCache` must not ship as library content: it is a definition with no sound use, and the
theorems about it are negative results.  Their value is as a **guard**.  A future slice reaching
for the hidden-value disjunct will reach for a symmetric cache-level predicate, and these two
theorems stand in the way of reintroducing one.  They sit beside the witnesses of
`HashSigTest.SLHDSA.Composition`, which play the same role for the canonical tweakable-hash
games: a compiled demonstration that a plausible-looking quantity is unconditionally one.

## Nothing here is runnable

Every statement is a mass under `𝒟[…]` of a lazily sampled uniform draw and is `noncomputable`, so
the file has no `main` and is built by the `HashSigTest` library glob alone.  The two theorems are
equalities, not bounds, so they cannot be weakened into something usable by a stronger hypothesis.

## What the checks cannot catch

* **That the campaign's hidden-value event is what `HiddenHitCache` over-approximates.**  No
  bridge in the ideal lane exists, so there is no formal statement that this predicate is implied
  by a forger's win; the tie is the argument above, not a theorem.
* **Whether some other cache-only predicate succeeds.**  These theorems refute this one.  The
  general claim is the root-cause argument above and is not formalised.

## Labels

Four declarations.  There is no private declaration and no instance.

*The refuted candidate*:

* `SLHDSA.SkgIdealFreshTest.HiddenHitCache`,
  `SLHDSA.SkgIdealFreshTest.not_hiddenHitCache_empty`,
  `SLHDSA.SkgIdealFreshTest.evalDist_hiddenHitCache_fresh_eq_one`,
  `SLHDSA.SkgIdealFreshTest.evalDist_hiddenHitCache_and_size_fresh_eq_one`.
-/

public section

namespace SLHDSA.SkgIdealFreshTest

open Security OracleComp OracleSpec ENNReal MeasureTheory

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]

/-- The joint signature of the ideal experiment's two lazy oracles. -/
local notation "jointSpec" => publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)

/-- The cache-level over-approximation of a hidden-value hit: some settled secret value occurs
among the inputs of some settled `T_l` query.  Refuted below; not usable as a bad event. -/
def HiddenHitCache (c : (jointSpec).QueryCache) : Prop :=
  ∃ (d : core.PkSeed × Adrs) (v : core.Y), c (Sum.inr d) = some v ∧
    ∃ (pkSeed : core.PkSeed) (k : core.AdrsKey) (xs : List core.Y),
      c (Sum.inl (PublicHashQuery.thash pkSeed k xs)) ≠ none ∧ v ∈ xs

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.Y] in
/-- The empty cache is not a hidden hit, so the candidate does satisfy the engine's side condition
at the empty cache. -/
theorem not_hiddenHitCache_empty : ¬ HiddenHitCache core ∅ := by
  simp [HiddenHitCache]

omit [SampleableType (Bytes vp.params.m)] in
/-- **The fresh-answer mass of `HiddenHitCache` at a public-hash step is one.**  At a cache
holding one secret value `v` and no `T_l` entry, the next `T_l` query on `[v]` turns the event on
whatever its answer is, so no `ε < 1` satisfies the engine's hypothesis. -/
theorem evalDist_hiddenHitCache_fresh_eq_one
    (pkSeed : core.PkSeed) (a : Adrs) (k : core.AdrsKey) (v : core.Y) :
    (letI : MeasurableSpace ((jointSpec).Range
        (Sum.inl (PublicHashQuery.thash pkSeed k [v]))) := ⊤;
      𝒟[($ᵗ (jointSpec).Range (Sum.inl (PublicHashQuery.thash pkSeed k [v]))
          : ProbComp _)]
        {u | HiddenHitCache core
          (((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v).cacheQuery
            (Sum.inl (PublicHashQuery.thash pkSeed k [v])) u)} = 1) := by
  let _ : MeasurableSpace ((jointSpec).Range
      (Sum.inl (PublicHashQuery.thash pkSeed k [v]))) := ⊤
  rw [show {u : (jointSpec).Range (Sum.inl (PublicHashQuery.thash pkSeed k [v])) |
      HiddenHitCache core
        (((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v).cacheQuery
          (Sum.inl (PublicHashQuery.thash pkSeed k [v])) u)} = Set.univ from by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨(pkSeed, a), v, by simp [OracleSpec.QueryCache.cacheQuery_of_ne], pkSeed, k, [v],
      by simp, by simp⟩]
  simp

omit [SampleableType (Bytes vp.params.m)] in
/-- **Conjoining a cache-size bound does not repair the fresh-answer mass.**  At the same cache,
which holds two entries, the size-restricted event also fires whatever the answer, so no `ε < 1`
satisfies the engine's hypothesis for the size-restricted predicate either. -/
theorem evalDist_hiddenHitCache_and_size_fresh_eq_one
    (pkSeed : core.PkSeed) (a : Adrs) (k : core.AdrsKey) (v : core.Y)
    (q : ℕ) (hq : 2 ≤ q) :
    (letI : MeasurableSpace ((jointSpec).Range
        (Sum.inl (PublicHashQuery.thash pkSeed k [v]))) := ⊤;
      𝒟[($ᵗ (jointSpec).Range (Sum.inl (PublicHashQuery.thash pkSeed k [v]))
          : ProbComp _)]
        {u | HiddenHitCache core
            (((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v).cacheQuery
              (Sum.inl (PublicHashQuery.thash pkSeed k [v])) u) ∧
          OracleSpec.QueryCache.enncard
            (((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v).cacheQuery
              (Sum.inl (PublicHashQuery.thash pkSeed k [v])) u) ≤ (q : ℝ≥0∞)} = 1) := by
  let _ : MeasurableSpace ((jointSpec).Range
      (Sum.inl (PublicHashQuery.thash pkSeed k [v]))) := ⊤
  have hsize : ∀ u : (jointSpec).Range (Sum.inl (PublicHashQuery.thash pkSeed k [v])),
      OracleSpec.QueryCache.enncard
        (((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v).cacheQuery
          (Sum.inl (PublicHashQuery.thash pkSeed k [v])) u) ≤ (q : ℝ≥0∞) := by
    intro u
    have h1 : OracleSpec.QueryCache.enncard
        ((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v) ≤ 1 := by
      simpa using OracleSpec.QueryCache.enncard_cacheQuery_le
        (∅ : (jointSpec).QueryCache) (Sum.inr (pkSeed, a)) v
    refine le_trans (OracleSpec.QueryCache.enncard_cacheQuery_le _ _ _) ?_
    refine le_trans (add_le_add_left h1 1) ?_
    exact_mod_cast hq
  rw [show {u : (jointSpec).Range (Sum.inl (PublicHashQuery.thash pkSeed k [v])) |
      HiddenHitCache core
          (((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v).cacheQuery
            (Sum.inl (PublicHashQuery.thash pkSeed k [v])) u) ∧
        OracleSpec.QueryCache.enncard
          (((∅ : (jointSpec).QueryCache).cacheQuery (Sum.inr (pkSeed, a)) v).cacheQuery
            (Sum.inl (PublicHashQuery.thash pkSeed k [v])) u) ≤ (q : ℝ≥0∞)} = Set.univ from by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨⟨(pkSeed, a), v, by simp [OracleSpec.QueryCache.cacheQuery_of_ne], pkSeed, k, [v],
      by simp, by simp⟩, hsize u⟩]
  simp

end SLHDSA.SkgIdealFreshTest
