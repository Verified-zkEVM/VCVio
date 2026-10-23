/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FreshHitBound

/-!
# Cache persistence and bad cached answers

Cache entries are never overwritten (`cache_value_persists`): once an answer is installed,
every later query returns that same answer. `Bad` is the event that some cached answer is bad for
its own input, and `CleanBad` is its negation at a cache. -/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.GrowthCharge

/-- Cache entries are never *overwritten*: an installed answer persists verbatim.

This is what makes a run started from the **empty** cache enough, where freshness at the moment
of the query is not available in the experiment, because the adversary may query a signer's
input first. Once an answer is installed, whoever installed it, every later query returns that
same answer. -/
theorem cache_value_persists {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ KeygenUniform.rom computation).run initialCache))
    (input : Bytes) (output : HashOutput) (hentry : initialCache input = some output) :
    finalCache input = some output := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hmem.2 ▸ hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
    have hmiddle : middleCache input = some output := by
      rcases queried with coin | queried
      · have hcache : middleCache = initialCache := by
          symm
          simpa [KeygenUniform.rom, Xmss.RandomOracleModel.impl, unifFwdImpl] using hquery
        exact hcache ▸ hentry
      · change (answer, middleCache) ∈ support ((randomOracle queried).run initialCache) at hquery
        cases hqueried : initialCache queried with
        | none =>
          rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
          obtain ⟨sampled, _, hpair⟩ := hquery
          have hmid : middleCache = initialCache.cacheQuery queried sampled :=
            (Prod.ext_iff.mp hpair).2.symm
          rw [hmid]
          have hne : input ≠ queried := by
            intro hsame
            rw [hsame, hqueried] at hentry
            simp at hentry
          rw [QueryCache.cacheQuery_of_ne initialCache sampled hne]
          exact hentry
        | some cached =>
          rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
            Set.mem_singleton_iff] at hquery
          have hmid : middleCache = initialCache := (Prod.ext_iff.mp hquery).2
          exact hmid ▸ hentry
    exact ih answer middleCache finalCache result hrest hmiddle

/-! ## Bad cached answers

A bad event is a predicate `bad` on an input and its answer. `Bad` says some cached answer is bad
for its own input, `CleanBad` says the cache holds none, and `CleanBad.cacheQuery` shows that
installing a non-bad answer keeps a cache clean. -/

/-- Some cached answer is bad for its own input. -/
def Bad {α : Type} (bad : Bytes → HashOutput → Prop) :
    α × QueryCache HashSpec → Prop := fun result =>
  ∃ input output, result.2 input = some output ∧ bad input output

/-- The cache holds no answer that is bad for its own input. -/
def CleanBad (bad : Bytes → HashOutput → Prop) (cache : QueryCache HashSpec) : Prop :=
  ∀ input output, cache input = some output → ¬ bad input output

/-- Installing an answer that is not bad for its input keeps a clean cache clean. -/
theorem CleanBad.cacheQuery {bad : Bytes → HashOutput → Prop} {cache : QueryCache HashSpec}
    (hclean : CleanBad bad cache) {input : Bytes} {output : HashOutput}
    (hmiss : ¬ bad input output) : CleanBad bad (cache.cacheQuery input output) := by
  intro queried answer hanswer
  by_cases heq : queried = input
  · subst heq
    rw [QueryCache.cacheQuery_self] at hanswer
    cases hanswer
    exact hmiss
  · rw [QueryCache.cacheQuery_of_ne cache output heq] at hanswer
    exact hclean queried answer hanswer

end SlhDsaSecurity.GrowthCharge
