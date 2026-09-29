/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.PRG
public import VCVio.EvalDist.MeasureTVDist.Bind
public import VCVio.EvalDist.MeasureTVDist.Event
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

import ToMathlib.Data.ENNReal.Gauss

/-!
# PRG from PRF

This file constructs a simple stream-style PRG from a PRF
`f : K → S → S × O`. Starting from a random state `s₀`, each round applies
the PRF to the current state, producing the next state and one output block.

The proof outline follows the standard switching argument:

1. Replace the real PRF with a random function.
2. Show that, except when the state chain repeats, the random-function world is
   identical to the ideal PRG world of independent uniform outputs.
3. Bound the remaining gap by the probability of a state collision.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory PRFScheme PRGScheme
open List (Vector)

namespace PRGfromPRF

variable {K S O : Type}

/-- Deterministically unroll `n` rounds of a state transition/output function. -/
def streamOutputs (step : S → S × O) : (n : ℕ) → S → List.Vector O n
  | 0, _ => .nil
  | n + 1, s =>
      let (s', out) := step s
      out ::ᵥ streamOutputs step n s'

/-- Query the PRF oracle `n` times, threading the returned state and collecting outputs. -/
def oracleOutputs :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector O n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', out) ← PRFScheme.functionQuery s
      let rest ← oracleOutputs n s'
      pure (out ::ᵥ rest)

/-- Query the PRF oracle `n` times, recording the states fed to the oracle. Repeated
states are exactly the bad event for the random-function to ideal-PRG hop. -/
def oracleVisitedStates :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector S n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', _) ← PRFScheme.functionQuery s
      let rest ← oracleVisitedStates n s'
      pure (s ::ᵥ rest)

/-- Stream-style PRG obtained by iterating a PRF `n` times. The seed contains both the
PRF key and the initial state; later theorems assume the PRF key distribution is uniform. -/
@[simps!] def streamPRG (prf : PRFScheme K S (S × O)) (n : ℕ) :
    PRGScheme (K × S) (List.Vector O n) where
  gen ks := streamOutputs (prf.eval ks.1) n ks.2

namespace streamPRG

variable {prf : PRFScheme K S (S × O)} {n : ℕ}

/-! ### Sampling and counting helpers

Facts about uniform samples of pairs and vectors and about cache cardinalities; each states
the structure it needs on `S` and `O`. -/

/-- The reference uniform output vector of length `N + 1`, written as a bind over a uniformly
sampled pair `p : S × O` whose first coordinate is discarded and whose second coordinate is the
prepended head block. This is the shared-base form used for the identical-until-bad coupling. -/
private lemma evalDist_uniformSample_vector_succ_pair [SampleableType S] [SampleableType O]
    (N : ℕ) :
    (letI : MeasurableSpace (List.Vector O (N + 1)) := ⊤;
      𝒟[($ᵗ (List.Vector O (N + 1)))] =
        𝒟[(do let p ← $ᵗ (S × O); (fun v => p.2 ::ᵥ v) <$> ($ᵗ (List.Vector O N)))]) := by
  let : MeasurableSpace (List.Vector O (N + 1)) := ⊤
  rw [(SampleableType.evalDistEq_uniformSample_vector_succ N).evalDist_eq,
    SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  exact (OracleComp.evalDist_bind_const _ _).symm

/-- Mass of `true` after a draw, as the integral of the continuation's mass of `true`. -/
private lemma evalDist_bind_apply_true {γ : Type} (mx : ProbComp γ) (f : γ → ProbComp Bool) :
    𝒟[mx >>= f] {true} = (letI : MeasurableSpace γ := ⊤; ∫⁻ x, 𝒟[f x] {true} ∂𝒟[mx]) := by
  let : MeasurableSpace γ := ⊤
  rw [evalDist_bind_of_discrete, Measure.bind_apply (measurableSet_singleton true)
    Measurable.of_discrete.aemeasurable]

/-- Caching a fresh (previously absent) key increases the live-entry count by exactly one. -/
private lemma enncard_cacheQuery_of_none [DecidableEq S]
    (c : (S →ₒ S × O).QueryCache) (s : S) (u : S × O)
    (hc : c s = none) :
    QueryCache.enncard (c.cacheQuery s u) = QueryCache.enncard c + 1 := by
  unfold QueryCache.enncard
  have hset : (c.cacheQuery s u).toSet = insert ⟨s, u⟩ c.toSet := by
    ext ⟨t', u'⟩
    by_cases ht : t' = s
    · subst ht
      simp only [QueryCache.mem_toSet, QueryCache.cacheQuery_self, Set.mem_insert_iff,
        Sigma.mk.injEq, heq_eq_eq, true_and]
      constructor
      · intro h
        exact Or.inl (Option.some.inj h).symm
      · rintro (rfl | h)
        · rfl
        · rw [hc] at h; exact absurd h (by simp)
    · rw [QueryCache.mem_toSet, QueryCache.cacheQuery_of_ne c u ht]
      simp [Set.mem_insert_iff, ht, QueryCache.mem_toSet]
  rw [hset]
  have hnotmem : (⟨s, u⟩ : (t : S) × S × O) ∉ c.toSet := by
    rw [QueryCache.mem_toSet, hc]; simp
  rw [Set.encard_insert_of_notMem hnotmem]
  push_cast
  ring

/-- For a finite state space, the live-entry count of a cache is the number of cached states. -/
private lemma enncard_eq_sum_isCached [Fintype S] (c : (S →ₒ S × O).QueryCache) :
    QueryCache.enncard c = ∑ s : S, (if c.isCached s then (1 : ℝ≥0∞) else 0) := by
  classical
  unfold QueryCache.enncard
  have himg : Sigma.fst '' c.toSet = {s : S | c.isCached s = true} := by
    ext s
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨t, u⟩, ht, rfl⟩
      rw [QueryCache.mem_toSet] at ht
      simp [QueryCache.isCached, ht]
    · intro hs
      rw [QueryCache.isCached, Option.isSome_iff_exists] at hs
      obtain ⟨u, hu⟩ := hs
      exact ⟨⟨s, u⟩, hu, rfl⟩
  have hinj : Set.InjOn Sigma.fst c.toSet := by
    rintro ⟨t₁, u₁⟩ h₁ ⟨t₂, u₂⟩ h₂ (rfl : t₁ = t₂)
    rw [QueryCache.mem_toSet] at h₁ h₂
    rw [h₁] at h₂
    obtain rfl := Option.some.inj h₂
    rfl
  have hencard : c.toSet.encard = {s : S | c.isCached s = true}.encard := by
    rw [← himg, hinj.encard_image]
  rw [hencard, Set.encard_eq_coe_toFinset_card, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [mul_one, mul_zero, add_zero, nsmul_eq_mul]
  rw [Set.toFinset_ofPred]
  norm_cast

/-! ### The real world -/

/-- Reduction from a distinguisher on the stream PRG output to a PRF distinguisher. It
samples an initial state, queries the candidate oracle `n` times, and feeds the resulting
output vector to the PRG adversary. -/
def prfReduction [SampleableType S]
    (n : ℕ) (adv : PRGAdversary (List.Vector O n)) : PRFAdversary S (S × O) :=
  show OracleComp (unifSpec + (S →ₒ S × O)) Bool from do
    let seed ← OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (S →ₒ S × O))
      ($ᵗ S)
    let outputs ← oracleOutputs n seed
    OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (S →ₒ S × O))
      (adv outputs)

/-- Under the real PRF query implementation, querying the oracle `n` times produces the
same outputs as the deterministic `streamOutputs`. -/
private lemma simulateQ_prfReal_oracleOutputs (k : K) (n : ℕ) (s : S) :
    simulateQ (prfRealQueryImpl prf k) (oracleOutputs n s) =
      (pure (streamOutputs (prf.eval k) n s) : ProbComp _) := by
  induction n generalizing s with
  | zero => simp [oracleOutputs, streamOutputs]
  | succ n ih =>
    cases h : prf.eval k s with
    | mk s' out =>
        simp only [oracleOutputs, streamOutputs, simulateQ_bind,
          simulateQ_prfRealQueryImpl_functionQuery, h, pure_bind]
        rw [ih]
        simp

/-- Applying the real PRF query implementation to the full reduction body simplifies to
sampling a seed and running the adversary on deterministic output. -/
private lemma simulateQ_prfReal_reduction [SampleableType S] (k : K) (n : ℕ)
    (adv : PRGAdversary (List.Vector O n)) :
    simulateQ (prf.prfRealQueryImpl k)
      (show OracleComp (unifSpec + (S →ₒ S × O)) Bool from do
        let seed ← liftComp ($ᵗ S) (unifSpec + ofFn fun _ => S × O)
        let outputs ← oracleOutputs n seed
        liftComp (adv outputs) (unifSpec + ofFn fun _ => S × O)) =
    (do let s ← $ᵗ S; adv (streamOutputs (prf.eval k) n s)) := by
  change simulateQ (prf.prfRealQueryImpl k)
      (do
        let seed ← liftComp ($ᵗ S) (unifSpec + ofFn fun _ => S × O)
        let outputs ← oracleOutputs n seed
        liftComp (adv outputs) (unifSpec + ofFn fun _ => S × O)) =
    (do
      let s ← $ᵗ S
      adv (streamOutputs (prf.eval k) n s))
  rw [simulateQ_bind, simulateQ_prfRealQueryImpl_liftComp]
  refine bind_congr ?_
  intro s
  rw [simulateQ_bind, simulateQ_prfReal_oracleOutputs, pure_bind,
      simulateQ_prfRealQueryImpl_liftComp]

/-- In the real world, the stream PRG experiment has the same output distribution as
the real PRF experiment for the reduction adversary, provided the PRF key
distribution is uniform. -/
theorem prgRealExperiment_eq_prfRealExperiment [SampleableType K] [SampleableType S]
    (hkey : prf.keygen =ᵈ ($ᵗ K : ProbComp K))
    (adv : PRGAdversary (List.Vector O n)) :
    𝒟[PRGScheme.prgRealExperiment (streamPRG prf n) adv] =
      𝒟[PRFScheme.prfRealExperiment prf (prfReduction (S := S) (O := O) n adv)] := by
  simp only [PRGScheme.prgRealExperiment, PRFScheme.prfRealExperiment, prfReduction, streamPRG]
  simp_rw [simulateQ_prfReal_reduction]
  change 𝒟[(·, ·) <$> ($ᵗ K) <*> ($ᵗ S) >>=
    fun ks => adv (streamOutputs (prf.eval ks.1) n ks.2)] = _
  simp only [monad_norm, Function.comp_def]
  let : MeasurableSpace K := ⊤
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, hkey.evalDist_eq]

/-- The ideal PRG experiment for the stream adversary is exactly: sample a uniform output
vector and run the adversary on it. -/
lemma prgIdealExperiment_eq_bind [SampleableType O] (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgIdealExperiment adv = (($ᵗ (List.Vector O n)) >>= adv) :=
  rfl

/-! ### The ideal world

The lazy random oracle on `S` needs equality on `S`, and its answers and the fresh output
blocks are sampled uniformly. -/

variable [DecidableEq S] [SampleableType S] [SampleableType O]

/-- Collision experiment for the ideal random-function world: sample an initial state,
iterate a lazy random oracle for `n` rounds, and test whether any queried state repeats. -/
def idealCollisionExperiment (n : ℕ) : ProbComp Bool := do
  let seed ← $ᵗ S
  let states ←
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := S) (R := S × O))
      (oracleVisitedStates n seed)).run' ∅
  return decide (¬ states.toList.Nodup)

/-- Probability of the bad event in the ideal random-function world. -/
noncomputable def collisionProb (n : ℕ) : ℝ≥0∞ :=
  𝒟[idealCollisionExperiment (S := S) (O := O) n] {true}

/-- The output distribution that the ideal PRF reduction feeds to the PRG adversary:
sample an initial seed, then read `n` output blocks off the lazy random oracle chain. -/
def idealOutputs (n : ℕ) : ProbComp (List.Vector O n) := do
  let seed ← $ᵗ S
  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅

/-- The ideal PRF experiment, applied to the stream reduction, factors as sampling the
adversary's input via the lazy-random-oracle chain (`idealOutputs`) and then running the
adversary. -/
lemma prfIdealExperiment_prfReduction_eq (adv : PRGAdversary (List.Vector O n)) :
    PRFScheme.prfIdealExperiment (prfReduction (S := S) (O := O) n adv) =
      (idealOutputs (S := S) (O := O) n >>= adv) := by
  unfold PRFScheme.prfIdealExperiment prfReduction idealOutputs
  rw [simulateQ_bind, simulateQ_prfIdealQueryImpl_liftComp, StateT.run'_liftM_bind]
  calc
    _ = (($ᵗ S) >>= fun seed =>
        (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
          (oracleOutputs n seed)).run' ∅ >>= adv) := by
      refine bind_congr fun seed => ?_
      rw [simulateQ_bind]
      simp only [simulateQ_prfIdealQueryImpl_liftComp]
      rw [StateT.run'_bind_liftM]
    _ = _ := (bind_assoc ($ᵗ S)
      (fun seed => (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
        (oracleOutputs n seed)).run' ∅) adv).symm

/-- The per-seed output distribution: run the lazy random oracle chain for `n` rounds from a
fixed initial state `seed`, collecting the output blocks. Averaging over `seed ← $ᵗ S` gives
`idealOutputs`. -/
def seedOutputs (n : ℕ) (seed : S) : ProbComp (List.Vector O n) :=
  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅

/-- The per-seed collision experiment: run the lazy random oracle chain for `n` rounds from a
fixed initial state `seed`, and test whether any queried state repeats. Averaging over
`seed ← $ᵗ S` gives `idealCollisionExperiment`. -/
def seedCollisionExperiment (n : ℕ) (seed : S) : ProbComp Bool := do
  let states ←
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
      (oracleVisitedStates n seed)).run' ∅
  return decide (¬ states.toList.Nodup)

/-- `idealOutputs` averages the per-seed chain outputs over a uniform initial state. -/
lemma idealOutputs_eq_bind :
    idealOutputs (S := S) (O := O) n = (($ᵗ S) >>= seedOutputs (S := S) (O := O) n) := rfl

/-- `idealCollisionExperiment` averages the per-seed collision test over a uniform initial state. -/
lemma idealCollisionExperiment_eq_bind :
    idealCollisionExperiment (S := S) (O := O) n =
      (($ᵗ S) >>= seedCollisionExperiment (S := S) (O := O) n) :=
  rfl

/-- Generalized collision experiment for an arbitrary starting cache `c`. Running the lazy
random oracle chain for `N` rounds from state `s`, the bad event is that the chain repeats a
state (`¬ Nodup`) or revisits a state already present in `c`. For `c = ∅` this reduces to
`seedCollisionExperiment`. The generalized cache is the induction vehicle: each fresh step extends
`c` by the just-visited state. -/
def genCollisionExperiment (N : ℕ) (s : S) (c : (S →ₒ S × O).QueryCache) :
    ProbComp Bool := do
  let states ←
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleVisitedStates N s)).run' c
  return decide (¬ states.toList.Nodup ∨ ∃ x ∈ states.toList, c.isCached x = true)

/-- One lazy-random-oracle step of the output chain: sample/recall the answer at `s`, then
recurse on the returned next-state with the updated cache, prepending the output block. -/
private lemma simulateQ_oracleOutputs_succ_run' (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) :
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs (N + 1) s)).run' c =
      (do
        let p ← ((S →ₒ S × O).randomOracle s).run c
        let rest ← (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
          (oracleOutputs N p.1.1)).run' p.2
        pure (p.1.2 ::ᵥ rest)) := by
  rw [oracleOutputs]
  simp only [simulateQ_bind, simulateQ_prfIdealQueryImpl_functionQuery, StateT.run'_bind']
  refine bind_congr fun a : (S × O) × (S →ₒ S × O).QueryCache => ?_
  obtain ⟨⟨s', out⟩, c'⟩ := a
  simp [StateT.run'_eq]

/-- One lazy-random-oracle step of the visited-state chain: sample/recall the answer at `s`, then
recurse on the returned next-state with the updated cache, prepending the just-visited state `s`. -/
private lemma simulateQ_oracleVisitedStates_succ_run' (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) :
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
        (oracleVisitedStates (N + 1) s)).run' c =
      (do
        let p ← ((S →ₒ S × O).randomOracle s).run c
        let rest ← (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
          (oracleVisitedStates N p.1.1)).run' p.2
        pure (s ::ᵥ rest)) := by
  rw [oracleVisitedStates]
  simp only [simulateQ_bind, simulateQ_prfIdealQueryImpl_functionQuery, StateT.run'_bind']
  refine bind_congr fun a : (S × O) × (S →ₒ S × O).QueryCache => ?_
  obtain ⟨⟨s', out⟩, c'⟩ := a
  simp [StateT.run'_eq]

/-- Cache-miss form of the lazy random oracle on input `s`: a fresh uniform draw `u : S × O`,
returned together with the cache extended by `s ↦ u`. -/
private lemma randomOracle_run_of_none (s : S) (c : (S →ₒ S × O).QueryCache) (hc : c s = none) :
    ((S →ₒ S × O).randomOracle s).run c
      = (fun u => (u, c.cacheQuery s u)) <$> ($ᵗ (S × O)) := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc]; rfl

/-- Cache-miss recursion for the generalized collision experiment. When `s` is uncached, the bad
event on the length-`N + 1` visited chain splits into the fresh draw at `s` (extending the cache by
`s`) followed by the bad event on the length-`N` sub-chain run against the extended cache. The
just-visited state `s` is folded into the cache, so the two bad events match pointwise. -/
private lemma genCollisionExperiment_succ_of_none (N : ℕ) (s : S) (c : (S →ₒ S × O).QueryCache)
    (hc : c s = none) :
    genCollisionExperiment (N + 1) s c =
      (do let p ← $ᵗ (S × O); genCollisionExperiment N p.1 (c.cacheQuery s p)) := by
  rw [genCollisionExperiment, simulateQ_oracleVisitedStates_succ_run',
    randomOracle_run_of_none s c hc]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun a => bind_congr fun b => ?_
  rw [genCollisionExperiment]
  refine bind_congr fun rest => ?_
  congr 1
  rw [decide_eq_decide, List.Vector.toList_cons]
  -- pointwise equivalence of the two bad events, using `c s = none`.
  have hkey : ∀ x : S,
      (c.cacheQuery s (a, b)).isCached x = true ↔ (x = s ∨ c.isCached x = true) := by
    intro x
    by_cases hx : x = s
    · subst hx; simp
    · rw [QueryCache.isCached_cacheQuery_of_ne c (a, b) hx]; simp [hx]
  have hcs : c.isCached s = false := by simp [QueryCache.isCached, hc]
  have hrest : (∃ x ∈ rest.toList, (c.cacheQuery s (a, b)).isCached x = true)
      ↔ (s ∈ rest.toList ∨ ∃ x ∈ rest.toList, c.isCached x = true) := by
    constructor
    · rintro ⟨x, hx, hxc⟩
      rcases (hkey x).1 hxc with rfl | hc'
      · exact Or.inl hx
      · exact Or.inr ⟨x, hx, hc'⟩
    · rintro (hs | ⟨x, hx, hxc⟩)
      · exact ⟨s, hs, (hkey s).2 (Or.inl rfl)⟩
      · exact ⟨x, hx, (hkey x).2 (Or.inr hxc)⟩
  have hhead : (∃ x ∈ (s :: rest.toList), c.isCached x = true)
      ↔ (∃ x ∈ rest.toList, c.isCached x = true) := by
    constructor
    · rintro ⟨x, hx, hxc⟩
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [hcs] at hxc; exact absurd hxc (by simp)
      · exact ⟨x, hx, hxc⟩
    · rintro ⟨x, hx, hxc⟩; exact ⟨x, List.mem_cons_of_mem _ hx, hxc⟩
  rw [hrest, List.nodup_cons, hhead]
  tauto

/-- Cache-hit determinism for the generalized collision experiment. When `s` is already cached, the
visited chain of length `N + 1` starts at `s`, which lies in the chain and is cached, so the bad
event always fires and the experiment returns `true` with probability one. -/
private lemma evalDist_genCollisionExperiment_succ_of_isCached (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) (hc : c.isCached s = true) :
    𝒟[genCollisionExperiment (N + 1) s c] {true} = 1 := by
  rw [← prEvent_eq_evalDist_singleton]
  refine prEvent_eq_one_of_forall_mem_support _ _ fun x hx => ?_
  rw [genCollisionExperiment, simulateQ_oracleVisitedStates_succ_run'] at hx
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hx
  obtain ⟨p, ⟨_, -, rest, -, hpeq⟩, rfl⟩ := hx
  subst hpeq
  rw [List.Vector.toList_cons, decide_eq_true (Or.inr ⟨s, List.mem_cons_self, hc⟩)]

/-- **Generalized per-seed core coupling.** For an arbitrary starting cache `c`, the total
variation distance between the lazy-random-oracle output chain (run from cache `c`) and a
uniformly random output vector is bounded by the generalized collision probability. Proved by
induction on the number of rounds: a fresh query produces an independent uniform block and the
cache grows by exactly the just-visited state, so the collision recursion closes; a repeated
query has already triggered the bad event, where the bound is trivially `1`. -/
lemma measureETVDist_seedOutputs_le_collision_gen (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) :
    (letI : MeasurableSpace (List.Vector O N) := ⊤;
      measureETVDist ((simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
          (oracleOutputs N s)).run' c) ($ᵗ (List.Vector O N))) ≤
      𝒟[genCollisionExperiment N s c] {true} := by
  have : Fintype O := Fintype.ofFinite O
  induction N generalizing s c with
  | zero =>
    let : MeasurableSpace (List.Vector O 0) := ⊤
    refine le_of_eq_of_le ((measureETVDist_eq_zero_iff _ _).2 ?_) zero_le
    simp only [oracleOutputs, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine Measure.ext_of_singleton fun y => ?_
    rw [List.Vector.eq_nil y, SampleableType.evalDist_uniformSample_singleton]
    simp [card_vector]
  | succ N ih =>
    let : MeasurableSpace (List.Vector O N) := ⊤
    let : MeasurableSpace (List.Vector O (N + 1)) := ⊤
    let : MeasurableSpace (S × O) := ⊤
    cases hc : c.isCached s with
    | false =>
      -- Cache miss: identical-until-bad coupling.
      have hcnone : c s = none := by
        simpa [QueryCache.isCached] using hc
      -- Both computations are binds over a freshly sampled pair `p : S × O`, sharing the head
      -- block `p.2` and differing only in the recursive tail.
      have hLHS :
          (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
              (oracleOutputs (N + 1) s)).run' c =
            (do let p ← $ᵗ (S × O);
                (fun v => p.2 ::ᵥ v) <$> (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
                  (oracleOutputs N p.1)).run' (c.cacheQuery s p)) := by
        rw [simulateQ_oracleOutputs_succ_run', randomOracle_run_of_none s c hcnone, bind_map_left]
        simp only [map_eq_bind_pure_comp, bind_pure_comp]
      -- Rewrite the goal as a distance between two binds over the shared pair `p : S × O`.
      calc measureETVDist ((simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
              (oracleOutputs (N + 1) s)).run' c) ($ᵗ (List.Vector O (N + 1)))
          = measureETVDist
              (($ᵗ (S × O)) >>= fun p =>
                (fun v => p.2 ::ᵥ v) <$> (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
                  (oracleOutputs N p.1)).run' (c.cacheQuery s p))
              (($ᵗ (S × O)) >>= fun p => (fun v => p.2 ::ᵥ v) <$> ($ᵗ (List.Vector O N))) := by
            rw [hLHS]
            simp only [measureETVDist, evalDist_uniformSample_vector_succ_pair (S := S) N]
        -- Bound each per-pair distance by the per-pair generalized collision probability.
        _ ≤ ∫⁻ p, 𝒟[genCollisionExperiment N p.1 (c.cacheQuery s p)] {true} ∂𝒟[$ᵗ (S × O)] :=
            measureETVDist_bind_bind_le_lintegral _ _ _ Measurable.of_discrete
              Measurable.of_discrete _ (Filter.Eventually.of_forall fun p =>
                (measureETVDist_map_le _ _ (fun v => p.2 ::ᵥ v) Measurable.of_discrete).trans
                  (ih p.1 (c.cacheQuery s p)))
        _ = 𝒟[genCollisionExperiment (N + 1) s c] {true} := by
            rw [genCollisionExperiment_succ_of_none N s c hcnone, evalDist_bind_apply_true]
    | true =>
      -- Cache hit: the bad event already fired, so the bound is trivially `1`.
      rw [evalDist_genCollisionExperiment_succ_of_isCached N s c hc]
      exact measureETVDist_le_one _ _

/-- **Per-seed core coupling.** For a fixed initial state, the total variation distance between
the lazy-random-oracle output chain and a uniformly random output vector is bounded by the
probability that the state chain revisits a state. This is the fundamental "identical until
bad" step: until the chain repeats, the lazy random oracle returns independent uniform blocks.

The empty-cache specialization of `measureETVDist_seedOutputs_le_collision_gen`. -/
lemma measureETVDist_seedOutputs_le_collision (seed : S) :
    (letI : MeasurableSpace (List.Vector O n) := ⊤;
      measureETVDist (seedOutputs n seed) ($ᵗ (List.Vector O n))) ≤
      𝒟[seedCollisionExperiment (O := O) n seed] {true} := by
  have heq :
      genCollisionExperiment (O := O) n seed ∅ = seedCollisionExperiment (O := O) n seed := by
    unfold genCollisionExperiment seedCollisionExperiment
    refine bind_congr fun states => ?_
    simp [QueryCache.isCached_empty]
  have h := measureETVDist_seedOutputs_le_collision_gen (O := O) n seed ∅
  rw [heq] at h
  exact h

/-- **Core coupling.** The total variation distance between the lazy-random-oracle output
chain and a uniformly random output vector is bounded by the state-collision probability.
This is the fundamental "identical until bad" step: until the state chain repeats, the lazy
random oracle returns independent uniform blocks, matching the ideal PRG distribution.

Obtained by averaging the per-seed bound `measureETVDist_seedOutputs_le_collision` over the
uniform initial state. -/
lemma measureETVDist_idealOutputs_le_collisionProb :
    (letI : MeasurableSpace (List.Vector O n) := ⊤;
      measureETVDist (idealOutputs (S := S) (O := O) n) ($ᵗ (List.Vector O n))) ≤
      collisionProb (S := S) (O := O) n := by
  let : MeasurableSpace (List.Vector O n) := ⊤
  let : MeasurableSpace S := ⊤
  rw [collisionProb, idealCollisionExperiment_eq_bind, idealOutputs_eq_bind,
    evalDist_bind_apply_true]
  calc measureETVDist (($ᵗ S) >>= seedOutputs n) ($ᵗ (List.Vector O n))
      = measureETVDist (($ᵗ S) >>= seedOutputs n) (($ᵗ S) >>= fun _ => $ᵗ (List.Vector O n)) := by
        simp only [measureETVDist, OracleComp.evalDist_bind_const]
    _ ≤ ∫⁻ seed, 𝒟[seedCollisionExperiment (O := O) n seed] {true} ∂𝒟[$ᵗ S] :=
        measureETVDist_bind_bind_le_lintegral _ _ _ Measurable.of_discrete Measurable.of_discrete _
          (Filter.Eventually.of_forall fun seed => measureETVDist_seedOutputs_le_collision seed)

/-- The gap between the ideal PRF and ideal PRG experiments is bounded by the
collision probability. This follows from the fundamental lemma of game playing:
when a lazy random function never receives the same input twice, its outputs are
independent uniform — matching the ideal PRG distribution exactly. The bound
comes from the probability that the state chain revisits some state.

*Proof outline (switching argument):*
1. Factor both experiments as: sample inputs to `adv`, then run `adv`.
2. In the ideal PRF world, the inputs come from a random-oracle chain.
3. In the ideal PRG world, the inputs are i.i.d. uniform.
4. Conditioned on no state collision, the random-oracle chain produces
   independent uniform outputs, so the two input distributions coincide.
5. By the "identical until bad" coupling (`measureETVDist_idealOutputs_le_collisionProb`),
   the total variation between the two input distributions is at most the collision
   probability.
6. By the data-processing inequality, running `adv` cannot increase the gap. -/
theorem prfIdealGap_le_collisionProb (adv : PRGAdversary (List.Vector O n)) :
    𝒟[PRFScheme.prfIdealExperiment (prfReduction (S := S) (O := O) n adv)].boolDist
        𝒟[PRGScheme.prgIdealExperiment adv] ≤
      collisionProb (S := S) (O := O) n := by
  let : MeasurableSpace (List.Vector O n) := ⊤
  rw [prfIdealExperiment_prfReduction_eq adv, prgIdealExperiment_eq_bind adv]
  calc 𝒟[idealOutputs n >>= adv].boolDist 𝒟[($ᵗ (List.Vector O n)) >>= adv]
      ≤ measureETVDist (idealOutputs n >>= adv) (($ᵗ (List.Vector O n)) >>= adv) :=
        Measure.absDiff_apply_le_etvDist _ _ (measurableSet_singleton true)
    _ ≤ measureETVDist (idealOutputs n) ($ᵗ (List.Vector O n)) :=
        measureETVDist_bind_le _ _ _ Measurable.of_discrete
    _ ≤ collisionProb (S := S) (O := O) n := measureETVDist_idealOutputs_le_collisionProb

/-- Security of the stream PRG obtained from a PRF: PRG distinguishing advantage is
bounded by the PRF advantage of the reduction plus the collision probability in the
ideal random-function world. -/
theorem security [SampleableType K]
    (hkey : prf.keygen =ᵈ ($ᵗ K : ProbComp K))
    (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgAdvantage (streamPRG prf n) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction (S := S) (O := O) n adv) +
      collisionProb (S := S) (O := O) n := by
  let prgReal := PRGScheme.prgRealExperiment (streamPRG prf n) adv
  let prfReal := PRFScheme.prfRealExperiment prf (prfReduction (S := S) (O := O) n adv)
  let prfIdeal := PRFScheme.prfIdealExperiment (prfReduction (S := S) (O := O) n adv)
  let prgIdeal := PRGScheme.prgIdealExperiment adv
  change 𝒟[prgReal].boolDist 𝒟[prgIdeal] ≤
    𝒟[prfReal].boolDist 𝒟[prfIdeal] + collisionProb (S := S) (O := O) n
  have hreal : 𝒟[prgReal] = 𝒟[prfReal] := prgRealExperiment_eq_prfRealExperiment hkey adv
  rw [hreal]
  exact (MeasureTheory.Measure.boolDist_triangle _ 𝒟[prfIdeal] _).trans
    (by gcongr; exact prfIdealGap_le_collisionProb adv)

/-- **Domain-invariance of the collision probability.** The generalized collision experiment reads
the starting cache only through its domain (`isCached`): on the good path cached values are never
inspected, and on a hit the bad event has already fired. Hence two caches with the same domain give
the same collision probability. -/
private lemma evalDist_genCollisionExperiment_eq_of_isCached_agree (N : ℕ) (s : S)
    (c c' : (S →ₒ S × O).QueryCache) (h : ∀ x, c.isCached x = c'.isCached x) :
    𝒟[genCollisionExperiment N s c] {true} = 𝒟[genCollisionExperiment N s c'] {true} := by
  induction N generalizing s c c' with
  | zero => simp [genCollisionExperiment]
  | succ N ih =>
    cases hc : c.isCached s with
    | true =>
      rw [evalDist_genCollisionExperiment_succ_of_isCached N s c hc,
        evalDist_genCollisionExperiment_succ_of_isCached N s c' (by rw [← h s]; exact hc)]
    | false =>
      have hc' : c'.isCached s = false := by rw [← h s]; exact hc
      have hcnone : c s = none := by simpa [QueryCache.isCached] using hc
      have hc'none : c' s = none := by simpa [QueryCache.isCached] using hc'
      rw [genCollisionExperiment_succ_of_none N s c hcnone,
        genCollisionExperiment_succ_of_none N s c' hc'none,
        evalDist_bind_apply_true, evalDist_bind_apply_true]
      refine lintegral_congr fun p => ih p.1 (c.cacheQuery s p) (c'.cacheQuery s p) fun x => ?_
      by_cases hx : x = s
      · subst hx; simp
      · rw [QueryCache.isCached_cacheQuery_of_ne c p hx,
          QueryCache.isCached_cacheQuery_of_ne c' p hx]
        exact h x

/-- **Generalized averaged birthday bound.** Averaging over the uniform initial state, the
generalized collision probability of the length-`N` chain starting from cache `c` is bounded by
`∑_{j < N} (|c| + j) / |S|`. Proved by induction on `N` (generalizing `c`): a cache miss draws a
fresh uniform state, growing the cache by one and shifting the bound; the union over already-cached
states contributes the leading `|c| / |S|` term. -/
private lemma evalDist_genCollisionExperiment_bind_le [Fintype S] (N : ℕ)
    (c : (S →ₒ S × O).QueryCache) :
    𝒟[(do let s ← $ᵗ S; genCollisionExperiment N s c)] {true} ≤
      ∑ j ∈ Finset.range N, (QueryCache.enncard c + (j : ℝ≥0∞)) * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace S := ⊤
  induction N generalizing c with
  | zero =>
    simp [genCollisionExperiment, oracleVisitedStates]
  | succ N ih =>
    obtain ⟨u₀⟩ : Nonempty (S × O) := inferInstance
    set C : ℝ≥0∞ := (Fintype.card S : ℝ≥0∞) with hC
    have hCne : C ≠ 0 := by
      rw [hC]; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hCtop : C ≠ ⊤ := by rw [hC]; exact ENNReal.natCast_ne_top _
    have hCcancel : C * C⁻¹ = 1 := ENNReal.mul_inv_cancel hCne hCtop
    set B : ℝ≥0∞ := ∑ j ∈ Finset.range N, (QueryCache.enncard c + 1 + (j : ℝ≥0∞)) * C⁻¹ with hB
    -- Termwise bound on the per-state collision probability.
    have hterm : ∀ s : S, 𝒟[genCollisionExperiment (N + 1) s c] {true} ≤
        (if c.isCached s then (1 : ℝ≥0∞) else 0) + B := by
      intro s
      cases hcs : c.isCached s with
      | true =>
        rw [evalDist_genCollisionExperiment_succ_of_isCached N s c hcs, ite_eq_left rfl]
        exact le_self_add
      | false =>
        rw [ite_eq_right (by simp), zero_add]
        have hcnone : c s = none := by simpa [QueryCache.isCached] using hcs
        rw [genCollisionExperiment_succ_of_none N s c hcnone]
        -- Replace each fresh cache value by a fixed one (domain invariance), then drop the
        -- unused output coordinate.
        have hdom :
            𝒟[(($ᵗ (S × O)) >>= fun p => genCollisionExperiment N p.1 (c.cacheQuery s p))] {true}
              = 𝒟[(($ᵗ (S × O)) >>= fun p =>
                  genCollisionExperiment N p.1 (c.cacheQuery s u₀))] {true} := by
          rw [evalDist_bind_apply_true, evalDist_bind_apply_true]
          refine lintegral_congr fun p =>
            evalDist_genCollisionExperiment_eq_of_isCached_agree N p.1 _ _ fun x => ?_
          by_cases hx : x = s
          · subst hx; simp
          · rw [QueryCache.isCached_cacheQuery_of_ne c p hx,
              QueryCache.isCached_cacheQuery_of_ne c u₀ hx]
        rw [hdom, SampleableType.evalDist_uniformSample_prod_bind_fst
          (fun s' => genCollisionExperiment N s' (c.cacheQuery s u₀))]
        refine le_trans (ih (c.cacheQuery s u₀)) (le_of_eq ?_)
        rw [hB]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [enncard_cacheQuery_of_none c s u₀ hcnone]
    calc 𝒟[(do let s ← $ᵗ S; genCollisionExperiment (N + 1) s c)] {true}
        = ∑ s : S, 𝒟[genCollisionExperiment (N + 1) s c] {true} * C⁻¹ := by
          rw [evalDist_bind_apply_true, lintegral_fintype]
          simp_rw [SampleableType.evalDist_uniformSample_singleton, ← hC]
      _ ≤ ∑ s : S, ((if c.isCached s then (1 : ℝ≥0∞) else 0) + B) * C⁻¹ :=
          Finset.sum_le_sum fun s _ => mul_le_mul_left (hterm s) _
      _ = QueryCache.enncard c * C⁻¹ + B := by
          simp_rw [add_mul, Finset.sum_add_distrib]
          congr 1
          · rw [enncard_eq_sum_isCached, Finset.sum_mul]
          · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm B, ← mul_assoc,
              ← hC, hCcancel, one_mul]
      _ = ∑ j ∈ Finset.range (N + 1), (QueryCache.enncard c + (j : ℝ≥0∞)) * C⁻¹ := by
          rw [Finset.sum_range_succ', hB]
          rw [Nat.cast_zero, add_zero]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring_nf

/-- **Birthday bound for the state-collision probability.** Over `n` rounds of the lazy random
oracle chain, each freshly sampled state is uniform over `S`, so the probability that the chain
revisits a state is at most `n·(n-1) / (2·|S|)` by a union bound over the at most `C(n,2)` pairs. -/
theorem collisionProb_le_birthday [Fintype S] (n : ℕ) :
    collisionProb (S := S) (O := O) n ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * (Fintype.card S : ℝ≥0∞)) := by
  -- The collision probability equals the empty-cache averaged collision probability.
  have hseed : ∀ seed : S,
      genCollisionExperiment (O := O) n seed ∅ = seedCollisionExperiment (O := O) n seed := by
    intro seed
    unfold genCollisionExperiment seedCollisionExperiment
    refine bind_congr fun states => ?_
    simp [QueryCache.isCached_empty]
  have hcomp : ((do let s ← $ᵗ S; genCollisionExperiment (O := O) n s ∅) : ProbComp Bool) =
      idealCollisionExperiment (S := S) (O := O) n := by
    rw [idealCollisionExperiment_eq_bind]
    exact bind_congr hseed
  -- Bound the collision probability by the Gauss sum, then collapse it.
  rw [collisionProb, ← hcomp]
  refine le_trans (evalDist_genCollisionExperiment_bind_le n ∅) (le_of_eq ?_)
  simp only [QueryCache.enncard_empty, zero_add]
  exact ENNReal.gauss_sum_inv_eq n (Fintype.card S : ℝ≥0∞)

/-- **Concrete security of the stream PRG.** The PRG distinguishing advantage is bounded by the
PRF advantage of the reduction plus the birthday term `n·(n-1) / (2·|S|)`, obtained by combining
`security` with `collisionProb_le_birthday`. -/
theorem security_birthday [Fintype S] [SampleableType K]
    (hkey : prf.keygen =ᵈ ($ᵗ K : ProbComp K))
    (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgAdvantage (streamPRG prf n) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction (S := S) (O := O) n adv) +
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * (Fintype.card S : ℝ≥0∞)) :=
  (security hkey adv).trans (by gcongr; exact collisionProb_le_birthday n)

end streamPRG

end PRGfromPRF
