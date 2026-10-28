/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
 # Uniform bases from a generator oracle

Querying a lazy random oracle at distinct labels gives a uniform basis. The label domain need
not be finite, and the oracle may already contain answers away from these labels.
-/

public section

open OracleComp OracleSpec

namespace DiscreteLogRelation

variable {ι D G : Type}

/-- Query a finite tuple of labels in index order. -/
@[expose] def queryFin : (n : ℕ) → (Fin n → D) → OracleComp (D →ₒ G) (Fin n → G)
  | 0, _ => pure Fin.elim0
  | n + 1, labels => do
    let g ← (D →ₒ G).query (labels 0)
    let gs ← queryFin n (fun i => labels i.succ)
    pure (Fin.cons g gs)

private theorem queryFin_uniform [DecidableEq D] [SampleableType G]
    (n : ℕ) (labels : Fin n → D) (hinj : Function.Injective labels)
    (cache : (D →ₒ G).QueryCache) (hfresh : ∀ i, cache (labels i) = none) :
    (simulateQ randomOracle (queryFin n labels)).run' cache =ᵈ ($ᵗ (Fin n → G)) := by
  induction n generalizing cache with
  | zero =>
    apply EvalDistEq.of_forall_prEvent_eq
    intro p
    have hp : p = fun _ => p Fin.elim0 := funext fun x =>
      congrArg p (Subsingleton.elim x Fin.elim0)
    rw [hp]
    simp only [queryFin, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    simp only [← bind_pure_comp, OracleComp.prEvent_bind_const]
  | succ n ih =>
    have he : (simulateQ randomOracle (queryFin (n + 1) labels)).run' cache =
        (do
          let g ← $ᵗ G
          let gs ← (simulateQ randomOracle (queryFin n (fun i => labels i.succ))).run'
            (cache.cacheQuery (labels 0) g)
          pure (Fin.cons g gs)) := by
      simp [queryFin, simulateQ_bind, StateT.run'_eq,
        StateT.run_bind, hfresh 0]
    rw [he]
    refine EvalDistEq.trans (my := (do
      let g ← $ᵗ G
      let gs ← $ᵗ (Fin n → G)
      pure (Fin.cons g gs) : ProbComp (Fin (n + 1) → G))) ?_ ?_
    · apply EvalDistEq.bind_right
      intro g
      have hf : ∀ i : Fin n, (cache.cacheQuery (labels 0) g) (labels i.succ) = none := by
        intro i
        rw [QueryCache.cacheQuery_of_ne _ _ (fun h => Fin.succ_ne_zero i (hinj h))]
        exact hfresh i.succ
      exact (ih (fun i => labels i.succ) (hinj.comp (Fin.succ_injective n))
        (cache.cacheQuery (labels 0) g) hf).bind_left
          (fun gs => (pure (Fin.cons g gs) : ProbComp (Fin (n + 1) → G)))
    · apply EvalDistEq.of_forall_prEvent_eq
      intro p
      simpa only [prEvent_norm] using
        SampleableType.prEvent_uniformSample_pair_of_bijective
          (g := fun (g : G) (gs : Fin n → G) => (Fin.cons g gs : Fin (n + 1) → G))
          (Fin.consEquiv (fun _ : Fin (n + 1) => G)).bijective p

/-- Query each basis label once, in the finite index type's canonical enumeration. -/
@[expose] noncomputable def queryBasis [Fintype ι] (labels : ι → D) :
    OracleComp (D →ₒ G) (ι → G) :=
  (fun gs i => gs (Fintype.equivFin ι i)) <$>
    queryFin (Fintype.card ι) (labels ∘ (Fintype.equivFin ι).symm)

/-- Distinct uncached generator labels give a uniformly distributed basis, even if the cache
contains unrelated entries. The output equality discards the final cache. -/
theorem queryBasis_evalDistEq_uniform [Fintype ι] [DecidableEq ι]
    [DecidableEq D] [SampleableType G]
    (labels : ι → D) (hinj : Function.Injective labels)
    (cache : (D →ₒ G).QueryCache) (hfresh : ∀ i, cache (labels i) = none) :
    (simulateQ randomOracle (queryBasis (G := G) labels)).run' cache =ᵈ ($ᵗ (ι → G)) := by
  have h := (queryFin_uniform (Fintype.card ι) (labels ∘ (Fintype.equivFin ι).symm)
    (hinj.comp (Fintype.equivFin ι).symm.injective) cache
    (fun i => hfresh _)).map (fun gs i => gs (Fintype.equivFin ι i))
  simp only [queryBasis, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at *
  refine h.trans (SampleableType.map_uniformSample_evalDistEq_of_bijective ?_)
  exact (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl G)).bijective

/-- A fresh lazy generator oracle produces the same basis distribution as independent uniform
sampling. Injectivity of the labels is the only restriction on their domain. -/
theorem queryBasis_empty_evalDistEq_uniform [Fintype ι] [DecidableEq ι]
    [DecidableEq D] [SampleableType G]
    (labels : ι → D) (hinj : Function.Injective labels) :
    (simulateQ randomOracle (queryBasis (G := G) labels)).run' ∅ =ᵈ ($ᵗ (ι → G)) :=
  queryBasis_evalDistEq_uniform labels hinj ∅ (by simp)

end DiscreteLogRelation
