/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ.FinMOfFn

/-!
# Finite fresh-query families

Distinct, initially uncached random-oracle inputs return an ordered family of independent uniform
answers. The equality keeps the finite monadic program, rather than identifying only its measure.
-/

public section

open OracleComp OracleSpec

namespace OracleComp

/-- A finite family of distinct fresh inputs draws one independent uniform response per input.
Only the final cache is discarded; the response order is the index order of `queries`. -/
theorem run'_fin_mOfFn_randomOracle_of_fresh {D R : Type} [DecidableEq D] [SampleableType R]
    (n : ℕ) (queries : Fin n → D) (hinj : Function.Injective queries)
    (cache : (D →ₒ R).QueryCache) (hfresh : ∀ i, cache (queries i) = none) :
    (simulateQ (randomOracle (spec := D →ₒ R))
      (Fin.mOfFn n fun i => (liftM ((D →ₒ R).query (queries i)) :
        OracleComp (D →ₒ R) R))).run' cache =
      Fin.mOfFn n (fun _ => ($ᵗ R)) := by
  induction n generalizing cache with
  | zero => simp
  | succ n ih =>
    simp only [Fin.mOfFn, simulateQ_bind]
    rw [StateT.run'_bind', simulateQ_spec_query, randomOracle.run_eq, hfresh 0]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro response
    have htail : Function.Injective (fun i : Fin n => queries i.succ) :=
      fun _ _ eq => Fin.succ_injective n (hinj eq)
    have hfreshTail : ∀ i : Fin n,
        (cache.cacheQuery (queries 0) response) (queries i.succ) = none := by
      intro i
      rw [QueryCache.cacheQuery_of_ne]
      · exact hfresh i.succ
      · intro eq
        exact Fin.succ_ne_zero i (hinj eq)
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
      map_bind, map_pure]
    have h := congrArg (fun program =>
        (Fin.cons (α := fun _ : Fin (n + 1) => R) response) <$> program)
      (ih (fun i => queries i.succ) htail
        (cache.cacheQuery (queries 0) response) hfreshTail)
    simpa [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc] using h

end OracleComp
