/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.PRF
public import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable

/-!
# Perfect pseudorandom functions

A PRF with a finite domain whose keyed function is distributed as a uniform function `D → R` has
PRF advantage `0` against every distinguisher (`PRFScheme.prfAdvantage_eq_zero_of_evalDistEq`).
The real experiment then samples a uniform table before the run, and the ideal experiment samples
the same table lazily during it.
-/

public section

open OracleComp OracleSpec

namespace PRFScheme

variable {K D R : Type}

/-- **A perfect PRF has advantage `0`.** If the function `prf.eval k` under a generated key `k` is
distributed as a uniform function on a finite domain, no distinguisher has an advantage. -/
theorem prfAdvantage_eq_zero_of_evalDistEq [DecidableEq D] [Finite D] [SampleableType R]
    [SampleableType (D → R)] (prf : PRFScheme K D R)
    (h : prf.eval <$> prf.keygen =ᵈ ($ᵗ (D → R) : ProbComp (D → R)))
    (adversary : PRFAdversary D R) : prf.prfAdvantage adversary = 0 := by
  let X : (D → R) → ProbComp Bool := fun g =>
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable ∅ g))) adversary
  have hreal : prf.prfRealExperiment adversary =ᵈ ($ᵗ (D → R)) >>= X := by
    refine EvalDistEq.trans ?_ (h.bind_left X)
    rw [bind_map_left]
    refine EvalDistEq.bind_right _ fun k => ?_
    have himpl : prf.prfRealQueryImpl k =
        unifFwdAnswerImpl (QueryImpl.ofFn (completeTable ∅ (prf.eval k))) := by
      funext t
      rcases t with n | x <;> rfl
    simp only [himpl]
    rfl
  have hideal : prfIdealExperiment adversary =ᵈ ($ᵗ (D → R)) >>= X :=
    let _ : MeasurableSpace Bool := ⊤
    EvalDistEq.of_evalDist_eq (evalDist_simulateQ_romImpl_run'_eq_completeTable adversary ∅)
  rw [prfAdvantage_eq_absDiff, ENNReal.absDiff_eq_zero]
  exact (hreal.prEvent_eq _).trans (hideal.prEvent_eq _).symm

end PRFScheme
