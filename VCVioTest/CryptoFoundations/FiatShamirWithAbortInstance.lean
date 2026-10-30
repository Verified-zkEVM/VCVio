/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A fully discharged instance of the Fiat-Shamir-with-aborts CMA-to-NMA bound

Non-vacuity witness for `FiatShamirWithAbort.euf_cma_to_nma`: a toy identification scheme and
a concrete adversary at which every hypothesis of the theorem is proved and the statistical loss
`cmaToNmaLoss` is strictly below `1`.

The toy has commitments uniform in `Fin (n + 1)`, never aborts and has an exact simulator, so the
parameters are `ε = 1/(n+1)`, `p = 0`, `ζ_zk = 0` and `δ = 0`. The adversary makes one signing
query and no hash query (`qS = 1`, `qH = 0`), so the loss is
`2·1·1·ε + 1·ε·2/2 = 3/(n+1)`. At `n + 1 = 8` this is `3/8`.

The managed-RO NMA advantage of the reduction on this adversary is computed exactly
(`managedRoNmaAdvantage_toy`, value `1/2`), so at eight commitments the right-hand side of the
instance is `7/8` and the instance yields the closed bound `unforgeableAdvantage ≤ 7/8`
(`toy_unforgeableAdvantage_eight_le`), which the trivial bound `advantage ≤ 1` does not.

The scheme itself is insecure (a forger can answer any challenge by querying the hash); nothing
here is a security statement. The point is that the hypotheses of the headline theorem are
jointly satisfiable at a point where its loss is below `1`.
-/

public section

open OracleComp OracleSpec ENNReal FiatShamirWithAbort

namespace VCVioTest.FiatShamirWithAbortInstance

variable (n : ℕ)

/-! ## The toy identification scheme -/

/-- Toy identification scheme with a large commitment space: the commitment is uniform in
`Fin (n + 1)`, the prover never aborts and echoes the challenge, and verification accepts exactly
when the response equals the challenge. -/
def toyIds : IdenSchemeWithAbort Unit Unit (Fin (n + 1)) Unit Bool Bool (fun _ _ => true) where
  commit _ _ := (fun w => (w, ())) <$> ($ᵗ Fin (n + 1))
  respond _ _ _ c := pure (some c)
  verify _ _ c z := decide (z = c)

/-- The trivial key relation on `Unit`. -/
def toyHr : GenerableRelation Unit Unit (fun _ _ => true) where
  gen := pure ((), ())
  gen_sound _ _ _ := rfl

/-- The exact simulator of `toyIds`'s honest transcripts: a uniform commitment and a uniform
challenge echoed as the response, never aborting. -/
def toySim : Unit → ProbComp (Option (Fin (n + 1) × Bool × Bool)) := fun _ => do
  let w ← $ᵗ Fin (n + 1)
  let c ← $ᵗ Bool
  pure (some (w, c, c))

/-- The toy scheme in the random-oracle model, on `Bool` messages with a single signing
attempt. -/
abbrev toySig := FiatShamirWithAbort.inROM (toyIds n) toyHr Bool 1

/-- The oracle family seen by a CMA adversary against `toySig`: uniform selection, the random
oracle on `(message, commitment)` pairs, and the signing oracle. -/
abbrev advSpec :=
  (unifSpec + (Bool × Fin (n + 1) →ₒ Bool)) + (Bool →ₒ Option (Fin (n + 1) × Bool))

/-- The adversary: request one signature on `false` and output it as a forgery on `true`. -/
def toyAdv : SignatureAlg.UnforgeableAdversary (toySig n) where
  main _ := do
    let σ ← (advSpec n).query (.inr false)
    pure (true, σ)

/-! ## The hypotheses of `euf_cma_to_nma` -/

/-- `toySim` is a perfect simulator, so HVZK holds with `ζ_zk = 0`. -/
theorem toyIds_hvzk : (toyIds n).HVZK (toySim n) (ENNReal.ofReal 0) := by
  rw [ENNReal.ofReal_zero, ← IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero]
  intro _ _ _
  have h : (toyIds n).honestExecution () () = toySim n () := by
    simp [IdenSchemeWithAbort.honestExecution, toyIds, toySim]
  rw [h]

/-- Every commitment is guessed with probability `1/(n+1)`. -/
theorem toyIds_guess (cm : Fin (n + 1)) :
    Pr{let x ← Prod.fst <$> (toyIds n).commit () ()}[x = cm] ≤
      ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
  have h : Prod.fst <$> (toyIds n).commit () () = $ᵗ Fin (n + 1) := by
    simp [toyIds]
  rw [h, SampleableType.prEvent_uniformSample_eq_singleton]
  simp only [Fintype.card_fin, one_div,
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < n + 1)]
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; rfl, ENNReal.ofReal_natCast]

/-- The toy prover never aborts. -/
theorem toyIds_abort :
    Pr{let x ← (toyIds n).honestExecution () ()}[x = none] ≤ ENNReal.ofReal 0 := by
  simp [IdenSchemeWithAbort.honestExecution, toyIds]

/-- The adversary makes one signing query and no hash query. -/
theorem toyAdv_queryBound (pk : Unit) :
    FiatShamir.signHashQueryBound Bool
      (S' := Option (Fin (n + 1) × Bool)) (oa := (toyAdv n).main pk) 1 0 := by
  simp [FiatShamir.signHashQueryBound, toyAdv]

/-! ## The instance -/

/-- At `qS = 1`, `qH = 0`, `ε = 1/(n+1)`, `p = ζ_zk = δ = 0`, the two collision summands of
`cmaToNmaLoss` are `2/(n+1)` and `1/(n+1)` and the HVZK and bad-key summands vanish. -/
theorem cmaToNmaLoss_toy :
    cmaToNmaLoss 1 0 (1 / (n + 1 : ℝ)) 0 0 0 zero_lt_one = 3 / (n + 1) := by
  norm_num [cmaToNmaLoss]
  ring

/-- `euf_cma_to_nma` at the toy scheme and adversary, with every hypothesis discharged: the
EUF-CMA advantage of `toyAdv` is at most the managed-RO NMA advantage of the reduction plus a
loss of `3/(n+1)` (`cmaToNmaLoss_toy`). -/
theorem toy_euf_cma_to_nma :
    SignatureAlg.unforgeableAdvantage (runtime (Commit := Fin (n + 1)) (Chal := Bool) Bool)
        (toyAdv n) ≤
      SignatureAlg.managedRoNmaAdvantage (runtime (Commit := Fin (n + 1)) (Chal := Bool) Bool)
        (simulatedNmaAdv (toyIds n) toyHr Bool 1 (toySim n) (toyAdv n)) +
      ENNReal.ofReal (cmaToNmaLoss 1 0 (1 / (n + 1 : ℝ)) 0 0 0 zero_lt_one) :=
  euf_cma_to_nma (toyIds n) toyHr Bool 1 (toySim n) (toyAdv n) 0 le_rfl (toyIds_hvzk n) 1 0
    (1 / (n + 1 : ℝ)) 0 0 (by positivity) le_rfl le_rfl zero_lt_one (fun _ _ => True)
    (by simp [toyHr]) (fun _ _ _ cm => toyIds_guess n cm) (fun _ _ _ => toyIds_abort n)
    (toyAdv_queryBound n)

/-! ## The managed-RO NMA side -/

/-- The toy runtime is the caching random oracle over the empty cache. -/
lemma runtime_evalDist_apply_singleton
    (oa : OracleComp (unifSpec + (Bool × Fin (n + 1) →ₒ Bool)) Bool) (b : Bool) :
    (runtime (Commit := Fin (n + 1)) (Chal := Bool) Bool).evalDist oa {b} =
      Pr{let x ← ((simulateQ (unifFwdImpl (Bool × Fin (n + 1) →ₒ Bool) +
          (randomOracle : QueryImpl (Bool × Fin (n + 1) →ₒ Bool)
            (StateT (Bool × Fin (n + 1) →ₒ Bool).QueryCache ProbComp))) oa).run' ∅)}[x = b] := by
  rw [runtime_evalDist_eq_simulateQ_run', ← prEvent_eq_evalDist_singleton]

/-- The managed-RO NMA advantage of the reduction on `toyAdv` is `1/2` for every `n`: the
simulator never aborts, the reduction forwards the simulated signature on `false` as a forgery on
`true`, and since `simulatedNmaAdv` erases the forgery's verification point from the returned
cache, verification hashes `(true, w)` live and accepts exactly when the fresh bit equals the
echoed challenge. -/
theorem managedRoNmaAdvantage_toy :
    SignatureAlg.managedRoNmaAdvantage (runtime (Commit := Fin (n + 1)) (Chal := Bool) Bool)
      (simulatedNmaAdv (toyIds n) toyHr Bool 1 (toySim n) (toyAdv n)) = 1 / 2 := by
  classical
  rw [SignatureAlg.managedRoNmaAdvantage,
      managedRoNmaExperiment_simulatedNmaAdv_eq_eufNmaExperiment,
    SignatureAlg.eufNmaExperiment, runtime_evalDist_apply_singleton]
  refine (ENNReal.toReal_eq_toReal_iff' (prEvent_ne_top _) (by finiteness)).mp ?_
  simp only [simulatedEufNmaAdv, simulatedNmaAdv, toyAdv, toySim, toyIds, toyHr, firstSome,
    FiatShamirWithAbort,
    simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    StateT.run_bind, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    QueryImpl.add_apply_inr, simulateQ_unifSim_run, roSim.simulateQ_liftComp]
  simp only [randomOracle, QueryCache.cacheQuery]
  simp (config := { decide := true }) [unifFwdImpl.simulateQ_run,
    roSim.simulateQ_liftM_spec_query,
    StateT.run_bind, StateT.run_modifyGet, StateT.run_pure,
    OracleComp.prEvent_bind_eq_tsum_prEvent, Finset.filter_insert, Finset.filter_singleton,
    apply_ite Finset.card, Finset.card_singleton, Finset.card_empty]
  simp (disch := finiteness) [Finset.filter_eq', ENNReal.toReal_mul, ENNReal.toReal_add,
    ENNReal.toReal_inv]
  field_simp
  norm_num

/-! ## The instance at eight commitments -/

/-- With eight commitments the loss is `3/8`. -/
theorem cmaToNmaLoss_toy_eight :
    cmaToNmaLoss 1 0 (1 / 8 : ℝ) 0 0 0 zero_lt_one = 3 / 8 := by
  norm_num [cmaToNmaLoss]

/-- With eight commitments the loss is strictly below `1`. -/
theorem cmaToNmaLoss_toy_eight_lt_one :
    cmaToNmaLoss 1 0 (1 / 8 : ℝ) 0 0 0 zero_lt_one < 1 := by
  rw [cmaToNmaLoss_toy_eight]
  norm_num

/-- `euf_cma_to_nma` at the toy scheme with commitments in `Fin 8`, every hypothesis
discharged, at loss `3/8` (`cmaToNmaLoss_toy_eight`). -/
theorem toy_euf_cma_to_nma_eight :
    SignatureAlg.unforgeableAdvantage (runtime (Commit := Fin 8) (Chal := Bool) Bool)
        (toyAdv 7) ≤
      SignatureAlg.managedRoNmaAdvantage (runtime (Commit := Fin 8) (Chal := Bool) Bool)
        (simulatedNmaAdv (toyIds 7) toyHr Bool 1 (toySim 7) (toyAdv 7)) +
      ENNReal.ofReal (cmaToNmaLoss 1 0 (1 / 8 : ℝ) 0 0 0 zero_lt_one) := by
  have h := toy_euf_cma_to_nma 7
  norm_num at h
  exact h

/-- Closed consequence at eight commitments: the right-hand side of `toy_euf_cma_to_nma_eight` is
`1/2 + 3/8 = 7/8` (`managedRoNmaAdvantage_toy`, `cmaToNmaLoss_toy_eight`), so the instance is not
implied by the trivial bound `unforgeableAdvantage ≤ 1`. -/
theorem toy_unforgeableAdvantage_eight_le :
    SignatureAlg.unforgeableAdvantage (runtime (Commit := Fin 8) (Chal := Bool) Bool)
        (toyAdv 7) ≤ 7 / 8 := by
  have h := toy_euf_cma_to_nma_eight
  rw [managedRoNmaAdvantage_toy, cmaToNmaLoss_toy_eight] at h
  refine h.trans (le_of_eq ((ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp ?_))
  simp (disch := finiteness) [ENNReal.toReal_add, ENNReal.toReal_div]
  norm_num

end VCVioTest.FiatShamirWithAbortInstance
