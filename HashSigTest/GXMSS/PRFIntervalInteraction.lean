/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedOracleInteraction
public import HashSigTest.GXMSS.PRFDerivedInterval

/-!
# Interval PRF interaction accounting

The real-game application retains a captured evaluator-key sampler. Repeated and inactive signing
requests still count in the source budget, and the displayed bound charges the whole retry budget.
-/

public section
namespace GXMSS.PRFInteractionProbe
open OracleComp OracleSpec SyncSignatureUnforgeability GXMSS.Probe GXMSS.IntervalMerkle
open GXMSS.Interval.PRFDerived.Unforgeability

/-- The captured key sampler derives a Boolean from a uniform three-way draw. -/
@[expose] def prf : PRFScheme Bool (GXMSS.Interval.PRFDerived.Query Unit Unit 3 1)
    (List ℕ × Bool) where
  keygen := do
    let i ← $ᵗ (Fin 3)
    pure (i.val == 0)
  eval := PRFIntervalProbe.evaluate

/-- One active request, its repetition and an inactive request are three signing calls. -/
@[expose] def adversary : Adversary unifSpec (PublicKey Unit (List ℕ)) (Fin 8) Unit
    (Signature Bool (List ℕ) 3 1) where
  forge _ := do
    let sig ← (unifSpec + signingSpec (Fin 8) Unit (Signature Bool (List ℕ) 3 1)).query
      (.inr (2, ()))
    let _ ← (unifSpec + signingSpec (Fin 8) Unit (Signature Bool (List ℕ) 3 1)).query
      (.inr (2, ()))
    let _ ← (unifSpec + signingSpec (Fin 8) Unit (Signature Bool (List ℕ) 3 1)).query
      (.inr (0, ()))
    pure (2, (), sig.getD ⟨false, fun _ => [], fun _ => []⟩)

/-- Repetition and inactivity do not reduce the all-request source count. -/
theorem three_requests : SigningQueryBound 3 adversary := by
  intro pk
  suffices ∀ sig : Option (Signature Bool (List ℕ) 3 1),
      IsQueryBoundP (pure (2, (), sig.getD ⟨false, fun _ => [], fun _ => []⟩) :
        OracleComp (unifSpec + signingSpec (Fin 8) Unit (Signature Bool (List ℕ) 3 1))
          (Forgery (Fin 8) Unit (Signature Bool (List ℕ) 3 1)))
        (fun q => q.isRight = true) 0 by
    simpa [adversary] using this
  intro sig
  trivial

/-- The first-request refusal behavior does not turn this into a one-request source program. -/
theorem not_one_request : ¬ SigningQueryBound 1 adversary := by
  intro h
  have hbudget := h ⟨[], ()⟩
  simp [adversary] at hbudget

/-- The named full-range budget contains no frontier term, including at height zero. -/
theorem full_count (h v qs K : ℕ) :
    functionQueryCount (Interval.full h) v qs K = 1 + 2 ^ h * v + qs * K := by
  have hc : Fintype.card (Subtree.FrontierNode (Interval.full h)) = 0 := Fintype.card_eq_zero
  simp only [functionQueryCount, keyMaterialQueryCount, Interval.length_full, hc, Nat.add_zero]

/-- The displayed budget charges three request budgets despite the repeated and inactive epochs. -/
theorem requests_charged :
    functionQueryCount PRFIntervalProbe.interior 1 3 3 =
      functionQueryCount PRFIntervalProbe.interior 1 1 3 + 6 := by
  unfold functionQueryCount
  omega

/-- The actual distinguisher obeys the named all-request function-query bound. -/
theorem native_budget :
    IsQueryBoundP (randgenPRFReduction (ChainProbe.traceInstance 3 3) enc
      PRFIntervalProbe.projection 3 PRFIntervalProbe.interior adversary)
      (fun q => q.isRight = true) (functionQueryCount PRFIntervalProbe.interior 1 3 3) :=
  randgenPRFReduction_functionQuery_bound (ChainProbe.traceInstance 3 3) enc
    PRFIntervalProbe.projection 3 3 PRFIntervalProbe.interior adversary three_requests

/-- The native real program uses the complete source game with the actual captured keygen. -/
theorem native_real :
    prf.prfRealExperiment (randgenPRFReduction (ChainProbe.traceInstance 3 3) enc
      PRFIntervalProbe.projection 3 PRFIntervalProbe.interior adversary) =
      strongValid (GXMSS.Interval.PRFDerived.scheme prf.keygen (ChainProbe.traceInstance 3 3)
        enc prf.eval PRFIntervalProbe.projection 3 PRFIntervalProbe.interior) <$>
      interaction (GXMSS.Interval.PRFDerived.scheme prf.keygen (ChainProbe.traceInstance 3 3)
        enc prf.eval PRFIntervalProbe.projection 3 PRFIntervalProbe.interior) adversary :=
  randgenPRFReduction_real_strong (ChainProbe.traceInstance 3 3) enc prf
    PRFIntervalProbe.projection 3 PRFIntervalProbe.interior adversary

end GXMSS.PRFInteractionProbe
