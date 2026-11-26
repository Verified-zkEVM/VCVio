/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime

/-!
# One-time IND-CPA checks for public-key encryption

A toy scheme on `Bool` sends the message in the clear. The adversary that chooses `true` and
`false` and outputs the ciphertext has one-time advantage `1`: the branch that encrypts the first
message returns `true` and the other `false`, at distance `1` with no factor of two. It is not
admissible when the leakage is the message itself; every adversary is admissible for a constant
leakage. An adversary admissible for the identity leakage chooses equal messages, so the two
branches agree and its advantage is `0` against every scheme.
-/

public section

open OracleComp ENNReal MeasureTheory AsymmEncAlg

namespace AsymmEncOneTimeTest

/-- A scheme that ignores its keys and sends the message in the clear. -/
@[expose]
def clear : AsymmEncAlg ProbComp Bool Unit Unit Bool where
  keygen := pure ((), ())
  encrypt _ msg := pure msg
  decrypt _ c := pure (some c)

/-- Chooses `true` and `false` and outputs the ciphertext. -/
@[expose]
def echo : IND_CPA_OneTime_Adversary clear where
  State := Unit
  chooseMessages _ := pure (true, false, ())
  distinguish _ c := pure c

/-- The branch at `true` encrypts the first message. -/
example (b : Bool) : IND_CPA_OneTime_Experiment echo b = pure b := by
  cases b <;> simp [IND_CPA_OneTime_Experiment, echo, clear]

/-- Against the scheme that sends the message in the clear, `echo` has advantage `1`. -/
theorem clear_advantage_echo :
    IND_CPA_OneTime_Advantage clear ProbCompRuntime.probComp echo = 1 := by
  rw [IND_CPA_OneTime_Advantage_eq_boolDist]
  simp [IND_CPA_OneTime_Experiment, echo, clear, Measure.boolDist]

/-- `echo` chooses messages that differ, so it is not admissible when the leakage is the message
itself. -/
example : ¬ echo.IsAdmissible id := fun h =>
  Bool.true_eq_false_eq_False (h () (true, false, ()) (by simp [echo]; rfl))

/-- Every adversary is admissible for a constant leakage. -/
example (adv : IND_CPA_OneTime_Adversary clear) : adv.IsAdmissible fun _ => () :=
  fun _ _ _ => rfl

/-- An adversary admissible for the identity leakage has advantage `0` against every scheme. -/
theorem advantage_eq_zero_of_isAdmissible_id {M PK SK C : Type}
    {encAlg : AsymmEncAlg ProbComp M PK SK C} (adv : IND_CPA_OneTime_Adversary encAlg)
    (h : adv.IsAdmissible id) :
    IND_CPA_OneTime_Advantage encAlg ProbCompRuntime.probComp adv = 0 := by
  have hexp : IND_CPA_OneTime_Experiment adv true =ᵈ IND_CPA_OneTime_Experiment adv false := by
    unfold IND_CPA_OneTime_Experiment
    refine EvalDistEq.bind_right _ fun ⟨pk, _⟩ =>
      OracleComp.EvalDistEq.bind_congr_of_support _ fun ⟨m₁, m₂, _⟩ hz => ?_
    have hm : m₁ = m₂ := h pk _ hz
    simp [hm]
  rw [IND_CPA_OneTime_Advantage_eq_boolDist, hexp.evalDist_eq]
  simp [Measure.boolDist]

end AsymmEncOneTimeTest
