/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.DataEncapMech
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Multi-query IND-CPA checks for DEMs

Two toy DEMs on `Bool` with a uniform `Bool` key: the pad `k ^^ msg`, and the insecure DEM that
sends the message in the clear. A one-query adversary that outputs its ciphertext has
multi-query advantage `0` against the pad and `1` against the insecure DEM, and when the leakage
reveals the message its query is refused. A two-query adversary has advantage `1` against the
pad, since both challenges use the experiment's one key. A one-time adversary is embedded by
`toMultiQuery`, with its query budget and the advantage equality.
-/

public section

open OracleSpec OracleComp ENNReal MeasureTheory

namespace DEMIndCpaTest

/-- The one-bit pad: encryption and decryption add the key. -/
@[expose]
def pad : DEMScheme ProbComp Bool Bool Bool where
  encrypt k msg := pure (k ^^ msg)
  decrypt k c := pure (k ^^ c)

/-- An insecure DEM that ignores its key. -/
@[expose]
def clear : DEMScheme ProbComp Bool Bool Bool where
  encrypt _ msg := pure msg
  decrypt _ c := pure c

/-- A one-query adversary: it asks for the encryption of `false` or `true` and outputs the
ciphertext as its guess. -/
@[expose]
def echo (dem : DEMScheme ProbComp Bool Bool Bool) : dem.IND_CPA_Adversary := do
  let c? : Option Bool ← (unifSpec + LeftOrRight.spec Bool Bool).query (.inr (false, true))
  return c?.getD false

lemma echo_makesAtMostQueries (dem : DEMScheme ProbComp Bool Bool Bool) :
    (echo dem).MakesAtMostQueries 1 := by
  simp [DEMScheme.IND_CPA_Adversary.MakesAtMostQueries, echo]

lemma liftProbComp_probComp {α : Type} (x : ProbComp α) :
    ProbCompRuntime.probComp.liftProbComp x = x := rfl

/-- Against the insecure DEM, the guess is always the hidden bit. -/
lemma clear_game :
    clear.IND_CPA_Game ProbCompRuntime.probComp (fun _ => ()) (echo clear) =
      (do let _ ← $ᵗ Bool; let _ ← $ᵗ Bool; pure true) := by
  simp [DEMScheme.IND_CPA_Game, DEMScheme.IND_CPA_Experiment, echo, clear,
    liftProbComp_probComp]

/-- The echo adversary wins against the insecure DEM with advantage `1`. -/
theorem clear_advantage :
    clear.IND_CPA_Advantage ProbCompRuntime.probComp (fun _ => ()) (echo clear) = 1 := by
  rw [DEMScheme.IND_CPA_Advantage, clear_game, ProbCompRuntime.probComp_evalDist]
  simp [Measure.boolBias]

/-- Against the pad, the guess is the negated key, independent of the hidden bit. -/
lemma pad_game :
    pad.IND_CPA_Game ProbCompRuntime.probComp (fun _ => ()) (echo pad) =
      (do let _ ← $ᵗ Bool; (!·) <$> ($ᵗ Bool)) := by
  simp only [DEMScheme.IND_CPA_Game, DEMScheme.IND_CPA_Experiment, echo, pad,
    liftProbComp_probComp]
  refine bind_congr fun b => ?_
  simp only [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun k => ?_
  cases b <;> cases k <;> simp

/-- The echo adversary has advantage `0` against the pad. -/
theorem pad_advantage :
    pad.IND_CPA_Advantage ProbCompRuntime.probComp (fun _ => ()) (echo pad) = 0 := by
  have hnot : 𝒟[(!·) <$> ($ᵗ Bool : ProbComp Bool)] = 𝒟[($ᵗ Bool : ProbComp Bool)] :=
    (SampleableType.map_uniformSample_evalDistEq_of_bijective
      (Function.Involutive.bijective Bool.not_not)).evalDist_eq
  rw [DEMScheme.IND_CPA_Advantage, pad_game, ProbCompRuntime.probComp_evalDist]
  simp [Measure.boolBias, hnot]

/-- A two-query adversary against the pad: it asks for the encryption of `false` under both
branches, then of `false` or `true`, and outputs the sum of the two ciphertexts. -/
@[expose]
def xorTwo : pad.IND_CPA_Adversary := do
  let c₀ : Option Bool ← (unifSpec + LeftOrRight.spec Bool Bool).query (.inr (false, false))
  let c₁ : Option Bool ← (unifSpec + LeftOrRight.spec Bool Bool).query (.inr (false, true))
  return (c₀.getD false ^^ c₁.getD false)

lemma xorTwo_makesAtMostQueries : xorTwo.MakesAtMostQueries 2 := by
  simp [DEMScheme.IND_CPA_Adversary.MakesAtMostQueries, xorTwo]

/-- Both challenges are encrypted under the one key of the experiment, so the sum of the
ciphertexts is the hidden bit. -/
lemma pad_game_xorTwo :
    pad.IND_CPA_Game ProbCompRuntime.probComp (fun _ => ()) xorTwo =
      (do let _ ← $ᵗ Bool; let _ ← $ᵗ Bool; pure true) := by
  simp only [DEMScheme.IND_CPA_Game, DEMScheme.IND_CPA_Experiment, xorTwo, pad,
    liftProbComp_probComp]
  refine bind_congr fun b => ?_
  simp only [bind_assoc]
  refine bind_congr fun k => ?_
  cases b <;> cases k <;> simp

/-- Two queries break the pad: a key reused across challenges is a two-time pad. -/
theorem pad_advantage_xorTwo :
    pad.IND_CPA_Advantage ProbCompRuntime.probComp (fun _ => ()) xorTwo = 1 := by
  rw [DEMScheme.IND_CPA_Advantage, pad_game_xorTwo, ProbCompRuntime.probComp_evalDist]
  simp [Measure.boolBias]

/-- When the leakage reveals the whole message, the pair `(false, true)` is refused, so even
against the insecure DEM the guess does not depend on the hidden bit. -/
lemma clear_experiment_leak (b : Bool) :
    clear.IND_CPA_Experiment ProbCompRuntime.probComp id (echo clear) b =
      (do let _ ← $ᵗ Bool; pure false) := by
  simp [DEMScheme.IND_CPA_Experiment, echo, liftProbComp_probComp]

/-! ## One-time adversaries -/

/-- A one-time adversary against the pad: it chooses `false` and `true` and outputs the
ciphertext. -/
def echoOneTime : pad.IND_CPA_OneTime_Adversary where
  State := Unit
  chooseMessages := pure (false, true, ())
  distinguish _ c := pure c

example : echoOneTime.toMultiQuery.MakesAtMostQueries 1 :=
  DEMScheme.IND_CPA_OneTime_Adversary.toMultiQuery_makesAtMostQueries _

example :
    pad.IND_CPA_OneTime_Advantage ProbCompRuntime.probComp echoOneTime =
      pad.IND_CPA_Advantage ProbCompRuntime.probComp (fun _ => ()) echoOneTime.toMultiQuery :=
  DEMScheme.IND_CPA_OneTime_Advantage_eq_IND_CPA_Advantage _ _

example (b : Bool) :
    pad.IND_CPA_Experiment ProbCompRuntime.probComp (fun _ => ()) echoOneTime.toMultiQuery b =
      DEMScheme.IND_CPA_OneTime_Experiment ProbCompRuntime.probComp echoOneTime b :=
  DEMScheme.IND_CPA_Experiment_toMultiQuery _ _ _

end DEMIndCpaTest
