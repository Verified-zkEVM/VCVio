/-
Copyright (c) 2026 Skas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skas
-/

module

public import VCVio.CryptoFoundations.KeyEncapMech.ANO
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Non-vacuity check for ciphertext anonymity

A toy KEM on `Bool` whose ciphertext is the public key itself, with every encapsulation carrying
the same fixed shared key. An ANO-CPA adversary that compares the challenge ciphertext with the
second challenge public key recovers the hidden bit exactly when the two independently generated
public keys differ, which they do on two of the four equally likely keygen outcomes. When they
coincide it guesses `true`, which is right half the time. So the game returns `true` with
probability `3 / 4`, and the ANO-CPA advantage, the Boolean bias of the game, is exactly `1 / 2`.

The scheme is perfectly correct, and the adversary ignores the encapsulated key it is handed, so
the computation also witnesses that the key-revealing game does not trivialise the notion: the
advantage is capped below `1` by the key-collision probability, not by any restriction on what the
adversary may read.
-/

public section

open OracleSpec OracleComp ENNReal MeasureTheory

namespace KEMAnoTest

/-- A maximally non-anonymous KEM: the ciphertext is the public key, and every encapsulation
carries the fixed shared key `false`, which `decaps` returns exactly when the ciphertext matches
the secret key. -/
@[expose]
def tagKem : KEMScheme ProbComp Bool Bool Bool Bool where
  keygen := do
    let k ← $ᵗ Bool
    pure (k, k)
  encaps pk := pure (pk, false)
  decaps sk c := pure (if c = sk then some false else none)

/-- Reads the public key straight out of the challenge ciphertext and compares it with the second
challenge public key. The encapsulated key it is handed is ignored. -/
@[expose]
def tagAdv : tagKem.ANO_CPA_Adversary where
  State := Bool
  preChallenge _ pk1 := pure pk1
  postChallenge pk1 c _ := pure (c == pk1)

/-- The game is three independent uniform `Bool` draws — the two keypairs and the hidden bit —
followed by a comparison of the challenge ciphertext with the second public key. -/
lemma tagKem_game :
    tagKem.ANO_CPA_Game ProbCompRuntime.probComp tagAdv =
      (do
        let pk0 : Bool ← $ᵗ Bool
        let pk1 : Bool ← $ᵗ Bool
        let b : Bool ← $ᵗ Bool
        pure (b == ((if b then pk1 else pk0) == pk1)) : ProbComp Bool) := by
  simp only [KEMScheme.ANO_CPA_Game, tagKem, tagAdv, ProbCompRuntime.probComp_liftProbComp,
    bind_assoc, pure_bind]

set_option maxHeartbeats 1600000 in
-- Peeling three nested `evalDist_bind_of_discrete` layers and evaluating the resulting
-- eight-term `ℝ≥0∞` sum exceeds the default heartbeat budget.
/-- The game returns `true` with probability `3 / 4`: the ciphertext reveals the hidden bit when
the two public keys differ, on two of the four keygen outcomes, and the guess is right half the
time on the other two. -/
lemma tagKem_game_true :
    𝒟[tagKem.ANO_CPA_Game ProbCompRuntime.probComp tagAdv] {true} = 3 / 4 := by
  rw [tagKem_game]
  simp only [evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable,
    lintegral_fintype, Fintype.sum_bool]
  simp only [evalDist_pure, Measure.dirac_apply' _ (measurableSet_singleton true),
    SampleableType.evalDist_uniformSample_singleton, Fintype.card_bool]
  simp
  ring_nf
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num

/-- The game returns `false` with probability `1 / 4`. -/
lemma tagKem_game_false :
    𝒟[tagKem.ANO_CPA_Game ProbCompRuntime.probComp tagAdv] {false} = 1 / 4 := by
  set q : ℝ≥0∞ := 𝒟[tagKem.ANO_CPA_Game ProbCompRuntime.probComp tagAdv] {false} with hq
  have hqne : q ≠ ⊤ := by rw [hq]; exact measure_ne_top _ _
  have hsplit : (3 : ℝ≥0∞) / 4 + q = 1 := by
    have := Measure.apply_true_add_apply_false_eq_one
      (𝒟[tagKem.ANO_CPA_Game ProbCompRuntime.probComp tagAdv])
    rw [tagKem_game_true, ← hq] at this
    exact this
  have hreal : q.toReal = 1 / 4 := by
    have := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add (ENNReal.div_ne_top (by norm_num) (by norm_num)) hqne,
      ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one] at this
    norm_num at this ⊢
    linarith
  rw [← ENNReal.ofReal_toReal hqne, hreal]
  simp

/-- The tag adversary has ANO-CPA advantage exactly `1 / 2`. -/
theorem tagAdvantage :
    tagKem.ANO_CPA_Advantage ProbCompRuntime.probComp tagAdv = 1 / 2 := by
  rw [tagKem.ANO_CPA_Advantage_eq_game_bias, ProbCompRuntime.probComp_evalDist,
    ← ENNReal.toReal_eq_toReal_iff' (Measure.boolBias_ne_top _)
      (ENNReal.div_ne_top (by norm_num) (by norm_num)),
    Measure.toReal_boolBias, tagKem_game_true, tagKem_game_false,
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

end KEMAnoTest
