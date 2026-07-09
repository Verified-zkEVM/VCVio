/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.CryptoFoundations.SecExp

/-!
# Eavesdropping Indistinguishability for Symmetric Encryption

This file defines the two-phase eavesdropping (single-ciphertext) indistinguishability
experiment for `SymmEncAlg`: the adversary chooses two challenge messages, the challenger
encrypts one of them selected by a hidden uniform bit, and the adversary must identify the
bit from the ciphertext. Both standard presentations are provided:

- `SymmEncAlg.EavExp` / `SymmEncAlg.eavBiasAdvantage`: the guessing form, where the
  experiment reports whether the adversary identified the hidden bit.
- `SymmEncAlg.EavExpFixed` / `SymmEncAlg.eavDistAdvantage`: the distinguishing form,
  comparing the adversary's output distribution across the two fixed values of the bit.

`SymmEncAlg.eavBiasAdvantage_eq_eavDistAdvantage` shows the two advantages coincide
exactly (via the hidden-bit decomposition
`ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage`), so the two induced
security notions agree with no loss factor. This is the single-scheme core of the
equivalence between the guessing and distinguishing definitions of eavesdropping security
(Katz–Lindell, Definitions 3.9 and 3.10).

The adversary structure mirrors the two-phase design of `AsymmEncAlg.IND_CPA_Adv`.
-/

universe v

open OracleComp

namespace SymmEncAlg

variable {M K C : Type}

/-- Two-phase eavesdropping adversary against a symmetric encryption scheme: choose two
challenge messages (retaining state), then try to identify from a ciphertext which of the
two it encrypts. Mirrors `AsymmEncAlg.IND_CPA_Adv`, minus the public key. -/
structure EavAdversary (m : Type → Type v) [Monad m] (M C : Type) where
  /-- Adversary state passed between the two phases. -/
  State : Type
  /-- Choose the two challenge messages. -/
  chooseMessages : m (M × M × State)
  /-- Guess which challenge message a ciphertext encrypts. -/
  distinguish : State → C → m Bool

variable (encAlg : SymmEncAlg ProbComp M K C) (adv : EavAdversary ProbComp M C)

/-- Eavesdropping indistinguishability experiment, guessing form: the adversary chooses
two messages, the challenger encrypts the one selected by a hidden uniform bit, and the
experiment reports whether the adversary identified the bit (`b = true` selects the
second chosen message). -/
def EavExp : ProbComp Bool := do
  let (m₀, m₁, s) ← adv.chooseMessages
  let k ← encAlg.keygen
  let b ← ($ᵗ Bool)
  let c ← encAlg.encrypt k (if b then m₁ else m₀)
  let b' ← adv.distinguish s c
  pure (b == b')

/-- Fixed-bit branch of the eavesdropping experiment, returning the adversary's output
bit rather than comparing it to the challenge bit. -/
def EavExpFixed (b : Bool) : ProbComp Bool := do
  let (m₀, m₁, s) ← adv.chooseMessages
  let k ← encAlg.keygen
  let c ← encAlg.encrypt k (if b then m₁ else m₀)
  adv.distinguish s c

/-- Bias advantage of the guessing experiment (Katz–Lindell Definition 3.9 form). -/
noncomputable def eavBiasAdvantage : ℝ := (EavExp encAlg adv).boolBiasAdvantage

/-- Distinguishing advantage between the two fixed-bit branches of the eavesdropping
experiment (Katz–Lindell Definition 3.10 form). -/
noncomputable def eavDistAdvantage : ℝ :=
  (EavExpFixed encAlg adv true).boolDistAdvantage (EavExpFixed encAlg adv false)

/-- The guessing bias of the eavesdropping experiment equals the distinguishing advantage
between its two fixed-bit branches: the hidden-bit decomposition of the experiment.
Single-scheme core of the equivalence of Katz–Lindell Definitions 3.9 and 3.10. -/
theorem eavBiasAdvantage_eq_eavDistAdvantage :
    eavBiasAdvantage encAlg adv = eavDistAdvantage encAlg adv := by
  let pref : ProbComp ((M × M × adv.State) × K) := do
    let ms ← adv.chooseMessages
    let k ← encAlg.keygen
    pure (ms, k)
  let real : (M × M × adv.State) × K → ProbComp Bool :=
    fun a => encAlg.encrypt a.2 a.1.2.1 >>= adv.distinguish a.1.2.2
  let rand : (M × M × adv.State) × K → ProbComp Bool :=
    fun a => encAlg.encrypt a.2 a.1.1 >>= adv.distinguish a.1.2.2
  have h := ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage pref real rand
  have hexp : EavExp encAlg adv = (do
      let a ← pref
      let b ← ($ᵗ Bool)
      let z ← if b then real a else rand a
      pure (b == z)) := by
    simp only [EavExp, pref, real, rand, monad_norm]
    refine bind_congr fun ms => ?_
    obtain ⟨m₀, m₁, s⟩ := ms
    refine bind_congr fun k => bind_congr fun b => ?_
    cases b <;> simp [monad_norm]
  have htrue : EavExpFixed encAlg adv true = (do
      let a ← pref
      real a) := by
    simp only [EavExpFixed, pref, real, monad_norm]
    refine bind_congr fun ms => ?_
    obtain ⟨m₀, m₁, s⟩ := ms
    simp [monad_norm]
  have hfalse : EavExpFixed encAlg adv false = (do
      let a ← pref
      rand a) := by
    simp only [EavExpFixed, pref, rand, monad_norm]
    refine bind_congr fun ms => ?_
    obtain ⟨m₀, m₁, s⟩ := ms
    simp [monad_norm]
  rw [eavBiasAdvantage, eavDistAdvantage, hexp, htrue, hfalse]
  exact h

end SymmEncAlg
