/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Examples.KatzLindell.SingleBit
import Examples.OneTimePad.Basic

/-!
# The One-Time Pad Is Eavesdropping-Secure

Sanity instance for the Katz–Lindell eavesdropping-security definitions: the one-time
pad family has *zero* advantage in the distinguishing game against every adversary —
efficient or not — because encrypting any two messages under a fresh uniform key gives
identical ciphertext distributions (`oneTimePad.cipherGivenMsg_equiv`). Perfect secrecy
therefore implies computational secrecy: `eavSecure_oneTimePad` discharges `EavSecure`
through the Definition 3.9 ↔ 3.10 game equality and `negligible_of_zero`, exercising
the full definitional pipeline end to end.
-/

open ENNReal OracleComp OracleSpec SymmEncAlg

namespace KatzLindell

/-- Any two fixed-bit branches of the eavesdropping experiment against the one-time pad
have the same distribution: per choice of challenge messages, the two branches are the
conditional ciphertext experiments composed with the same distinguisher, and those agree
by the XOR coupling `oneTimePad.cipherGivenMsg_equiv`. -/
theorem evalDist_privKEavFixed_oneTimePad
    (A : PPTEavAdversary (fun n => BitVec n) (fun n => BitVec n)) (b₁ b₂ : Bool) (n : ℕ) :
    𝒟[privKEavFixed (fun m => oneTimePad m) A b₁ n] =
      𝒟[privKEavFixed (fun m => oneTimePad m) A b₂ n] := by
  have key : ∀ (m₁ m₂ : BitVec n) (dis : BitVec n → ProbComp Bool),
      𝒟[do
        let k ← (oneTimePad n).keygen
        let c ← (oneTimePad n).encrypt k m₁
        dis c] =
      𝒟[do
        let k ← (oneTimePad n).keygen
        let c ← (oneTimePad n).encrypt k m₂
        dis c] := by
    intro m₁ m₂ dis
    have hcg : 𝒟[(oneTimePad n).PerfectSecrecyCipherGivenMsgExp m₁] =
        𝒟[(oneTimePad n).PerfectSecrecyCipherGivenMsgExp m₂] :=
      oneTimePad.cipherGivenMsg_equiv n m₁ m₂
    calc 𝒟[do
          let k ← (oneTimePad n).keygen
          let c ← (oneTimePad n).encrypt k m₁
          dis c]
        = 𝒟[(oneTimePad n).PerfectSecrecyCipherGivenMsgExp m₁ >>= dis] := by
          rw [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, bind_assoc]
      _ = 𝒟[(oneTimePad n).PerfectSecrecyCipherGivenMsgExp m₂ >>= dis] := by
          rw [evalDist_bind, evalDist_bind, hcg]
      _ = _ := by rw [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, bind_assoc]
  simp only [privKEavFixed, EavExpFixed, PPTEavAdversary.toEavAdversary]
  rw [evalDist_bind, evalDist_bind]
  refine bind_congr fun ms => ?_
  obtain ⟨m₀, m₁, s⟩ := ms
  exact key _ _ _

/-- Every adversary — polynomial time or not — has zero advantage in the distinguishing
form of the eavesdropping game against the one-time pad. -/
theorem eavDistGame_oneTimePad_advantage_eq_zero
    (A : PPTEavAdversary (fun n => BitVec n) (fun n => BitVec n)) (n : ℕ) :
    (eavDistGame (fun m => oneTimePad m)).advantage A n = 0 := by
  have h := evalDist_privKEavFixed_oneTimePad A true false n
  simp only [eavDistGame, ProbComp.boolDistAdvantage,
    OracleComp.probOutput_congr rfl h, sub_self, abs_zero, ENNReal.ofReal_zero]

/-- **The one-time pad is eavesdropping-secure**: perfect secrecy implies computational
secrecy, unconditionally — an end-to-end check that `EavSecure` is satisfiable. -/
theorem eavSecure_oneTimePad : EavSecure (fun n => oneTimePad n) := by
  rw [eavSecure_iff_distGame_secure]
  exact fun A _ => negligible_of_zero (eavDistGame_oneTimePad_advantage_eq_zero A)

-- Claim 3.11 instantiated at the one-time pad: no polynomial-time adversary predicts
-- any single bit of a uniform plaintext from its one-time-pad encryption. The whole
-- pipeline — definitions, reduction, and machine-level polynomial-time transfer —
-- discharges on a concrete scheme.
example (i : ℕ) :
    (predictBitGame (fun n => oneTimePad n) i).secureAgainst OracleComp.IsPolyTime :=
  secureAgainst_predictBitGame_of_eavSecure _
    (fun n => Computability.finEncodingBitVec n) eavSecure_oneTimePad i

end KatzLindell
