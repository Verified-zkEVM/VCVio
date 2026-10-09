/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Hidden-seed coupling on a small instance

A secret `s : Bool` hiding a single derivation at the public point `s` of a random oracle on
`Bool` shows that the flag bound `ε` times the expected count is attained. Each public point is
encoded under one of the two secrets (`ε = 2⁻¹`), and a single public query at `true` raises the
flag exactly under the secret `true`, so with probability `2⁻¹`. That program makes one public
query on every run, so its expected count is `1`. The bound needs no query budget: it applies as
stated to a program that makes its public query only on one outcome of a coin.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace HiddenSeedTight

/-- Programs with uniform draws, a public random oracle on `Bool` and one derivation query. -/
abbrev spec : OracleSpec ((ℕ ⊕ Bool) ⊕ Unit) := (Bool →ₒ Bool).withDerivations Unit Bool

/-- The secret `s` places the derivation at the public point `s`. -/
def E : SecretEncoding (Bool →ₒ Bool) Bool Unit Bool where
  enc s _ := s
  range_eq _ _ := rfl
  injective _ _ _ _ := rfl

/-- Public queries. -/
def IsPub : spec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred IsPub
  | .inl (.inl _) => inferInstanceAs (Decidable False)
  | .inl (.inr _) => inferInstanceAs (Decidable True)
  | .inr _ => inferInstanceAs (Decidable False)

/-- A single public query at `true`. -/
def prog : OracleComp spec Bool := liftM (spec.query (.inl (.inr true)))

/-- Each public point is encoded under one of the two secrets. -/
theorem prEvent_mem_range_enc_le (t : Bool) :
    Pr{let s ← $ᵗ Bool}[t ∈ Set.range (E.enc s)] ≤ 2⁻¹ := by
  refine (prEvent_mono _ _ (fun s : Bool ↦ s = t) fun s ⟨_, h⟩ ↦ h).trans ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool, Nat.cast_ofNat]

/-- The flag is raised exactly under the secret `true`, so with probability `2⁻¹`. -/
theorem prEvent_flaggedIdealImpl_eq :
    Pr{
      let s ← $ᵗ Bool
      let z ← (simulateQ (E.flaggedIdealImpl s) prog).run ((∅, ∅), false)}[z.2.2 = true] =
      2⁻¹ := by
  calc _ = Pr{
        let s ← $ᵗ Bool
        let _ ← (simulateQ (E.flaggedIdealImpl s) prog).run ((∅, ∅), false)}[s = true] := by
        simp only [prEvent_bind_bind_eq_lintegral_of_discrete]
        refine lintegral_congr fun s ↦ prEvent_congr_of_support _ _ _ fun z hz ↦ ?_
        simp only [prog, simulateQ_spec_query, SecretEncoding.flaggedIdealImpl,
          QueryImpl.extendState_apply, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨_, -, rfl⟩ := hz
        rw [Bool.false_or, E.encodedQuery_eq_true_iff]
        simp only [Sum.inl.injEq, Sum.inr.injEq, E, exists_const]
    _ = Pr{let s ← $ᵗ Bool}[s = true] := congrArg (· {True}) <|
        evalDist_bind_congr_of_support _ _ _ fun _ _ ↦ evalDist_bind_const _ _
    _ = 2⁻¹ := by
        rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool, Nat.cast_ofNat]

/-- The expected number of public queries of the program is `1`, so the flag bound `ε` times the
expected count gives `2⁻¹`, which by `prEvent_flaggedIdealImpl_eq` holds with equality. -/
example :
    Pr{
      let s ← $ᵗ Bool
      let z ← (simulateQ (E.flaggedIdealImpl s) prog).run ((∅, ∅), false)}[z.2.2 = true] ≤
      2⁻¹ := by
  have h := E.prEvent_flaggedIdealImpl_le_mul_expectedSimulatedQueryCount
    prEvent_mem_range_enc_le (p := IsPub) (fun _ _ ↦ trivial) prog
  have hc : expectedSimulatedQueryCount (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
      IsPub prog (∅, ∅) = 1 := by
    simp only [prog, expectedSimulatedQueryCount_query]
    rfl
  rwa [hc, mul_one] at h

/-- A program that makes its public query only on one outcome of a fair coin. -/
def progCoin : OracleComp spec Bool := do
  let b : Fin 2 ← liftM (spec.query (.inl (.inl 1)))
  if b = 0 then liftM (spec.query (.inl (.inr true))) else pure true

/-- The flag bound `ε` times the expected count needs no query budget. -/
example :
    Pr{
      let s ← $ᵗ Bool
      let z ← (simulateQ (E.flaggedIdealImpl s) progCoin).run ((∅, ∅), false)}[z.2.2 = true] ≤
      2⁻¹ * expectedSimulatedQueryCount (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
        IsPub progCoin (∅, ∅) :=
  E.prEvent_flaggedIdealImpl_le_mul_expectedSimulatedQueryCount prEvent_mem_range_enc_le
    (fun _ _ ↦ trivial) progCoin

end HiddenSeedTight
