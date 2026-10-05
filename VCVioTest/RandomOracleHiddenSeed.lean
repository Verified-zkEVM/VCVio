/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Hidden-seed coupling on small instances

A secret `s : Fin 8` hides a single derivation at the public point `s` of a random oracle on `ℕ`.
Only public queries below `8` can hit an encoded point, so the budget charges those and leaves
every other query free. Each public point is encoded under at most one of the eight secrets, so
the averaged real-against-ideal bound applies with `ε = 8⁻¹`, here for a program that makes one
charged public query, one free public query and one derivation query.

A secret `s : Bool` hiding a single derivation at the public point `s` of a random oracle on
`Bool` shows that the flag bound `q * ε` is attained. Each public point is encoded under one of
the two secrets (`ε = 2⁻¹`), and a single public query at `true` (`q = 1`) raises the flag
exactly under the secret `true`, so with probability `2⁻¹ = q * ε`. That program makes one
public query on every run, so its expected count is `1` and the flag bound `ε` times the expected
count is attained as well. That bound needs no query budget: it applies as stated to a program
that makes its public query only on one outcome of a coin.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace HiddenSeedToy

/-- Programs with uniform draws, a public random oracle on `ℕ` and one derivation query. -/
abbrev spec : OracleSpec ((ℕ ⊕ ℕ) ⊕ Unit) := (ℕ →ₒ Bool).withDerivations Unit Bool

/-- The secret `s` places the derivation at the public point `s`. -/
def E : SecretEncoding (ℕ →ₒ Bool) (Fin 8) Unit Bool where
  enc s _ := s
  range_eq _ _ := rfl
  injective _ _ _ _ := rfl

/-- The public queries that can hit an encoded point: those below `8`. -/
def IsLowQuery : spec.Domain → Prop
  | .inl (.inr t) => t < 8
  | _ => False

instance : DecidablePred IsLowQuery
  | .inl (.inl _) => inferInstanceAs (Decidable False)
  | .inl (.inr t) => inferInstanceAs (Decidable (t < 8))
  | .inr _ => inferInstanceAs (Decidable False)

/-- Every public point is encoded under at most one of the eight secrets. -/
theorem prEvent_mem_range_enc_le (t : ℕ) :
    Pr{let s ← $ᵗ Fin 8}[t ∈ Set.range (E.enc s)] ≤ 8⁻¹ := by
  classical
  refine (prEvent_mono _ _ (fun s : Fin 8 ↦ (s : ℕ) = t) fun s ⟨_, h⟩ ↦ h).trans ?_
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  have hcard : (Finset.univ.filter fun s : Fin 8 ↦ (s : ℕ) = t).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb ↦ Fin.ext <|
      ((Finset.mem_filter.1 ha).2).trans (Finset.mem_filter.1 hb).2.symm
  calc ((Finset.univ.filter fun s : Fin 8 ↦ (s : ℕ) = t).card : ℝ≥0∞) / ((8 : ℕ) : ℝ≥0∞)
      ≤ 1 / ((8 : ℕ) : ℝ≥0∞) := by gcongr; exact_mod_cast hcard
    _ = 8⁻¹ := by rw [one_div, Nat.cast_ofNat]

/-- Any event of the secret and the real game exceeds the ideal game by at most `q / 8`, for a
program making at most `q` public queries below `8`. -/
theorem prEvent_realImpl_le_add_mul {α : Type} (oa : OracleComp spec α) {q : ℕ}
    (h : IsQueryBoundP oa IsLowQuery q) (P : Fin 8 → α × (ℕ →ₒ Bool).QueryCache → Prop) :
    Pr{let s ← $ᵗ Fin 8; let z ← (simulateQ (E.realImpl s) oa).run ∅}[P s z] ≤
      Pr{
        let s ← $ᵗ Fin 8
        let z ← (simulateQ (SecretEncoding.idealImpl (ℕ →ₒ Bool) Unit Bool) oa).run (∅, ∅)}[
        P s (z.1, E.merge s z.2)] + q * 8⁻¹ :=
  E.prEvent_realImpl_le_add_mul prEvent_mem_range_enc_le (fun s _ ↦ s.isLt) h P

/-- One charged public query, one free public query and one derivation query. -/
def prog : OracleComp spec Bool := do
  let a ← liftM (spec.query (.inl (.inr 3)))
  let _ ← liftM (spec.query (.inl (.inr 100)))
  let b ← liftM (spec.query (.inr ()))
  return a == b

/-- The program makes one public query below `8`. -/
theorem isQueryBoundP_prog : IsQueryBoundP prog IsLowQuery 1 := by
  simp only [prog, isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
  decide

/-- The real game of the program exceeds the ideal game by at most `8⁻¹` on any event. -/
example (P : Fin 8 → Bool × (ℕ →ₒ Bool).QueryCache → Prop) :
    Pr{let s ← $ᵗ Fin 8; let z ← (simulateQ (E.realImpl s) prog).run ∅}[P s z] ≤
      Pr{
        let s ← $ᵗ Fin 8
        let z ← (simulateQ (SecretEncoding.idealImpl (ℕ →ₒ Bool) Unit Bool) prog).run (∅, ∅)}[
        P s (z.1, E.merge s z.2)] + 8⁻¹ := by
  simpa only [Nat.cast_one, one_mul] using prEvent_realImpl_le_add_mul prog isQueryBoundP_prog P

end HiddenSeedToy

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

/-- The program makes one public query. -/
theorem isQueryBoundP_prog : IsQueryBoundP prog IsPub 1 := by
  simp only [prog, isQueryBoundP_query_iff]
  decide

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

/-- The flag bound `q * ε` applies here with `q = 1` and `ε = 2⁻¹`, and by
`prEvent_flaggedIdealImpl_eq` it holds with equality. -/
example :
    Pr{
      let s ← $ᵗ Bool
      let z ← (simulateQ (E.flaggedIdealImpl s) prog).run ((∅, ∅), false)}[z.2.2 = true] ≤
      (1 : ℕ) * 2⁻¹ :=
  E.prEvent_flaggedIdealImpl_le_mul prEvent_mem_range_enc_le (fun _ _ ↦ trivial)
    isQueryBoundP_prog

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
