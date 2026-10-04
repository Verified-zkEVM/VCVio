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

A secret `s : Fin 8` hides a single derivation at the public point `s` of a random oracle on `ℕ`.
Only public queries below `8` can hit an encoded point, so the budget charges those and leaves
every other query free. Each public point is encoded under at most one of the eight secrets, so
the averaged real-against-ideal bound applies with `ε = 8⁻¹`, here for a program that makes one
charged public query, one free public query and one derivation query.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace HiddenSeedToy

/-- Programs with uniform draws, a public random oracle on `ℕ` and one derivation query. -/
abbrev spec : OracleSpec ((ℕ ⊕ ℕ) ⊕ Unit) := (ℕ →ₒ Bool).withDerivations Unit Bool

/-- The secret `s` places the derivation at the public point `s`. -/
def enc : SecretEncoding (ℕ →ₒ Bool) (Fin 8) Unit Bool where
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
    Pr{let s ← $ᵗ Fin 8}[t ∈ Set.range (enc.enc s)] ≤ 8⁻¹ := by
  classical
  refine (prEvent_mono _ _ (fun s : Fin 8 ↦ (s : ℕ) = t) fun s (hs : t ∈ Set.range (enc.enc s)) ↦
    hs.choose_spec).trans ?_
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  have hcard : (Finset.univ.filter fun s : Fin 8 ↦ (s : ℕ) = t).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb ↦ Fin.ext <|
      ((Finset.mem_filter.1 ha).2).trans (Finset.mem_filter.1 hb).2.symm
  calc ((Finset.univ.filter fun s : Fin 8 ↦ (s : ℕ) = t).card : ℝ≥0∞) / ((8 : ℕ) : ℝ≥0∞)
      ≤ 1 / ((8 : ℕ) : ℝ≥0∞) := by gcongr; exact_mod_cast hcard
    _ = 8⁻¹ := by rw [one_div, Nat.cast_ofNat]

/-- Any event of the secret and the real game exceeds the ideal game by at most `q / 8`, for a
program making at most `q` public queries below `8`. -/
theorem prEvent_realImpl_le {α : Type} (oa : OracleComp spec α) {q : ℕ}
    (h : IsQueryBoundP oa IsLowQuery q) (P : Fin 8 → α × (ℕ →ₒ Bool).QueryCache → Prop) :
    Pr{let s ← $ᵗ Fin 8; let z ← (simulateQ (enc.realImpl s) oa).run ∅}[P s z] ≤
      Pr{
        let s ← $ᵗ Fin 8
        let z ← (simulateQ (SecretEncoding.idealImpl (ℕ →ₒ Bool) Unit Bool) oa).run (∅, ∅)}[
        P s (z.1, enc.merge s z.2)] + q * 8⁻¹ :=
  enc.prEvent_realImpl_le_add_mul prEvent_mem_range_enc_le (fun s _ ↦ s.isLt) h P

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
    Pr{let s ← $ᵗ Fin 8; let z ← (simulateQ (enc.realImpl s) prog).run ∅}[P s z] ≤
      Pr{
        let s ← $ᵗ Fin 8
        let z ← (simulateQ (SecretEncoding.idealImpl (ℕ →ₒ Bool) Unit Bool) prog).run (∅, ∅)}[
        P s (z.1, enc.merge s z.2)] + 8⁻¹ := by
  simpa only [Nat.cast_one, one_mul] using prEvent_realImpl_le prog isQueryBoundP_prog P

end HiddenSeedToy
