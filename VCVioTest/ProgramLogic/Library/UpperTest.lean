/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.UpperRanked
public meta import VCVio.ProgramLogic.Tactics

/-!
# The upper reading: usage tests

A plain `Pr[E] ≤ ε` goal becomes a core triple by `rw [prEvent_le_iff_triple]`, which `vcgen`
decomposes with the registered and the explicitly passed rules; `upper_readback` returns the
verification conditions to `ℝ≥0∞`. Bad-event bounds through a stateful simulation go through the
union bound over queries.
-/

@[expose] public section

open ENNReal Std.WP OrderDual OracleSpec OracleComp OracleComp.ProgramLogic
open scoped OracleComp.Upper

set_option experimental.vcgen true

namespace VCVioTest.ProgramLogic.Library.Upper

open OracleComp.Upper

/-- A bound that holds on every path, by the registered rules alone. -/
example : ⦃ toDual 0 ⦄ (do let _ ← $ᵗ Bool; let c ← $ᵗ Bool; pure (c || true) : ProbComp Bool)
    ⦃ fun r => toDual (propInd (r = false)) ⦄ := by
  vcgen (errorOnMissingSpec := true)
  simp [propInd]

/-- The same, by a bare `vcgen`: with `VCVio.ProgramLogic.Tactics` imported, the goal still
reaches core's VC generator. -/
example : ⦃ toDual 0 ⦄ (do let _ ← $ᵗ Bool; let c ← $ᵗ Bool; pure (c || true) : ProbComp Bool)
    ⦃ fun r => toDual (propInd (r = false)) ⦄ := by
  vcgen
  simp [propInd]

/-- A plain event bound, by the averaging rule. -/
example : Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[b = true] ≤ 2⁻¹ := by
  rw [prEvent_le_iff_triple]
  vcgen [Spec.uniformSample_avg]
  upper_readback
  simp [propInd]

/-- A single fresh draw after an opaque prefix (`d` bad values per prefix output). -/
example {α F : Type} [SampleableType F] [Fintype F] (pre : ProbComp α) (P : α → F → Prop)
    [∀ a, DecidablePred (P a)] (d : ℕ) (h : ∀ a, (Finset.univ.filter (P a)).card ≤ d) :
    Pr{let a ← pre; let x ← $ᵗ F}[P a x] ≤ d / Fintype.card F := by
  rw [prEvent_le_iff_triple']
  vcgen [Spec.ofSupport pre, Spec.uniformSample_avg]
  upper_readback
  simp only [propInd_eq_ite, Finset.sum_boole]
  gcongr
  exact_mod_cast h _

/-- Two fresh draws, by the bad-event rule for the first and averaging for the second. -/
example : Pr{let x ← ($ᵗ (Fin 4) : ProbComp (Fin 4)); let y ← $ᵗ (Fin 4)}[x = 0 ∨ y = 0] ≤
    1 / 4 + 1 / 4 := by
  rw [prEvent_le_iff_triple']
  have h := Spec.uniformSample_bind_of_bad (β := Fin 4)
    (fun x => (fun y => x = 0 ∨ y = 0) <$> ($ᵗ (Fin 4) : ProbComp (Fin 4))) (· = 0) (d := 1)
    (by decide) (ε := 1 / 4) (fun P => toDual (propInd P)) (epost := Lean.Order.bot)
    (fun _ => propInd_le_one _) fun x hx => by
      vcgen [Spec.uniformSample_avg]
      upper_readback
      simp [propInd_eq_ite, hx]
  simpa using h

/-- A stateful draw that raises a flag on `true`. -/
def flagDraw : StateT Bool ProbComp Bool := do
  let b ← liftM ($ᵗ Bool : ProbComp Bool)
  modify (· || b)
  return b

/-- A stateful event bound: a triple of the upper reading, read back from one initial state. -/
example : Pr{let z ← flagDraw.run false}[z.2 = true] ≤ 2⁻¹ := by
  refine (prEvent_run_le_of_triple (p := fun _ s => s = true)
    (pre := fun s => toDual (propInd (s = true) + 2⁻¹)) ?_ false).trans (by simp)
  vcgen [flagDraw, Spec.uniformSample_avg]
  upper_readback
  rename_i s
  cases s <;> simp [propInd_eq_ite, ENNReal.div_self]

/-- Lifting along an inclusion of uniform specifications: `vcgen` continues into the lifted
program. -/
example : ⦃ toDual 2⁻¹ ⦄ (liftComp ($ᵗ Bool : ProbComp Bool) (unifSpec + coinSpec))
    ⦃ fun b => toDual (propInd (b = true)) ⦄ := by
  vcgen [Spec.uniformSample_avg]
  upper_readback
  simp [propInd]

/-- A coin answered by a draw from `Fin 4` that raises the bad flag on `0`. -/
def hitCoin : QueryImpl coinSpec (StateT Bool ProbComp) := fun _ => StateT.mk fun bad =>
  (fun x : Fin 4 => (decide (x = 0), bad || decide (x = 0))) <$> ($ᵗ (Fin 4))

lemma prEvent_hitCoin_bad (t : Unit) :
    Pr{let z ← (hitCoin t).run false}[z.2 = true] ≤ 4⁻¹ := by
  rw [hitCoin, StateT.run_mk, prEvent_map]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [SampleableType.prEvent_uniformSample, Finset.filter_eq', ite_eq_left (Finset.mem_univ _),
    Finset.card_singleton]
  simp

/-- The union bound over the queries of an adversary: `n` queries raise the flag with
probability at most `n / 4`. -/
example {α : Type} (oa : OracleComp coinSpec α) (n : ℕ) (hn : IsTotalQueryBound oa n) :
    Pr{let z ← (simulateQ hitCoin oa).run false}[z.2 = true] ≤ n * 4⁻¹ :=
  prEvent_simulateQ_run_bad_le_of_step hitCoin (· = true) 4⁻¹
    (fun t s hs => by simp only [Bool.not_eq_true] at hs; subst hs; exact prEvent_hitCoin_bad t)
    oa n hn false (by simp)

/-- A coin that keeps the state. -/
def plainCoin : QueryImpl coinSpec (StateT Bool ProbComp) := fun _ => StateT.mk fun bad =>
  (fun b => (b, bad)) <$> ($ᵗ Bool)

/-- Only the left oracle can raise the flag, so only left queries are charged. -/
example {α : Type} (oa : OracleComp (coinSpec + coinSpec) α) (n : ℕ)
    (hn : oa.IsQueryBoundP (·.isLeft) n) :
    Pr{let z ← (simulateQ (hitCoin + plainCoin) oa).run false}[z.2 = true] ≤ n * 4⁻¹ :=
  prEvent_simulateQ_run_bad_le_of_step_isQueryBoundP _ (· = true) 4⁻¹ (·.isLeft)
    (fun t ht s hs => by
      obtain ⟨t⟩ | ⟨t⟩ := t
      · simp only [Bool.not_eq_true] at hs; subst hs; exact prEvent_hitCoin_bad t
      · simp at ht)
    (fun t ht s hs => by
      obtain ⟨t⟩ | ⟨t⟩ := t
      · simp at ht
      · simpa [plainCoin, StateT.run_mk] using hs)
    oa n hn false (by simp)

/-! ## Notation: `wp⟦·⟧` and `⊤` next to the upper reading -/

section brackets

open scoped OracleComp.ProgramLogic

/-- `wp⟦·⟧` still denotes the expectation with the upper reading open. -/
example (oa : ProbComp Bool) (g : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (h : ⦃ toDual ε ⦄ oa ⦃ fun a => toDual (g a) ⦄) : wp⟦oa⟧ g ≤ ε :=
  (wp_le_iff_triple oa g ε).2 h

/-- `⊤` on the expectation carrier is unaffected. -/
example (oa : ProbComp Bool) (g : Bool → ℝ≥0∞) : wp⟦oa⟧ g ≤ ⊤ := le_top

/-- The trivial upper bound `⊤`. -/
example (oa : ProbComp Bool) (g : Bool → ℝ≥0∞) : ⦃ toDual ⊤ ⦄ oa ⦃ fun a => toDual (g a) ⦄ :=
  (wp_le_iff_triple oa g ⊤).1 le_top

end brackets

end VCVioTest.ProgramLogic.Library.Upper
