/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Expectation
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Selecting the measure interpretation

`open scoped ExpectationWP.Lower` makes the expectation interpretation of lawful
measure semantics, `ExpectationWP.wpMonad` (`VCVio.EvalDist.Expectation`), the core
weakest-precondition instance of every such monad, so `wp mx post ⊥` and core triples read
expectations. Its laws are stated on `wp⟦mx⟧ post` in `VCVio.EvalDist.Expectation` and
`VCVio.EvalDist.ProbabilityNotation`. `open scoped ExpectationWP.Upper` selects its dual, under
which a triple states an upper bound on an expectation, as `OracleComp.Upper` does for oracle
computations.

Opening either scope selects its expectation carrier over core's instances whose carrier is
`Prop`.
-/

public section

open MeasureTheory Std.WP
open scoped ENNReal

universe v

namespace ExpectationWP.Lower

variable (m : Type → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- Select the ordered expectation algebra of successful-output measures. The scope's priority
sits above core's direct instances and below the reading scopes of `OracleComp`
(`OracleComp.Necessary.Dispatch`, `OracleComp.Possible`, `OracleComp.Upper`, …), so a reading
opened for oracle computations is never outranked by this generic one. -/
noncomputable scoped instance (priority := 1050) instMAlgOrdered : MAlgOrdered m ℝ≥0∞ :=
  algebra m

variable {m} in
/-- The selected algebra integrates its actual nonnegative output. -/
@[simp]
theorem μ_eq_lintegral (mx : m ℝ≥0∞) : MAlgOrdered.μ mx = ∫⁻ x, x ∂𝒟[mx] := rfl

/-- Select the expectation interpretation of successful-output measures. -/
noncomputable scoped instance (priority := 1050) instWP [LawfulMonad m] :
    WPMonad m ℝ≥0∞ EStack⟨⟩ :=
  wpMonad m

/-- The expectation interpretation as a direct `WP` instance on programs. Core interprets its
concrete monads (`Id`, `Option`, `Except`, …) through direct `WP` instances, which instance search
tries before any `WPMonad`-derived one; this instance outranks them while the scope is open. -/
noncomputable scoped instance (priority := 1050) wpInst [LawfulMonad m] {α : Type} :
    WP (m α) α ℝ≥0∞ EStack⟨⟩ :=
  (wpMonad m).toWP α

end ExpectationWP.Lower

namespace ExpectationWP.Upper

open OrderDual

variable (m : Type → Type v) [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

open scoped ExpectationWP.Lower in
/-- Select the dual of the expectation interpretation: a triple states an upper bound on an
expectation. The scope's priority sits above core's direct instances and below the upper-bound
reading of `OracleComp` (`OracleComp.Upper`), so the oracle reading is never outranked by this
generic one. -/
noncomputable scoped instance (priority := 1050) instWP : WPMonad m ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  ExactWPMonad.dual

/-- The dual expectation interpretation as a direct `WP` instance on programs. -/
noncomputable scoped instance (priority := 1050) wpInst {α : Type} :
    WP (m α) α ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  (instWP m).toWP α

variable {m} {α : Type}

/-- The weakest precondition of the dual reading is the expectation of the postcondition, read
in `ℝ≥0∞`. -/
theorem wp_eq (mx : m α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    wp mx post epost = toDual (wp⟦mx⟧ fun a => ofDual (post a)) :=
  rfl

/-- A residual weakest precondition of the dual reading, read in `ℝ≥0∞`, is an expectation. -/
theorem ofDual_wp (mx : m α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    ofDual (wp mx post epost) = wp⟦mx⟧ fun a => ofDual (post a) :=
  rfl

/-- An expectation moved into the dual reading. -/
theorem toDual_wp (mx : m α) (g : α → ℝ≥0∞) :
    toDual (wp⟦mx⟧ g) = wp mx (fun a => toDual (g a)) Lean.Order.bot :=
  rfl

/-- A triple of the dual reading is an upper bound on the expectation. -/
theorem triple_iff (mx : m α) (pre : ℝ≥0∞ᵒᵈ) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    Triple mx pre post epost ↔ wp⟦mx⟧ (fun a => ofDual (post a)) ≤ ofDual pre :=
  Triple.iff

/-- An upper bound on an expectation is a triple of the dual reading, for every monad with lawful
measure semantics. -/
theorem wp_le_iff_triple (mx : m α) (g : α → ℝ≥0∞) (ε : ℝ≥0∞) :
    wp⟦mx⟧ g ≤ ε ↔ ⦃ toDual ε ⦄ mx ⦃ fun a => toDual (g a) ⦄ :=
  (triple_iff mx _ _ _).symm

/-- An opaque sub-program's expectation, as its own upper bound: `vcgen [Spec.ofWp mx]` leaves
the expectation of `mx` in the verification condition, for a hypothesis on it to bound. Not
registered, since it applies to every program. -/
theorem Spec.ofWp (mx : m α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple mx (toDual (wp⟦mx⟧ fun a => ofDual (post a))) post epost := by
  rw [triple_iff, ofDual_toDual]

/-- An opaque sub-program's expectation is at most the largest value of the postcondition: the
rule `OracleComp.Upper` registers for a draw, for any monad with lawful measure semantics. Not
registered, since it applies to every program; `vcgen [Spec.ofSup mx]` leaves a verification
condition for each value of `mx`. -/
theorem Spec.ofSup (mx : m α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple mx (Lean.Order.iInf post) post epost := by
  rw [triple_iff]
  exact wp_le_of_forall_le mx fun x => Lean.Order.iInf_le post x

end ExpectationWP.Upper
