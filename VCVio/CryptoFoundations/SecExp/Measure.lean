/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.MeasureTheory.Measure.Bool
public import VCVio.EvalDist.Defs.Semantics.Core
public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.Monad.Bool
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Measure-valued advantages of Boolean experiments

The bias and distinguishing advantages of `ProbComp Bool` experiments observe their
successful-output measures directly, and fair-coin decompositions use the native measure API.
-/

public section

universe u v w

open MeasureTheory OracleComp OracleSpec ENNReal Polynomial Prod

/-- Bias advantage of a Boolean-valued game: the gap between the probabilities of the two outputs.

This is the canonical single-game formulation for hidden-bit guessing experiments. -/
@[expose]
noncomputable def ProbComp.boolBiasAdvantage (p : ProbComp Bool) : ℝ :=
  |(𝒟[p] {true}).toReal - (𝒟[p] {false}).toReal|

/-- Distinguishing advantage between two Boolean-valued games, measured on the `true` branch.

For Boolean outputs this is equivalent to measuring the gap on `false`; choosing `true` is just a
conventional presentation. -/
@[expose]
noncomputable def ProbComp.boolDistAdvantage (p q : ProbComp Bool) : ℝ :=
  |(𝒟[p] {true}).toReal - (𝒟[q] {true}).toReal|

/-- Triangle inequality for Boolean distinguishing advantage. -/
lemma ProbComp.boolDistAdvantage_triangle (p q r : ProbComp Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r :=
  Measure.boolDist_triangle _ _ _

/-- A Boolean game has zero distinguishing advantage against itself. -/
@[simp, grind =]
lemma ProbComp.boolDistAdvantage_self (p : ProbComp Bool) : p.boolDistAdvantage p = 0 :=
  Measure.boolDist_self 𝒟[p]

/-- Boolean distinguishing advantage is symmetric. -/
lemma ProbComp.boolDistAdvantage_comm (p q : ProbComp Bool) :
    p.boolDistAdvantage q = q.boolDistAdvantage p :=
  Measure.boolDist_comm _ _

/-- The `true`-branch probability of one Boolean-valued game is bounded above by the
`true`-branch probability of another game plus their distinguishing advantage.

This is the `ENNReal`-level interpretation of the real-valued identity `a ≤ b + |a - b|`,
packaged for SSP game-hopping: converting an `advantage p q ≤ ε` assumption into a direct
probability inequality `Pr[true|p] ≤ Pr[true|q] + ENNReal.ofReal ε` that plugs into chained
`calc`-style bounds. -/
lemma ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.ofReal (p.boolDistAdvantage q) :=
  Measure.apply_true_le_add_ofReal_boolDist 𝒟[p] 𝒟[q]

/-- Re-express Boolean bias as twice the absolute deviation of `Pr[true]` from `1/2`. -/
lemma ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half (p : ProbComp Bool) :
    p.boolBiasAdvantage = 2 * |(𝒟[p] {true}).toReal - 1 / 2| :=
  Measure.boolBias_eq_two_mul_abs_sub_half_of_isProbabilityMeasure 𝒟[p]

/-- Fair hidden-bit guessing has the distinguishing advantage of its two branches. -/
lemma ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch
    (real rand : ProbComp Bool) :
    (do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)).boolBiasAdvantage = real.boolDistAdvantage rand := by
  simpa only [ProbComp.boolBiasAdvantage, ProbComp.boolDistAdvantage,
    Measure.boolBias, Measure.boolDist] using
    evalDist_boolBias_bind_coin ($ᵗ Bool : ProbComp Bool) real rand (by simp) (by simp)

/-- Version of `boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch` with a shared sampled
prefix before the real/random branch is chosen. -/
lemma ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage
    {α : Type} (pref : ProbComp α) (real rand : α → ProbComp Bool) :
    (do
      let a ← pref
      let b ← ($ᵗ Bool)
      let z ← if b then real a else rand a
      pure (b == z)).boolBiasAdvantage =
    (do
      let a ← pref
      real a).boolDistAdvantage
      (do
        let a ← pref
        rand a) := by
  let game : ProbComp Bool := do
    let a ← pref
    let b ← ($ᵗ Bool)
    let z ← if b then real a else rand a
    pure (b == z)
  let left : ProbComp Bool := do
    let a ← pref
    real a
  let right : ProbComp Bool := do
    let a ← pref
    rand a
  let branchGame : ProbComp Bool := do
    let b ← ($ᵗ Bool)
    let z ← if b then left else right
    pure (b == z)
  have hbranch : 𝒟[game] = 𝒟[branchGame] := by
    let : MeasurableSpace α := ⊤
    calc
      𝒟[game] = 𝒟[($ᵗ Bool) >>= fun b => pref >>= fun a => do
          let z ← if b then real a else rand a
          pure (b == z)] := by
            simpa [game, monad_norm] using
              (evalDist_bind_bind_swap pref ($ᵗ Bool)
                (fun a b => do
                  let z ← if b then real a else rand a
                  pure (b == z))
                (measurable_from_prod_countable_left fun _ => .of_discrete))
      _ = 𝒟[branchGame] := by
        congr 1
        simp only [branchGame]
        apply bind_congr
        intro b
        cases b <;> simp [left, right]
  rw [show game.boolBiasAdvantage = branchGame.boolBiasAdvantage by
    unfold ProbComp.boolBiasAdvantage
    rw [hbranch]]
  simpa [branchGame, left, right] using
    ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch left right
