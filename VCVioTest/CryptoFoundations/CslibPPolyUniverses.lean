/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVioCslib.NonuniformPPoly
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Higher-universe canaries for the optional cslib P/poly facade

Lean can silently specialize an exported declaration to `Type 0` when its
universe is omitted. These examples keep the security-game facade usable by
ordinary oracle families whose query and answer types live above `Type 0`.
-/

public section

universe u

open OracleSpec ENNReal OracleComp.Complexity

namespace VCVioTest.CslibPPolyUniverses

variable {index input output : ℕ → Type (u + 1)}
  [∀ n, DecidableEq (index n)]
  {spec : (n : ℕ) → OracleSpec.{u + 1, u + 1} (index n)}

example (boundary : NonuniformBoundary spec input output)
    (game : SecurityGame ((n : ℕ) → input n → OracleComp (spec n) (output n))) : Prop :=
  game.secureAgainstNonuniformPPT boundary

example (boundary : NonuniformBoundary spec input output)
    (game : SecurityGame ((n : ℕ) → input n → OracleComp (spec n) (output n)))
    {error : ℕ → ℝ≥0∞} (errorNegligible : negligible error)
    (advantageBound :
      ∀ (adversary : (n : ℕ) → input n → OracleComp (spec n) (output n))
        (queries : ℕ → ℕ),
        (∀ n value, OracleComp.IsTotalQueryBound (adversary n value) (queries n)) →
        ∀ n, game.advantage adversary n ≤ (queries n : ℝ≥0∞) * error n) :
    game.secureAgainstNonuniformPPT boundary :=
  SecurityGame.secureAgainstNonuniformPPT_of_advantage_le_mul_totalQueries
    boundary game errorNegligible advantageBound

/-! ## An enabled fair-coin query with an actual machine certificate

This fixture instantiates the public VCVio boundary and witness, including initialization,
head observation, and enabled answer transition code. Its two answers produce different
returned values, and its certified query budget is exactly one.
-/

open ToCslib.Computability PFunctor

noncomputable instance : Fintype coinSpec.toPFunctor.Idx :=
  Fintype.ofFinite ((_: Unit) × Bool)

noncomputable def coinBoundary :
    NonuniformBoundary (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool) :=
  NonuniformBoundary.coin (BitEncFam.const Unit) BitEncFam.bool

noncomputable def coinStateEncoding : StrEncFam fun _ => Option Bool :=
  BitEncFam.bool.option.toStrEncFam

@[reducible] def coinMachine (_n : ℕ) :
    DynSystem.DynComputation coinSpec.toPFunctor Unit Bool :=
  .ofStep (S := Option Bool)
    (fun
      | none => Sum.inr ⟨(), some⟩
      | some answer => Sum.inl answer)
    (fun _ => none)

noncomputable def coinRealization : CslibPPoly.Realization coinBoundary where
  machine := coinMachine
  rounds := .C 1
  state := coinStateEncoding
  initCode := .ofFintype (BitEncFam.const Unit).enc_injective
    (fun n => (coinMachine n).init) (.C 1) (fun _ => by simp)
    (BitEncFam.const Unit).widBound
    (fun n value => ((BitEncFam.const Unit).len_eq n value).le.trans
      ((BitEncFam.const Unit).wid_le n))
    coinStateEncoding.bound (fun n value => coinStateEncoding.len_le n _)
  headCode := .ofFintype coinStateEncoding.enc_injective
    (fun n => (coinMachine n).head) (.C 3) (fun _ => by simp)
    coinStateEncoding.bound coinStateEncoding.len_le
    coinBoundary.head.bound (fun n value => coinBoundary.head.len_le n _)
  updateCode := .ofFintype (coinStateEncoding.pairVar coinBoundary.index).enc_injective
    (fun n => (coinMachine n).update?) (.C 6)
    (fun _ => by
      have hcard : Fintype.card coinSpec.toPFunctor.Idx = 2 := by
        rw [Fintype.card_eq_nat_card]
        change Nat.card ((_: Unit) × Bool) = 2
        simp
      simp [Fintype.card_prod, hcard])
    (coinStateEncoding.pairVar coinBoundary.index).bound
    (fun n value => (coinStateEncoding.pairVar coinBoundary.index).len_le n _)
    coinStateEncoding.option.bound (fun n value => coinStateEncoding.option.len_le n _)

def coinProgram (_n : ℕ) (_value : Unit) : OracleComp coinSpec Bool :=
  liftM (coinSpec.query ())

noncomputable def coinWitness : NonuniformPPTWitness coinBoundary coinProgram where
  realization := coinRealization
  implements := CslibPPoly.Realization.Implements.intro fun _ _ => by
    simp only [coinRealization, Polynomial.eval_C]
    rfl
  progress _ _ := by
    change CslibPPoly.ProgramProgress (FreeM.liftBind (P := coinSpec.toPFunctor) () FreeM.pure)
    rw [CslibPPoly.programProgress_liftBind]
    exact ⟨⟨false⟩, fun answer => CslibPPoly.programProgress_pure answer⟩

example : IsNonuniformPPTBy coinBoundary coinProgram :=
  IsNonuniformPPTBy.intro coinWitness

example (n : ℕ) : OracleComp.IsTotalQueryBound (coinProgram n ()) 1 := by
  simpa [coinWitness, coinRealization] using NonuniformPPTWitness.queryBound coinWitness n ()

example (answer : Bool) :
    (coinMachine 0).update? (none, ⟨(), answer⟩) = some (some answer) := by
  rfl

example : (coinMachine 0).update? (none, ⟨(), false⟩) ≠
    (coinMachine 0).update? (none, ⟨(), true⟩) := by
  decide

example (answer : Bool) : (coinMachine 0).head (some answer) = Sum.inl answer := rfl

/-- The certified query has the canonical fair-coin distribution under native measures. -/
example (n : ℕ) (answer : Bool) : 𝒟[coinProgram n ()] {answer} = (2 : ℝ≥0∞)⁻¹ := by
  simp only [coinProgram, OracleComp.evalDist_liftM_query,
    OracleSpec.IsMeasureSpec.toMeasure_eq_uniformOn,
    ProbabilityTheory.uniformOn_univ_apply_singleton]
  norm_num

end VCVioTest.CslibPPolyUniverses
