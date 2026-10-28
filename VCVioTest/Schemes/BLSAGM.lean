/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.AGM.Reductions
import all VCVio.Schemes.BLS.AGM.Reductions
public import Mathlib.Algebra.Field.ZMod

/-! # Concrete algebraic BLS fixtures over the field of order 101

The algebraic fixture asks one hash query and explains its output by the newly received
point. Multiplication is the pairing and both generators are one. Sampling uses `Fin 101`
directly, so module initialization does not enumerate a field.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction
open scoped ENNReal

namespace BLSAGMTest

/-- Primality of the concrete test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩
/-- Uniform sampling through `Fin 101`, without a load-time enumeration. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

private abbrev K := ZMod 101
private abbrev Groups := BLS.AGM.Group K K
private abbrev Spec := explainedSpec K Groups (BLS.AGM.Query Bool) BLS.AGM.Reply

private def output (inputs : GroupModel.Interaction.Groups Groups)
    (reply : Message Unit Groups) : Explained K Bool Groups :=
  Explained.ofVectors (extend inputs reply.groups) false (fun s => match s with
    | false => [fun i => if i.val = (inputs false).length then 1 else 0]
    | true => [])

private def oneHash : BLS.AlgebraicAdversary K Bool K K (LinearMap.mul K K) 1 1 where
  main input := do
    let reply ← Spec.query ⟨⟨.inl (.inr false), BLS.AGM.groupInputs [] []⟩, fun _ => []⟩
    return output input.groups reply
  algebraic input := by
    constructor
    · exact fun s => by cases s <;> exact .nil
    · intro reply
      exact Explained.valid_ofVectors _ _ _
  protocol input := by
    rw [allPathsSatisfy_query_bind]
    refine ⟨fun s => by cases s <;> rfl, fun reply _ => ?_⟩
    simp [output, Explained.ofVectors]

private theorem oneHash_raw (pk : K × K) :
    oneHash.toUnforgeableAdversary.main pk = (do
      let h ← (BLS.AGM.rawSpec Bool K).query (.inl (.inr false))
      pure (false, h)) := by
  simp [BLS.AlgebraicAdversary.toUnforgeableAdversary, oneHash, BLS.AGM.oracle,
    output, Explained.ofVectors,
    BLS.AGM.forgery, BLS.AGM.initialInput, BLS.AGM.groupInputs, extend, evaluate]

private theorem oneHash_good (X Y : K) :
    BLS.goodReduction oneHash 1 X 1 Y = (fun ρ : K => ρ / ρ) <$> ($ᵗ K) := by
  simp [BLS.goodReduction, BLS.reductionRun, BLS.reductionOracle, BLS.cached_run,
    BLS.coefficients, oneHash, output, Explained.ofVectors, BLS.AGM.initialInput,
    BLS.AGM.groupInputs, extend, evaluate]

/-- A certified one-hash algebraic adversary forgets to exactly the ordinary hash-and-return
program in the existing BLS oracle specification. -/
theorem one_hash_adversary_exists :
    ∃ A : BLS.AlgebraicAdversary (ZMod 101) Bool (ZMod 101) (ZMod 101)
      (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1,
      (∀ pk, A.toUnforgeableAdversary.main pk = (do
        let h ← (BLS.AGM.rawSpec Bool (ZMod 101)).query (.inl (.inr false))
        pure (false, h))) ∧
      (∀ X Y, BLS.goodReduction A 1 X 1 Y =
        (fun ρ : ZMod 101 => ρ / ρ) <$> ($ᵗ (ZMod 101))) :=
  ⟨oneHash, oneHash_raw, oneHash_good⟩

/-- Returning the first generator guesses the sampled scalar with probability exactly `1/101`
in the concrete (1,1)-DLog experiment. -/
theorem dlog11_identity_guess_probability :
    Pr{let b ← (DLog11.experiment (1 : ZMod 101) (1 : ZMod 101)
      (fun g _ _ _ => pure g))}[b = true] = (1 / 101 : ℝ≥0∞) := by
  simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
  simpa [eq_comm] using
    SampleableType.prEvent_uniformSample_eq_singleton (1 : ZMod 101)

end BLSAGMTest
