/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Reduction
public import Mathlib.Algebra.Field.ZMod

/-! # Aggregate BLS regression theorems

Concrete two-signer verification and duplicate-message rejection over `ZMod 101` with
multiplication as the pairing. A separate two-dimensional second-source example records
the distinction between a linear source map and compatibility with the pairing.
-/

public section

open OracleComp OracleSpec

namespace BLSAggregateTest

/-- Primality of the local test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- Sample through `Fin 101` without enumerating a finite type at module initialization. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

local notation "toyScheme" =>
  BLS.Aggregate.scheme (M := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1

/-- Signers with secrets two and three sign different messages with hashes seven and five;
their aggregate signature is 29 and verifies. -/
theorem two_signer_correctness :
    simulateQ (unifFwdAnswerImpl
      (fun b => if b then 5 else 7 : QueryImpl (Bool →ₒ ZMod 101) Id))
      ((toyScheme).aggregateVerify [(2, false), (3, true)] 29) =
        (pure true : ProbComp Bool) := by
  have h := BLS.Aggregate.aggregateVerify_honest
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 (fun b : Bool => if b then 5 else 7)
    [(2, false), (3, true)] (by simp)
  norm_num at h ⊢
  exact h

/-- The scheme rejects repeated messages even when both component signatures are honest. -/
theorem duplicate_message_rejected :
    (toyScheme).aggregateVerify [(2, false), (3, false)] 35 = pure false := by
  exact BLS.Aggregate.aggregateVerify_eq_false_of_not_nodup _ _ _ _ (by simp)

/-- The public identity source map gives the expected subtraction of the programmed mask. -/
theorem identity_map_extracts (x r h : ZMod 101) :
    x * (h + r) - r * x = x * h := by
  simpa using BLS.Aggregate.sub_mask_eq (LinearMap.id (R := ZMod 101) (M := ZMod 101))
    1 x r h

/-- A zero-query adversary returning a singleton has explicit budgets zero, zero, and one. -/
theorem zero_query_bound :
    let A : AggregateSignatureAlg.UnforgeableAdversary toyScheme :=
      ⟨fun pk => pure ([(pk, false)], 0)⟩
    BLS.Aggregate.QueryBound A 0 0 1 := by
  simp [BLS.Aggregate.QueryBound]

/-- A linear source map can meet the two generator hypotheses yet fail the arbitrary-key
pairing identity needed to strip contributions. Here `ψ` projects the first coordinate,
while the pairing uses the sum of both coordinates. -/
theorem source_map_compatibility_counterexample :
    let ψ : (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 := LinearMap.fst _ _ _
    let e : ZMod 101 →ₗ[ZMod 101] (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 :=
      (LinearMap.mul (ZMod 101) (ZMod 101)).compl₂
        (LinearMap.fst _ _ _ + LinearMap.snd _ _ _)
    let g₂ : ZMod 101 × ZMod 101 := (1, 0)
    Function.Bijective (· • ψ g₂ : ZMod 101 → ZMod 101) ∧
      e (ψ g₂) g₂ ≠ 0 ∧ e (ψ (0, 1)) g₂ ≠ e (ψ g₂) (0, 1) := by
  simp

/-- A valid two-message pairing equation need not yield the challenge solution after
stripping the chosen key with a merely linear source map. The honest secret and challenge
are one, the selected mask is zero, and the other hash's scalar is one. -/
theorem arbitrary_key_stripping_counterexample :
    let ψ : (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 := LinearMap.fst _ _ _
    let e : ZMod 101 →ₗ[ZMod 101] (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 :=
      (LinearMap.mul (ZMod 101) (ZMod 101)).compl₂
        (LinearMap.fst _ _ _ + LinearMap.snd _ _ _)
    let g₂ : ZMod 101 × ZMod 101 := (1, 0)
    e 2 g₂ = e 1 g₂ + e 1 (0, 1) ∧ (2 : ZMod 101) - ψ (0, 1) ≠ 1 := by
  norm_num
  decide

end BLSAggregateTest
