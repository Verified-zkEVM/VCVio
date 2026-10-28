/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Security
public import Mathlib.Algebra.Field.ZMod
import VCVio.EvalDist.ProbabilityBounds

/-! # BLS over the field of order 101

Concrete consumers of the Boneh–Lynn–Shacham scheme, with multiplication as the pairing
and both generators equal to one. The adversary hashes `false`, signs `true`, and uses
the scalar visible in this toy public key to forge on `false`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace BLSTest

/-- Primality certificate for the local test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- Sample directly as `Fin 101`, without constructing an enumeration at module load. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

local notation "toyScheme" =>
  BLS.scheme (M := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1

private def adversary : SignatureAlg.UnforgeableAdversary toyScheme where
  main pk := do
    let h : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inl (.inr false))
    let _ : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inr true)
    return (false, pk.2 * h)

/-- Multiplication with unit generators instantiates the generic ROM completeness theorem. -/
private theorem perfectlyComplete :
    (toyScheme).PerfectlyComplete (ProbCompRuntime.rom (Bool →ₒ ZMod 101)) :=
  BLS.perfectlyComplete _ _ _

/-- The fixture uses one direct hash query and one signing query on every public key. -/
private theorem queryBound : BLS.QueryBound adversary 1 1 := by
  intro pk
  constructor <;> simp [adversary, isQueryBoundP_query_bind_iff]

/-- In the concrete pairing, every accepted signature equals the secret times the hash. -/
private theorem verification_iff (x h σ : ZMod 101) : σ * 1 = h * (x * 1) ↔ σ = x * h := by
  simpa using BLS.pairing_eq_iff (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
    (by intro y; exact ⟨y, by simp⟩) (by simp) x h σ

/-- A concrete one-hash, one-sign adversary satisfies the factor-three bound for the named
index-guessing reduction, by instantiating the general EUF-CMA theorem. -/
theorem one_hash_one_sign_bound :
    let A : SignatureAlg.UnforgeableAdversary toyScheme := ⟨fun pk => do
      let h : ZMod 101 ←
        ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inl (.inr false))
      let _ : ZMod 101 ←
        ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inr true)
      return (false, pk.2 * h)⟩
    BLS.QueryBound A 1 1 ∧
      SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ ZMod 101)) A ≤
        3 * Pr{let b ← CoCDH.experiment 1 1 (BLS.reduction A 1 1)}[b = true] := by
  change BLS.QueryBound adversary 1 1 ∧ _
  refine ⟨queryBound, ?_⟩
  have hg : Function.Bijective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) := by
    simp
  have h := BLS.unforgeableAdvantage_le adversary 1 1 queryBound hg (by simp)
  norm_num at h
  exact h

end BLSTest
