/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Security
public import Mathlib.Algebra.Field.ZMod

/-! # BLS over the field of order 101

Concrete consumers of the Boneh–Lynn–Shacham scheme, with multiplication as the pairing
and both generators equal to one. The adversary hashes `false`, signs `true`, and uses
the scalar visible in this toy public key to forge on `false`. Its budget of one hash and one
signing query is tight, and it meets every hypothesis of the security theorem.
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

/-- Hash `false`, sign `true`, and forge on `false` with the scalar the toy public key shows. -/
@[expose] def adversary : SignatureAlg.UnforgeableAdversary toyScheme where
  main pk := do
    let h : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inl (.inr false))
    let _ : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inr true)
    return (false, pk.2 * h)

/-- The fixture uses one direct hash query and one signing query on every public key. -/
theorem adversary_romQueryBound : adversary.RomQueryBound 1 1 := by
  intro pk
  constructor <;>
    simp [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery,
      SignatureAlg.IsSignQuery]

/-- The hash budget is tight: no public key admits a budget of zero direct hash queries. -/
theorem not_adversary_romQueryBound_zero_one : ¬ adversary.RomQueryBound 0 1 := fun h => by
  simpa [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery] using (h (0, 0)).1

/-- The signing budget is tight: no public key admits a budget of zero signing queries. -/
theorem not_adversary_romQueryBound_one_zero : ¬ adversary.RomQueryBound 1 0 := fun h => by
  simpa [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery,
    SignatureAlg.IsSignQuery] using (h (0, 0)).2

/-- The one-hash, one-sign adversary meets every hypothesis of the security theorem, which then
bounds its advantage by three times the success of the named co-CDH reduction. -/
theorem one_hash_one_sign_bound :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ ZMod 101)) adversary ≤
      3 * Pr{let b ← CoCDH.experiment 1 1 (BLS.coCDHReduction adversary 1 1)}[b = true] := by
  have hg : Function.Bijective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) := by
    simp
  have h := BLS.unforgeableAdvantage_le adversary 1 1 adversary_romQueryBound hg (by simp)
  norm_num at h
  exact h

end BLSTest
