/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Abort
public import VCVio.Schemes.BLS.Execution
public import VCVio.CryptoFoundations.HardnessAssumptions.CoCDH
public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount

/-! # The BLS index-guessing co-CDH solver

The Boneh–Lynn–Shacham reduction guesses one insertion index and programs its hash answer
with the challenge. Other answers carry sampled scalar preimages. Signing the selected
message raises a persistent abort flag; an aborted run returns zero.
-/

public section

open OracleComp OracleSpec

namespace BLS

variable {F G₁ G₂ Gₜ M : Type}

/-- Run the co-CDH solver with a fixed insertion-index guess. The final hash lookup ensures
that an output message not queried by the adversary can still occupy the guessed slot.
An aborted run or a forgery away from the guessed slot returns zero. -/
@[expose] def coCDHReductionAt [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (j : ℕ) : CoCDH.Adversary F G₁ G₂ :=
  fun gen₁ _ X₁ X₂ h => do
    let z ← (simulateQ (indexedOracle (tagDraw (V := F) j) (fun tag => tag.elim h (· • gen₁))
      (fun tag => tag.elim 0 (· • X₁)) (some j))
      (withFinalHash (A.main (X₁, X₂)))).run OracleState.empty
    if z.2.bad then return 0
    match z.2.cache z.1.1.1 with
    | some (none, _) => return z.1.1.2
    | _ => return 0

/-- The index-guessing co-CDH reduction. The guess is uniform among `qH + qS + 1` slots,
including hashes introduced by signing and final verification. The co-CDH experiment applies
its ordinary equality test to the output, including the zero fallback on abort. -/
@[expose] def coCDHReduction [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (qH qS : ℕ) : CoCDH.Adversary F G₁ G₂ :=
  fun gen₁ gen₂ X₁ X₂ h => do
    let j ← $ᵗ Fin (qH + qS + 1)
    coCDHReductionAt A j.val gen₁ gen₂ X₁ X₂ h

end BLS
