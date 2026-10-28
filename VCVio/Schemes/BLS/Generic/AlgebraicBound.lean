/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.Translation
public import VCVio.Schemes.BLS.AGM.Security

/-! # The algebraic BLS bound for a generic pairing adversary

The exact forgetful translation transports the algebraic theorem to the ordinary BLS
advantage of a handle adversary. The two terms on the right are the named algebraic
reductions applied to that certified translation.
-/

public section

open OracleComp OracleSpec GroupModel

namespace BLS

/-- The real generic BLS advantage satisfies the algebraic two-reduction bound, with no
change to the random-oracle experiment or its signing oracle. -/
theorem unforgeableAdvantage_le_of_generic_algebraic {F M G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (A : Generic.Adversary F M) (hA : Generic.FollowsProtocol A)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁))
      (A.toUnforgeableAdversary e g₁ g₂) ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction (A.toAlgebraic hA e g₁ g₂))}[b = true] +
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction (A.toAlgebraic hA e g₁ g₂))}[b = true] +
      1 / Fintype.card F := by
  have h := unforgeableAdvantage_le_of_algebraic (A.toAlgebraic hA e g₁ g₂) hg₁ he
  rwa [Generic.Adversary.toAlgebraic_toUnforgeableAdversary] at h

end BLS
