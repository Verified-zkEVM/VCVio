/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Bridge

/-! # Tight algebraic Schnorr signature security

The existing Schnorr EUF-CMA game reduces to the existing discrete-log experiment with
one named, single-pass reduction. The exceptional-challenge term counts adversarial hashes
and the final verification hash. The signing-programming term comes from the existing
Fiat-Shamir signing simulation and uniform Schnorr commitments.

This is the full-field Schnorr bound of Fuchsbauer, Plouviez and Seurin,
*Blind Schnorr Signatures and Signed ElGamal Encryption in the Algebraic Group Model*,
EUROCRYPT 2020, https://eprint.iacr.org/2019/877. The additive terms match
`Schnorr.agm_security` in zkSecurity's `signature-security-lean` at revision `3eaa8c4`;
that source's resource-indexed supremum is instantiated here by an explicit reduction.
Both implementations sample nonces from the full field and hash `(message, commitment)`.
The certified protocol shape excludes malformed requests. Bijective scalar multiplication
by `g` and a group sampler supply the hypotheses of VCVio's signing-simulation theorem.
-/

public section

open OracleComp
open scoped ENNReal

namespace Schnorr

/-- Tight EUF-CMA security of the existing Schnorr signature against certified algebraic
adversaries, with explicit signing and hash budgets and a named discrete-log reduction. -/
theorem unforgeableAdvantage_le_of_algebraic {F G M : Type}
    [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G] [DecidableEq M]
    (g : G) (hg : Function.Bijective (fun x : F => x • g))
    (A : AlgebraicAdversary F G M) (qS qH : ℕ)
    (hS : ∀ pk, IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.Reduction.signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.Reduction.hashRequest q = true) qH) :
    SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := G) (Chal := F) M)
        (A.toUnforgeableAdversary g) ≤
      Pr{let b ← DiffieHellman.dlogExperiment g (agmReduction g A)}[b = true] +
        (qH + 1 : ℝ≥0∞) / Fintype.card F +
        (qS : ℝ≥0∞) * (qS + qH) / Fintype.card F := by
  have hs := unforgeableAdvantage_le_simulatedCma g hg A qS qH hS hH
  rw [AGM.simulatedCma_eq_run] at hs
  have he := AGM.Reduction.run_success_le_dlogExperiment g hg.1 A qH hH
  simp only [prEvent_norm] at hs
  exact hs.trans (by
    simpa only [div_eq_mul_inv] using add_le_add he
      (le_refl ((qS : ℝ≥0∞) * (qS + qH) * (Fintype.card F : ℝ≥0∞)⁻¹)))

end Schnorr
