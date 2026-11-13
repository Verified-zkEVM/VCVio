/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Asymptotic PRF security

A family of pseudorandom functions indexed by a security parameter `lam`, whose key, domain and
range types may depend on `lam`, has an asymptotic security game, `PRFScheme.prfSecurityGame`. An
adversary is a family of PRF distinguishers, one for each security parameter, and its advantage at
`lam` is the PRF advantage (`PRFScheme.prfAdvantage`) of its member at `lam` against the member of
the PRF family at `lam`. The family is secure against a class of distinguisher families
(`SecurityGame.secureAgainst`) when every family in the class has negligible advantage. The class
carries the efficiency notion; the concrete PRF game does not model running time.

`u lam` independently keyed instances of a PRF family are the family
`fun lam => (prf lam).multiKey (Fin (u lam))` (`PRFScheme.multiKey`), so security of its game is
multi-instance PRF security with `u lam` instances at parameter `lam`.

## Main definitions

* `PRFScheme.prfSecurityGame`: the asymptotic security game of a PRF family.
-/

public section

open OracleComp OracleSpec ENNReal

namespace PRFScheme

variable {K D R : ℕ → Type} [∀ lam, DecidableEq (D lam)] [∀ lam, SampleableType (R lam)]

/-- The asymptotic security game of a PRF family `prf` indexed by the security parameter: an
adversary is a family of distinguishers, and its advantage at `lam` is the PRF advantage of its
member at `lam` against `prf lam`. -/
@[expose]
noncomputable def prfSecurityGame (prf : (lam : ℕ) → PRFScheme (K lam) (D lam) (R lam)) :
    SecurityGame ((lam : ℕ) → PRFAdversary (D lam) (R lam)) where
  advantage adversary lam := prfAdvantage (prf lam) (adversary lam)

@[simp]
lemma prfSecurityGame_advantage (prf : (lam : ℕ) → PRFScheme (K lam) (D lam) (R lam))
    (adversary : (lam : ℕ) → PRFAdversary (D lam) (R lam)) (lam : ℕ) :
    (prfSecurityGame prf).advantage adversary lam = prfAdvantage (prf lam) (adversary lam) :=
  rfl

end PRFScheme
