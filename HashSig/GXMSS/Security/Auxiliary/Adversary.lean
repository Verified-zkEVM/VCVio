/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Scheme
public import VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Concrete GXMSS epoch and adaptive adversary
-/

public section

namespace GXMSS.Reductions

open OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Epoch indices of a complete binary tree of height `h`. -/
abbrev Epoch (h : ℕ) := Fin (2 ^ h)

/-- Adaptive synchronized-signature adversary with ambient uniform sampling. -/
abbrev SchemeAdversary (PP H M R : Type) (h v : ℕ) :=
  SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M
    (GXMSS.Signature R H h v)

end GXMSS.Reductions
