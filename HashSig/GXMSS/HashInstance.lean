/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.TweakableHash

/-!
# Common hash instance for generalized XMSS

The common hash, input embeddings and separated tweak domains of Constructions 1 and 2
of Drake, Khovratovich, Kudinov and Wagner, ePrint 2025/055.
-/

public section

namespace GXMSS

/-- Shared deterministic hash interfaces. Epoch and chain labels are zero-based Lean indices;
positive chain steps are represented by `Fin (2^w-1)` and interpreted as their value plus one.
Input embedding images may overlap; only the chain and tree tweak images must be disjoint. -/
structure HashInstance (PP T X H : Type) (h w v : ℕ) where
  /-- One common tweakable hash for all three input forms. -/
  thf : TweakableHash PP T X H
  /-- Embed a chain digest into the common input domain. -/
  digestInput : H ↪ X
  /-- Embed an ordered left/right pair into the common input domain. -/
  pairInput : (H × H) ↪ X
  /-- Embed an endpoint vector into the common input domain. -/
  vectorInput : (Fin v → H) ↪ X
  /-- Injective chain tweaks for epoch, chain label and positive step. -/
  chainTweak : (Fin (2 ^ h) × Fin v × Fin (2 ^ w - 1)) ↪ T
  /-- Injective tree tweaks on the full level/index rectangle. -/
  treeTweak : (Fin (h + 1) × Fin (2 ^ h)) ↪ T
  /-- Chain tweaks and tree tweaks have distinct images. -/
  chain_ne_tree : ∀ c t, chainTweak c ≠ treeTweak t

end GXMSS
