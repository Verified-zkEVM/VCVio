/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.HypertreeGeneral

/-!
# General-hypertree schedule canaries

These examples pin the two boundary depths at which Algorithm 12 is easiest to implement
incorrectly: the discarded recovery at `d = 1`, and the absence of a discarded recovery after the
top signature when `d = 2`.
-/

public section

namespace SLHDSA.GeneralHypertreeTest

open GeneralHypertree

variable (vp : ValidatedParams) (core : CorePrimitives vp.params)
variable {m : Type → Type*} [Monad m] [LawfulMonad m]

/-- The signature width is intrinsic and cannot differ from the hypertree depth. -/
example (sig : Signature vp core) : sig.toArray.size = vp.params.d := sig.size_toArray

/-- The one-layer signer still performs FIPS Algorithm 12's unconditional layer-zero recovery,
even though the recovered value does not affect the returned singleton signature. -/
example (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (layer tree leaf : ℕ) :
    signLayersWith vp core hash compress nodeHash sk pk true 1 layer tree leaf msg = (do
      let adrs := layerAdrs layer tree
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk adrs leaf
      let _ ← xmssPkFromSigWith core hash compress nodeHash leaf sig msg adrs
      return #v[sig]) := by
  rfl

/-- With two layers, the first signature is recovered and signed by the top XMSS tree, while the
top signature is returned without a second discarded recovery. -/
example (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (layer tree leaf : ℕ) :
    signLayersWith vp core hash compress nodeHash sk pk false 2 layer tree leaf msg = (do
      let adrs0 := layerAdrs layer tree
      let sig0 ← xmssSignWith core hash compress nodeHash msg sk pk adrs0 leaf
      let root0 ← xmssPkFromSigWith core hash compress nodeHash leaf sig0 msg adrs0
      let adrs1 := layerAdrs (layer + 1) (tree / 2 ^ vp.params.hp)
      let sig1 ← xmssSignWith core hash compress nodeHash root0 sk pk adrs1
        (tree % 2 ^ vp.params.hp)
      return (#v[sig1]).insertIdx 0 sig0) := by
  simp [signLayersWith]

/-- General root generation always addresses layer `d - 1`, tree zero. -/
example (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    rootWith vp core hash compress nodeHash sk pk =
      xmssRootWith core hash compress nodeHash sk pk
        (layerAdrs (vp.params.d - 1) 0) := by
  rfl

end SLHDSA.GeneralHypertreeTest
