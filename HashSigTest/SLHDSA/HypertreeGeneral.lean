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
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 1 = vp.params.d) :
    signFromPositionWith vp core hash compress nodeHash sk pk true pos 1 hremaining msg = (do
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let _ ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
      return #v[sig]) := by
  rfl

/-- With two layers, the first signature is recovered and signed by the top XMSS tree, while the
top signature is returned without a second discarded recovery. -/
example (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 2 = vp.params.d) :
    signFromPositionWith vp core hash compress nodeHash sk pk false pos 2 hremaining msg = (do
      let sig0 ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let root0 ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig0 msg pos.toAdrs
      let next := pos.next (by omega)
      let sig1 ←
        xmssSignWith core hash compress nodeHash root0 sk pk next.toAdrs next.leaf.val
      return (#v[sig1]).insertIdx 0 sig0) := by
  simp [signFromPositionWith]

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
