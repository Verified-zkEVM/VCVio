/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.DepthOneCompatibility

/-!
# Hypertree callback refinement and trajectory conformance

The low-level callback APIs, explicit public-hash programs, and deterministic interpretations use
one XMSS and hypertree control flow.  The theorems in this module make the callback-to-query
refinement explicit and expose the exact FIPS 205 layer/tree/leaf trajectory without introducing a
second construction algorithm.

## References

- NIST FIPS 205, Section 7, Algorithms 12--13
-/

@[expose] public section

namespace SLHDSA

open OracleComp

variable {p : Params}

/-! ## XMSS callback refinement -/

/-- Instantiating the callback XMSS signer with the public-hash query callbacks is exactly the
canonical explicit-query signer. -/
@[simp]
theorem xmssSignWith_publicHash_eq_xmssSignM (core : CorePrimitives p)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    xmssSignWith core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        msg sk pk adrs idx = xmssSignM core msg sk pk adrs idx := rfl

/-- Instantiating callback XMSS recovery with the public-hash query callbacks is exactly the
canonical explicit-query recovery program. -/
@[simp]
theorem xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM (core : CorePrimitives p)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) :
    xmssPkFromSigWith core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        idx sig msg adrs = xmssPkFromSigM core idx sig msg pk adrs := rfl

/-- Instantiating callback XMSS root generation with the public-hash query callbacks is exactly
the canonical explicit-query key-generation root. -/
@[simp]
theorem xmssRootWith_publicHash_eq_xmssRootM (core : CorePrimitives p)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    xmssRootWith core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        sk pk adrs = xmssRootM core sk pk adrs := rfl

/-- A fixed total public-hash answer interprets the callback XMSS signer as the pure signer. -/
theorem simulateQ_xmssSignWith_publicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    simulateQ answer
        (xmssSignWith core (m := OracleComp (publicHashSpec core))
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk)
          msg sk pk adrs idx) =
      xmssSign (PublicHash.withPublicHash core answer) msg sk pk adrs idx := by
  exact simulateQ_xmssSignM_withPublicHash core answer msg sk pk adrs idx

/-- A fixed total public-hash answer interprets callback XMSS recovery as pure recovery. -/
theorem simulateQ_xmssPkFromSigWith_publicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (xmssPkFromSigWith core (m := OracleComp (publicHashSpec core))
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk)
          idx sig msg adrs) =
      xmssPkFromSig (PublicHash.withPublicHash core answer) idx sig msg pk adrs := by
  exact simulateQ_xmssPkFromSigM_withPublicHash core answer idx sig msg pk adrs

/-- A fixed total public-hash answer interprets callback XMSS root generation as the pure root. -/
theorem simulateQ_xmssRootWith_publicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (xmssRootWith core (m := OracleComp (publicHashSpec core))
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk)
          sk pk adrs) =
      xmssRoot (PublicHash.withPublicHash core answer) sk pk adrs := by
  exact simulateQ_xmssRootM_withPublicHash core answer sk pk adrs

namespace GeneralHypertree

/-! ## Arbitrary-depth callback refinement -/

/-- Exact depth-one callback schedule: Algorithm 12 recovers the sole XMSS signature and discards
the result before returning it. -/
theorem signFromPositionWith_one_recover (vp : ValidatedParams)
    (core : CorePrimitives vp.params) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 1 = vp.params.d) :
    signFromPositionWith vp core hash compress nodeHash sk pk true pos 1 hremaining msg = (do
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let _ ← xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
      return #v[sig]) := by
  rfl

/-- Exact two-layer callback schedule: the first XMSS root becomes the top-layer message, while the
top signature is returned without an additional discarded recovery. -/
theorem signFromPositionWith_two (vp : ValidatedParams)
    (core : CorePrimitives vp.params) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 2 = vp.params.d) :
    signFromPositionWith vp core hash compress nodeHash sk pk false pos 2 hremaining msg = (do
      let sig0 ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let root0 ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig0 msg pos.toAdrs
      let next := pos.next (by omega)
      let sig1 ← xmssSignWith core hash compress nodeHash root0 sk pk next.toAdrs next.leaf.val
      return (#v[sig1]).insertIdx 0 sig0) := by
  simp [signFromPositionWith]

/-- The callback-parametric signing loop instantiated with the public-hash query callbacks is
exactly the explicit-query structural loop, including the depth-one discarded recovery. -/
theorem signFromPositionWith_eq_signFromPositionM (vp : ValidatedParams)
    (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    signFromPositionWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        sk pk recoverFinal pos layers hremaining msg =
      signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => rfl
  | one => cases recoverFinal <;> rfl
  | more layers _ ih =>
      simp only [signFromPositionWith, signFromPositionM, xmssSignM,
        xmssPkFromSigM, ih]

/-- The callback-parametric recovery loop instantiated with public-hash query callbacks is exactly
the explicit-query structural recovery loop. -/
theorem recoverFromPositionWith_eq_recoverFromPositionM (vp : ValidatedParams)
    (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (pk : core.PkSeed) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    recoverFromPositionWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        pk pos layers hremaining msg sigs =
      recoverFromPositionM vp core pk pos layers hremaining msg sigs := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => rfl
  | one => rfl
  | more layers _ ih =>
      simp only [recoverFromPositionWith, recoverFromPositionM, xmssPkFromSigM, ih]

/-- Callback-parametric general hypertree signing is the canonical explicit-query signer after
instantiating the three public-hash callbacks. -/
theorem signWith_eq_signM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    signWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        msg sk pk parts = signM vp core msg sk pk parts := by
  exact signFromPositionWith_eq_signFromPositionM vp core sk pk _ _ _ _ _

/-- Callback-parametric top-root generation is the canonical explicit-query key-generation root
after instantiating the three public-hash callbacks. -/
theorem rootWith_eq_rootM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) :
    rootWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        sk pk = rootM vp core sk pk := rfl

/-- Callback-parametric arbitrary-depth recovery is the canonical explicit-query recovery program
after instantiating the three public-hash callbacks. -/
theorem pkFromSigWith_eq_pkFromSigM (vp : ValidatedParams)
    (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    pkFromSigWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        msg sig pk parts = pkFromSigM vp core msg sig pk parts := by
  exact recoverFromPositionWith_eq_recoverFromPositionM vp core pk _ _ _ _ _

/-- A fixed total public-hash answer interprets callback general-hypertree signing as the pure
signer. -/
theorem simulateQ_signWith_publicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer
        (signWith vp core (m := OracleComp (publicHashSpec core))
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk)
          msg sk pk parts) =
      sign vp (PublicHash.withPublicHash core answer) msg sk pk parts := by
  rw [signWith_eq_signM, simulateQ_signM_withPublicHash]

/-- A fixed total public-hash answer interprets callback top-root generation as the pure root used
by key generation. -/
theorem simulateQ_rootWith_publicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    simulateQ answer
        (rootWith vp core (m := OracleComp (publicHashSpec core))
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) sk pk) =
      root vp (PublicHash.withPublicHash core answer) sk pk := by
  rw [rootWith_eq_rootM, simulateQ_rootM_withPublicHash]

/-- A fixed total public-hash answer interprets callback arbitrary-depth recovery as pure
recovery. -/
theorem simulateQ_pkFromSigWith_publicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer
        (pkFromSigWith vp core (m := OracleComp (publicHashSpec core))
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk)
          msg sig pk parts) =
      pkFromSig vp (PublicHash.withPublicHash core answer) msg sig pk parts := by
  rw [pkFromSigWith_eq_pkFromSigM, simulateQ_pkFromSigM_withPublicHash]

end GeneralHypertree

namespace HypertreeConformance

/-! ## Exact typed position trace -/

/-- Exact FIPS layer trajectory, indexed by the validated hypertree depth. -/
def trajectory (vp : ValidatedParams) (parts : DigestParts vp.params) :
    Vector (LayerPosition vp) vp.params.d :=
  Vector.ofFn (LayerPosition.atLayer vp parts)

/-- Observable layer/tree/leaf and address-layer/tree coordinates for one trajectory entry. -/
def traceEntry {vp : ValidatedParams} (pos : LayerPosition vp) : List ℕ :=
  [pos.layer.val, pos.tree.val, pos.leaf.val, pos.toAdrs.layer, pos.toAdrs.tree]

/-- Exact observable hypertree trajectory. -/
def trace (vp : ValidatedParams) (parts : DigestParts vp.params) :
    Vector (List ℕ) vp.params.d :=
  (trajectory vp parts).map traceEntry

@[simp]
theorem trajectory_get (vp : ValidatedParams) (parts : DigestParts vp.params)
    (j : Fin vp.params.d) :
    (trajectory vp parts).get j = LayerPosition.atLayer vp parts j := by
  change (Vector.ofFn (LayerPosition.atLayer vp parts))[j.val] = _
  exact Vector.getElem_ofFn j.isLt

@[simp]
theorem trace_get (vp : ValidatedParams) (parts : DigestParts vp.params)
    (j : Fin vp.params.d) :
    (trace vp parts).get j = traceEntry (LayerPosition.atLayer vp parts j) := by
  change ((Vector.ofFn (LayerPosition.atLayer vp parts)).map traceEntry)[j.val] = _
  rw [Vector.getElem_map, Vector.getElem_ofFn]

/-- The trace starts with the exact digest-derived tree and leaf. -/
theorem trace_zero (vp : ValidatedParams) (parts : DigestParts vp.params) :
    (trace vp parts).get ⟨0, vp.valid.d_pos⟩ =
      [0, parts.idxTree.val, parts.idxLeaf.val, 0, parts.idxTree.val] := by
  rw [trace_get, LayerPosition.atLayer_zero_eq_initial]
  rfl

/-- Every adjacent trace entry applies the FIPS low-bits/high-bits transition and propagates the
new layer/tree coordinates into the XMSS base address. -/
theorem trace_succ (vp : ValidatedParams) (parts : DigestParts vp.params)
    (j : Fin vp.params.d) (hnext : j.val + 1 < vp.params.d) :
    let current := LayerPosition.atLayer vp parts j
    (trace vp parts).get ⟨j.val + 1, hnext⟩ =
      [j.val + 1, current.tree.val / 2 ^ vp.params.hp,
        current.tree.val % 2 ^ vp.params.hp,
        j.val + 1, current.tree.val / 2 ^ vp.params.hp] := by
  rw [trace_get, LayerPosition.atLayer_succ_eq_next vp parts j hnext]
  simp [traceEntry]

end HypertreeConformance

end SLHDSA
