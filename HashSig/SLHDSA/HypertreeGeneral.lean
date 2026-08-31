/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Hypertree
public import HashSig.SLHDSA.Position

/-!
# General SLH-DSA hypertree (FIPS 205 Algorithms 12--13)

This module lifts the established XMSS construction from the one-layer specialization to every
validated SLH-DSA parameter set.  A signature has exactly `d` XMSS components, stored in increasing
layer order.  The signer and root-recovery program share the FIPS low-bits/high-bits position
recurrence.

The layer-zero root recovery in Algorithm 12 is unconditional.  Consequently the `d = 1` signer
has the same output as the old one-layer signer but performs the discarded recovery prescribed by
FIPS.  For `d > 1`, the final (top-layer) XMSS signature is not recovered by the signer.

## References

- NIST FIPS 205, Section 7, Algorithms 12--13
-/

@[expose] public section

namespace SLHDSA.GeneralHypertree

open OracleComp

/-- A general hypertree signature contains exactly one XMSS signature for every layer. -/
abbrev Signature (vp : ValidatedParams) (core : CorePrimitives vp.params) :=
  Vector (XmssSig vp.params core) vp.params.d

/-- The base XMSS address at a particular hypertree layer and tree. -/
def layerAdrs (layer tree : ℕ) : Adrs :=
  (Adrs.zero.setLayerAddress layer).setTreeAddress tree

@[simp]
theorem layerAdrs_layer (layer tree : ℕ) : (layerAdrs layer tree).layer = layer := rfl

@[simp]
theorem layerAdrs_tree (layer tree : ℕ) : (layerAdrs layer tree).tree = tree := rfl

/-- Typed structural loop for FIPS Algorithm 12.

`recoverFinal` is true only for the `d = 1` entry call. Every non-final component is recovered to
obtain the message signed at the next layer. The loop invariant states that `layers` is exactly the
number of positions from `pos` through the final layer. -/
def signFromPositionWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      m (Vector (XmssSig vp.params core) layers)
  | 0, _, _ => pure #v[]
  | 1, _, msg => do
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ ← xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
        return #v[sig]
      else
        return #v[sig]
  | layers + 2, hremaining, msg => do
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let root ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
      let next := pos.next (by omega)
      let rest ← signFromPositionWith vp core hash compress nodeHash sk pk false next
        (layers + 1) (by simp [next]; omega) root
      return rest.insertIdx 0 sig

/-- Typed structural loop for FIPS Algorithm 13. It consumes one signature per layer and threads
each recovered XMSS root into the next reachable position. -/
def recoverFromPositionWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (pk : core.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      Vector (XmssSig vp.params core) layers → m core.Y
  | 0, _, msg, _ => pure msg
  | 1, _, msg, sigs =>
      xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sigs.head msg pos.toAdrs
  | layers + 2, hremaining, msg, sigs => do
      let root ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sigs.head msg pos.toAdrs
      let next := pos.next (by omega)
      recoverFromPositionWith vp core hash compress nodeHash pk next (layers + 1)
        (by simp [next]; omega) root sigs.tail

/-! ## Callback-parametric construction -/

/-- FIPS Algorithm 12 for arbitrary positive `d`. -/
def signWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m (Signature vp core) :=
  let pos := LayerPosition.initial vp parts
  signFromPositionWith vp core hash compress nodeHash sk pk (vp.params.d == 1) pos
    vp.params.d (by simp [pos]) msg

/-- Root of the unique top-layer XMSS tree: layer `d - 1`, tree zero. -/
def rootWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) : m core.Y :=
  xmssRootWith core hash compress nodeHash sk pk
    (layerAdrs (vp.params.d - 1) 0)

/-- Recover the public root authenticated by a general hypertree signature. -/
def pkFromSigWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m core.Y :=
  let pos := LayerPosition.initial vp parts
  recoverFromPositionWith vp core hash compress nodeHash pk pos vp.params.d
    (by simp [pos]) msg sig

/-! ## Explicit-public-hash programs -/

/-- Explicit-public-hash form of the typed structural signing loop. -/
def signFromPositionM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      m (Vector (XmssSig vp.params core) layers)
  | 0, _, _ => pure #v[]
  | 1, _, msg => do
      let sig ← xmssSignM core msg sk pk pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ ← xmssPkFromSigM core pos.leaf.val sig msg pk pos.toAdrs
        return #v[sig]
      else
        return #v[sig]
  | layers + 2, hremaining, msg => do
      let sig ← xmssSignM core msg sk pk pos.toAdrs pos.leaf.val
      let root ← xmssPkFromSigM core pos.leaf.val sig msg pk pos.toAdrs
      let next := pos.next (by omega)
      let rest ← signFromPositionM vp core sk pk false next (layers + 1)
        (by simp [next]; omega) root
      return rest.insertIdx 0 sig

/-- Explicit-public-hash form of the typed structural recovery loop. -/
def recoverFromPositionM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (pk : core.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      Vector (XmssSig vp.params core) layers → m core.Y
  | 0, _, msg, _ => pure msg
  | 1, _, msg, sigs =>
      xmssPkFromSigM core pos.leaf.val sigs.head msg pk pos.toAdrs
  | layers + 2, hremaining, msg, sigs => do
      let root ← xmssPkFromSigM core pos.leaf.val sigs.head msg pk pos.toAdrs
      let next := pos.next (by omega)
      recoverFromPositionM vp core pk next (layers + 1) (by simp [next]; omega) root sigs.tail

/-- Canonical explicit-public-hash hypertree signer for arbitrary `d`. -/
def signM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m (Signature vp core) :=
  let pos := LayerPosition.initial vp parts
  signFromPositionM vp core sk pk (vp.params.d == 1) pos vp.params.d
    (by simp [pos]) msg

/-- Canonical explicit-public-hash top-root generation for arbitrary `d`. -/
def rootM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) : m core.Y :=
  rootWith vp core (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) sk pk

/-- Canonical explicit-public-hash hypertree recovery for arbitrary `d`. -/
def pkFromSigM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m core.Y :=
  let pos := LayerPosition.initial vp parts
  recoverFromPositionM vp core pk pos vp.params.d (by simp [pos]) msg sig

/-- Canonical explicit-public-hash hypertree verification for arbitrary `d`. -/
def verifyM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) : m Bool := do
  let recovered ← pkFromSigM vp core msg sig pk parts
  return decide (recovered = pkRoot)

/-! ## Naturality -/

/-- Query-preserving monad morphisms commute with the typed structural signer. -/
theorem signFromPositionM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    F.toMonadHom (signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg) =
      signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => simp [signFromPositionM]
  | one =>
      cases recoverFinal <;>
        simp [signFromPositionM, xmssSignM_natural core F, xmssPkFromSigM_natural core F]
  | more layers _ ih =>
      simp [signFromPositionM, xmssSignM_natural core F,
        xmssPkFromSigM_natural core F, ih]

/-- Query-preserving monad morphisms commute with the typed structural recovery loop. -/
theorem recoverFromPositionM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pk : core.PkSeed) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    F.toMonadHom (recoverFromPositionM vp core pk pos layers hremaining msg sigs) =
      recoverFromPositionM vp core pk pos layers hremaining msg sigs := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => simp [recoverFromPositionM]
  | one => simp [recoverFromPositionM, xmssPkFromSigM_natural core F]
  | more layers _ ih =>
      simp [recoverFromPositionM, xmssPkFromSigM_natural core F, ih]

/-- Query-preserving monad morphisms commute with arbitrary-`d` hypertree signing. -/
theorem signM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    F.toMonadHom (signM vp core msg sk pk parts) = signM vp core msg sk pk parts := by
  exact signFromPositionM_natural vp core F sk pk _ _ _ _ _

/-- Query-preserving monad morphisms commute with top-root generation. -/
theorem rootM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    F.toMonadHom (rootM vp core sk pk) = rootM vp core sk pk := by
  exact xmssRootM_natural core F sk pk (layerAdrs (vp.params.d - 1) 0)

/-- Query-preserving monad morphisms commute with arbitrary-`d` hypertree recovery. -/
theorem pkFromSigM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    F.toMonadHom (pkFromSigM vp core msg sig pk parts) =
      pkFromSigM vp core msg sig pk parts := by
  exact recoverFromPositionM_natural vp core F pk _ _ _ _ _

/-- Query-preserving monad morphisms commute with arbitrary-`d` hypertree verification. -/
theorem verifyM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) :
    F.toMonadHom (verifyM vp core msg sig pk parts pkRoot) =
      verifyM vp core msg sig pk parts pkRoot := by
  simp [verifyM, pkFromSigM_natural vp core F]

/-! ## Pure deterministic interpretations -/

/-- Deterministic general-hypertree signing is the canonical interpretation of `signM`. -/
def sign (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) : Signature vp prims.core :=
  simulateQ (PublicHash.impl prims)
    (signM vp prims.core msg sk pk parts :
      OracleComp (publicHashSpec prims.core) (Signature vp prims.core))

/-- Deterministic top-root generation is the canonical interpretation of `rootM`. -/
def root (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (rootM vp prims.core sk pk : OracleComp (publicHashSpec prims.core) prims.Y)

/-- Deterministic root recovery is the canonical interpretation of `pkFromSigM`. -/
def pkFromSig (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (pkFromSigM vp prims.core msg sig pk parts :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- Deterministic verification is the canonical interpretation of `verifyM`. -/
def verify (vp : ValidatedParams) (prims : Primitives vp.params) [DecidableEq prims.Y]
    (msg : prims.Y) (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : prims.Y) : Bool :=
  simulateQ (PublicHash.impl prims)
    (verifyM vp prims.core msg sig pk parts pkRoot :
      OracleComp (publicHashSpec prims.core) Bool)

/-! ## Deterministic-handler parity -/

@[simp]
theorem simulateQ_signM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer
        (signM vp core msg sk pk parts :
          OracleComp (publicHashSpec core) (Signature vp core)) =
      sign vp (PublicHash.withPublicHash core answer) msg sk pk parts := by
  simp [sign, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_rootM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    simulateQ answer (rootM vp core sk pk : OracleComp (publicHashSpec core) core.Y) =
      root vp (PublicHash.withPublicHash core answer) sk pk := by
  simp [root, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_pkFromSigM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer
        (pkFromSigM vp core msg sig pk parts : OracleComp (publicHashSpec core) core.Y) =
      pkFromSig vp (PublicHash.withPublicHash core answer) msg sig pk parts := by
  simp [pkFromSig, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_verifyM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    [DecidableEq core.Y]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) :
    simulateQ answer
        (verifyM vp core msg sig pk parts pkRoot : OracleComp (publicHashSpec core) Bool) =
      verify vp (PublicHash.withPublicHash core answer) msg sig pk parts pkRoot := by
  simp [verify, PublicHash.impl_withPublicHash]

end SLHDSA.GeneralHypertree
