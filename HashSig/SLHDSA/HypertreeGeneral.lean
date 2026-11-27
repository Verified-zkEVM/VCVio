/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Hypertree
public import HashSig.SLHDSA.Position
public import HashSig.SLHDSA.Hypertree.Program

/-!
# General SLH-DSA hypertree (FIPS 205 Algorithms 12--13)

This module lifts the established XMSS construction from the one-layer specialization to every
validated SLH-DSA parameter set.  A signature has exactly `d` XMSS components, stored in increasing
layer order.  The signer and root-recovery program share the FIPS low-bits/high-bits position
recurrence.

The layer-zero root recovery in Algorithm 12 is unconditional.  Consequently the `d = 1` signer
performs the discarded recovery prescribed by FIPS even though its layer loop body is empty.
For `d > 1`, the final (top-layer) XMSS signature is not recovered by the signer.

## References

- NIST FIPS 205, Section 7, Algorithms 12--13
-/

@[expose] public section

namespace SLHDSA.GeneralHypertree

open OracleComp

/-- The canonical intrinsic hypertree signature from `Hypertree`.  This namespace introduces the
arbitrary-depth algorithms, not a second representation of their output. -/
abbrev Signature (vp : ValidatedParams) (core : CorePrimitives vp.params) :=
  HtSigCore vp.params core

/-- The base XMSS address at a particular hypertree layer and tree. -/
def layerAdrs (layer tree : ℕ) : Adrs :=
  (Adrs.zero.setLayerAddress layer).setTreeAddress tree

@[simp]
theorem layerAdrs_layer (layer tree : ℕ) : (layerAdrs layer tree).layer = layer := rfl

@[simp]
theorem layerAdrs_tree (layer tree : ℕ) : (layerAdrs layer tree).tree = tree := rfl

/-- A reachable final-layer position uses exactly the unique top-tree address committed by key
generation. -/
theorem LayerPosition.toAdrs_eq_layerAdrs_of_isFinal {vp : ValidatedParams}
    (pos : LayerPosition vp)
    (hfinal : pos.layer.val + 1 = vp.params.d) :
    pos.toAdrs = layerAdrs (vp.params.d - 1) 0 := by
  have hlayer : pos.layer.val = vp.params.d - 1 := by omega
  have htree : pos.tree.val = 0 :=
    LayerPosition.tree_eq_zero_of_isFinal pos hfinal
  simp [LayerPosition.toAdrs, layerAdrs, Adrs.zero, Adrs.setLayerAddress,
    Adrs.setTreeAddress, hlayer, htree]

/-- A typed layer position carrying its exact number of remaining components. -/
abbrev RemainingPosition (vp : ValidatedParams) (layers : Nat) :=
  { position : LayerPosition vp // position.layer.val + layers = vp.params.d }

/-- Advance one typed position while retaining the remaining-component invariant. -/
def nextRemainingPosition (vp : ValidatedParams) (layers : Nat)
    (position : RemainingPosition vp (layers + 2)) : RemainingPosition vp (layers + 1) :=
  ⟨position.val.next (by have := position.property; omega), by
    simp only [LayerPosition.next_layer_val]
    have := position.property
    omega⟩

/-- Typed structural loop for FIPS Algorithm 12.

The public helper accepts either `recoverFinal` flag; it affects only a singleton entry. The full
signer chooses true exactly at `d = 1`. Every non-final component is recovered to
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
      m (Vector (XmssSig vp.params core) layers) :=
  fun layers remaining message =>
    Hypertree.Program.signLayers (nextRemainingPosition vp)
      (fun _ current value =>
        xmssSignWith core hash compress nodeHash value sk pk
          current.val.toAdrs current.val.leaf.val)
      (fun _ current signature value =>
        xmssPkFromSigWith core hash compress nodeHash current.val.leaf.val signature value
          current.val.toAdrs)
      recoverFinal layers ⟨pos, remaining⟩ message

/-- Typed structural loop for FIPS Algorithm 13. Its public-hash callbacks capture the seed.
It consumes one signature per layer and threads each recovered root into the next position. -/
def recoverFromPositionWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      Vector (XmssSig vp.params core) layers → m core.Y :=
  fun layers remaining message signatures =>
    Hypertree.Program.recoverLayers (nextRemainingPosition vp)
      (fun _ current signature value =>
        xmssPkFromSigWith core hash compress nodeHash current.val.leaf.val signature value
          current.val.toAdrs)
      layers ⟨pos, remaining⟩ message signatures

/-- The zero component equation for the typed signer. -/
theorem signFromPositionWith_zero (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp)
    (remaining : pos.layer.val + (0) = vp.params.d) (message : core.Y) :
    signFromPositionWith vp core hash compress nodeHash sk pk recoverFinal pos (0)
      remaining message =
      (pure #v[] : m (Vector (XmssSig vp.params core) (0))) := rfl

/-- The one component equation for the typed signer. -/
theorem signFromPositionWith_one (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp)
    (remaining : pos.layer.val + (1) = vp.params.d) (message : core.Y) :
    signFromPositionWith vp core hash compress nodeHash sk pk recoverFinal pos (1)
      remaining message =
      (do
        let sig ← xmssSignWith core hash compress nodeHash message sk pk pos.toAdrs pos.leaf.val
        if recoverFinal then
          let _ ← xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig message pos.toAdrs
          return #v[sig]
        else
          return #v[sig] : m (Vector (XmssSig vp.params core) (1))) := rfl

/-- The add two component equation for the typed signer. -/
theorem signFromPositionWith_add_two (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp)
    (layers : Nat) (remaining : pos.layer.val + (layers + 2) = vp.params.d) (message : core.Y) :
    signFromPositionWith vp core hash compress nodeHash sk pk recoverFinal pos (layers +
      2) remaining message =
      (do
        let sig ← xmssSignWith core hash compress nodeHash message sk pk pos.toAdrs pos.leaf.val
        let root ←
          xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig message pos.toAdrs
        let next := pos.next (by omega)
        let rest ← signFromPositionWith vp core hash compress nodeHash sk pk false next
          (layers + 1) (by simp [next]; omega) root
        return rest.insertIdx 0 sig : m (Vector (XmssSig vp.params core) (layers + 2))) := rfl

/-- The zero component equation for the typed recovery. -/
theorem recoverFromPositionWith_zero (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (pos : LayerPosition vp)
    (remaining : pos.layer.val + (0) = vp.params.d) (message : core.Y)
    (signatures : Vector (XmssSig vp.params core) (0)) :
    recoverFromPositionWith vp core hash compress nodeHash pos (0) remaining message
      signatures =
      (pure message : m core.Y) := rfl

/-- The one component equation for the typed recovery. -/
theorem recoverFromPositionWith_one (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (pos : LayerPosition vp)
    (remaining : pos.layer.val + (1) = vp.params.d) (message : core.Y)
    (signatures : Vector (XmssSig vp.params core) (1)) :
    recoverFromPositionWith vp core hash compress nodeHash pos (1) remaining message
      signatures =
      (xmssPkFromSigWith core hash compress nodeHash pos.leaf.val signatures.head message
        pos.toAdrs : m core.Y) := rfl

/-- The add two component equation for the typed recovery. -/
theorem recoverFromPositionWith_add_two (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (pos : LayerPosition vp)
    (layers : Nat) (remaining : pos.layer.val + (layers + 2) = vp.params.d) (message : core.Y)
    (signatures : Vector (XmssSig vp.params core) (layers + 2)) :
    recoverFromPositionWith vp core hash compress nodeHash pos (layers + 2) remaining
      message signatures =
      (do
        let root ←
          xmssPkFromSigWith core hash compress nodeHash pos.leaf.val
            signatures.head message pos.toAdrs
        let next := pos.next (by omega)
        recoverFromPositionWith vp core hash compress nodeHash next (layers + 1)
          (by simp [next]; omega) root signatures.tail : m core.Y) := rfl

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
    (msg : core.Y) (sig : Signature vp core)
    (parts : DigestParts vp.params) : m core.Y :=
  let pos := LayerPosition.initial vp parts
  recoverFromPositionWith vp core hash compress nodeHash pos vp.params.d
    (by simp [pos]) msg sig

/-! ## Pure typed structural loops -/

/-- Pure typed layer signing with the same entry-sensitive component schedule. -/
def signFromPosition (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → prims.Y →
      Vector (XmssSig vp.params prims.core) layers :=
  fun layers remaining message =>
    Hypertree.Program.signLayers (m := Id) (nextRemainingPosition vp)
      (fun _ current value =>
        xmssSign prims value sk pk current.val.toAdrs current.val.leaf.val)
      (fun _ current signature value =>
        xmssPkFromSig prims current.val.leaf.val signature value pk current.val.toAdrs)
      recoverFinal layers ⟨pos, remaining⟩ message

/-- Deterministic specialization of FIPS Algorithm 13 over the same typed trajectory. -/
def recoverFromPosition (vp : ValidatedParams) (prims : Primitives vp.params)
    (pk : prims.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → prims.Y →
      Vector (XmssSig vp.params prims.core) layers → prims.Y :=
  fun layers remaining message signatures =>
    Hypertree.Program.recoverLayers (m := Id) (nextRemainingPosition vp)
      (fun _ current signature value =>
        xmssPkFromSig prims current.val.leaf.val signature value pk current.val.toAdrs)
      layers ⟨pos, remaining⟩ message signatures

/-- The zero component equation for the typed signer. -/
theorem signFromPosition_zero (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp)
    (remaining : pos.layer.val + (0) = vp.params.d) (message : prims.Y) :
    signFromPosition vp prims sk pk recoverFinal pos (0) remaining
      message =
      (#v[] : Vector (XmssSig vp.params prims.core) (0)) := rfl

/-- The one component equation for the typed signer. -/
theorem signFromPosition_one (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp)
    (remaining : pos.layer.val + (1) = vp.params.d) (message : prims.Y) :
    signFromPosition vp prims sk pk recoverFinal pos (1) remaining
      message =
      (let sig := xmssSign prims message sk pk pos.toAdrs pos.leaf.val
        if recoverFinal then
          let _ := xmssPkFromSig prims pos.leaf.val sig message pk pos.toAdrs
          #v[sig]
        else
          #v[sig] : Vector (XmssSig vp.params prims.core) (1)) := rfl

/-- The add two component equation for the typed signer. -/
theorem signFromPosition_add_two (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp)
    (layers : Nat) (remaining : pos.layer.val + (layers + 2) = vp.params.d) (message : prims.Y) :
    signFromPosition vp prims sk pk recoverFinal pos (layers + 2) remaining
      message =
      (let sig := xmssSign prims message sk pk pos.toAdrs pos.leaf.val
        let root := xmssPkFromSig prims pos.leaf.val sig message pk pos.toAdrs
        let next := pos.next (by omega)
        let rest := signFromPosition vp prims sk pk false next (layers + 1)
          (by simp [next]; omega) root
        rest.insertIdx 0 sig : Vector (XmssSig vp.params prims.core) (layers + 2)) := rfl

/-- The zero component equation for the typed recovery. -/
theorem recoverFromPosition_zero (vp : ValidatedParams) (prims : Primitives vp.params)
    (pk : prims.PkSeed) (pos : LayerPosition vp)
    (remaining : pos.layer.val + (0) = vp.params.d) (message : prims.Y)
    (signatures : Vector (XmssSig vp.params prims.core) (0)) :
    recoverFromPosition vp prims pk pos (0) remaining message
      signatures =
      (message : prims.Y) := rfl

/-- The one component equation for the typed recovery. -/
theorem recoverFromPosition_one (vp : ValidatedParams) (prims : Primitives vp.params)
    (pk : prims.PkSeed) (pos : LayerPosition vp)
    (remaining : pos.layer.val + (1) = vp.params.d) (message : prims.Y)
    (signatures : Vector (XmssSig vp.params prims.core) (1)) :
    recoverFromPosition vp prims pk pos (1) remaining message
      signatures =
      (xmssPkFromSig prims pos.leaf.val signatures.head message pk pos.toAdrs : prims.Y) := rfl

/-- The add two component equation for the typed recovery. -/
theorem recoverFromPosition_add_two (vp : ValidatedParams) (prims : Primitives vp.params)
    (pk : prims.PkSeed) (pos : LayerPosition vp)
    (layers : Nat) (remaining : pos.layer.val + (layers + 2) = vp.params.d) (message : prims.Y)
    (signatures : Vector (XmssSig vp.params prims.core) (layers + 2)) :
    recoverFromPosition vp prims pk pos (layers + 2) remaining message
      signatures =
      (let root := xmssPkFromSig prims pos.leaf.val signatures.head message pk pos.toAdrs
        let next := pos.next (by omega)
        recoverFromPosition vp prims pk next (layers + 1) (by simp [next]; omega)
          root signatures.tail : prims.Y) := rfl

/-! ## Explicit-public-hash programs -/

/-- Explicit-public-hash form of the typed structural signing loop.  This is literally the
callback loop above, specialized to the canonical public-hash queries. -/
def signFromPositionM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      m (Vector (XmssSig vp.params core) layers) :=
  signFromPositionWith vp core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) sk pk recoverFinal pos

/-- Explicit-public-hash form of the typed structural recovery loop.  This shares the callback
implementation used by all other interpretations. -/
def recoverFromPositionM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (pk : core.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      Vector (XmssSig vp.params core) layers → m core.Y :=
  recoverFromPositionWith vp core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) pos

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

/-! ## Fixed-answer structural equations -/

/-- Interpreting the explicit-hash structural signer by one fixed total answer function gives
the corresponding pure typed loop. -/
@[simp]
theorem simulateQ_signFromPositionM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    simulateQ answer
        (signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg :
          OracleComp (publicHashSpec core) (Vector (XmssSig vp.params core) layers)) =
      signFromPosition vp (PublicHash.withPublicHash core answer) sk pk recoverFinal pos layers
        hremaining msg := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => rfl
  | one =>
      cases recoverFinal <;>
        simp only [signFromPositionM, signFromPositionWith_one, signFromPosition_one,
          xmssSignWith_publicHash_eq_xmssSignM,
          xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind, simulateQ_pure,
          simulateQ_xmssSignM_withPublicHash, simulateQ_xmssPkFromSigM_withPublicHash,
          Bool.false_eq_true, ↓reduceIte] <;> rfl
  | more layers _ ih =>
      simp only [signFromPositionM] at ih
      simp only [signFromPositionM, signFromPositionWith_add_two, signFromPosition_add_two,
        xmssSignWith_publicHash_eq_xmssSignM,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind, simulateQ_pure,
        simulateQ_xmssSignM_withPublicHash, simulateQ_xmssPkFromSigM_withPublicHash, ih]
      rfl

/-- Interpreting the explicit-hash structural recovery loop by one fixed total answer function
gives the corresponding pure typed loop. -/
@[simp]
theorem simulateQ_recoverFromPositionM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (pk : core.PkSeed) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    simulateQ answer
        (recoverFromPositionM vp core pk pos layers hremaining msg sigs :
          OracleComp (publicHashSpec core) core.Y) =
      recoverFromPosition vp (PublicHash.withPublicHash core answer) pk pos layers hremaining
        msg sigs := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => rfl
  | one =>
      simp only [recoverFromPositionM, recoverFromPositionWith_one, recoverFromPosition_one,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM,
        simulateQ_xmssPkFromSigM_withPublicHash]
  | more layers _ ih =>
      simp only [recoverFromPositionM] at ih
      simp only [recoverFromPositionM, recoverFromPositionWith_add_two, recoverFromPosition_add_two,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind,
        simulateQ_xmssPkFromSigM_withPublicHash, ih]
      rfl

/-! ## Functional correctness -/

private theorem head_insertIdx_zero {X : Type*} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).head = x := by
  simp [Vector.head, Vector.insertIdx_zero]

private theorem tail_insertIdx_zero {X : Type*} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).tail = rest := by
  rw [Vector.insertIdx_zero]
  apply Vector.ext
  intro i hi
  simp [Vector.tail_eq_cast_extract]

/-- Recovering the result of the typed structural signer reaches the unique top-layer XMSS root,
for every positive validated hypertree depth.  The statement is independent of the initial
digest-derived tree and leaf because the typed position recurrence proves that the final tree is
zero. -/
theorem recoverFromPosition_signFromPosition (vp : ValidatedParams)
    (prims : Primitives vp.params) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : prims.Y) :
    recoverFromPosition vp prims pk pos layers hremaining msg
        (signFromPosition vp prims sk pk recoverFinal pos layers hremaining msg) =
      xmssRoot prims sk pk (layerAdrs (vp.params.d - 1) 0) := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero =>
      have := pos.layer.isLt
      omega
  | one =>
      cases recoverFinal <;>
        change xmssPkFromSig prims pos.leaf.val
          (xmssSign prims msg sk pk pos.toAdrs pos.leaf.val) msg pk pos.toAdrs = _
      all_goals
        rw [xmssPkFromSig_xmssSign prims msg sk pk pos.toAdrs pos.leaf.val pos.leaf.isLt]
        rw [LayerPosition.toAdrs_eq_layerAdrs_of_isFinal pos (by omega)]
  | more layers _ ih =>
      simp only [signFromPosition_add_two, recoverFromPosition_add_two]
      rw [head_insertIdx_zero, tail_insertIdx_zero]
      rw [xmssPkFromSig_xmssSign prims msg sk pk pos.toAdrs pos.leaf.val pos.leaf.isLt]
      exact ih false (pos.next (by omega)) _ _

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
  | zero => simp [signFromPositionM, signFromPositionWith_zero]
  | one =>
      cases recoverFinal <;>
        simp [signFromPositionM, signFromPositionWith_one, xmssSignWith_publicHash_eq_xmssSignM,
          xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, xmssSignM_natural core F,
          xmssPkFromSigM_natural core F]
  | more layers _ ih =>
      simp only [signFromPositionM] at ih
      simp [signFromPositionM, signFromPositionWith_add_two, xmssSignWith_publicHash_eq_xmssSignM,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, xmssSignM_natural core F,
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
  | zero => simp [recoverFromPositionM, recoverFromPositionWith_zero]
  | one => simp [recoverFromPositionM, recoverFromPositionWith_one,
      xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, xmssPkFromSigM_natural core F]
  | more layers _ ih =>
      simp only [recoverFromPositionM] at ih
      simp [recoverFromPositionM, recoverFromPositionWith_add_two,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, xmssPkFromSigM_natural core F, ih]

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

/-! ## Pure API equations and completeness -/

/-- The canonical deterministic signer is exactly the pure typed Algorithm 12 loop. -/
theorem sign_eq_signFromPosition (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    sign vp prims msg sk pk parts =
      let pos := LayerPosition.initial vp parts
      signFromPosition vp prims sk pk (vp.params.d == 1) pos vp.params.d
        (by simp [pos]) msg := by
  unfold sign signM
  rw [simulateQ_signFromPositionM_withPublicHash]
  cases prims
  rfl

/-- The canonical deterministic verifier-side root recovery is exactly the pure typed Algorithm
13 loop. -/
theorem pkFromSig_eq_recoverFromPosition (vp : ValidatedParams)
    (prims : Primitives vp.params) (msg : prims.Y)
    (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    pkFromSig vp prims msg sig pk parts =
      let pos := LayerPosition.initial vp parts
      recoverFromPosition vp prims pk pos vp.params.d (by simp [pos]) msg sig := by
  unfold pkFromSig pkFromSigM
  rw [simulateQ_recoverFromPositionM_withPublicHash]
  cases prims
  rfl

/-- The general-hypertree root — the value FIPS 205 Algorithm 18 publishes as `PK.root` — is
the top-layer XMSS root at tree zero. -/
@[simp]
theorem root_eq_xmssRoot (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) :
    root vp prims sk pk = xmssRoot prims sk pk (layerAdrs (vp.params.d - 1) 0) := by
  unfold root rootM rootWith
  change simulateQ (PublicHash.impl prims)
      (xmssRootM prims.core sk pk (layerAdrs (vp.params.d - 1) 0) :
        OracleComp (publicHashSpec prims.core) prims.Y) = _
  exact simulateQ_xmssRootM prims sk pk (layerAdrs (vp.params.d - 1) 0)

/-- Arbitrary-depth hypertree completeness: honest signing and recovery yield the public root. -/
theorem pkFromSig_sign (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    pkFromSig vp prims msg (sign vp prims msg sk pk parts) pk parts = root vp prims sk pk := by
  rw [pkFromSig_eq_recoverFromPosition, sign_eq_signFromPosition, root_eq_xmssRoot]
  exact recoverFromPosition_signFromPosition vp prims sk pk _ _ _ _ _

/-- Deterministic verification is equality with the recovered top root. -/
theorem verify_eq_decide (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y]
    (msg : prims.Y) (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : prims.Y) :
    verify vp prims msg sig pk parts pkRoot =
      decide (pkFromSig vp prims msg sig pk parts = pkRoot) := by
  unfold verify verifyM pkFromSig
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- Honest arbitrary-depth hypertree signatures verify against the top-layer root. -/
theorem verify_sign (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y]
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    verify vp prims msg (sign vp prims msg sk pk parts) pk parts (root vp prims sk pk) = true := by
  rw [verify_eq_decide, pkFromSig_sign]
  simp

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

/-- Fixed-answer arbitrary-depth hypertree completeness.  Signing, recovery, and top-root
generation are interpreted by one total public-hash answer function. -/
theorem simulateQ_pkFromSigM_signM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer (do
      let sig ← signM vp core msg sk pk parts
      pkFromSigM vp core msg sig pk parts) =
    simulateQ answer (rootM vp core sk pk) := by
  simp only [simulateQ_bind, simulateQ_signM_withPublicHash,
    simulateQ_pkFromSigM_withPublicHash, simulateQ_rootM_withPublicHash]
  exact pkFromSig_sign vp (PublicHash.withPublicHash core answer) msg sk pk parts

/-- Fixed-answer arbitrary-depth hypertree verification completeness.  In particular, the
`d = 1` execution retains Algorithm 12's discarded recovery through `signM`. -/
theorem simulateQ_verifyM_signM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    [DecidableEq core.Y]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer (do
      let pkRoot ← rootM vp core sk pk
      let sig ← signM vp core msg sk pk parts
      verifyM vp core msg sig pk parts pkRoot) = true := by
  simp only [simulateQ_bind, simulateQ_rootM_withPublicHash,
    simulateQ_signM_withPublicHash, simulateQ_verifyM_withPublicHash]
  exact verify_sign vp (PublicHash.withPublicHash core answer) msg sk pk parts

end SLHDSA.GeneralHypertree
