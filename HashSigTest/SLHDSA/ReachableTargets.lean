/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Security.ReachableTargets

/-!
# Reachable-target ledger canaries

These small executable examples distinguish one-, two-, and three-layer target schedules.  The
two-layer cases pin the order and address fields, so swapping layer order or omitting the top
tree is observable rather than hidden behind the symbolic cardinality theorems.
-/

@[expose] public section

namespace SLHDSATest.ReachableTargets

open SLHDSA SLHDSA.Security

def oneLayer : ValidatedParams :=
  ⟨{ n := 1, h := 1, d := 1, hp := 1, a := 1, k := 1, lgw := 1 }, by decide⟩

def twoLayer : ValidatedParams :=
  ⟨{ n := 1, h := 2, d := 2, hp := 1, a := 1, k := 1, lgw := 1 }, by decide⟩

def threeLayer : ValidatedParams :=
  ⟨{ n := 1, h := 3, d := 3, hp := 1, a := 1, k := 1, lgw := 1 }, by decide⟩

/-- A one-layer hypertree contains one XMSS tree and two WOTS instances. -/
example : (allXmssTrees oneLayer).length = 1 ∧
    (allWotsInstances oneLayer).length = 2 := by decide

/-- The two-layer enumeration is bottom-up and includes both bottom trees and the unique
top tree. -/
example : (allXmssTrees twoLayer).map (fun coord => (coord.layer.val, coord.tree.val)) =
    [(0, 0), (0, 1), (1, 0)] := by decide

/-- WOTS instances refine each two-layer tree by its two leaves without changing layer order. -/
example : (allWotsInstances twoLayer).map
      (fun pos => (pos.layer.val, pos.tree.val, pos.leaf.val)) =
    [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1),
      (1, 0, 0), (1, 0, 1)] := by decide

/-- With height one per XMSS tree, each tree contributes exactly its root address. -/
example : (xmssNodeAddresses twoLayer).map
      (fun adrs => (adrs.layer, adrs.tree, adrs.word2, adrs.word3)) =
    [(0, 0, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0)] := by decide

/-- FORS positions cover every leaf of every bottom-layer tree, in tree-major order. -/
example : (allBottomPositions twoLayer).map (fun pos => (pos.tree.val, pos.leaf.val)) =
    [(0, 0), (0, 1), (1, 0), (1, 1)] := by decide

/-- FORS leaf addresses retain both the bottom XMSS tree and key-pair leaf, and vary the
global FORS node index in the final word. -/
example : (forsLeafAddresses twoLayer).map
      (fun adrs => (adrs.tree, adrs.word1, adrs.word2, adrs.word3)) =
    [(0, 0, 0, 0), (0, 0, 0, 1), (0, 1, 0, 0), (0, 1, 0, 1),
      (1, 0, 0, 0), (1, 0, 0, 1), (1, 1, 0, 0), (1, 1, 0, 1)] := by decide

/-- The three FORS ledgers realize the expected F/H/Tℓ counts for the two-layer canary. -/
example : (forsLeafAddresses twoLayer).length = 8 ∧
    (forsTreeAddresses twoLayer).length = 4 ∧
    (forsRootAddresses twoLayer).length = 4 := by decide

/-- The first reachable WOTS steps traverse chains before leaves, trees, and layers. -/
example : ((wotsStepAddresses twoLayer).take 4).map
      (fun adrs => (adrs.layer, adrs.tree, adrs.word1, adrs.word2, adrs.word3)) =
    [(0, 0, 0, 0, 0), (0, 0, 0, 1, 0),
      (0, 0, 0, 2, 0), (0, 0, 0, 3, 0)] := by decide

/-- The executed `w - 1` step space is strictly below the architecture's loose `w`-per-chain
TCR cap in this profile, while WOTS Tℓ has one target per instance. -/
example : (wotsStepAddresses twoLayer).length = 72 ∧
    targetCount twoLayer.params .wotsFTcr = 144 ∧
    (wotsPkAddresses twoLayer).length = 6 := by decide

/-- A three-layer, height-one schedule has `4 + 2 + 1` trees, two WOTS leaves per tree, and
one internal node per tree. -/
example : (allXmssTrees threeLayer).length = 7 ∧
    (allWotsInstances threeLayer).length = 14 ∧
    (xmssNodeAddresses threeLayer).length = 7 ∧
    (allBottomPositions threeLayer).length = 8 ∧
    (forsLeafAddresses threeLayer).length = 16 := by decide

end SLHDSATest.ReachableTargets
