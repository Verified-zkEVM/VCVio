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
  ⟨{ n := 1, h := 6, d := 3, hp := 2, a := 1, k := 1, lgw := 1 }, by decide⟩

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

/-- A three-layer, height-two schedule has `16 + 4 + 1` trees, four WOTS leaves per tree, and
three internal nodes per tree. -/
example : (allXmssTrees threeLayer).length = 21 ∧
    (allWotsInstances threeLayer).length = 84 ∧
    (xmssNodeAddresses threeLayer).length = 63 := by decide

end SLHDSATest.ReachableTargets
