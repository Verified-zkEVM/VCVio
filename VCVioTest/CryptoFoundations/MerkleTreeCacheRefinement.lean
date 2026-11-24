/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.CacheRefinement

/-!
# Settled-path cache and miss-order controls

These height-zero, height-one and height-two programs retain complete 256-bit raw replies.
A stateful miss handler makes a change in miss order observable.
Only the sibling subtrees are programmed; the selected leaf and its ancestors sample afresh.
An unrelated high-bit row tests retention of the entire cache.
-/

public section

open OracleComp OracleSpec PerfectMerkleTree

namespace VCVioTest.MerkleTreeCacheRefinement

/-- Every raw response keeps all 256 bits. -/
private abbrev rawSpec : OracleSpec Nat := Nat →ₒ BitVec 256

/-- A miss returns the old sampler counter and advances it once. -/
private def miss : QueryImpl rawSpec (StateT Nat Id) :=
  fun _ => StateT.mk fun n => pure (BitVec.ofNat 256 n, n + 1)

/-- Leaf query indices retain their global offsets. -/
private def leaf (idx : Nat) : OracleComp rawSpec Nat :=
  (fun w => w.toNat) <$> query (spec := rawSpec) idx

/-- Node values distinguish child order as well as the sampled raw reply. -/
private def nodeHash (height idx left right : Nat) : OracleComp rawSpec Nat := do
  let w ← query (spec := rawSpec) (100 + 10 * height + idx)
  pure (100 * left + 10 * right + w.toNat)

/-- Program every height-two sibling query, leaving the selected spine unsettled. -/
private def pathCache (idx : Nat) : rawSpec.QueryCache :=
  QueryCache.ofFn fun q =>
    if (12 ≤ q ∧ q ≤ 15 ∧ q ≠ idx) ∨ (116 ≤ q ∧ q ≤ 117 ∧ q ≠ 110 + idx / 2)
    then some (BitVec.ofNat 256 q) else none

/-- An unread high-bit response must survive every traversal. -/
private def marker : BitVec 256 := BitVec.ofNat 256 (2 ^ 200 + 9)

/-- Extend the settled cache with a row outside every tree callback. -/
private def liveCache (idx : Nat) : rawSpec.QueryCache :=
  (pathCache idx).cacheQuery 99 marker

/-- Authentication paths are ordered from the leaf toward the root. -/
private def pathFor (r : Fin 4) : Vector Nat 2 :=
  match r.val with
  | 0 => #v[13, 1667]
  | 1 => #v[12, 1667]
  | 2 => #v[15, 1446]
  | _ => #v[14, 1446]

/-- Literal root values pin the left/right schedule for all four global leaf residues. -/
private def rootFor (r : Fin 4) : Nat :=
  match r.val with
  | 0 => 80277
  | 1 => 142277
  | 2 => 151167
  | _ => 159167

/-- The smaller programmed cache actually settles each supplied path. -/
private theorem paths_settled (r : Fin 4) :
    simulateQ (pathCache (12 + r.val)).toPartialImpl
      (intrinsicAuthPathM leaf nodeHash (12 + r.val) 2) = some (pathFor r) := by
  fin_cases r <;> dsimp only [rawSpec] <;> decide

/-- The full result and entire live cache agree, not only the sampled output. -/
private theorem all_residues_joint (r : Fin 4) :
    (simulateQ miss.withCaching (merkleRootM leaf nodeHash 2 3)).run (liveCache (12 + r.val)) =
      (simulateQ miss.withCaching (do
        let y ← leaf (12 + r.val)
        climbM nodeHash (12 + r.val) y (pathFor r).toList)).run (liveCache (12 + r.val)) := by
  have hle : pathCache (12 + r.val) ≤ liveCache (12 + r.val) :=
    QueryCache.le_cacheQuery (cache := pathCache (12 + r.val)) (t := 99) (u := marker)
      (by simp [pathCache])
  have hparent : (12 + r.val) / 2 ^ 2 = 3 := by omega
  simpa only [hparent] using
    run_simulateQ_merkleRootM_eq_run_climbM_of_path_settled miss leaf nodeHash
      (12 + r.val) 2 hle (pathFor r) (paths_settled r)

/-- The full traversal samples the selected leaf, its parent and the root in that order. -/
private theorem full_run_observations (r : Fin 4) :
    let z := (((simulateQ miss.withCaching (merkleRootM leaf nodeHash 2 3)).run
      (liveCache (12 + r.val))).run 5).run
    (z.1.1, z.2, z.1.2 (12 + r.val), z.1.2 (110 + (12 + r.val) / 2),
      z.1.2 123, z.1.2 99) =
      (rootFor r, 8, some (BitVec.ofNat 256 5), some (BitVec.ofNat 256 6),
        some (BitVec.ofNat 256 7), some marker) := by
  fin_cases r <;> dsimp only [rawSpec] <;> simp only [Prod.mk.injEq] <;> decide

/-- The reconstruction independently has the same ordered misses and complete high-bit row. -/
private theorem climb_run_observations (r : Fin 4) :
    let z := (((simulateQ miss.withCaching (do
      let y ← leaf (12 + r.val)
      climbM nodeHash (12 + r.val) y (pathFor r).toList)).run
        (liveCache (12 + r.val))).run 5).run
    (z.1.1, z.2, z.1.2 (12 + r.val), z.1.2 (110 + (12 + r.val) / 2),
      z.1.2 123, z.1.2 99) =
      (rootFor r, 8, some (BitVec.ofNat 256 5), some (BitVec.ofNat 256 6),
        some (BitVec.ofNat 256 7), some marker) := by
  fin_cases r <;> dsimp only [rawSpec] <;> simp only [Prod.mk.injEq] <;> decide

/-- A leaf may repeat a physical raw query, while the cache samples it only once. -/
private def repeatedLeaf (idx : Nat) : OracleComp rawSpec Nat := do
  let x ← query (spec := rawSpec) idx
  let y ← query (spec := rawSpec) idx
  pure (x.toNat + y.toNat)

/-- A one-level sibling is warm and the selected leaf remains cold. -/
private def oneLevelCache : rawSpec.QueryCache :=
  (∅ : rawSpec.QueryCache).cacheQuery 1 (BitVec.ofNat 256 3)

/-- An even selected leaf keeps the sampled value on the left of its warm sibling. -/
private theorem even_one_level :
    let z := (((simulateQ miss.withCaching
      (merkleRootM leaf nodeHash 1 0)).run oneLevelCache).run 5).run
    (z.1.1, z.2) = (536, 7) := by decide

/-- An odd selected leaf keeps the warm sibling on its left. -/
private theorem odd_one_level :
    let cache := (∅ : rawSpec.QueryCache).cacheQuery 0 (BitVec.ofNat 256 3)
    let z := (((simulateQ miss.withCaching
      (merkleRootM leaf nodeHash 1 0)).run cache).run 5).run
    (z.1.1, z.2) = (356, 7) := by decide

/-- Repeated raw calls do not create extra miss samples or change the child orientation. -/
private theorem repeated_raw_queries :
    let z := (((simulateQ miss.withCaching
      (merkleRootM repeatedLeaf nodeHash 1 0)).run oneLevelCache).run 5).run
    (z.1.1, z.2) = (1066, 7) := by decide

/-- A cold sibling is not settled by supplying an arbitrary digest in its place. -/
private theorem missing_settlement :
    simulateQ (∅ : rawSpec.QueryCache).toPartialImpl
      (intrinsicAuthPathM leaf nodeHash 0 1) = none := by decide

/-- With an unsettled sibling, replacing it by zero changes the result and miss count. -/
private theorem unsettled_replacement_differs :
    let full := (((simulateQ miss.withCaching
      (merkleRootM leaf nodeHash 1 0)).run ∅).run 5).run
    let short := (((simulateQ miss.withCaching (do
      let y ← leaf 0
      climbM nodeHash 0 y [0])).run ∅).run 5).run
    (full.1.1, full.2) = (567, 8) ∧ (short.1.1, short.2) = (506, 7) := by decide

/-- The empty path needs no sibling settlement and preserves a global leaf index. -/
private theorem height_zero :
    let z := (((simulateQ miss.withCaching
      (merkleRootM leaf nodeHash 0 37)).run ∅).run 5).run
    (z.1.1, z.2, z.1.2 37) = (5, 6, some (BitVec.ofNat 256 5)) := by decide

/-- A failing miss still retains its update of the underlying sampler state. -/
private def failingMiss : QueryImpl rawSpec (ExceptT Unit (StateT Nat Id)) := fun q => do
  let n : Nat ← get
  modify (· + 1)
  if q = 110 then throw () else pure (BitVec.ofNat 256 n)

/-- Failure at the parent keeps the selected-leaf and failing-miss state prefix. -/
private theorem error_prefix_retained :
    let z := ((((simulateQ failingMiss.withCaching
      (merkleRootM leaf nodeHash 1 0)).run oneLevelCache).run).run 5).run
    ((match z.1 with | .error _ => true | .ok _ => false), z.2) = (true, 7) := by decide

universe u v

/-- The public law retains arbitrary sampler state without a support interface on that sampler. -/
theorem stateful_joint_cache {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ Y : Type u}
    (so : QueryImpl spec (StateT σ m)) (leaf : Nat → OracleComp spec Y)
    (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y) (idx h : Nat)
    {known live : spec.QueryCache} (hle : known ≤ live) (path : Vector Y h)
    (hpath : simulateQ known.toPartialImpl (intrinsicAuthPathM leaf nodeHash idx h) = some path)
    (s : σ) :
    ((simulateQ so.withCaching (merkleRootM leaf nodeHash h (idx / 2 ^ h))).run live).run s =
      ((simulateQ so.withCaching (do
        let y ← leaf idx
        climbM nodeHash idx y path.toList)).run live).run s :=
  congrArg (fun f => f.run s)
    (run_simulateQ_merkleRootM_eq_run_climbM_of_path_settled so leaf nodeHash idx h hle path hpath)

end VCVioTest.MerkleTreeCacheRefinement
