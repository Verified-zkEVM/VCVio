/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.CacheRefinement.Cost

/-!
# Weighted settled-path cache and miss-order controls

These height-zero, height-one and height-two programs retain complete 256-bit raw replies.
A stateful miss handler makes a change in miss order observable.
Each physical call pays its input-dependent weight before cache lookup.
Only sibling subtrees are programmed; the selected leaf and its ancestors sample afresh.
An unrelated high-bit row tests retention of the entire cache.
-/

public section

open OracleComp OracleSpec PerfectMerkleTree

namespace VCVioTest.MerkleTreeCostRefinement

/-- Expand only the public writer execution law before checking finite interpreter runs. -/
private theorem cost_impl_eq {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (so : QueryImpl spec m) (w : spec.Domain → Nat) :
    so.withAddCost w = fun t =>
      WriterT.mk ((fun a => (a, Multiplicative.ofAdd (w t))) <$> so t) := by
  funext t
  apply WriterT.ext
  simp [QueryImpl.withAddCost_apply, AddWriterT.addTell, WriterT.run_bind]

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

/-- Each raw input has a distinct positive weight. -/
private def weight (q : Nat) : Nat := q + 1

/-- The sibling program's four calls have this exact weighted score. -/
private def deltaFor (r : Fin 4) : Nat :=
  match r.val with
  | 0 => 163
  | 1 => 162
  | 2 => 160
  | _ => 159

/-- The three calls on the selected spine have this exact weighted score. -/
private def shortCost (r : Fin 4) : Nat :=
  match r.val with
  | 0 => 254
  | 1 => 255
  | 2 => 257
  | _ => 258

/-- The actual smaller partial cache settles both the path and its declared score. -/
private theorem scored_paths (r : Fin 4) :
    simulateQ (pathCache (12 + r.val)).toPartialImpl
      (simulateQ ((QueryImpl.id' rawSpec).withAddCost weight)
        (intrinsicAuthPathM leaf nodeHash (12 + r.val) 2)).runAdd =
          some (pathFor r, deltaFor r) := by
  fin_cases r <;> dsimp only [rawSpec] <;> simp only [cost_impl_eq] <;> decide

/-- All four global leaf residues retain the exact full-cache endpoint offset. -/
private theorem all_residues_joint (r : Fin 4) :
    ((simulateQ (miss.withCaching.withAddCost weight)
      (merkleRootM leaf nodeHash 2 3)).runAdd).run (liveCache (12 + r.val)) =
      (fun z : (Nat × Nat) × rawSpec.QueryCache =>
        ((z.1.1, z.1.2 + deltaFor r), z.2)) <$>
      ((simulateQ (miss.withCaching.withAddCost weight) (do
        let y ← leaf (12 + r.val)
        climbM nodeHash (12 + r.val) y (pathFor r).toList)).runAdd).run
          (liveCache (12 + r.val)) := by
  have hle : pathCache (12 + r.val) ≤ liveCache (12 + r.val) :=
    QueryCache.le_cacheQuery (cache := pathCache (12 + r.val)) (t := 99) (u := marker)
      (by simp [pathCache])
  have hparent : (12 + r.val) / 2 ^ 2 = 3 := by omega
  simpa only [hparent] using run_simulateQ_merkleRootM_cost_offset_of_path_score
    miss weight leaf nodeHash (12 + r.val) 2 hle (pathFor r) (deltaFor r) (scored_paths r)

/-- The full traversal pays 417 and samples only the three unsettled spine calls in order. -/
private theorem full_observations (r : Fin 4) :
    let z := ((((simulateQ (miss.withCaching.withAddCost weight)
      (merkleRootM leaf nodeHash 2 3)).runAdd).run (liveCache (12 + r.val))).run 5).run
    (z.1.1.1, z.1.1.2, z.2, z.1.2 (12 + r.val), z.1.2 (110 + (12 + r.val) / 2),
      z.1.2 123, z.1.2 99) =
      (rootFor r, 417, 8, some (BitVec.ofNat 256 5), some (BitVec.ofNat 256 6),
        some (BitVec.ofNat 256 7), some marker) := by
  fin_cases r <;> dsimp only [rawSpec] <;> simp only [cost_impl_eq, Prod.mk.injEq] <;> decide

/-- The residual's independently checked score differs by the actual path score. -/
private theorem short_observations (r : Fin 4) :
    let z := ((((simulateQ (miss.withCaching.withAddCost weight) (do
      let y ← leaf (12 + r.val)
      climbM nodeHash (12 + r.val) y (pathFor r).toList)).runAdd).run
        (liveCache (12 + r.val))).run 5).run
    (z.1.1.1, z.1.1.2, z.2, z.1.2 99) = (rootFor r, shortCost r, 8, some marker) := by
  fin_cases r <;> dsimp only [rawSpec] <;> simp only [cost_impl_eq, Prod.mk.injEq] <;> decide

/-- A height-zero path costs zero while its global selected leaf still pays its own weight. -/
private theorem height_zero :
    simulateQ (∅ : rawSpec.QueryCache).toPartialImpl
      (simulateQ ((QueryImpl.id' rawSpec).withAddCost weight)
        (intrinsicAuthPathM leaf nodeHash 37 0)).runAdd = some (#v[], 0) ∧
    let z := ((((simulateQ (miss.withCaching.withAddCost weight)
      (merkleRootM leaf nodeHash 0 37)).runAdd).run ∅).run 5).run
    (z.1.1.1, z.1.1.2, z.2) = (5, 38, 6) := by
  dsimp only [rawSpec]
  simp only [cost_impl_eq]
  decide

/-- Both parity branches keep child order and charge every warm sibling call. -/
private theorem height_one :
    let evenCache := (∅ : rawSpec.QueryCache).cacheQuery 1 (BitVec.ofNat 256 3)
    let oddCache := (∅ : rawSpec.QueryCache).cacheQuery 0 (BitVec.ofNat 256 3)
    let even := ((((simulateQ (miss.withCaching.withAddCost weight)
      (merkleRootM leaf nodeHash 1 0)).runAdd).run evenCache).run 5).run
    let odd := ((((simulateQ (miss.withCaching.withAddCost weight)
      (merkleRootM leaf nodeHash 1 0)).runAdd).run oddCache).run 5).run
    (even.1.1.1, even.1.1.2, even.2, odd.1.1.1, odd.1.1.2, odd.2) =
      (536, 114, 7, 356, 114, 7) := by
  dsimp only [rawSpec]
  simp only [cost_impl_eq]
  decide

/-- All raw calls alias one warm row, and the leaf makes the same call twice. -/
private def aliasLeaf (_ : Nat) : OracleComp rawSpec (BitVec 256) := do
  let _ ← query (spec := rawSpec) 0
  query (spec := rawSpec) 0

/-- Each internal hash makes one more call at that same raw input. -/
private def aliasNode (_ _ : Nat) (_ _ : BitVec 256) : OracleComp rawSpec (BitVec 256) :=
  query (spec := rawSpec) 0

/-- Repeated hits retain the full high-bit answer and cost five versus three physical calls. -/
private theorem aliased_warm :
    let c := (∅ : rawSpec.QueryCache).cacheQuery 0 marker
    let full := ((((simulateQ (miss.withCaching.withAddCost (fun _ => 1))
      (merkleRootM aliasLeaf aliasNode 1 0)).runAdd).run c).run 23).run
    let short := ((((simulateQ (miss.withCaching.withAddCost (fun _ => 1)) (do
      let y ← aliasLeaf 0
      climbM aliasNode 0 y [marker])).runAdd).run c).run 23).run
    (full.1.1.1, full.1.1.2, full.2, short.1.1.1, short.1.1.2, short.2) =
      (marker, 5, 23, marker, 3, 23) := by
  dsimp only [rawSpec]
  simp only [cost_impl_eq]
  decide

/-- A normal error payload is an ordinary returned value, so its charge remains observable. -/
private def normalErrorLeaf (idx : Nat) : OracleComp rawSpec (Except Nat Nat) :=
  OracleComp.queryBind idx fun w => pure (.error w.toNat)

/-- This parent retains the left child's normal error payload. -/
private def normalErrorNode (_ _ : Nat) (left _ : Except Nat Nat) :
    OracleComp rawSpec (Except Nat Nat) := pure left

/-- Normal errors keep their data and writer charge in both completed runs. -/
private theorem normal_error_payload :
    let c := ((∅ : rawSpec.QueryCache).cacheQuery 0 (BitVec.ofNat 256 5)).cacheQuery 1
      (BitVec.ofNat 256 3)
    let full := ((((simulateQ (miss.withCaching.withAddCost (fun _ => 1))
      (merkleRootM normalErrorLeaf normalErrorNode 1 0)).runAdd).run c).run 23).run
    let short := ((((simulateQ (miss.withCaching.withAddCost (fun _ => 1)) (do
      let y ← normalErrorLeaf 0
      climbM normalErrorNode 0 y [.error 3])).runAdd).run c).run 23).run
    (full.1.1, full.2, short.1.1, short.2) = ((.error 5, 2), 23, (.error 5, 1), 23) := by
  dsimp only [rawSpec]
  simp only [cost_impl_eq]
  rfl

/-- A genuine base-monad failure retains sampler state but discards the outer writer result. -/
private def failingMiss : QueryImpl rawSpec (ExceptT Nat (StateT Nat Id)) := fun q => do
  let n : Nat ← get
  modify (· + 1)
  if q = 110 then throw 99 else pure (BitVec.ofNat 256 n)

/-- Both traversals retain the failure payload and miss-state prefix, with no returned charge. -/
private theorem true_failure :
    let c := (∅ : rawSpec.QueryCache).cacheQuery 1 (BitVec.ofNat 256 3)
    let full := (((((simulateQ (failingMiss.withCaching.withAddCost weight)
      (merkleRootM leaf nodeHash 1 0)).runAdd).run c).run).run 5).run
    let short := (((((simulateQ (failingMiss.withCaching.withAddCost weight) (do
      let y ← leaf 0
      climbM nodeHash 0 y [3])).runAdd).run c).run).run 5).run
    full = (.error 99, 7) ∧ short = (.error 99, 7) := by
  dsimp only [rawSpec]
  simp only [cost_impl_eq]
  constructor <;> rfl

/-- A missing sibling does not provide a scored settled-path witness. -/
private theorem unknown_path :
    simulateQ (∅ : rawSpec.QueryCache).toPartialImpl
      (simulateQ ((QueryImpl.id' rawSpec).withAddCost weight)
        (intrinsicAuthPathM leaf nodeHash 0 1)).runAdd = none := by
  dsimp only [rawSpec]
  simp only [cost_impl_eq]
  decide

universe v

/-- Ordinary clients retain all target effects along with the exact weighted endpoint shift. -/
theorem joint_cost_offset {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m] {Y : Type}
    (so : QueryImpl spec m) (w : spec.Domain → Nat)
    (leaf : Nat → OracleComp spec Y) (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y)
    (idx h : Nat) {known live : spec.QueryCache} (hle : known ≤ live)
    (path : Vector Y h) (delta : Nat)
    (hscore : simulateQ known.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w)
        (intrinsicAuthPathM leaf nodeHash idx h)).runAdd = some (path, delta)) :
    ((simulateQ (so.withCaching.withAddCost w)
      (merkleRootM leaf nodeHash h (idx / 2 ^ h))).runAdd).run live =
      (fun z : (Y × Nat) × spec.QueryCache => ((z.1.1, z.1.2 + delta), z.2)) <$>
        ((simulateQ (so.withCaching.withAddCost w)
          (do let y ← leaf idx; climbM nodeHash idx y path.toList)).runAdd).run live :=
  run_simulateQ_merkleRootM_cost_offset_of_path_score
    so w leaf nodeHash idx h hle path delta hscore

end VCVioTest.MerkleTreeCostRefinement
