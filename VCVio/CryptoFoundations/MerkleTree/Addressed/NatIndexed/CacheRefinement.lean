/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Root reconstruction from a settled authentication path

Successful evaluation of the path program under a partial cache settles its sibling subtrees.
Every raw query reached by those subtrees must be settled.
Replaying them leaves the entire cache unchanged and never calls the miss handler.
The full root has the same result and final cache as the selected leaf followed by its climb.
This holds for every lawful target monad.
The two programs need not make the same number of physical oracle calls.
-/

public section

namespace PerfectMerkleTree

open OracleComp OracleSpec

universe u v

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι} {Y : Type u}

/-- Interpreting a cached free run preserves the complete result and cache. -/
private theorem simulateQ_cached_free {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (so : QueryImpl spec m) {α : Type u} (oa : OracleComp spec α) (cache : spec.QueryCache) :
    simulateQ so ((simulateQ (QueryImpl.id' spec).withCaching oa).run cache) =
      (simulateQ so.withCaching oa).run cache := by
  apply simulateQ_StateT_compose (QueryImpl.id' spec).withCaching so so.withCaching
  intro t c
  cases hc : c t <;> simp [QueryImpl.withCaching_apply, hc]

/-- A settled sibling remains a pure replay after any cached free prefix. -/
private theorem free_settled_suffix {α β γ : Type u} (pre : OracleComp spec α)
    (settled : OracleComp spec β) (k : α → β → spec.QueryCache → OracleComp spec γ)
    (cache : spec.QueryCache) {b : β}
    (hb : simulateQ cache.toPartialImpl settled = some b) :
    ((simulateQ (QueryImpl.id' spec).withCaching pre).run cache >>= fun p =>
      (simulateQ (QueryImpl.id' spec).withCaching settled).run p.2 >>= fun q =>
        k p.1 q.1 q.2) =
      ((simulateQ (QueryImpl.id' spec).withCaching pre).run cache >>= fun p => k p.1 b p.2) := by
  apply OracleComp.bind_congr_of_forall_mem_support
  intro p hp
  -- The prefix cannot overwrite a settled response, even when queries alias.
  have hle := QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching
    (QueryImpl.id' spec) pre hp
  rw [QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl
    (QueryImpl.id' spec) settled (QueryCache.simulateQ_toPartialImpl_mono hle settled hb)]
  simp

/-- In the free miss world, settled siblings remove only cache hits from the full traversal. -/
private theorem free_root_eq_leaf_climb (leaf : Nat → OracleComp spec Y)
    (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y) (h idx : Nat)
    (cache : spec.QueryCache) (path : Vector Y h)
    (hpath : simulateQ cache.toPartialImpl (intrinsicAuthPathM leaf nodeHash idx h) = some path) :
    (simulateQ (QueryImpl.id' spec).withCaching
      (merkleRootM leaf nodeHash h (idx / 2 ^ h))).run cache =
      (simulateQ (QueryImpl.id' spec).withCaching (do
        let y ← leaf idx
        climbM nodeHash idx y path.toList)).run cache := by
  induction h generalizing idx cache with
  | zero =>
    have hp : path = #v[] := Vector.eq_empty
    subst path
    simp [merkleRootM]
  | succ h ih =>
    obtain ⟨pre, sib, hpre, hsib, rfl⟩ :=
      (simulateQ_intrinsicAuthPathM_succ_eq_some_iff cache.toPartialImpl
        leaf nodeHash idx h).mp hpath
    have hdiv : idx / 2 ^ (h + 1) = idx / 2 ^ h / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    by_cases heven : idx / 2 ^ h % 2 = 0
    · have hl : 2 * (idx / 2 ^ (h + 1)) = idx / 2 ^ h := by omega
      have hr : 2 * (idx / 2 ^ (h + 1)) + 1 = sibling (idx / 2 ^ h) := by
        simp only [sibling, heven, ↓reduceIte]
        omega
      calc
        _ = ((simulateQ (QueryImpl.id' spec).withCaching
            (merkleRootM leaf nodeHash h (idx / 2 ^ h))).run cache >>= fun p =>
            (simulateQ (QueryImpl.id' spec).withCaching
              (merkleRootM leaf nodeHash h (sibling (idx / 2 ^ h)))).run p.2 >>= fun q =>
              (simulateQ (QueryImpl.id' spec).withCaching
                (nodeHash (h + 1) (idx / 2 ^ (h + 1)) p.1 q.1)).run q.2) := by
          rw [merkleRootM, hr, hl]
          simp only [simulateQ_bind, StateT.run_bind]
        -- The right sibling is settled before the selected left subtree starts.
        _ = ((simulateQ (QueryImpl.id' spec).withCaching
            (merkleRootM leaf nodeHash h (idx / 2 ^ h))).run cache >>= fun p =>
              (simulateQ (QueryImpl.id' spec).withCaching
                (nodeHash (h + 1) (idx / 2 ^ (h + 1)) p.1 sib)).run p.2) :=
          free_settled_suffix (merkleRootM leaf nodeHash h (idx / 2 ^ h))
            (merkleRootM leaf nodeHash h (sibling (idx / 2 ^ h)))
            (fun y s c => (simulateQ (QueryImpl.id' spec).withCaching
              (nodeHash (h + 1) (idx / 2 ^ (h + 1)) y s)).run c) cache hsib
        _ = _ := by
          rw [ih idx cache pre hpre]
          simp only [Vector.toList_push, climbM_concat, Vector.length_toList, heven,
            ↓reduceIte, simulateQ_bind, StateT.run_bind, bind_assoc]
    · have hl : 2 * (idx / 2 ^ (h + 1)) = sibling (idx / 2 ^ h) := by
        simp only [sibling, heven, ↓reduceIte]
        omega
      have hr : 2 * (idx / 2 ^ (h + 1)) + 1 = idx / 2 ^ h := by omega
      -- The settled left sibling frames the starting cache before the selected right subtree.
      rw [merkleRootM, hr, hl]
      simp only [simulateQ_bind, StateT.run_bind]
      rw [QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl
        (QueryImpl.id' spec) _ hsib, pure_bind]
      rw [ih idx cache pre hpre]
      simp only [Vector.toList_push, climbM_concat, Vector.length_toList, heven,
        ↓reduceIte, simulateQ_bind, StateT.run_bind, bind_assoc]

/-- A settled path program permits root reconstruction in any lawful miss handler.
The selected leaf and climb retain the full root result and entire final cache.
The premise evaluates the path program under a partial cache.
That cache may be smaller than the initial live cache.
Indices retain their global subtree offsets.
No equality of physical query counts is asserted.
-/
theorem run_simulateQ_merkleRootM_eq_run_climbM_of_path_settled
    {m : Type u → Type v} [Monad m] [LawfulMonad m] (so : QueryImpl spec m)
    (leaf : Nat → OracleComp spec Y) (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y)
    (idx h : Nat) {known live : spec.QueryCache} (hle : known ≤ live) (path : Vector Y h)
    (hpath : simulateQ known.toPartialImpl (intrinsicAuthPathM leaf nodeHash idx h) = some path) :
    (simulateQ so.withCaching (merkleRootM leaf nodeHash h (idx / 2 ^ h))).run live =
      (simulateQ so.withCaching (do
        let y ← leaf idx
        climbM nodeHash idx y path.toList)).run live := by
  -- Interpret the same free miss program, retaining all target effects on both sides.
  have hfree := free_root_eq_leaf_climb leaf nodeHash h idx live path
    (QueryCache.simulateQ_toPartialImpl_mono hle _ hpath)
  simpa only [simulateQ_cached_free] using congrArg (simulateQ so) hfree

end PerfectMerkleTree
