/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.CacheRefinement
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost

/-!
# The exact query charge of settled sibling subtrees

A settled authentication path determines the charge of its sibling subtree programs.
The full root adds exactly that charge to the selected leaf and climb.
The result and entire final cache agree under any lawful miss handler.
A raw call is a query in the supplied oracle signature.
Every raw call pays its declared natural-number weight before cache lookup, including warm hits.
A failure in the base monad may discard the writer result, so this is no failed-prefix cost law.
-/

public section

namespace PerfectMerkleTree

open OracleComp OracleSpec

universe v

variable {ι : Type} {spec : OracleSpec ι} {Y : Type}

private theorem partial_score_path_succ {Y : Type} (cache : spec.QueryCache)
    (w : spec.Domain → Nat) (leaf : Nat → OracleComp spec Y)
    (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y)
    (idx h : Nat) (pre : Vector Y h) (sib : Y) (d e : Nat)
    (hp : simulateQ cache.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w)
        (intrinsicAuthPathM leaf nodeHash idx h)).runAdd = some (pre, d))
    (hs : simulateQ cache.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w)
        (merkleRootM leaf nodeHash h (sibling (idx / 2 ^ h)))).runAdd = some (sib, e)) :
    simulateQ cache.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w)
        (intrinsicAuthPathM leaf nodeHash idx (h + 1))).runAdd = some (pre.push sib, d + e) := by
  -- Fuse the free score into the partial oracle before composing its two reached binds.
  rw [QueryImpl.simulateQ_withAddCost_runAdd_fusion] at hp hs ⊢
  simp [intrinsicAuthPathM, simulateQ_bind, AddWriterT.runAdd_bind, hp, hs]

private theorem plain_of_partial_score {α : Type} (cache : spec.QueryCache) (w : spec.Domain → Nat)
    (p : OracleComp spec α) (a : α) (delta : Nat)
    (hs : simulateQ cache.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w) p).runAdd = some (a, delta)) :
    simulateQ cache.toPartialImpl p = some a := by
  -- Erasing the charge recovers the original partial interpretation at the same result.
  have erased := congrArg (fun x => Prod.fst <$> x) hs
  rw [QueryImpl.simulateQ_withAddCost_runAdd_fusion, AddWriterT.fst_map_runAdd] at erased
  simpa [QueryImpl.withAddCost, QueryImpl.fst_map_run_withCost] using erased

private theorem partial_score_path_succ_decompose {Y : Type} (cache : spec.QueryCache)
    (w : spec.Domain → Nat) (leaf : Nat → OracleComp spec Y)
    (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y)
    (idx h : Nat) (path : Vector Y (h + 1)) (delta : Nat)
    (hs : simulateQ cache.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w)
        (intrinsicAuthPathM leaf nodeHash idx (h + 1))).runAdd = some (path, delta)) :
    ∃ (pre : Vector Y h) (sib : Y) (d e : Nat),
      simulateQ cache.toPartialImpl
        (simulateQ ((QueryImpl.id' spec).withAddCost w)
          (intrinsicAuthPathM leaf nodeHash idx h)).runAdd = some (pre, d) ∧
      simulateQ cache.toPartialImpl
        (simulateQ ((QueryImpl.id' spec).withAddCost w)
          (merkleRootM leaf nodeHash h (sibling (idx / 2 ^ h)))).runAdd = some (sib, e) ∧
      pre.push sib = path ∧ delta = d + e := by
  -- The score fixes the same path whose prefix and sibling are read from the partial cache.
  have plain := plain_of_partial_score cache w _ path delta hs
  obtain ⟨pre, sib, hpre, hsib, rfl⟩ :=
    (simulateQ_intrinsicAuthPathM_succ_eq_some_iff cache.toPartialImpl leaf nodeHash idx h).mp plain
  obtain ⟨d, hd⟩ := QueryImpl.exists_cost_of_toPartialImpl w _ cache pre hpre
  obtain ⟨e, he⟩ := QueryImpl.exists_cost_of_toPartialImpl w _ cache sib hsib
  refine ⟨pre, sib, d, e, hd, he, rfl, ?_⟩
  -- Compose those two scores before identifying their sum with the supplied score.
  have same := hs.symm.trans (partial_score_path_succ cache w leaf nodeHash idx h pre sib d e hd he)
  exact congrArg Prod.snd (Option.some.inj same)

private theorem simulateQ_cached_free {m : Type → Type v} [Monad m] [LawfulMonad m]
    [DecidableEq ι] (so : QueryImpl spec m) {α : Type}
    (body : OracleComp spec α) (cache : spec.QueryCache) :
    simulateQ so ((simulateQ (QueryImpl.id' spec).withCaching body).run cache) =
      (simulateQ so.withCaching body).run cache := by
  -- State-handler composition preserves the whole cache through the free interpreter.
  apply simulateQ_StateT_compose (QueryImpl.id' spec).withCaching so so.withCaching
  intro t c
  cases hc : c t <;> simp [QueryImpl.withCaching_apply, hc]

private theorem simulateQ_costed_cached_free {m : Type → Type v} [Monad m] [LawfulMonad m]
    [DecidableEq ι] (so : QueryImpl spec m) {α : Type} (w : spec.Domain → Nat)
    (body : OracleComp spec α) (cache : spec.QueryCache) :
    simulateQ so
      (((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) body).runAdd).run cache) =
      ((simulateQ (so.withCaching.withAddCost w) body).runAdd).run cache := by
  -- Fuse the same free score on both sides of the cache interpreter equality.
  rw [← QueryImpl.simulateQ_withAddCost_runAdd_fusion, simulateQ_cached_free,
    QueryImpl.simulateQ_withAddCost_runAdd_fusion]

private theorem free_cost_bind [DecidableEq ι] {α β : Type} (w : spec.Domain → Nat)
    (p : OracleComp spec α) (k : α → OracleComp spec β) (cache : spec.QueryCache) :
    ((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) (p >>= k)).runAdd).run cache =
      (((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) p).runAdd).run cache >>=
        fun x => (fun y => ((y.1.1, x.1.2 + y.1.2), y.2)) <$>
          ((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) (k x.1.1)).runAdd).run
            x.2) := by
  -- Retain the prefix charge while threading its reached cache into the continuation.
  simp [simulateQ_bind, AddWriterT.runAdd_bind, StateT.run_bind, StateT.run_map, Prod.map]

private theorem free_cost_settled_suffix [DecidableEq ι] {α β γ : Type}
    (w : spec.Domain → Nat) (pre : OracleComp spec α) (settled : OracleComp spec β)
    (k : (α × Nat) → (β × Nat) → spec.QueryCache → OracleComp spec γ)
    (cache : spec.QueryCache) (b : β) (delta : Nat)
    (hb : simulateQ cache.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w) settled).runAdd = some (b, delta)) :
    (((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) pre).runAdd).run cache >>=
      fun p => ((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) settled).runAdd).run
        p.2 >>= fun q => k p.1 q.1 q.2) =
      (((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) pre).runAdd).run cache >>=
        fun p => k p.1 (b, delta) p.2) := by
  apply OracleComp.bind_congr_of_forall_mem_support
  intro p hp
  rw [← QueryImpl.simulateQ_withAddCost_runAdd_fusion] at hp
  -- The actual scored prefix can only extend the cache, even when raw queries alias.
  have hle := QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching
    (QueryImpl.id' spec) _ hp
  -- Replay the scored sibling program, keeping its charge along with its answer.
  have replay := QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl
    (QueryImpl.id' spec) _ (QueryCache.simulateQ_toPartialImpl_mono hle _ hb)
  rw [QueryImpl.simulateQ_withAddCost_runAdd_fusion] at replay
  rw [replay, pure_bind]

private theorem free_root_cost_offset [DecidableEq ι] (w : spec.Domain → Nat)
    (leaf : Nat → OracleComp spec Y) (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y)
    (h idx : Nat) (cache : spec.QueryCache) (path : Vector Y h) (delta : Nat)
    (hscore : simulateQ cache.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w)
        (intrinsicAuthPathM leaf nodeHash idx h)).runAdd = some (path, delta)) :
    ((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w)
      (merkleRootM leaf nodeHash h (idx / 2 ^ h))).runAdd).run cache =
      (fun z : (Y × Nat) × spec.QueryCache => ((z.1.1, z.1.2 + delta), z.2)) <$>
        ((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w)
          (do let y ← leaf idx; climbM nodeHash idx y path.toList)).runAdd).run cache := by
  let run {α : Type} (body : OracleComp spec α) (c : spec.QueryCache) :=
    ((simulateQ ((QueryImpl.id' spec).withCaching.withAddCost w) body).runAdd).run c
  have run_bind {α β : Type} (p : OracleComp spec α) (k : α → OracleComp spec β)
      (c : spec.QueryCache) : run (p >>= k) c =
      (run p c >>= fun x => (fun y => ((y.1.1, x.1.2 + y.1.2), y.2)) <$> run (k x.1.1) x.2) :=
    free_cost_bind w p k c
  change run (merkleRootM leaf nodeHash h (idx / 2 ^ h)) cache =
    (fun z : (Y × Nat) × spec.QueryCache => ((z.1.1, z.1.2 + delta), z.2)) <$>
      run (do let y ← leaf idx; climbM nodeHash idx y path.toList) cache
  induction h generalizing idx cache delta with
  | zero =>
    have hp : path = #v[] := Vector.eq_empty
    subst path
    have hd : delta = 0 := by simpa [intrinsicAuthPathM] using hscore.symm
    subst delta
    simp [merkleRootM]
  | succ h ih =>
    -- The supplied path score is the sum of its prefix and final sibling subtree scores.
    obtain ⟨pre, sib, d, e, hd, he, rfl, rfl⟩ :=
      partial_score_path_succ_decompose cache w leaf nodeHash idx h path delta hscore
    by_cases heven : idx / 2 ^ h % 2 = 0
    · have hl : 2 * (idx / 2 ^ (h + 1)) = idx / 2 ^ h := by
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        omega
      have hr : 2 * (idx / 2 ^ (h + 1)) + 1 = sibling (idx / 2 ^ h) := by
        simp only [sibling, heven, ↓reduceIte]
        omega
      calc
        _ = (run (merkleRootM leaf nodeHash h (idx / 2 ^ h)) cache >>= fun p =>
            run (merkleRootM leaf nodeHash h (sibling (idx / 2 ^ h))) p.2 >>= fun q =>
              (fun z => ((z.1.1, p.1.2 + q.1.2 + z.1.2), z.2)) <$>
                run (nodeHash (h + 1) (idx / 2 ^ (h + 1)) p.1.1 q.1.1) q.2) := by
          rw [merkleRootM, hr, hl]
          simp [run_bind, map_bind, Functor.map_map, Nat.add_assoc]
        -- The right sibling replays after the selected left subtree, retaining its charge.
        _ = (run (merkleRootM leaf nodeHash h (idx / 2 ^ h)) cache >>= fun p =>
              (fun z => ((z.1.1, p.1.2 + e + z.1.2), z.2)) <$>
                run (nodeHash (h + 1) (idx / 2 ^ (h + 1)) p.1.1 sib) p.2) :=
          free_cost_settled_suffix w (merkleRootM leaf nodeHash h (idx / 2 ^ h))
            (merkleRootM leaf nodeHash h (sibling (idx / 2 ^ h)))
            (fun p q c => (fun z => ((z.1.1, p.2 + q.2 + z.1.2), z.2)) <$>
              run (nodeHash (h + 1) (idx / 2 ^ (h + 1)) p.1 q.1) c) cache sib e he
        _ = _ := by
          -- Natural-number commutativity moves both settled charges after the common residual.
          rw [ih idx cache pre d hd]
          simp [Vector.toList_push, climbM_concat, heven, run_bind, bind_map_left, map_bind,
            Functor.map_map, bind_assoc, Nat.add_comm, Nat.add_left_comm]
    · have hl : 2 * (idx / 2 ^ (h + 1)) = sibling (idx / 2 ^ h) := by
        simp only [sibling, heven, ↓reduceIte]
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        omega
      have hr : 2 * (idx / 2 ^ (h + 1)) + 1 = idx / 2 ^ h := by
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        omega
      -- The settled left sibling precedes the selected right subtree and frames its cache.
      have replay := QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl
        (QueryImpl.id' spec) _ he
      rw [QueryImpl.simulateQ_withAddCost_runAdd_fusion] at replay
      rw [merkleRootM, hr, hl]
      simp only [run_bind]
      rw [show run (merkleRootM leaf nodeHash h (sibling (idx / 2 ^ h))) cache =
        pure ((sib, e), cache) from replay, pure_bind]
      rw [ih idx cache pre d hd]
      simp [Vector.toList_push, climbM_concat, heven, run_bind, bind_map_left, map_bind,
        Functor.map_map, bind_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A settled scored path is the exact extra query charge of full root reconstruction.
Both traversals retain the same result and entire cache, including unrelated entries.
-/
theorem run_simulateQ_merkleRootM_cost_offset_of_path_score
    {m : Type → Type v} [Monad m] [LawfulMonad m] [DecidableEq ι]
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
          (do let y ← leaf idx; climbM nodeHash idx y path.toList)).runAdd).run live := by
  -- Interpret one free equality so all surviving misses retain their original target effects.
  have hfree := free_root_cost_offset w leaf nodeHash h idx live path delta
    (QueryCache.simulateQ_toPartialImpl_mono hle _ hscore)
  simpa only [simulateQ_map, simulateQ_costed_cached_free] using congrArg (simulateQ so) hfree

/-- Plain path settlement supplies the score witness and the exact full-root cost offset. -/
theorem exists_run_simulateQ_merkleRootM_cost_offset_of_path_settled
    {m : Type → Type v} [Monad m] [LawfulMonad m] [DecidableEq ι]
    (so : QueryImpl spec m) (w : spec.Domain → Nat)
    (leaf : Nat → OracleComp spec Y) (nodeHash : Nat → Nat → Y → Y → OracleComp spec Y)
    (idx h : Nat) {known live : spec.QueryCache} (hle : known ≤ live)
    (path : Vector Y h)
    (hpath : simulateQ known.toPartialImpl (intrinsicAuthPathM leaf nodeHash idx h) = some path) :
    ∃ delta,
      simulateQ known.toPartialImpl
        (simulateQ ((QueryImpl.id' spec).withAddCost w)
          (intrinsicAuthPathM leaf nodeHash idx h)).runAdd = some (path, delta) ∧
      ((simulateQ (so.withCaching.withAddCost w)
        (merkleRootM leaf nodeHash h (idx / 2 ^ h))).runAdd).run live =
        (fun z : (Y × Nat) × spec.QueryCache => ((z.1.1, z.1.2 + delta), z.2)) <$>
          ((simulateQ (so.withCaching.withAddCost w)
            (do let y ← leaf idx; climbM nodeHash idx y path.toList)).runAdd).run live := by
  obtain ⟨delta, hscore⟩ := QueryImpl.exists_cost_of_toPartialImpl w _ known path hpath
  exact ⟨delta, hscore, run_simulateQ_merkleRootM_cost_offset_of_path_score
    so w leaf nodeHash idx h hle path delta hscore⟩

end PerfectMerkleTree
