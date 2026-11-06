/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
import all HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.Auxiliary.Interval.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.Interval.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Reductions.CollisionBounds
import all HashSig.GXMSS.Security.Reductions.CollisionBounds
public import HashSig.GXMSS.Security.Reductions.Interval.MerkleGames
import all HashSig.GXMSS.Security.Reductions.Interval.MerkleGames
public import HashSig.GXMSS.Security.Reductions.Interval.SourcePartition
import all HashSig.GXMSS.Security.Reductions.Interval.SourcePartition
public import HashSig.GXMSS.Security.Reductions.TCRSimulation
import all HashSig.GXMSS.Security.Reductions.TCRSimulation

/-!
# Interval Merkle reduction and obstruction bound

The Merkle obstruction event is bounded by the addressed-hash SM-DT-TCR advantage of
`merkleTargetCollisionAdversary`. Its accepted registration history contains all positive chain
steps and the surviving mixed-tree nodes. The coupled experiment preserves the full signing view.
-/

public section

namespace GXMSS.Interval.Unforgeability

open OracleComp OracleSpec TweakableHash GXMSS.IntervalMerkle GXMSS.Reductions

variable {PP T X H M R : Type} {h w v : ℕ}

private theorem not_frontier_of_intersecting_subspan (I : Interval h)
    (z t level index : ℕ)
    (hmeet : ¬ Subtree.DisjointFromInterval I level index)
    (hlower : t * 2 ^ z ≤ index * 2 ^ level)
    (hupper : (index + 1) * 2 ^ level ≤ (t + 1) * 2 ^ z) :
    ¬ Subtree.IsInactiveFrontier I z t := by
  intro hf
  apply hmeet
  rcases hf.disjoint with hd | hd
  · exact Or.inl (hupper.trans hd)
  · exact Or.inr (lt_of_lt_of_le hd hlower)

/-- An active raw endpoint vector is registered even when inactive subtrees are pruned. -/
private theorem leafTarget_mem_prunedTargetRun
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (ep : Epoch h) (he : Epoch.IsActive I ep) (hlower : t * 2 ^ z ≤ ep.val)
    (hupper : ep.val + 1 ≤ (t + 1) * 2 ^ z) :
    (P.treeTweak (0, ep), P.vectorInput (endpoints ep)) ∈
      (prunedTargetRun P I pp endpoints fillers fallback z t).2 := by
  have hmeet : ¬ Subtree.DisjointFromInterval I 0 ep.val := by
    rcases he with ⟨hfirst, hlast⟩
    simp only [Subtree.DisjointFromInterval, pow_zero, Nat.mul_one]
    omega
  induction z generalizing t with
  | zero =>
      have ht' : t < 2 ^ h := by simpa using ht
      have hf : ¬ Subtree.IsInactiveFrontier I 0 t :=
        not_frontier_of_intersecting_subspan I 0 t 0 ep.val hmeet
          (by simpa using hlower) (by simpa using hupper)
      have hep : ep = ⟨t, ht'⟩ := by
        apply Fin.ext
        change ep.val = t
        simp only [pow_zero, Nat.mul_one] at hlower hupper
        omega
      subst ep
      simp [prunedTargetRun, hf, ht']
  | succ z ih =>
      have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
      have hp : 0 < 2 ^ z := by positivity
      have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hlevel : z + 1 < h + 1 := by omega
      have hindex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
      have hf : ¬ Subtree.IsInactiveFrontier I (z + 1) t :=
        not_frontier_of_intersecting_subspan I (z + 1) t 0 ep.val hmeet
          (by simpa using hlower) (by simpa using hupper)
      rw [prunedTargetRun, dite_eq_right hf, dite_eq_left hlevel, dite_eq_left hindex]
      simp only [List.mem_append, List.mem_singleton]
      by_cases hside : ep.val < (2 * t + 1) * 2 ^ z
      · exact Or.inl (Or.inl (ih (t := 2 * t) (hz := by omega) (ht := hleft)
          (by rw [hpow] at hlower; nlinarith) (by omega)))
      · exact Or.inl (Or.inr (ih (t := 2 * t + 1) (hz := by omega) (ht := hright)
          (by omega) (by rw [hpow] at hupper; nlinarith)))

private theorem activeLeafTarget_mem_prunedTargets
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H)
    (ep : Epoch h) (he : Epoch.IsActive I ep) :
    (P.treeTweak (0, ep), P.vectorInput (endpoints ep)) ∈
      prunedTargets P I pp endpoints fillers := by
  unfold prunedTargets
  exact leafTarget_mem_prunedTargetRun P I pp endpoints fillers
    (P.leafHash pp 0 (endpoints 0)) h 0 le_rfl (by simp) ep he (by simp)
    (by simp)

private theorem take_engine_authPath {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx height z : ℕ) (hz : z ≤ height) :
    (PerfectMerkleTree.authPath leaf nodeHash idx height).take z =
      PerfectMerkleTree.authPath leaf nodeHash idx z := by
  induction height with
  | zero =>
      have heq : z = 0 := by omega
      subst z
      rfl
  | succ height ih =>
    rw [PerfectMerkleTree.authPath_succ]
    by_cases hlt : z ≤ height
    · rw [List.take_append_of_le_length (by simpa using hlt)]
      exact ih hlt
    · have heq : z = height + 1 := by omega
      subst z
      rw [← PerfectMerkleTree.authPath_succ]
      simp

/-- The ordinary verifier's actual mixed-path prefix reaches the mixed subtree on an active
leaf's ancestor chain. No complete authentication path is substituted. -/
private theorem active_honest_climb_prefix
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H)
    (ep : Epoch h) (he : Epoch.IsActive I ep) (z : ℕ) (hz : z ≤ h) :
    PerfectMerkleTree.climb (GXMSS.IntervalMerkle.ordinaryNode P pp) ep.val
      (P.leafHash pp ep (endpoints ep))
      ((List.ofFn (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep)).take z) =
        GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers z (ep.val / 2 ^ z) := by
  have hpath : List.ofFn (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep) =
      PerfectMerkleTree.authPath (GXMSS.IntervalMerkle.leaf P I pp endpoints fillers)
        (GXMSS.IntervalMerkle.node P I pp fillers) ep.val h := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [GXMSS.IntervalMerkle.authPath]
  have htake : List.length
      ((List.ofFn (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep)).take z) = z := by
    simp [hz]
  have hc := GXMSS.IntervalMerkle.climb_congr_ancestors (GXMSS.IntervalMerkle.ordinaryNode P pp)
    (GXMSS.IntervalMerkle.node P I pp fillers) ep.val (P.leafHash pp ep (endpoints ep))
    ((List.ofFn (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep)).take z)
    (by
      intro level _ hlevel left right
      have hle : level ≤ h := (by simpa only [htake] using hlevel : level ≤ z).trans hz
      have hl : level < h + 1 := by omega
      have hi := (Merkle.ancestor_legal ep level hle).2
      rw [GXMSS.IntervalMerkle.node_isActive_ancestor P I pp fillers ep he level hle left right]
      simp [GXMSS.IntervalMerkle.ordinaryNode, hl, hi])
  rw [hpath, take_engine_authPath _ _ _ _ _ hz] at hc
  have hcomplete := PerfectMerkleTree.climb_authPath
    (GXMSS.IntervalMerkle.leaf P I pp endpoints fillers) (GXMSS.IntervalMerkle.node P I pp fillers)
    ep.val z
  rw [GXMSS.IntervalMerkle.leaf_isActive P I pp endpoints fillers ep he] at hcomplete
  rw [hpath, take_engine_authPath _ _ _ _ _ hz]
  exact hc.trans hcomplete

/-- Ordered ordinary hash inputs along the actual active mixed path are the two mixed child
subtree roots at their natural global parent address. -/
private theorem active_honest_children
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H)
    (ep : Epoch h) (he : Epoch.IsActive I ep) (z : Fin h) :
    let current := PerfectMerkleTree.climb (GXMSS.IntervalMerkle.ordinaryNode P pp) ep.val
      (P.leafHash pp ep (endpoints ep))
      ((List.ofFn (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep)).take z.val)
    let sibling := GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep z
    let children := if ep.val / 2 ^ z.val % 2 = 0 then (current, sibling) else (sibling, current)
    let parent := ep.val / 2 ^ (z.val + 1)
    children =
      (GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers z.val (2 * parent),
        GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers z.val (2 * parent + 1)) := by
  dsimp only
  rw [active_honest_climb_prefix P I pp endpoints fillers ep he z.val (by omega),
    GXMSS.IntervalMerkle.authPath_eq_subtreeRoot P I pp endpoints fillers ep z]
  let q := ep.val / 2 ^ z.val
  let parent := ep.val / 2 ^ (z.val + 1)
  have hdiv : q / 2 = parent := by
    dsimp [q, parent]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  have hquot : q = 2 * parent + q % 2 := by
    have h := Nat.mod_add_div q 2
    omega
  change (if q % 2 = 0 then
      (GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers z.val q,
        GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers z.val (PerfectMerkleTree.sibling
            q))
    else
      (GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers z.val (PerfectMerkleTree.sibling
          q),
        GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers z.val q)) = _
  by_cases heven : q % 2 = 0
  · have heq : q = 2 * parent := by omega
    rw [ite_eq_left heven]
    have hsibling : PerfectMerkleTree.sibling q = q + 1 := ite_eq_left heven
    rw [hsibling, heq]
  · have heq : q = 2 * parent + 1 := by omega
    have hsibling : PerfectMerkleTree.sibling q = 2 * parent := by
      simp only [PerfectMerkleTree.sibling, heven, ite_false]
      omega
    rw [ite_eq_right heven, hsibling, heq]

private theorem nodeTarget_mem_prunedTargetRun
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (level : Fin (h + 1)) (index : Fin (2 ^ h))
    (hpos : 0 < level.val) (hlevelBound : level.val ≤ z)
    (hmeet : ¬ Subtree.DisjointFromInterval I level.val index.val)
    (hlower : t * 2 ^ z ≤ index.val * 2 ^ level.val)
    (hupper : (index.val + 1) * 2 ^ level.val ≤ (t + 1) * 2 ^ z) :
    (P.treeTweak (level, index), P.pairInput
      (GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers (level.val - 1) (2 * index.val),
       GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers (level.val - 1) (2 * index.val +
           1))) ∈
      (prunedTargetRun P I pp endpoints fillers fallback z t).2 := by
  induction z generalizing t with
  | zero => omega
  | succ z ih =>
      have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
      have hp : 0 < 2 ^ z := by positivity
      have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have htreeLevel : z + 1 < h + 1 := by omega
      have htreeIndex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
      have hf : ¬ Subtree.IsInactiveFrontier I (z + 1) t :=
        not_frontier_of_intersecting_subspan I _ _ _ _ hmeet hlower hupper
      rw [prunedTargetRun, dite_eq_right hf, dite_eq_left htreeLevel,
        dite_eq_left htreeIndex]
      simp only [List.mem_append, List.mem_singleton]
      by_cases htop : level.val = z + 1
      · have hindexEq : index.val = t := by
          have hpLevel : 0 < 2 ^ level.val := by positivity
          rw [htop] at hlower hupper
          nlinarith
        have hlevelEq : level = ⟨z + 1, htreeLevel⟩ := by
          apply Fin.ext
          exact htop
        have hindexFinEq : index = ⟨t, htreeIndex⟩ := by
          apply Fin.ext
          exact hindexEq
        subst level
        subst index
        let leftRun := prunedTargetRun P I pp endpoints fillers fallback z (2 * t)
        let rightRun := prunedTargetRun P I pp endpoints fillers fallback z (2 * t + 1)
        have hleftRoot :=
          ((prunedTargetRun_legal P I pp endpoints fillers fallback z (2 * t)
            (by omega) hleft).1).trans
            (prunedRoot_eq_subtreeRoot P I pp endpoints fillers z (2 * t))
        have hrightRoot :=
          ((prunedTargetRun_legal P I pp endpoints fillers fallback z (2 * t + 1)
            (by omega) hright).1).trans
            (prunedRoot_eq_subtreeRoot P I pp endpoints fillers z (2 * t + 1))
        exact Or.inr (by simp [hleftRoot, hrightRoot])
      · have hbelow : level.val ≤ z := by omega
        have hfactor : 2 ^ z = 2 ^ (z - level.val) * 2 ^ level.val := by
          rw [← Nat.pow_add, Nat.sub_add_cancel hbelow]
        by_cases hside : index.val < (2 * t + 1) * 2 ^ (z - level.val)
        · have hleftUpper : (index.val + 1) * 2 ^ level.val ≤
              (2 * t + 1) * 2 ^ z := by
            calc
              (index.val + 1) * 2 ^ level.val ≤
                  ((2 * t + 1) * 2 ^ (z - level.val)) * 2 ^ level.val :=
                Nat.mul_le_mul_right _ (by omega)
              _ = (2 * t + 1) * 2 ^ z := by rw [hfactor]; ring
          exact Or.inl (Or.inl (ih (t := 2 * t) (hz := by omega) (ht := hleft)
            hbelow (by rw [hpow] at hlower; nlinarith) hleftUpper))
        · have hrightLower : (2 * t + 1) * 2 ^ z ≤
              index.val * 2 ^ level.val := by
            calc
              (2 * t + 1) * 2 ^ z =
                  ((2 * t + 1) * 2 ^ (z - level.val)) * 2 ^ level.val := by
                rw [hfactor]
                ring
              _ ≤ index.val * 2 ^ level.val :=
                Nat.mul_le_mul_right _ (by omega)
          exact Or.inl (Or.inr (ih (t := 2 * t + 1) (hz := by omega) (ht := hright)
            hbelow hrightLower (by rw [hpow] at hupper; nlinarith)))

private theorem nodeTarget_mem_prunedTargets
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H)
    (level : Fin (h + 1)) (index : Fin (2 ^ h)) (hpos : 0 < level.val)
    (hlegal : (index.val + 1) * 2 ^ level.val ≤ 2 ^ h)
    (hmeet : ¬ Subtree.DisjointFromInterval I level.val index.val) :
    (P.treeTweak (level, index), P.pairInput
      (GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers (level.val - 1) (2 * index.val),
       GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers (level.val - 1) (2 * index.val +
           1))) ∈
      prunedTargets P I pp endpoints fillers := by
  unfold prunedTargets
  exact nodeTarget_mem_prunedTargetRun P I pp endpoints fillers
    (P.leafHash pp 0 (endpoints 0)) h 0 le_rfl (by simp) level index hpos
    (Nat.le_of_lt_succ level.isLt) hmeet (by simp) (by simpa using hlegal)

/-- Every ordered ordinary pair input on an active mixed opening is in actual pruned Q. -/
private theorem active_honest_children_registered
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H)
    (ep : Epoch h) (he : Epoch.IsActive I ep) (z : Fin h) :
    let current := PerfectMerkleTree.climb (GXMSS.IntervalMerkle.ordinaryNode P pp) ep.val
      (P.leafHash pp ep (endpoints ep))
      ((List.ofFn (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep)).take z.val)
    let sibling := GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep z
    let children := if ep.val / 2 ^ z.val % 2 = 0 then (current, sibling) else (sibling, current)
    (P.treeTweak (Merkle.parentAddress ep z), P.pairInput children) ∈
      prunedTargets P I pp endpoints fillers := by
  dsimp only
  rw [active_honest_children P I pp endpoints fillers ep he z]
  have hreachable := Merkle.parentAddress_reachable ep z
  let address := Merkle.parentAddress ep z
  let height := address.1
  let index := address.2
  change Merkle.ReachableNode h height.val index.val at hreachable
  obtain ⟨hpos, _, hlegal⟩ := hreachable
  have hmeet : ¬ Subtree.DisjointFromInterval I height.val index.val :=
    Epoch.isActive_ancestor_not_disjointFromInterval I ep he (z.val + 1)
  have hnode := nodeTarget_mem_prunedTargets P I pp endpoints fillers
    height index hpos hlegal hmeet
  simpa only [height, index, address, Merkle.parentAddress, Nat.add_sub_cancel] using hnode

/-- Every retained inactive honest target is in the actual accepted postorder schedule. -/
private theorem honestTargetQueries_subset_prunedTargets
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (target : T × X)
    (htarget : target ∈ GXMSS.Interval.MerkleWitnesses.honestTargetQueries P I pp endpoints fillers)
        :
    target ∈ prunedTargets P I pp endpoints fillers := by
  simp only [GXMSS.Interval.MerkleWitnesses.honestTargetQueries, List.mem_flatMap,
    List.mem_map, List.mem_filter, decide_eq_true_eq] at htarget
  obtain ⟨level, _, index, ⟨_, hpos, hlegal, hmeet⟩, rfl⟩ := htarget
  exact nodeTarget_mem_prunedTargets P I pp endpoints fillers level index hpos hlegal hmeet

/-- A returned inactive witness converts to its checked global address in the actual schedule. -/
private theorem inactive_collision_registered [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (starts endpoints : Epoch h → Fin v → H) (fillers : Fillers I H)
    (e : Epoch h) (he : ¬ Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (q : ℕ) (first second : H × H)
    (hw : GXMSS.Interval.MerkleWitnesses.findAboveFrontier P I pp endpoints fillers e ys auth =
      some (q, first, second))
    (hroot : P.recoverRoot pp e ys auth = GXMSS.IntervalMerkle.root P I pp endpoints fillers)
    (hne : frontierValue I fillers (frontierLevel I e) (e.val / 2 ^ frontierLevel I e)
      (frontierLevel_isInactiveFrontier I e he) ≠
        GXMSS.Interval.MerkleWitnesses.openingFrontierDigest P I pp e ys auth) :
    let level := frontierLevel I e + q
    let index := e.val / 2 ^ level
    ∃ (hl : level < h + 1) (hi : index < 2 ^ h),
      (P.treeTweak (⟨level, hl⟩, ⟨index, hi⟩), P.pairInput first) ∈
        endpointTargets P pp starts ++ prunedTargets P I pp endpoints fillers ∧
      first ≠ second ∧
      P.nodeHash pp ⟨level, hl⟩ ⟨index, hi⟩ first.1 first.2 =
        P.nodeHash pp ⟨level, hl⟩ ⟨index, hi⟩ second.1 second.2 := by
  dsimp only
  obtain ⟨⟨az, ai⟩, haz, hai, _, _, hpairs, hhash, hmem⟩ :=
    GXMSS.Interval.MerkleWitnesses.findAboveFrontier_sound P I pp endpoints fillers e he ys auth
      q first second hw hroot hne
  have hl : frontierLevel I e + q < h + 1 := by rw [← haz]; exact az.isLt
  have hi : e.val / 2 ^ (frontierLevel I e + q) < 2 ^ h := by rw [← hai]; exact ai.isLt
  have hazFin : az = ⟨frontierLevel I e + q, hl⟩ := Fin.ext haz
  have haiFin : ai = ⟨e.val / 2 ^ (frontierLevel I e + q), hi⟩ := Fin.ext hai
  rw [hazFin, haiFin] at hmem hhash
  refine ⟨hl, hi, ?_, hpairs, hhash⟩
  exact List.mem_append_right _
    (honestTargetQueries_subset_prunedTargets P I pp endpoints fillers _ hmem)

/-- Rekeying an opening preserves its query inputs when both hashes agree on its ancestors. -/
private theorem openingQueries_rekey {A B Y : Type} {s : BinaryTree.Skeleton}
    (key₁ : BinaryTree.SkeletonInternalIndex s → A) (hash₁ : A → Y → Y → Y)
    (key₂ : BinaryTree.SkeletonInternalIndex s → B) (hash₂ : B → Y → Y → Y)
    (rekey : A → B) (idx : BinaryTree.SkeletonLeafIndex s) (leaf : Y)
    (path : List.Vector Y idx.depth)
    (hk : ∀ a, a.IsAncestorOf idx → rekey (key₁ a) = key₂ a)
    (hn : ∀ a, a.IsAncestorOf idx → ∀ l r,
      hash₁ (key₁ a) l r = hash₂ (key₂ a) l r) :
    (AddressedMerkleTree.openingQueries key₁ hash₁ idx leaf path).map
      (fun q => (⟨rekey q.address, q.input⟩ : AddressedMerkleTree.NodeQuery B Y)) =
      AddressedMerkleTree.openingQueries key₂ hash₂ idx leaf path := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft idx ih =>
    have hc := GXMSS.IntervalMerkle.putativeRoot_congr_ancestors
      (fun a => hash₁ (key₁ (.ofLeft a))) (fun a => hash₂ (key₂ (.ofLeft a)))
      idx leaf path.tail (by intro a ha; exact hn (.ofLeft a) (by simpa using ha))
    simp only [AddressedMerkleTree.openingQueries, List.map_cons]
    rw [hc, hk .ofInternal (by simp)]
    congr 1
    exact ih _ _ path.tail
      (by intro a ha; exact hk (.ofLeft a) (by simpa using ha))
      (by intro a ha; exact hn (.ofLeft a) (by simpa using ha))
  | ofRight idx ih =>
    have hc := GXMSS.IntervalMerkle.putativeRoot_congr_ancestors
      (fun a => hash₁ (key₁ (.ofRight a))) (fun a => hash₂ (key₂ (.ofRight a)))
      idx leaf path.tail (by intro a ha; exact hn (.ofRight a) (by simpa using ha))
    simp only [AddressedMerkleTree.openingQueries, List.map_cons]
    rw [hc, hk .ofInternal (by simp)]
    congr 1
    exact ih _ _ path.tail
      (by intro a ha; exact hk (.ofRight a) (by simpa using ha))
      (by intro a ha; exact hn (.ofRight a) (by simpa using ha))

/-- Every original-hash query along an active mixed opening was actually registered. -/
private theorem active_openingQueries_registered
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H)
    (e : Epoch h) (he : Epoch.IsActive I e) (target : T × X)
    (htarget : target ∈ P.merkleOpeningQueries pp e (endpoints e)
      (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers e)) :
    target ∈ prunedTargets P I pp endpoints fillers := by
  simp only [HashInstance.merkleOpeningQueries, List.mem_cons, List.mem_map] at htarget
  rcases htarget with rfl | ⟨query, hquery, rfl⟩
  · exact activeLeafTarget_mem_prunedTargets P I pp endpoints fillers e he
  · let leaf := GXMSS.IntervalMerkle.leaf P I pp endpoints fillers
    let node := GXMSS.IntervalMerkle.node P I pp fillers
    let nh := PerfectMerkleTree.nodeHashAt node h 0
    let key := fun a => P.treeTweak (HashInstance.engineAddress a)
    let hash := fun t l r => TweakableHash.eval P.thf pp t (P.pairInput (l, r))
    let idx := BinaryTree.SkeletonLeafIndex.ofNat h e
    let ld := PerfectMerkleTree.leafData leaf h 0
    have hleaf : ld.get idx = P.leafHash pp e (endpoints e) := by
      simpa [ld, idx, Nat.div_eq_of_lt e.isLt, leaf,
        GXMSS.IntervalMerkle.leaf_isActive P I pp endpoints fillers e he] using
        PerfectMerkleTree.leafData_get_ofNat leaf h e
    have hpath : HashInstance.openingProof e
        (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers e) =
        InductiveMerkleTree.generateProof (PerfectMerkleTree.tree leaf node h 0) idx := by
      apply Subtype.ext
      have hp : List.ofFn (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers e) =
          PerfectMerkleTree.authPath leaf node e.val h := by
        apply List.ext_getElem
        · simp
        · intro i hi hj
          simp [GXMSS.IntervalMerkle.authPath, leaf, node]
      simp [HashInstance.openingProof, hp, PerfectMerkleTree.authPath,
        idx, Nat.div_eq_of_lt e.isLt]
    have hn : ∀ a, a.IsAncestorOf idx → ∀ l r, nh a l r = hash (key a) l r := by
      intro a ha l r
      have hai := PerfectMerkleTree.natAddr_index_of_isAncestorOf_ofNat ha
      rw [Nat.div_eq_of_lt e.isLt] at hai
      obtain ⟨hpos, hle⟩ := a.natAddr_height_pos_le 0
      change GXMSS.IntervalMerkle.node P I pp fillers (a.natAddr 0).height
        (a.natAddr 0).index l r = _
      rw [hai, GXMSS.IntervalMerkle.node_isActive_ancestor P I pp fillers e he _ hle]
      simp [hash, key, HashInstance.engineAddress, HashInstance.nodeHash, hai]
    have hqueries := openingQueries_rekey id nh key hash key idx
      (P.leafHash pp e (endpoints e))
      (HashInstance.openingProof e (GXMSS.IntervalMerkle.authPath P I pp endpoints fillers e))
      (by intros; rfl) hn
    change query ∈ AddressedMerkleTree.openingQueries key hash idx
      (P.leafHash pp e (endpoints e)) _ at hquery
    rw [← hqueries] at hquery
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hquery
    rw [hpath, ← hleaf] at horiginal
    obtain ⟨a, ha, haddr, hinput⟩ := HashInstance.mem_openingQueries_honestTree
      id nh ld idx original horiginal
    have hai := PerfectMerkleTree.natAddr_index_of_isAncestorOf_ofNat ha
    rw [Nat.div_eq_of_lt e.isLt] at hai
    obtain ⟨hpos, hle⟩ := a.natAddr_height_pos_le 0
    let address := HashInstance.engineAddress a
    let level := address.1
    let index := address.2
    have hpos' : 0 < level.val := hpos
    have hlegal : (index.val + 1) * 2 ^ level.val ≤ 2 ^ h := by
      have bounds := Merkle.internalAddress_legal h h 0 le_rfl (by simp) a
      have reachable := bounds.2
      exact reachable.2
    have hmeet : ¬ Subtree.DisjointFromInterval I level.val index.val := by
      change ¬ Subtree.DisjointFromInterval I (a.natAddr 0).height (a.natAddr 0).index
      rw [hai]
      exact Epoch.isActive_ancestor_not_disjointFromInterval I e he _
    rw [haddr, hinput]
    change (P.treeTweak (HashInstance.engineAddress a), P.pairInput
      (AddressedMerkleTree.childPairAt (PerfectMerkleTree.tree leaf node h 0) a)) ∈ _
    rw [PerfectMerkleTree.childPairAt_tree]
    exact nodeTarget_mem_prunedTargets P I pp endpoints fillers level index hpos' hlegal hmeet

/-- The deterministic candidate wins against the actual accepted registration history. -/
private theorem intervalMerkleCandidate_wins
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (hv : 0 < v) (pp : PP)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (e : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v))
    (hob : merkleObstructionEvent P enc K I (GXMSS.Interval.keys P I pp starts fillers).2
      ((GXMSS.Interval.keys P I pp starts fillers).1, (e, msg, sig), history) = true) :
    let endpoints := GXMSS.endpoints P pp starts
    let registered := endpointTargets P pp starts ++ prunedTargets P I pp endpoints fillers
    let state : IntervalTCRState PP T X H h v I :=
      ⟨⟨starts, endpoints, GXMSS.IntervalMerkle.root P I pp endpoints fillers,
        registered, fallback⟩, fillers⟩
    GXMSS.Unforgeability.merkleCandidateWins P pp registered
      (intervalMerkleCandidate P enc I state pp
        ((GXMSS.Interval.keys P I pp starts fillers).1, (e, msg, sig), history)) = true := by
  let endpoints := GXMSS.endpoints P pp starts
  let registered := endpointTargets P pp starts ++ prunedTargets P I pp endpoints fillers
  have hlen : registered.length ≤ (merkleTCRProblem P).numTargets := by
    simpa only [registered, List.length_append, endpointTargets_length,
      prunedTargets_length] using prunedProblem_capacity P I hv
  have hsplit := hob
  simp only [merkleObstructionEvent, Bool.and_eq_true] at hsplit
  have hvfy : GXMSS.verify P enc (GXMSS.Interval.keys P I pp starts fillers).1 e msg sig = true :=
      by
    have hs := hsplit.1
    simp only [SyncSignatureUnforgeability.strongValid, GXMSS.Interval.scheme,
      GXMSS.Interval.verify, Bool.and_eq_true] at hs
    exact hs.1
  cases hw : enc.value pp msg sig.randomizer e with
  | none =>
    simp [merkleObstructionEvent, GXMSS.Interval.keys, GXMSS.keys, hw] at hob
  | some word =>
    let ys := fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i)
    have hroot : P.recoverRoot pp e ys sig.path = GXMSS.IntervalMerkle.root P I pp endpoints fillers
        := by
      simp only [GXMSS.verify, GXMSS.Interval.keys, GXMSS.keys, hw] at hvfy
      exact of_decide_eq_true hvfy
    by_cases he : Epoch.IsActive I e
    · have hne : (endpoints e, GXMSS.IntervalMerkle.authPath P I pp endpoints fillers e) ≠
          (ys, sig.path) := by
        have hd := hsplit.2
        simp only [GXMSS.Interval.keys, GXMSS.keys, hw, he, dite_true] at hd
        exact of_decide_eq_true hd
      have hr := (GXMSS.IntervalMerkle.recoverRoot_authPath_isActive P I pp endpoints fillers e
          he).trans
        hroot.symm
      obtain ⟨collision, hc⟩ := Option.isSome_iff_exists.mp
        (P.findMerkleCollision_isSome pp e _ _ _ _ hne hr)
      have hm := active_openingQueries_registered P I pp endpoints fillers e he _
        (P.findMerkleCollision_mem_queries pp e _ _ _ _ hc).1
      obtain ⟨_, hlookup, _⟩ := registeredIndex_spec registered collision.tweak collision.first
        (merkleTCRProblem P).numTargets (List.mem_append_right _ hm) hlen
      obtain ⟨hne', hhash⟩ := P.findMerkleCollision_sound pp e _ _ _ _ hc
      have hwin : decide (collision.second ≠ collision.first ∧
          TweakableHash.eval P.thf pp collision.tweak collision.second =
            TweakableHash.eval P.thf pp collision.tweak collision.first) = true :=
        decide_eq_true ⟨Ne.symm hne', hhash.symm⟩
      simpa only [intervalMerkleCandidate, GXMSS.Unforgeability.merkleCandidateWins,
        hw, he, ite_true, ys, hc, hlookup, registered, endpoints, GXMSS.Interval.keys,
        GXMSS.keys] using hwin
    · have hne : frontierValue I fillers (frontierLevel I e) (e.val / 2 ^ frontierLevel I e)
          (frontierLevel_isInactiveFrontier I e he) ≠
            GXMSS.Interval.MerkleWitnesses.openingFrontierDigest P I pp e ys sig.path := by
        have hd := hsplit.2
        simp only [GXMSS.Interval.keys, GXMSS.keys, hw,
          he, dite_false] at hd
        exact Ne.symm (of_decide_eq_true hd)
      obtain ⟨q, second, hc⟩ := GXMSS.Interval.MerkleWitnesses.findAboveFrontier_oriented
        P I pp endpoints fillers e he ys sig.path hroot hne
      obtain ⟨hl, hi, hm, hneq, hhash⟩ := inactive_collision_registered P I pp starts endpoints
        fillers e he ys sig.path q _ second hc hroot hne
      obtain ⟨_, hlookup, _⟩ := registeredIndex_spec registered _ _
        (merkleTCRProblem P).numTargets hm hlen
      let first := PerfectMerkleTree.honestChildren
        (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp endpoints fillers (frontierLevel I e) i)
        (fun j i => GXMSS.IntervalMerkle.node P I pp fillers (frontierLevel I e + j) i)
        q (e.val / 2 ^ frontierLevel I e / 2 ^ q)
      have hin : P.pairInput second ≠ P.pairInput first := by
        let pairInput := P.pairInput
        exact fun hh => hneq (pairInput.injective hh).symm
      have hwin : decide (P.pairInput second ≠ P.pairInput first ∧
          TweakableHash.eval P.thf pp (P.treeTweak (⟨_, hl⟩, ⟨_, hi⟩)) (P.pairInput second) =
            TweakableHash.eval P.thf pp
              (P.treeTweak (⟨_, hl⟩, ⟨_, hi⟩)) (P.pairInput first)) = true := by
        exact decide_eq_true ⟨hin, hhash.symm⟩
      simpa only [intervalMerkleCandidate, GXMSS.Unforgeability.merkleCandidateWins,
        hw, he, ite_false, ys, hc, hl, hi, dite_true, hlookup, registered, endpoints,
        GXMSS.Interval.keys, GXMSS.keys] using hwin

private noncomputable def coupledMerkleObstruction
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (A : GXMSS.Reductions.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let thf := P.thf
  let pp ← thf.seedGen
  let _fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← sampleFillers I H
  let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
  let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  pure (merkleObstructionEvent P enc K I sk out)

private noncomputable def coupledMerkleWin
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (A : GXMSS.Reductions.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let thf := P.thf
  let pp ← thf.seedGen
  let fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← sampleFillers I H
  let endpoints := GXMSS.endpoints P pp starts
  let registered := endpointTargets P pp starts ++ prunedTargets P I pp endpoints fillers
  let state : IntervalTCRState PP T X H h v I :=
    ⟨⟨starts, endpoints, GXMSS.IntervalMerkle.root P I pp endpoints fillers,
      registered, fallback⟩, fillers⟩
  let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
  let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  pure (GXMSS.Unforgeability.merkleCandidateWins P pp registered
    (intervalMerkleCandidate P enc I state pp out))

private theorem coupledMerkleObstruction_evalDist
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (A : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    𝒟[coupledMerkleObstruction P enc K I A] =
      𝒟[merkleObstructionExperiment P enc K I A] := by
  unfold coupledMerkleObstruction merkleObstructionExperiment GXMSS.Interval.keygen
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr_of_support
  intro pp _
  exact evalDist_bind_const ($ᵗ H : ProbComp H) _

private theorem merkleExperiment_eq_coupledWin
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (hv : 0 < v)
    (A : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment (merkleTargetCollisionAdversary P enc K I hv A) =
      coupledMerkleWin P enc K I A := by
  have hsetup (pp : PP) := tcrIntervalSetup_run P
    (2 * (2 ^ h) * v * (2 ^ w)) I pp (prunedProblem_capacity P I hv)
  unfold SM_DT_TCR_Experiment coupledMerkleWin
  simp only [merkleTargetCollisionAdversary]
  unfold merkleTCRProblem
  apply bind_congr
  intro pp
  rw [hsetup pp]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  apply bind_congr
  intro fillers
  apply bind_congr
  intro out
  dsimp only [GXMSS.Unforgeability.merkleCandidateWins]
  cases intervalMerkleCandidate P enc I _ pp out with
  | mk j second =>
    cases (endpointTargets P pp starts ++
      prunedTargets P I pp (GXMSS.endpoints P pp starts) fillers)[j]? <;> rfl

/-- The native Merkle obstruction bound for `merkleTargetCollisionAdversary`. -/
@[expose] def MerkleObstructionBound [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (hv : 0 < v)
    (A : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Epoch h) M (GXMSS.Signature R H h v)) : Prop :=
  ProbCompRuntime.probComp.evalDist (merkleObstructionExperiment P enc K I A) {true} ≤
    SM_DT_TCR_Advantage (merkleTargetCollisionAdversary P enc K I hv A)

/-- The native obstruction mass is bounded by the addressed-hash Merkle TCR advantage.
The coupling retains the entire signing view and both accepted registration histories. -/
theorem merkleObstructionMass_le_advantage
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (hv : 0 < v)
    (A : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Epoch h) M (GXMSS.Signature R H h v)) : MerkleObstructionBound P enc K I hv A := by
  unfold MerkleObstructionBound SM_DT_TCR_Advantage
  simp only [ProbCompRuntime.probComp_evalDist]
  rw [← coupledMerkleObstruction_evalDist P enc K I A,
    merkleExperiment_eq_coupledWin P enc K I hv A]
  unfold coupledMerkleObstruction coupledMerkleWin
  let thf := P.thf
  apply evalDist_bind_apply_mono_of_support thf.seedGen _ _ (by measurability)
  intro pp _
  apply evalDist_bind_apply_mono_of_support ($ᵗ H : ProbComp H) _ _ (by measurability)
  intro fallback _
  apply evalDist_bind_apply_mono_of_support (GXMSS.sampleStarts H h v) _ _ (by measurability)
  intro starts _
  apply evalDist_bind_apply_mono_of_support (sampleFillers I H) _ _ (by measurability)
  intro fillers _
  simp only [GXMSS.Interval.viewWithKeys, bind_assoc]
  dsimp only [SyncSignatureUnforgeability.ExperimentResult,
    SyncSignatureUnforgeability.Forgery]
  apply evalDist_bind_apply_mono_of_support _ _ _ (by measurability)
  rintro ⟨⟨e, msg, sig⟩, history⟩ _
  change 𝒟[(pure (merkleObstructionEvent P enc K I
    (GXMSS.Interval.keys P I pp starts fillers).2
    ((GXMSS.Interval.keys P I pp starts fillers).1, (e, msg, sig), history)) :
      ProbComp Bool)] {true} ≤
    𝒟[(pure (GXMSS.Unforgeability.merkleCandidateWins P pp
      (endpointTargets P pp starts ++ prunedTargets P I pp (GXMSS.endpoints P pp starts) fillers)
      (intervalMerkleCandidate P enc I
        ⟨⟨starts, GXMSS.endpoints P pp starts,
          GXMSS.IntervalMerkle.root P I pp (GXMSS.endpoints P pp starts) fillers,
          endpointTargets P pp starts ++
            prunedTargets P I pp (GXMSS.endpoints P pp starts) fillers,
          fallback⟩, fillers⟩ pp
        ((GXMSS.Interval.keys P I pp starts fillers).1, (e, msg, sig), history))) :
      ProbComp Bool)] {true}
  by_cases ho : merkleObstructionEvent P enc K I (GXMSS.Interval.keys P I pp starts fillers).2
      ((GXMSS.Interval.keys P I pp starts fillers).1, (e, msg, sig), history) = true
  · have hwin := intervalMerkleCandidate_wins P enc K I hv pp starts fillers fallback
      e msg sig history ho
    rw [ho, hwin]
  · have hf := Bool.eq_false_iff.mpr ho
    rw [hf]
    simp

end GXMSS.Interval.Unforgeability
