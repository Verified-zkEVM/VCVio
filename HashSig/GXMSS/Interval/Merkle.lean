/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Merkle
import all HashSig.GXMSS.Merkle

/-!
# Interval Merkle trees

An inclusive interval of active epochs retains the ordinary hashed endpoint leaves. Each
maximal subtree outside the interval has one independently sampled digest at its root. Tree
addresses are levels counted upward from the leaves and zero-based indices at each height.
-/

public section

namespace GXMSS.IntervalMerkle

/-- An inclusive, nonempty interval selected before key generation. -/
structure Interval (h : ℕ) where
  /-- First active epoch. -/
  first : Fin (2 ^ h)
  /-- Last active epoch. -/
  last : Fin (2 ^ h)
  /-- The selected range is nonempty. -/
  ordered : first ≤ last

/-- The interval containing every epoch. -/
@[expose] def Interval.full (h : ℕ) : Interval h :=
  ⟨0, ⟨2 ^ h - 1, Nat.sub_lt (by positivity) (by decide)⟩, by simp⟩

variable {h : ℕ}

/-- Membership in the inclusive active interval. -/
@[expose] def Epoch.IsActive (I : Interval h) (e : Fin (2 ^ h)) : Prop :=
  I.first ≤ e ∧ e ≤ I.last

instance (I : Interval h) (e : Fin (2 ^ h)) : Decidable (Epoch.IsActive I e) := by
  unfold Epoch.IsActive
  infer_instance

/-- The dyadic leaf span is disjoint from the active interval, independently of address validity. -/
@[expose] def Subtree.DisjointFromInterval (I : Interval h)
    (subtreeHeight subtreeIndex : ℕ) : Prop :=
  let first := I.first
  let last := I.last
  (subtreeIndex + 1) * 2 ^ subtreeHeight ≤ first.val ∨
    last.val < subtreeIndex * 2 ^ subtreeHeight

instance (I : Interval h) (subtreeHeight subtreeIndex : ℕ) :
    Decidable (Subtree.DisjointFromInterval I subtreeHeight subtreeIndex) := by
  unfold Subtree.DisjointFromInterval
  infer_instance

/-- A legal tree address whose subtree is inactive while its parent meets the interval. -/
@[expose] def Subtree.IsInactiveFrontier (I : Interval h) (subtreeHeight subtreeIndex : ℕ) : Prop :=
  subtreeHeight < h ∧ (subtreeIndex + 1) * 2 ^ subtreeHeight ≤ 2 ^ h ∧
    Subtree.DisjointFromInterval I subtreeHeight subtreeIndex ∧
    ¬ Subtree.DisjointFromInterval I (subtreeHeight + 1) (subtreeIndex / 2)

instance (I : Interval h) (subtreeHeight subtreeIndex : ℕ) :
    Decidable (Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex) := by
  unfold Subtree.IsInactiveFrontier
  infer_instance

/-- A maximal inactive subtree has a height inside the finite address rectangle. -/
theorem Subtree.IsInactiveFrontier.height_le {I : Interval h} {subtreeHeight subtreeIndex : ℕ}
    (hf : IsInactiveFrontier I subtreeHeight subtreeIndex) : subtreeHeight ≤ h :=
  Nat.le_of_lt hf.1

/-- A maximal inactive subtree's dyadic span fits inside the full epoch range. -/
theorem Subtree.IsInactiveFrontier.span_le {I : Interval h} {subtreeHeight subtreeIndex : ℕ}
    (hf : IsInactiveFrontier I subtreeHeight subtreeIndex) :
    (subtreeIndex + 1) * 2 ^ subtreeHeight ≤ 2 ^ h := by
  obtain ⟨_, hspan, _, _⟩ := hf
  exact hspan

/-- A maximal inactive subtree is disjoint from the active interval. -/
theorem Subtree.IsInactiveFrontier.disjoint {I : Interval h} {subtreeHeight subtreeIndex : ℕ}
    (hf : IsInactiveFrontier I subtreeHeight subtreeIndex) :
    DisjointFromInterval I subtreeHeight subtreeIndex := by
  obtain ⟨_, _, hdisjoint, _⟩ := hf
  exact hdisjoint

/-- A maximal inactive subtree's parent intersects the active interval. -/
theorem Subtree.IsInactiveFrontier.parent_not_disjoint
    {I : Interval h} {subtreeHeight subtreeIndex : ℕ}
    (hf : IsInactiveFrontier I subtreeHeight subtreeIndex) :
    ¬ DisjointFromInterval I (subtreeHeight + 1) (subtreeIndex / 2) := by
  obtain ⟨_, _, _, hparent⟩ := hf
  exact hparent

/-- The strict frontier characterization agrees with the expanded legal-address formula,
including its root alternative: a nonempty active interval rules out an inactive legal root. -/
theorem Subtree.isInactiveFrontier_iff_expanded (I : Interval h)
    (subtreeHeight subtreeIndex : ℕ) :
    IsInactiveFrontier I subtreeHeight subtreeIndex ↔
      subtreeHeight ≤ h ∧ (subtreeIndex + 1) * 2 ^ subtreeHeight ≤ 2 ^ h ∧
        DisjointFromInterval I subtreeHeight subtreeIndex ∧
        (subtreeHeight = h ∨
          ¬ DisjointFromInterval I (subtreeHeight + 1) (subtreeIndex / 2)) := by
  constructor
  · rintro ⟨hlt, hspan, hdisjoint, hparent⟩
    exact ⟨Nat.le_of_lt hlt, hspan, hdisjoint, Or.inr hparent⟩
  · rintro ⟨hle, hspan, hdisjoint, hparent⟩
    have hlt : subtreeHeight < h := by
      by_contra hnot
      have heq : subtreeHeight = h := by omega
      subst subtreeHeight
      have hp : 0 < 2 ^ h := by positivity
      have hi : subtreeIndex = 0 := by nlinarith
      subst subtreeIndex
      let first := I.first
      let last := I.last
      have hfirst : first.val < 2 ^ h := first.isLt
      have hordered : first.val ≤ last.val := I.ordered
      simp only [DisjointFromInterval, zero_add, one_mul, zero_mul] at hdisjoint
      change 2 ^ h ≤ first.val ∨ last.val < 0 at hdisjoint
      omega
    refine ⟨hlt, hspan, hdisjoint, ?_⟩
    rcases hparent with hroot | hparent
    · omega
    · exact hparent

/-- A leaf outside the active range is itself inactive. -/
theorem Subtree.disjointFromInterval_leaf_iff (I : Interval h) (e : Fin (2 ^ h)) :
    Subtree.DisjointFromInterval I 0 e.val ↔ ¬ Epoch.IsActive I e := by
  simp only [Subtree.DisjointFromInterval, Epoch.IsActive, pow_zero, mul_one, not_and_or, not_le]
  omega

/-- An active epoch lies strictly within every one of its ancestor subtrees. -/
theorem Epoch.isActive_ancestor_not_disjointFromInterval (I : Interval h) (e : Fin (2 ^ h))
    (he : Epoch.IsActive I e) (subtreeHeight : ℕ) :
    ¬ Subtree.DisjointFromInterval I subtreeHeight (e.val / 2 ^ subtreeHeight) := by
  have hlow := Nat.div_mul_le_self e.val (2 ^ subtreeHeight)
  have hhigh : e.val < (e.val / 2 ^ subtreeHeight + 1) * 2 ^ subtreeHeight := by
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ e.val (by positivity : 0 < 2 ^ subtreeHeight))
  rcases he with ⟨ha, hb⟩
  simp only [Subtree.DisjointFromInterval, Fin.le_def] at *
  omega

/-- An active epoch has no frontier node on its ancestor chain. -/
theorem Epoch.isActive_ancestor_not_isInactiveFrontier (I : Interval h) (e : Fin (2 ^ h))
    (he : Epoch.IsActive I e) (subtreeHeight : ℕ) :
    ¬ Subtree.IsInactiveFrontier I subtreeHeight (e.val / 2 ^ subtreeHeight) := by
  intro hf
  exact Epoch.isActive_ancestor_not_disjointFromInterval I e he subtreeHeight hf.disjoint

/-- A child on an epoch's ancestor chain remains inactive when its parent is inactive. -/
theorem Subtree.disjointFromInterval_child_of_parent (I : Interval h) (e : Fin (2 ^ h)) (z : ℕ)
    (hp : Subtree.DisjointFromInterval I (z + 1) (e.val / 2 ^ (z + 1))) :
    Subtree.DisjointFromInterval I z (e.val / 2 ^ z) := by
  let c := e.val / 2 ^ z
  have hdiv : e.val / 2 ^ (z + 1) = c / 2 := by
    simp [c, pow_succ, Nat.div_div_eq_div_mul]
  have hlow : (c / 2) * 2 ≤ c := Nat.div_mul_le_self c 2
  have hhigh : c + 1 ≤ (c / 2 + 1) * 2 :=
    Nat.succ_le_of_lt (by simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ c (by decide : 0 < 2)))
  have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := pow_succ 2 z
  have hlow' : (c / 2) * 2 ^ (z + 1) ≤ c * 2 ^ z := by
    rw [hpow]
    nlinarith [Nat.mul_le_mul_right (2 ^ z) hlow]
  have hhigh' : (c + 1) * 2 ^ z ≤ (c / 2 + 1) * 2 ^ (z + 1) := by
    rw [hpow]
    nlinarith [Nat.mul_le_mul_right (2 ^ z) hhigh]
  rcases hp with hbefore | hafter
  · left
    rw [hdiv] at hbefore
    exact hhigh'.trans hbefore
  · right
    rw [hdiv] at hafter
    exact lt_of_lt_of_le hafter hlow'

/-- Inactivity propagates from an ancestor to every descendant on the same epoch path. -/
theorem Subtree.disjointFromInterval_descendant (I : Interval h) (e : Fin (2 ^ h))
    (z k : ℕ) (hzk : z ≤ k)
    (hk : Subtree.DisjointFromInterval I k (e.val / 2 ^ k)) :
    Subtree.DisjointFromInterval I z (e.val / 2 ^ z) := by
  induction k, hzk using Nat.le_induction with
  | base => exact hk
  | succ k _ ih => exact ih (Subtree.disjointFromInterval_child_of_parent I e k hk)

/-- The highest inactive ancestor of an epoch, computed by bounded search. -/
@[expose] def frontierLevel (I : Interval h) (e : Fin (2 ^ h)) : ℕ :=
  Nat.findGreatest (fun z => Subtree.DisjointFromInterval I z (e.val / 2 ^ z)) h

/-- An inactive epoch's highest inactive ancestor is a legal maximal frontier node. -/
theorem frontierLevel_isInactiveFrontier (I : Interval h) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) :
    Subtree.IsInactiveFrontier I (frontierLevel I e) (e.val / 2 ^ frontierLevel I e) := by
  let m := frontierLevel I e
  have hzero : Subtree.DisjointFromInterval I 0 (e.val / 2 ^ 0) := by
    simpa using (Subtree.disjointFromInterval_leaf_iff I e).2 he
  have hm : Subtree.DisjointFromInterval I m (e.val / 2 ^ m) := by
    exact Nat.findGreatest_spec (P := fun z => Subtree.DisjointFromInterval I z (e.val / 2 ^ z))
      (Nat.zero_le h) hzero
  have hle : m ≤ h := Nat.findGreatest_le h
  have hbound : (e.val / 2 ^ m + 1) * 2 ^ m ≤ 2 ^ h := by
    by_cases hz : m = 0
    · rw [hz]
      simp only [pow_zero, Nat.div_one, mul_one]
      exact Nat.succ_le_of_lt e.isLt
    · obtain ⟨_, _, hspan⟩ := Merkle.ancestor_reachable e m (Nat.pos_of_ne_zero hz) hle
      exact hspan
  have hparent : m < h → ¬ Subtree.DisjointFromInterval I (m + 1) (e.val / 2 ^ (m + 1)) := by
    intro hlt hp
    have hlarge := Nat.le_findGreatest
      (P := fun z => Subtree.DisjointFromInterval I z (e.val / 2 ^ z)) (by omega : m + 1 ≤ h) hp
    change m + 1 ≤ m at hlarge
    omega
  have hdiv : (e.val / 2 ^ m) / 2 = e.val / 2 ^ (m + 1) := by
    simp [pow_succ, Nat.div_div_eq_div_mul]
  apply (Subtree.isInactiveFrontier_iff_expanded I m _).2
  refine ⟨hle, hbound, hm, ?_⟩
  by_cases htop : m = h
  · exact Or.inl htop
  · right
    rw [hdiv]
    exact hparent (by omega)

/-- A tree address whose span contains an epoch has that epoch's quotient index. -/
theorem index_eq_div_of_contains (e : ℕ) (subtreeHeight subtreeIndex : ℕ)
    (hlo : subtreeIndex * 2 ^ subtreeHeight ≤ e)
    (hhi : e < (subtreeIndex + 1) * 2 ^ subtreeHeight) :
    subtreeIndex = e / 2 ^ subtreeHeight := by
  have hp : 0 < 2 ^ subtreeHeight := by positivity
  have hle : subtreeIndex ≤ e / 2 ^ subtreeHeight :=
    (Nat.le_div_iff_mul_le hp).2 hlo
  have hlt : e / 2 ^ subtreeHeight < subtreeIndex + 1 :=
    (Nat.div_lt_iff_lt_mul hp).2 hhi
  omega

/-- A subtree contains an epoch when its leaf span contains the epoch index. -/
@[expose] def Subtree.CoversEpoch (subtreeHeight subtreeIndex epoch : ℕ) : Prop :=
  subtreeIndex * 2 ^ subtreeHeight ≤ epoch ∧ epoch < (subtreeIndex + 1) * 2 ^ subtreeHeight

/-- Every inactive epoch is covered by the frontier address found by bounded search. -/
theorem frontierLevel_coversEpoch (I : Interval h) (e : Fin (2 ^ h)) :
    Subtree.CoversEpoch (frontierLevel I e) (e.val / 2 ^ frontierLevel I e) e.val := by
  constructor
  · exact Nat.div_mul_le_self e.val (2 ^ frontierLevel I e)
  · simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ e.val (by positivity : 0 < 2 ^ frontierLevel I e))

/-- No other maximal inactive subtree covering an inactive epoch has a different address. -/
theorem Subtree.isInactiveFrontier_unique (I : Interval h) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) (subtreeHeight subtreeIndex : ℕ)
    (hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex)
    (hcover : Subtree.CoversEpoch subtreeHeight subtreeIndex e.val) :
    subtreeHeight = frontierLevel I e ∧ subtreeIndex = e.val / 2 ^ subtreeHeight := by
  let m := frontierLevel I e
  have hindex : subtreeIndex = e.val / 2 ^ subtreeHeight :=
    index_eq_div_of_contains e.val subtreeHeight subtreeIndex hcover.1 hcover.2
  have hlevel_le : subtreeHeight ≤ m := by
    have hfind := Nat.le_findGreatest (P := fun z => Subtree.DisjointFromInterval I z (e.val /
      2 ^ z))
      hf.height_le (by simpa [hindex] using hf.disjoint)
    exact hfind
  have hm : Subtree.DisjointFromInterval I m (e.val / 2 ^ m) := by
    have hzero : Subtree.DisjointFromInterval I 0 (e.val / 2 ^ 0) := by
      simpa using (Subtree.disjointFromInterval_leaf_iff I e).2 he
    exact Nat.findGreatest_spec (P := fun z => Subtree.DisjointFromInterval I z (e.val / 2 ^ z))
      (Nat.zero_le h) hzero
  have hlevel_ge : m ≤ subtreeHeight := by
    by_contra hlt
    have hlt' : subtreeHeight < m := by omega
    have hparent : ¬ Subtree.DisjointFromInterval I (subtreeHeight + 1)
        (e.val / 2 ^ (subtreeHeight + 1)) := by
      simpa [hindex, pow_succ, Nat.div_div_eq_div_mul] using hf.parent_not_disjoint
    exact hparent (Subtree.disjointFromInterval_descendant I e (subtreeHeight + 1) m (by omega) hm)
  exact ⟨by omega, hindex⟩

/-- A frontier node can cover only epochs outside the active interval. -/
theorem Epoch.not_isActive_of_isInactiveFrontier_coversEpoch (I : Interval h) (e : Fin (2 ^ h))
    (subtreeHeight subtreeIndex : ℕ) (hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex)
    (hcover : Subtree.CoversEpoch subtreeHeight subtreeIndex e.val) : ¬ Epoch.IsActive I e := by
  intro he
  rcases he with ⟨ha, hb⟩
  rcases hcover with ⟨hlo, hhi⟩
  rcases hf.disjoint with hbefore | hafter
  · omega
  · omega

/-- An inactive epoch has no inactive ancestor strictly above its maximal frontier node. -/
theorem frontier_above_not_disjointFromInterval (I : Interval h) (e : Fin (2 ^ h))
    (subtreeHeight : ℕ)
    (hlt : frontierLevel I e < subtreeHeight) (hle : subtreeHeight ≤ h) :
    ¬ Subtree.DisjointFromInterval I subtreeHeight (e.val / 2 ^ subtreeHeight) := by
  intro hinactive
  have hlarge := Nat.le_findGreatest
    (P := fun z => Subtree.DisjointFromInterval I z (e.val / 2 ^ z)) hle hinactive
  change subtreeHeight ≤ frontierLevel I e at hlarge
  omega

/-- No legal node of a full active interval can be a filler root. -/
theorem Subtree.full_not_isInactiveFrontier (h subtreeHeight subtreeIndex : ℕ) :
    ¬ Subtree.IsInactiveFrontier (Interval.full h) subtreeHeight subtreeIndex := by
  intro hf
  obtain ⟨_, hbound, hinactive, _⟩ := hf
  have hp : 0 < 2 ^ subtreeHeight := by positivity
  have ht : subtreeIndex * 2 ^ subtreeHeight < 2 ^ h := by nlinarith
  rcases hinactive with hbefore | hafter
  · simp only [Interval.full, Fin.val_zero] at hbefore
    have hpositive : 0 < (subtreeIndex + 1) * 2 ^ subtreeHeight :=
      Nat.mul_pos (by omega) hp
    omega
  · simp only [Interval.full] at hafter
    omega

/-- Every epoch is active in the full interval. -/
theorem Epoch.isActive_full (e : Fin (2 ^ h)) : Epoch.IsActive (Interval.full h) e := by
  constructor
  · simp [Interval.full]
  · have hp : 0 < 2 ^ h := by positivity
    simp only [Interval.full, Fin.le_def]
    omega

/-- Finite coordinates for an independently sampled maximal inactive subtree root. -/
abbrev Subtree.FrontierNode (I : Interval h) :=
  { address : Fin (h + 1) × Fin (2 ^ h) //
    let (subtreeHeight, subtreeIndex) := address
    Subtree.IsInactiveFrontier I subtreeHeight.val subtreeIndex.val }

/-- The computable frontier address associated to an inactive epoch. -/
@[expose] def frontierOf (I : Interval h) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) : Subtree.FrontierNode I :=
  let subtreeHeight := frontierLevel I e
  have hfrontier := frontierLevel_isInactiveFrontier I e he
  let address : Fin (h + 1) × Fin (2 ^ h) :=
    (⟨subtreeHeight, Nat.lt_succ_of_le hfrontier.height_le⟩,
      ⟨e.val / 2 ^ subtreeHeight, (Merkle.ancestor_legal e subtreeHeight hfrontier.height_le).2⟩)
  ⟨address, hfrontier⟩

/-- The computed maximal frontier node covers its inactive epoch. -/
theorem frontierOf_coversEpoch (I : Interval h) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) :
    let node := frontierOf I e he
    let (subtreeHeight, subtreeIndex) := node.val
    Subtree.CoversEpoch subtreeHeight.val subtreeIndex.val e.val := by
  exact frontierLevel_coversEpoch I e

/-- Every frontier node containing an inactive epoch is the computed maximal node. -/
theorem Subtree.frontierNode_unique (I : Interval h) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) (node : Subtree.FrontierNode I)
    (hcover : let (subtreeHeight, subtreeIndex) := node.val
      Subtree.CoversEpoch subtreeHeight.val subtreeIndex.val e.val) :
    node = frontierOf I e he := by
  obtain ⟨address, hfrontier⟩ := node
  obtain ⟨subtreeHeight, subtreeIndex⟩ := address
  obtain ⟨hl, hi⟩ := Subtree.isInactiveFrontier_unique I e he subtreeHeight.val subtreeIndex.val
    hfrontier hcover
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hl
  · apply Fin.ext
    simpa [frontierOf, hl] using hi

/-- Every inactive frontier is strictly below the public root because the active interval
contains its first epoch. -/
theorem Subtree.IsInactiveFrontier.height_lt (I : Interval h) (subtreeHeight subtreeIndex : ℕ)
    (hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex) : subtreeHeight < h := by
  exact hf.1

/-- One digest for each maximal inactive subtree. -/
abbrev Fillers (I : Interval h) (H : Type) := Subtree.FrontierNode I → H

instance (h : ℕ) : IsEmpty (Subtree.FrontierNode (Interval.full h)) where
  false node := by
    obtain ⟨⟨subtreeHeight, subtreeIndex⟩, hfrontier⟩ := node
    exact Subtree.full_not_isInactiveFrontier h subtreeHeight.val subtreeIndex.val hfrontier

/-- Sample independent uniform digests only at maximal inactive subtree roots. -/
@[expose] noncomputable def sampleFillers (I : Interval h) (H : Type) [SampleableType H] :
    ProbComp (Fillers I H) :=
  if hc : Fintype.card (Subtree.FrontierNode I) = 0 then
    let emptyFrontier : IsEmpty (Subtree.FrontierNode I) := Fintype.card_eq_zero_iff.mp hc
    pure (fun node => False.elim (emptyFrontier.false node))
  else Fintype.mPi (fun _ : Subtree.FrontierNode I => $ᵗ H)

/-- Full-range key generation has no filler draw or filler output coordinate. -/
theorem sampleFillers_full (h : ℕ) (H : Type) [SampleableType H] :
    sampleFillers (Interval.full h) H = pure (fun x => isEmptyElim x) := by
  have hc : Fintype.card (Subtree.FrontierNode (Interval.full h)) = 0 :=
    Fintype.card_eq_zero
  simp only [sampleFillers, dite_eq_left hc]
  congr 1

/-- The mixed tree's natural-index leaf adapter. A leaf covered by a larger inactive subtree
may retain its ordinary endpoint hash; the ancestor filler replaces that subtree's result. -/
@[expose] def leaf {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) (subtreeIndex : ℕ) : H :=
  if hi : subtreeIndex < 2 ^ h then
    if hf : Subtree.IsInactiveFrontier I 0 subtreeIndex then
      fillers ⟨(⟨0, by omega⟩, ⟨subtreeIndex, hi⟩), hf⟩
    else P.leafHash pp ⟨subtreeIndex, hi⟩ (xs ⟨subtreeIndex, hi⟩)
  else P.leafHash pp 0 (xs 0)

/-- The mixed tree's natural-index pair adapter. A frontier node terminates recursion at
its stored uniform digest; all other reachable internal nodes use the ordinary ordered pair hash. -/
@[expose] def node {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (subtreeHeight subtreeIndex : ℕ) (left right : H) : H :=
  if hl : subtreeHeight < h + 1 then
    if hi : subtreeIndex < 2 ^ h then
      if hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex then
        fillers ⟨(⟨subtreeHeight, hl⟩, ⟨subtreeIndex, hi⟩), hf⟩
      else P.nodeHash pp ⟨subtreeHeight, hl⟩ ⟨subtreeIndex, hi⟩ left right
    else left
  else left

/-- The ordinary addressed pair hash on natural indices, including the complete tree's
out-of-rectangle default. This is the recurrence used by unrestricted root recovery. -/
@[expose] def ordinaryNode {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (subtreeHeight subtreeIndex : ℕ) (left right : H) : H :=
  if hl : subtreeHeight < h + 1 then
    if hi : subtreeIndex < 2 ^ h then
      P.nodeHash pp ⟨subtreeHeight, hl⟩ ⟨subtreeIndex, hi⟩ left right
    else left
  else left

/-- The unrestricted complete-tree root recovery is the ordinary addressed climb. -/
theorem recoverRoot_eq_climb {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) (auth : Fin h → H) :
    P.recoverRoot pp e xs auth =
      PerfectMerkleTree.climb (ordinaryNode P pp) e.val
        (P.leafHash pp e xs) (List.ofFn auth) := by
  unfold HashInstance.recoverRoot HashInstance.nodeExtension ordinaryNode
  rfl

/-- Mixed-tree digest of the subtree at a natural height and index. -/
@[expose] def subtreeRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ) : H :=
  PerfectMerkleTree.merkleRoot (leaf P I pp xs fillers) (node P I pp fillers)
    subtreeHeight subtreeIndex

/-- Public root of the mixed tree. -/
@[expose] def root {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) : H :=
  subtreeRoot P I pp xs fillers h 0

/-- Leaf-first authentication path in the mixed tree. -/
@[expose] def authPath {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) : Fin h → H :=
  fun z => (PerfectMerkleTree.authPath (leaf P I pp xs fillers)
    (node P I pp fillers) e h)[z.val]'(by simp)

/-- In a full interval, each legal leaf is the ordinary hashed endpoint vector. -/
theorem leaf_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers (Interval.full h) H)
    (e : Fin (2 ^ h)) :
    leaf P (Interval.full h) pp xs fillers e.val = P.leafHash pp e (xs e) := by
  simp [leaf, e.isLt, Subtree.full_not_isInactiveFrontier]

/-- In a full interval, each reachable internal address uses the ordinary pair hash. -/
theorem node_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (fillers : Fillers (Interval.full h) H) (subtreeHeight subtreeIndex : ℕ)
    (hl : subtreeHeight ≤ h) (hi : (subtreeIndex + 1) * 2 ^ subtreeHeight ≤ 2 ^ h)
    (left right : H) :
    node P (Interval.full h) pp fillers subtreeHeight subtreeIndex left right =
      P.nodeHash pp ⟨subtreeHeight, by omega⟩
        ⟨subtreeIndex, (Merkle.subtree_legal hl hi).2⟩ left right := by
  have hl' : subtreeHeight < h + 1 := by omega
  have hi' := (Merkle.subtree_legal hl hi).2
  simp [node, hl', hi', Subtree.full_not_isInactiveFrontier]

/-- At the full interval, `root` equals `HashInstance.merkleRoot` on the same endpoint array. -/
theorem root_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers (Interval.full h) H) :
    root P (Interval.full h) pp xs fillers = P.merkleRoot pp xs := by
  unfold root subtreeRoot HashInstance.merkleRoot
  apply Merkle.root_extension_independent _ _ _ _ h h 0 le_rfl (by simp)
  · intro i hi
    simpa [HashInstance.leafExtension, hi] using leaf_full P pp xs fillers ⟨i, hi⟩
  · intro j hj hle i hi l r
    have hj' : j < h + 1 := by omega
    have hi' := (Merkle.subtree_legal hle hi).2
    simpa [HashInstance.nodeExtension, hj', hi'] using
      node_full P pp fillers j i hle hi l r

/-- At the full interval, `authPath` equals `HashInstance.authPath` for every epoch. -/
theorem authPath_full {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers (Interval.full h) H)
    (e : Fin (2 ^ h)) :
    authPath P (Interval.full h) pp xs fillers e = P.authPath pp xs e := by
  have heq := Merkle.authPath_extension_independent
    (leaf P (Interval.full h) pp xs fillers) (P.leafExtension pp xs)
    (node P (Interval.full h) pp fillers) (P.nodeExtension pp) h e
    (by intro i hi
        simpa [HashInstance.leafExtension, hi] using leaf_full P pp xs fillers ⟨i, hi⟩)
    (by intro j hj hle i hi l r
        have hj' : j < h + 1 := by omega
        have hi' := (Merkle.subtree_legal hle hi).2
        simpa [HashInstance.nodeExtension, hj', hi'] using
          node_full P pp fillers j i hle hi l r)
  funext z
  unfold authPath HashInstance.authPath
  simp only [heq]

/-- Putative recovery depends only on pair hashes along its selected leaf's ancestors. -/
private theorem putativeRoot_congr_ancestors {Y : Type} {s : BinaryTree.Skeleton}
    (node₁ node₂ : BinaryTree.SkeletonInternalIndex s → Y → Y → Y)
    (idx : BinaryTree.SkeletonLeafIndex s) (value : Y)
    (path : List.Vector Y idx.depth)
    (hn : ∀ a, a.IsAncestorOf idx → ∀ l r, node₁ a l r = node₂ a l r) :
    AddressedMerkleTree.getPutativeRootAddressedWithHash node₁ idx value path =
      AddressedMerkleTree.getPutativeRootAddressedWithHash node₂ idx value path := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft sub ih =>
    simp only [AddressedMerkleTree.getPutativeRootAddressedWithHash]
    rw [ih (fun a => node₁ (.ofLeft a)) (fun a => node₂ (.ofLeft a)) path.tail
      (by intro a ha l r; exact hn (.ofLeft a) (by simpa using ha) l r)]
    exact hn .ofInternal (by simp) _ _
  | ofRight sub ih =>
    simp only [AddressedMerkleTree.getPutativeRootAddressedWithHash]
    rw [ih (fun a => node₁ (.ofRight a)) (fun a => node₂ (.ofRight a)) path.tail
      (by intro a ha l r; exact hn (.ofRight a) (by simpa using ha) l r)]
    exact hn .ofInternal (by simp) _ _

/-- Natural-index root recovery depends only on hashes at the opened leaf's parent addresses. -/
theorem climb_congr_ancestors {Y : Type} (node₁ node₂ : ℕ → ℕ → Y → Y → Y)
    (e : ℕ) (value : Y) (path : List Y)
    (hn : ∀ subtreeHeight, 0 < subtreeHeight → subtreeHeight ≤ path.length → ∀ l r,
      node₁ subtreeHeight (e / 2 ^ subtreeHeight) l r =
        node₂ subtreeHeight (e / 2 ^ subtreeHeight) l r) :
    PerfectMerkleTree.climb node₁ e value path =
      PerfectMerkleTree.climb node₂ e value path := by
  rw [PerfectMerkleTree.climb_eq node₁ e value path rfl,
    PerfectMerkleTree.climb_eq node₂ e value path rfl]
  apply putativeRoot_congr_ancestors
  intro a ha l r
  obtain ⟨hpos, hle⟩ := a.natAddr_height_pos_le (e / 2 ^ path.length)
  simpa [PerfectMerkleTree.nodeHashAt,
    PerfectMerkleTree.natAddr_index_of_isAncestorOf_ofNat ha] using
    hn _ hpos hle l r

/-- An active epoch retains its ordinary endpoint-vector leaf hash. -/
theorem leaf_isActive {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (he : Epoch.IsActive I e) :
    leaf P I pp xs fillers e.val = P.leafHash pp e (xs e) := by
  have hnot : ¬ Subtree.IsInactiveFrontier I 0 e.val := by
    simpa using Epoch.isActive_ancestor_not_isInactiveFrontier I e he 0
  simp [leaf, e.isLt, hnot]

/-- Every parent hash on an active path is the ordinary addressed pair hash. -/
theorem node_isActive_ancestor {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h)) (he : Epoch.IsActive I e)
    (subtreeHeight : ℕ) (hl : subtreeHeight ≤ h) (left right : H) :
    node P I pp fillers subtreeHeight (e.val / 2 ^ subtreeHeight) left right =
      P.nodeHash pp ⟨subtreeHeight, by omega⟩
        ⟨e.val / 2 ^ subtreeHeight, (Merkle.ancestor_legal e subtreeHeight hl).2⟩ left right := by
  have hl' : subtreeHeight < h + 1 := by omega
  have hi' := (Merkle.ancestor_legal e subtreeHeight hl).2
  simp [node, hl', hi', Epoch.isActive_ancestor_not_isInactiveFrontier I e he subtreeHeight]

/-- Every pair hash strictly above an inactive epoch's frontier uses the ordinary addressed
Merkle hash, which is the branch needed for inactive-opening collision extraction. -/
theorem node_above_frontier {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h))
    (subtreeHeight : ℕ) (hlt : frontierLevel I e < subtreeHeight) (hle : subtreeHeight ≤ h)
    (left right : H) :
    node P I pp fillers subtreeHeight (e.val / 2 ^ subtreeHeight) left right =
      P.nodeHash pp ⟨subtreeHeight, by omega⟩
        ⟨e.val / 2 ^ subtreeHeight, (Merkle.ancestor_legal e subtreeHeight hle).2⟩ left right := by
  have hl' : subtreeHeight < h + 1 := by omega
  have hi' := (Merkle.ancestor_legal e subtreeHeight hle).2
  have hnot : ¬ Subtree.IsInactiveFrontier I subtreeHeight (e.val / 2 ^ subtreeHeight) := by
    intro hf
    exact frontier_above_not_disjointFromInterval I e subtreeHeight hlt hle hf.disjoint
  simp [node, hl', hi', hnot]

/-- A finite mixed-tree path is the engine's leaf-first list. -/
private theorem ofFn_authPath {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) :
    List.ofFn (authPath P I pp xs fillers e) =
      PerfectMerkleTree.authPath (leaf P I pp xs fillers) (node P I pp fillers) e h := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [authPath]

/-- The `z`th leaf-first proof element is exactly the root of the height-`z` sibling subtree. -/
private theorem engine_authPath_get {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z height : ℕ)
    (hz : z < height) :
    (PerfectMerkleTree.authPath leaf nodeHash idx height)[z]'(by simp [hz]) =
      PerfectMerkleTree.merkleRoot leaf nodeHash z
        (PerfectMerkleTree.sibling (idx / 2 ^ z)) := by
  induction height with
  | zero => omega
  | succ height ih =>
    simp only [PerfectMerkleTree.authPath_succ]
    by_cases hlt : z < height
    · simpa [hlt] using ih hlt
    · have heq : z = height := by omega
      subst z
      simp

/-- Each mixed authentication-path entry is the digest of its exact sibling subtree. -/
theorem authPath_eq_subtreeRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (z : Fin h) :
    authPath P I pp xs fillers e z = subtreeRoot P I pp xs fillers z.val
      (PerfectMerkleTree.sibling (e.val / 2 ^ z.val)) := by
  exact engine_authPath_get (leaf P I pp xs fillers) (node P I pp fillers)
    e.val z.val h z.isLt

/-- For every active epoch, `HashInstance.recoverRoot` applied to its endpoint vector and
mixed-tree `authPath` yields `root`, using the addressed pair-hash recurrence. -/
theorem recoverRoot_authPath_isActive {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (he : Epoch.IsActive I e) :
    P.recoverRoot pp e (xs e) (authPath P I pp xs fillers e) =
      root P I pp xs fillers := by
  have hn : ∀ subtreeHeight, 0 < subtreeHeight → subtreeHeight ≤ h → ∀ l r,
      P.nodeExtension pp subtreeHeight (e.val / 2 ^ subtreeHeight) l r =
        node P I pp fillers subtreeHeight (e.val / 2 ^ subtreeHeight) l r := by
    intro subtreeHeight _ hle l r
    have hl' : subtreeHeight < h + 1 := by omega
    have hi' := (Merkle.ancestor_legal e subtreeHeight hle).2
    simpa [HashInstance.nodeExtension, hl', hi'] using
      (node_isActive_ancestor P I pp fillers e he subtreeHeight hle l r).symm
  have hc := climb_congr_ancestors (P.nodeExtension pp) (node P I pp fillers)
    e.val (P.leafHash pp e (xs e)) (List.ofFn (authPath P I pp xs fillers e))
    (by intro subtreeHeight hp hl l r; exact hn subtreeHeight hp (by simpa using hl) l r)
  have heq := PerfectMerkleTree.climb_authPath
    (leaf P I pp xs fillers) (node P I pp fillers) e.val h
  rw [← ofFn_authPath, leaf_isActive P I pp xs fillers e he] at heq
  rw [Nat.div_eq_of_lt e.isLt] at heq
  change PerfectMerkleTree.climb (P.nodeExtension pp) e.val
    (P.leafHash pp e (xs e)) (List.ofFn (authPath P I pp xs fillers e)) = _
  exact hc.trans (by simpa [root, subtreeRoot] using heq)

/-- A maximal inactive subtree contributes exactly its sampled digest, irrespective of the
complete start and endpoint arrays below it. -/
theorem subtreeRoot_isInactiveFrontier {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ)
    (hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex) :
    subtreeRoot P I pp xs fillers subtreeHeight subtreeIndex =
      fillers ⟨(⟨subtreeHeight, Nat.lt_succ_of_le hf.height_le⟩,
        ⟨subtreeIndex, (Merkle.subtree_legal hf.height_le hf.span_le).2⟩), hf⟩ := by
  have hle : subtreeHeight ≤ h := hf.height_le
  have hl : subtreeHeight < h + 1 := by omega
  have hi := (Merkle.subtree_legal hf.height_le hf.span_le).2
  cases subtreeHeight with
  | zero =>
    simp [subtreeRoot, leaf, hi, hf]
  | succ z =>
    simp [subtreeRoot, PerfectMerkleTree.merkleRoot_succ, node, hl, hi, hf]

/-- A subtree whose parent meets the active interval ignores all inactive endpoint entries. -/
private theorem subtreeRoot_eq_of_active_endpoints_eq {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ e, Epoch.IsActive I e → xs e = ys e)
    (z i : ℕ) (hz : z ≤ h) (hspan : (i + 1) * 2 ^ z ≤ 2 ^ h)
    (hparent : ¬ Subtree.DisjointFromInterval I (z + 1) (i / 2)) :
    subtreeRoot P I pp xs fillers z i = subtreeRoot P I pp ys fillers z i := by
  induction z generalizing i with
  | zero =>
    have hi : i < 2 ^ h := by simpa using hspan
    by_cases hd : Subtree.DisjointFromInterval I 0 i
    · have hf : Subtree.IsInactiveFrontier I 0 i :=
        (Subtree.isInactiveFrontier_iff_expanded I 0 i).2
          ⟨hz, hspan, hd, Or.inr hparent⟩
      rw [subtreeRoot_isInactiveFrontier P I pp xs fillers 0 i hf,
        subtreeRoot_isInactiveFrontier P I pp ys fillers 0 i hf]
    · have he : Epoch.IsActive I (⟨i, hi⟩ : Fin (2 ^ h)) := by
        by_contra hn
        exact hd ((Subtree.disjointFromInterval_leaf_iff I ⟨i, hi⟩).2 hn)
      simp only [subtreeRoot, PerfectMerkleTree.merkleRoot_zero]
      rw [leaf_isActive P I pp xs fillers ⟨i, hi⟩ he,
        leaf_isActive P I pp ys fillers ⟨i, hi⟩ he, hactive _ he]
  | succ z ih =>
    by_cases hd : Subtree.DisjointFromInterval I (z + 1) i
    · have hf : Subtree.IsInactiveFrontier I (z + 1) i :=
        (Subtree.isInactiveFrontier_iff_expanded I (z + 1) i).2
          ⟨hz, hspan, hd, Or.inr hparent⟩
      rw [subtreeRoot_isInactiveFrontier P I pp xs fillers (z + 1) i hf,
        subtreeRoot_isInactiveFrontier P I pp ys fillers (z + 1) i hf]
    · have hp : 0 < 2 ^ z := by positivity
      have hl : (2 * i + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [pow_succ] at hspan
        nlinarith
      have hr : (2 * i + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [pow_succ] at hspan
        nlinarith
      have hleft := ih (2 * i) (by omega) hl (by simpa using hd)
      have hright := ih (2 * i + 1) (by omega) hr (by
        have hi : (2 * i + 1) / 2 = i := by omega
        simpa only [hi] using hd)
      change node P I pp fillers (z + 1) i
        (subtreeRoot P I pp xs fillers z (2 * i))
        (subtreeRoot P I pp xs fillers z (2 * i + 1)) = _
      rw [hleft, hright]
      rfl

/-- The interval root depends only on active endpoint vectors and the retained frontier table. -/
theorem root_eq_of_active_endpoints_eq {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ e, Epoch.IsActive I e → xs e = ys e) :
    root P I pp xs fillers = root P I pp ys fillers := by
  apply subtreeRoot_eq_of_active_endpoints_eq P I pp xs ys fillers hactive h 0 le_rfl
    (by simp)
  let first := I.first
  have he : Epoch.IsActive I first := ⟨le_rfl, I.ordered⟩
  have hi : first.val < 2 ^ (h + 1) := by
    have hf := first.isLt
    rw [pow_succ]
    omega
  simpa [Nat.div_eq_of_lt hi] using
    Epoch.isActive_ancestor_not_disjointFromInterval I first he (h + 1)

/-- An honest active authentication path ignores inactive endpoint entries, including entries
strictly below an inactive frontier of positive height. -/
theorem authPath_eq_of_active_endpoints_eq {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ e, Epoch.IsActive I e → xs e = ys e)
    (e : Fin (2 ^ h)) (he : Epoch.IsActive I e) :
    authPath P I pp xs fillers e = authPath P I pp ys fillers e := by
  funext z
  rw [authPath_eq_subtreeRoot, authPath_eq_subtreeRoot]
  have hparent := Epoch.isActive_ancestor_not_disjointFromInterval I e he (z.val + 1)
  have hdiv : e.val / 2 ^ (z.val + 1) = (e.val / 2 ^ z.val) / 2 := by
    simp [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv] at hparent
  have hsib := PerfectMerkleTree.sibling_div_two (e.val / 2 ^ z.val)
  have hs : PerfectMerkleTree.sibling (e.val / 2 ^ z.val) + 1 ≤
      ((e.val / 2 ^ z.val) / 2 + 1) * 2 := by
    unfold PerfectMerkleTree.sibling
    split_ifs <;> omega
  obtain ⟨_, _, hbound⟩ := Merkle.ancestor_reachable e (z.val + 1) (by omega) (by omega)
  rw [hdiv, pow_succ] at hbound
  apply subtreeRoot_eq_of_active_endpoints_eq P I pp xs ys fillers hactive z.val _ (by omega)
  · nlinarith [Nat.mul_le_mul_right (2 ^ z.val) hs]
  · simpa only [hsib] using hparent

/-- The digest stored at a legal maximal inactive address. -/
@[expose] def frontierValue {H : Type} (I : Interval h) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ)
    (hf : Subtree.IsInactiveFrontier I subtreeHeight subtreeIndex) : H :=
  fillers ⟨(⟨subtreeHeight, Nat.lt_succ_of_le hf.height_le⟩,
    ⟨subtreeIndex, (Merkle.subtree_legal hf.height_le hf.span_le).2⟩), hf⟩

/-- A direct partial-tree recursion. At a maximal inactive node it returns the stored filler
without descending; otherwise it follows the ordinary hashed-leaf and pair-hash recursion. -/
@[expose] def prunedRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) : (subtreeHeight subtreeIndex : ℕ) → H
  | 0, subtreeIndex =>
      if hf : Subtree.IsInactiveFrontier I 0 subtreeIndex then
        frontierValue I fillers 0 subtreeIndex hf
      else leaf P I pp xs fillers subtreeIndex
  | subtreeHeight + 1, subtreeIndex =>
      if hf : Subtree.IsInactiveFrontier I (subtreeHeight + 1) subtreeIndex then
        frontierValue I fillers (subtreeHeight + 1) subtreeIndex hf
      else node P I pp fillers (subtreeHeight + 1) subtreeIndex
        (prunedRoot P I pp xs fillers subtreeHeight (2 * subtreeIndex))
        (prunedRoot P I pp xs fillers subtreeHeight (2 * subtreeIndex + 1))

/-- The direct pruned recursion and the addressed perfect-tree engine have identical digests
at every height and address. -/
theorem prunedRoot_eq_subtreeRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (subtreeHeight subtreeIndex : ℕ) :
    prunedRoot P I pp xs fillers subtreeHeight subtreeIndex =
      subtreeRoot P I pp xs fillers subtreeHeight subtreeIndex := by
  induction subtreeHeight generalizing subtreeIndex with
  | zero =>
      by_cases hf : Subtree.IsInactiveFrontier I 0 subtreeIndex
      · simp [prunedRoot, hf, frontierValue,
          subtreeRoot_isInactiveFrontier P I pp xs fillers 0 subtreeIndex hf]
      · simp [prunedRoot, hf, subtreeRoot]
  | succ subtreeHeight ih =>
      by_cases hf : Subtree.IsInactiveFrontier I (subtreeHeight + 1) subtreeIndex
      · simp [prunedRoot, hf, frontierValue,
          subtreeRoot_isInactiveFrontier P I pp xs fillers (subtreeHeight + 1) subtreeIndex hf]
      · simp only [prunedRoot, dite_eq_right hf, subtreeRoot,
          PerfectMerkleTree.merkleRoot_succ]
        rw [ih (2 * subtreeIndex), ih (2 * subtreeIndex + 1)]
        rfl

/-- Every authentication entry is the corresponding pruned sibling-subtree digest. -/
theorem authPath_eq_prunedRoot {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (e : Fin (2 ^ h)) (z : Fin h) :
    authPath P I pp xs fillers e z = prunedRoot P I pp xs fillers z.val
      (PerfectMerkleTree.sibling (e.val / 2 ^ z.val)) := by
  rw [authPath_eq_subtreeRoot, prunedRoot_eq_subtreeRoot]

/-- A complete subtree can be used as a leaf in a higher perfect tree, with original
address levels retained by shifting each parent hash height. -/
theorem subtreeRoot_shift {PP T X H : Type} {w v : ℕ}
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (z k t : ℕ) :
    subtreeRoot P I pp xs fillers (z + k) t =
      PerfectMerkleTree.merkleRoot
        (fun i => subtreeRoot P I pp xs fillers z i)
        (fun j i => node P I pp fillers (z + j) i) k t := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, PerfectMerkleTree.merkleRoot_succ]
    change node P I pp fillers (z + k + 1) t
      (subtreeRoot P I pp xs fillers (z + k) (2 * t))
      (subtreeRoot P I pp xs fillers (z + k) (2 * t + 1)) = _
    rw [ih (2 * t), ih (2 * t + 1)]
    simp only [Nat.add_succ]

end GXMSS.IntervalMerkle
