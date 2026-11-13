/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Merkle

/-!
# Inclusive epoch intervals and inactive frontiers

A nonempty active range determines the unique maximal inactive subtree covering each inactive
epoch. Finite frontier addresses retain dyadic spans and exclude the public root.
-/

public section

namespace GXMSS.IntervalMerkle

variable {h : ℕ}

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
    · obtain ⟨_, _, hspan⟩ := PerfectMerkleTree.ancestor_reachable e m (Nat.pos_of_ne_zero hz) hle
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
      ⟨e.val / 2 ^ subtreeHeight,
        (PerfectMerkleTree.ancestor_legal e subtreeHeight hfrontier.height_le).2⟩)
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

end GXMSS.IntervalMerkle
