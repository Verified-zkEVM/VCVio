/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Fors.Schedule
public import Mathlib.Data.List.TakeDrop

/-!
# Dependency geometry of actual FORS call schedules

All-height subtree footprints, sibling and forest disjointness establish unique writes and
strict-prefix child reads in the actual selected-provider-first signing order.
-/

public section

namespace SLHDSA.Graph.ForsSchedule

variable {p : Params}

/-- Structural coordinates within a global FORS subtree, retaining its key and all heights. -/
@[expose] def Footprint (key : ForsKey p) (height index : Nat) : StructuralNode p → Prop
  | .forsPrf location leaf => location = key ∧ leaf.val / 2 ^ height = index
  | .forsTree location level position =>
      location = key ∧ level.val ≤ height ∧ position.val / 2 ^ (height - level.val) = index
  | _ => False

/-- A coordinate in either child subtree lies in the original parent interval. -/
theorem footprint_child (key : ForsKey p) (height index : Nat) (side : Fin 2)
    (node : StructuralNode p) (member : Footprint key height (2 * index + side.val) node) :
    Footprint key (height + 1) index node := by
  cases node with
  | forsPrf location leaf =>
      obtain ⟨same, descendant⟩ := member
      refine ⟨same, ?_⟩
      rw [pow_succ, ← Nat.div_div_eq_div_mul, descendant]
      have := side.isLt
      omega
  | forsTree location level position =>
      obtain ⟨same, lower, descendant⟩ := member
      refine ⟨same, by omega, ?_⟩
      rw [show height + 1 - level.val = (height - level.val) + 1 by omega,
        pow_succ, ← Nat.div_div_eq_div_mul, descendant]
      have := side.isLt
      omega
  | _ => contradiction

/-- Every actual provider and tree node lies in the exact global descendant interval. -/
theorem mem_subtree_footprint (key : ForsKey p) (height : Nat) (bound : height ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - height))) (node : StructuralNode p)
    (member : node ∈ subtree key height bound index) : Footprint key height index.val node := by
  induction height with
  | zero =>
      simp only [subtree, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [Footprint, treeNode]
  | succ height ih =>
      simp only [subtree, List.mem_append, List.mem_singleton] at member
      rcases member with (left | right) | rfl
      · exact footprint_child key height index.val 0 node (ih _ _ left)
      · exact footprint_child key height index.val 1 node (ih _ _ right)
      · simp [Footprint, treeNode]

/-- The left and right subtree intervals are disjoint for every structural node family. -/
theorem footprint_children_disjoint (key : ForsKey p) (height index : Nat)
    (node : StructuralNode p) :
    ¬ (Footprint key height (2 * index) node ∧ Footprint key height (2 * index + 1) node) := by
  cases node with
  | forsPrf location leaf =>
      rintro ⟨⟨_, left⟩, ⟨_, right⟩⟩
      omega
  | forsTree location level position =>
      rintro ⟨⟨_, _, left⟩, ⟨_, _, right⟩⟩
      omega
  | _ => simp [Footprint]

/-- A subtree's final parent is outside both of its lower child intervals. -/
theorem parent_not_in_lower (key : ForsKey p) (height : Nat) (bound : height + 1 ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - (height + 1)))) (other : Nat) :
    ¬ Footprint key height other (treeNode key (height + 1) bound index) := by
  simp [Footprint, treeNode]

/-- The actual postorder subtree never writes the same structural coordinate twice. -/
theorem subtree_nodup (key : ForsKey p) (height : Nat) (bound : height ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - height))) :
    (subtree key height bound index).Nodup := by
  induction height with
  | zero => simp [subtree, treeNode]
  | succ height ih =>
      rw [subtree, List.nodup_append', List.nodup_append']
      refine ⟨⟨ih _ _, ih _ _, ?_⟩, by simp, ?_⟩
      · apply List.disjoint_left.mpr
        intro node left right
        exact footprint_children_disjoint key height index.val node
          ⟨mem_subtree_footprint key height (by omega) _ node left,
            mem_subtree_footprint key height (by omega) _ node right⟩
      · apply List.disjoint_left.mpr
        intro node member parent
        simp only [List.mem_singleton] at parent
        subst node
        rcases List.mem_append.mp member with left | right
        · exact parent_not_in_lower key height bound index (2 * index.val)
            (mem_subtree_footprint key height (by omega) _ _ left)
        · exact parent_not_in_lower key height bound index (2 * index.val + 1)
            (mem_subtree_footprint key height (by omega) _ _ right)

private def Ready (valid : p.Valid) (nodes : List (StructuralNode p)) : Prop :=
  ∀ (index : Nat) (bound : index < nodes.length) (child : StructuralNode p),
    Node.structural child ∈ (nodes[index]).children valid → child ∈ nodes.take index

private theorem ready_nil (valid : p.Valid) : Ready valid [] := by
  intro index bound
  simp at bound

private theorem ready_append (valid : p.Valid) (left right : List (StructuralNode p))
    (first : Ready valid left) (second : Ready valid right) : Ready valid (left ++ right) := by
  intro index bound child member
  by_cases earlier : index < left.length
  · rw [List.getElem_append_left earlier] at member
    rw [List.take_append_of_le_length (by omega)]
    exact first index earlier child member
  · have later : index - left.length < right.length := by
      simp only [List.length_append] at bound
      omega
    rw [List.getElem_append_right (by omega)] at member
    have found := second (index - left.length) later child member
    rw [List.take_append]
    exact List.mem_append_right _ found

private theorem ready_append_parent (valid : p.Valid) (nodes : List (StructuralNode p))
    (parent : StructuralNode p) (ready : Ready valid nodes)
    (children : ∀ child : StructuralNode p, Node.structural child ∈ parent.children valid →
      child ∈ nodes) : Ready valid (nodes ++ [parent]) := by
  intro index bound child member
  by_cases earlier : index < nodes.length
  · rw [List.getElem_append_left earlier] at member
    rw [List.take_append_of_le_length (by omega)]
    exact ready index earlier child member
  · have same : index = nodes.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst index
    have atEnd : (nodes ++ [parent])[nodes.length] = parent := by simp
    rw [atEnd] at member
    simpa using children child member

private theorem subtree_ready (valid : p.Valid) (key : ForsKey p) (height : Nat)
    (bound : height ≤ p.a) (index : Fin (p.k * 2 ^ (p.a - height))) :
    Ready valid (subtree key height bound index) := by
  induction height with
  | zero =>
      intro position positionBound child member
      have cases : position = 0 ∨ position = 1 := by simp [subtree] at positionBound; omega
      rcases cases with rfl | rfl
      · simp [subtree, StructuralNode.children] at member
      · simp [subtree, treeNode, StructuralNode.children] at member
        simp [subtree, member]
  | succ height ih =>
      rw [subtree]
      apply ready_append_parent valid _ _
      · exact ready_append valid _ _ (ih (by omega) _) (ih (by omega) _)
      · intro child member
        simp only [treeNode, StructuralNode.children,
          show ¬ height + 1 = 0 by omega, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false,
          Node.structural.injEq] at member
        rcases member with rfl | rfl
        · apply List.mem_append_left
          exact root_mem_subtree key height (by omega) _
        · apply List.mem_append_right
          exact root_mem_subtree key height (by omega) _

private theorem auth_ready (valid : p.Valid) (key : ForsKey p)
    (selected : Fin (p.k * 2 ^ p.a)) (height : Nat) (bound : height ≤ p.a) :
    Ready valid (auth key selected height bound) := by
  induction height with
  | zero => exact ready_nil valid
  | succ height ih =>
      exact ready_append valid _ _ (ih (by omega)) (subtree_ready valid key height (by omega) _)

private theorem ready_flatten (valid : p.Valid) (lists : List (List (StructuralNode p)))
    (ready : ∀ nodes ∈ lists, Ready valid nodes) : Ready valid lists.flatten := by
  induction lists with
  | nil => exact ready_nil valid
  | cons nodes rest ih =>
      exact ready_append valid _ _ (ready nodes (by simp))
        (ih fun next member => ready next (by simp [member]))

/-- Every actual nonseed child is available strictly before its dependent call. -/
theorem signing_children_before (valid : p.Valid) (key : ForsKey p) (md : List Byte)
    (position : Fin (signing key md).length) (child : StructuralNode p)
    (member : Node.structural child ∈ ((signing key md)[position]).children valid) :
    child ∈ (signing key md).take position := by
  have ready : Ready valid (signing key md) := by
    apply ready_flatten
    intro nodes member
    obtain ⟨tree, rfl⟩ := List.mem_ofFn.mp member
    change Ready valid ([.forsPrf key (selected md tree)] ++ auth key (selected md tree) p.a le_rfl)
    apply ready_append valid
    · intro index bound child member
      have zero : index = 0 := by simp at bound; omega
      subst index
      simp [StructuralNode.children] at member
    · exact auth_ready valid key _ _ _
  exact ready position position.isLt child member

private theorem sibling_ne_self (index : Nat) : PerfectMerkleTree.sibling index ≠ index := by
  unfold PerfectMerkleTree.sibling
  split_ifs <;> omega

private theorem sibling_intervals_disjoint (key : ForsKey p) (selected lower upper : Nat)
    (ordered : lower < upper) (node : StructuralNode p) :
    ¬ (Footprint key lower (PerfectMerkleTree.sibling (selected / 2 ^ lower)) node ∧
      Footprint key upper (PerfectMerkleTree.sibling (selected / 2 ^ upper)) node) := by
  have arithmetic (level position : Nat) (levelBound : level ≤ lower)
      (first : position / 2 ^ (lower - level) = PerfectMerkleTree.sibling (selected / 2 ^ lower))
      (second : position / 2 ^ (upper - level) =
        PerfectMerkleTree.sibling (selected / 2 ^ upper)) : False := by
    have same : PerfectMerkleTree.sibling (selected / 2 ^ upper) = selected / 2 ^ upper := by
      calc
        PerfectMerkleTree.sibling (selected / 2 ^ upper) = position / 2 ^ (upper - level) :=
          second.symm
        _ = position / 2 ^ (lower - level) / 2 ^ (upper - lower) := by
          rw [PerfectMerkleTree.div_pow_eq_div_pow_div_pow position (lower - level)
            (upper - level) (by omega),
            show upper - level - (lower - level) = upper - lower by omega]
        _ = PerfectMerkleTree.sibling (selected / 2 ^ lower) / 2 ^ (upper - lower) := by rw [first]
        _ = selected / 2 ^ lower / 2 ^ (upper - lower) :=
          PerfectMerkleTree.sibling_div_pow _ _ (by omega)
        _ = selected / 2 ^ upper :=
          (PerfectMerkleTree.div_pow_eq_div_pow_div_pow _ _ _ (by omega)).symm
    exact sibling_ne_self _ same
  cases node with
  | forsPrf location leaf =>
      rintro ⟨⟨_, first⟩, ⟨_, second⟩⟩
      exact arithmetic 0 leaf.val (by omega) first second
  | forsTree location level position =>
      rintro ⟨⟨_, levelBound, first⟩, ⟨_, _, second⟩⟩
      exact arithmetic level.val position.val levelBound first second
  | _ => simp [Footprint]

private theorem auth_footprint (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a))
    (height : Nat) (bound : height ≤ p.a) (node : StructuralNode p)
    (member : node ∈ auth key selected height bound) :
    ∃ level < height,
      Footprint key level (PerfectMerkleTree.sibling (selected.val / 2 ^ level)) node := by
  induction height with
  | zero => simp [auth] at member
  | succ height ih =>
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨level, lower, inside⟩ := ih (by omega) earlier
        exact ⟨level, by omega, inside⟩
      · exact ⟨height, by omega, mem_subtree_footprint key height (by omega) _ _ current⟩

/-- Authentication siblings and their descendants are computed once in the actual order. -/
theorem auth_nodup (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a))
    (height : Nat) (bound : height ≤ p.a) : (auth key selected height bound).Nodup := by
  induction height with
  | zero => simp [auth]
  | succ height ih =>
      rw [auth, List.nodup_append']
      refine ⟨ih (by omega), subtree_nodup key height (by omega) _, ?_⟩
      apply List.disjoint_left.mpr
      intro node earlier current
      obtain ⟨level, lower, first⟩ := auth_footprint key selected height (by omega) node earlier
      exact sibling_intervals_disjoint key selected.val level height lower node
        ⟨first, mem_subtree_footprint key height (by omega) _ _ current⟩

private def InForestTree (key : ForsKey p) (tree : Nat) : StructuralNode p → Prop
  | .forsPrf location leaf => location = key ∧ leaf.val / 2 ^ p.a = tree
  | .forsTree location level index =>
      location = key ∧ index.val / 2 ^ (p.a - level.val) = tree
  | _ => False

private theorem footprint_forestTree (key : ForsKey p) (selected height : Nat)
    (bound : height < p.a) (node : StructuralNode p)
    (inside : Footprint key height (PerfectMerkleTree.sibling (selected / 2 ^ height)) node) :
    InForestTree key (selected / 2 ^ p.a) node := by
  have arithmetic (level position : Nat) (levelBound : level ≤ height)
      (descendant : position / 2 ^ (height - level) =
        PerfectMerkleTree.sibling (selected / 2 ^ height)) :
      position / 2 ^ (p.a - level) = selected / 2 ^ p.a := by
    calc
      position / 2 ^ (p.a - level) =
          position / 2 ^ (height - level) / 2 ^ (p.a - height) := by
        rw [PerfectMerkleTree.div_pow_eq_div_pow_div_pow position (height - level)
          (p.a - level) (by omega),
          show p.a - level - (height - level) = p.a - height by omega]
      _ = PerfectMerkleTree.sibling (selected / 2 ^ height) / 2 ^ (p.a - height) := by
        rw [descendant]
      _ = selected / 2 ^ height / 2 ^ (p.a - height) :=
        PerfectMerkleTree.sibling_div_pow _ _ (by omega)
      _ = selected / 2 ^ p.a :=
        (PerfectMerkleTree.div_pow_eq_div_pow_div_pow _ _ _ (by omega)).symm
  cases node with
  | forsPrf location leaf =>
      obtain ⟨same, descendant⟩ := inside
      exact ⟨same, arithmetic 0 leaf.val (by omega) descendant⟩
  | forsTree location level index =>
      obtain ⟨same, levelBound, descendant⟩ := inside
      exact ⟨same, arithmetic level.val index.val levelBound descendant⟩
  | _ => contradiction

private theorem auth_forestTree (key : ForsKey p)
    (selected : Fin (p.k * 2 ^ p.a)) (height : Nat) (bound : height ≤ p.a)
    (node : StructuralNode p) (member : node ∈ auth key selected height bound) :
    InForestTree key (selected.val / 2 ^ p.a) node := by
  induction height with
  | zero => simp [auth] at member
  | succ height ih =>
      rw [auth, List.mem_append] at member
      rcases member with earlier | current
      · exact ih (by omega) earlier
      · exact footprint_forestTree key selected.val height (by omega) node
          (mem_subtree_footprint key height (by omega) _ _ current)

private theorem inForestTree_unique (key : ForsKey p) (left right : Nat)
    (node : StructuralNode p) (first : InForestTree key left node)
    (second : InForestTree key right node) : left = right := by
  cases node with
  | forsPrf location leaf | forsTree location level index => exact first.2.symm.trans second.2
  | _ => contradiction

private def slotSchedule (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a)) :
    List (StructuralNode p) :=
  .forsPrf key selected :: auth key selected p.a le_rfl

private theorem slot_forestTree (key : ForsKey p) (md : List Byte) (tree : Fin p.k)
    (node : StructuralNode p) (member : node ∈ slotSchedule key (selected md tree)) :
    InForestTree key tree.val node := by
  rcases List.mem_cons.mp member with rfl | auth
  · exact ⟨rfl, selected_div md tree⟩
  · have inside := auth_forestTree key (selected md tree) p.a le_rfl node auth
    rwa [selected_div] at inside

/-- The exact signing schedule never repeats a structural coordinate. -/
theorem signing_nodup (key : ForsKey p) (md : List Byte) : (signing key md).Nodup := by
  rw [signing, List.nodup_flatten]
  constructor
  · intro nodes member
    obtain ⟨tree, rfl⟩ := List.mem_ofFn.mp member
    exact List.nodup_cons.mpr ⟨selected_prf_not_mem_auth key _ _ _, auth_nodup key _ _ _⟩
  · rw [List.pairwise_ofFn]
    intro left right ordered
    apply List.disjoint_left.mpr
    intro node first second
    have same := inForestTree_unique key left.val right.val node
      (slot_forestTree key md left node first) (slot_forestTree key md right node second)
    exact (Nat.ne_of_lt ordered) same

/-- The signature's selected secret is an actual provider call in the signing schedule. -/
theorem selected_mem_signing (key : ForsKey p) (md : List Byte) (tree : Fin p.k) :
    StructuralNode.forsPrf key (selected md tree) ∈ signing key md := by
  apply List.mem_flatten.mpr
  exact ⟨_, List.mem_ofFn.mpr ⟨tree, rfl⟩, by simp⟩

/-- Each returned authentication cell is computed by the actual signing schedule. -/
theorem authentication_mem_signing (key : ForsKey p) (md : List Byte) (tree : Fin p.k)
    (height : Fin p.a) : authentication key (selected md tree) height ∈ signing key md := by
  apply List.mem_flatten.mpr
  refine ⟨_, List.mem_ofFn.mpr ⟨tree, rfl⟩, List.mem_cons_of_mem _ ?_⟩
  exact authentication_mem_auth key _ p.a le_rfl height

end SLHDSA.Graph.ForsSchedule
