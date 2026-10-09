/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option
public import VCVio.OracleComp.SimSemantics.StateT.EqDistTriple.Simulate

/-!
# Equal-distribution triples for effectful Merkle traversals

Two runs of `PerfectMerkleTree.merkleRootM`, `intrinsicAuthPathM` or `climbM` in
`StateT σ ProbComp`, over different leaf and node callbacks, agree in distribution when the
callbacks are related by `OracleComp.EqDistTriple` at the addresses the traversal visits.

The relation between a node value and the state is a family `R h i y s`: the value `y` at height
`h` and index `i` is related to the state `s`, for instance by being recorded in it. It is stable
along the state preorder `r`, so a sibling computed earlier stays related while later subtrees
run. A node step at `(h + 1, i)` need agree only on inputs related to the current state as the
values of its children `(h, 2 * i)` and `(h, 2 * i + 1)`, and must relate its output to
`(h + 1, i)`. A leaf step must relate its output to `(0, i)`. A state invariant `Inv` is threaded
through every step. Along the trivial preorder `⊤`, with `R` and `Inv` trivial, the lemmas
transport equality of measures from every state.

The same rules hold for traversals over an oracle specification whose callbacks are related by
`QueryImpl.EqDistTriple` under one stateful interpretation `so`
(`QueryImpl.EqDistTriple.merkleRootM`, `intrinsicAuthPathM`, `climbM`): the simulation of a
traversal is the traversal of the simulated callbacks.
-/

public section

namespace PerfectMerkleTree

open OracleComp

variable {σ Y : Type} {r : σ → σ → Prop} [IsPreorder σ r] (Inv : σ → Prop)
  (R : ℕ → ℕ → Y → σ → Prop) {leaf₁ leaf₂ : ℕ → StateT σ ProbComp Y}
  {node₁ node₂ : ℕ → ℕ → Y → Y → StateT σ ProbComp Y}

private theorem div_two_pow_succ {i k j : ℕ} (h : i / 2 ^ k = j) : i / 2 ^ (k + 1) = j / 2 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, h]

/-- Roots of the perfect subtree at `(z, t)` agree when the leaf callbacks agree at its leaves
`i / 2 ^ z = t` and the node callbacks at its internal nodes `(h + 1, i)` with `h < z` and
`i / 2 ^ (z - (h + 1)) = t`; the right-hand root is related to the final state at `(z, t)`. -/
theorem merkleRootM_eqDistTriple (hR : ∀ h i y s s', r s s' → R h i y s → R h i y s')
    (z t : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = t →
      EqDistTriple r Inv (leaf₁ i) (leaf₂ i) fun y s ↦ Inv s ∧ R 0 i y s)
    (hnode : ∀ h i, h < z → i / 2 ^ (z - (h + 1)) = t → ∀ left right,
      EqDistTriple r (fun s ↦ Inv s ∧ R h (2 * i) left s ∧ R h (2 * i + 1) right s)
        (node₁ (h + 1) i left right) (node₂ (h + 1) i left right)
        fun y s ↦ Inv s ∧ R (h + 1) i y s) :
    EqDistTriple r Inv (merkleRootM leaf₁ node₁ z t) (merkleRootM leaf₂ node₂ z t)
      fun y s ↦ Inv s ∧ R z t y s := by
  induction z generalizing t with
  | zero => exact hleaf t (by simp)
  | succ z ih =>
    have sub : ∀ b < 2, EqDistTriple r Inv (merkleRootM leaf₁ node₁ z (2 * t + b))
        (merkleRootM leaf₂ node₂ z (2 * t + b)) fun y s ↦ Inv s ∧ R z (2 * t + b) y s :=
      fun b hb ↦ ih _ (fun i hi ↦ hleaf i (by rw [div_two_pow_succ hi]; omega))
        fun h i hh hi ↦ hnode h i (by omega) (by
          rw [show z + 1 - (h + 1) = z - (h + 1) + 1 by omega, div_two_pow_succ hi]; omega)
    refine (sub 0 (by omega)).bind fun left ↦
      (((sub 1 (by omega)).frame (F := R z (2 * t) left) fun s s' ↦ hR _ _ _ s s').bind
        fun right ↦ ?_)
    exact (hnode z t (by omega) (by simp) left right).mono
      (fun s hs ↦ ⟨hs.1.1, hs.2, hs.1.2⟩) fun _ _ hy ↦ hy

/-- Authentication paths of leaf `idx` over `z` levels agree when the callbacks agree at the
leaves and internal nodes of the height-`z` subtree containing `idx`; entry `j` of the right-hand
path is related to the final state as the value of the level-`j` sibling
`(j, sibling (idx / 2 ^ j))`. -/
theorem intrinsicAuthPathM_eqDistTriple (hR : ∀ h i y s s', r s s' → R h i y s → R h i y s')
    (idx z : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = idx / 2 ^ z →
      EqDistTriple r Inv (leaf₁ i) (leaf₂ i) fun y s ↦ Inv s ∧ R 0 i y s)
    (hnode : ∀ h i, h < z → i / 2 ^ (z - (h + 1)) = idx / 2 ^ z → ∀ left right,
      EqDistTriple r (fun s ↦ Inv s ∧ R h (2 * i) left s ∧ R h (2 * i + 1) right s)
        (node₁ (h + 1) i left right) (node₂ (h + 1) i left right)
        fun y s ↦ Inv s ∧ R (h + 1) i y s) :
    EqDistTriple r Inv (intrinsicAuthPathM leaf₁ node₁ idx z)
      (intrinsicAuthPathM leaf₂ node₂ idx z)
      fun path s ↦ Inv s ∧ ∀ j (hj : j < z), R j (sibling (idx / 2 ^ j)) path[j] s := by
  induction z with
  | zero => exact EqDistTriple.pure _ fun s hs ↦ ⟨hs, fun j hj ↦ absurd hj (by omega)⟩
  | succ z ih =>
    have hup : ∀ {i k j}, i / 2 ^ k = j → j / 2 = idx / 2 ^ z / 2 → i / 2 ^ (k + 1) =
        idx / 2 ^ (z + 1) := fun hi hj ↦ by rw [div_two_pow_succ hi, hj, div_two_pow_succ rfl]
    refine (ih (fun i hi ↦ hleaf i (hup hi rfl)) fun h i hh hi ↦ hnode h i (by omega) ?_).bind
      fun path ↦ ?_
    · rw [show z + 1 - (h + 1) = z - (h + 1) + 1 by omega]
      exact hup hi rfl
    refine ((merkleRootM_eqDistTriple Inv R hR z _ (fun i hi ↦ hleaf i (hup hi
      (sibling_div_two _))) fun h i hh hi ↦ hnode h i (by omega) ?_).frame
      (F := fun s ↦ ∀ j (hj : j < z), R j (sibling (idx / 2 ^ j)) path[j] s)
      fun s s' hs hF j hj ↦ hR _ _ _ _ _ hs (hF j hj)).bind fun root ↦
        EqDistTriple.pure _ fun s hs ↦ ⟨hs.1.1, fun j hj ↦ ?_⟩
    · rw [show z + 1 - (h + 1) = z - (h + 1) + 1 by omega]
      exact hup hi (sibling_div_two _)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · simpa [Vector.getElem_push_lt hj] using hs.2 j hj
      · simpa using hs.1.2

/-- Climbs from leaf `idx` agree when the node callbacks agree at the ancestors
`(h + 1, idx / 2 ^ (h + 1))` of the leaf, `h < auth.length`, and the starting value and every
path entry `auth[j]` are related to the starting state as the values of the leaf `(0, idx)` and
of the level-`j` sibling. The right-hand climb is related to the final state as the value of the
ancestor at height `auth.length`. -/
theorem climbM_eqDistTriple (hR : ∀ h i y s s', r s s' → R h i y s → R h i y s')
    (idx : ℕ) (node : Y) (auth : List Y)
    (hnode : ∀ h, h < auth.length → ∀ left right,
      EqDistTriple r (fun s ↦ Inv s ∧ R h (2 * (idx / 2 ^ (h + 1))) left s ∧
          R h (2 * (idx / 2 ^ (h + 1)) + 1) right s)
        (node₁ (h + 1) (idx / 2 ^ (h + 1)) left right)
        (node₂ (h + 1) (idx / 2 ^ (h + 1)) left right)
        fun y s ↦ Inv s ∧ R (h + 1) (idx / 2 ^ (h + 1)) y s) :
    EqDistTriple r
      (fun s ↦ Inv s ∧ R 0 idx node s ∧
        ∀ j (hj : j < auth.length), R j (sibling (idx / 2 ^ j)) auth[j] s)
      (climbM node₁ idx node auth) (climbM node₂ idx node auth)
      fun y s ↦ Inv s ∧ R auth.length (idx / 2 ^ auth.length) y s := by
  induction auth using List.reverseRecOn with
  | nil => exact EqDistTriple.pure _ fun s hs ↦ ⟨hs.1, by simpa using hs.2.1⟩
  | append_singleton auth a ih =>
    simp only [List.length_append, List.length_singleton] at hnode ⊢
    rw [climbM_concat, climbM_concat]
    refine (((ih fun h hh ↦ hnode h (by omega)).frame
      (F := R auth.length (sibling (idx / 2 ^ auth.length)) a) fun s s' ↦ hR _ _ _ s s').mono
      (fun s hs ↦ ?_) fun _ _ hy ↦ hy).bind fun child ↦ ?_
    · obtain ⟨hInv, hstart, hauth⟩ := hs
      refine ⟨⟨hInv, hstart, fun j hj ↦ ?_⟩, by simpa using hauth auth.length (by omega)⟩
      simpa [List.getElem_append_left hj] using hauth j (by omega)
    have hdiv := div_two_pow_succ (i := idx) (k := auth.length) rfl
    split_ifs with hpar
    · refine (hnode _ (by omega) child a).mono (fun s hs ↦ ⟨hs.1.1, ?_, ?_⟩) fun _ _ hy ↦ hy
      · convert hs.1.2 using 2
        omega
      · convert hs.2 using 2
        simp only [sibling, hpar, ↓reduceIte]
        omega
    · refine (hnode _ (by omega) a child).mono (fun s hs ↦ ⟨hs.1.1, ?_, ?_⟩) fun _ _ hy ↦ hy
      · convert hs.2 using 2
        simp only [sibling, hpar, ↓reduceIte]
        omega
      · convert hs.1.2 using 2
        omega

end PerfectMerkleTree

namespace QueryImpl.EqDistTriple

open OracleComp PerfectMerkleTree

variable {ι : Type} {spec : OracleSpec ι} {σ Y : Type} {so : QueryImpl spec (StateT σ ProbComp)}
  {r : σ → σ → Prop} [IsPreorder σ r] (Inv : σ → Prop) (R : ℕ → ℕ → Y → σ → Prop)
  {leaf₁ leaf₂ : ℕ → OracleComp spec Y} {node₁ node₂ : ℕ → ℕ → Y → Y → OracleComp spec Y}

/-- Roots of the perfect subtree at `(z, t)`, over callbacks on `spec` run under `so`, agree when
the leaf callbacks agree at its leaves and the node callbacks at its internal nodes; the right-hand
root is related to the final state at `(z, t)`. The simulation of a traversal is the traversal of
the simulated callbacks, so this is `PerfectMerkleTree.merkleRootM_eqDistTriple` for those. -/
theorem merkleRootM (hR : ∀ h i y s s', r s s' → R h i y s → R h i y s') (z t : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = t →
      so.EqDistTriple r Inv (leaf₁ i) (leaf₂ i) fun y s ↦ Inv s ∧ R 0 i y s)
    (hnode : ∀ h i, h < z → i / 2 ^ (z - (h + 1)) = t → ∀ left right,
      so.EqDistTriple r (fun s ↦ Inv s ∧ R h (2 * i) left s ∧ R h (2 * i + 1) right s)
        (node₁ (h + 1) i left right) (node₂ (h + 1) i left right)
        fun y s ↦ Inv s ∧ R (h + 1) i y s) :
    so.EqDistTriple r Inv (PerfectMerkleTree.merkleRootM leaf₁ node₁ z t)
      (PerfectMerkleTree.merkleRootM leaf₂ node₂ z t) fun y s ↦ Inv s ∧ R z t y s := by
  have e : ∀ (leaf : ℕ → OracleComp spec Y) (node : ℕ → ℕ → Y → Y → OracleComp spec Y),
      simulateQ so (PerfectMerkleTree.merkleRootM leaf node z t) =
        PerfectMerkleTree.merkleRootM (fun i ↦ simulateQ so (leaf i))
          (fun h i l r ↦ simulateQ so (node h i l r)) z t :=
    fun leaf node ↦ merkleRootM_natural (simulateQ' so) leaf node _ _ (fun _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) z t
  rw [QueryImpl.EqDistTriple, e, e]
  exact merkleRootM_eqDistTriple Inv R hR z t hleaf hnode

/-- Authentication paths of leaf `idx` over `z` levels, over callbacks on `spec` run under `so`,
agree when the callbacks agree at the leaves and internal nodes of the height-`z` subtree
containing `idx`; entry `j` of the right-hand path is related to the final state as the value of
the level-`j` sibling. The simulation of a traversal is the traversal of the simulated callbacks,
so this is `PerfectMerkleTree.intrinsicAuthPathM_eqDistTriple` for those. -/
theorem intrinsicAuthPathM (hR : ∀ h i y s s', r s s' → R h i y s → R h i y s') (idx z : ℕ)
    (hleaf : ∀ i, i / 2 ^ z = idx / 2 ^ z →
      so.EqDistTriple r Inv (leaf₁ i) (leaf₂ i) fun y s ↦ Inv s ∧ R 0 i y s)
    (hnode : ∀ h i, h < z → i / 2 ^ (z - (h + 1)) = idx / 2 ^ z → ∀ left right,
      so.EqDistTriple r (fun s ↦ Inv s ∧ R h (2 * i) left s ∧ R h (2 * i + 1) right s)
        (node₁ (h + 1) i left right) (node₂ (h + 1) i left right)
        fun y s ↦ Inv s ∧ R (h + 1) i y s) :
    so.EqDistTriple r Inv (PerfectMerkleTree.intrinsicAuthPathM leaf₁ node₁ idx z)
      (PerfectMerkleTree.intrinsicAuthPathM leaf₂ node₂ idx z)
      fun path s ↦ Inv s ∧ ∀ j (hj : j < z), R j (sibling (idx / 2 ^ j)) path[j] s := by
  have e : ∀ (leaf : ℕ → OracleComp spec Y) (node : ℕ → ℕ → Y → Y → OracleComp spec Y),
      simulateQ so (PerfectMerkleTree.intrinsicAuthPathM leaf node idx z) =
        PerfectMerkleTree.intrinsicAuthPathM (fun i ↦ simulateQ so (leaf i))
          (fun h i l r ↦ simulateQ so (node h i l r)) idx z :=
    fun leaf node ↦ intrinsicAuthPathM_natural (simulateQ' so) leaf node _ _ (fun _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) idx z
  rw [QueryImpl.EqDistTriple, e, e]
  exact intrinsicAuthPathM_eqDistTriple Inv R hR idx z hleaf hnode

/-- Climbs from leaf `idx`, over node callbacks on `spec` run under `so`, agree when the node
callbacks agree at the ancestors of the leaf and the starting value and path entries are related
to the starting state as the values of the leaf and of its siblings; the right-hand climb is
related to the final state as the value of the ancestor at height `auth.length`. The simulation
of a climb is the climb of the simulated callbacks, so this is
`PerfectMerkleTree.climbM_eqDistTriple` for those. -/
theorem climbM (hR : ∀ h i y s s', r s s' → R h i y s → R h i y s') (idx : ℕ) (node : Y)
    (auth : List Y)
    (hnode : ∀ h, h < auth.length → ∀ left right,
      so.EqDistTriple r (fun s ↦ Inv s ∧ R h (2 * (idx / 2 ^ (h + 1))) left s ∧
          R h (2 * (idx / 2 ^ (h + 1)) + 1) right s)
        (node₁ (h + 1) (idx / 2 ^ (h + 1)) left right)
        (node₂ (h + 1) (idx / 2 ^ (h + 1)) left right)
        fun y s ↦ Inv s ∧ R (h + 1) (idx / 2 ^ (h + 1)) y s) :
    so.EqDistTriple r
      (fun s ↦ Inv s ∧ R 0 idx node s ∧
        ∀ j (hj : j < auth.length), R j (sibling (idx / 2 ^ j)) auth[j] s)
      (PerfectMerkleTree.climbM node₁ idx node auth) (PerfectMerkleTree.climbM node₂ idx node auth)
      fun y s ↦ Inv s ∧ R auth.length (idx / 2 ^ auth.length) y s := by
  have e : ∀ node' : ℕ → ℕ → Y → Y → OracleComp spec Y,
      simulateQ so (PerfectMerkleTree.climbM node' idx node auth) =
        PerfectMerkleTree.climbM (fun h i l r ↦ simulateQ so (node' h i l r)) idx node auth :=
    fun node' ↦ climbM_natural (simulateQ' so) node' _ (fun _ _ _ _ ↦ rfl) idx node auth
  rw [QueryImpl.EqDistTriple, e, e]
  exact climbM_eqDistTriple Inv R hR idx node auth hnode

end QueryImpl.EqDistTriple
