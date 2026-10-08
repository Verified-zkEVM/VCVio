/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.EqDistTriple

/-!
# Equal-distribution triples through the Merkle and vector combinators

The state is a counter, ordered by `≤`. Both leaf callbacks return the counter and increment it.
The left node callback returns `max left right`; the right one returns `min (max left right) s`
at counter `s`, so the two agree only when both inputs are at most the counter. The relation
`R h i y s := y ≤ s` records exactly that, and is stable as the counter grows. Each combinator is
instantiated with these callbacks; the climb also needs its starting value and path entries
related to the starting counter. The last examples instantiate the same lemmas along the trivial
preorder, with no precondition and no relation.
-/

public section

namespace VCVioTest.EqDistTripleToy

open OracleComp OracleSpec PerfectMerkleTree

/-- Return the counter and increment it. -/
def leaf₁ (_ : ℕ) : StateT ℕ ProbComp ℕ := modifyGet fun s ↦ (s, s + 1)

/-- Return the counter and increment it, through `get` and `set`. -/
def leaf₂ (_ : ℕ) : StateT ℕ ProbComp ℕ := do
  let s ← get
  set (s + 1)
  return s

/-- The larger input. -/
def node₁ (_ _ left right : ℕ) : StateT ℕ ProbComp ℕ := pure (max left right)

/-- The larger input, capped by the counter. -/
def node₂ (_ _ left right : ℕ) : StateT ℕ ProbComp ℕ := do
  let s ← get
  return min (max left right) s

/-- A value at most the counter. -/
def R (_ _ y s : ℕ) : Prop := y ≤ s

theorem R_mono (h i y s s' : ℕ) (hs : s ≤ s') (hy : R h i y s) : R h i y s' :=
  le_trans hy hs

theorem leaf_triple (i : ℕ) : EqDistTriple (· ≤ ·) (fun _ ↦ True) (leaf₁ i) (leaf₂ i)
    fun y s ↦ True ∧ R 0 i y s := by
  intro s _
  have h₁ : (leaf₁ i).run s = pure (s, s + 1) := rfl
  have h₂ : (leaf₂ i).run s = pure (s, s + 1) := by simp [leaf₂]
  refine ⟨fun {_} ↦ by rw [h₁, h₂], fun z hz ↦ ?_⟩
  simp only [h₂, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨by simp, trivial, by simp [R]⟩

theorem node_triple (h i left right : ℕ) :
    EqDistTriple (· ≤ ·)
      (fun s ↦ True ∧ R h (2 * i) left s ∧ R h (2 * i + 1) right s)
      (node₁ (h + 1) i left right) (node₂ (h + 1) i left right)
      fun y s ↦ True ∧ R (h + 1) i y s := by
  intro s ⟨_, hl, hr⟩
  have h₂ : (node₂ (h + 1) i left right).run s = pure (max left right, s) := by
    simp [node₂, min_eq_left (max_le hl hr)]
  refine ⟨fun {_} ↦ by rw [h₂]; rfl, fun z hz ↦ ?_⟩
  simp only [h₂, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨le_rfl, trivial, max_le hl hr⟩

example (z t s : ℕ) :
    𝒟[(merkleRootM leaf₁ node₁ z t).run s] = 𝒟[(merkleRootM leaf₂ node₂ z t).run s] :=
  (merkleRootM_eqDistTriple _ R R_mono z t (fun i _ ↦ leaf_triple i)
    fun h i _ _ ↦ node_triple h i).evalDist_run_eq trivial

/-- The right-hand root is at most the final counter. -/
example (z t s : ℕ) : ∀ w ∈ support ((merkleRootM leaf₂ node₂ z t).run s), w.1 ≤ w.2 :=
  fun w hw ↦ ((merkleRootM_eqDistTriple _ R R_mono z t (fun i _ ↦ leaf_triple i)
    fun h i _ _ ↦ node_triple h i) s trivial).2 w hw |>.2.2

example (idx z s : ℕ) [MeasurableSpace (Vector ℕ z × ℕ)] :
    𝒟[(intrinsicAuthPathM leaf₁ node₁ idx z).run s] =
      𝒟[(intrinsicAuthPathM leaf₂ node₂ idx z).run s] :=
  (intrinsicAuthPathM_eqDistTriple _ R R_mono idx z (fun i _ ↦ leaf_triple i)
    fun h i _ _ ↦ node_triple h i).evalDist_run_eq trivial

/-- A climb from inputs at most the counter. -/
example (idx node s : ℕ) (auth : List ℕ) (hnode : node ≤ s) (hauth : ∀ a ∈ auth, a ≤ s) :
    𝒟[(climbM node₁ idx node auth).run s] = 𝒟[(climbM node₂ idx node auth).run s] :=
  (climbM_eqDistTriple _ R R_mono idx node auth fun h _ ↦ node_triple h _).evalDist_run_eq
    ⟨trivial, hnode, fun _ hj ↦ hauth _ (List.getElem_mem hj)⟩

example (k s : ℕ) [MeasurableSpace (Vector ℕ k × ℕ)] :
    𝒟[(Vector.ofFnM (n := k) fun i ↦ leaf₁ i).run s] =
      𝒟[(Vector.ofFnM (n := k) fun i ↦ leaf₂ i).run s] :=
  (eqDistTriple_ofFnM (fun _ ↦ True) (fun (i : Fin k) ↦ R 0 i) (fun i ↦ R_mono 0 i)
    fun i ↦ leaf_triple i).evalDist_run_eq trivial

/-! ## Along the trivial preorder -/

/-- The larger input, after reading the counter. -/
def node₃ (_ _ left right : ℕ) : StateT ℕ ProbComp ℕ := do
  let _ ← get
  return max left right

theorem leaf_triple_top (i : ℕ) :
    EqDistTriple ⊤ (fun _ ↦ True) (leaf₁ i) (leaf₂ i) fun _ _ ↦ True ∧ True :=
  .of_evalDist_run_eq (fun _ _ ↦ (leaf_triple i).evalDist_run_eq trivial)
    fun _ _ ↦ ⟨trivial, trivial⟩

theorem node_triple_top (h i left right : ℕ) :
    EqDistTriple ⊤ (fun _ ↦ True ∧ True ∧ True) (node₁ h i left right) (node₃ h i left right)
      fun _ _ ↦ True ∧ True :=
  .of_evalDist_run_eq (fun s _ ↦ by simp [node₁, node₃]) fun _ _ ↦ ⟨trivial, trivial⟩

/-- Callbacks with equal measures from every state give roots with equal measures from every
state. -/
example (z t s : ℕ) :
    𝒟[(merkleRootM leaf₁ node₁ z t).run s] = 𝒟[(merkleRootM leaf₂ node₃ z t).run s] :=
  (merkleRootM_eqDistTriple (r := ⊤) (fun _ ↦ True) (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ _ _ _ ↦ trivial) z t (fun i _ ↦ leaf_triple_top i)
    fun h i _ _ ↦ node_triple_top (h + 1) i).evalDist_run_eq trivial

/-! ## From oracle programs -/

/-- A Merkle program over an oracle, run under a stateful handler, is the same combinator over
the handled callbacks, to which the lemmas above apply. -/
example {ι σ Y : Type} {spec : OracleSpec ι} (so : QueryImpl spec (StateT σ ProbComp))
    (leaf : ℕ → OracleComp spec Y) (node : ℕ → ℕ → Y → Y → OracleComp spec Y) (z t : ℕ) :
    simulateQ so (merkleRootM leaf node z t) =
      merkleRootM (fun i ↦ simulateQ so (leaf i)) (fun h i l r ↦ simulateQ so (node h i l r))
        z t :=
  merkleRootM_natural (simulateQ' so) _ _ _ _ (fun _ ↦ rfl) (fun _ _ _ _ ↦ rfl) z t

end VCVioTest.EqDistTripleToy
