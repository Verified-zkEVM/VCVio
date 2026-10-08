/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.EqDistTriple
public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel

/-!
# Equal-distribution triples through the Merkle and vector combinators

The state is a counter, ordered by `≤`. Both leaf callbacks return the counter and increment it.
The left node callback returns `max left right`; the right one returns `min (max left right) s`
at counter `s`, so the two agree only when both inputs are at most the counter. The relation
`R h i y s := y ≤ s` records exactly that, and is stable as the counter grows. Each combinator is
instantiated with these callbacks; the climb also needs its starting value and path entries
related to the starting counter. Further examples read the postcondition on the left-hand
program through `symm`, and instantiate the same lemmas along the trivial preorder, with no
precondition and no relation. The last sections compose an authentication path, a leaf and a
climb, and relate an honest tree to a labelled tree over a relabelled graph, with the drawn cells
as the node relation.
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

/-- The left-hand root is at most the final counter, through `symm`. -/
example (z t s : ℕ) : ∀ w ∈ support ((merkleRootM leaf₁ node₁ z t).run s), w.1 ≤ w.2 :=
  fun w hw ↦ ((merkleRootM_eqDistTriple _ R R_mono z t (fun i _ ↦ leaf_triple i)
    fun h i _ _ ↦ node_triple h i).symm s trivial).2 w hw |>.2.2

/-- A leaf forms a triple with itself. -/
example (i : ℕ) : EqDistTriple (· ≤ ·) (fun _ ↦ True) (leaf₁ i) (leaf₁ i)
    fun y s ↦ True ∧ R 0 i y s :=
  .of_support fun s _ z hz ↦ by
    simp only [show (leaf₁ i).run s = pure (s, s + 1) from rfl, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨by simp, trivial, by simp [R]⟩

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
  (Vector.ofFnM_eqDistTriple (fun _ ↦ True) (fun (i : Fin k) ↦ R 0 i) (fun i ↦ R_mono 0 i)
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

/-! ## Authentication path into a climb

The postcondition of `intrinsicAuthPathM` relates entry `j` of the path to the state as the
value of the level-`j` sibling of the leaf; after a leaf step, it is the precondition of
`climbM` on the path as a list, so the climb ends at the root of the subtree containing the leaf.
-/

namespace VCVioTest.EqDistTripleCompose

open OracleComp PerfectMerkleTree

variable {σ Y : Type} {r : σ → σ → Prop} [IsPreorder σ r] (Inv : σ → Prop)
  (R : ℕ → ℕ → Y → σ → Prop) {leaf₁ leaf₂ : ℕ → StateT σ ProbComp Y}
  {node₁ node₂ : ℕ → ℕ → Y → Y → StateT σ ProbComp Y}

/-- Path, leaf and climb at one leaf agree, and the right-hand climb ends at the subtree root. -/
theorem authPath_leaf_climb (hR : ∀ h i y s s', r s s' → R h i y s → R h i y s')
    (idx z : ℕ)
    (hleaf : ∀ i, EqDistTriple r Inv (leaf₁ i) (leaf₂ i) fun y s ↦ Inv s ∧ R 0 i y s)
    (hnode : ∀ h i left right,
      EqDistTriple r (fun s ↦ Inv s ∧ R h (2 * i) left s ∧ R h (2 * i + 1) right s)
        (node₁ (h + 1) i left right) (node₂ (h + 1) i left right)
        fun y s ↦ Inv s ∧ R (h + 1) i y s) :
    EqDistTriple r Inv
      (do let path ← intrinsicAuthPathM leaf₁ node₁ idx z
          let l ← leaf₁ idx
          climbM node₁ idx l path.toList)
      (do let path ← intrinsicAuthPathM leaf₂ node₂ idx z
          let l ← leaf₂ idx
          climbM node₂ idx l path.toList)
      fun y s ↦ Inv s ∧ R z (idx / 2 ^ z) y s := by
  refine (intrinsicAuthPathM_eqDistTriple Inv R hR idx z (fun i _ ↦ hleaf i)
    fun h i _ _ ↦ hnode h i).bind fun path ↦ ?_
  refine ((hleaf idx).frame (F := fun s ↦ ∀ j (hj : j < z),
      R j (sibling (idx / 2 ^ j)) path[j] s)
    fun s s' hs hF j hj ↦ hR _ _ _ _ _ hs (hF j hj)).bind fun l ↦ ?_
  have := climbM_eqDistTriple Inv R hR idx l path.toList
    fun h _ left right ↦ hnode h (idx / 2 ^ (h + 1)) left right
  simp only [Vector.length_toList, Vector.getElem_toList] at this
  exact this.mono (fun s hs ↦ ⟨hs.1.1, hs.1.2, hs.2⟩) fun _ _ h ↦ h

end VCVioTest.EqDistTripleCompose

/-! ## Drawn cells of a relabelled graph

A perfect tree over a canonical graph: leaf `i` is the derivation `sec i`, and internal node
`(h + 1, i)` is the graph node `key (h + 1) i`, whose children are the cells of `(h, 2 * i)` and
`(h, 2 * i + 1)`. The honest tree answers each internal node by a public query at the node's
point; the labelled tree reads the node's label. Both run under the eager handler, the honest
callbacks lifted to the label operations. Along the order of relabelling states, with the
relation "the value is the drawn cell", the step triples (`QueryImpl.EqDistTriple`) combine by
`QueryImpl.EqDistTriple.merkleRootM` into a triple of the trees, so the two trees have equal
measures from every state.
-/

namespace VCVioTest.EqDistTripleRelabel

open OracleComp OracleSpec PerfectMerkleTree

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type}
  (G : CanonicalGraph pub X K R) (sec : ℕ → X) (key : ℕ → ℕ → K) (cell : ℕ → ℕ → X ⊕ K)
  (q : ℕ → ℕ → R → R → ι) (hq : ∀ h i l r, pub.Range (q h i l r) = R)

/-- The cells and points of a perfect tree over `G`. -/
structure TreeShape : Prop where
  cell_zero : ∀ i, cell 0 i = .inl (sec i)
  cell_succ : ∀ h i, cell (h + 1) i = .inr (key (h + 1) i)
  ch : ∀ h i, G.ch (key (h + 1) i) = [cell h (2 * i), cell h (2 * i + 1)]
  q_eq : ∀ h i l r, q (h + 1) i l r = G.pt (key (h + 1) i) [l, r]

/-- Honest leaf: the derivation. -/
def honestLeaf (i : ℕ) : OracleComp (pub.withDerivations X R) R :=
  query (spec := pub.withDerivations X R) (.inr (sec i))

/-- Honest node: the public query at the node's point. -/
def honestNode (h i : ℕ) (l r : R) : OracleComp (pub.withDerivations X R) R :=
  cast (hq h i l r) <$> query (spec := pub.withDerivations X R) (.inl (.inr (q h i l r)))

/-- Labelled node: the node's label. -/
def labNode (h i : ℕ) (_ _ : R) : OracleComp (pub.withLabels X K R) R :=
  query (spec := pub.withLabels X K R) (.inr (.inr (key h i)))

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- The value is the drawn cell of `(h, i)`. -/
def Rel (h i : ℕ) (y : R) (st : RelabelState pub X K R) : Prop := st.2 (cell h i) = some y

omit [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)] in
theorem Rel_mono (h i : ℕ) (y : R) (st st' : RelabelState pub X K R) (hle : st ≤ st')
    (hy : Rel cell h i y st) : Rel cell h i y st' := hle.2 hy

/-- From drawn children, the lifted honest node step is the label read. -/
theorem node_triple (hS : TreeShape G sec key cell q) (h i : ℕ) (l r : R) :
    G.eagerImpl.EqDistTriple (· ≤ ·)
      (fun st ↦ True ∧ Rel cell h (2 * i) l st ∧ Rel cell h (2 * i + 1) r st)
      (liftComp (honestNode (X := X) q hq (h + 1) i l r) _) (labNode key (h + 1) i l r)
      fun y st ↦ True ∧ Rel cell (h + 1) i y st := by
  rintro st ⟨-, hl, hr⟩
  have hch : G.childVals st (key (h + 1) i) = some [l, r] :=
    G.childVals_eq_some_iff.2 (hS.ch h i ▸ .cons hl (.cons hr .nil))
  have hlab : (simulateQ G.eagerImpl (labNode key (h + 1) i l r)).run st =
      (RelabelState.drawCell (.inr (key (h + 1) i))).run st := by
    simp only [labNode, simulateQ_HasQuery_query, CanonicalGraph.eagerImpl_apply_inr]
    rfl
  have hhon : (simulateQ G.eagerImpl (liftComp (honestNode (X := X) q hq (h + 1) i l r) _)).run st =
      (RelabelState.drawCell (.inr (key (h + 1) i))).run st := by
    rw [CanonicalGraph.simulateQ_eagerImpl_liftComp, honestNode, simulateQ_map,
      simulateQ_HasQuery_query, StateT.run_map]
    generalize hq (h + 1) i l r = e
    revert e
    rw [hS.q_eq h i l r]
    intro e
    rw [G.relabelImpl_run_pt hch, Functor.map_map]
    conv_rhs => rw [← id_map ((RelabelState.drawCell (.inr (key (h + 1) i))).run st)]
    congr 1
    funext z
    simp only [Prod.map_fst, Prod.map_snd, id_eq, cast_cast, cast_eq]
  refine ⟨fun {_} ↦ by rw [hhon, hlab], fun z hz ↦ ?_⟩
  rw [hlab] at hz
  obtain ⟨hle, hc⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell hz
  exact ⟨hle, trivial, by rw [Rel, hS.cell_succ]; exact hc⟩

/-- The lifted derivation leaf draws its cell. -/
theorem leaf_triple (hS : TreeShape G sec key cell q) (i : ℕ) :
    G.eagerImpl.EqDistTriple (· ≤ ·) (fun _ ↦ True)
      (liftComp (honestLeaf (pub := pub) (R := R) sec i) _)
      (liftComp (honestLeaf (pub := pub) (R := R) sec i) _)
      fun y st ↦ True ∧ Rel cell 0 i y st := by
  refine .of_support fun st _ z hz ↦ ?_
  simp only [CanonicalGraph.simulateQ_eagerImpl_liftComp, honestLeaf, simulateQ_HasQuery_query,
    CanonicalGraph.relabelImpl_apply_inr] at hz
  obtain ⟨hle, hc⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell hz
  exact ⟨hle, trivial, by rw [Rel, hS.cell_zero]; exact hc⟩

/-- The honest tree over the lifted callbacks and the labelled tree are related under the eager
handler, and the right-hand root is the drawn cell of `(z, t)`. -/
theorem tree_triple (hS : TreeShape G sec key cell q) (z t : ℕ) :
    G.eagerImpl.EqDistTriple (· ≤ ·) (fun _ ↦ True)
      (merkleRootM (fun i ↦ liftComp (honestLeaf (pub := pub) (R := R) sec i) _)
        (fun h i l r ↦ liftComp (honestNode (X := X) q hq h i l r) _) z t)
      (merkleRootM (fun i ↦ liftComp (honestLeaf (pub := pub) (R := R) sec i) _) (labNode key)
        z t)
      fun y st ↦ True ∧ Rel cell z t y st :=
  .merkleRootM (fun _ ↦ True) (Rel cell) (Rel_mono cell) z t
    (fun i _ ↦ leaf_triple G sec key cell q hS i)
    fun h i _ _ l r ↦ node_triple G sec key cell q hq hS h i l r

/-- The honest root and the labelled root have equal measures under the eager handler. -/
example (hS : TreeShape G sec key cell q) (z t : ℕ) (st : RelabelState pub X K R)
    [MeasurableSpace (R × RelabelState pub X K R)] :
    𝒟[(simulateQ G.eagerImpl
        (merkleRootM (fun i ↦ liftComp (honestLeaf (pub := pub) (R := R) sec i) _)
          (fun h i l r ↦ liftComp (honestNode (X := X) q hq h i l r) _) z t)).run st] =
      𝒟[(simulateQ G.eagerImpl
        (merkleRootM (fun i ↦ liftComp (honestLeaf (pub := pub) (R := R) sec i) _) (labNode key)
          z t)).run st] :=
  (tree_triple G sec key cell q hq hS z t).evalDist_run_eq trivial

/-- After any program over the labels, the honest and labelled roots still have equal measures:
the eager handler only grows the state, so the program is related to itself
(`QueryImpl.EqDistTriple.refl_of_step`), and `bind` sequences it with the trees. -/
example (hS : TreeShape G sec key cell q) {α : Type} (oa : OracleComp (pub.withLabels X K R) α)
    (z t : ℕ) (st : RelabelState pub X K R) [MeasurableSpace (R × RelabelState pub X K R)] :
    𝒟[(simulateQ G.eagerImpl (oa >>= fun _ ↦
        merkleRootM (fun i ↦ liftComp (honestLeaf (pub := pub) (R := R) sec i) _)
          (fun h i l r ↦ liftComp (honestNode (X := X) q hq h i l r) _) z t)).run st] =
      𝒟[(simulateQ G.eagerImpl (oa >>= fun _ ↦
        merkleRootM (fun i ↦ liftComp (honestLeaf (pub := pub) (R := R) sec i) _) (labNode key)
          z t)).run st] :=
  ((QueryImpl.EqDistTriple.refl_of_step (P := fun _ ↦ True)
    (fun _ _ _ ↦ G.le_of_mem_support_eagerImpl) oa).bind
    fun _ ↦ tree_triple G sec key cell q hq hS z t).evalDist_run_eq trivial

end VCVioTest.EqDistTripleRelabel
