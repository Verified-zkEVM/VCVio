/-
Copyright (c) 2026 IAOM / Equation Capital dba Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abraxas1010 (IAOM / Apoth3osis)
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.ToSingle
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Uniqueness

/-!
# Batch Opening Uniqueness

The batch analogue of `VCVio.CryptoFoundations.MerkleTree.Inductive.Uniqueness`: any two batch
openings for the *same* selector that produce the same putative root must agree on the claimed
values of every selected leaf and on the entire (pruned) authentication data, provided the hash is
injective on the node-hash inputs the two openings induce. The Merkle root uniquely determines the
committed values at all opened positions simultaneously.

`batchOpeningHashQueries` lists the ordered child pairs hashed while recomputing the root of one
batch opening. As a set, it is the union over the selected leaves of the single-opening
transcripts `openingHashQueries` of the extracted single openings `batchToSingleProof`
(`mem_batchOpeningHashQueries_iff`): pruning removes duplicated and derivable authentication
data, not hash evaluations. `getPutativeBatchRootWithHash_unique_of_queryInjectiveOn` assumes
injectivity only on a finite log covering both transcripts (`HashInjectiveOnQueries`), which a
compressing hash can satisfy and which a random-oracle or collision-resistance argument can
discharge. The statements under global `Function.Injective2` are the special case where the log
is the union of both transcripts. For binding with no assumption on the hash, see the constructive
collision results in `Binding.lean` and the cross-selector `getPutativeBatchRootWithHash_binding`
in `ToSingle.lean`, which return a collision as data.

Two points specific to the batch setting:

* Cross-shape disagreements are impossible by typing plus inhabitation: a `pruneRight`
  opening cannot be confused with an `internalBoth` opening of the same selector, because
  the latter carries a `BatchProof` for a subtree that the former's hypothesis says has no
  selected leaves, and `BatchProof` is uninhabited on such selectors
  (`BatchProof.anySelected_of_batchProof`).
* The claimed-value tuples also agree on their (vacuous) components at pruned subtrees,
  since `SelectedValues` degenerates to a subsingleton there
  (`selectedValues_eq_of_not_anySelected`).

## Main results

- `batchOpeningHashQueries`, `BatchOpeningHashCovered` — the node-hash inputs of one batch
  opening and their coverage by a query log
- `mem_batchOpeningHashQueries_iff` — the batch transcript is the union of the transcripts of the
  single openings extracted at the selected leaves
- `getPutativeBatchRootWithHash_unique_of_queryInjectiveOn` — batch opening uniqueness under
  injectivity on a covering query log
- `getPutativeBatchRootWithHash_unique` — batch opening uniqueness under a globally injective hash
- `getPutativeBatchRootWithHash_batch_roots_ne_of_ne` — contrapositive: distinct claimed
  values at the same selector produce distinct roots
-/

@[expose] public section

namespace InductiveMerkleTree

open BinaryTree

variable {α : Type _}

/-- Over a selector with no selected leaves, the type of claimed values is degenerate: any
two values tuples are equal (every component is a `PUnit`). -/
theorem selectedValues_eq_of_not_anySelected {s : Skeleton} {sel : LeafData Bool s}
    (h : sel.anySelected = false) (v₁ v₂ : SelectedValues α sel) : v₁ = v₂ := by
  induction sel with
  | leaf b =>
    cases b with
    | false => rfl
    | true => simp [LeafData.anySelected] at h
  | internal l r ihl ihr =>
    simp only [LeafData.anySelected, Bool.or_eq_false_iff] at h
    exact Prod.ext (ihl h.1 v₁.1 v₂.1) (ihr h.2 v₁.2 v₂.2)

/-! ## Queried node-hash inputs -/

/-- The ordered child pairs hashed while recomputing the putative root of one batch opening,
listed in pre-order: the pair hashed at a node precedes the pairs hashed in its left subtree,
which precede those in its right subtree. -/
def batchOpeningHashQueries (hashFn : α → α → α) :
    {s : Skeleton} → {sel : LeafData Bool s} → SelectedValues α sel → BatchProof α sel →
      List (α × α)
  | _, _, _, .leaf => []
  | _, _, v, .internalBoth pl pr =>
    (getPutativeBatchRootWithHash hashFn v.1 pl, getPutativeBatchRootWithHash hashFn v.2 pr) ::
      (batchOpeningHashQueries hashFn v.1 pl ++ batchOpeningHashQueries hashFn v.2 pr)
  | _, _, v, .pruneRight _ rightRoot pl =>
    (getPutativeBatchRootWithHash hashFn v.1 pl, rightRoot) ::
      batchOpeningHashQueries hashFn v.1 pl
  | _, _, v, .pruneLeft _ leftRoot pr =>
    (leftRoot, getPutativeBatchRootWithHash hashFn v.2 pr) ::
      batchOpeningHashQueries hashFn v.2 pr

/-- Every node-hash input induced by a batch opening occurs in `log`. -/
def BatchOpeningHashCovered (hashFn : α → α → α) (log : List (α × α)) {s : Skeleton}
    {sel : LeafData Bool s} (v : SelectedValues α sel) (p : BatchProof α sel) : Prop :=
  ∀ q ∈ batchOpeningHashQueries hashFn v p, q ∈ log

/-- A batch proof selects some leaf. -/
theorem BatchProof.exists_get_eq_true {s : Skeleton} {sel : LeafData Bool s}
    (p : BatchProof α sel) : ∃ idx : SkeletonLeafIndex s, sel.get idx = true := by
  induction p with
  | leaf => exact ⟨.ofLeaf, rfl⟩
  | internalBoth pl pr ihl ihr =>
    obtain ⟨idx, hidx⟩ := ihl
    exact ⟨.ofLeft idx, by simpa using hidx⟩
  | pruneRight hr rightRoot pl ih =>
    obtain ⟨idx, hidx⟩ := ih
    exact ⟨.ofLeft idx, by simpa using hidx⟩
  | pruneLeft hl leftRoot pr ih =>
    obtain ⟨idx, hidx⟩ := ih
    exact ⟨.ofRight idx, by simpa using hidx⟩

/-- Every pair queried by the single opening extracted at a selected leaf is queried by the batch
opening. -/
theorem mem_batchOpeningHashQueries_of_mem_openingHashQueries (hashFn : α → α → α)
    {s : Skeleton} {sel : LeafData Bool s} (v : SelectedValues α sel) (p : BatchProof α sel)
    (idx : SkeletonLeafIndex s) (hidx : sel.get idx = true) {q : α × α}
    (hq : q ∈ openingHashQueries hashFn idx (selectedValueAt v idx hidx)
      (batchToSingleProof hashFn v p idx hidx)) :
    q ∈ batchOpeningHashQueries hashFn v p := by
  induction p with
  | leaf =>
    cases idx with
    | ofLeaf => simp [openingHashQueries] at hq
  | internalBoth pl pr ihl ihr =>
    cases idx with
    | ofLeft idxL =>
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.head_cons,
        List.Vector.tail_cons, getPutativeRootWithHash_batchToSingleProof,
        List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihl v.1 idxL _ hq))
    | ofRight idxR =>
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.head_cons,
        List.Vector.tail_cons, getPutativeRootWithHash_batchToSingleProof,
        List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihr v.2 idxR _ hq))
  | pruneRight hr rightRoot pl ih =>
    cases idx with
    | ofLeft idxL =>
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.head_cons,
        List.Vector.tail_cons, getPutativeRootWithHash_batchToSingleProof,
        List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih v.1 idxL _ hq)
    | ofRight idxR =>
      exact absurd (LeafData.anySelected_of_get idxR (by simpa using hidx)) (by simp [hr])
  | pruneLeft hl leftRoot pr ih =>
    cases idx with
    | ofRight idxR =>
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.head_cons,
        List.Vector.tail_cons, getPutativeRootWithHash_batchToSingleProof,
        List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih v.2 idxR _ hq)
    | ofLeft idxL =>
      exact absurd (LeafData.anySelected_of_get idxL (by simpa using hidx)) (by simp [hl])

/-- Every pair queried by a batch opening is queried by the single opening extracted at some
selected leaf. -/
theorem exists_mem_openingHashQueries_of_mem_batchOpeningHashQueries (hashFn : α → α → α)
    {s : Skeleton} {sel : LeafData Bool s} (v : SelectedValues α sel) (p : BatchProof α sel)
    {q : α × α} (hq : q ∈ batchOpeningHashQueries hashFn v p) :
    ∃ (idx : SkeletonLeafIndex s) (hidx : sel.get idx = true),
      q ∈ openingHashQueries hashFn idx (selectedValueAt v idx hidx)
        (batchToSingleProof hashFn v p idx hidx) := by
  induction p with
  | leaf => simp [batchOpeningHashQueries] at hq
  | internalBoth pl pr ihl ihr =>
    simp only [batchOpeningHashQueries, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · obtain ⟨idx, hidx⟩ := pl.exists_get_eq_true
      refine ⟨.ofLeft idx, by simpa using hidx, ?_⟩
      simp [openingHashQueries, batchToSingleProof, selectedValueAt,
        getPutativeRootWithHash_batchToSingleProof]
    · obtain ⟨idx, hidx, hq⟩ := ihl v.1 hq
      refine ⟨.ofLeft idx, by simpa using hidx, ?_⟩
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.tail_cons,
        List.mem_cons]
      exact Or.inr hq
    · obtain ⟨idx, hidx, hq⟩ := ihr v.2 hq
      refine ⟨.ofRight idx, by simpa using hidx, ?_⟩
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.tail_cons,
        List.mem_cons]
      exact Or.inr hq
  | pruneRight hr rightRoot pl ih =>
    simp only [batchOpeningHashQueries, List.mem_cons] at hq
    rcases hq with rfl | hq
    · obtain ⟨idx, hidx⟩ := pl.exists_get_eq_true
      refine ⟨.ofLeft idx, by simpa using hidx, ?_⟩
      simp [openingHashQueries, batchToSingleProof, selectedValueAt,
        getPutativeRootWithHash_batchToSingleProof]
    · obtain ⟨idx, hidx, hq⟩ := ih v.1 hq
      refine ⟨.ofLeft idx, by simpa using hidx, ?_⟩
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.tail_cons,
        List.mem_cons]
      exact Or.inr hq
  | pruneLeft hl leftRoot pr ih =>
    simp only [batchOpeningHashQueries, List.mem_cons] at hq
    rcases hq with rfl | hq
    · obtain ⟨idx, hidx⟩ := pr.exists_get_eq_true
      refine ⟨.ofRight idx, by simpa using hidx, ?_⟩
      simp [openingHashQueries, batchToSingleProof, selectedValueAt,
        getPutativeRootWithHash_batchToSingleProof]
    · obtain ⟨idx, hidx, hq⟩ := ih v.2 hq
      refine ⟨.ofRight idx, by simpa using hidx, ?_⟩
      simp only [openingHashQueries, batchToSingleProof, selectedValueAt, List.Vector.tail_cons,
        List.mem_cons]
      exact Or.inr hq

/-- **The batch transcript is the union of the single-opening transcripts.** A pair is queried by
a batch opening exactly when it is queried by the single opening `batchToSingleProof` extracted at
some selected leaf. -/
theorem mem_batchOpeningHashQueries_iff (hashFn : α → α → α)
    {s : Skeleton} {sel : LeafData Bool s} (v : SelectedValues α sel) (p : BatchProof α sel)
    (q : α × α) :
    q ∈ batchOpeningHashQueries hashFn v p ↔
      ∃ (idx : SkeletonLeafIndex s) (hidx : sel.get idx = true),
        q ∈ openingHashQueries hashFn idx (selectedValueAt v idx hidx)
          (batchToSingleProof hashFn v p idx hidx) :=
  ⟨exists_mem_openingHashQueries_of_mem_batchOpeningHashQueries hashFn v p,
    fun ⟨idx, hidx, hq⟩ => mem_batchOpeningHashQueries_of_mem_openingHashQueries hashFn v p idx
      hidx hq⟩

/-- A batch opening is covered by a log exactly when every single opening extracted at a selected
leaf is covered by it. -/
theorem batchOpeningHashCovered_iff (hashFn : α → α → α) (log : List (α × α))
    {s : Skeleton} {sel : LeafData Bool s} (v : SelectedValues α sel) (p : BatchProof α sel) :
    BatchOpeningHashCovered hashFn log v p ↔
      ∀ (idx : SkeletonLeafIndex s) (hidx : sel.get idx = true),
        OpeningHashCovered hashFn log idx (selectedValueAt v idx hidx)
          (batchToSingleProof hashFn v p idx hidx) := by
  simp only [BatchOpeningHashCovered, OpeningHashCovered, mem_batchOpeningHashQueries_iff]
  exact ⟨fun h idx hidx q hq => h q ⟨idx, hidx, hq⟩,
    fun h q ⟨idx, hidx, hq⟩ => h idx hidx q hq⟩

/-! ## Uniqueness -/

/-- **Queried-domain batch opening uniqueness.** If two batch openings for the same selector are
covered by one transcript on which `hashFn` is injective, equality of their putative roots forces
equality of both the claimed selected values and the pruned authentication data. -/
theorem getPutativeBatchRootWithHash_unique_of_queryInjectiveOn
    (hashFn : α → α → α) (log : List (α × α)) (hinj : HashInjectiveOnQueries hashFn log)
    {s : Skeleton} {sel : LeafData Bool s}
    (v₁ v₂ : SelectedValues α sel) (p₁ p₂ : BatchProof α sel)
    (hcovered₁ : BatchOpeningHashCovered hashFn log v₁ p₁)
    (hcovered₂ : BatchOpeningHashCovered hashFn log v₂ p₂)
    (heq : getPutativeBatchRootWithHash hashFn v₁ p₁
         = getPutativeBatchRootWithHash hashFn v₂ p₂) :
    v₁ = v₂ ∧ p₁ = p₂ := by
  induction p₁ with
  | leaf =>
    cases p₂ with
    | leaf => exact ⟨heq, rfl⟩
  | internalBoth pl₁ pr₁ ihl ihr =>
    cases p₂ with
    | internalBoth pl₂ pr₂ =>
      simp only [BatchOpeningHashCovered, batchOpeningHashQueries, List.mem_cons,
        List.mem_append, forall_eq_or_imp] at hcovered₁ hcovered₂
      simp only [getPutativeBatchRootWithHash] at heq
      obtain ⟨hL, hR⟩ := Prod.mk.inj (hinj _ hcovered₁.1 _ hcovered₂.1 heq)
      obtain ⟨hvl, hpl⟩ := ihl v₁.1 v₂.1 pl₂ (fun q hq => hcovered₁.2 q (Or.inl hq))
        (fun q hq => hcovered₂.2 q (Or.inl hq)) hL
      obtain ⟨hvr, hpr⟩ := ihr v₁.2 v₂.2 pr₂ (fun q hq => hcovered₁.2 q (Or.inr hq))
        (fun q hq => hcovered₂.2 q (Or.inr hq)) hR
      exact ⟨Prod.ext hvl hvr, by rw [hpl, hpr]⟩
    | pruneRight hr₂ rightRoot₂ pl₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pr₁) (by simp [hr₂])
    | pruneLeft hl₂ leftRoot₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pl₁) (by simp [hl₂])
  | pruneRight hr₁ rightRoot₁ pl₁ ih =>
    cases p₂ with
    | internalBoth pl₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pr₂) (by simp [hr₁])
    | pruneRight hr₂ rightRoot₂ pl₂ =>
      simp only [BatchOpeningHashCovered, batchOpeningHashQueries, List.mem_cons,
        forall_eq_or_imp] at hcovered₁ hcovered₂
      simp only [getPutativeBatchRootWithHash] at heq
      obtain ⟨hL, hRoot⟩ := Prod.mk.inj (hinj _ hcovered₁.1 _ hcovered₂.1 heq)
      obtain ⟨hvl, hpl⟩ := ih v₁.1 v₂.1 pl₂ hcovered₁.2 hcovered₂.2 hL
      refine ⟨Prod.ext hvl (selectedValues_eq_of_not_anySelected hr₁ v₁.2 v₂.2), ?_⟩
      rw [hpl, hRoot]
    | pruneLeft hl₂ leftRoot₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pr₂) (by simp [hr₁])
  | pruneLeft hl₁ leftRoot₁ pr₁ ih =>
    cases p₂ with
    | internalBoth pl₂ pr₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pl₂) (by simp [hl₁])
    | pruneRight hr₂ rightRoot₂ pl₂ =>
      exact absurd (BatchProof.anySelected_of_batchProof pl₂) (by simp [hl₁])
    | pruneLeft hl₂ leftRoot₂ pr₂ =>
      simp only [BatchOpeningHashCovered, batchOpeningHashQueries, List.mem_cons,
        forall_eq_or_imp] at hcovered₁ hcovered₂
      simp only [getPutativeBatchRootWithHash] at heq
      obtain ⟨hRoot, hR⟩ := Prod.mk.inj (hinj _ hcovered₁.1 _ hcovered₂.1 heq)
      obtain ⟨hvr, hpr⟩ := ih v₁.2 v₂.2 pr₂ hcovered₁.2 hcovered₂.2 hR
      refine ⟨Prod.ext (selectedValues_eq_of_not_anySelected hl₁ v₁.1 v₂.1) hvr, ?_⟩
      rw [hpr, hRoot]

/-- **Batch opening uniqueness under a globally injective hash.** When `hashFn` is injective, two
batch openings for the same selector that produce the same putative root must agree on both the
claimed selected values and the entire pruned authentication data.

This is the special case of `getPutativeBatchRootWithHash_unique_of_queryInjectiveOn` whose log is
the union of the two openings' transcripts. -/
theorem getPutativeBatchRootWithHash_unique
    (hashFn : α → α → α) (hinj : Function.Injective2 hashFn)
    {s : Skeleton} {sel : LeafData Bool s}
    (v₁ v₂ : SelectedValues α sel) (p₁ p₂ : BatchProof α sel)
    (heq : getPutativeBatchRootWithHash hashFn v₁ p₁
         = getPutativeBatchRootWithHash hashFn v₂ p₂) :
    v₁ = v₂ ∧ p₁ = p₂ :=
  getPutativeBatchRootWithHash_unique_of_queryInjectiveOn hashFn
    (batchOpeningHashQueries hashFn v₁ p₁ ++ batchOpeningHashQueries hashFn v₂ p₂)
    (HashInjectiveOnQueries.of_injective2 hinj _) v₁ v₂ p₁ p₂
    (fun _ hq => List.mem_append_left _ hq) (fun _ hq => List.mem_append_right _ hq) heq

/-- Contrapositive of batch uniqueness: with an injective hash, distinct claimed value
tuples for the same selector always produce distinct putative roots, regardless of the
authentication data used. -/
theorem getPutativeBatchRootWithHash_batch_roots_ne_of_ne
    (hashFn : α → α → α) (hinj : Function.Injective2 hashFn)
    {s : Skeleton} {sel : LeafData Bool s}
    (v₁ v₂ : SelectedValues α sel) (p₁ p₂ : BatchProof α sel) (hne : v₁ ≠ v₂) :
    getPutativeBatchRootWithHash hashFn v₁ p₁
      ≠ getPutativeBatchRootWithHash hashFn v₂ p₂ :=
  fun heq => hne (getPutativeBatchRootWithHash_unique hashFn hinj v₁ v₂ p₁ p₂ heq).1

end InductiveMerkleTree
