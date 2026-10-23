/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Extract
public import VCVio.CryptoFoundations.MerkleTree.Recovery

/-!
# Stability of salted Merkle extraction

Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Lemma 8.6: fresh insertion can change extraction only
when its answer is the root or a component of a supported node input. The shared decoded-input
count bounds this set by two labels per supported input. All stability statements allow collisions.
-/

public section

open Quantum BinaryTree MerkleTreeHashing MerkleTreeExtractor
universe uX uY uM uS
namespace SaltedMerkle
variable {X : Type uX} {Y : Type uY} {Msg : Type uM} {Salt : Type uS}

/-- Components of supported node inputs, as in Definition 8.5. -/
@[expose]
def halfPreimages (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (D : Database X Y) : Set Y :=
  MerkleTreeExtractor.halfPreimages
    (RoleDecoder.ofInjective (enc.node ()) (enc.node_injective ())).decode D

variable (enc : QueryEncoding X Unit Unit (Msg × Salt) Y)

/-- The left component of a supported node input belongs to the half-preimage set. -/
theorem fst_mem_halfPreimages {D : Database X Y} {c : Y × Y} (h : D (enc.node () c) ≠ none) :
    c.1 ∈ halfPreimages enc D :=
  ⟨enc.node () c, c, h, RoleDecoder.decode_encode _ c, Or.inl rfl⟩

/-- The right component of a supported node input belongs to the half-preimage set. -/
theorem snd_mem_halfPreimages {D : Database X Y} {c : Y × Y} (h : D (enc.node () c) ≠ none) :
    c.2 ∈ halfPreimages enc D :=
  ⟨enc.node () c, c, h, RoleDecoder.decode_encode _ c, Or.inr rfl⟩

/-- At most two half-preimages occur per supported oracle input. -/
theorem ncard_halfPreimages_le (D : Database X Y) (hD : {x | D x ≠ none}.Finite) :
    (halfPreimages enc D).ncard ≤ 2 * {x | D x ≠ none}.ncard :=
  MerkleTreeExtractor.ncard_halfPreimages_le _ D hD

/-- Every table over a finite oracle domain satisfies the half-preimage bound. -/
theorem ncard_halfPreimages_le_of_finite [Finite X] (D : Database X Y) :
    (halfPreimages enc D).ncard ≤ 2 * {x | D x ≠ none}.ncard :=
  ncard_halfPreimages_le enc D (Set.toFinite _)

section Extract
variable [LinearOrder Y] [Fintype Y]

/-- A resolved node pair contributes both its components to the half-preimage set. -/
theorem resolvePair_mem_halfPreimages {D : Database X Y} {u : Y} {c : Y × Y}
    (h : resolvePair (enc.node ()) D u = some c) :
    c.1 ∈ halfPreimages enc D ∧ c.2 ∈ halfPreimages enc D := by
  have hd : D (enc.node () c) ≠ none := by simp [resolvePair_spec h]
  exact ⟨fst_mem_halfPreimages enc hd, snd_mem_halfPreimages enc hd⟩

/-- Every reached typed node has the root label or a supported node-input component. -/
theorem extractedLabel_mem (D : Database X Y) (rt : Y) (d : ℕ)
    (i : SkeletonNodeIndex (Skeleton.perfect d)) {u : Y}
    (h : (treeWith (fun _ : Unit => resolvePair (enc.node ()) D) (Skeleton.perfect d)
      (fun _ => ()) rt).get i = some u) : u ∈ insert rt (halfPreimages enc D) := by
  exact treeWith_get_mem _ _
    (fun _ _ _ _ hc => (resolvePair_mem_halfPreimages enc hc).imp
      (Set.mem_insert_of_mem rt) (Set.mem_insert_of_mem rt)) _ _ _ (Set.mem_insert _ _) i h

variable [DecidableEq X] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  {D : Database X Y} {x : X} {y : Y}

/-- Fresh insertion outside the reached-label set leaves the complete extracted value unchanged. -/
theorem extract_eq_of_not_mem {d : ℕ} {rt : Y} (hx : D x = none)
    (hy : y ∉ insert rt (halfPreimages enc D)) :
    extract enc d rt (Function.update D x (some y)) = extract enc d rt D := by
  have ht : treeWith (fun _ : Unit => resolvePair (enc.node ()) (Function.update D x (some y)))
      (Skeleton.perfect d) (fun _ => ()) rt =
      treeWith (fun _ : Unit => resolvePair (enc.node ()) D) (Skeleton.perfect d)
        (fun _ => ()) rt := by
    apply treeWith_eq_of_eqOn _ _ (insert rt (halfPreimages enc D))
    · intro address u hu c hc
      exact (resolvePair_mem_halfPreimages enc hc).imp
        (Set.mem_insert_of_mem rt) (Set.mem_insert_of_mem rt)
    · intro address u hu
      exact resolvePair_update (enc.node ()) hx (fun h => hy (h ▸ hu))
    · exact Set.mem_insert _ _
  have hl : ∀ i, extLeaf enc d rt (Function.update D x (some y)) i = extLeaf enc d rt D i := by
    intro i
    rw [extLeaf, ht, extLeaf]
    unfold recoverLeaf
    exact Option.bind_congr fun u hu =>
      resolvePair_update (enc.leaf ()) hx (fun h => hy (h ▸ extractedLabel_mem enc D rt d _ hu))
  simp only [extract, ht, hl]

/-- If fresh insertion changes extraction, its answer lies in the root/half-preimage set. -/
theorem mem_of_extract_ne {d : ℕ} {rt : Y} (hx : D x = none)
    (hne : extract enc d rt (Function.update D x (some y)) ≠ extract enc d rt D) :
    y ∈ insert rt (halfPreimages enc D) :=
  by_contra fun hy => hne (extract_eq_of_not_mem enc hx hy)
/-- **Lemma 8.6 for `MTMultiExtract`**: adding `x ↦ y` at an empty position of the database `j'`
does not change the extraction of a tuple, provided `y` avoids `{rt_i} ∪ HP(D_{j'})` for every
position `i` of the tuple with oracle `j'`. -/
theorem multiExtract_update_eq {k : ℕ} (d : Fin k → ℕ) (tic : TpIC k Y)
    (Ds : Fin k → Database X Y) (j' : Fin k) (hx : Ds j' x = none)
    (hy : ∀ i, (tic.2 i).1 = j' → y ∉ insert (tic.2 i).2 (halfPreimages enc (Ds j'))) :
    (multiExtract enc d).extract tic (Function.update Ds j' (Function.update (Ds j') x (some y))) =
      (multiExtract enc d).extract tic Ds := by
  simp only [multiExtract]
  split_ifs with h
  · funext i
    by_cases hi : (tic.2 i).1 = j'
    · have hyi := hy i hi
      rw [hi, Function.update_self]
      exact extract_eq_of_not_mem enc hx hyi
    · rw [Function.update_of_ne hi]
  · rfl

end Extract
end SaltedMerkle
