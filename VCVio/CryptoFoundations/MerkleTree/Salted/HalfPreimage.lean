/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Extract

/-!
# Half-preimages and the stability of Merkle extraction

The half-preimages of a database `D` (Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Def 8.5,
p. 55; Chiesa, Manohar and Spooner, TCC 2019, Def 6.3) are the values `u` that occur as one
half of a node input `(u, u')` or `(u', u)` in the domain of `D`.

Lemma 8.6 (p. 55; CMS19 Lemma 6.5) says that adding a new entry `x ↦ y` to `D` can change
`MTExtract(rt, D)` only when `y ∈ {rt} ∪ HP(D)`. It holds for **every** database, with or without
collisions:

* every label that the extraction reaches is the root or a half of a node input in `dom D`, so it
  lies in `{rt} ∪ HP(D)` (`extLabel_mem`);
* the new entry changes no preimage set of a value `u ≠ y` (`nodePre_update`, `leafPre_update`), so
  the extraction, which only asks for preimages of reached labels, is unchanged.

Lemma 8.8 (§8.3, p. 56) uses this with `|HP(D)| ≤ 2 |D|` (`ncard_halfPreimages_le`) to bound
the instability of the online label of `MTMultiExtract`; `multiExtract_update_eq` is the form of
Lemma 8.6 for one database of a tuple.

## Main definitions

* `SaltedMerkle.halfPreimages enc D`: `HP(D)`, for the node-shaped inputs.

## Main results

* `SaltedMerkle.extract_eq_of_not_mem`: Lemma 8.6.
* `SaltedMerkle.mem_of_extract_ne`: Lemma 8.6, in the paper's contrapositive form.
* `SaltedMerkle.multiExtract_update_eq`: Lemma 8.6 for `MTMultiExtract`.
* `SaltedMerkle.ncard_halfPreimages_le`: `|HP(D)| ≤ 2 |dom D|` for every database with finite
  support; `SaltedMerkle.ncard_halfPreimages_le_of_finite` for a finite oracle domain.
-/

public section

open Quantum

universe uX uY uM uS

namespace SaltedMerkle

variable {X : Type uX} {Y : Type uY} {Msg : Type uM} {Salt : Type uS}

/-- The half-preimages `HP(D)` of a database (Def 8.5, p. 55): the values `u` with a node
input `(u, u')` or `(u', u)` in the domain of `D`. -/
@[expose]
def halfPreimages (enc : Encoding X Y Msg Salt) (D : Database X Y) : Set Y :=
  {u | ∃ u', D (enc.node (u, u')) ≠ none ∨ D (enc.node (u', u)) ≠ none}

variable (enc : Encoding X Y Msg Salt)

/-- The left half of a node input in the domain is a half-preimage. -/
theorem fst_mem_halfPreimages {D : Database X Y} {c : Y × Y} (h : D (enc.node c) ≠ none) :
    c.1 ∈ halfPreimages enc D :=
  ⟨c.2, Or.inl h⟩

/-- The right half of a node input in the domain is a half-preimage. -/
theorem snd_mem_halfPreimages {D : Database X Y} {c : Y × Y} (h : D (enc.node c) ≠ none) :
    c.2 ∈ halfPreimages enc D :=
  ⟨c.1, Or.inr h⟩

/-- `|HP(D)| ≤ 2 |dom D|` for a database with finite support: every input in the domain contributes
at most its two halves. The oracle domain `X` may be infinite. -/
theorem ncard_halfPreimages_le (D : Database X Y) (hD : {x | D x ≠ none}.Finite) :
    (halfPreimages enc D).ncard ≤ 2 * {x | D x ≠ none}.ncard := by
  set P : Set (Y × Y) := {c | D (enc.node c) ≠ none}
  have hP : P.Finite := hD.preimage enc.node_injective.injOn
  have hsub : halfPreimages enc D ⊆ Prod.fst '' P ∪ Prod.snd '' P := by
    rintro u ⟨u', h | h⟩
    · exact Or.inl ⟨(u, u'), h, rfl⟩
    · exact Or.inr ⟨(u', u), h, rfl⟩
  have hcard : P.ncard ≤ {x | D x ≠ none}.ncard :=
    Set.ncard_le_ncard_of_injOn enc.node (fun _ hc ↦ hc) enc.node_injective.injOn hD
  calc (halfPreimages enc D).ncard
      ≤ (Prod.fst '' P ∪ Prod.snd '' P).ncard :=
        Set.ncard_le_ncard hsub ((hP.image _).union (hP.image _))
    _ ≤ (Prod.fst '' P).ncard + (Prod.snd '' P).ncard := Set.ncard_union_le _ _
    _ ≤ P.ncard + P.ncard := add_le_add (Set.ncard_image_le hP) (Set.ncard_image_le hP)
    _ ≤ 2 * {x | D x ≠ none}.ncard := by omega

/-- `|HP(D)| ≤ 2 |dom D|` over a finite oracle domain, where every database has finite support. -/
theorem ncard_halfPreimages_le_of_finite [Finite X] (D : Database X Y) :
    (halfPreimages enc D).ncard ≤ 2 * {x | D x ≠ none}.ncard :=
  ncard_halfPreimages_le enc D (Set.toFinite _)

section Extract

variable [LinearOrder Y] [Fintype Y]

/-- Every label that `MTExtract(rt, D)` reaches is the root or a half-preimage of `D`. -/
theorem extLabel_mem {D : Database X Y} {rt : Y} {j p : ℕ} {u : Y}
    (h : extLabel enc D rt j p = some u) : u ∈ insert rt (halfPreimages enc D) := by
  induction j generalizing p u with
  | zero =>
      cases Option.some.inj h
      exact Set.mem_insert _ _
  | succ j ih =>
      rw [extLabel_succ] at h
      obtain ⟨u', -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
      have hD : D (enc.node c) ≠ none := by simp [nodePre_spec enc hc]
      refine Set.mem_insert_of_mem _ ?_
      split_ifs
      · exact fst_mem_halfPreimages enc hD
      · exact snd_mem_halfPreimages enc hD

variable [DecidableEq X] {D : Database X Y} {x : X} {y : Y}

/-- Adding an entry `x ↦ y` at an empty position does not change the node preimage of `u ≠ y`. -/
theorem nodePre_update (hx : D x = none) {u : Y} (hu : u ≠ y) :
    nodePre enc (Function.update D x (some y)) u = nodePre enc D u := by
  simp only [nodePre, leastPre_update hx hu]

omit [Fintype Y] in
/-- Adding an entry `x ↦ y` at an empty position does not change the leaf preimage of `u ≠ y`. -/
theorem leafPre_update [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
    (hx : D x = none) {u : Y} (hu : u ≠ y) :
    leafPre enc (Function.update D x (some y)) u = leafPre enc D u := by
  simp only [leafPre, leastPre_update hx hu]

/-- Adding an entry `x ↦ y` with `y ∉ {rt} ∪ HP(D)` at an empty position does not change the
extracted labels. -/
theorem extLabel_update {rt : Y} (hx : D x = none) (hy : y ∉ insert rt (halfPreimages enc D))
    (j p : ℕ) : extLabel enc (Function.update D x (some y)) rt j p = extLabel enc D rt j p := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
      rw [extLabel_succ, extLabel_succ, ih]
      refine Option.bind_congr fun u hu ↦ ?_
      rw [nodePre_update enc hx fun h : u = y ↦ hy (h ▸ extLabel_mem enc hu)]

variable [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- **Lemma 8.6** (p. 55; CMS19 Lemma 6.5), for every database, collisions included: adding
an entry `x ↦ y` at an empty position, with `y ∉ {rt} ∪ HP(D)`, does not change
`MTExtract(rt, D)`. -/
theorem extract_eq_of_not_mem {d : ℕ} {rt : Y} (hx : D x = none)
    (hy : y ∉ insert rt (halfPreimages enc D)) :
    extract enc d rt (Function.update D x (some y)) = extract enc d rt D := by
  have hleaf : ∀ ι, extLeaf enc d rt (Function.update D x (some y)) ι = extLeaf enc d rt D ι := by
    intro ι
    rw [extLeaf, extLeaf, extLabel_update enc hx hy]
    exact Option.bind_congr fun u hu ↦
      leafPre_update enc hx fun h : u = y ↦ hy (h ▸ extLabel_mem enc hu)
  simp only [extract, hleaf, extLabel_update enc hx hy]

/-- **Lemma 8.6**, as stated in the paper: if adding `x ↦ y` at an empty position changes
`MTExtract(rt, D)`, then `y ∈ {rt} ∪ HP(D)`. -/
theorem mem_of_extract_ne {d : ℕ} {rt : Y} (hx : D x = none)
    (hne : extract enc d rt (Function.update D x (some y)) ≠ extract enc d rt D) :
    y ∈ insert rt (halfPreimages enc D) :=
  by_contra fun hy ↦ hne (extract_eq_of_not_mem enc hx hy)

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
