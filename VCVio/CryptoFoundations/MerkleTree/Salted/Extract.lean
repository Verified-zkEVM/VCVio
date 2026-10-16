/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Defs
public import VCVio.Quantum.VC.MultiExtractor
public import VCVio.Quantum.Oracle.Compressed.Basic
public import VCVio.OracleComp.QueryTracking.Collision

/-!
# Extraction from a database for salted Merkle trees

The extractor `MTExtract(rt, D)` of Chiesa, Di, Hu and Zheng (ePrint 2025/2166, §8.3,
pp. 54–55) reads a salted Merkle tree out of a database `D : Database X Y`, the classical state
of a compressed oracle. Starting from the root `rt`, it expands a vertex with label `u` into the
lexicographically first node preimage `(y₀, y₁)` of `u`, and at the leaves it reads the
lexicographically first leaf preimage `(m_ι, γ_ι)`. `MTMultiExtract` (p. 55) runs `MTExtract`
on every commitment of a tuple, against the database of its oracle.

## Design

* `extract` is a level recursion (`extLabel`) instead of the paper's while loop: the label at
  level `j + 1` and position `p` is the left or right half of the node preimage of the label at
  level `j` and position `p / 2`.
* A vertex is expanded only on a *node-shaped* preimage `D (enc.node (y₀, y₁)) = some u`. The paper
  tests `u ∈ im(D)` (p. 54) and then takes the first preimage of node length (p. 54). When `u` has
  a preimage but none of node length, which can happen under domain separation (for example a leaf
  input mapped to `u`), the paper's step is undefined; expanding only on a node-shaped preimage
  repairs that case by leaving the children `⊥`.
* "Lexicographically first" is the least element in `Lex (Y × Y)` and `Lex (Msg × Salt)`, which
  needs `LinearOrder` on `Y`, `Msg` and `Salt`. Any finite type has one, so this is a choice of
  extractor rather than a restriction; Lemma 8.6 holds for every such choice.
* `multiExtract` has a distinctness guard: a tuple with a repeated oracle index extracts to all `⊥`.
  Without it, Def 7.1 property 1 fails (see `Quantum.MultiExtractor.Admissible`).

## Conditions 2 and 3 of Thm 8.4

The classical conditions of Thm 8.4 (pp. 53–54) that §8.3 verifies for salted Merkle trees
(pp. 55–56), with `P_good` the collision-free databases (`collisionFree`):

* `extract_binding`, `multiExtract_binding` (condition 2, p. 53): if a collision-free
  database accepts `(rt, ans, pf)`, the extracted message agrees with `ans` and the extracted
  trapdoor opens `dom ans` to `pf`;
* `extract_valid`, `multiExtract_valid` (condition 3, p. 54): every database accepts the
  extracted message on its domain with the opening of the extracted trapdoor;
* `empty_mem_collisionFree` (condition 2, first half): `∅ ∈ P_good`.

## Main definitions

* `SaltedMerkle.nodePre`, `SaltedMerkle.leafPre`: the lexicographically first preimages.
* `SaltedMerkle.extLabel`, `SaltedMerkle.extract`: `MTExtract`.
* `SaltedMerkle.multiExtract`: `MTMultiExtract`, with the distinctness guard.
* `SaltedMerkle.collisionFree`: `P_good`, the databases in which an output determines its input;
  for `X Y : Type` it is the absence of `OracleComp.CacheHasCollision` on
  `Quantum.Database.equivQueryCache` (`mem_collisionFree_iff`).

## Main results

* `SaltedMerkle.multiExtract_admissible`: Def 7.1, repaired as in
  `Quantum.MultiExtractor.Admissible`.
* `SaltedMerkle.consistent_extract`: the extracted trapdoor is consistent with `D`.
* `SaltedMerkle.extract_binding`, `SaltedMerkle.extract_valid` and their multi-extractor forms.

The extractor and conditions 2 and 3 are stated with `SaltedMerkle.checkOn`, the table check of
`SaltedMerkle.checkIOForm` (`checkIOForm_checkOn`), and take `X`, `Y`, `Msg` and `Salt` in
independent universes.
-/

public section

open OracleComp OracleSpec Quantum

universe uX uY uM uS

namespace SaltedMerkle

variable {X : Type uX} {Y : Type uY} {Msg : Type uM} {Salt : Type uS}

/-! ## Least preimages -/

/-- The least element of a finite set, if it is nonempty. -/
@[expose]
def leastOf {α : Type*} [LinearOrder α] (s : Finset α) : Option α :=
  if h : s.Nonempty then some (s.min' h) else none

/-- The least element of a set belongs to it. -/
theorem mem_of_leastOf_eq_some {α : Type*} [LinearOrder α] {s : Finset α} {a : α}
    (h : leastOf s = some a) : a ∈ s := by
  unfold leastOf at h
  split_ifs at h with hs
  cases h
  exact s.min'_mem hs

/-- The least element of a set with only one element is that element. -/
theorem leastOf_eq_some {α : Type*} [LinearOrder α] {s : Finset α} {a : α} (ha : a ∈ s)
    (huniq : ∀ b ∈ s, b = a) : leastOf s = some a := by
  unfold leastOf
  rw [dite_eq_left ⟨a, ha⟩]
  exact congrArg some (huniq _ (s.min'_mem _))

/-- The least `a` with `D (f a) = some u`, if there is one. -/
@[expose]
def leastPre {α : Type*} [Fintype α] [LinearOrder α] [DecidableEq Y] (f : α → X)
    (D : Database X Y) (u : Y) : Option α :=
  leastOf (Finset.univ.filter fun a ↦ D (f a) = some u)

section leastPre

variable {α : Type*} [Fintype α] [LinearOrder α] [DecidableEq Y] {f : α → X} {D : Database X Y}
  {u : Y} {a : α}

/-- The least preimage is a preimage. -/
theorem leastPre_spec (h : leastPre f D u = some a) : D (f a) = some u := by
  simpa using mem_of_leastOf_eq_some h

/-- A unique preimage is the least preimage. -/
theorem leastPre_eq_some (h : D (f a) = some u) (huniq : ∀ b, D (f b) = some u → b = a) :
    leastPre f D u = some a :=
  leastOf_eq_some (by simpa using h) fun b hb ↦ huniq b (by simpa using hb)

/-- Adding the entry `x ↦ y` at an empty position does not change the preimages of `u ≠ y`. -/
theorem leastPre_update [DecidableEq X] {x : X} {y : Y} (hx : D x = none) (hu : u ≠ y) :
    leastPre f (Function.update D x (some y)) u = leastPre f D u := by
  unfold leastPre
  congr 1
  refine Finset.filter_congr fun b _ ↦ ?_
  by_cases hb : f b = x
  · rw [hb, Function.update_self, hx]
    simp [Ne.symm hu]
  · rw [Function.update_of_ne hb]

end leastPre

/-! ## The collision-free databases -/

/-- `P_good` of §8.3 (p. 55): the databases without a collision, that is, in which an output
determines its input. For `X Y : Type` this is the absence of #851's
`OracleComp.CacheHasCollision` on `Quantum.Database.equivQueryCache` (`mem_collisionFree_iff`). -/
@[expose]
def collisionFree : Set (Database X Y) :=
  {D | ∀ ⦃x₀ x₁ : X⦄ ⦃y : Y⦄, D x₀ = some y → D x₁ = some y → x₀ = x₁}

/-- `∅ ∈ P_good` (Thm 8.4 condition 2, p. 53). -/
theorem empty_mem_collisionFree : (Database.empty : Database X Y) ∈ collisionFree := by
  intro x₀ x₁ y h₀
  simp [Database.empty] at h₀

/-- In a collision-free database, an output determines its input. -/
theorem eq_of_mem_collisionFree {D : Database X Y} (hD : D ∈ collisionFree) {x₀ x₁ : X} {y : Y}
    (h₀ : D x₀ = some y) (h₁ : D x₁ = some y) : x₀ = x₁ :=
  hD h₀ h₁

/-- `collisionFree` is the absence of `OracleComp.CacheHasCollision` on the query cache of the
database. -/
theorem mem_collisionFree_iff {X Y : Type} {D : Database X Y} :
    D ∈ collisionFree ↔ ¬ CacheHasCollision (Database.equivQueryCache D) := by
  constructor
  · rintro hD ⟨t₁, t₂, u₁, u₂, hne, h₁, h₂, heq⟩
    rw [Database.equivQueryCache_apply] at h₁ h₂
    exact hne (hD h₁ (h₂.trans (congrArg some (eq_of_heq heq).symm)))
  · intro hD x₀ x₁ y h₀ h₁
    exact cache_lookup_eq_of_noCollision hD
      (by rw [Database.equivQueryCache_apply]; exact h₀)
      ⟨y, by rw [Database.equivQueryCache_apply]; exact h₁, HEq.rfl⟩

/-! ## The extractor -/

section Extract

variable [LinearOrder Y]

section Node

variable [Fintype Y]

/-- The lexicographically first node preimage `(y₀, y₁)` of `u` (p. 54). -/
@[expose]
def nodePre (enc : Encoding X Y Msg Salt) (D : Database X Y) (u : Y) : Option (Y × Y) :=
  (leastPre (fun p : Lex (Y × Y) ↦ enc.node (ofLex p)) D u).map ofLex

/-- The label at level `j` and position `p` of the tree that `MTExtract(rt, D)` builds
(p. 54): the root is `rt`, and the label at level `j + 1` and position `p` is the left half
(`p` even) or the right half (`p` odd) of the node preimage of its parent label. -/
@[expose]
def extLabel (enc : Encoding X Y Msg Salt) (D : Database X Y) (rt : Y) : ℕ → ℕ → Option Y
  | 0, _ => some rt
  | j + 1, p => (extLabel enc D rt j (p / 2)).bind fun u ↦
      (nodePre enc D u).map fun c ↦ if p % 2 = 0 then c.1 else c.2

variable (enc : Encoding X Y Msg Salt)

/-- The extracted label at level `0` is the root. -/
theorem extLabel_zero (D : Database X Y) (rt : Y) (p : ℕ) : extLabel enc D rt 0 p = some rt :=
  rfl

/-- The extracted label at level `j + 1` is a half of the node preimage of its parent label. -/
theorem extLabel_succ (D : Database X Y) (rt : Y) (j p : ℕ) :
    extLabel enc D rt (j + 1) p = (extLabel enc D rt j (p / 2)).bind fun u ↦
      (nodePre enc D u).map fun c ↦ if p % 2 = 0 then c.1 else c.2 :=
  rfl

/-- The node preimage of `u` is a node input that `D` maps to `u`. -/
theorem nodePre_spec {D : Database X Y} {u : Y} {c : Y × Y} (h : nodePre enc D u = some c) :
    D (enc.node c) = some u := by
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
  exact leastPre_spec (α := Lex (Y × Y)) hc'

/-- In a collision-free database, the node preimage of an output is the unique one. -/
theorem nodePre_eq_of_mem_collisionFree {D : Database X Y} (hD : D ∈ collisionFree) {u : Y}
    {c : Y × Y} (h : D (enc.node c) = some u) : nodePre enc D u = some c := by
  have : leastPre (fun p : Lex (Y × Y) ↦ enc.node (ofLex p)) D u = some (toLex c) :=
    leastPre_eq_some h fun b hb ↦
      congrArg toLex (enc.node_injective (eq_of_mem_collisionFree hD hb h))
  simp [nodePre, this]

end Node

section Leaf

variable [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- The lexicographically first leaf preimage `(m, γ)` of `u` (p. 55). -/
@[expose]
def leafPre (enc : Encoding X Y Msg Salt) (D : Database X Y) (u : Y) : Option (Msg × Salt) :=
  (leastPre (fun p : Lex (Msg × Salt) ↦ enc.leaf (ofLex p)) D u).map ofLex

variable (enc : Encoding X Y Msg Salt)

/-- The leaf preimage of `u` is a leaf input that `D` maps to `u`. -/
theorem leafPre_spec {D : Database X Y} {u : Y} {c : Msg × Salt} (h : leafPre enc D u = some c) :
    D (enc.leaf c) = some u := by
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
  exact leastPre_spec (α := Lex (Msg × Salt)) hc'

/-- In a collision-free database, the leaf preimage of an output is the unique one. -/
theorem leafPre_eq_of_mem_collisionFree {D : Database X Y} (hD : D ∈ collisionFree) {u : Y}
    {c : Msg × Salt} (h : D (enc.leaf c) = some u) : leafPre enc D u = some c := by
  have : leastPre (fun p : Lex (Msg × Salt) ↦ enc.leaf (ofLex p)) D u = some (toLex c) :=
    leastPre_eq_some h fun b hb ↦
      congrArg toLex (enc.leaf_injective (eq_of_mem_collisionFree hD hb h))
  simp [leafPre, this]

end Leaf

/-! ## Parsing an accepted check -/

section Parse

variable [DecidableEq X] (enc : Encoding X Y Msg Salt)

/-- If a database accepts `(rt, ans, pf)`, every pair that `OutputIO` lists for an opened position
is an entry of the database. -/
theorem leafIO_sub_of_checkOn {d : ℕ} {rt : Y} {ans : PartialVec (2 ^ d) Msg} {pf : Pf Y Salt d}
    {D : Database X Y} (h : checkOn enc d D rt ans pf = true) :
    (∀ ι, (pf ι).isSome = (ans ι).isSome) ∧ ∀ ι a pp, ans ι = some a → pf ι = some pp →
      ∀ p ∈ leafIO enc rt ι a pp, D p.1 = some p.2 := by
  change (outputIO enc d rt ans pf).elim false (checkIOOn D) = true at h
  unfold outputIO at h
  split_ifs at h with hpf
  · rw [Option.elim_some, checkIOOn_eq_true_iff] at h
    refine ⟨hpf, fun ι a pp ha hpp p hp ↦ h p ?_⟩
    rw [List.mem_dedup, List.mem_flatMap]
    exact ⟨ι, List.mem_finRange _, by rw [ha, hpp]; exact hp⟩
  · simp at h

end Parse

variable [Fintype Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- The leaf preimage `(m_ι, γ_ι)` of the extracted leaf label (pp. 54–55). -/
@[expose]
def extLeaf (enc : Encoding X Y Msg Salt) (d : ℕ) (rt : Y) (D : Database X Y) (ι : ℕ) :
    Option (Msg × Salt) :=
  (extLabel enc D rt d ι).bind (leafPre enc D)

/-- `MTExtract(rt, D)` (pp. 54–55): the extracted message and the trapdoor `(γ, C)`, with `⊥` for
every value that the extraction does not reach. -/
@[expose]
def extract (enc : Encoding X Y Msg Salt) (d : ℕ) (rt : Y) (D : Database X Y) :
    PartialVec (2 ^ d) Msg × Td Y Salt d :=
  (fun ι ↦ (extLeaf enc d rt D ι).map Prod.fst,
    (fun ι ↦ (extLeaf enc d rt D ι).map Prod.snd, fun j q ↦ extLabel enc D rt j q))

/-- `MTMultiExtract` (p. 55) with a distinctness guard: position `i` of a tuple with distinct
indices is `MTExtract(rt_i, D_{idx_i})` for the tree of depth `d i`; a tuple with a repeated index
extracts to all `⊥`. -/
@[expose]
def multiExtract (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ) :
    MultiExtractor k Y (DmOf (fun i ↦ 2 ^ d i) Msg fun i ↦ Td Y Salt (d i))
      (Fin k → Database X Y) where
  extract tic Ds := if Function.Injective tic.idx then
      fun i ↦ extract enc (d (Fin.castLE tic.1.len_le i)) (tic.2 i).2 (Ds (tic.2 i).1)
    else fun _ ↦ (fun _ ↦ none, tdBot)

/-- **`MTMultiExtract` is admissible** (Def 7.1, repaired as in
`Quantum.MultiExtractor.Admissible`). -/
theorem multiExtract_admissible (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ) :
    (multiExtract enc d).Admissible fun _ ↦ (fun _ ↦ none, tdBot) where
  eq_bot_of_not_injective tic Ds h i := by
    simp only [multiExtract, ite_eq_right h]
  prefix_eq tic Ds h j' hj' i := by
    simp only [multiExtract, ite_eq_left h, ite_eq_left (TpIC.idx_prefix_injective h j' hj')]
    rfl

variable (enc : Encoding X Y Msg Salt)

/-- In range, the extracted table holds the extracted labels. -/
theorem labelAt_extract (d : ℕ) (rt : Y) (D : Database X Y) {j p : ℕ} (hj : j ≤ d)
    (hp : p < 2 ^ j) : labelAt (extract enc d rt D).2.2 j p = extLabel enc D rt j p :=
  labelAt_mk _ hj hp

/-! ## Condition 3: validity -/

/-- The extracted trapdoor is consistent with the extracted message for the relation
`D x = some y`. -/
theorem consistent_extract (d : ℕ) (rt : Y) (D : Database X Y) :
    Consistent (fun x y ↦ D x = some y) enc rt (extract enc d rt D).1 (extract enc d rt D).2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [labelAt_extract enc d rt D (Nat.zero_le d) (Nat.two_pow_pos 0)]
    rfl
  · intro i hi p hp hsome
    have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    rw [labelAt_extract enc d rt D (by omega) hp, extLabel_succ] at hsome
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨c, hc, -⟩ := Option.map_eq_some_iff.mp hv
    refine ⟨u, c.1, c.2, ?_, ?_, ?_, nodePre_spec enc hc⟩
    · rw [labelAt_extract enc d rt D (by omega) (by omega)]
      exact hu
    · rw [labelAt_extract enc d rt D (by omega) (by omega), extLabel_succ,
        show 2 * (p / 2) / 2 = p / 2 by omega]
      simp [hu, hc]
    · rw [labelAt_extract enc d rt D (by omega) (by omega), extLabel_succ,
        show (2 * (p / 2) + 1) / 2 = p / 2 by omega]
      simp [hu, hc, show (2 * (p / 2) + 1) % 2 = 1 by omega]
  · intro ι a ha
    simp only [extract] at ha
    obtain ⟨⟨a', s⟩, hleaf, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨l, hl, hpre⟩ := Option.bind_eq_some_iff.mp hleaf
    refine ⟨s, l, by simp [extract, hleaf], ?_, leafPre_spec enc hpre⟩
    rw [labelAt_extract enc d rt D le_rfl ι.isLt]
    exact hl

section Valid

variable [DecidableEq X]

/-- **Validity** (Thm 8.4 condition 3, p. 54; §8.3, p. 56): every database accepts the
extracted message on its domain, with the opening of the extracted trapdoor. -/
theorem extract_valid (d : ℕ) (rt : Y) (D : Database X Y) :
    checkOn enc d D rt (extract enc d rt D).1
      (opening d (extract enc d rt D).1.dom (extract enc d rt D).2) = true := by
  obtain ⟨io, hio, hG⟩ := (consistent_extract enc d rt D).outputIO_opening
  change (outputIO enc d rt _ _).elim false (checkIOOn D) = true
  rw [hio, Option.elim_some, checkIOOn_eq_true_iff]
  exact hG

end Valid

/-! ## Condition 2: binding -/

/-- Along an accepted opening of a collision-free database, the extraction follows the path: the
extracted labels are the path nodes and their siblings, and the extracted leaf is the answer with
its salt. -/
theorem extract_path_of_checkOn {d : ℕ} {rt : Y} {D : Database X Y} (hD : D ∈ collisionFree)
    {ι : Fin (2 ^ d)} {a : Msg} {pp : PathProof Y Salt d}
    (hleaf : D (enc.leaf (a, pp.salt)) = some (pp.node rt d))
    (hnode : ∀ j : Fin d,
      D (enc.node (order (anc d ι ((j : ℕ) + 1)) (pp.path j))) = some (pp.node rt j)) :
    extLeaf enc d rt D ι = some (a, pp.salt) ∧ ∀ j : Fin d,
      extLabel enc D rt ((j : ℕ) + 1) (anc d ι ((j : ℕ) + 1)) = some (pp.path j).1 ∧
        extLabel enc D rt ((j : ℕ) + 1) (sib (anc d ι ((j : ℕ) + 1))) = some (pp.path j).2 := by
  -- The parent label of level `j + 1` is the path node of level `j`.
  have hpar : ∀ j : Fin d, nodePre enc D (pp.node rt j) =
      some (order (anc d ι ((j : ℕ) + 1)) (pp.path j)) :=
    fun j ↦ nodePre_eq_of_mem_collisionFree enc hD (hnode j)
  have hnode_succ : ∀ j : Fin d, pp.node rt ((j : ℕ) + 1) = (pp.path j).1 := fun j ↦ by
    unfold PathProof.node
    rw [dite_eq_left ⟨by omega, j.isLt⟩]
    rfl
  have hlab : ∀ j, j ≤ d → extLabel enc D rt j (anc d ι j) = some (pp.node rt j) := by
    intro j
    induction j with
    | zero =>
        intro _
        unfold PathProof.node
        rw [dite_eq_right (by omega)]
        rfl
    | succ j ih =>
        intro hj
        have hjd : j < d := by omega
        rw [extLabel_succ, anc_succ_div_two hjd, ih hjd.le, Option.bind_some,
          hpar ⟨j, hjd⟩, Option.map_some, hnode_succ ⟨j, hjd⟩]
        congr 1
        unfold order
        split_ifs <;> rfl
  have hsib : ∀ j : Fin d,
      extLabel enc D rt ((j : ℕ) + 1) (sib (anc d ι ((j : ℕ) + 1))) = some (pp.path j).2 := by
    intro j
    rw [extLabel_succ, sib_div_two, anc_succ_div_two j.isLt, hlab j j.isLt.le, Option.bind_some,
      hpar j, Option.map_some]
    congr 1
    unfold order sib
    split_ifs <;> first | rfl | omega
  refine ⟨?_, fun j ↦ ⟨?_, hsib j⟩⟩
  · rw [extLeaf, show (ι : ℕ) = anc d ι d from (anc_self _).symm, hlab d le_rfl,
      Option.bind_some]
    exact leafPre_eq_of_mem_collisionFree enc hD hleaf
  · rw [hlab _ j.isLt, hnode_succ]

variable [DecidableEq X]

/-- **Binding** (Thm 8.4 condition 2, p. 53; §8.3, pp. 55–56): if a collision-free
database accepts `(rt, ans, pf)`, then the extracted message agrees with `ans` on `dom ans`, and the
extracted trapdoor opens `dom ans` to exactly `pf`. -/
theorem extract_binding {d : ℕ} {rt : Y} {ans : PartialVec (2 ^ d) Msg} {pf : Pf Y Salt d}
    {D : Database X Y} (hD : D ∈ collisionFree)
    (h : checkOn enc d D rt ans pf = true) :
    (extract enc d rt D).1.Agrees ans ∧ opening d ans.dom (extract enc d rt D).2 = pf := by
  obtain ⟨hpf, hmem⟩ := leafIO_sub_of_checkOn enc h
  have key : ∀ ι a pp, ans ι = some a → pf ι = some pp →
      extLeaf enc d rt D ι = some (a, pp.salt) ∧ ∀ j : Fin d,
        extLabel enc D rt ((j : ℕ) + 1) (anc d ι ((j : ℕ) + 1)) = some (pp.path j).1 ∧
          extLabel enc D rt ((j : ℕ) + 1) (sib (anc d ι ((j : ℕ) + 1))) =
            some (pp.path j).2 := by
    intro ι a pp ha hpp
    have hio := hmem ι a pp ha hpp
    refine extract_path_of_checkOn enc hD (hio _ List.mem_cons_self) fun j ↦
      hio (enc.node (order (anc d ι ((j : ℕ) + 1)) (pp.path j)), pp.node rt j) ?_
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hpp : ∀ ι a, ans ι = some a → ∃ pp, pf ι = some pp := fun ι a ha ↦
    Option.isSome_iff_exists.mp (by rw [hpf, ha]; rfl)
  refine ⟨fun ι a ha ↦ ?_, funext fun ι ↦ ?_⟩
  · obtain ⟨pp, hpp⟩ := hpp ι a ha
    simp [extract, (key ι a pp ha hpp).1]
  · cases ha : ans ι with
    | none =>
        have : pf ι = none := by simpa [ha] using hpf ι
        simp [opening, PartialVec.mem_dom, ha, this]
    | some a =>
        obtain ⟨pp, hpp⟩ := hpp ι a ha
        obtain ⟨hl, hpath⟩ := key ι a pp ha hpp
        have hopt : optionPi (pathPair (extract enc d rt D).2.2 ι) = some pp.path := by
          refine optionPi_eq_some_iff.mpr fun j ↦ ?_
          have hlt := anc_lt ι.isLt j.isLt
          rw [pathPair, labelAt_extract enc d rt D j.isLt hlt,
            labelAt_extract enc d rt D j.isLt (sib_lt hlt), (hpath j).1, (hpath j).2]
          rfl
        simp only [extract] at hopt
        rw [hpp]
        simp [opening, PartialVec.mem_dom, ha, extract, hl, hopt]

/-! ## The multi-extractor -/

variable {k : ℕ} (d : Fin k → ℕ)

/-- **Binding for `MTMultiExtract`** (Thm 8.4 condition 2, p. 53): for distinct indices and
collision-free databases, if every check passes, every extracted message agrees with its answers
and every extracted trapdoor opens to its proof. -/
theorem multiExtract_binding (hk : 1 ≤ k) (idx : Fin k → Fin k) (hidx : Function.Injective idx)
    (cm : Fin k → Y) (ans : ∀ i, PartialVec (2 ^ d i) Msg) (pf : ∀ i, Pf Y Salt (d i))
    (Ds : Fin k → Database X Y) (hD : ∀ i, Ds i ∈ collisionFree)
    (h : ∀ i, checkOn enc (d i) (Ds (idx i)) (cm i) (ans i) (pf i) = true)
    (i : Fin k) :
    ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).1.Agrees (ans i) ∧
      opening (d i) (ans i).dom ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).2 =
        pf i := by
  have hinj : Function.Injective (TpIC.full hk idx cm).idx := hidx
  simp only [multiExtract, ite_eq_left hinj]
  exact extract_binding enc (hD (idx i)) (h i)

/-- **Validity for `MTMultiExtract`** (Thm 8.4 condition 3, p. 54): for distinct indices and
any databases, every extracted message passes the check on its domain with the opening of its
extracted trapdoor. -/
theorem multiExtract_valid (hk : 1 ≤ k) (idx : Fin k → Fin k) (hidx : Function.Injective idx)
    (cm : Fin k → Y) (Ds : Fin k → Database X Y) (i : Fin k) :
    checkOn enc (d i) (Ds (idx i)) (cm i)
      ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).1
      (opening (d i) ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).1.dom
        ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).2) = true := by
  have hinj : Function.Injective (TpIC.full hk idx cm).idx := hidx
  simp only [multiExtract, ite_eq_left hinj]
  exact extract_valid enc (d i) (cm i) (Ds (idx i))

end Extract

end SaltedMerkle
