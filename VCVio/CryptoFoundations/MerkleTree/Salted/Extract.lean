/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Defs
public import VCVio.CryptoFoundations.MerkleTree.OrderedResolver
public import VCVio.Quantum.VC.MultiExtractor
public import VCVio.Quantum.Oracle.Compressed.Basic
public import VCVio.OracleComp.QueryTracking.Collision

/-!
# Salted Merkle extraction

The extractor of Chiesa, Di, Hu and Zheng, ePrint 2025/2166, §8.3 reconstructs a partial tree
with the shared Merkle walker, selecting the lexicographically least pair at each role.
Collision-free tables recover accepted openings exactly. Validity holds for every table.
-/

public section

open OracleComp OracleSpec Quantum BinaryTree MerkleTreeHashing MerkleTreeExtractor

universe uX uY uM uS
namespace SaltedMerkle
variable {X : Type uX} {Y : Type uY} {Msg : Type uM} {Salt : Type uS}
/-! ## The collision-free databases -/

/-- `P_good` of §8.3 (p. 55): the databases without a collision, that is, in which an output
determines its input. For `X Y : Type` this is the absence of
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

section Parse
variable [DecidableEq X] [DecidableEq Y] (enc : QueryEncoding X Unit Unit (Msg × Salt) Y)

/-- If a database accepts `(rt, ans, pf)`, every pair that `OutputIO` lists for an opened position
is an entry of the database. -/
theorem leafIO_sub_of_checkOn {d : ℕ} {rt : Y} {ans : PartialVec (2 ^ d) Msg} {pf : Pf Y Salt d}
    {D : Database X Y} (h : checkOn enc d D rt ans pf = true) :
    (∀ ι, (pf ι).isSome = (ans ι).isSome) ∧ ∀ ι a pp, ans ι = some a → pf ι = some pp →
      ∀ p ∈ leafIO enc rt ι a pp, D p.1 = some p.2 := by
  change (pairs enc d rt ans pf).elim false (checkIOOn D) = true at h
  unfold pairs at h
  split_ifs at h with hpf
  · rw [Option.elim_some, checkIOOn_eq_true_iff] at h
    refine ⟨hpf, fun ι a pp ha hpp p hp ↦ h p ?_⟩
    rw [List.mem_dedup, List.mem_flatMap]
    exact ⟨ι, List.mem_finRange _, by rw [ha, hpp]; exact hp⟩
  · simp at h

end Parse

section Extract
variable [LinearOrder Y] [Fintype Y] [LinearOrder Msg] [Fintype Msg]
  [LinearOrder Salt] [Fintype Salt]

/-- Recover the payload at a reached leaf of the partial tree. -/
@[expose]
def extLeaf (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) (rt : Y)
    (D : Database X Y) (i : Fin (2 ^ d)) : Option (Msg × Salt) :=
  recoverLeaf (resolvePair (enc.leaf ()) D)
    (treeWith (fun _ : Unit => resolvePair (enc.node ()) D) (Skeleton.perfect d)
      (fun _ => ()) rt) (SkeletonLeafIndex.perfectEquiv d i)

/-- Extract messages, salts and the partial typed tree from a claimed root. -/
@[expose]
def extract (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) (rt : Y)
    (D : Database X Y) : PartialVec (2 ^ d) Msg × Td Y Salt d :=
  (fun i => (extLeaf enc d rt D i).map Prod.fst,
    (fun i => (extLeaf enc d rt D i).map Prod.snd,
      treeWith (fun _ : Unit => resolvePair (enc.node ()) D) (Skeleton.perfect d)
        (fun _ => ()) rt))
/-- `MTMultiExtract` (p. 55) with a distinctness guard: position `i` of a tuple with distinct
indices is `MTExtract(rt_i, D_{idx_i})` for the tree of depth `d i`; a tuple with a repeated index
extracts to all `⊥`. -/
@[expose]
def multiExtract (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) {k : ℕ} (d : Fin k → ℕ) :
    MultiExtractor k Y (DmOf (fun i ↦ 2 ^ d i) Msg fun i ↦ Td Y Salt (d i))
      (Fin k → Database X Y) where
  extract tic Ds := if Function.Injective tic.idx then
      fun i ↦ extract enc (d (Fin.castLE tic.1.len_le i)) (tic.2 i).2 (Ds (tic.2 i).1)
    else fun _ ↦ (fun _ ↦ none, tdBot)

/-- **`MTMultiExtract` is admissible** (Def 7.1, repaired as in
`Quantum.MultiExtractor.Admissible`). -/
theorem multiExtract_admissible (enc : QueryEncoding X Unit Unit (Msg × Salt) Y)
    {k : ℕ} (d : Fin k → ℕ) :
    (multiExtract enc d).Admissible fun _ ↦ (fun _ ↦ none, tdBot) where
  eq_bot_of_not_injective tic Ds h i := by
    simp only [multiExtract, ite_eq_right h]
  prefix_eq tic Ds h j' hj' i := by
    simp only [multiExtract, ite_eq_left h, ite_eq_left (TpIC.idx_prefix_injective h j' hj')]
    rfl

variable (enc : QueryEncoding X Unit Unit (Msg × Salt) Y)

/-- Extraction produces a consistent trapdoor on all tables, including collisionful tables. -/
theorem consistent_extract (d : ℕ) (rt : Y) (D : Database X Y) :
    Consistent (fun x y => D x = some y) enc rt (extract enc d rt D).1
      (extract enc d rt D).2 := by
  refine ⟨treeWith_getRootValue _ _ _ _,
    partialTreeConsistent_treeWith _ _ _ (fun _ _ h => resolvePair_spec h) _ _, ?_⟩
  intro i a ha
  obtain ⟨⟨a', salt⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨label, hl, hc⟩ := Option.bind_eq_some_iff.mp hp
  exact ⟨salt, label, by simp [extract, hp], hl, resolvePair_spec hc⟩

/-- Every extracted message verifies on its domain with its generated opening. -/
theorem extract_valid [DecidableEq X] (d : ℕ) (rt : Y) (D : Database X Y) :
    checkOn enc d D rt (extract enc d rt D).1
      (opening d (extract enc d rt D).1.dom (extract enc d rt D).2) = true := by
  obtain ⟨io, hio, hG⟩ := (consistent_extract enc d rt D).pairs_opening
  change (pairs enc d rt _ _).elim false (checkIOOn D) = true
  rw [hio, Option.elim_some, checkIOOn_eq_true_iff]
  exact hG
/-- Collision-free accepted checks recover the exact salt, message and labelled path. -/
theorem extract_path_of_checkOn {d : ℕ} {rt : Y} {D : Database X Y} (hD : D ∈ collisionFree)
    {i : Fin (2 ^ d)} {a : Msg} {pp : PathProof Y Salt d}
    (hchecks : ∀ q ∈ leafIO enc rt i a pp, D q.1 = some q.2) :
    extLeaf enc d rt D i = some (a, pp.salt) ∧
      readPath (extract enc d rt D).2.2 (SkeletonLeafIndex.perfectEquiv d i) = some (pp.at _) := by
  obtain ⟨hp, label, hl, hleaf⟩ := readPath_treeWith_of_checks (enc.node ()) D
    (fun _ : Unit => resolvePair (enc.node ()) D)
    (fun _ _ h => resolvePair_eq_of_injective (enc.node_injective ()) hD h)
    (SkeletonLeafIndex.perfectEquiv d i) rt (pp.at _) (enc.leaf () (a, pp.salt))
    (by simpa only [leafIO, List.mem_rotate] using hchecks)
  refine ⟨?_, hp⟩
  rw [extLeaf, recoverLeaf, hl, Option.bind_some]
  exact resolvePair_eq_of_injective (enc.leaf_injective ()) hD hleaf

variable [DecidableEq X]

/-- Binding recovers every answered message and regenerates the entire proof exactly. -/
theorem extract_binding {d : ℕ} {rt : Y} {ans : PartialVec (2 ^ d) Msg}
    {pf : Pf Y Salt d} {D : Database X Y} (hD : D ∈ collisionFree)
    (h : checkOn enc d D rt ans pf = true) :
    (extract enc d rt D).1.Agrees ans ∧ opening d ans.dom (extract enc d rt D).2 = pf := by
  obtain ⟨hpf, hmem⟩ := leafIO_sub_of_checkOn enc h
  have hpp : ∀ i a, ans i = some a → ∃ pp, pf i = some pp := fun i a ha =>
    Option.isSome_iff_exists.mp (by rw [hpf, ha]; rfl)
  refine ⟨fun i a ha => ?_, funext fun i => ?_⟩
  · obtain ⟨pp, hp⟩ := hpp i a ha
    have hk := extract_path_of_checkOn enc hD (hmem i a pp ha hp)
    simp [extract, hk.1]
  · cases ha : ans i with
    | none =>
        have hp : pf i = none := by simpa [ha] using hpf i
        simp [opening, PartialVec.mem_dom, ha, hp]
    | some a =>
        obtain ⟨pp, hp⟩ := hpp i a ha
        obtain ⟨hl, ht⟩ := extract_path_of_checkOn enc hD (hmem i a pp ha hp)
        rw [hp]
        simp only [opening, PartialVec.mem_dom, ha, Option.isSome_some, ite_true]
        rw [ht]
        simp only [extract, hl, Option.map_some, Option.bind_some]
        rfl
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
