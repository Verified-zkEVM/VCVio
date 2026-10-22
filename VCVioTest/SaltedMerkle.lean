/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Salted.HalfPreimage

/-!
# Tests for salted Merkle trees

Toy instances of Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Definition 8.2, with one-bit labels,
messages and salts and tagged oracle inputs:

* depths `d = 0` and `d = 1`, with their non-adaptive checks and perfect completeness;
* an honest commitment for an explicit hash function, opened and checked by evaluation;
* `MTExtract` evaluated on a small explicit database, its validity, and Lemma 8.6 on it.
-/

public section

namespace VCVioTest.SaltedMerkleCanary

open SaltedMerkle Quantum MerkleTreeHashing BinaryTree

/-- Tagged inputs: node inputs on the left, leaf inputs `(m, γ)` on the right. -/
abbrev X := (Bool × Bool) ⊕ (Bool × Bool)

/-- The tagged encoding. -/
def enc : QueryEncoding X Unit Unit (Bool × Bool) Bool where
  node _ := Sum.inl
  leaf _ := Sum.inr
  node_injective _ := Sum.inl_injective
  leaf_injective _ := Sum.inr_injective

/-! ## Depths `0` and `1` -/

example : DetVectorCommitment X Bool Bool Bool (Td Bool Bool 0) (Pf Bool Bool 0) 1 := scheme enc 0

example : VectorCommitment X Bool Bool Bool (Td Bool Bool 1) (Pf Bool Bool 1) 2 :=
  (scheme enc 1).toVectorCommitment

/-- Finite labels and salts give a finite trapdoor register. -/
example : Finite (Td Bool Bool 2) := inferInstance

noncomputable example : Fintype (Td Bool Bool 2) := inferInstance

example : (scheme (Msg := Bool) enc 0).PerfectlyComplete := perfectlyComplete enc 0

example : (scheme (Msg := Bool) enc 1).PerfectlyComplete := perfectlyComplete enc 1

/-- Perfect completeness relative to an arbitrary oracle distribution (Def 3.7). -/
example (D : MeasureTheory.Measure (X → Bool)) [MeasureTheory.IsProbabilityMeasure D] :
    (scheme (Msg := Bool) enc 1).toVectorCommitment.PerfectlyComplete D :=
  perfectlyComplete_toVectorCommitment enc 1 D

/-- The query complexity is non-decreasing, so `qVC 2` also bounds an opening of one position. -/
example : Monotone (nonadaptiveCheck (Msg := Bool) enc 1).qVC := (nonadaptiveCheck enc 1).qVC_mono

/-- At depth `1`, an opening of both positions makes at most `2 · 2 = 4` checks. -/
example : (nonadaptiveCheck (Msg := Bool) enc 1).qVC 2 = 4 := rfl

/-- At depth `0`, the one opening lists at most `2 · 1 - 1 = 1` distinct pair. -/
example (rt : Bool) (ans : PartialVec 1 Bool) (td : Td Bool Bool 0) (io : List (X × Bool))
    (h : pairs enc 0 rt ans (opening 0 ans.dom td) = some io) : io.length ≤ 1 :=
  length_pairs_opening_le enc rt ans _ td io h

/-! ## An honest commitment, opened and checked -/

/-- A hash function that tells nodes and leaves apart and is not symmetric in its arguments. -/
def H : X → Bool
  | .inl (a, b) => a && !b
  | .inr (m, γ) => m != γ

/-- The committed message `(true, false)`. -/
def msg : Fin 2 → Bool := ![true, false]

/-- The salts `(false, false)`. -/
def salts : Fin 2 → Bool := ![false, false]

/-- The leaf labels are `H (true, false) = true` and `H (false, false) = false`, and the root is
`H (true, false) = true`. -/
example : (honestTree enc 1 H msg salts).1 = true := by decide

/-- Opening both positions lists three distinct pairs: the two leaf pairs, and the root pair,
which both paths share, once. -/
example : (pairs enc 1 (honestTree enc 1 H msg salts).1 (PartialVec.restrict msg Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2)).map List.length = some 3 := by
  decide

/-- The honest opening of both positions passes the check. -/
example : (nonadaptiveCheck enc 1).checkOn (fun x ↦ some (H x)) (honestTree enc 1 H msg salts).1
    (PartialVec.restrict msg Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2) = true := by decide

/-- A wrong answer is rejected. -/
example : (nonadaptiveCheck enc 1).checkOn (fun x ↦ some (H x)) (honestTree enc 1 H msg salts).1
    (PartialVec.restrict ![false, false] Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2) = false := by decide

/-! ## Extraction from an explicit database -/

/-- The database of the honest tree above: the two leaf queries and the root query. -/
def D : Database X Bool
  | .inr (true, false) => some true
  | .inr (false, false) => some false
  | .inl (true, false) => some true
  | _ => none

/-- `MTExtract(true, D)` recovers the message and the salts. -/
example : (extract enc 1 true D).1 = ![some true, some false] := by decide

example : (extract enc 1 true D).2.1 = ![some false, some false] := by decide

/-- The extracted labels: the root, then the leaf labels. -/
example : (extract enc 1 true D).2.2.get
    (SkeletonLeafIndex.perfectEquiv 1 0).toNodeIndex = some true ∧
    (extract enc 1 true D).2.2.get
      (SkeletonLeafIndex.perfectEquiv 1 1).toNodeIndex = some false := by
  decide

/-- From the root `false`, which has no node-shaped preimage in `D` (its only preimage is the leaf
input `(false, false)`), nothing is extracted. -/
example : (extract enc 1 false D).1 = fun _ ↦ none := by decide

/-- The extracted message passes the check on its domain (Thm 8.4 condition 3). -/
example : (nonadaptiveCheck enc 1).checkOn D true (extract enc 1 true D).1
    (opening 1 (extract enc 1 true D).1.dom (extract enc 1 true D).2) = true :=
  extract_valid enc 1 true D

/-- Lemma 8.6 on the empty database, whose half-preimages are empty: an entry with output
`false ≠ rt` does not change the extraction from `true`. -/
example : extract enc 1 true (Function.update Database.empty (.inl (true, true)) (some false)) =
    extract enc 1 true Database.empty :=
  extract_eq_of_not_mem enc rfl (by simp [SaltedMerkle.halfPreimages,
    MerkleTreeExtractor.halfPreimages, Database.empty])

/-- An entry whose output is the root can change the extraction: after adding
`(false, true) ↦ true`, the root `true` has the lexicographically first preimage `(false, true)`,
and the leaves swap. -/
example : (extract enc 1 true (Function.update D (.inl (false, true)) (some true))).1 =
    ![some false, some true] := by decide

/-! ## Typed perfect trees and prescribed checks -/

/-- The depth-zero trapdoor stores its only leaf at the root. -/
example : (honestTree enc 0 H (fun _ => true) (fun _ => false)).2.2 =
    FullData.leaf (some true) := rfl

/-- Depth-one labels are stored in the shared typed tree representation. -/
example : (honestTree enc 1 H msg salts).2.2 =
    FullData.internal (some true) (.leaf (some true)) (.leaf (some false)) := rfl

/-- Index zero selects the left child and index one the right child. -/
example : SkeletonLeafIndex.perfectEquiv 1 0 = .ofLeft .ofLeaf ∧
    SkeletonLeafIndex.perfectEquiv 1 1 = .ofRight .ofLeaf := ⟨rfl, rfl⟩

/-- The high bit is read first at depth two. -/
example : SkeletonLeafIndex.perfectEquiv 2 1 = .ofLeft (.ofRight .ofLeaf) ∧
    SkeletonLeafIndex.perfectEquiv 2 2 = .ofRight (.ofLeft .ofLeaf) := ⟨rfl, rfl⟩

/-- Leaf data transported across the public equivalence recovers the original message. -/
example (i : Fin 2) :
    (LeafData.ofFun (Skeleton.perfect 1)
      (fun j => msg ((SkeletonLeafIndex.perfectEquiv 1).symm j))).get
        (SkeletonLeafIndex.perfectEquiv 1 i) = msg i := by simp

/-- The shared pure builder and the salted honest tree agree at every node. -/
example : (honestTree enc 1 H msg salts).2.2 =
    (InductiveMerkleTree.buildMerkleTreeWithHash
      (LeafData.ofFun (Skeleton.perfect 1) fun i =>
        H (enc.leaf () (msg ((SkeletonLeafIndex.perfectEquiv 1).symm i),
          salts ((SkeletonLeafIndex.perfectEquiv 1).symm i))))
      (fun a b => H (enc.node () (a, b)))).map some := rfl

/-- An absent salt prevents an answered leaf from opening. -/
example : checkOn enc 1 (fun x => some (H x)) true (PartialVec.restrict msg {0})
    (opening 1 {0} ((fun _ => none), (honestTree enc 1 H msg salts).2.2)) = false := by
  decide

/-- Swapping the path label and sibling falsifies the prescribed root check. -/
example : checkOn enc 1 (fun x => some (H x)) true (PartialVec.restrict msg {0})
    ![some ⟨false, ⟨[(false, true)], rfl⟩⟩, none] = false := by decide

/-- An entry outside the answer domain is rejected even when its hash checks are honest. -/
example : pairs enc 1 true (PartialVec.restrict msg {0})
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2) = none := by decide

/-- A singleton opening queries the leaf before its parent. -/
example : pairs enc 1 true (PartialVec.restrict msg {0})
    (opening 1 {0} (honestTree enc 1 H msg salts).2) =
    some [(enc.leaf () (true, false), true), (enc.node () (true, false), true)] := by decide

/-- At depth two the leaf comes first, followed by the root and then its child. -/
example : leafIO enc true (0 : Fin 4) false
    ⟨false, ⟨[(true, false), (false, true)], rfl⟩⟩ =
    [(enc.leaf () (false, false), false), (enc.node () (true, false), true),
      (enc.node () (false, true), true)] := by decide

/-- Right edges preserve sibling orientation after placing the leaf first. -/
example : leafIO enc true (3 : Fin 4) false
    ⟨false, ⟨[(true, false), (false, true)], rfl⟩⟩ =
    [(enc.leaf () (false, false), false), (enc.node () (false, true), true),
      (enc.node () (true, false), true)] := by decide

/-- Two openings share the root pair; deduplication keeps it only once. -/
example : pairs enc 1 true (PartialVec.restrict msg Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2) =
    some [(enc.leaf () (true, false), true), (enc.leaf () (false, false), false),
      (enc.node () (true, false), true)] := by decide

/-- An extracted empty table knows the claimed root, unlike the repeated-index bottom. -/
example : (extract enc 0 true Database.empty).2.2.getRootValue = some true ∧
    (tdBot : Td Bool Bool 0).2.getRootValue = none := ⟨rfl, rfl⟩

/-- With an empty answer domain, the empty opening has no checks. -/
example : pairs enc 0 true (fun _ => none) (opening 0 ∅ tdBot) = some [] := by decide

/-! ## Overlapping oracle roles and ordered collisions -/

/-- Leaf and node encodings have identical ranges. -/
def overlapEnc : QueryEncoding (Bool × Bool) Unit Unit (Bool × Bool) Bool where
  leaf _ := id
  node _ := id
  leaf_injective _ := Function.injective_id
  node_injective _ := Function.injective_id

/-- Both roles issue exactly the same physical query. -/
example : overlapEnc.queryImpl (.leaf () (false, true)) =
    overlapEnc.queryImpl (.node () false true) := rfl

/-- The same input can be decoded in either role. -/
def overlapDecoder : RoleDecoder (overlapEnc.node ()) where
  decode := some
  decode_encode _ := rfl
  encode_decode _ _ h := (Option.some.inj h).symm

/-- A single supported input serves both roles. -/
def overlapD : Database (Bool × Bool) Bool
  | (false, true) => some true
  | _ => none

/-- Node recovery and leaf recovery read the same database cell. -/
example : MerkleTreeExtractor.resolvePair (overlapEnc.node ()) overlapD true = some (false, true) ∧
    MerkleTreeExtractor.resolvePair (overlapEnc.leaf ()) overlapD true = some (false, true) := by
  decide

/-- The shared cell supplies a child pair and the payload of the reached right leaf. -/
example : (extract overlapEnc 1 true overlapD).1 = ![none, some false] ∧
    (extract overlapEnc 1 true overlapD).2.1 = ![none, some true] := by decide

/-- Overlap preserves validity of the generated labelled opening. -/
example : checkOn overlapEnc 1 overlapD true (extract overlapEnc 1 true overlapD).1
    (opening 1 (extract overlapEnc 1 true overlapD).1.dom
      (extract overlapEnc 1 true overlapD).2) = true := by decide

/-- A collisionful table presents two candidates in each role. -/
def collisionD : Database (Bool × Bool) Bool
  | (false, true) | (true, false) => some true
  | _ => none

/-- Candidate ordering chooses `(false, true)` in both roles despite the collision. -/
example : MerkleTreeExtractor.resolvePair (overlapEnc.node ()) collisionD true =
    some (false, true) ∧
    MerkleTreeExtractor.resolvePair (overlapEnc.leaf ()) collisionD true =
      some (false, true) := by decide

/-- Depth-zero extraction uses the same least leaf candidate. -/
example : (extract overlapEnc 0 true collisionD).1 = ![some false] ∧
    (extract overlapEnc 0 true collisionD).2.1 = ![some true] := by decide

/-- The collision is real: distinct actual inputs have the same response. -/
example : collisionD (false, true) = some true ∧ collisionD (true, false) = some true ∧
    (false, true) ≠ (true, false) := by decide

/-- Fresh insertion at another response preserves selection on a collisionful table. -/
example : MerkleTreeExtractor.resolvePair (overlapEnc.node ())
    (Function.update collisionD (true, true) (some false)) true =
      MerkleTreeExtractor.resolvePair (overlapEnc.node ()) collisionD true := by decide

/-! ## Randomized algorithms in the general interface -/

/-- A toy commitment whose `Open` appends a fresh, ignored coin and whose `Check` tosses a coin on
a malformed proof. Neither algorithm is deterministic, and the general interface holds it. -/
def coinVC : VectorCommitment Bool Bool Bool Unit Unit (Bool × Bool) 1 where
  commit _ := pure ((), ())
  opening _ _ := do
    let b ← $ᵗ Bool
    pure (true, b)
  check _ _ pf := if pf.1 then pure true else OracleComp.liftComp ($ᵗ Bool) _

/-- The toy commitment is perfectly complete against every oracle function, hence for every oracle
distribution. -/
theorem coinVC_perfectlyCompleteForAll : coinVC.PerfectlyCompleteForAll := by
  intro H m Q b hb
  revert hb
  simp [VectorCommitment.completenessExp, coinVC]

example (D : MeasureTheory.Measure (Bool → Bool)) [MeasureTheory.IsProbabilityMeasure D] :
    coinVC.PerfectlyComplete D :=
  coinVC_perfectlyCompleteForAll.perfectlyComplete D

/-! ## Universe canaries -/

/-- Commitment tuples over a type in `Type 1` are finite. -/
example : Fintype (TpIC 2 (ULift.{1} Bool)) := inferInstance

/-- Pairs of tuples with commitments and decommitments in different universes are finite. -/
example : Fintype (TpICD 2 (ULift.{1} Bool) fun _ ↦ ULift.{2} Bool) := inferInstance

/-- A multi-extractor with commitments, decommitments and states in three nonzero universes. -/
example : MultiExtractor 2 (ULift.{1} Bool) (fun _ ↦ ULift.{2} Bool) (ULift.{3} Unit) :=
  ⟨fun _ _ _ ↦ ⟨true⟩⟩

/-- The tagged encoding with every type lifted to a nonzero universe. -/
def encU : QueryEncoding (ULift.{1} X) Unit Unit
    (ULift.{3} Bool × ULift.{4} Bool) (ULift.{2} Bool) where
  node _ c := ⟨enc.node () (c.1.down, c.2.down)⟩
  leaf _ p := ⟨enc.leaf () (p.1.down, p.2.down)⟩
  node_injective _ := by
    rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨e⟩⟩ h
    simp_all [enc]
  leaf_injective _ := by
    rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨e⟩⟩ h
    simp_all [enc]

/-- `MTMultiExtract` over the lifted encoding is an admissible multi-extractor. -/
example : (multiExtract encU (k := 2) fun _ ↦ 1).Admissible fun _ ↦ (fun _ ↦ none, tdBot) :=
  multiExtract_admissible encU _

/-- An encoding with labels and salts in `Type 1`, oracle inputs in `Type 2` and messages in
`Type 3`. -/
def encY : QueryEncoding (ULift.{2} X) Unit Unit
    (ULift.{3} Bool × ULift.{1} Bool) (ULift.{1} Bool) where
  node _ c := ⟨enc.node () (c.1.down, c.2.down)⟩
  leaf _ p := ⟨enc.leaf () (p.1.down, p.2.down)⟩
  node_injective _ := by
    rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨e⟩⟩ h
    simp_all [enc]
  leaf_injective _ := by
    rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨e⟩⟩ h
    simp_all [enc]

/-- `commitTree` with labels and salts in `Type 1`, answered by a fixed function, gives the
honest root and trapdoor. -/
example (H : ULift.{2} X → ULift.{1} Bool) (msg : Fin (2 ^ 1) → ULift.{3} Bool)
    (γ : Fin (2 ^ 1) → ULift.{1} Bool) :
    simulateQ (fun x ↦ (pure (H x) : Id (ULift.{1} Bool))) (commitTree encY 1 msg γ) =
      pure (honestTree encY 1 H msg γ) :=
  simulateQ_commitTree encY 1 H msg γ

/-- An encoding whose oracle input type `X` lives in `Type 1`; the answers and salts are bits. -/
def encX : QueryEncoding (ULift.{1} X) Unit Unit (ULift.{2} Bool × Bool) Bool where
  node _ c := ⟨enc.node () c⟩
  leaf _ p := ⟨enc.leaf () (p.1.down, p.2)⟩
  node_injective _ := fun _ _ h ↦ (enc.node_injective ()) (congrArg ULift.down h)
  leaf_injective _ := by
    rintro ⟨⟨a⟩, b⟩ ⟨⟨c⟩, e⟩ h
    simp_all [enc]

/-- The salted Merkle scheme over an oracle with inputs in `Type 1` and messages in `Type 2` is
perfectly complete for every oracle distribution. -/
example (D : MeasureTheory.Measure (ULift.{1} X → Bool))
    [MeasureTheory.IsProbabilityMeasure D] :
    (scheme (Msg := ULift.{2} Bool) encX 1).toVectorCommitment.PerfectlyComplete D :=
  perfectlyComplete_toVectorCommitment encX 1 D

/-! ## Half-preimages over an infinite oracle domain -/

/-- The tagged encoding into an oracle domain with an unused infinite summand. -/
def encN : QueryEncoding (X ⊕ ℕ) Unit Unit (Bool × Bool) Bool where
  node _ c := .inl (enc.node () c)
  leaf _ p := .inl (enc.leaf () p)
  node_injective _ := Sum.inl_injective.comp (enc.node_injective ())
  leaf_injective _ := Sum.inl_injective.comp (enc.leaf_injective ())

/-- `|HP(D)| ≤ 2 |dom D|` for a database with finite support over the infinite domain `X ⊕ ℕ`. -/
example (D : Database (X ⊕ ℕ) Bool) (hD : {x | D x ≠ none}.Finite) :
    (halfPreimages encN D).ncard ≤ 2 * {x | D x ≠ none}.ncard :=
  ncard_halfPreimages_le encN D hD

end VCVioTest.SaltedMerkleCanary
