/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Salted.Commutativity
public import VCVio.CryptoFoundations.MerkleTree.Salted.Extraction

/-!
# Tests for salted Merkle trees

Toy instances of the salted Merkle commitment of ePrint 2025/2166, Def 8.2, with one-bit labels,
messages and salts and tagged oracle inputs:

* depths `d = 0` and `d = 1`, with their `CheckIO` forms and perfect completeness;
* an honest commitment for an explicit hash function, opened and checked by evaluation;
* `MTExtract` evaluated on a small explicit database, its validity, and Lemma 8.6 on it;
* `Conditions` at depths one and two, concrete P2, sharp P3, and the seven-cell extraction bound.
-/

public section

namespace VCVioTest.SaltedMerkleCanary

open SaltedMerkle Quantum

/-- Tagged inputs: node inputs on the left, leaf inputs `(m, γ)` on the right. -/
abbrev X := (Bool × Bool) ⊕ (Bool × Bool)

/-- The tagged encoding. -/
def enc : Encoding X Bool Bool Bool where
  node := Sum.inl
  leaf := Sum.inr
  node_injective := Sum.inl_injective
  leaf_injective := Sum.inr_injective

/-! ## Depths `0` and `1` -/

example : DetVectorCommitment X Bool Bool Bool (Td Bool Bool 0) (Pf Bool Bool 0) 1 := scheme enc 0

example : VectorCommitment X Bool Bool Bool (Td Bool Bool 1) (Pf Bool Bool 1) 2 :=
  (scheme enc 1).toVectorCommitment

example : (scheme (Msg := Bool) enc 0).PerfectlyComplete := perfectlyComplete enc 0

example : (scheme (Msg := Bool) enc 1).PerfectlyComplete := perfectlyComplete enc 1

/-- Perfect completeness relative to an arbitrary oracle distribution (Def 3.7). -/
example (D : MeasureTheory.Measure (X → Bool)) [MeasureTheory.IsProbabilityMeasure D] :
    (scheme (Msg := Bool) enc 1).toVectorCommitment.PerfectlyComplete D :=
  perfectlyComplete_toVectorCommitment enc 1 D

/-- The query complexity is non-decreasing, so `qVC 2` also bounds an opening of one position. -/
example : Monotone (checkIOForm (Msg := Bool) enc 1).qVC := (checkIOForm enc 1).qVC_mono

/-- At depth `1`, an opening of both positions makes at most `2 · 2 = 4` checks. -/
example : (checkIOForm (Msg := Bool) enc 1).qVC 2 = 4 := rfl

/-- At depth `0`, the one opening lists at most `2 · 1 - 1 = 1` distinct pair. -/
example (rt : Bool) (ans : PartialVec 1 Bool) (td : Td Bool Bool 0) (io : List (X × Bool))
    (h : outputIO enc 0 rt ans (opening 0 ans.dom td) = some io) : io.length ≤ 1 :=
  length_outputIO_opening_le enc rt ans _ td io h

/-! ## Conditions and the extraction cell bound -/

/-- The sufficient conditions elaborate for two trees of depths one and two. -/
example : Conditions (fun i : Fin 2 ↦ (scheme enc (![1, 2] i)).toVectorCommitment)
    (fun i ↦ checkIOForm enc (![1, 2] i)) (multiExtract enc ![1, 2])
    (fun _ ↦ tdBot) collisionFree := conditions enc ![1, 2]

/-- The depth-two extraction bound is seven cells, while arbitrary paths allow twelve. -/
example : 2 * 2 ^ 2 - 1 = 7 ∧ (checkIOForm enc 2).qVC 4 = 12 := by decide

/-- The seven-cell bound applies to every proof read from one depth-two trapdoor. -/
example (rt : Bool) (ans : PartialVec 4 Bool) (td : Td Bool Bool 2) (io : List (X × Bool))
    (h : outputIO enc 2 rt ans (opening 2 ans.dom td) = some io) : io.length ≤ 7 :=
  length_outputIO_opening_le enc rt ans _ td io h

/-! ## Concrete P2 -/

/-- A tagged encoding with three possible hash outputs. -/
def enc3 : Encoding ((ZMod 3 × ZMod 3) ⊕ (Bool × Bool)) (ZMod 3) Bool Bool where
  node := Sum.inl
  leaf := Sum.inr
  node_injective := Sum.inl_injective
  leaf_injective := Sum.inr_injective

noncomputable local instance :
    OracleSpec.UniformAnswerMeasure (((ZMod 3 × ZMod 3) ⊕ (Bool × Bool)) →ₒ ZMod 3) :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _

local instance : LinearOrder (ZMod 3) := inferInstanceAs (LinearOrder (Fin 3))

/-- P2 elaborates for two depth-one trees and every valid encoding of their extractions. -/
example {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (code : TpDCode 2 (DmOf (fun _ ↦ 2 ^ 1) Bool fun _ ↦ Td (ZMod 3) Bool 1) Z) :
    ComBound.{0, 0} (compressedVCOracle 2 ((ZMod 3 × ZMod 3) ⊕ (Bool × Bool)) (ZMod 3))
      (multiExtract enc3 (fun _ ↦ 1)) code
      (SaltedMerkle.comErrorBound (Y := ZMod 3)) :=
  SaltedMerkle.comBound (k := 2) (Z := Z) enc3 (fun _ ↦ 1) code

/-- The universal cap is active for three possible hash outputs. -/
example : SaltedMerkle.comErrorBound (Y := ZMod 3) 0 = 4 := by
  norm_num [SaltedMerkle.comErrorBound, ZMod.card]
  norm_num [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le]

/-- With 97 outputs and no prior calls the constant-24 estimate is active. -/
example : SaltedMerkle.comErrorBound (Y := ZMod 97) 0 = 24 / 97 := by
  norm_num [SaltedMerkle.comErrorBound, ZMod.card]
  rw [← div_eq_mul_inv, min_eq_right]
  norm_num [ENNReal.div_le_iff]

/-! ## Sharp P3 -/

/-- P3 for two depth-two trees uses seven cells per opening, with exponent `14n`. -/
example {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (code : TpDCode 2 (DmOf (fun _ ↦ 2 ^ 2) Bool fun _ ↦ Td (ZMod 3) Bool 2) Z) :
    ExtractionCorrect.{0, 0} (fun _ : Fin 2 ↦ (scheme enc3 2).toVectorCommitment)
      (compressedVCOracle 2 ((ZMod 3 × ZMod 3) ⊕ (Bool × Bool)) (ZMod 3))
      (multiExtract enc3 (fun _ ↦ 2)) code
      (fun _ _ _ n ↦ ENNReal.ofReal (1 - (1 - (3 : ℝ)⁻¹) ^ (2 * n * 7))) :=
  extractionCorrect_uniformDepth enc3 2 code

/-- The same sharp bound permits a family with different depths and at most four leaves each. -/
example {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (code : TpDCode 2 (DmOf (fun i ↦ 2 ^ (![1, 2] i)) Bool
      fun i ↦ Td (ZMod 3) Bool (![1, 2] i)) Z) :
    ExtractionCorrect.{0, 0} (fun i : Fin 2 ↦ (scheme enc3 (![1, 2] i)).toVectorCommitment)
      (compressedVCOracle 2 ((ZMod 3 × ZMod 3) ⊕ (Bool × Bool)) (ZMod 3))
      (multiExtract enc3 ![1, 2]) code
      (fun _ _ _ n ↦ SaltedMerkle.extractErrorBound (Y := ZMod 3) 4 n) :=
  extractionCorrect enc3 ![1, 2] code 4 (by intro i; fin_cases i <;> decide)

/-- One depth-one opening with three possible outputs has exact bound `1 - (2/3)^6`. -/
example : SaltedMerkle.extractErrorBound (Y := ZMod 3) 2 1 = ENNReal.ofReal (665 / 729) := by
  norm_num [SaltedMerkle.extractErrorBound, ZMod.card]

/-- Checking no openings incurs zero extraction error. -/
example (L : ℕ) : SaltedMerkle.extractErrorBound (Y := ZMod 3) L 0 = 0 := by
  simp [SaltedMerkle.extractErrorBound]

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
example : (outputIO enc 1 (honestTree enc 1 H msg salts).1 (PartialVec.restrict msg Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2)).map List.length = some 3 := by
  decide

/-- The honest opening of both positions passes the check. -/
example : (checkIOForm enc 1).checkOn (fun x ↦ some (H x)) (honestTree enc 1 H msg salts).1
    (PartialVec.restrict msg Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2) = true := by decide

/-- A wrong answer is rejected. -/
example : (checkIOForm enc 1).checkOn (fun x ↦ some (H x)) (honestTree enc 1 H msg salts).1
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
example : labelAt (extract enc 1 true D).2.2 1 0 = some true ∧
    labelAt (extract enc 1 true D).2.2 1 1 = some false := by decide

/-- From the root `false`, which has no node-shaped preimage in `D` (its only preimage is the leaf
input `(false, false)`), nothing is extracted. -/
example : (extract enc 1 false D).1 = fun _ ↦ none := by decide

/-- The extracted message passes the check on its domain (Thm 8.4 condition 3). -/
example : (checkIOForm enc 1).checkOn D true (extract enc 1 true D).1
    (opening 1 (extract enc 1 true D).1.dom (extract enc 1 true D).2) = true :=
  extract_valid enc 1 true D

/-- Lemma 8.6 on the empty database, whose half-preimages are empty: an entry with output
`false ≠ rt` does not change the extraction from `true`. -/
example : extract enc 1 true (Function.update Database.empty (.inl (true, true)) (some false)) =
    extract enc 1 true Database.empty :=
  extract_eq_of_not_mem enc rfl (by simp [halfPreimages, Database.empty])

/-- An entry whose output is the root can change the extraction: after adding
`(false, true) ↦ true`, the root `true` has the lexicographically first preimage `(false, true)`,
and the leaves swap. -/
example : (extract enc 1 true (Function.update D (.inl (false, true)) (some true))).1 =
    ![some false, some true] := by decide

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
def encU : Encoding (ULift.{1} X) (ULift.{2} Bool) (ULift.{3} Bool) (ULift.{4} Bool) where
  node c := ⟨enc.node (c.1.down, c.2.down)⟩
  leaf p := ⟨enc.leaf (p.1.down, p.2.down)⟩
  node_injective := by
    rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨e⟩⟩ h
    simp_all [enc]
  leaf_injective := by
    rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨e⟩⟩ h
    simp_all [enc]

/-- `MTMultiExtract` over the lifted encoding is an admissible multi-extractor. -/
example : (multiExtract encU (k := 2) fun _ ↦ 1).Admissible fun _ ↦ (fun _ ↦ none, tdBot) :=
  multiExtract_admissible encU _

/-- An encoding with labels and salts in `Type 1`, oracle inputs in `Type 2` and messages in
`Type 3`. -/
def encY : Encoding (ULift.{2} X) (ULift.{1} Bool) (ULift.{3} Bool) (ULift.{1} Bool) where
  node c := ⟨enc.node (c.1.down, c.2.down)⟩
  leaf p := ⟨enc.leaf (p.1.down, p.2.down)⟩
  node_injective := by
    rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨e⟩⟩ h
    simp_all [enc]
  leaf_injective := by
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
def encX : Encoding (ULift.{1} X) Bool (ULift.{2} Bool) Bool where
  node c := ⟨enc.node c⟩
  leaf p := ⟨enc.leaf (p.1.down, p.2)⟩
  node_injective := fun _ _ h ↦ enc.node_injective (congrArg ULift.down h)
  leaf_injective := by
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
def encN : Encoding (X ⊕ ℕ) Bool Bool Bool where
  node c := .inl (enc.node c)
  leaf p := .inl (enc.leaf p)
  node_injective := Sum.inl_injective.comp enc.node_injective
  leaf_injective := Sum.inl_injective.comp enc.leaf_injective

/-- `|HP(D)| ≤ 2 |dom D|` for a database with finite support over the infinite domain `X ⊕ ℕ`. -/
example (D : Database (X ⊕ ℕ) Bool) (hD : {x | D x ≠ none}.Finite) :
    (halfPreimages encN D).ncard ≤ 2 * {x | D x ≠ none}.ncard :=
  ncard_halfPreimages_le encN D hD

end VCVioTest.SaltedMerkleCanary
