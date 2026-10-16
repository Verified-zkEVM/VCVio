/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.MultiExtractor
public import VCVio.Quantum.Oracle.Compressed.CommutatorSharp
public import VCVio.Quantum.Oracle.Emulated

/-!
# The purified extractor and the record unitaries

The unitaries of Def 7.2 of Chiesa, Di, Hu and Zheng (ePrint 2025/2166, §7, pp. 49–50):

* `U_MultiExtract` (p. 49) on `(TpIC × Z) × S`: controlled on a commitment tuple `tic` and a
  basis state `s` of the oracle's private register, it adds an encoding of `MultiExtract(tic, s)`
  to the output register `Z` (`Quantum.extractUnitary`);
* `Record(U)` (pp. 49–50) on `(TpIC × Yr) × (S × R)`: controlled on `tic`, it applies `U` to the
  register `Yr` and the cell `R_tic` of the recording register (`Quantum.recordUnitary`);
* `Record(MultiExtract, U)` (p. 50): controlled on `tic` and `s`, it applies `U` to `Yr` and
  the cell `R_(tic, MultiExtract(tic, s))` (`Quantum.recordMEUnitary`).

## Encodings

The paper writes the extracted tuple into its output register by XOR with a bit string
(p. 49). Here the output register is any type `Z` with an additive group structure, and a
`Quantum.TpDCode` is an injective encoding `TpD k Dm → Z`; the paper's case is
`Z = Fin N → ZMod 2`. The encoding has no decoder field: a total decoder `Z → TpD k Dm` would not
exist when `TpD k Dm` is empty. Decoding is the partial inverse `Quantum.TpDCode.decodeAt`. The
default encoding (`Quantum.TpDCode.ofFintype`) writes into `ZMod (card (TpD k Dm) + 1)`.

## Main definitions

* `Quantum.onFactor e M`: the matrix `M` applied to one factor of a register split by `e`.
* `Quantum.TpDCode`, `Quantum.TpDCode.ofEmbedding`, `Quantum.TpDCode.ofFintype`,
  `Quantum.TpDCode.decodeAt`.
* `Quantum.extractPerm`, `Quantum.extractUnitary`, `Quantum.extractBlock`.
* `Quantum.RecReg`, `Quantum.cellControlled`, `Quantum.recordUnitary`, `Quantum.recordMEUnitary`.

## Main results

* `Quantum.extractUnitary_mem_unitaryGroup`, `Quantum.recordUnitary_mem_unitaryGroup`,
  `Quantum.recordMEUnitary_mem_unitaryGroup`.
* `Quantum.extractUnitary_eq_sum_labelControlled`: for a fixed tuple, `U_MultiExtract` is
  label-controlled by `s ↦ MultiExtract(tic, s)` with members `1 ⊗ xorShift z`. This is the form of
  the purified measurements of Cor 5.6 (p. 31).
-/

public section

open Matrix
open scoped Kronecker

universe u v w

namespace Quantum

/-! ## Basis permutations and placement on a factor -/

section onFactor

/-- The basis matrix of a bijection is unitary. -/
theorem basisMatrix_perm_mem_unitaryGroup {A : Type*} [Fintype A] [DecidableEq A]
    (e : Equiv.Perm A) : basisMatrix e ∈ unitaryGroup A ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact conjTranspose_basisMatrix_mul_self e.injective

variable {n A R : Type*} [DecidableEq R]

/-- The matrix `M` on the factor `A` of a register split as `A × R` by `e`, and the identity on
the rest `R`. -/
@[expose]
def onFactor (e : n ≃ A × R) (M : Matrix A A ℂ) : Matrix n n ℂ :=
  reindex e.symm e.symm (M ⊗ₖ (1 : Matrix R R ℂ))

/-- The entries of `onFactor e M`. -/
theorem onFactor_apply (e : n ≃ A × R) (M : Matrix A A ℂ) (a b : n) :
    onFactor e M a b = if (e a).2 = (e b).2 then M (e a).1 (e b).1 else 0 := by
  simp [onFactor, one_apply]

/-- `onFactor e M` does not change the rest of the register. -/
theorem eq_of_onFactor_apply_ne_zero {e : n ≃ A × R} {M : Matrix A A ℂ} {a b : n}
    (h : onFactor e M a b ≠ 0) : (e a).2 = (e b).2 := by
  by_contra hne
  exact h (by simp [onFactor_apply, hne])

variable [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A] [Finite R]

/-- A unitary on one factor is a unitary on the register. -/
theorem onFactor_mem_unitaryGroup (e : n ≃ A × R) {M : Matrix A A ℂ}
    (hM : M ∈ unitaryGroup A ℂ) : onFactor e M ∈ unitaryGroup n ℂ := by
  have := Fintype.ofFinite R
  exact reindex_mem_unitaryGroup _ (kronecker_mem_unitary hM (one_mem _))

omit [DecidableEq n] [DecidableEq A] in
/-- Placement on a factor is multiplicative. -/
theorem onFactor_mul (e : n ≃ A × R) (M N : Matrix A A ℂ) :
    onFactor e (M * N) = onFactor e M * onFactor e N := by
  have := Fintype.ofFinite R
  simp only [onFactor, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one]

omit [Fintype n] [Fintype A] [Finite R] in
/-- Placement on a factor sends the identity to the identity. -/
@[simp]
theorem onFactor_one (e : n ≃ A × R) : onFactor e (1 : Matrix A A ℂ) = 1 := by
  simp [onFactor]

end onFactor

/-! ## Encodings of decommitment tuples -/

/-- An injective encoding of decommitment tuples into the output register `Z` of
`U_MultiExtract`. The paper XORs a bit encoding (ePrint 2025/2166, p. 49); any injective
map into an additive group serves the same purpose. There is no decoder field, since a total
decoder would not exist for an empty `TpD k Dm`; see `Quantum.TpDCode.decodeAt`. -/
structure TpDCode (k : ℕ) (Dm : Fin k → Type v) (Z : Type w) where
  /-- The encoding of a decommitment tuple. -/
  enc : TpD k Dm → Z
  /-- Distinct tuples have distinct encodings. -/
  enc_injective : Function.Injective enc

namespace TpDCode

variable {k : ℕ} {Dm : Fin k → Type v} {Z : Type w}

/-- The encoding along an embedding. -/
@[expose]
def ofEmbedding (f : TpD k Dm ↪ Z) : TpDCode k Dm Z :=
  ⟨f, f.injective⟩

/-- The default encoding of finite decommitment tuples, into `ZMod (card (TpD k Dm) + 1)` along
`Fintype.equivFin`. The extra element keeps the register finite and nonempty when `TpD k Dm` is
empty. -/
@[expose]
noncomputable def ofFintype [∀ i, Fintype (Dm i)] :
    TpDCode k Dm (ZMod (Fintype.card (TpD k Dm) + 1)) :=
  ofEmbedding ((Fintype.equivFin (TpD k Dm)).toEmbedding.trans Fin.castSuccEmb)

/-- The default encoding. -/
noncomputable instance [∀ i, Fintype (Dm i)] :
    Inhabited (TpDCode k Dm (ZMod (Fintype.card (TpD k Dm) + 1))) :=
  ⟨ofFintype⟩

variable (code : TpDCode k Dm Z)

/-- Decoding at a given length: the tuple of length `j` whose encoding is `z`, if there is one. -/
@[expose]
noncomputable def decodeAt (j : TupleLen k) (z : Z) : Option (TpDLen k Dm j) :=
  open Classical in
  if h : ∃ t : TpDLen k Dm j, code.enc ⟨j, t⟩ = z then some h.choose else none

/-- Encodings of tuples of the same length are equal only for equal tuples. -/
theorem enc_mk_inj {j : TupleLen k} {t t' : TpDLen k Dm j} :
    code.enc ⟨j, t⟩ = code.enc ⟨j, t'⟩ ↔ t = t' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  exact eq_of_heq (Sigma.mk.inj (code.enc_injective h)).2

/-- `decodeAt j z = some t` exactly when `z` encodes `t`. -/
theorem decodeAt_eq_some_iff {j : TupleLen k} {z : Z} {t : TpDLen k Dm j} :
    code.decodeAt j z = some t ↔ code.enc ⟨j, t⟩ = z := by
  unfold decodeAt
  split_ifs with h
  · refine ⟨fun e ↦ ?_, fun e ↦ ?_⟩
    · cases Option.some.inj e
      exact h.choose_spec
    · exact congrArg some ((code.enc_mk_inj).mp (h.choose_spec.trans e.symm))
  · exact ⟨fun e ↦ absurd e (by simp), fun e ↦ absurd ⟨t, e⟩ h⟩

/-- Decoding an encoding returns the tuple. -/
@[simp]
theorem decodeAt_enc (j : TupleLen k) (t : TpDLen k Dm j) : code.decodeAt j (code.enc ⟨j, t⟩) =
    some t :=
  code.decodeAt_eq_some_iff.mpr rfl

end TpDCode

/-! ## The purified extractor -/

section extract

variable {k : ℕ} {Cm : Type u} {Dm : Fin k → Type v} {S : Type*} {Z : Type w}
  [AddGroup Z] (ME : MultiExtractor k Cm Dm S) (code : TpDCode k Dm Z)

/-- The basis permutation of `U_MultiExtract` (ePrint 2025/2166, p. 49):
`|tic, z⟩|s⟩ ↦ |tic, z + enc(MultiExtract(tic, s))⟩|s⟩`. -/
@[expose]
def extractPerm : Equiv.Perm ((TpIC k Cm × Z) × S) where
  toFun a := ((a.1.1, a.1.2 + code.enc ⟨a.1.1.1, ME.extract a.1.1 a.2⟩), a.2)
  invFun a := ((a.1.1, a.1.2 - code.enc ⟨a.1.1.1, ME.extract a.1.1 a.2⟩), a.2)
  left_inv a := by simp
  right_inv a := by simp

/-- The action of `extractPerm` on a basis state. -/
@[simp]
theorem extractPerm_apply (tic : TpIC k Cm) (z : Z) (s : S) :
    extractPerm ME code ((tic, z), s) = ((tic, z + code.enc ⟨tic.1, ME.extract tic s⟩), s) :=
  rfl

variable [Fintype Cm] [DecidableEq Cm] [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]

/-- **`U_MultiExtract`** (ePrint 2025/2166, Def 7.2, p. 49), the basis matrix of
`Quantum.extractPerm`. -/
@[expose]
noncomputable def extractUnitary : Matrix ((TpIC k Cm × Z) × S) ((TpIC k Cm × Z) × S) ℂ :=
  basisMatrix (extractPerm ME code)

omit [Fintype Cm] [Fintype S] [Fintype Z] in
/-- The entries of `U_MultiExtract`: `⟨(tic, z), s| U |(tic', z'), s'⟩` is one exactly when
`tic = tic'`, `s = s'` and `z = z' + enc(MultiExtract(tic', s'))`. -/
theorem extractUnitary_apply (tic tic' : TpIC k Cm) (z z' : Z) (s s' : S) :
    extractUnitary ME code ((tic, z), s) ((tic', z'), s') =
      if tic = tic' ∧ z = z' + code.enc ⟨tic'.1, ME.extract tic' s'⟩ ∧ s = s' then 1 else 0 := by
  simp only [extractUnitary, basisMatrix_apply, extractPerm_apply, Prod.mk.injEq, and_assoc]

/-- `U_MultiExtract` is unitary. -/
theorem extractUnitary_mem_unitaryGroup :
    extractUnitary ME code ∈ unitaryGroup ((TpIC k Cm × Z) × S) ℂ :=
  basisMatrix_perm_mem_unitaryGroup _

/-- The block of `U_MultiExtract` at a fixed tuple `tic`, on `S × Z`: label-controlled by
`s ↦ enc(MultiExtract(tic, s))`, with members `1 ⊗ xorShift z`. -/
@[expose]
noncomputable def extractBlock (tic : TpIC k Cm) : Matrix (S × Z) (S × Z) ℂ :=
  labelControlled (fun a ↦ code.enc ⟨tic.1, ME.extract tic a.1⟩) fun z ↦
    (1 : Matrix S S ℂ) ⊗ₖ xorShift Z z

/-- The regrouping `TpIC × (S × Z) ≃ (TpIC × Z) × S` used to place the blocks of
`U_MultiExtract`. -/
@[expose]
def extractRegroup : TpIC k Cm × (S × Z) ≃ (TpIC k Cm × Z) × S where
  toFun a := ((a.1, a.2.2), a.2.1)
  invFun a := (a.1.1, (a.2, a.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype S] [Fintype Z] in
/-- **`U_MultiExtract` is block diagonal in the tuple, with label-controlled blocks**:
`U_MultiExtract = ∑_tic |tic⟩⟨tic| ⊗ labelControlled (s ↦ enc(ME(tic, s))) (z ↦ 1 ⊗ xorShift z)`.
Each block has the form of the purified measurements of Cor 5.6 of ePrint 2025/2166
(p. 31): a labelling of the rest of the register, and an XOR shift on the output. -/
theorem extractUnitary_eq_sum_labelControlled :
    extractUnitary ME code = ∑ tic, reindex extractRegroup extractRegroup
      (single tic tic (1 : ℂ) ⊗ₖ extractBlock ME code tic) := by
  ext ⟨⟨t, z⟩, s⟩ ⟨⟨t', z'⟩, s'⟩
  rw [Matrix.sum_apply, Finset.sum_eq_single t (fun b _ hb ↦ by
    simp [extractRegroup, hb]) (by simp)]
  simp only [extractUnitary, basisMatrix_apply, extractPerm_apply, reindex_apply,
    submatrix_apply, extractRegroup, Equiv.coe_fn_symm_mk, kroneckerMap_apply, single_apply,
    extractBlock, labelControlled_apply, one_apply, xorShift_apply, Prod.mk.injEq]
  by_cases ht : t = t'
  · subst ht
    by_cases hs : s = s'
    · subst hs
      simp
    · simp [hs]
  · simp [ht]

end extract

/-! ## The record unitaries -/

section record

variable {Q Yr S Rg K Cell G : Type*} [DecidableEq K]

/-- Split off the register `Yr` and the cell `key` of a recording register `Rg ≅ (K → Cell) × G`
from `(Q × Yr) × (S × Rg)`. The rest keeps the control `Q`, the private register `S`, the other
cells and `G`. -/
@[expose]
def cellSplit (eR : Rg ≃ (K → Cell) × G) (key : K) :
    (Q × Yr) × (S × Rg) ≃ (Yr × Cell) × (Q × S × ({j // j ≠ key} → Cell) × G) where
  toFun a := ((a.1.2, (eR a.2.2).1 key),
    (a.1.1, a.2.1, fun j ↦ (eR a.2.2).1 j, (eR a.2.2).2))
  invFun b := ((b.2.1, b.1.1),
    (b.2.2.1, eR.symm ((Equiv.funSplitAt key Cell).symm (b.1.2, b.2.2.2.1), b.2.2.2.2)))
  left_inv a := by
    obtain ⟨⟨q, y⟩, s, r⟩ := a
    have h := (Equiv.funSplitAt key Cell).symm_apply_apply (eR r).1
    simp only [Equiv.funSplitAt_apply] at h
    simp [h]
  right_inv b := by
    obtain ⟨⟨y, c⟩, q, s, f, g⟩ := b
    simp only [Equiv.funSplitAt_symm_apply, Equiv.apply_symm_apply, Prod.mk.injEq, dite_true,
      true_and, and_true]
    exact funext fun j : {j // j ≠ key} ↦ by simp [j.2]

/-- The rest of `cellSplit` keeps the control and the private register. -/
theorem cellSplit_snd (eR : Rg ≃ (K → Cell) × G) (key : K) (a : (Q × Yr) × (S × Rg)) :
    ((cellSplit eR key a).2.1, (cellSplit eR key a).2.2.1) = (a.1.1, a.2.1) :=
  rfl

variable [Fintype Q] [DecidableEq Q] [Fintype Yr] [DecidableEq Yr] [Fintype S] [DecidableEq S]
  [Fintype Rg] [DecidableEq Rg] [Fintype K] [Fintype Cell] [DecidableEq Cell] [DecidableEq G]

/-- Apply `U` to `Yr` and the cell `β(q, s)` of the recording register, controlled on the
control `q` and the private register `s`. Both record unitaries of Def 7.2 have this form. -/
@[expose]
noncomputable def cellControlled (eR : Rg ≃ (K → Cell) × G) (β : Q × S → K)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) : Matrix ((Q × Yr) × (S × Rg)) ((Q × Yr) × (S × Rg)) ℂ :=
  labelControlled (fun a ↦ β (a.1.1, a.2.1)) fun key ↦ onFactor (cellSplit eR key) U

/-- A cell-controlled unitary is unitary. -/
theorem cellControlled_mem_unitaryGroup [Finite G] (eR : Rg ≃ (K → Cell) × G) (β : Q × S → K)
    {U : Matrix (Yr × Cell) (Yr × Cell) ℂ} (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    cellControlled eR β U ∈ unitaryGroup ((Q × Yr) × (S × Rg)) ℂ := by
  have := Fintype.ofFinite G
  refine labelControlled_mem_unitaryGroup (fun key a b h ↦ ?_)
    fun key ↦ onFactor_mem_unitaryGroup _ hU
  have e := eq_of_onFactor_apply_ne_zero h
  simp only [cellSplit, Equiv.coe_fn_mk, Prod.mk.injEq] at e
  simp only [e.1, e.2.1]

/-- The recording register `R` (ePrint 2025/2166, p. 49): one cell per commitment tuple
and one per pair of a commitment tuple and a decommitment tuple. -/
@[expose]
def RecReg (k : ℕ) (Cm : Type u) (Dm : Fin k → Type v) (Cell : Type w) : Type (max u v w) :=
  (TpIC k Cm → Cell) × (TpICD k Cm Dm → Cell)

variable {k : ℕ} {Cm : Type u} {Dm : Fin k → Type v} [Fintype Cm] [DecidableEq Cm]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]

/-- The recording register is finite. -/
instance : Fintype (RecReg k Cm Dm Cell) :=
  inferInstanceAs (Fintype ((TpIC k Cm → Cell) × (TpICD k Cm Dm → Cell)))

/-- The recording register has decidable equality. -/
instance : DecidableEq (RecReg k Cm Dm Cell) :=
  inferInstanceAs (DecidableEq ((TpIC k Cm → Cell) × (TpICD k Cm Dm → Cell)))

/-- The recording register as its two families of cells. -/
@[expose]
def RecReg.equiv : RecReg k Cm Dm Cell ≃ (TpIC k Cm → Cell) × (TpICD k Cm Dm → Cell) :=
  Equiv.refl _

/-- The recording register with every cell at `c`. -/
@[expose]
def RecReg.const (c : Cell) : RecReg k Cm Dm Cell :=
  (fun _ ↦ c, fun _ ↦ c)

/-- **`Record(U)`** (ePrint 2025/2166, Def 7.2, pp. 49–50) on `(TpIC × Yr) × (S × R)`:
controlled on `tic`, it applies `U` to `Yr` and the cell `R_tic`. -/
@[expose]
noncomputable def recordUnitary (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) :
    Matrix ((TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell))
      ((TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell)) ℂ :=
  cellControlled RecReg.equiv Prod.fst U

/-- `Record(U)` is unitary. -/
theorem recordUnitary_mem_unitaryGroup {U : Matrix (Yr × Cell) (Yr × Cell) ℂ}
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    recordUnitary (S := S) (k := k) (Cm := Cm) (Dm := Dm) U ∈ unitaryGroup _ ℂ :=
  cellControlled_mem_unitaryGroup _ _ hU

/-- **`Record(MultiExtract, U)`** (ePrint 2025/2166, Def 7.2, p. 50) on
`(TpIC × Yr) × (S × R)`: controlled on `tic` and the private register `s`, it applies `U` to `Yr`
and the cell `R_(tic, MultiExtract(tic, s))`. -/
@[expose]
noncomputable def recordMEUnitary (ME : MultiExtractor k Cm Dm S)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) :
    Matrix ((TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell))
      ((TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell)) ℂ :=
  cellControlled (RecReg.equiv.trans (Equiv.prodComm _ _))
    (fun p ↦ (⟨p.1, ME.extract p.1 p.2⟩ : TpICD k Cm Dm)) U

/-- `Record(MultiExtract, U)` is unitary. -/
theorem recordMEUnitary_mem_unitaryGroup (ME : MultiExtractor k Cm Dm S)
    {U : Matrix (Yr × Cell) (Yr × Cell) ℂ} (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    recordMEUnitary ME U ∈ unitaryGroup _ ℂ :=
  cellControlled_mem_unitaryGroup _ _ hU

end record

end Quantum
