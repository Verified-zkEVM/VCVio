/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.MultiExtractable
public import VCVio.Quantum.Oracle.Compressed.Equivalence

/-!
# Compressed vector-commitment oracles

The ordinary ports are the compressed standard oracles of Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, Lemma 9.2. Classical reads project onto optional cell labels after decompression.
Both capabilities intertwine the complete-table random-oracle model, giving exact equality of
observed laws for arbitrary adaptive mixed programs. Ordinary-only laws follow by restriction.
-/

public section

open Matrix MeasureTheory Convexity
open scoped Kronecker ENNReal NNReal

universe u uL vL w u₁ v₁

namespace Quantum

/-! ## Splitting off one table -/

section split

variable {M T ι : Type*} [DecidableEq ι]

/-- Split the table at `i` off a register `M × (ι → T)`:
`M × (ι → T) ≃ (M × T) × ({j // j ≠ i} → T)`. -/
@[expose]
def splitAt (M T : Type*) (i : ι) : M × (ι → T) ≃ (M × T) × ({j // j ≠ i} → T) :=
  (Equiv.prodCongr (Equiv.refl M) (Equiv.piSplitAt i fun _ ↦ T)).trans
    (Equiv.prodAssoc M T _).symm

/-- `splitAt M T i` pairs the message register with the `i`-th table entry and keeps the other
entries. -/
@[simp]
theorem splitAt_apply (i : ι) (m : M) (D : ι → T) :
    splitAt M T i (m, D) = ((m, D i), fun j ↦ D j.1) :=
  rfl

/-- A basis matrix placed on one factor is the basis matrix of the map acting on that factor. -/
theorem onFactor_basisMatrix {n A R : Type*} [DecidableEq n] [DecidableEq A] [DecidableEq R]
    (e : n ≃ A × R) (σ : A → A) :
    onFactor e (basisMatrix σ) = basisMatrix fun a ↦ e.symm (σ (e a).1, (e a).2) := by
  ext a b
  rw [onFactor_apply, basisMatrix_apply, basisMatrix_apply]
  by_cases h₁ : (e a).2 = (e b).2 <;> by_cases h₂ : (e a).1 = σ (e b).1 <;>
    simp [h₁, h₂, Equiv.eq_symm_apply, Prod.ext_iff]

variable [Fintype ι] [DecidableEq T] [DecidableEq M]

/-- An operator on the table at `i`, beside an identity on `M`, placed through `splitAt` is the
identity on `M` next to the pi-tensor product with that operator at `i` and identities
elsewhere. -/
theorem onFactor_splitAt_one_kronecker (i : ι) (K : Matrix T T ℂ) :
    onFactor (splitAt M T i) ((1 : Matrix M M ℂ) ⊗ₖ K) =
      (1 : Matrix M M ℂ) ⊗ₖ piKron (Pi.mulSingle i K) := by
  ext ⟨m, D⟩ ⟨m', D'⟩
  rw [onFactor_apply, splitAt_apply, splitAt_apply, kroneckerMap_apply, kroneckerMap_apply,
    piKron_apply, Fintype.prod_eq_mul_prod_subtype_ne _ i, Pi.mulSingle_eq_same]
  have hrest : (∏ j : {j // j ≠ i},
      (Pi.mulSingle i K : ι → Matrix T T ℂ) j.1 (D j.1) (D' j.1)) =
      if (fun j : {j // j ≠ i} ↦ D j.1) = fun j ↦ D' j.1 then 1 else 0 := by
    have h1 (j : {j // j ≠ i}) : (Pi.mulSingle i K : ι → Matrix T T ℂ) j.1 = 1 :=
      Pi.mulSingle_eq_of_ne (M := fun _ ↦ Matrix T T ℂ) j.2 K
    simp only [h1, one_apply, funext_iff]
    exact Fintype.prod_boole
  rw [hrest]
  split_ifs <;> simp

end split

/-! ## Table oracles and operators on the table register -/

section table

variable {X Y T : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype T] [DecidableEq T]

/-- A product with the basis matrix of a bijection on the left reads a row of the right factor. -/
theorem basisMatrix_equiv_mul_apply {A B C : Type*} [Fintype A] [DecidableEq B] (e : A ≃ B)
    (N : Matrix A C ℂ) (b : B) (c : C) : (basisMatrix e * N) b c = N (e.symm b) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ ha
    rw [basisMatrix_apply, ite_eq_right_iff.mpr fun h ↦ absurd (by simp [h]) ha, zero_mul]
  · simp

/-- **A table oracle commutes with an operator on the table register that never connects two
tables reading different functions.** -/
theorem tableOracle_mul_one_kronecker_comm (read : T → X → Y) {K : Matrix T T ℂ}
    (hK : ∀ t t', K t t' ≠ 0 → read t = read t') :
    tableOracle read * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ K) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ K) * tableOracle read := by
  ext ⟨m, t⟩ ⟨m', t'⟩
  rw [tableOracle, basisMatrix_equiv_mul_apply, mul_basisMatrix_apply]
  change ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ K) ((oracleEquiv (read t)).symm m, t) (m', t') =
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ K) (m, t) (oracleEquiv (read t') m', t')
  simp only [kroneckerMap_apply, one_apply]
  by_cases h : K t t' = 0
  · simp [h]
  · rw [hK t t' h]
    simp only [Equiv.symm_apply_eq]

end table

/-! ## k compressed oracles -/

section oracle

variable (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The compression of every cell of every database of `(D_i)_{i ∈ [k]}`: the pi-tensor product
of `k` copies of `Quantum.compressAll X Y`. -/
@[expose]
noncomputable def compressDatabases :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  piKron fun _ : Fin k ↦ compressAll X Y

omit [DecidableEq X] in
/-- Compressing every database is Hermitian. -/
theorem conjTranspose_compressDatabases :
    (compressDatabases k X Y)ᴴ = compressDatabases k X Y := by
  rw [compressDatabases, conjTranspose_piKron, conjTranspose_compressAll]

/-- For nonempty `Y`, compressing every database is an involution. -/
theorem compressDatabases_mul_self [Nonempty Y] :
    compressDatabases k X Y * compressDatabases k X Y = 1 := by
  rw [compressDatabases, piKron_mul]
  simp_rw [compressAll_mul_self]
  exact piKron_one

variable [AddCommGroup Y]

omit [Fintype Y] in
/-- The standard oracle on the query register and the database `D_i`. -/
theorem onFactor_splitAt_standardOracle (i : Fin k) :
    onFactor (splitAt (X × Y) (Database X Y) i) (standardOracle X Y) =
      tableOracle fun D : Fin k → Database X Y ↦ (D i).lookup := by
  rw [standardOracle, tableOracle, tableOracle, onFactor_basisMatrix]
  congr 1
  funext ⟨m, D⟩
  simp only [splitAt, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply,
    id_eq, Equiv.prodAssoc_symm_apply, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.refl_symm, tableOracleEquiv_apply, Equiv.symm_symm, Equiv.prodAssoc_apply,
    Prod.mk.eta, Equiv.symm_apply_apply]
  rfl

/-- **The k compressed oracles are conjugates of standard oracles.** Port `i` is the oracle that
reads the database `D_i` (`Quantum.tableOracle`), conjugated by the compression of every cell of
every database: compressing the databases other than `D_i` commutes with that oracle and squares
to the identity. -/
private theorem compressedPort_eq_conj (i : Fin k) :
    onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
        tableOracle (fun D : Fin k → Database X Y ↦ (D i).lookup) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) := by
  set Ci := piKron (Pi.mulSingle i (compressAll X Y))
  set R := piKron (Function.update (fun _ : Fin k ↦ compressAll X Y) i 1)
  have hCR : compressDatabases k X Y = Ci * R := by
    rw [compressDatabases, piKron_mul]
    congr 1
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  have hRC : compressDatabases k X Y = R * Ci := by
    rw [compressDatabases, piKron_mul]
    congr 1
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  have hRR : R * R = 1 := by
    rw [piKron_mul]
    convert piKron_one (ι := Fin k) (Z := Database X Y) using 2
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h, compressAll_mul_self]
  have hT : tableOracle (fun D : Fin k → Database X Y ↦ (D i).lookup) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ R) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ R) *
        tableOracle (fun D : Fin k → Database X Y ↦ (D i).lookup) := by
    refine tableOracle_mul_one_kronecker_comm _ fun D D' hDD' ↦ ?_
    by_contra hne
    refine hDD' (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    have hi : D i ≠ D' i := fun h ↦ hne (by rw [h])
    simp [hi]
  rw [compressedOracle, onFactor_mul, onFactor_mul,
    onFactor_splitAt_standardOracle, onFactor_splitAt_one_kronecker]
  set T := tableOracle fun D : Fin k → Database X Y ↦ (D i).lookup
  set I := (1 : Matrix (X × Y) (X × Y) ℂ)
  calc (I ⊗ₖ Ci) * T * (I ⊗ₖ Ci) =
      (I ⊗ₖ Ci) * T * ((I ⊗ₖ R) * (I ⊗ₖ R)) * (I ⊗ₖ Ci) := by
        rw [← mul_kronecker_mul, Matrix.one_mul, hRR, one_kronecker_one, Matrix.mul_one]
    _ = (I ⊗ₖ Ci) * ((I ⊗ₖ R) * T) * ((I ⊗ₖ R) * (I ⊗ₖ Ci)) := by
        rw [← hT]
        simp only [Matrix.mul_assoc]
    _ = (I ⊗ₖ (Ci * R)) * T * (I ⊗ₖ (R * Ci)) := by
        rw [← Hybrid.one_kronecker_mul_one_kronecker, ← Hybrid.one_kronecker_mul_one_kronecker]
        simp only [Matrix.mul_assoc]
        rfl
    _ = _ := by rw [← hCR, ← hRC]

/-- A classical read distinguishes every stored label, including the empty label. -/
@[expose]
noncomputable def compressedReadProjector (c : Fin k × X) (a : Option Y) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if D c.1 c.2 = a then 1 else 0) * compressDatabases k X Y

/-- Multiplying conjugates cancels the interior copies of an involution. -/
theorem compressed_conjugate_mul {M : Type*} [Monoid M] (C : M) (hC : C * C = 1) (P Q : M) :
    (C * P * C) * (C * Q * C) = C * (P * Q) * C := by
  calc
    _ = C * P * (C * C) * Q * C := by simp only [mul_assoc]
    _ = _ := by rw [hC, mul_one]; simp only [mul_assoc]

omit [AddCommGroup Y] in
/-- Compressed cell outcomes are Hermitian. -/
theorem compressedReadProjector_hermitian (c : Fin k × X) (a : Option Y) :
    (compressedReadProjector k X Y c a)ᴴ = compressedReadProjector k X Y c a := by
  have h : (diagonal (fun D : Fin k → Database X Y ↦
      if D c.1 c.2 = a then (1 : ℂ) else 0))ᴴ =
      diagonal (fun D ↦ if D c.1 c.2 = a then (1 : ℂ) else 0) := by
    ext D D'
    by_cases he : D = D' <;> by_cases ha : D c.1 c.2 = a <;>
      simp_all [conjTranspose_apply, eq_comm]
  simp only [compressedReadProjector, conjTranspose_mul, conjTranspose_compressDatabases,
    h, Matrix.mul_assoc]

/-- Compressed cell outcomes are orthogonal, including the missing outcome. -/
theorem compressedReadProjector_orthogonal (c : Fin k × X) (a b : Option Y) :
    compressedReadProjector k X Y c a * compressedReadProjector k X Y c b =
      if a = b then compressedReadProjector k X Y c a else 0 := by
  have h : (diagonal (fun D : Fin k → Database X Y ↦
      if D c.1 c.2 = a then (1 : ℂ) else 0)) *
      diagonal (fun D ↦ if D c.1 c.2 = b then (1 : ℂ) else 0) =
      if a = b then diagonal (fun D ↦ if D c.1 c.2 = a then (1 : ℂ) else 0) else 0 := by
    rw [diagonal_mul_diagonal]
    ext D D'
    by_cases hab : a = b <;> by_cases he : D = D' <;>
      by_cases ha : D c.1 c.2 = a <;> by_cases hb : D c.1 c.2 = b <;> simp_all
  simp only [compressedReadProjector,
    compressed_conjugate_mul _ (compressDatabases_mul_self k X Y), h]
  split_ifs <;> simp

/-- Every cell has exactly one optional label before compression. -/
theorem compressedReadProjector_complete (c : Fin k × X) :
    ∑ a, compressedReadProjector k X Y c a = 1 := by
  simp only [compressedReadProjector, ← Finset.sum_mul, ← Finset.mul_sum]
  have h : (∑ a : Option Y, diagonal (fun D : Fin k → Database X Y ↦
      if D c.1 c.2 = a then (1 : ℂ) else 0)) = 1 := by
    ext D D'
    by_cases he : D = D'
    · subst D'; simp [Matrix.sum_apply]
    · simp [Matrix.sum_apply, one_apply, he]
  rw [h, Matrix.mul_one, compressDatabases_mul_self]

/-- Reads commute across cells, including cells in different databases. -/
theorem compressedReadProjector_commute (c d : Fin k × X) (a b : Option Y) :
    compressedReadProjector k X Y c a * compressedReadProjector k X Y d b =
      compressedReadProjector k X Y d b * compressedReadProjector k X Y c a := by
  simp only [compressedReadProjector,
    compressed_conjugate_mul _ (compressDatabases_mul_self k X Y), diagonal_mul_diagonal, mul_comm]

/-- The ordinary port commutes with the framed read projector. -/
theorem compressedReadProjector_commute_ordinary (i : Fin k) (c : Fin k × X) (a : Option Y) :
    onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) *
        (1 ⊗ₖ compressedReadProjector k X Y c a) =
      (1 ⊗ₖ compressedReadProjector k X Y c a) *
        onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) := by
  let P : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
    diagonal fun D ↦ if D c.1 c.2 = a then 1 else 0
  have hP := tableOracle_mul_one_kronecker_comm (fun D : Fin k → Database X Y ↦ (D i).lookup)
    (K := P) (fun D D' h ↦ by
      have he : D = D' := by
        by_contra hn
        exact h (by simp [P, hn])
      rw [he])
  rw [compressedPort_eq_conj, compressedReadProjector]
  simp only [← Hybrid.one_kronecker_mul_one_kronecker]
  have hC : ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
      (1 ⊗ₖ compressDatabases k X Y) = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressDatabases_mul_self, one_kronecker_one]
  rw [compressed_conjugate_mul _ hC, compressed_conjugate_mul _ hC, hP]

/-- **k compressed oracles** (Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Lemma 9.2, p. 58):
the emulated oracle whose
private register holds `k` databases `(D_i)_{i ∈ [k]}`, all started empty (`COInit`, p. 58), and
whose port `i` applies the compressed oracle `Quantum.compressedOracle X Y` to the query register
and the database `D_i`, and the identity to the other databases. -/
@[expose]
noncomputable def compressedVCOracle : VCOracle k X Y where
  S := QReg.of (Fin k → Database X Y)
  init := SubState.basis fun _ ↦ Database.empty
  U i := onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)
  unitary _ := onFactor_mem_unitaryGroup _ compressedOracle_mem_unitaryGroup
  classicalRead := {
    A := compressedReadProjector k X Y
    hermitian := compressedReadProjector_hermitian k X Y
    orthogonal := compressedReadProjector_orthogonal k X Y
    complete := compressedReadProjector_complete k X Y
    commute_cells := fun c a d b ↦ compressedReadProjector_commute k X Y c d a b
    commute_ordinary := compressedReadProjector_commute_ordinary k X Y }

/-- The private register of the k compressed oracles holds `k` databases. -/
theorem compressedVCOracle_S :
    (compressedVCOracle k X Y).S = QReg.of (Fin k → Database X Y) :=
  rfl

/-- The k compressed oracles start with every database empty. -/
theorem compressedVCOracle_init :
    (compressedVCOracle k X Y).init = SubState.basis fun _ ↦ Database.empty :=
  rfl

/-- The port `i` of the k compressed oracles is the compressed oracle on the query register and
the database `D_i`, with the identity on the other databases. -/
theorem compressedVCOracle_U (i : Fin k) :
    (compressedVCOracle k X Y).U i =
      onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) :=
  rfl

/-- **The ports of the k compressed oracles are unitary.** -/
theorem compressedVCOracle_U_mem_unitaryGroup (i : Fin k) :
    (compressedVCOracle k X Y).U i ∈ unitaryGroup ((X × Y) × (Fin k → Database X Y)) ℂ :=
  (compressedVCOracle k X Y).unitary i

variable {k X Y}

/-- **The k compressed oracles are conjugates of standard oracles.** Port `i` is the oracle that
reads the database `D_i` (`Quantum.tableOracle`), conjugated by the compression of every cell of
every database: compressing the databases other than `D_i` commutes with that oracle and squares
to the identity. -/
theorem compressedVCOracle_U_eq_conj (i : Fin k) :
    (compressedVCOracle k X Y).U i =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
        tableOracle (fun D : Fin k → Database X Y ↦ (D i).lookup) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) :=
  compressedPort_eq_conj k X Y i

end oracle

/-! ## Oracle commutation -/

section slots

variable {M₁ M₂ S : Type*} [DecidableEq M₁] [DecidableEq M₂]

/-- An operator on the shared register beside the identity on the first query register, placed
through `Quantum.slotFst`, is the identity on both query registers next to that operator. -/
theorem onFactor_slotFst_one_kronecker (K : Matrix S S ℂ) :
    onFactor (slotFst M₁ M₂ S) ((1 : Matrix M₁ M₁ ℂ) ⊗ₖ K) =
      (1 : Matrix (M₁ × M₂) (M₁ × M₂) ℂ) ⊗ₖ K := by
  ext ⟨⟨a, b⟩, s⟩ ⟨⟨a', b'⟩, s'⟩
  simp only [onFactor_apply, slotFst, Equiv.coe_fn_mk, kroneckerMap_apply, one_apply,
    Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

/-- An operator on the shared register beside the identity on the second query register, placed
through `Quantum.slotSnd`, is the identity on both query registers next to that operator. -/
theorem onFactor_slotSnd_one_kronecker (K : Matrix S S ℂ) :
    onFactor (slotSnd M₁ M₂ S) ((1 : Matrix M₂ M₂ ℂ) ⊗ₖ K) =
      (1 : Matrix (M₁ × M₂) (M₁ × M₂) ℂ) ⊗ₖ K := by
  ext ⟨⟨a, b⟩, s⟩ ⟨⟨a', b'⟩, s'⟩
  simp only [onFactor_apply, slotSnd, Equiv.coe_fn_mk, kroneckerMap_apply, one_apply,
    Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype S] [DecidableEq S]

/-- **Table oracles on two query registers commute** (the step of Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, Lemma 9.2
proof, p. 58, after the compression has been factored out): the oracle that reads the
function `read t` into the second query register commutes with the oracle that reads the function
`read' t` into the first query register, for any two reading maps on a shared register. -/
theorem tableOracle_slotSnd_mul_slotFst_comm (read read' : S → X → Y) :
    onFactor (slotSnd (X × Y) (X × Y) S) (tableOracle read) *
        onFactor (slotFst (X × Y) (X × Y) S) (tableOracle read') =
      onFactor (slotFst (X × Y) (X × Y) S) (tableOracle read') *
        onFactor (slotSnd (X × Y) (X × Y) S) (tableOracle read) := by
  rw [tableOracle, tableOracle, onFactor_basisMatrix, onFactor_basisMatrix, ← basisMatrix_comp,
    ← basisMatrix_comp]
  rfl

end slots

section commute

/-- Conjugation by an involution preserves commutation. -/
theorem conj_mul_conj_comm {M : Type*} [Monoid M] {P A B : M} (hP : P * P = 1)
    (h : A * B = B * A) : P * A * P * (P * B * P) = P * B * P * (P * A * P) := by
  rw [compressed_conjugate_mul P hP, compressed_conjugate_mul P hP, h]

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- **The k compressed oracles commute** (Chiesa, Di, Hu and Zheng, ePrint 2025/2166,
Lemma 9.2 first equation, p. 58):
for all `i j : Fin k`, port `i` acting on the second query register and the databases commutes
with port `j` acting on the first query register and the databases. The case `i = j` is the
statement for one database queried through two registers. This is the equation of
`Quantum.OraclesCommute`, stated on the database register `Fin k → Database X Y`. -/
theorem compressedVCOracle_commute (i j : Fin k) :
    onFactor (slotSnd (X × Y) (X × Y) (Fin k → Database X Y)) ((compressedVCOracle k X Y).U i) *
        onFactor (slotFst (X × Y) (X × Y) (Fin k → Database X Y))
          ((compressedVCOracle k X Y).U j) =
      onFactor (slotFst (X × Y) (X × Y) (Fin k → Database X Y))
          ((compressedVCOracle k X Y).U j) *
        onFactor (slotSnd (X × Y) (X × Y) (Fin k → Database X Y))
          ((compressedVCOracle k X Y).U i) := by
  rw [compressedVCOracle_U_eq_conj, compressedVCOracle_U_eq_conj]
  simp only [onFactor_mul, onFactor_slotFst_one_kronecker, onFactor_slotSnd_one_kronecker]
  refine conj_mul_conj_comm ?_ (tableOracle_slotSnd_mul_slotFst_comm _ _)
  rw [← mul_kronecker_mul, Matrix.one_mul, compressDatabases_mul_self, one_kronecker_one]

end commute

/-! ## Simulations between emulated oracles -/

private theorem evalDistMap_eq_of_runtime_simulation
    {spec : QuantumOracleSpec.{u₁, v₁}} (R₁ R₂ : QuantumRuntime spec)
    (V : MatrixMap R₁.D R₂.D)
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L spec W A) (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, W u) → γ) : R₂.evalDistMap I x ρ f = R₁.evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap]
  refine congrArg Measure.sum (funext fun p ↦ ?_)
  rw [QuantumRuntime.trace_jointPost_eq_of_simulation I h hV hinit x ρ p]

namespace EmulatedOracle

section intertwine

variable {P : Type u} {In : P → QReg}

/-- An isometry intertwining the ports and initialization preserves every observed law. -/
theorem outcomeLawWith_eq_of_intertwine (E₁ E₂ : EmulatedOracle P In)
    (M : Matrix E₂.S E₁.S ℂ)
    (hM : Mᴴ * M = 1)
    (hU : ∀ i, E₂.U i * ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) =
      ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) * E₁.U i)
    (hinit : MatrixMap.conj M E₁.init.matrix = E₂.init.matrix) {L : LocalSig.{uL, vL}}
    (I : L.Interp) {W : QReg → Type w} {A : QReg} (x : QuantumComp L (uSpec P In) W A)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, W u) → γ) :
    E₂.toRuntime.evalDistMap I x ρ f = E₁.toRuntime.evalDistMap I x ρ f := by
  refine evalDistMap_eq_of_runtime_simulation E₁.toRuntime E₂.toRuntime (MatrixMap.conj M)
    (fun i r ↦ ?_) (MatrixMap.isTP_conj hM) hinit I x ρ f
  change MatrixMap.conj (E₂.U i) ∘ₗ (MatrixMap.conj M).amplifyLeft (In i) =
    (MatrixMap.conj M).amplifyLeft (In i) ∘ₗ MatrixMap.conj (E₁.U i)
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul, hU i]

/-- Kraus maps whose operators `M ω` resolve the identity (`∑ ω, (M ω)ᴴ M ω = 1`),
applied on the second factor, preserve the trace in sum. -/
theorem sum_trace_amplifyLeft_conj {Ω S B : Type*} {S' : Ω → Type*} [Fintype Ω] [Fintype S]
    [DecidableEq S] [∀ ω, Fintype (S' ω)] [Fintype B] (M : ∀ ω, Matrix (S' ω) S ℂ)
    (hM : ∑ ω, (M ω)ᴴ * M ω = 1) (N : Matrix (B × S) (B × S) ℂ) :
    ∑ ω, ((MatrixMap.conj (M ω)).amplifyLeft B N).trace = N.trace := by
  classical
  simp only [MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply]
  have h (ω : Ω) :
      (((1 : Matrix B B ℂ) ⊗ₖ M ω) * N * ((1 : Matrix B B ℂ) ⊗ₖ M ω)ᴴ).trace =
      (((1 : Matrix B B ℂ) ⊗ₖ ((M ω)ᴴ * M ω)) * N).trace := by
    rw [Matrix.trace_mul_cycle, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul]
  have hsum : ∑ ω, (1 : Matrix B B ℂ) ⊗ₖ ((M ω)ᴴ * M ω) =
      (1 : Matrix B B ℂ) ⊗ₖ ∑ ω, (M ω)ᴴ * M ω := by
    exact (map_sum (kroneckerBilinear (R := ℂ) (1 : Matrix B B ℂ)) _ _).symm
  simp only [h, ← Matrix.trace_sum, ← Finset.sum_mul, hsum, hM, one_kronecker_one,
    Matrix.one_mul]

end intertwine

section coherent

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}

/-- The identity on the coherent register next to `M` is block diagonal over the index, with the
identity on `In i` next to `M` on the block of `i`. -/
theorem one_kronecker_eq_submatrix_blockDiagonal' {S S' : Type*} (M : Matrix S' S ℂ) :
    (1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ M =
      (Matrix.blockDiagonal' fun i ↦ (1 : Matrix (In i) (In i) ℂ) ⊗ₖ M).submatrix
        (Equiv.sigmaProdDistrib (fun i ↦ In i) S')
        (Equiv.sigmaProdDistrib (fun i ↦ In i) S) := by
  ext ⟨⟨i, a⟩, d⟩ ⟨⟨i', a'⟩, d'⟩
  by_cases h : i = i'
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, Matrix.one_apply]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h, h]

/-- **Intertwining passes to the coherent oracle.** If `M` intertwines every port of `E₁` with the
same port of `E₂`, it intertwines their coherent oracles. -/
theorem coherent_U_mul_one_kronecker (E₁ E₂ : EmulatedOracle P In)
    (M : Matrix E₂.S E₁.S ℂ)
    (hU : ∀ i, E₂.U i * ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) =
      ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) * E₁.U i) :
    E₂.coherent.U () * ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ M) =
      ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ M) * E₁.coherent.U () := by
  rw [one_kronecker_eq_submatrix_blockDiagonal']
  simp only [EmulatedOracle.coherent, Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_mul]
  congr 2
  funext i
  exact hU i

end coherent

end EmulatedOracle

/-! ## The uniform superposition over a finite type -/

section uniform

variable (Ω : Type*) [Fintype Ω]

/-- The uniform superposition `|Ω|^(-1/2) ∑ ω, |ω⟩` over a finite type, as a column. -/
@[expose]
noncomputable def uniformColumnOn : Matrix Ω Unit ℂ :=
  Matrix.of fun _ _ ↦ cellAmp Ω

/-- For nonempty `Ω`, the uniform superposition is a unit vector. -/
theorem conjTranspose_uniformColumnOn_mul_self [Nonempty Ω] :
    (uniformColumnOn Ω)ᴴ * uniformColumnOn Ω = 1 := by
  have hN : (Fintype.card Ω : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext ⟨⟩ ⟨⟩
  simp only [Matrix.mul_apply, conjTranspose_apply, uniformColumnOn, of_apply, star_cellAmp,
    cellAmp_mul_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_apply_eq]
  exact mul_inv_cancel₀ hN

/-- For nonempty `Ω`, the register `Ω` in the uniform superposition. -/
@[expose]
noncomputable def uniformState [Nonempty Ω] : SubState Ω :=
  (SubInstrument.ofIsometry (uniformColumnOn Ω) (conjTranspose_uniformColumnOn_mul_self Ω)).post
    (SubState.basis ()) ()

/-- The density matrix of the uniform superposition is `|u⟩⟨u|` for the uniform column `u`. -/
theorem matrix_uniformState [Nonempty Ω] :
    (uniformState Ω).matrix = MatrixMap.conj (uniformColumnOn Ω) (Matrix.single () () 1) := by
  rw [uniformState, DSubInstrument.matrix_post, SubInstrument.branch_ofIsometry_apply,
    SubState.matrix_basis]

/-- The amplitude of a type whose cardinality is the `n`-th power of that of another. -/
theorem cellAmp_eq_pow {B : Type*} [Fintype B] {n : ℕ}
    (h : Fintype.card Ω = Fintype.card B ^ n) : cellAmp Ω = cellAmp B ^ n := by
  have hsq (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
    rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) n), ← pow_mul, mul_comm, pow_mul,
      Real.sq_sqrt ha]
  rw [cellAmp, cellAmp, h, Nat.cast_pow, hsq _ (Nat.cast_nonneg _), ← inv_pow, Complex.ofReal_pow]

end uniform

/-! ## The purified k-fold random oracle -/

section purified

variable (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Tabulating `k` functions as `k` databases. -/
@[expose]
def ofFunDatabases (H : Fin k → X → Y) : Fin k → Database X Y :=
  fun i ↦ Database.ofFun (H i)

variable {k X Y} in
omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Distinct families of functions tabulate to distinct tuples of databases. -/
theorem ofFunDatabases_injective : Function.Injective (ofFunDatabases k X Y) :=
  fun _ _ h ↦ funext fun i ↦ Database.ofFun_injective (congrFun h i)

omit [DecidableEq Y] in
/-- A pi-tensor product over an empty index is the identity. -/
theorem piKron_of_isEmpty {ι Z : Type*} [Fintype ι] [IsEmpty ι] [DecidableEq Z]
    (A : ι → Matrix Z Z ℂ) : piKron A = 1 := by
  ext D D'
  rw [piKron_apply, Finset.univ_eq_empty, Finset.prod_empty, Subsingleton.elim D D',
    one_apply_eq]

/-- Compressing every database is an involution as soon as there is a family of `k` functions
`X → Y`: either `Y` is nonempty, or there are no databases to compress (`k = 0`) or no cells
(`X` empty). -/
theorem compressDatabases_mul_self_of_nonempty [Nonempty (Fin k → X → Y)] :
    compressDatabases k X Y * compressDatabases k X Y = 1 := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · rcases isEmpty_or_nonempty (Fin k) with hk | hk
    · rw [compressDatabases, piKron_of_isEmpty, Matrix.one_mul]
    · obtain ⟨i⟩ := hk
      obtain ⟨H⟩ := ‹Nonempty (Fin k → X → Y)›
      have : IsEmpty X := ⟨fun x ↦ isEmptyElim (H i x)⟩
      have h1 : compressAll X Y = 1 := piKron_of_isEmpty _
      simp only [compressDatabases, h1, piKron_one, Matrix.one_mul]
  · exact compressDatabases_mul_self k X Y

/-- Tabulating the uniform superposition over families of `k` functions gives the `k` empty
databases with every cell compressed (the `k`-fold form of `E |φ⟩ = S^{⊗X} |∅⟩`). -/
theorem basisMatrix_ofFunDatabases_mul_uniformColumnOn :
    basisMatrix (ofFunDatabases k X Y) * uniformColumnOn (Fin k → X → Y) =
      compressDatabases k X Y *
        basisMatrix fun _ : Unit ↦ fun _ : Fin k ↦ (Database.empty : Database X Y) := by
  ext D u
  rw [mul_basisMatrix_apply, compressDatabases, piKron_apply]
  simp only [compressAll_apply_empty, Matrix.mul_apply, basisMatrix_apply, uniformColumnOn,
    of_apply, boole_mul]
  by_cases h : ∀ i x, D i x ≠ none
  · choose H hH using fun i ↦ Database.exists_ofFun_eq (h i)
    have hD : D = ofFunDatabases k X Y H := funext fun i ↦ (hH i).symm
    rw [Finset.sum_eq_single H (fun H' _ hne ↦ ite_eq_right fun h' ↦
      hne (ofFunDatabases_injective (hD.symm.trans h')).symm) (by simp), ite_eq_left hD,
      Finset.prod_congr rfl fun i _ ↦ ite_eq_left (h i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← pow_mul]
    exact cellAmp_eq_pow _ (B := Y) (by simp [← pow_mul])
  · push Not at h
    obtain ⟨i, x, hx⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right fun h' ↦ h' x hx)]
    refine Finset.sum_eq_zero fun H _ ↦ ite_eq_right ?_
    rintro rfl
    simp [ofFunDatabases, Database.ofFun] at hx

variable [AddCommGroup Y]

/-- **The purified k-fold random oracle**: the private register holds `k` total functions
`X → Y`, started in the uniform superposition over all families, and port `i` applies the table
oracle `|x, y⟩|H⟩ ↦ |x, y + H i x⟩|H⟩`. It is the intermediate oracle of the proof of
`Quantum.outcomeLawWith_compressedVCOracle`. -/
@[expose]
noncomputable def purifiedVCOracle : VCOracle k X Y where
  S := QReg.of (Fin k → X → Y)
  init := uniformState (Fin k → X → Y)
  U i := tableOracle fun H : Fin k → X → Y ↦ H i
  unitary _ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact conjTranspose_tableOracle_mul_self _
  classicalRead := {
    A := fun c a ↦ diagonal fun H ↦ if some (H c.1 c.2) = a then 1 else 0
    hermitian := by
      intro c a
      ext H H'
      by_cases h : H = H' <;> by_cases ha : some (H c.1 c.2) = a <;>
        simp_all [conjTranspose_apply, eq_comm]
    orthogonal := by
      intro c a b
      rw [diagonal_mul_diagonal]
      ext H H'
      by_cases hab : a = b <;> by_cases h : H = H' <;>
        by_cases ha : some (H c.1 c.2) = a <;> by_cases hb : some (H c.1 c.2) = b <;>
        simp_all
    complete := by
      intro c
      ext H H'
      by_cases h : H = H' <;> simp [Matrix.sum_apply, one_apply, h]
    commute_cells := by intros; simp only [diagonal_mul_diagonal, mul_comm]
    commute_ordinary := by
      intro i c a
      apply tableOracle_mul_one_kronecker_comm
      intro H H' h
      have he : H = H' := by
        by_contra hn
        exact h (by simp [hn])
      rw [he] }

variable {k X Y}

/-- **The k compressed oracles simulate the purified k-fold random oracle.** Tabulating the `k`
functions and compressing every cell, `V = S^{⊗(k·X)} E^{⊗k}`, is an isometry that intertwines
the ports and sends the uniform superposition to the empty databases. -/
theorem compressedVCOracle_U_mul_one_kronecker (i : Fin k) :
    onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))) *
        tableOracle fun H : Fin k → X → Y ↦ H i := by
  have hE : tableOracle (fun D : Fin k → Database X Y ↦ (D i).lookup) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix (ofFunDatabases k X Y)) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix (ofFunDatabases k X Y)) *
        tableOracle fun H : Fin k → X → Y ↦ H i :=
    tableOracle_mul_one_kronecker_basisMatrix fun H ↦ Database.lookup_ofFun (H i)
  rw [← compressedVCOracle_U, compressedVCOracle_U_eq_conj,
    ← Hybrid.one_kronecker_mul_one_kronecker]
  calc _ = ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
        tableOracle (fun D : Fin k → Database X Y ↦ (D i).lookup) *
        (((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
          ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y)) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix (ofFunDatabases k X Y)) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [← mul_kronecker_mul, Matrix.one_mul, compressDatabases_mul_self_of_nonempty,
            one_kronecker_one, Matrix.mul_one, Matrix.mul_assoc, hE, Matrix.mul_assoc]

omit [AddCommGroup Y] in
/-- The tabulate-and-compress map is an isometry. -/
theorem conjTranspose_compressDatabases_mul_basisMatrix_mul_self [Nonempty (Fin k → X → Y)] :
    (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))ᴴ *
      (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y)) = 1 := by
  rw [conjTranspose_mul, conjTranspose_compressDatabases, Matrix.mul_assoc,
    ← Matrix.mul_assoc (compressDatabases k X Y), compressDatabases_mul_self_of_nonempty,
    Matrix.one_mul, conjTranspose_basisMatrix_mul_self ofFunDatabases_injective]

/-- The tabulate-and-compress map sends the uniform superposition to the empty databases. -/
theorem conj_compressDatabases_mul_basisMatrix_init :
    MatrixMap.conj (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))
        (purifiedVCOracle k X Y).init.matrix =
      (compressedVCOracle k X Y).init.matrix := by
  change MatrixMap.conj _ (uniformState (Fin k → X → Y)).matrix =
    (SubState.basis fun _ : Fin k ↦ (Database.empty : Database X Y)).matrix
  rw [matrix_uniformState, ← LinearMap.comp_apply, ← MatrixMap.conj_mul, Matrix.mul_assoc,
    basisMatrix_ofFunDatabases_mul_uniformColumnOn, ← Matrix.mul_assoc,
    compressDatabases_mul_self_of_nonempty, Matrix.one_mul, conj_basisMatrix_single,
    SubState.matrix_basis]

/-- Reading the `k` functions at `H` intertwines the purified oracle with the random oracles of
`H`: `(U_{H i} ⊗ 1) (1 ⊗ ⟨H|) = (1 ⊗ ⟨H|) StOᵢ`. -/
theorem oracleUnitary_kronecker_one_mul_one_kronecker_evalRow_apply (H : Fin k → X → Y)
    (i : Fin k) :
    (oracleUnitary (H i) ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ evalRow H) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ evalRow H) *
        tableOracle fun H' : Fin k → X → Y ↦ H' i := by
  ext ⟨m, u⟩ ⟨m', H'⟩
  by_cases hH : H' = H
  · subst hH
    simp only [evalRow, Matrix.mul_apply, kroneckerMap_apply, oracleUnitary_apply,
      one_apply_eq, mul_one, Matrix.one_apply, of_apply, ↓reduceIte, mul_ite, mul_zero,
      Fintype.sum_prod_type, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_ite_irrel,
      Finset.sum_boole, Finset.filter_const, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, tableOracle_apply, tableOracleEquiv_apply, oracleEquiv_apply, ite_mul,
      one_mul, zero_mul, Prod.mk.injEq, and_true, Finset.sum_ite_eq]
    split_ifs <;> simp
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, evalRow, oracleUnitary_apply,
      tableOracle_apply, Matrix.one_apply, hH, Ne.symm hH]

omit [AddCommGroup Y] in
/-- The rows `⟨H|` resolve the identity on the register of `k` functions. -/
theorem sum_conjTranspose_evalRow_mul_self :
    ∑ H : Fin k → X → Y, (evalRow H)ᴴ * evalRow H = 1 := by
  ext H' H''
  simp [Matrix.sum_apply, Matrix.mul_apply, evalRow, Matrix.one_apply, eq_comm]

/-- Reading the uniform superposition at `H` leaves the weight `|Y|^(-k|X|)`. -/
theorem conj_evalRow_purifiedVCOracle_init (H : Fin k → X → Y) :
    MatrixMap.conj (evalRow H) (purifiedVCOracle k X Y).init.matrix =
      (((Fintype.card (Fin k → X → Y) : ℝ≥0)⁻¹ : ℝ) : ℂ) •
        (romVCOracle k X Y H).init.matrix := by
  change MatrixMap.conj (evalRow H) (uniformState (Fin k → X → Y)).matrix =
    _ • (SubState.basis ()).matrix
  rw [matrix_uniformState, ← LinearMap.comp_apply, ← MatrixMap.conj_mul, SubState.matrix_basis]
  ext ⟨⟩ ⟨⟩
  simp only [evalRow, uniformColumnOn, MatrixMap.conj_apply, conjTranspose_mul, Matrix.mul_apply,
    Finset.univ_unique, PUnit.default_eq_unit, of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, single_apply_same, mul_one, Finset.sum_const,
    Finset.card_singleton, one_smul, conjTranspose_apply, star_cellAmp, RCLike.star_def,
    MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_zero, cellAmp_mul_self, Fintype.card_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, NNReal.coe_pow,
    NNReal.coe_natCast, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast]
  change _ = _ * Matrix.single () () (1 : ℂ) () ()
  rw [Matrix.single_apply_same, mul_one]

/-- A read on a tabulated complete function selects exactly its optional value. -/
theorem compressedReadProjector_mul_tabulate (c : Fin k × X) (a : Option Y) :
    compressedReadProjector k X Y c a *
        (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y)) =
      (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y)) *
        diagonal (fun H ↦ if some (H c.1 c.2) = a then (1 : ℂ) else 0) := by
  have h : (diagonal (fun D : Fin k → Database X Y ↦
      if D c.1 c.2 = a then (1 : ℂ) else 0)) * basisMatrix (ofFunDatabases k X Y) =
      basisMatrix (ofFunDatabases k X Y) *
        diagonal (fun H ↦ if some (H c.1 c.2) = a then (1 : ℂ) else 0) := by
    ext D H
    simp only [diagonal_mul, mul_diagonal, basisMatrix_apply]
    by_cases he : D = ofFunDatabases k X Y H
    · subst D; exact mul_comm _ _
    · simp [he]
  calc
    _ = compressDatabases k X Y *
        ((diagonal fun D : Fin k → Database X Y ↦ if D c.1 c.2 = a then (1 : ℂ) else 0) *
          basisMatrix (ofFunDatabases k X Y)) := by
      rw [compressedReadProjector, Matrix.mul_assoc,
        ← Matrix.mul_assoc (compressDatabases k X Y) (compressDatabases k X Y),
        compressDatabases_mul_self, Matrix.one_mul, Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.mul_assoc]

/-- The missing outcome annihilates the complete-table subspace. -/
theorem compressedReadProjector_none_mul_tabulate (c : Fin k × X) :
    compressedReadProjector k X Y c none *
      (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y)) = 0 := by
  rw [compressedReadProjector_mul_tabulate]
  simp

omit [AddCommGroup Y] in
/-- Evaluating a complete table intertwines each optional read with the real read. -/
theorem rom_read_mul_evalRow (H : Fin k → X → Y) (c : Fin k × X) (a : Option Y) :
    (if a = some (H c.1 c.2) then (1 : Matrix Unit Unit ℂ) else 0) * evalRow H =
      evalRow H * diagonal (fun H' ↦ if some (H' c.1 c.2) = a then (1 : ℂ) else 0) := by
  ext u H'
  by_cases ha : a = some (H c.1 c.2) <;> by_cases hh : H = H' <;>
    simp_all [evalRow, mul_diagonal, eq_comm]

end purified

private theorem runtimeLaw_eq_sum {spec : QuantumOracleSpec.{u₁, v₁}}
    {Ω : Type*} [Fintype Ω] (E : QuantumRuntime spec)
    (F : Ω → QuantumRuntime spec) (M : ∀ ω, Matrix (F ω).D E.D ℂ) (c : Ω → ℝ≥0)
    (hM : ∑ ω, (M ω)ᴴ * M ω = 1)
    (hstep : ∀ ω i r, ((F ω).step i).branch r ∘ₗ
        (MatrixMap.conj (M ω)).amplifyLeft (spec.In i) =
      (MatrixMap.conj (M ω)).amplifyLeft (spec.Out i) ∘ₗ (E.step i).branch r)
    (hinit : ∀ ω, MatrixMap.conj (M ω) E.init.matrix =
      ((c ω : ℝ) : ℂ) • (F ω).init.matrix)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L spec W A) (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, W u) → γ) :
    E.evalDistMap I x ρ f =
      ∑ ω, (c ω : ℝ≥0∞) • (F ω).evalDistMap I x ρ f := by
  have htr (p : Σ u, W u) : (E.jointPost I x ρ p).matrix.trace =
      ∑ ω, ((c ω : ℝ) : ℂ) * ((F ω).jointPost I x ρ p).matrix.trace := by
    rw [← EmulatedOracle.sum_trace_amplifyLeft_conj M hM]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    have hsim := QuantumRuntime.simulation (R₁ := E) (R₂ := (F ω))
      (V := MatrixMap.conj (M ω)) I (hstep ω) x p
    have h' := LinearMap.congr_fun hsim (ρ.matrix ⊗ₖ E.init.matrix)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_kronecker, hinit,
      kronecker_smul, map_smul] at h'
    rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost, ← h', Matrix.trace_smul,
      smul_eq_mul]
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply, QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs]
  simp only [Measure.smul_apply, smul_eq_mul, QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs,
    htr, Complex.re_sum, Complex.re_ofReal_mul, ← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine tsum_congr fun p ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg, Finset.sum_mul]
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [ENNReal.ofReal_mul (c ω).coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
  · exact fun ω _ ↦ mul_nonneg (c ω).coe_nonneg (SubState.trace_re_nonneg _)

namespace VCOracle

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Ordinary and read intertwiners together intertwine every mixed runtime branch. -/
theorem mixed_step_intertwine (E F : VCOracle k X Y) (M : Matrix F.S E.S ℂ)
    (hU : ∀ i, F.U i * (1 ⊗ₖ M) = (1 ⊗ₖ M) * E.U i)
    (hA : ∀ c a, F.classicalRead.A c a * M = M * E.classicalRead.A c a)
    (p : (mixedOracleSpec k X Y).Port) (r : (mixedOracleSpec k X Y).Result p) :
    (F.mixedRuntime.step p).branch r ∘ₗ
        (MatrixMap.conj M).amplifyLeft ((mixedOracleSpec k X Y).In p) =
      (MatrixMap.conj M).amplifyLeft ((mixedOracleSpec k X Y).Out p) ∘ₗ
        (E.mixedRuntime.step p).branch r := by
  cases p with
  | inl p =>
    change MatrixMap.conj (F.coherent.U p) ∘ₗ (MatrixMap.conj M).amplifyLeft _ =
      (MatrixMap.conj M).amplifyLeft _ ∘ₗ MatrixMap.conj (E.coherent.U p)
    rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
      EmulatedOracle.coherent_U_mul_one_kronecker E.toEmulatedOracle F.toEmulatedOracle M hU]
  | inr c =>
    change Option Y at r
    change (F.classicalRead.step c).branch r ∘ₗ (MatrixMap.conj M).amplifyLeft Unit =
      (MatrixMap.conj M).amplifyLeft Unit ∘ₗ (E.classicalRead.step c).branch r
    rw [ProjectiveClassicalAnswers.step_branch, ProjectiveClassicalAnswers.step_branch,
      MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
      ← mul_kronecker_mul, Matrix.one_mul, ← mul_kronecker_mul, Matrix.one_mul, hA]

/-- An isometry intertwining both capabilities preserves every observed law. -/
theorem evalDistMap_eq_of_mixed_intertwine (E F : VCOracle k X Y) (M : Matrix F.S E.S ℂ)
    (hM : Mᴴ * M = 1)
    (hU : ∀ i, F.U i * (1 ⊗ₖ M) = (1 ⊗ₖ M) * E.U i)
    (hA : ∀ c a, F.classicalRead.A c a * M = M * E.classicalRead.A c a)
    (hinit : MatrixMap.conj M E.init.matrix = F.init.matrix) {L : LocalSig.{uL, vL}}
    (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (mixedOracleSpec k X Y) W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, W u) → γ) :
    F.mixedRuntime.evalDistMap I x ρ f = E.mixedRuntime.evalDistMap I x ρ f := by
  exact evalDistMap_eq_of_runtime_simulation E.mixedRuntime F.mixedRuntime (MatrixMap.conj M)
    (mixed_step_intertwine E F M hU hA) (MatrixMap.isTP_conj hM) hinit I x ρ f

/-- A complete family of mixed intertwiners resolves a runtime law as a mixture. -/
theorem evalDistMap_eq_sum_of_mixed_intertwine {Ω : Type*} [Fintype Ω] (E : VCOracle k X Y)
    (F : Ω → VCOracle k X Y) (M : ∀ ω, Matrix (F ω).S E.S ℂ) (c : Ω → ℝ≥0)
    (hM : ∑ ω, (M ω)ᴴ * M ω = 1)
    (hU : ∀ ω i, (F ω).U i * (1 ⊗ₖ M ω) = (1 ⊗ₖ M ω) * E.U i)
    (hA : ∀ ω d a, (F ω).classicalRead.A d a * M ω = M ω * E.classicalRead.A d a)
    (hinit : ∀ ω, MatrixMap.conj (M ω) E.init.matrix =
      ((c ω : ℝ) : ℂ) • (F ω).init.matrix)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (mixedOracleSpec k X Y) W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, W u) → γ) :
    E.mixedRuntime.evalDistMap I x ρ f =
      ∑ ω, (c ω : ℝ≥0∞) • (F ω).mixedRuntime.evalDistMap I x ρ f :=
  runtimeLaw_eq_sum E.mixedRuntime (fun ω ↦ (F ω).mixedRuntime) M c hM
    (fun ω ↦ mixed_step_intertwine E (F ω) (M ω) (hU ω) (hA ω)) hinit I x ρ f

end VCOracle

/-! ## Perfect simulation of k random oracles (Lemma 4.4 for k oracles) -/

section main

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] {L : LocalSig.{uL, vL}} (I : L.Interp)
  {W : QReg → Type w} {A : QReg} {γ : Type*} [MeasurableSpace γ]

/-- Every adaptive mixed program has exactly the uniform random-oracle observed law. -/
theorem evalDistMap_mixed_compressedVCOracle
    (x : QuantumComp L (mixedOracleSpec k X Y) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).mixedRuntime.evalDistMap I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).mixedRuntime.evalDistMap I x ρ f := by
  rw [VCOracle.evalDistMap_eq_of_mixed_intertwine
    (purifiedVCOracle k X Y) (compressedVCOracle k X Y)
    (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))
    conjTranspose_compressDatabases_mul_basisMatrix_mul_self
    compressedVCOracle_U_mul_one_kronecker compressedReadProjector_mul_tabulate
    conj_compressDatabases_mul_basisMatrix_init I x ρ f,
    VCOracle.evalDistMap_eq_sum_of_mixed_intertwine (purifiedVCOracle k X Y)
      (fun H ↦ romVCOracle k X Y H) (fun H ↦ evalRow H)
      (fun _ ↦ (Fintype.card _ : ℝ≥0)⁻¹) sum_conjTranspose_evalRow_mul_self
      oracleUnitary_kronecker_one_mul_one_kronecker_evalRow_apply rom_read_mul_evalRow
      conj_evalRow_purifiedVCOracle_init I x ρ f]
  simp [ENNReal.coe_inv]

/-- Ordinary coherent programs have the same observed law as the uniform random oracle,
by restricting the exact mixed-runtime law to the ordinary ports. -/
theorem outcomeLawWith_coherent_compressedVCOracle
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).coherent.toRuntime.evalDistMap I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).coherent.toRuntime.evalDistMap I x ρ f := by
  have h := evalDistMap_mixed_compressedVCOracle I x.liftOrdinary ρ f
  have hl (E : VCOracle k X Y) :
      E.mixedRuntime.evalDistMap I x.liftOrdinary ρ f =
        E.coherent.toRuntime.evalDistMap I x ρ f := by
    simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost,
      VCOracle.mixedRuntime, EmulatedOracle.withClassicalReads,
      QuantumRuntime.run_liftOrdinary]
    rfl
  simpa only [hl] using h

private def reifyLocal {spec : QuantumOracleSpec.{u₁, v₁}} :
    {A : QReg} → QuantumComp L spec W A →
      QuantumComp LocalSig.instruments.{vL} spec W A
  | _, .pure a => .pure a
  | _, .liftBind (.prim o) cont =>
      QuantumComp.primBind ⟨L.Outcome o, L.next o, I o⟩ fun b ↦ reifyLocal (cont (ULift.up b))
  | _, .liftBind (.query i B e) cont =>
      QuantumComp.queryBind i B e fun r ↦ reifyLocal (cont (ULift.up r))

private theorem run_reifyLocal {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)
    (x : QuantumComp L spec W A) : R.run .instruments (reifyLocal I x) = R.run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ a => rfl
  | primBind _ o cont ih => exact congrArg (((I o).frame R.D).bind) (funext ih)
  | queryBind _ i B e cont ih =>
    change (DSubInstrument.bind (R.queryStep i B e) fun r ↦
      R.run .instruments (reifyLocal I (cont r))) =
      (DSubInstrument.bind (R.queryStep i B e) fun r ↦ R.run I (cont r))
    congr 1
    funext r
    exact ih r

private theorem law_reifyLocal {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    R.evalDistMap .instruments (reifyLocal I x) ρ f = R.evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost, run_reifyLocal]

/-- **The k compressed oracles are perfectly indistinguishable from k random oracles**
(Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Lemma 4.4, p. 29, for `k` oracles,
as used in Lemma 9.2, p. 58), for programs
calling the oracles through their classical ports: every program, observed through any function
of its leaf, has the same law against `Quantum.compressedVCOracle k X Y` as on average over
uniformly random families `H : Fin k → X → Y` against `Quantum.romVCOracle k X Y H`.
Programs are adaptive, with their own local operations and registers, a final register that may
depend on the outcome, and any number of calls on each path. -/
theorem outcomeLawWith_compressedVCOracle
    (x : QuantumComp L (uSpec (Fin k) (oIn k X Y)) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).toRuntime.evalDistMap I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).toRuntime.evalDistMap I x ρ f := by
  have h := outcomeLawWith_coherent_compressedVCOracle .instruments
    (reifyLocal I x).toCoherent ρ f
  simpa only [EmulatedOracle.outcomeLawWith_toCoherent, law_reifyLocal] using h

end main

/-! ## P1 and the oracle commutation in the form of Definition 7.3 -/

section definition

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- The mixed law against the barycenter of the standard simplex, the uniform distribution on a
nonempty finite type, is the average of the laws. -/
theorem mixedLawWith_barycenter {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{uL, vL}}
    {W : QReg → Type w} {A : QReg} {Ω : Type*} [Fintype Ω] [Nonempty Ω] {β : Type*}
    [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) :
    mixedLawWith (StdSimplex.barycenter : StdSimplex ℝ Ω) R I x ρ f =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ • (R ω).evalDistMap I x ρ (f ω) := by
  rw [mixedLawWith, Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [StdSimplex.weights_barycenter_apply,
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_natCast]

/-- **P1 for the k compressed oracles with `κsim = 0`** (Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, Lemma 4.4, p. 29, for
`k` oracles, as used in Lemma 9.2, p. 58): the mixed k compressed oracles simulate the
random-oracle model, the uniform distribution over the families `H : Fin k → X → Y` of
`Quantum.romVCOracle k X Y H`, with no error. -/
theorem simulates_compressedVCOracle :
    Simulates (StdSimplex.barycenter : StdSimplex ℝ (Fin k → X → Y))
      (fun H ↦ (romVCOracle k X Y H).mixedRuntime) (compressedVCOracle k X Y) 0 := by
  intro t A W x f ρ _
  rw [mixedLawWith_barycenter, evalDistMap_mixed_compressedVCOracle]
  simp only [Pi.zero_apply, add_zero, le_refl, and_self]

/-- Against a uniformly sampled random oracle, every program has the same law against the
coherent k compressed oracles as in the random-oracle model (`Quantum.sampledEvalDistMap`). -/
theorem outcomeLawWith_coherent_compressedVCOracle_eq_sampledLawWith
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {A : QReg} {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).coherent.toRuntime.evalDistMap I x ρ f =
      sampledEvalDistMap (fun H ↦ (romVCOracle k X Y H).coherent.toRuntime)
        I x ρ fun _ ↦ f := by
  rw [outcomeLawWith_coherent_compressedVCOracle, sampledEvalDistMap_eq_sum, Finset.smul_sum]

/-- The classical-port form of `outcomeLawWith_coherent_compressedVCOracle_eq_sampledLawWith`. -/
theorem outcomeLawWith_compressedVCOracle_eq_sampledLawWith
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg} {γ : Type*}
    [MeasurableSpace γ] (x : QuantumComp L (uSpec (Fin k) (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).toRuntime.evalDistMap I x ρ f =
      sampledEvalDistMap (fun H ↦ (romVCOracle k X Y H).toRuntime) I x ρ fun _ ↦ f := by
  rw [outcomeLawWith_compressedVCOracle, sampledEvalDistMap_eq_sum, Finset.smul_sum]

/-- **P1 for the k compressed oracles with `κsim = 0`, against a sampleable random oracle**: the
form of `Quantum.simulates_compressedVCOracle` for the uniform distribution
`Quantum.uniformWeights` of a sampleable type of families. -/
theorem simulates_uniformWeights_compressedVCOracle [SampleableType (Fin k → X → Y)] :
    Simulates (uniformWeights (Fin k → X → Y))
      (fun H ↦ (romVCOracle k X Y H).mixedRuntime) (compressedVCOracle k X Y) 0 :=
  Simulates.ofUniform fun t A W x f ρ _ ↦ by
    rw [evalDistMap_mixed_compressedVCOracle, sampledEvalDistMap_eq_sum, Finset.smul_sum]
    simp only [Pi.zero_apply, add_zero, le_refl, and_self]

/-- **The k compressed oracles commute** (Chiesa, Di, Hu and Zheng, ePrint 2025/2166,
Lemma 9.2 first equation,
p. 58), in the form of the first half of property P2 (Definition 7.3, p. 50). -/
theorem oraclesCommute_compressedVCOracle : OraclesCommute (compressedVCOracle k X Y) :=
  fun i j ↦ compressedVCOracle_commute i j

end definition

end Quantum
