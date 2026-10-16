/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.MultiExtractable
public import VCVio.Quantum.Oracle.Compressed.Equivalence

/-!
# k compressed oracles

The emulated oracle of Lemma 9.2 of Chiesa, Di, Hu and Zheng (ePrint 2025/2166, p. 58):
`k` compressed standard oracles `COstd` (Section 4.3, p. 29), one database `D_i` per
oracle, all started empty. Port `i` applies the compressed standard oracle to the query register
and to `D_i` and leaves the other databases alone. This file proves the two facts about it that
Definition 7.3 asks of an emulated oracle and that hold for every multi-extractor: P1 with
`κsim = 0` and the first half of P2, the commutation of the ports (Lemma 9.2, first equation,
p. 58).

## Main definitions

* `Quantum.compressDatabases k X Y`: the compression unitary on every database, `C^{⊗k}`.
* `Quantum.compressedVCOracle k X Y`: the k compressed oracles, a `Quantum.VCOracle k X Y`.
* `Quantum.purifiedVCOracle k X Y`: the purified random oracle, which holds the uniform
  superposition of the families `H : Fin k → X → Y` and answers port `i` from `H i`.

## Main results

* `Quantum.compressedVCOracle_U_mem_unitaryGroup`: every port is unitary.
* `Quantum.compressedVCOracle_U_eq_conj`: port `i` is the table oracle reading `D_i`, conjugated by
  `1 ⊗ C^{⊗k}`.
* `Quantum.compressedVCOracle_commute`, `Quantum.oraclesCommute_compressedVCOracle`: the ports
  commute, in the form `Quantum.OraclesCommute` of Definition 7.3 (p. 50).
* `Quantum.outcomeLawWith_coherent_compressedVCOracle`: every program, with any local operations,
  leaves and outcome map, has the same law against the coherent k compressed oracles as the
  average of its laws against the random oracles `Quantum.romVCOracle k X Y H`. The classical-port
  form is `Quantum.outcomeLawWith_compressedVCOracle`.
* `Quantum.simulates_compressedVCOracle`: P1 with `κsim = 0` against the uniform weights
  `StdSimplex.barycenter`, and `Quantum.simulates_uniformWeights_compressedVCOracle` against
  `Quantum.uniformWeights` of a sampleable type of families (Lemma 4.4 for `k` oracles, p. 29).

## Proof

The equality of laws is proved at the level of matrices, without a hybrid argument. Port `i` is
`(1 ⊗ C^{⊗k}) T_i (1 ⊗ C^{⊗k})`, where `T_i` is the table oracle reading `D_i`. The isometry
`V = C^{⊗k} B`, where `B` embeds a family of functions as a tuple of total databases, intertwines
the ports of the purified oracle with those of the k compressed oracles and carries the initial
state of the purified oracle, the uniform superposition, to the empty databases
(`Quantum.EmulatedOracle.outcomeLawWith_eq_of_intertwine`). The rows `⟨H|` resolve the identity,
intertwine the ports of the purified oracle with those of the random oracle `H`, and read the
uniform superposition with weight `|Y|^{-k|X|}`
(`Quantum.EmulatedOracle.outcomeLawWith_eq_sum_of_intertwine`). Both steps hold for any emulated
oracles and pass to the coherent oracles (`Quantum.EmulatedOracle.coherent_U_mul_one_kronecker`).

## Departures from the paper

* Answers lie in any finite additive group `Y`, as in `Quantum.romVCOracle`; the paper's
  bitstrings with XOR are one instance. The statements about the oracles carry no nonemptiness
  hypothesis: the zero of `Y` already makes `Y` and `Fin k → X → Y` nonempty. Only the
  algebra-free helpers on compression and on the uniform superposition
  (`Quantum.compressDatabases_mul_self`, `Quantum.compressDatabases_mul_self_of_nonempty`,
  `Quantum.uniformState`) assume nonemptiness.
* `Quantum.compressedVCOracle_commute` is stated on the register `Fin k → Database X Y`;
  `Quantum.oraclesCommute_compressedVCOracle` is the form of Definition 7.3.
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
  have hrest : (∏ j : {j // j ≠ i}, (Pi.mulSingle i K : ι → Matrix T T ℂ) j.1 (D j.1) (D' j.1)) =
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

/-- Products of operators on the second factor beside an identity. -/
theorem one_kronecker_mul_one_kronecker {A B C E : Type*} [Fintype A] [DecidableEq A] [Fintype C]
    (K : Matrix B C ℂ) (L : Matrix C E ℂ) :
    ((1 : Matrix A A ℂ) ⊗ₖ K) * ((1 : Matrix A A ℂ) ⊗ₖ L) = (1 : Matrix A A ℂ) ⊗ₖ (K * L) := by
  rw [← mul_kronecker_mul, Matrix.one_mul]

end table

/-! ## k compressed oracles -/

section oracle

variable (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The compression of every cell of every database of `(D_i)_{i ∈ [k]}`: the pi-tensor product
of `k` copies of `Quantum.compressAll X Y`. -/
@[expose]
noncomputable def compressDatabases : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  piKron fun _ : Fin k ↦ compressAll X Y

omit [DecidableEq X] in
/-- Compressing every database is Hermitian. -/
theorem conjTranspose_compressDatabases : (compressDatabases k X Y)ᴴ = compressDatabases k X Y := by
  rw [compressDatabases, conjTranspose_piKron, conjTranspose_compressAll]

/-- For nonempty `Y`, compressing every database is an involution. -/
theorem compressDatabases_mul_self [Nonempty Y] :
    compressDatabases k X Y * compressDatabases k X Y = 1 := by
  rw [compressDatabases, piKron_mul]
  simp_rw [compressAll_mul_self]
  exact piKron_one

variable [AddCommGroup Y]

/-- **k compressed oracles** (ePrint 2025/2166, Lemma 9.2, p. 58): the emulated oracle whose
private register holds `k` databases `(D_i)_{i ∈ [k]}`, all started empty (`COInit`, p. 58), and
whose port `i` applies the compressed oracle `Quantum.compressedOracle X Y` to the query register
and the database `D_i`, and the identity to the other databases. -/
@[expose]
noncomputable def compressedVCOracle : VCOracle k X Y where
  S := QReg.of (Fin k → Database X Y)
  init := SubState.basis fun _ ↦ Database.empty
  U i := onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)
  unitary _ := onFactor_mem_unitaryGroup _ compressedOracle_mem_unitaryGroup

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
theorem compressedVCOracle_U_eq_conj (i : Fin k) :
    (compressedVCOracle k X Y).U i =
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
  rw [compressedVCOracle_U, compressedOracle, onFactor_mul, onFactor_mul,
    onFactor_splitAt_standardOracle, onFactor_splitAt_one_kronecker]
  set T := tableOracle fun D : Fin k → Database X Y ↦ (D i).lookup
  set I := (1 : Matrix (X × Y) (X × Y) ℂ)
  calc (I ⊗ₖ Ci) * T * (I ⊗ₖ Ci) = (I ⊗ₖ Ci) * T * ((I ⊗ₖ R) * (I ⊗ₖ R)) * (I ⊗ₖ Ci) := by
        rw [one_kronecker_mul_one_kronecker, hRR, one_kronecker_one, Matrix.mul_one]
    _ = (I ⊗ₖ Ci) * ((I ⊗ₖ R) * T) * ((I ⊗ₖ R) * (I ⊗ₖ Ci)) := by
        rw [← hT]
        simp only [Matrix.mul_assoc]
    _ = (I ⊗ₖ (Ci * R)) * T * (I ⊗ₖ (R * Ci)) := by
        rw [← one_kronecker_mul_one_kronecker, ← one_kronecker_mul_one_kronecker]
        simp only [Matrix.mul_assoc]
        rfl
    _ = _ := by rw [← hCR, ← hRC]

end oracle

/-! ## Oracle commutation -/

section slots

variable {M₁ M₂ S : Type*} [Fintype M₁] [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂]
  [Fintype S] [DecidableEq S]

omit [Fintype M₁] [Fintype M₂] [Fintype S] [DecidableEq S] in
/-- An operator on the shared register beside the identity on the first query register, placed
through `Quantum.slotFst`, is the identity on both query registers next to that operator. -/
theorem onFactor_slotFst_one_kronecker (K : Matrix S S ℂ) :
    onFactor (slotFst M₁ M₂ S) ((1 : Matrix M₁ M₁ ℂ) ⊗ₖ K) =
      (1 : Matrix (M₁ × M₂) (M₁ × M₂) ℂ) ⊗ₖ K := by
  ext ⟨⟨a, b⟩, s⟩ ⟨⟨a', b'⟩, s'⟩
  simp only [onFactor_apply, slotFst, Equiv.coe_fn_mk, kroneckerMap_apply, one_apply,
    Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

omit [Fintype M₁] [Fintype M₂] [Fintype S] [DecidableEq S] in
/-- An operator on the shared register beside the identity on the second query register, placed
through `Quantum.slotSnd`, is the identity on both query registers next to that operator. -/
theorem onFactor_slotSnd_one_kronecker (K : Matrix S S ℂ) :
    onFactor (slotSnd M₁ M₂ S) ((1 : Matrix M₂ M₂ ℂ) ⊗ₖ K) =
      (1 : Matrix (M₁ × M₂) (M₁ × M₂) ℂ) ⊗ₖ K := by
  ext ⟨⟨a, b⟩, s⟩ ⟨⟨a', b'⟩, s'⟩
  simp only [onFactor_apply, slotSnd, Equiv.coe_fn_mk, kroneckerMap_apply, one_apply,
    Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- **Table oracles on two query registers commute** (the step of ePrint 2025/2166, Lemma 9.2
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
  calc P * A * P * (P * B * P) = P * (A * (P * P) * B) * P := by simp only [mul_assoc]
    _ = P * (B * (P * P) * A) * P := by rw [hP, mul_one, mul_one, h]
    _ = P * B * P * (P * A * P) := by simp only [mul_assoc]

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- **The k compressed oracles commute** (ePrint 2025/2166, Lemma 9.2 first equation, p. 58):
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
  rw [one_kronecker_mul_one_kronecker, compressDatabases_mul_self, one_kronecker_one]

end commute

/-! ## Simulations between emulated oracles -/

namespace EmulatedOracle

section intertwine

variable {P : Type u} {In : P → QReg}

/-- **Indistinguishability of emulated oracles through an isometry.** If an isometry `M` from the
private register of `E₁` to that of `E₂` intertwines every port (`U₂ᵢ (1 ⊗ M) = (1 ⊗ M) U₁ᵢ`)
and sends the initial substate of `E₁` to that of `E₂`, then every program, observed through any
function of its leaf, has the same law against the two runtimes. -/
theorem outcomeLawWith_eq_of_intertwine (E₁ E₂ : EmulatedOracle P In) (M : Matrix E₂.S E₁.S ℂ)
    (hM : Mᴴ * M = 1)
    (hU : ∀ i, E₂.U i * ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) =
      ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) * E₁.U i)
    (hinit : MatrixMap.conj M E₁.init.matrix = E₂.init.matrix) {L : LocalSig.{uL, vL}}
    (I : L.Interp) {W : QReg → Type w} {A : QReg} (x : QuantumComp L (uSpec P In) W A)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, W u) → γ) :
    E₂.toRuntime.outcomeLawWith I x ρ f = E₁.toRuntime.outcomeLawWith I x ρ f := by
  simp only [QuantumRuntime.outcomeLawWith]
  refine congrArg Measure.sum (funext fun p ↦ ?_)
  rw [QuantumRuntime.trace_jointPost_eq_of_simulation (R₁ := E₁.toRuntime) (R₂ := E₂.toRuntime)
    (V := MatrixMap.conj M) I (fun i r ↦ ?_) (MatrixMap.isTP_conj hM) hinit x ρ p]
  change MatrixMap.conj (E₂.U i) ∘ₗ (MatrixMap.conj M).amplifyLeft (In i) =
    (MatrixMap.conj M).amplifyLeft (In i) ∘ₗ MatrixMap.conj (E₁.U i)
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul, hU i]

/-- Kraus maps whose operators `M ω` resolve the identity (`∑ ω, (M ω)ᴴ M ω = 1`), applied on the
second factor, preserve the trace in sum. -/
theorem sum_trace_amplifyLeft_conj {Ω S B : Type*} {S' : Ω → Type*} [Fintype Ω] [Fintype S]
    [DecidableEq S] [∀ ω, Fintype (S' ω)] [Fintype B] (M : ∀ ω, Matrix (S' ω) S ℂ)
    (hM : ∑ ω, (M ω)ᴴ * M ω = 1) (N : Matrix (B × S) (B × S) ℂ) :
    ∑ ω, ((MatrixMap.conj (M ω)).amplifyLeft B N).trace = N.trace := by
  classical
  simp only [MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply]
  have h (ω : Ω) : (((1 : Matrix B B ℂ) ⊗ₖ M ω) * N * ((1 : Matrix B B ℂ) ⊗ₖ M ω)ᴴ).trace =
      (((1 : Matrix B B ℂ) ⊗ₖ ((M ω)ᴴ * M ω)) * N).trace := by
    rw [Matrix.trace_mul_cycle, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul]
  have hsum : ∑ ω, (1 : Matrix B B ℂ) ⊗ₖ ((M ω)ᴴ * M ω) =
      (1 : Matrix B B ℂ) ⊗ₖ ∑ ω, (M ω)ᴴ * M ω := by
    ext ⟨b, t⟩ ⟨b', t'⟩
    simp [Matrix.sum_apply, Finset.mul_sum]
  simp only [h, ← Matrix.trace_sum, ← Finset.sum_mul, hsum, hM, one_kronecker_one, Matrix.one_mul]

/-- **Purification of a mixture of emulated oracles.** If row maps `M ω` from the private
register of `E` to the private registers of `F ω` resolve the identity, intertwine every port,
and read the initial substate of `E` as `c ω` times that of `F ω`, then the law of every program
against `E` is the mixture with weights `c ω` of its laws against the `F ω`. -/
theorem outcomeLawWith_eq_sum_of_intertwine {Ω : Type*} [Fintype Ω] (E : EmulatedOracle P In)
    (F : Ω → EmulatedOracle P In) (M : ∀ ω, Matrix (F ω).S E.S ℂ) (c : Ω → ℝ≥0)
    (hM : ∑ ω, (M ω)ᴴ * M ω = 1)
    (hU : ∀ ω i, (F ω).U i * ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M ω) =
      ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M ω) * E.U i)
    (hinit : ∀ ω, MatrixMap.conj (M ω) E.init.matrix = ((c ω : ℝ) : ℂ) • (F ω).init.matrix)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (uSpec P In) W A) (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, W u) → γ) :
    E.toRuntime.outcomeLawWith I x ρ f =
      ∑ ω, (c ω : ℝ≥0∞) • (F ω).toRuntime.outcomeLawWith I x ρ f := by
  have htr (p : Σ u, W u) : (E.toRuntime.jointPost I x ρ p).matrix.trace =
      ∑ ω, ((c ω : ℝ) : ℂ) * ((F ω).toRuntime.jointPost I x ρ p).matrix.trace := by
    rw [← sum_trace_amplifyLeft_conj M hM]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    have hsim := QuantumRuntime.simulation (R₁ := E.toRuntime) (R₂ := (F ω).toRuntime)
      (V := MatrixMap.conj (M ω)) I (fun i r ↦ by
        change MatrixMap.conj ((F ω).U i) ∘ₗ (MatrixMap.conj (M ω)).amplifyLeft (In i) =
          (MatrixMap.conj (M ω)).amplifyLeft (In i) ∘ₗ MatrixMap.conj (E.U i)
        rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul, hU ω i]) x p
    have h' := LinearMap.congr_fun hsim (ρ.matrix ⊗ₖ E.init.matrix)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_kronecker, hinit,
      kronecker_smul, map_smul] at h'
    rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost, ← h', Matrix.trace_smul,
      smul_eq_mul]
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply, QuantumRuntime.outcomeLawWith_apply _ _ _ _ _ hs]
  simp only [Measure.smul_apply, smul_eq_mul, QuantumRuntime.outcomeLawWith_apply _ _ _ _ _ hs,
    htr, Complex.re_sum, Complex.re_ofReal_mul, ← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine tsum_congr fun p ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg, Finset.sum_mul]
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [ENNReal.ofReal_mul (c ω).coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
  · exact fun ω _ ↦ mul_nonneg (c ω).coe_nonneg (SubState.trace_re_nonneg _)

end intertwine

section coherent

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}

/-- The identity on the coherent register next to `M` is block diagonal over the index, with the
identity on `In i` next to `M` on the block of `i`. -/
theorem one_kronecker_eq_submatrix_blockDiagonal' {S S' : Type*} (M : Matrix S' S ℂ) :
    (1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ M =
      (Matrix.blockDiagonal' fun i ↦ (1 : Matrix (In i) (In i) ℂ) ⊗ₖ M).submatrix
        (Equiv.sigmaProdDistrib (fun i ↦ In i) S') (Equiv.sigmaProdDistrib (fun i ↦ In i) S) := by
  ext ⟨⟨i, a⟩, d⟩ ⟨⟨i', a'⟩, d'⟩
  by_cases h : i = i'
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, Matrix.one_apply]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h, h]

/-- **Intertwining passes to the coherent oracle.** If `M` intertwines every port of `E₁` with the
same port of `E₂`, it intertwines their coherent oracles. -/
theorem coherent_U_mul_one_kronecker (E₁ E₂ : EmulatedOracle P In) (M : Matrix E₂.S E₁.S ℂ)
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

variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

/-- The uniform superposition `|Ω|^(-1/2) ∑ ω, |ω⟩` over a finite type, as a column. -/
@[expose]
noncomputable def uniformColumnOn : Matrix Ω Unit ℂ :=
  Matrix.of fun _ _ ↦ cellAmp Ω

omit [DecidableEq Ω] in
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

omit [DecidableEq Ω] in
/-- The density matrix of the uniform superposition is `|u⟩⟨u|` for the uniform column `u`. -/
theorem matrix_uniformState [Nonempty Ω] :
    (uniformState Ω).matrix = MatrixMap.conj (uniformColumnOn Ω) (Matrix.single () () 1) := by
  rw [uniformState, SubInstrument.matrix_post, SubInstrument.branch_ofIsometry_apply,
    SubState.matrix_basis]

omit [DecidableEq Ω] in
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
  rw [← compressedVCOracle_U, compressedVCOracle_U_eq_conj, ← one_kronecker_mul_one_kronecker]
  calc _ = ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
        tableOracle (fun D : Fin k → Database X Y ↦ (D i).lookup) *
        (((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
          ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y)) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix (ofFunDatabases k X Y)) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [one_kronecker_mul_one_kronecker, compressDatabases_mul_self_of_nonempty,
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
    simp [Matrix.mul_apply, Fintype.sum_prod_type, evalRow, oracleUnitary_apply,
      tableOracle_apply, Matrix.one_apply]
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
      (((Fintype.card (Fin k → X → Y) : ℝ≥0)⁻¹ : ℝ) : ℂ) • (romVCOracle k X Y H).init.matrix := by
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

end purified

/-! ## Perfect simulation of k random oracles (Lemma 4.4 for k oracles) -/

section main

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] {L : LocalSig.{uL, vL}} (I : L.Interp)
  {W : QReg → Type w} {A : QReg} {γ : Type*} [MeasurableSpace γ]

/-- Against the k compressed oracles and the purified k-fold random oracle, called through their
classical ports, every program has the same observed law. -/
theorem outcomeLawWith_compressedVCOracle_eq_purifiedVCOracle
    (x : QuantumComp L (uSpec (Fin k) (oIn k X Y)) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).toRuntime.outcomeLawWith I x ρ f =
      (purifiedVCOracle k X Y).toRuntime.outcomeLawWith I x ρ f :=
  EmulatedOracle.outcomeLawWith_eq_of_intertwine _ _ _
    conjTranspose_compressDatabases_mul_basisMatrix_mul_self
    compressedVCOracle_U_mul_one_kronecker conj_compressDatabases_mul_basisMatrix_init I x ρ f

/-- Against the coherent forms of the k compressed oracles and of the purified k-fold random
oracle, every program has the same observed law. -/
theorem outcomeLawWith_coherent_compressedVCOracle_eq_purifiedVCOracle
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).coherent.toRuntime.outcomeLawWith I x ρ f =
      (purifiedVCOracle k X Y).coherent.toRuntime.outcomeLawWith I x ρ f :=
  EmulatedOracle.outcomeLawWith_eq_of_intertwine _ _ _
    conjTranspose_compressDatabases_mul_basisMatrix_mul_self
    (fun _ ↦ EmulatedOracle.coherent_U_mul_one_kronecker _ _ _
      compressedVCOracle_U_mul_one_kronecker)
    conj_compressDatabases_mul_basisMatrix_init I x ρ f

omit [DecidableEq Y] [AddCommGroup Y] in
/-- The weight `|Fin k → X → Y|⁻¹` of each family of functions, as an extended real. -/
theorem coe_inv_card_fun_eq [Nonempty (Fin k → X → Y)] :
    (((Fintype.card (Fin k → X → Y) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.coe_inv (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast]

/-- Against the purified k-fold random oracle, called through its classical ports, the law of
every program is the average over all families `H` of its laws against the random oracles `H`. -/
theorem outcomeLawWith_purifiedVCOracle
    (x : QuantumComp L (uSpec (Fin k) (oIn k X Y)) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (purifiedVCOracle k X Y).toRuntime.outcomeLawWith I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).toRuntime.outcomeLawWith I x ρ f := by
  rw [EmulatedOracle.outcomeLawWith_eq_sum_of_intertwine (purifiedVCOracle k X Y)
    (fun H ↦ romVCOracle k X Y H) (fun H ↦ evalRow H) (fun _ ↦ (Fintype.card _ : ℝ≥0)⁻¹)
    sum_conjTranspose_evalRow_mul_self
    (fun H i ↦ oracleUnitary_kronecker_one_mul_one_kronecker_evalRow_apply H i)
    conj_evalRow_purifiedVCOracle_init I x ρ f]
  simp only [coe_inv_card_fun_eq]

/-- Against the coherent form of the purified k-fold random oracle, the law of every program is
the average over all families `H` of its laws against the coherent random oracles `H`. -/
theorem outcomeLawWith_coherent_purifiedVCOracle
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (purifiedVCOracle k X Y).coherent.toRuntime.outcomeLawWith I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).coherent.toRuntime.outcomeLawWith I x ρ f := by
  rw [EmulatedOracle.outcomeLawWith_eq_sum_of_intertwine (purifiedVCOracle k X Y).coherent
    (fun H ↦ (romVCOracle k X Y H).coherent) (fun H ↦ evalRow H)
    (fun _ ↦ (Fintype.card _ : ℝ≥0)⁻¹) sum_conjTranspose_evalRow_mul_self
    (fun H _ ↦ EmulatedOracle.coherent_U_mul_one_kronecker _ _ _
      fun i ↦ oracleUnitary_kronecker_one_mul_one_kronecker_evalRow_apply H i)
    conj_evalRow_purifiedVCOracle_init I x ρ f]
  simp only [coe_inv_card_fun_eq]

/-- **The k compressed oracles are perfectly indistinguishable from k random oracles**
(ePrint 2025/2166, Lemma 4.4, p. 29, for `k` oracles, as used in Lemma 9.2, p. 58), for programs
calling the oracles through their classical ports: every program, observed through any function
of its leaf, has the same law against `Quantum.compressedVCOracle k X Y` as on average over
uniformly random families `H : Fin k → X → Y` against `Quantum.romVCOracle k X Y H`. Programs are
general: adaptive, with their own local operations and registers, a final register that may
depend on the outcome, and any number of calls on each path. -/
theorem outcomeLawWith_compressedVCOracle
    (x : QuantumComp L (uSpec (Fin k) (oIn k X Y)) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).toRuntime.outcomeLawWith I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).toRuntime.outcomeLawWith I x ρ f := by
  rw [outcomeLawWith_compressedVCOracle_eq_purifiedVCOracle, outcomeLawWith_purifiedVCOracle]

/-- **The coherent k compressed oracles are perfectly indistinguishable from coherent k random
oracles** (ePrint 2025/2166, Lemma 4.4 for `k` oracles, p. 29): the form of
`Quantum.outcomeLawWith_compressedVCOracle` for programs against the coherent oracle, the form in
which `Quantum.Simulates` states property P1 with `κsim = 0`. -/
theorem outcomeLawWith_coherent_compressedVCOracle
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).coherent.toRuntime.outcomeLawWith I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).coherent.toRuntime.outcomeLawWith I x ρ f := by
  rw [outcomeLawWith_coherent_compressedVCOracle_eq_purifiedVCOracle,
    outcomeLawWith_coherent_purifiedVCOracle]

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
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ • (R ω).outcomeLawWith I x ρ (f ω) := by
  rw [mixedLawWith, Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [StdSimplex.weights_barycenter_apply,
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_natCast]

/-- **P1 for the k compressed oracles with `κsim = 0`** (ePrint 2025/2166, Lemma 4.4, p. 29, for
`k` oracles, as used in Lemma 9.2, p. 58): the coherent k compressed oracles simulate the
random-oracle model, the uniform distribution over the families `H : Fin k → X → Y` of
`Quantum.romVCOracle k X Y H`, with no error. -/
theorem simulates_compressedVCOracle :
    Simulates (StdSimplex.barycenter : StdSimplex ℝ (Fin k → X → Y))
      (fun H ↦ (romVCOracle k X Y H).coherent.toRuntime) (compressedVCOracle k X Y) 0 := by
  intro t A W x f ρ _
  rw [mixedLawWith_barycenter, outcomeLawWith_coherent_compressedVCOracle]
  simp only [Pi.zero_apply, add_zero, le_refl, and_self]

/-- Against a uniformly sampled random oracle, every program has the same law against the
coherent k compressed oracles as in the random-oracle model (`Quantum.sampledLawWith`). -/
theorem outcomeLawWith_coherent_compressedVCOracle_eq_sampledLawWith
    [SampleableType (Fin k → X → Y)] {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {A : QReg} {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).coherent.toRuntime.outcomeLawWith I x ρ f =
      sampledLawWith (fun H ↦ (romVCOracle k X Y H).coherent.toRuntime) I x ρ fun _ ↦ f := by
  rw [outcomeLawWith_coherent_compressedVCOracle, sampledLawWith_eq_sum, Finset.smul_sum]

/-- The classical-port form of `outcomeLawWith_coherent_compressedVCOracle_eq_sampledLawWith`. -/
theorem outcomeLawWith_compressedVCOracle_eq_sampledLawWith [SampleableType (Fin k → X → Y)]
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg} {γ : Type*}
    [MeasurableSpace γ] (x : QuantumComp L (uSpec (Fin k) (oIn k X Y)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedVCOracle k X Y).toRuntime.outcomeLawWith I x ρ f =
      sampledLawWith (fun H ↦ (romVCOracle k X Y H).toRuntime) I x ρ fun _ ↦ f := by
  rw [outcomeLawWith_compressedVCOracle, sampledLawWith_eq_sum, Finset.smul_sum]

/-- **P1 for the k compressed oracles with `κsim = 0`, against a sampleable random oracle**: the
form of `Quantum.simulates_compressedVCOracle` for the uniform distribution
`Quantum.uniformWeights` of a sampleable type of families. -/
theorem simulates_uniformWeights_compressedVCOracle [SampleableType (Fin k → X → Y)] :
    Simulates (uniformWeights (Fin k → X → Y))
      (fun H ↦ (romVCOracle k X Y H).coherent.toRuntime) (compressedVCOracle k X Y) 0 :=
  Simulates.ofUniform fun t A W x f ρ _ ↦ by
    rw [outcomeLawWith_coherent_compressedVCOracle_eq_sampledLawWith]
    simp only [Pi.zero_apply, add_zero, le_refl, and_self]

/-- **The k compressed oracles commute** (ePrint 2025/2166, Lemma 9.2 first equation,
p. 58), in the form of the first half of property P2 (Definition 7.3, p. 50). -/
theorem oraclesCommute_compressedVCOracle : OraclesCommute (compressedVCOracle k X Y) :=
  fun i j ↦ compressedVCOracle_commute i j

end definition

end Quantum
