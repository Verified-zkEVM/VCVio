/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Commutativity
public import VCVio.Quantum.VC.Proof.Offline
public import VCVio.Quantum.Oracle.Compressed.CollisionRuntime

/-!
# Recording grades and summed branch comparisons

Occupied commitment keys and database entries form a coherent joint grade. Summed branch Gram
bounds give both directed square-root inequalities with the same source total weight.
The recording swap follows Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Definition 9.8 and
Lemmas 9.10–9.12, pp. 66–67. Ordinary coherent ports specialize to selected oracle mass.
-/

public section

open Matrix
open scoped Kronecker ENNReal ComplexOrder

namespace Quantum

section
variable {Q Yr S Cell : Type*} {T : Q → Type*}
  [∀ q, DecidableEq (T q)]

/-- Swap each unsplit cell with the split cell selected by its dependent label. -/
@[expose]
def cellSwap (f : ∀ q, T q) (R : (Q → Cell) × ((Σ q, T q) → Cell)) :=
  (fun q ↦ R.2 ⟨q, f q⟩, fun qt : Σ q, T q ↦ if qt.2 = f qt.1 then R.1 qt.1 else R.2 qt)

/-- Equality of spectator cells is transported from unsplit to split recording. -/
theorem cellSwap_rest (f : ∀ q, T q) (q : Q)
    (R R' : (Q → Cell) × ((Σ q, T q) → Cell)) :
    ((∀ p, p ≠ q → (cellSwap f R).1 p = (cellSwap f R').1 p) ∧
      (cellSwap f R).2 = (cellSwap f R').2) ↔
    (R.1 = R'.1 ∧ ∀ qt : Σ q, T q, qt ≠ ⟨q, f q⟩ → R.2 qt = R'.2 qt) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨funext fun p ↦ ?_, fun qt hqt ↦ ?_⟩
    · simpa [cellSwap] using congrFun h₂ ⟨p, f p⟩
    · obtain ⟨p, t⟩ := qt
      by_cases ht : t = f p
      · subst ht
        exact h₁ p (fun hp ↦ hqt (by subst hp; rfl))
      · simpa [cellSwap, ht] using congrFun h₂ ⟨p, t⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p hp ↦ ?_, funext fun qt ↦ ?_⟩
    · exact h₂ ⟨p, f p⟩ fun he ↦ hp (congrArg Sigma.fst he)
    · obtain ⟨p, t⟩ := qt
      by_cases ht : t = f p
      · simp [cellSwap, ht, h₁]
      · have hn : (⟨p, t⟩ : Σ q, T q) ≠ ⟨q, f q⟩ := by
          intro he
          have hp := congrArg Sigma.fst he
          subst hp
          exact ht (eq_of_heq (Sigma.mk.inj he).2)
        simpa [cellSwap, ht] using h₂ ⟨p, t⟩ hn

end

namespace RecReg

variable {k : ℕ} {Cm Cell : Type*} {Dm : Fin k → Type*}

section population

variable [Fintype Cm] [∀ i, Fintype (Dm i)]

/-- The occupied keys, including both the unsplit cell and every split cell at that key. -/
@[expose]
noncomputable def occupied (bot : Cell) (R : RecReg k Cm Dm Cell) : Finset (TpIC k Cm) :=
  open Classical in
  Finset.univ.filter fun q ↦ R.1 q ≠ bot ∨ ∃ t, R.2 ⟨q, t⟩ ≠ bot

/-- Membership in the occupied-key set. -/
@[simp]
theorem mem_occupied (bot : Cell) (R : RecReg k Cm Dm Cell) (q : TpIC k Cm) :
    q ∈ occupied bot R ↔ R.1 q ≠ bot ∨ ∃ t, R.2 ⟨q, t⟩ ≠ bot := by
  classical
  simp [occupied]

/-- The number of occupied keys of a recording register. -/
@[expose]
noncomputable def population (bot : Cell) (R : RecReg k Cm Dm Cell) : ℕ :=
  (occupied bot R).card

/-- An empty record has no occupied keys, also when the key type is empty. -/
@[simp]
theorem occupied_const (bot : Cell) :
    occupied bot (const bot : RecReg k Cm Dm Cell) = ∅ := by
  classical
  simp [occupied, const]

/-- An empty record has zero population. -/
@[simp]
theorem population_const (bot : Cell) :
    population bot (const bot : RecReg k Cm Dm Cell) = 0 := by
  simp [population]

/-- Changing only cells at one key increases the recording population by at most one. -/
theorem population_le_of_eq_off_key (bot : Cell) (R R' : RecReg k Cm Dm Cell)
    (q : TpIC k Cm) (h₁ : ∀ p, p ≠ q → R'.1 p = R.1 p)
    (h₂ : ∀ p, p ≠ q → ∀ t, R'.2 ⟨p, t⟩ = R.2 ⟨p, t⟩) :
    population bot R' ≤ population bot R + 1 := by
  classical
  have hsub : occupied bot R' ⊆ insert q (occupied bot R) := by
    intro p hp
    by_cases hpq : p = q
    · simp [hpq]
    · rw [Finset.mem_insert]
      right
      simpa only [mem_occupied, h₁ p hpq, h₂ p hpq] using hp
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

end population

variable [∀ i, DecidableEq (Dm i)]
  {S : Type*} (ME : MultiExtractor k Cm Dm S)

/-- Swap the unsplit cell at every key with the cell selected by extraction at that key. -/
@[expose]
def swap (s : S) (R : RecReg k Cm Dm Cell) : RecReg k Cm Dm Cell :=
  (fun q ↦ R.2 ⟨q, ME.extract q s⟩,
    fun qt ↦ if qt.2 = ME.extract qt.1 s then R.1 qt.1 else R.2 qt)

/-- Swapping twice restores all recording cells. -/
@[simp]
theorem swap_swap (s : S) (R : RecReg k Cm Dm Cell) : swap ME s (swap ME s R) = R := by
  apply Prod.ext
  · funext q
    simp [swap]
  · funext qt
    rcases qt with ⟨q, t⟩
    by_cases ht : t = ME.extract q s
    · subst ht
      simp [swap]
    · simp [swap, ht]

/-- The recording swap as an involutive basis permutation. -/
@[expose]
def swapEquiv (s : S) : Equiv.Perm (RecReg k Cm Dm Cell) where
  toFun := swap ME s
  invFun := swap ME s
  left_inv := swap_swap ME s
  right_inv := swap_swap ME s

/-- The swap fixes the all-bottom record for every private basis state. -/
@[simp]
theorem swap_const (s : S) (bot : Cell) :
    swap ME s (const bot : RecReg k Cm Dm Cell) = const bot := by
  apply Prod.ext
  · rfl
  · funext qt
    simp [swap, const]

/-- Equality off the unsplit queried cell after swapping is equality off the selected split
cell before swapping. This identifies the spectator registers in recording conjugacy. -/
theorem swap_rest_eq_iff (s : S) (q : TpIC k Cm) (R R' : RecReg k Cm Dm Cell) :
    ((∀ p, p ≠ q → (swap ME s R).1 p = (swap ME s R').1 p) ∧
      (swap ME s R).2 = (swap ME s R').2) ↔
    (R.1 = R'.1 ∧ ∀ qt : TpICD k Cm Dm,
      qt ≠ ⟨q, ME.extract q s⟩ → R.2 qt = R'.2 qt) := by
  exact cellSwap_rest (fun q ↦ ME.extract q s) q R R'


variable [Fintype Cm] [∀ i, Fintype (Dm i)]

/-- The swap preserves the occupied keys exactly. -/
@[simp]
theorem occupied_swap (s : S) (bot : Cell) (R : RecReg k Cm Dm Cell) :
    occupied bot (swap ME s R) = occupied bot R := by
  classical
  have forward (R : RecReg k Cm Dm Cell) :
      occupied bot (swap ME s R) ⊆ occupied bot R := by
    intro q hq
    rw [mem_occupied] at hq ⊢
    rcases hq with hq | ⟨t, ht⟩
    · exact Or.inr ⟨ME.extract q s, hq⟩
    · change (if t = ME.extract q s then R.1 q else R.2 ⟨q, t⟩) ≠ bot at ht
      split_ifs at ht
      · exact Or.inl ht
      · exact Or.inr ⟨t, ht⟩
  exact Finset.Subset.antisymm (forward R) (by simpa using forward (swap ME s R))

/-- The recording population is invariant under the swap. -/
@[simp]
theorem population_swap (s : S) (bot : Cell) (R : RecReg k Cm Dm Cell) :
    population bot (swap ME s R) = population bot R := by
  simp [population]

/-- The swap acts identically on a record with no occupied keys. -/
theorem swap_eq_self_of_population_eq_zero (s : S) (bot : Cell)
    (R : RecReg k Cm Dm Cell) (h : population bot R = 0) : swap ME s R = R := by
  have hR : R = const bot := by
    have he : occupied bot R = ∅ := Finset.card_eq_zero.mp h
    have hz (q : TpIC k Cm) : R.1 q = bot ∧ ∀ t, R.2 ⟨q, t⟩ = bot := by
      have hn : q ∉ occupied bot R := by simp [he]
      simpa only [mem_occupied, not_or, not_not, not_exists] using hn
    exact Prod.ext (funext fun q ↦ (hz q).1) (funext fun qt ↦ (hz qt.1).2 qt.2)
  simp [hR]

/-- On a given recording basis state, the swap depends only on extractor outputs at occupied
keys. Thus an empty list of relevant outputs also gives an exact, constant action. -/
theorem swap_eq_of_extract_eq_on_occupied (s s' : S) (bot : Cell)
    (R : RecReg k Cm Dm Cell)
    (h : ∀ q ∈ occupied bot R, ME.extract q s = ME.extract q s') :
    swap ME s R = swap ME s' R := by
  classical
  have hz (q : TpIC k Cm) (hq : q ∉ occupied bot R) :
      R.1 q = bot ∧ ∀ t, R.2 ⟨q, t⟩ = bot := by
    simpa only [mem_occupied, not_or, not_not, not_exists] using hq
  apply Prod.ext
  · funext q
    by_cases hq : q ∈ occupied bot R
    · simp only [swap, h q hq]
    · exact ((hz q hq).2 _).trans ((hz q hq).2 _).symm
  · funext qt
    obtain ⟨q, t⟩ := qt
    by_cases hq : q ∈ occupied bot R
    · simp only [swap, h q hq]
    · simp [swap, (hz q hq).1, (hz q hq).2]

end RecReg

section locality

variable {Q Yr S Rg K Cell G : Type*} [DecidableEq Q] [DecidableEq S]
  [Fintype K] [DecidableEq K] [DecidableEq Cell] [DecidableEq G]

/-- A cell-controlled matrix entry changes only the selected cell and the response. -/
theorem cellControlled_apply (eR : Rg ≃ (K → Cell) × G) (β : Q × S → K)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (a b : (Q × Yr) × (S × Rg)) :
    cellControlled eR β U a b =
      if a.1.1 = b.1.1 ∧ a.2.1 = b.2.1 ∧
        (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦ (eR a.2.2).1 j) =
          (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦ (eR b.2.2).1 j) ∧
        (eR a.2.2).2 = (eR b.2.2).2 then
          U (a.1.2, (eR a.2.2).1 (β (a.1.1, a.2.1)))
            (b.1.2, (eR b.2.2).1 (β (a.1.1, a.2.1))) else 0 := by
  rw [cellControlled, labelControlled_apply, onFactor_apply]
  simp only [cellSplit, Equiv.coe_fn_mk, Prod.mk.injEq]

/-- A nonzero cell-controlled matrix entry preserves the control, private state, and all
recording cells other than the selected key. No unitarity assumption is needed. -/
theorem cellControlled_locality (eR : Rg ≃ (K → Cell) × G) (β : Q × S → K)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (a b : (Q × Yr) × (S × Rg)) (h : cellControlled eR β U a b ≠ 0) :
    a.1.1 = b.1.1 ∧ a.2.1 = b.2.1 ∧
      (∀ j, j ≠ β (a.1.1, a.2.1) → (eR a.2.2).1 j = (eR b.2.2).1 j) ∧
      (eR a.2.2).2 = (eR b.2.2).2 := by
  rw [cellControlled, labelControlled_apply] at h
  have he := eq_of_onFactor_apply_ne_zero h
  change (a.1.1, a.2.1, (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦
      (eR a.2.2).1 j), (eR a.2.2).2) =
    (b.1.1, b.2.1, (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦
      (eR b.2.2).1 j), (eR b.2.2).2) at he
  simp only [Prod.mk.injEq] at he
  exact ⟨he.1, he.2.1, fun j hj ↦ congrFun he.2.2.1 ⟨j, hj⟩, he.2.2.2⟩

end locality

section cellConjugacy

variable {Q Yr S Cell : Type*} {T : Q → Type*}
  [Fintype Q] [DecidableEq Q] [∀ q, Fintype (T q)] [∀ q, DecidableEq (T q)]
  [DecidableEq S] [DecidableEq Cell]

/-- Conjugating unsplit cell control by the dependent cell swap gives split cell control.
The concrete key and cell types keep dependent reindexing explicit. -/
theorem cellControlled_swap (f : S → ∀ q, T q)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (q p : Q) (y z : Yr) (s r : S)
    (R R' : (Q → Cell) × ((Σ q, T q) → Cell)) :
    cellControlled (Equiv.refl _) Prod.fst U ((q, y), (s, cellSwap (f s) R))
      ((p, z), (r, cellSwap (f r) R')) =
    cellControlled (Equiv.prodComm _ _) (fun a : Q × S ↦ ⟨a.1, f a.2 a.1⟩)
      U ((q, y), (s, R)) ((p, z), (r, R')) := by
  classical
  rw [cellControlled_apply, cellControlled_apply]
  dsimp only [Equiv.refl_apply, Equiv.prodComm_apply]
  by_cases hq : q = p
  · subst p
    by_cases hs : s = r
    · subst r
      simp only [eq_self, true_and, funext_iff, Subtype.forall]
      apply if_congr
      · simpa only [funext_iff, Prod.swap, Subtype.forall] using
          (cellSwap_rest (f s) q R R').trans and_comm
      · rfl
      · rfl
    · simp only [hs, and_false, false_and, ite_false]
  · simp only [hq, false_and, ite_false]

end cellConjugacy

section
variable {k : ℕ} {Cm Yr S Cell : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [DecidableEq Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  [DecidableEq S] [DecidableEq Cell]
/-- The recording swap conjugates the two recording ports entrywise. -/
theorem recordUnitary_swap_apply (ME : MultiExtractor k Cm Dm S)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (q p : TpIC k Cm) (y z : Yr) (s r : S) (R R' : RecReg k Cm Dm Cell) :
    recordUnitary U ((q, y), (s, RecReg.swap ME s R))
      ((p, z), (r, RecReg.swap ME r R')) =
    recordMEUnitary ME U ((q, y), (s, R)) ((p, z), (r, R')) := by
  exact cellControlled_swap (fun s q ↦ ME.extract q s) U q p y z s r R R'
end

namespace RecReg
variable {k : ℕ} {Cm Cell S : Type*} {Dm : Fin k → Type*}
  [∀ i, DecidableEq (Dm i)] (ME : MultiExtractor k Cm Dm S)
/-- The extraction-controlled swap on the entire private register. -/
@[expose]
def privateSwapEquiv : Equiv.Perm (S × RecReg k Cm Dm Cell) :=
  Equiv.prodCongrRight (swapEquiv ME)
/-- The private swap keeps the oracle basis state and swaps its recording cells. -/
@[simp]
theorem privateSwapEquiv_apply (s : S) (R : RecReg k Cm Dm Cell) :
    privateSwapEquiv ME (s, R) = (s, swap ME s R) := rfl
/-- The private swap is its own inverse. -/
@[simp]
theorem privateSwapEquiv_symm : (privateSwapEquiv (Cell := Cell) ME).symm =
    privateSwapEquiv ME := rfl
variable [Fintype Cm] [∀ i, Fintype (Dm i)] [DecidableEq S] [DecidableEq Cell]
/-- The unitary basis matrix of the private recording swap (ePrint 2025/2166,
Definition 9.8, p. 66). -/
@[expose]
noncomputable def swapUnitary : Matrix (S × RecReg k Cm Dm Cell)
    (S × RecReg k Cm Dm Cell) ℂ := basisMatrix (privateSwapEquiv ME)
/-- The recording swap is unitary, with no hypothesis on the extractor. -/
theorem swapUnitary_mem_unitaryGroup [DecidableEq Cm] [Fintype S] [Fintype Cell] :
    swapUnitary (Cell := Cell) ME ∈ unitaryGroup _ ℂ :=
  basisMatrix_perm_mem_unitaryGroup _
/-- The recording swap is Hermitian. -/
@[simp]
theorem swapUnitary_conjTranspose : (swapUnitary (Cell := Cell) ME)ᴴ = swapUnitary ME := by
  rw [swapUnitary, conjTranspose_basisMatrix_equiv, privateSwapEquiv_symm]
/-- The swap fixes arbitrary oracle states tensored with the empty recording register. -/
theorem swapUnitary_initial [DecidableEq Cm] [Fintype S] [Fintype Cell]
    (σ : Matrix S S ℂ) (bot : Cell) :
    MatrixMap.conj (swapUnitary ME) (σ ⊗ₖ (SubState.basis (const bot)).matrix) =
      σ ⊗ₖ (SubState.basis (const bot)).matrix := by
  rw [swapUnitary, conj_basisMatrix_equiv, privateSwapEquiv_symm]
  ext ⟨s, R⟩ ⟨r, R'⟩
  have hs (s : S) (R : RecReg k Cm Dm Cell) :
      const bot = swap ME s R ↔ const bot = R := by
    constructor
    · intro h
      have hh := congrArg (swap ME s) h
      simpa only [swap_swap, swap_const] using hh
    · rintro rfl
      exact (swap_const ME s bot).symm
  simp only [submatrix_apply, privateSwapEquiv_apply, kroneckerMap_apply,
    SubState.matrix_basis, single_apply, hs]
end RecReg
section
variable {k : ℕ} {Cm Yr S Cell : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  [DecidableEq Yr] [DecidableEq S] [DecidableEq Cell]
/-- Framing the private swap by an identity is the corresponding basis permutation. -/
theorem one_kronecker_swapUnitary (ME : MultiExtractor k Cm Dm S) :
    (1 : Matrix Yr Yr ℂ) ⊗ₖ RecReg.swapUnitary (Cell := Cell) ME =
      basisMatrix (Equiv.prodCongr (Equiv.refl Yr) (RecReg.privateSwapEquiv ME)) := by
  ext ⟨y, s, R⟩ ⟨z, r, R'⟩
  simp only [RecReg.swapUnitary, kroneckerMap_apply, one_apply, basisMatrix_apply,
    Equiv.prodCongr_apply]
  split_ifs <;> simp_all

variable [DecidableEq Cm] [Fintype Yr] [Fintype S] [Fintype Cell]

/-- Exact recording-port conjugacy, ePrint 2025/2166, Lemma 9.13, p. 67. -/
theorem recordUnitary_swap_conjugacy (ME : MultiExtractor k Cm Dm S)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) :
    ((1 : Matrix (TpIC k Cm × Yr) (TpIC k Cm × Yr) ℂ) ⊗ₖ RecReg.swapUnitary ME)ᴴ *
      recordUnitary U * (1 ⊗ₖ RecReg.swapUnitary ME) = recordMEUnitary ME U := by
  rw [one_kronecker_swapUnitary, conjTranspose_basisMatrix_mul_mul_basisMatrix]
  ext ⟨⟨q, y⟩, s, R⟩ ⟨⟨p, z⟩, r, R'⟩
  exact recordUnitary_swap_apply ME U q p y z s r R R'
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [AddGroup Z]
/-- The private recording swap commutes with purified extraction, ePrint 2025/2166,
Lemma 9.7, p. 69. -/
theorem extractUnitary_swap_conjugacy (ME : MultiExtractor k Cm Dm S)
    (code : TpDCode k Dm Z) :
    ((1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ RecReg.swapUnitary ME)ᴴ *
      reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
        (extractUnitary ME code ⊗ₖ
          (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ)) *
      (1 ⊗ₖ RecReg.swapUnitary ME) =
      reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
        (extractUnitary ME code ⊗ₖ (1 : Matrix (RecReg k Cm Dm Cell)
          (RecReg k Cm Dm Cell) ℂ)) := by
  rw [one_kronecker_swapUnitary, conjTranspose_basisMatrix_mul_mul_basisMatrix]
  ext ⟨⟨q, y⟩, s, R⟩ ⟨⟨p, z⟩, r, R'⟩
  simp only [submatrix_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    RecReg.privateSwapEquiv_apply, reindex_apply, Equiv.prodAssoc_symm_apply,
    kroneckerMap_apply, extractUnitary_apply, one_apply]
  by_cases hs : s = r
  · subst r
    have hr : RecReg.swap ME s R = RecReg.swap ME s R' ↔ R = R' :=
      (RecReg.swapEquiv ME s).injective.eq_iff
    simp only [hr]
  · simp only [hs, and_false, ite_false, zero_mul]
end

section
variable {A B : Type*}
/-- Right multiplication by a permutation matrix relabels columns. -/
theorem mul_basisMatrix_perm_apply [Fintype B] [DecidableEq B] (M : Matrix A B ℂ) (e : Equiv.Perm B)
    (a : A) (b : B) :
    (M * basisMatrix e) a b = M a (e b) := by
  simp [mul_apply, basisMatrix_apply, mul_ite]
end
section
variable {Q S R : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] [DecidableEq S]
  [Fintype R] [DecidableEq R]
/-- The commutator with a private controlled permutation, entrywise. -/
theorem controlledPermutation_commutator_apply
    (e : S → Equiv.Perm R) (M : Matrix (Q × S) (Q × S) ℂ)
    (q p : Q) (s r : S) (v w : R) :
    let V := basisMatrix (Equiv.prodCongr (Equiv.refl Q) (Equiv.prodCongrRight e))
    let O := reindex (Equiv.prodAssoc Q S R) (Equiv.prodAssoc Q S R)
      (M ⊗ₖ (1 : Matrix R R ℂ))
    (V * O - O * V) (q, s, v) (p, r, w) =
      M (q, s) (p, r) * ((if v = e s w then 1 else 0) - if v = e r w then 1 else 0) := by
  dsimp only
  rw [Matrix.sub_apply, basisMatrix_equiv_mul_apply, mul_basisMatrix_perm_apply]
  simp only [reindex_apply, submatrix_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, Equiv.prodCongrRight_symm,
    Equiv.prodCongrRight_apply, Function.comp_apply, Equiv.prodAssoc_symm_apply,
    kroneckerMap_apply, one_apply, Equiv.symm_apply_eq, mul_sub]
end

namespace RecReg
variable {k : ℕ} {Cm Cell S T : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
/-- Extractors agreeing on occupied keys induce the same swap on that basis state. -/
theorem swap_eq_of_extract_eq (ME : MultiExtractor k Cm Dm S)
    (ME' : MultiExtractor k Cm Dm T) (s : S) (t : T) (bot : Cell)
    (R : RecReg k Cm Dm Cell)
    (h : ∀ q ∈ occupied bot R, ME.extract q s = ME'.extract q t) :
    swap ME s R = swap ME' t R := by
  exact swap_eq_of_extract_eq_on_occupied
    (⟨fun q ↦ Sum.elim (ME.extract q) (ME'.extract q)⟩ :
      MultiExtractor k Cm Dm (S ⊕ T)) (.inl s) (.inr t) bot R h
/-- Extend labels on a finite key set using fixed fallback values on other keys. -/
@[expose]
noncomputable def restrictedExtractor (ME : MultiExtractor k Cm Dm S)
    (keys : Finset (TpIC k Cm)) (s₀ : S) :
    MultiExtractor k Cm Dm (∀ q : keys, TpDLen k Dm q.1.1) :=
  open Classical in
  ⟨fun q l ↦ if h : q ∈ keys then l ⟨q, h⟩ else ME.extract q s₀⟩
/-- On an occupied-key sector, the swap is controlled only by that sector's labels. -/
theorem swap_restrictedExtractor (ME : MultiExtractor k Cm Dm S)
    (keys : Finset (TpIC k Cm)) (s₀ s : S) (bot : Cell) (R : RecReg k Cm Dm Cell)
    (hR : occupied bot R ⊆ keys) :
    swap (restrictedExtractor ME keys s₀) (fun q ↦ ME.extract q.1 s) R = swap ME s R := by
  apply swap_eq_of_extract_eq _ _ _ _ bot
  intro q hq
  simp [restrictedExtractor, hR hq]
end RecReg

open OracleSpec
open scoped Matrix.Norms.L2Operator

section
variable {X Y B : Type} {ι : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [UniformAnswerMeasure (X →ₒ Y)] [Fintype B] [DecidableEq B]
/-- Transfer the generalized commutator bound to a database source cutoff. The output
cutoff is one larger, as the ordinary port can create one database entry. The squared norm
is bounded by 24 times the joint-label instability. -/
theorem l2_opNorm_source_commutator_sq_le (π : Database X Y → ι) (t : ℕ)
    (U : ι → Matrix B B ℂ) (hU : ∀ l, U l ∈ unitaryGroup _ ℂ) :
    let L := labelControlled (fun a : ((X × Y) × Database X Y) × B ↦ π a.1.2)
      (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U l)
    ‖(L * (compressedOracle X Y ⊗ₖ (1 : Matrix B B ℂ)) -
      (compressedOracle X Y ⊗ₖ (1 : Matrix B B ℂ)) * L) *
      (sizeProjector X Y t ⊗ₖ (1 : Matrix B B ℂ))‖ ^ 2 ≤
      24 * (Database.instability π (t + 1)).toReal := by
  dsimp only
  rw [commutator_mul_sizeProjector_kronecker_eq t _
    (labelControlled_mul_sizeProjector_kronecker π U t)]
  have hp : ‖sizeProjector X Y t ⊗ₖ (1 : Matrix B B ℂ)‖ ≤ 1 := by
    apply (l2_opNorm_kronecker_one_le _).trans
    rw [sizeProjector, l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro a
    split_ifs <;> norm_num
  have hm := l2_opNorm_mul
    (labelControlled (fun a : ((X × Y) × Database X Y) × B ↦ π a.1.2)
      (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U l) *
      (truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix B B ℂ)) -
      (truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix B B ℂ)) *
      labelControlled (fun a ↦ π a.1.2) (fun l ↦ 1 ⊗ₖ U l))
    (sizeProjector X Y t ⊗ₖ (1 : Matrix B B ℂ))
  have hn := hm.trans (mul_le_of_le_one_right (norm_nonneg _) hp)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul π (t + 1) hU)
end

section
variable {Q S R ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] [DecidableEq S]
  [Fintype R] [DecidableEq R]
/-- A label-controlled permutation has an entrywise commutator formula without matrix sums. -/
theorem labelControlled_permutation_commutator_apply (π : S → ι)
    (e : ι → Equiv.Perm R) (M : Matrix (Q × S) (Q × S) ℂ)
    (a b : Q × S) (v w : R) :
    let L := labelControlled (fun a : (Q × S) × R ↦ π a.1.2)
      (fun l ↦ (1 : Matrix (Q × S) (Q × S) ℂ) ⊗ₖ basisMatrix (e l))
    (L * (M ⊗ₖ (1 : Matrix R R ℂ)) - (M ⊗ₖ (1 : Matrix R R ℂ)) * L)
        (a, v) (b, w) =
      M a b * ((if v = e (π a.2) w then 1 else 0) - if v = e (π b.2) w then 1 else 0) := by
  have hl : labelControlled (fun a : (Q × S) × R ↦ π a.1.2)
      (fun l ↦ (1 : Matrix (Q × S) (Q × S) ℂ) ⊗ₖ basisMatrix (e l)) =
      basisMatrix (Equiv.prodCongrRight fun a : Q × S ↦ e (π a.2)) := by
    ext ⟨a, r⟩ ⟨b, s⟩
    simp only [labelControlled_apply, kroneckerMap_apply, one_apply, basisMatrix_apply,
      Equiv.prodCongrRight_apply, Prod.mk.injEq]
    by_cases h : a = b
    · subst b
      simp
    · simp [h]
  dsimp only
  rw [hl, Matrix.sub_apply, basisMatrix_equiv_mul_apply, mul_basisMatrix_perm_apply]
  simp only [Equiv.prodCongrRight_symm, Equiv.prodCongrRight_apply, Function.comp_apply,
    kroneckerMap_apply, one_apply, Equiv.symm_apply_eq, mul_sub]
end

section
variable {Q S R : Type*} [DecidableEq R]
/-- The entrywise commutator of a controlled private permutation with an ordinary port. -/
@[expose]
noncomputable def permutationDefect (e : S → Equiv.Perm R)
    (M : Matrix (Q × S) (Q × S) ℂ) : Matrix (Q × S × R) (Q × S × R) ℂ :=
  fun a b ↦ M (a.1, a.2.1) (b.1, b.2.1) *
    ((if a.2.2 = e a.2.1 b.2.2 then 1 else 0) -
      if a.2.2 = e b.2.1 b.2.2 then 1 else 0)
end
section
variable {k : ℕ} {Cm Cell S Q : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [DecidableEq Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  [Fintype Cell] [DecidableEq Cell] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]
/-- Occupied-key sectors lift uniform sector bounds to the coherent recording register. -/
theorem l2_opNorm_recordingDefect_le
    (ME : MultiExtractor k Cm Dm S) (M : Matrix (Q × S) (Q × S) ℂ)
    (g : S → ℕ) (bot : Cell) (t : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (s₀ : S)
    (hlocal : ∀ keys : Finset (TpIC k Cm),
      ‖permutationDefect
          (fun s ↦ RecReg.swapEquiv (RecReg.restrictedExtractor ME keys s₀)
            (fun q ↦ ME.extract q.1 s)) M *
        diagonal (fun a : Q × S × RecReg k Cm Dm Cell ↦
          if g a.2.1 + keys.card ≤ t then (1 : ℂ) else 0)‖ ≤ c) :
    ‖permutationDefect (RecReg.swapEquiv ME) M *
      diagonal (fun a : Q × S × RecReg k Cm Dm Cell ↦
        if g a.2.1 + RecReg.population bot a.2.2 ≤ t then (1 : ℂ) else 0)‖ ≤ c := by
  classical
  let β : Q × S × RecReg k Cm Dm Cell → Finset (TpIC k Cm) :=
    fun a ↦ RecReg.occupied bot a.2.2
  refine l2_opNorm_le_of_submatrix_le β β ?_ hc ?_
  · intro a b hab
    rw [mul_diagonal] at hab
    have hd := left_ne_zero_of_mul hab
    unfold permutationDefect at hd
    have hn := right_ne_zero_of_mul hd
    split_ifs at hn with h₁ h₂ h₂
    · simp at hn
    · change RecReg.occupied bot a.2.2 = RecReg.occupied bot b.2.2
      rw [h₁]
      exact RecReg.occupied_swap ME a.2.1 bot b.2.2
    · change RecReg.occupied bot a.2.2 = RecReg.occupied bot b.2.2
      rw [h₂]
      exact RecReg.occupied_swap ME b.2.1 bot b.2.2
    · simp at hn
  · intro keys
    let K := permutationDefect
      (fun s ↦ RecReg.swapEquiv (RecReg.restrictedExtractor ME keys s₀)
        (fun q ↦ ME.extract q.1 s)) M *
      diagonal (fun a : Q × S × RecReg k Cm Dm Cell ↦
        if g a.2.1 + keys.card ≤ t then (1 : ℂ) else 0)
    have he : (permutationDefect (RecReg.swapEquiv ME) M *
        diagonal (fun a : Q × S × RecReg k Cm Dm Cell ↦
          if g a.2.1 + RecReg.population bot a.2.2 ≤ t then (1 : ℂ) else 0)).submatrix
          (Subtype.val : {a // β a = keys} → _) (Subtype.val : {a // β a = keys} → _) =
        K.submatrix (Subtype.val : {a // β a = keys} → _)
          (Subtype.val : {a // β a = keys} → _) := by
      ext a b
      have hb : RecReg.occupied bot b.1.2.2 = keys := b.2
      have hs (s : S) := RecReg.swap_restrictedExtractor ME keys s₀ s bot b.1.2.2
        (Finset.Subset.trans (Finset.Subset.refl _) (by rw [hb]))
      simp only [submatrix_apply, mul_diagonal, permutationDefect, RecReg.swapEquiv,
        Equiv.coe_fn_mk, hs, RecReg.population, hb, K]
      rfl
    rw [he]
    exact (l2_opNorm_submatrix_le_of_injective K Subtype.val_injective
      Subtype.val_injective).trans (hlocal keys)
end
section
variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
  [DecidableEq n] [DecidableEq n']
/-- Restricting rows and columns and applying a contractive source mask preserves a norm bound. -/
theorem l2_opNorm_submatrix_mul_mask_le (M : Matrix m n ℂ) (f : m' → m) (g : n' → n)
    (hf : Function.Injective f) (hg : Function.Injective g) (p : n' → ℂ)
    (hp : ∀ a, ‖p a‖ ≤ 1) : ‖M.submatrix f g * diagonal p‖ ≤ ‖M‖ := by
  have hd : ‖diagonal p‖ ≤ 1 := by
    rw [l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr hp
  exact ((l2_opNorm_mul _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hd)).trans
    (l2_opNorm_submatrix_le_of_injective M hf hg)
end
section
variable {X Y R : Type} {k : ℕ} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype R] [DecidableEq R]
/-- An ordinary port splits into sectors of the unchanged databases,
with a source population mask. -/
theorem l2_opNorm_familyDefect_source_le (i : Fin k)
    (e : (Fin k → Database X Y) → Equiv.Perm R) (n t : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hlocal : ∀ Dfix : Fin k → Database X Y,
      ‖permutationDefect (fun d ↦ e (Function.update Dfix i d)) (compressedOracle X Y) *
        diagonal (fun a : (X × Y) × Database X Y × R ↦
          if a.2.1.size + n ≤ t then (1 : ℂ) else 0)‖ ≤ c) :
    ‖permutationDefect e (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)) *
      diagonal (fun a : (X × Y) × (Fin k → Database X Y) × R ↦
        if (∑ j, (a.2.1 j).size) + n ≤ t then (1 : ℂ) else 0)‖ ≤ c := by
  classical
  let β : (X × Y) × (Fin k → Database X Y) × R → ({j // j ≠ i} → Database X Y) :=
    fun a j ↦ a.2.1 j.1
  have hM (a b : (X × Y) × (Fin k → Database X Y) × R) :
      onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) (a.1, a.2.1) (b.1, b.2.1) =
        if β a = β b then compressedOracle X Y (a.1, a.2.1 i) (b.1, b.2.1 i) else 0 := by
    rw [onFactor_apply]
    rfl
  refine l2_opNorm_le_of_submatrix_le β β ?_ hc ?_
  · intro a b hab
    rw [mul_diagonal] at hab
    have hm := left_ne_zero_of_mul (left_ne_zero_of_mul hab)
    rw [hM] at hm
    split_ifs at hm with h
    · exact h
    · exact (hm rfl).elim
  · intro rest
    let Fiber := {a : (X × Y) × (Fin k → Database X Y) × R // β a = rest}
    let fix : Fin k → Database X Y := (Equiv.funSplitAt i (Database X Y)).symm
      (Database.empty, rest)
    let f : Fiber → (X × Y) × Database X Y × R :=
      fun a ↦ (a.1.1, a.1.2.1 i, a.1.2.2)
    have hd (a : Fiber) : Function.update fix i (a.1.2.1 i) = a.1.2.1 := by
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · rw [Function.update_of_ne hj]
        have ha := congrFun a.2 ⟨j, hj⟩
        simpa only [fix, Equiv.funSplitAt_symm_apply, dite_eq_right hj] using ha.symm
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h₁ := congrArg Prod.fst hab
      have h₂ := congrArg (fun z ↦ z.2.1) hab
      have h₃ := congrArg (fun z ↦ z.2.2) hab
      dsimp only [f] at h₁ h₂ h₃
      have hD : a.1.2.1 = b.1.2.1 := by rw [← hd a, ← hd b, h₂]
      exact Prod.ext h₁ (Prod.ext hD h₃)
    let K := permutationDefect (fun d ↦ e (Function.update fix i d)) (compressedOracle X Y) *
      diagonal (fun a : (X × Y) × Database X Y × R ↦
        if a.2.1.size + n ≤ t then (1 : ℂ) else 0)
    let P0 : Matrix Fiber Fiber ℂ :=
      diagonal (fun a ↦ if (∑ j, (a.1.2.1 j).size) + n ≤ t then 1 else 0)
    have he : (permutationDefect e
        (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)) *
        diagonal (fun a : (X × Y) × (Fin k → Database X Y) × R ↦
          if (∑ j, (a.2.1 j).size) + n ≤ t then (1 : ℂ) else 0)).submatrix
          (Subtype.val : Fiber → _) (Subtype.val : Fiber → _) =
        K.submatrix f f * P0 := by
      ext a b
      have hr : β a.1 = β b.1 := a.2.trans b.2.symm
      have hs : (b.1.2.1 i).size ≤ ∑ j, (b.1.2.1 j).size :=
        Finset.single_le_sum (f := fun j ↦ (b.1.2.1 j).size)
          (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      simp only [submatrix_apply, mul_diagonal, permutationDefect, hM, hr, ite_true,
        K, P0, f, hd]
      by_cases hg : (∑ j, (b.1.2.1 j).size) + n ≤ t
      · have hi : (b.1.2.1 i).size + n ≤ t := by omega
        simp [hg, hi]
      · simp [hg]
    rw [he]
    apply le_trans ?_ (hlocal fix)
    apply l2_opNorm_submatrix_mul_mask_le K f f hf hf
    intro a
    split_ifs <;> norm_num
end

section
variable {X Y B : Type} {ι : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
  [Fintype B] [DecidableEq B]
/-- The source-restricted permutation commutator satisfies the generalized coefficient-24 bound. -/
theorem l2_opNorm_permutationDefect_source_sq_le (π : Database X Y → ι) (t : ℕ)
    (e : ι → Equiv.Perm B) :
    ‖permutationDefect (fun d ↦ e (π d)) (compressedOracle X Y) *
        diagonal (fun a : (X × Y) × Database X Y × B ↦
          if a.2.1.size ≤ t then (1 : ℂ) else 0)‖ ^ 2 ≤
      24 * (Database.instability π (t + 1)).toReal := by
  have h := l2_opNorm_source_commutator_sq_le π t (fun l ↦ basisMatrix (e l))
    (fun l ↦ basisMatrix_perm_mem_unitaryGroup (e l))
  dsimp only at h
  let L := labelControlled (fun a : ((X × Y) × Database X Y) × B ↦ π a.1.2)
    (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
      basisMatrix (e l))
  let C := L * (compressedOracle X Y ⊗ₖ (1 : Matrix B B ℂ)) -
    (compressedOracle X Y ⊗ₖ (1 : Matrix B B ℂ)) * L
  have hp : sizeProjector X Y t ⊗ₖ (1 : Matrix B B ℂ) =
      diagonal (fun a : ((X × Y) × Database X Y) × B ↦
        if a.1.2.size ≤ t then (1 : ℂ) else 0) := by
    rw [sizeProjector, ← diagonal_one, diagonal_kronecker_diagonal]
    simp only [mul_one]
  have he : permutationDefect (fun d ↦ e (π d)) (compressedOracle X Y) *
        diagonal (fun a : (X × Y) × Database X Y × B ↦
          if a.2.1.size ≤ t then (1 : ℂ) else 0) =
      (C * (sizeProjector X Y t ⊗ₖ (1 : Matrix B B ℂ))).submatrix
        (Equiv.prodAssoc (X × Y) (Database X Y) B).symm
        (Equiv.prodAssoc (X × Y) (Database X Y) B).symm := by
    rw [hp]
    ext ⟨xy, d, v⟩ ⟨xy', d', w⟩
    simp only [submatrix_apply, Equiv.prodAssoc_symm_apply, mul_diagonal,
      permutationDefect]
    rw [show C ((xy, d), v) ((xy', d'), w) = _ from
      labelControlled_permutation_commutator_apply π e (compressedOracle X Y)
        (xy, d) (xy', d') v w]
  rw [he, l2_opNorm_submatrix_equiv]
  exact h
end

section
variable {X Y Cm Cell : Type} {k : ℕ} {Dm : Fin k → Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] [Fintype Cm] [DecidableEq Cm]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)] [Fintype Cell] [DecidableEq Cell]
/-- The occupied-key and unchanged-database sector decompositions give the ordinary-port
source bound from joint-label instabilities. Empty occupied sets give zero commutator. -/
theorem l2_opNorm_compressed_recordingDefect_source_sq_le
    (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (bot : Cell)
    (i : Fin k) (t : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hi : ∀ (keys : Finset (TpIC k Cm)), 1 ≤ keys.card → keys.card ≤ t →
      ∀ Dfix : Fin k → Database X Y,
        24 * (Database.instability
          (fun D ↦ fun q : keys ↦ ME.extract q.1 (Function.update Dfix i D))
          (t - keys.card + 1)).toReal ≤ r) :
    ‖permutationDefect (RecReg.swapEquiv ME)
        (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)) *
      diagonal (fun a : (X × Y) × (Fin k → Database X Y) × RecReg k Cm Dm Cell ↦
        if (∑ j, (a.2.1 j).size) + RecReg.population bot a.2.2 ≤ t
        then (1 : ℂ) else 0)‖ ^ 2 ≤ r := by
  refine le_trans ?_ (le_of_eq (Real.sq_sqrt hr))
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg r)).mpr
  apply l2_opNorm_recordingDefect_le ME _ (fun d ↦ ∑ j, (d j).size) bot t
    (Real.sqrt r) (Real.sqrt_nonneg r) (fun _ ↦ Database.empty)
  intro keys
  by_cases hz : keys = ∅
  · subst keys
    have he : ∀ s r : Fin k → Database X Y,
        (fun q : (∅ : Finset (TpIC k Cm)) ↦ ME.extract q.1 s) =
          (fun q : (∅ : Finset (TpIC k Cm)) ↦ ME.extract q.1 r) := by
      intro s r
      exact Subsingleton.elim _ _
    have hzero : permutationDefect
        (fun s ↦ RecReg.swapEquiv (Cell := Cell)
          (RecReg.restrictedExtractor ME ∅ (fun _ ↦ Database.empty))
          (fun q ↦ ME.extract q.1 s))
        (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)) = 0 := by
      ext a b
      simp only [permutationDefect, he a.2.1 b.2.1, sub_self, mul_zero, Matrix.zero_apply]
    rw [hzero, Matrix.zero_mul, norm_zero]
    exact Real.sqrt_nonneg r
  · by_cases ht : keys.card ≤ t
    · apply l2_opNorm_familyDefect_source_le i _ keys.card t (Real.sqrt r) (Real.sqrt_nonneg r)
      intro Dfix
      have h := l2_opNorm_permutationDefect_source_sq_le
        (fun D ↦ fun q : keys ↦ ME.extract q.1 (Function.update Dfix i D)) (t - keys.card)
        (RecReg.swapEquiv (Cell := Cell)
          (RecReg.restrictedExtractor ME keys (fun _ ↦ Database.empty)))
      have hn : 1 ≤ keys.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
      have hb := h.trans (hi keys hn ht Dfix)
      have hcut (D : Database X Y) : D.size + keys.card ≤ t ↔ D.size ≤ t - keys.card := by omega
      simpa only [hcut] using (Real.le_sqrt (norm_nonneg _) hr).mpr hb
    · have hcut (a : (X × Y) × (Fin k → Database X Y) × RecReg k Cm Dm Cell) :
          ¬ (∑ j, (a.2.1 j).size) + keys.card ≤ t := by omega
      simp only [hcut, ite_false, diagonal_zero, Matrix.mul_zero, norm_zero]
      exact Real.sqrt_nonneg r
end

section
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- A unitary change of frame identifies the source Gram matrices of a difference and commutator. -/
theorem source_rotated_difference_gram (U V P : Matrix A A ℂ)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) :
    ((U - Vᴴ * U * V) * P)ᴴ * ((U - Vᴴ * U * V) * P) =
      ((V * U - U * V) * P)ᴴ * ((V * U - U * V) * P) := by
  have he : (U - Vᴴ * U * V) * P = Vᴴ * ((V * U - U * V) * P) := by
    rw [← Matrix.mul_assoc Vᴴ, Matrix.mul_sub, ← Matrix.mul_assoc Vᴴ V, hV,
      Matrix.one_mul]
    simp only [Matrix.sub_mul, Matrix.mul_assoc]
  rw [he, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V Vᴴ, hV', Matrix.one_mul]
end
section
variable {k : ℕ} {Cm Cell S Q : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [DecidableEq Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  [Fintype Cell] [DecidableEq Cell] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]
/-- The entrywise recording defect is the ordinary-port commutator with the private swap. -/
theorem permutationDefect_eq_swap_commutator (ME : MultiExtractor k Cm Dm S)
    (M : Matrix (Q × S) (Q × S) ℂ) :
    permutationDefect (RecReg.swapEquiv (Cell := Cell) ME) M =
      (1 ⊗ₖ RecReg.swapUnitary ME) *
        reindex (Equiv.prodAssoc Q S _) (Equiv.prodAssoc Q S _) (M ⊗ₖ 1) -
      reindex (Equiv.prodAssoc Q S _) (Equiv.prodAssoc Q S _) (M ⊗ₖ 1) *
        (1 ⊗ₖ RecReg.swapUnitary ME) := by
  rw [one_kronecker_swapUnitary]
  ext ⟨q, s, v⟩ ⟨p, r, w⟩
  exact (controlledPermutation_commutator_apply (RecReg.swapEquiv ME) M q p s r v w).symm
end
section
variable {k : ℕ} {Cm Cell S Q : Type} {Dm : Fin k → Type}
  [Fintype Cm] [DecidableEq Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  [Fintype Cell] [DecidableEq Cell] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]
/-- The recording commutator source bound gives the Gram inequality
for the rotated ordinary port. -/
theorem posSemidef_rotated_port_difference_of_source_bound
    (ME : MultiExtractor k Cm Dm S) (M : Matrix (Q × S) (Q × S) ℂ)
    (g : S → ℕ) (bot : Cell) (t : ℕ) (r : ℝ)
    (h : ‖permutationDefect (RecReg.swapEquiv ME) M *
      diagonal (fun a : Q × S × RecReg k Cm Dm Cell ↦
        if g a.2.1 + RecReg.population bot a.2.2 ≤ t then (1 : ℂ) else 0)‖ ^ 2 ≤ r) :
    let V := (1 : Matrix Q Q ℂ) ⊗ₖ RecReg.swapUnitary (Cell := Cell) ME
    let O := reindex (Equiv.prodAssoc Q S _) (Equiv.prodAssoc Q S _) (M ⊗ₖ 1)
    let P := (1 : Matrix Q Q ℂ) ⊗ₖ diagonal
      (fun a : S × RecReg k Cm Dm Cell ↦
        if g a.1 + RecReg.population bot a.2 ≤ t then (1 : ℂ) else 0)
    (r • (1 : Matrix (Q × S × RecReg k Cm Dm Cell) _ ℂ) -
      ((O - Vᴴ * O * V) * P)ᴴ * ((O - Vᴴ * O * V) * P)).PosSemidef := by
  dsimp only
  have hv := kronecker_mem_unitary (one_mem (unitaryGroup Q ℂ))
    (RecReg.swapUnitary_mem_unitaryGroup (Cell := Cell) ME)
  rw [source_rotated_difference_gram _ _ _
    (mem_unitaryGroup_iff'.mp hv) (mem_unitaryGroup_iff.mp hv),
    ← permutationDefect_eq_swap_commutator]
  have hp : (1 : Matrix Q Q ℂ) ⊗ₖ diagonal
      (fun a : S × RecReg k Cm Dm Cell ↦
        if g a.1 + RecReg.population bot a.2 ≤ t then (1 : ℂ) else 0) =
      diagonal (fun a : Q × S × RecReg k Cm Dm Cell ↦
        if g a.2.1 + RecReg.population bot a.2.2 ≤ t then (1 : ℂ) else 0) := by
    rw [← diagonal_one, diagonal_kronecker_diagonal]
    simp only [one_mul]
  rw [hp]
  exact MatrixMap.posSemidef_scalar_sub_gram_of_norm_sq_le _ h
end

namespace Database
variable {X Y : Type} {ι κ : Type*} [DecidableEq X] [AnswerMeasure (X →ₒ Y)]
/-- Coarsening labels cannot increase instability, stated through equality preservation. -/
theorem instability_le_of_eq_imp (π₁ : Database X Y → ι) (π₂ : Database X Y → κ)
    (h : ∀ D D', π₂ D = π₂ D' → π₁ D = π₁ D') (t : ℕ) :
    instability π₁ t ≤ instability π₂ t := by
  rw [instability_eq_iSup_flip_compl, instability_eq_iSup_flip_compl]
  refine iSup_le fun k ↦ QueryCache.flip_le_iff.mpr fun D hD hlt x hx ↦ ?_
  refine le_iSup_of_le (π₂ (equivQueryCache.symm D)) <|
    (QueryCache.updateProb_mono D x fun c hc ↦ ?_).trans
      (QueryCache.updateProb_le_flip rfl hlt hx)
  simp only [Set.mem_compl_iff, mem_labelPartition] at hD hc ⊢
  exact fun he ↦ hc ((h _ _ he).trans hD)
end Database

section recordGrade

variable {k : ℕ} {Cm Yr S Cell : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [DecidableEq Cm] [∀ i, Fintype (Dm i)]
  [DecidableEq S] [DecidableEq Cell]

/-- A recording call preserves the private basis state and increases occupied keys by at most
one, even for a coherent input tuple. -/
theorem recordUnitary_population_le (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (a b : (TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell))
    (h : recordUnitary U a b ≠ 0) :
    a.2.1 = b.2.1 ∧ RecReg.population bot a.2.2 ≤ RecReg.population bot b.2.2 + 1 := by
  have hl := cellControlled_locality RecReg.equiv Prod.fst U a b h
  refine ⟨hl.2.1, RecReg.population_le_of_eq_off_key bot b.2.2 a.2.2 a.1.1
    hl.2.2.1 ?_⟩
  intro p _ t
  exact congrFun hl.2.2.2 ⟨p, t⟩

variable [∀ i, DecidableEq (Dm i)]

/-- Extraction-indexed recording has the same population cost as unsplit recording. -/
theorem recordMEUnitary_population_le (ME : MultiExtractor k Cm Dm S) (bot : Cell)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (a b : (TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell))
    (h : recordMEUnitary ME U a b ≠ 0) :
    a.2.1 = b.2.1 ∧ RecReg.population bot a.2.2 ≤ RecReg.population bot b.2.2 + 1 := by
  have hl := cellControlled_locality (RecReg.equiv.trans (Equiv.prodComm _ _))
    (fun p ↦ (⟨p.1, ME.extract p.1 p.2⟩ : TpICD k Cm Dm)) U a b h
  refine ⟨hl.2.1, RecReg.population_le_of_eq_off_key bot b.2.2 a.2.2 a.1.1
    (fun p _ ↦ congrFun hl.2.2.2 p) ?_⟩
  intro p hp t
  exact hl.2.2.1 ⟨p, t⟩ fun he ↦ hp (congrArg Sigma.fst he)

end recordGrade

namespace VCOracle

variable {k : ℕ} {X Y Cm Z Yr Cell : Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  {Dm : Fin k → Type} [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
  (bot : Cell) (g : E.S → ℕ)

/-- An ordinary or extraction call with a passive record increases the joint grade by at most
one if the ordinary ports increase the private grade by at most one. -/
theorem withRecReg_U_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (p : Fin k ⊕ Unit) (a b : extIn k X Y Cm Z p)
    (s r : E.S × RecReg k Cm Dm Cell)
    (h : (E.withRecReg ME code bot).U p (a, s) (b, r) ≠ 0) :
    g s.1 + RecReg.population bot s.2 ≤ g r.1 + RecReg.population bot r.2 + 1 := by
  change ((E.withExtract ME code).U p (a, s.1) (b, r.1) *
    (1 : Matrix (RecReg k Cm Dm Cell) _ ℂ) s.2 r.2) ≠ 0 at h
  have hr : s.2 = r.2 := by
    by_contra hn
    exact h (by simp [hn])
  have hu := left_ne_zero_of_mul h
  have hg : g s.1 ≤ g r.1 + 1 := by
    rcases p with i | u
    · exact hE i a b s.1 r.1 hu
    · obtain ⟨ta, za⟩ := a
      obtain ⟨tb, zb⟩ := b
      change extractUnitary ME code ((ta, za), s.1) ((tb, zb), r.1) ≠ 0 at hu
      rw [extractUnitary_apply] at hu
      split_ifs at hu with he
      · exact he.2.2 ▸ Nat.le_succ _
      · exact (hu rfl).elim
  rw [hr]
  omega

/-- Every port of the unsplit recording world raises the joint private/record grade by at most
one. This is a matrix-entry statement and preserves coherent port choice. -/
theorem withRecord_U_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    (p : (Fin k ⊕ Unit) ⊕ Unit) (a b : recIn k X Y Cm Z Yr p)
    (s r : E.S × RecReg k Cm Dm Cell)
    (h : (E.withRecord ME code bot U hU).U p (a, s) (b, r) ≠ 0) :
    g s.1 + RecReg.population bot s.2 ≤ g r.1 + RecReg.population bot r.2 + 1 := by
  rcases p with p | u
  · exact withRecReg_U_grade E ME code bot g hE p a b s r h
  · obtain ⟨he, hp⟩ := recordUnitary_population_le bot U (a, s) (b, r) h
    dsimp at he hp
    rw [he]
    omega

/-- Every port of the extraction-indexed recording world has the same joint grade bound. -/
theorem withRecordME_U_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    (p : (Fin k ⊕ Unit) ⊕ Unit) (a b : recIn k X Y Cm Z Yr p)
    (s r : E.S × RecReg k Cm Dm Cell)
    (h : (E.withRecordME ME code bot U hU).U p (a, s) (b, r) ≠ 0) :
    g s.1 + RecReg.population bot s.2 ≤ g r.1 + RecReg.population bot r.2 + 1 := by
  rcases p with p | u
  · exact withRecReg_U_grade E ME code bot g hE p a b s r h
  · obtain ⟨he, hp⟩ := recordMEUnitary_population_le ME bot U (a, s) (b, r) h
    dsimp at he hp
    rw [he]
    omega

end VCOracle

section runGrade

universe uL vL w

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (F : EmulatedOracle P In) (g : F.S → ℕ)

/-- Matrix-entry grade bounds propagate through arbitrary adaptive programs, with coherent
port choice, local instruments, and changing entangled workspaces. The input operator need
only satisfy the support hypothesis; positivity and normalization are unnecessary. -/
theorem EmulatedOracle.querySupportedOn_run_of_grade
    (hF : ∀ i a b s r, F.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (EmulatedOracle.cohSpec In) W A) {t n : ℕ}
    (hx : x.IsQueryBound fun _ ↦ n) (ρ : Matrix (A × F.S) (A × F.S) ℂ)
    (hρ : QuerySupportedOn (fun m : A × F.S ↦ g m.2) (Set.Iic t) ρ)
    (p : Σ B, W B) :
    QuerySupportedOn (fun m : p.1 × F.S ↦ g m.2) (Set.Iic (t + n))
      ((F.coherent.toRuntime.run I x).branch p ρ) := by
  have hstep := F.coherent.querySupportedOn_toRuntime_step g
    (fun i a b s r h ↦ F.coherent_U_grade g
      (fun i a b s r h ↦ hF i b a r s h) i a b s r h)
  simpa using QuerySupportedOn.run_of_step F.coherent.toRuntime g hstep I hx hρ p

end runGrade

section compressedGrade

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- One ordinary port increases the sum of all database sizes by at most one. -/
theorem compressedVCOracle_U_totalSize_le (i : Fin k) (a b : X × Y)
    (s r : Fin k → Database X Y)
    (h : (compressedVCOracle k X Y).U i (a, s) (b, r) ≠ 0) :
    ∑ j, (s j).size ≤ (∑ j, (r j).size) + 1 := by
  change onFactor (splitAt (X × Y) (Database X Y) i)
    (compressedOracle X Y) (a, s) (b, r) ≠ 0 at h
  rw [onFactor_apply] at h
  split_ifs at h with he
  · change (fun j : {j // j ≠ i} ↦ s j.1) = (fun j ↦ r j.1) at he
    have hi := size_le_of_compressedOracle_apply_ne_zero h
    have hj (j : Fin k) : (s j).size ≤ (r j).size + if j = i then 1 else 0 := by
      by_cases hji : j = i
      · simpa [hji] using hi
      · simp [hji, congrFun he ⟨j, hji⟩]
    simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  · exact (h rfl).elim

end compressedGrade

namespace VCOracle

universe uL vL w

variable {k : ℕ} {X Y Cm Z Yr Cell : Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  {Dm : Fin k → Type} [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
  (bot : Cell) (g : E.S → ℕ)

/-- The initial workspace and empty recording register have joint grade zero. -/
theorem recording_initial_grade
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    {A : QReg} (ρ : SubState A) :
    QuerySupportedOn (fun m : A × (E.S × RecReg k Cm Dm Cell) ↦
      g m.2.1 + RecReg.population bot m.2.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ (E.init.matrix ⊗ₖ
        (SubState.basis (RecReg.const bot : RecReg k Cm Dm Cell)).matrix)) := by
  intro a b hab
  simp only [kroneckerMap_apply] at hab
  have hd := left_ne_zero_of_mul (right_ne_zero_of_mul hab)
  have hr := right_ne_zero_of_mul (right_ne_zero_of_mul hab)
  rw [SubState.matrix_basis, Matrix.single_apply] at hr
  split_ifs at hr with he
  · obtain ⟨ha, hb⟩ := hinit _ _ hd
    change g a.2.1 + RecReg.population bot a.2.2 ≤ 0 ∧
      g b.2.1 + RecReg.population bot b.2.2 ≤ 0
    rw [← he.1, ← he.2, RecReg.population_const]
    exact ⟨by simpa using ha, by simpa using hb⟩
  · exact (hr rfl).elim

/-- The initialized unsplit recording experiment has joint grade at most its total query
budget on every output branch, for arbitrary local operations and subnormalized inputs. -/
theorem withRecord_jointPost_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (EmulatedOracle.cohSpec (recIn k X Y Cm Z Yr)) W A)
    {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) (p : Σ B, W B) :
    QuerySupportedOn (fun m : p.1 × (E.S × RecReg k Cm Dm Cell) ↦
      g m.2.1 + RecReg.population bot m.2.2) (Set.Iic t)
      (((E.withRecord ME code bot U hU).coherent.toRuntime.jointPost I x ρ p).matrix) := by
  have h := (E.withRecord ME code bot U hU).querySupportedOn_run_of_grade
    (fun s ↦ g s.1 + RecReg.population bot s.2)
    (withRecord_U_grade E ME code bot g hE U hU) I x hx _
    (recording_initial_grade E bot g hinit ρ (Dm := Dm)) p
  have hi : (E.withRecord ME code bot U hU).coherent.toRuntime.init.matrix =
      E.init.matrix ⊗ₖ (SubState.basis (RecReg.const bot)).matrix :=
    SubState.matrix_prod _ _
  rw [QuantumRuntime.matrix_jointPost, hi]
  simpa only [Nat.zero_add, withRecord, withRecordME, withRecReg, withExtract,
    EmulatedOracle.extend, EmulatedOracle.addRegister] using h

/-- The extraction-indexed recording experiment obeys the same joint grade, with the same
query budget and no restriction on adaptive stopping or coherent port selection. -/
theorem withRecordME_jointPost_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (EmulatedOracle.cohSpec (recIn k X Y Cm Z Yr)) W A)
    {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) (p : Σ B, W B) :
    QuerySupportedOn (fun m : p.1 × (E.S × RecReg k Cm Dm Cell) ↦
      g m.2.1 + RecReg.population bot m.2.2) (Set.Iic t)
      (((E.withRecordME ME code bot U hU).coherent.toRuntime.jointPost I x ρ p).matrix) := by
  have h := (E.withRecordME ME code bot U hU).querySupportedOn_run_of_grade
    (fun s ↦ g s.1 + RecReg.population bot s.2)
    (withRecordME_U_grade E ME code bot g hE U hU) I x hx _
    (recording_initial_grade E bot g hinit ρ (Dm := Dm)) p
  have hi : (E.withRecordME ME code bot U hU).coherent.toRuntime.init.matrix =
      E.init.matrix ⊗ₖ (SubState.basis (RecReg.const bot)).matrix :=
    SubState.matrix_prod _ _
  rw [QuantumRuntime.matrix_jointPost, hi]
  simpa only [Nat.zero_add, withRecord, withRecordME, withRecReg, withExtract,
    EmulatedOracle.extend, EmulatedOracle.addRegister] using h

end VCOracle

/-! ## Grade-sensitive weights on actual prefixes -/

namespace QuerySupportedOn

/-- Tracing out the unused workspace preserves a grade read from the private register. -/
theorem callInput {A J E D Z : Type*} [Fintype A] [Fintype J] [Fintype E] [Fintype D]
    [DecidableEq A] [DecidableEq J] [DecidableEq E] [DecidableEq D]
    {g : D → Z} {T : Set Z} {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × D ↦ g m.2) T ρ) (ℓ : A ≃ J × E) :
    QuerySupportedOn (fun m : J × D ↦ g m.2) T (QuantumRuntime.callInput ℓ D ρ) := by
  intro a b hab
  simp only [QuantumRuntime.callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
    SubInstrument.relabel_branch_apply, submatrix_apply] at hab
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact hρ _ _ he

end QuerySupportedOn

namespace QuantumRuntime

universe uL vL uP vP w

variable {spec : QuantumOracleSpec.{uP, vP}} {L : LocalSig.{uL, vL}}
  (R : QuantumRuntime spec) (I : L.Interp) (g : R.D → ℕ)

/-- A local comparison needed only on grade `t+j` bounds the weight of the actual `j`-th
query from an input of grade `t`. All intervening local instruments and query outcomes are
included. The hypothesis is on one-step operators, not on complete executions. -/
theorem queryWeight_mono_of_grade
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    {w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    {W : QReg → Type w} {A : QReg} (x : QuantumComp L spec W A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (t j : ℕ)
    (hgrade : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ)
    (hw : ∀ i σ, σ.PosSemidef →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic (t + j)) σ →
        w i σ ≤ w' i σ) :
    R.queryWeight I w x ρ j ≤ R.queryWeight I w' x ρ j := by
  induction x using QuantumComp.inductionOn generalizing t j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact ENNReal.tsum_le_tsum fun b ↦
      ih b (((I o).frame R.D).posSemidef_branch_apply b hρ) t j
        (hgrade.amplify_snd _) hw
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero =>
      exact hw i _ (posSemidef_callInput ℓ hρ) (by simpa using hgrade.callInput ℓ)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      refine ENNReal.tsum_le_tsum fun r ↦
        ih r ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) (t + 1) j
          (QuerySupportedOn.queryStep_of_step R g hR i E ℓ r hgrade) ?_
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hw

/-- A summed branch Gram inequality bounds the entire instrument discrepancy on a
supported input. The outcomes are summed before taking a bound. -/
theorem krausWeight_le_of_sum_gram [∀ i, Fintype (spec.Result i)]
    (C : ∀ i, spec.Result i → Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ)
    (i : spec.Port) (P Δ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (hC : (r • Δ - ∑ a, (C i a * P)ᴴ * (C i a * P)).PosSemidef)
    {σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ} (hσ : σ.PosSemidef)
    (hsupp : MatrixMap.conj P σ = σ) :
    krausWeight C i σ ≤ ENNReal.ofReal r * ENNReal.ofReal (Δ * σ).trace.re := by
  have ht := hC.trace_mul_re_nonneg hσ
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul,
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum] at ht
  have he (a : spec.Result i) :
      (((C i a * P)ᴴ * (C i a * P)) * σ).trace =
        (MatrixMap.conj (C i a) σ).trace := by
    rw [← MatrixMap.trace_conj_apply, MatrixMap.conj_mul, LinearMap.comp_apply, hsupp]
  simp only [he] at ht
  have hn (a : spec.Result i) : 0 ≤ (MatrixMap.conj (C i a) σ).trace.re :=
    (hσ.mul_mul_conjTranspose_same (C i a)).trace_re_nonneg
  rw [krausWeight, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun a _ ↦ hn a), ← ENNReal.ofReal_mul hr]
  exact ENNReal.ofReal_le_ofReal (sub_nonneg.mp ht)

/-- Graded branch discrepancies accumulate against the selected weight of the source run.
Total calls bound the support in time even when different calls have different outcome types. -/
theorem tsum_rpow_queryWeight_le_of_total_grade
    (hR : ∀ i a t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch a σ))
    (d w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    {W : QReg → Type w} {A : QReg} {x : QuantumComp L spec W A}
    {t : ℕ} (hx : x.IsTotalQueryBound t)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hgrade : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic 0) ρ)
    (rate : ℕ → ℝ≥0∞)
    (hd : ∀ j < t, ∀ i σ, σ.PosSemidef →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic j) σ →
        d i σ ≤ rate j * w i σ) :
    ∑' j, R.queryWeight I d x ρ j ^ (2⁻¹ : ℝ) ≤
      ((∑ j ∈ Finset.range t, rate j) * R.totalWeight I w x ρ) ^ (2⁻¹ : ℝ) := by
  have hz : ∀ j ∉ Finset.range t, R.queryWeight I d x ρ j ^ (2⁻¹ : ℝ) = 0 := by
    intro j hj
    rw [R.queryWeight_eq_zero_of_isTotalQueryBound I hx (by simpa using hj) ρ,
      ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz]
  calc
    _ ≤ ∑ j ∈ Finset.range t,
        rate j ^ (2⁻¹ : ℝ) * R.queryWeight I w x ρ j ^ (2⁻¹ : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      rw [← R.queryWeight_const_mul]
      exact R.queryWeight_mono_of_grade I g hR x hρ 0 j hgrade
        (by simpa using hd j (Finset.mem_range.mp hj))
    _ ≤ _ := by
      refine (ENNReal.inner_le_Lp_mul_Lq _ _ _ Real.HolderConjugate.two_two).trans ?_
      simp only [rpow_inv_two_rpow_two, one_div]
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      gcongr
      exact ENNReal.sum_le_tsum _

end QuantumRuntime

namespace EmulatedOracle

section chargedComparison

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (E : EmulatedOracle P In)

/-- Portwise squared operator bounds lift to coherent selected mass on a supported input.
The private projector may depend on the query position; no measurement of its grade or of
its coherent port index is performed. -/
theorem ofReal_trace_coherentBlocks_conj_le_selectedMass
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (P₀ : Matrix E.S E.S ℂ) (selected : P → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ p,
      ((if selected p then r else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ P₀))ᴴ * (C p * (1 ⊗ₖ P₀))).PosSemidef)
    {σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ} (hσ : σ.PosSemidef)
    (hsupp : MatrixMap.conj ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀) σ = σ) :
    ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re ≤
      ENNReal.ofReal r * E.selectedMass selected σ := by
  let B := fun p ↦ C p * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ P₀)
  have hb := posSemidef_coherentBlocks hC
  change (coherentBlocks ((fun p ↦ (if selected p then r else 0) • 1) -
    (fun p ↦ (B p)ᴴ) * B)).PosSemidef at hb
  rw [coherentBlocks_sub, coherentBlocks_mul, coherentBlocks_adjoint] at hb
  have he : coherentBlocks B = coherentBlocks C *
      ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀) := by
    change coherentBlocks (C * (fun p ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ P₀)) = _
    rw [coherentBlocks_mul, coherentBlocks_database]
  rw [he] at hb
  have ht := ofReal_trace_conj_le
    (coherentBlocks C * ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀))
    (selectedCharge selected r) (r := 1) (by norm_num)
    (by simpa only [one_smul, selectedCharge] using hb) hσ
  rw [MatrixMap.conj_mul, LinearMap.comp_apply, hsupp] at ht
  simpa only [ENNReal.ofReal_one, one_mul, E.ofReal_trace_selectedCharge selected hr hσ]
    using ht

/-- A grade-restricted squared port bound controls the discrepancy weight at an actual query
prefix by its selected coherent input mass. The bound is tested at grade `t+j`, so it can
vary with time without changing the execution or measuring the recording register. -/
theorem queryWeight_conj_le_selectedMass_of_grade
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec In) W A) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef) (t j : ℕ)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic t) ρ)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (selected : P → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ p,
      ((if selected p then r else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ t + j then (1 : ℂ) else 0))ᴴ *
          (C p * (1 ⊗ₖ diagonal fun d ↦
          if g d ≤ t + j then (1 : ℂ) else 0))).PosSemidef) :
    E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ≤
      ENNReal.ofReal r * E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ E.selectedMass selected σ) x ρ j := by
  rw [← QuantumRuntime.queryWeight_const_mul]
  refine E.coherent.toRuntime.queryWeight_mono_of_grade I g
    (E.coherent.querySupportedOn_toRuntime_step g (E.coherent_U_grade g hE))
    x hρ t j hgrade fun _ σ hσ hsupp ↦ ?_
  refine E.ofReal_trace_coherentBlocks_conj_le_selectedMass C _ selected hr hC hσ ?_
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  exact hsupp.conj_diagonal_eq_self fun m hm ↦ by simp [Set.mem_Iic.mp hm]

/-- A time-dependent family of grade-restricted port bounds accumulates against the actual
selected query mass. This is the Cauchy–Schwarz step of the online hybrid, before identifying
the discrepancy operators with a recording-swap comparison. -/
theorem tsum_rpow_queryWeight_conj_le_of_grade
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic 0) ρ)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (selected : P → Bool) (r : ℕ → ℝ) (hr : ∀ j < t, 0 ≤ r j)
    (hC : ∀ j < t, ∀ p,
      ((if selected p then r j else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))ᴴ *
          (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))).PosSemidef) :
    ∑' j, E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ^
          (2⁻¹ : ℝ) ≤
      ((∑ j ∈ Finset.range t, ENNReal.ofReal (r j)) *
        E.selectedTotalMass I selected x ρ) ^ (2⁻¹ : ℝ) := by
  have hb := E.coherent.toRuntime.tsum_rpow_queryWeight_le_of_total_grade I g
    (E.coherent.querySupportedOn_toRuntime_step g (E.coherent_U_grade g hE))
    (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re)
    (fun _ σ ↦ E.selectedMass selected σ)
    ((QuantumComp.isTotalQueryBound_iff_isQueryBound x t).mpr hx) hρ hgrade
    (fun j ↦ ENNReal.ofReal (r j)) ?_
  · simpa only [QuantumRuntime.totalWeight, E.tsum_queryWeight_selectedMass] using hb
  · intro j hj _ σ hσ hsupp
    refine E.ofReal_trace_coherentBlocks_conj_le_selectedMass C _ selected
      (hr j hj) (hC j hj) hσ ?_
    rw [← diagonal_one, diagonal_kronecker_diagonal]
    exact hsupp.conj_diagonal_eq_self fun m hm ↦ by simp [Set.mem_Iic.mp hm]

/-- Both square-root event comparisons follow from graded portwise squared difference
bounds. The two directions use the selected mass of the first, actual execution. The second
runtime has the same initialization and coherent block steps given by `V`; arbitrary local
instruments, observations, and subnormalized workspace inputs are allowed. -/
theorem outcomeLawWith_rpow_bounds_of_graded_ports
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    (V : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (s₁ : Unit → SubInstrument (cohIn In × E.S) (cohIn In × E.S) Unit)
    (hV : ∀ i a, (s₁ i).branch a = MatrixMap.conj (coherentBlocks V))
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t)
    (ρ : SubState A)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ E.init.matrix))
    (selected : P → Bool) (r : ℕ → ℝ) (hr : ∀ j < t, 0 ≤ r j)
    (hC : ∀ j < t, ∀ p,
      ((if selected p then r j else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        ((E.U p - V p) * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))ᴴ *
          ((E.U p - V p) *
            (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))).PosSemidef)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    let p₀ := E.coherent.toRuntime.evalDistMap I x ρ f s
    let p₁ := (QuantumRuntime.mk E.S E.init s₁).evalDistMap I x ρ f s
    let err := ((∑ j ∈ Finset.range t, ENNReal.ofReal (r j)) *
      E.selectedTotalMass I selected x (ρ.matrix ⊗ₖ E.init.matrix)) ^ (2⁻¹ : ℝ)
    p₀ ^ (2⁻¹ : ℝ) ≤ p₁ ^ (2⁻¹ : ℝ) + err ∧
      p₁ ^ (2⁻¹ : ℝ) ≤ p₀ ^ (2⁻¹ : ℝ) + err := by
  have hb := E.tsum_rpow_queryWeight_conj_le_of_grade g hE I hx
    (ρ.prod E.init).posSemidef hgrade (E.U - V) selected r hr hC
  rw [SubState.matrix_prod] at hb
  have hw : (QuantumRuntime.krausWeight (spec := cohSpec In) (D := E.S)
      (fun (i a : Unit) ↦ E.coherent.U i - coherentBlocks V)) =
      (fun (_ : Unit) σ ↦
        ENNReal.ofReal (MatrixMap.conj (coherentBlocks (E.U - V)) σ).trace.re) := by
    funext i σ
    cases i
    simp only [QuantumRuntime.krausWeight, tsum_fintype, Fintype.sum_unique,
      coherentBlocks_sub]
    rfl
  have h₀ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le I E.init
    E.coherent.toRuntime_step_branch hV x ρ f hs
  have h₁ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le' I E.init
    E.coherent.toRuntime_step_branch hV x ρ f hs
  rw [hw] at h₀ h₁
  exact ⟨h₀.trans (add_le_add le_rfl hb), h₁.trans (add_le_add le_rfl hb)⟩

end chargedComparison
end EmulatedOracle
end Quantum
