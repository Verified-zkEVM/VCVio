/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Action
public import VCVio.Quantum.Oracle.Compressed.Equivalence

/-!
# The database grows by at most one cell per call

A call to the compressed oracle changes only the queried cell of the database
(`Quantum.eq_update_of_compressedOracle_apply_ne_zero`), so it increases the number of nonempty
cells by at most one, and the local operations of a program do not touch the database register.
For a program that makes at most `q` calls on every path, run against the compressed runtime from
the empty database, the joint state at every leaf is therefore supported on databases with at
most `q` nonempty cells (Zhandry, Crypto 2019; Chiesa, Di, Hu and Zheng, ePrint 2025/2166,
§4.3).

The statements hold for general programs (`Quantum.QuantumComp`): adaptive, with their own local
operations and registers, and with a final register that may depend on the outcome. The bound is
stated for the operators themselves, not only for positive ones, so it applies on every branch of
the run.

Support is expressed with `Quantum.QuerySupportedOn`, read through the size of the database
component of a basis element.

## Main definitions

* `Quantum.DatabaseSupportedOn t ρ`: the condition `P_t` of ePrint 2025/2166 on an operator on
  `M × Database X Y`, support on databases with at most `t` nonempty cells.

## Main results

* `Quantum.DatabaseSupportedOn.queryStep_compressedRuntime`: one call takes `P_t` to `P_(t + 1)`.
* `Quantum.DatabaseSupportedOn.run_compressedRuntime`: a program with at most `q` calls on every
  path takes `P_t` to `P_(t + q)`.
* `Quantum.forallQueries_compressedRuntime`: every call of such a program receives an operator
  supported on databases with at most `n` nonempty cells, for `t + q ≤ n + 1`.
* `Quantum.databaseSupportedOn_jointPost_compressedRuntime`: from the empty database, the joint
  state at every leaf satisfies `P_q`.
-/

public section

open Matrix
open scoped Kronecker

universe u v w

namespace Quantum

/-! ## Support through a read map -/

namespace QuerySupportedOn

variable {M M' A B R Z Z' : Type*}

/-- Support passes along any change of read map and set that keeps the basis elements in the
support. -/
theorem imp {q : M → Z} {q' : M → Z'} {S : Set Z} {S' : Set Z'} {ρ : Matrix M M ℂ}
    (h : QuerySupportedOn q S ρ) (hq : ∀ m, q m ∈ S → q' m ∈ S') : QuerySupportedOn q' S' ρ :=
  fun m m' hm ↦ ⟨hq m (h m m' hm).1, hq m' (h m m' hm).2⟩

/-- Support is closed under sums of families. -/
theorem tsum {ι : Type*} {q : M → Z} {S : Set Z} {f : ι → Matrix M M ℂ}
    (hf : ∀ i, QuerySupportedOn q S (f i)) : QuerySupportedOn q S (∑' i, f i) := by
  intro m m' hm
  by_cases hs : Summable f
  · rw [Matrix.tsum_apply_apply hs] at hm
    obtain ⟨i, hi⟩ := not_forall.mp fun hc : ∀ i, f i m m' = 0 ↦ hm (by simp [hc])
    exact hf i m m' hi
  · rw [tsum_eq_zero_of_not_summable hs] at hm
    exact absurd rfl hm

/-- Conjugation by `K` moves the support from `S` to `S'` when every nonzero entry `K m' m` with
`q m ∈ S` has `q' m' ∈ S'`. -/
theorem conj [Fintype M] {q : M → Z} {q' : M' → Z'} {S : Set Z} {S' : Set Z'}
    {ρ : Matrix M M ℂ} (h : QuerySupportedOn q S ρ) {K : Matrix M' M ℂ}
    (hK : ∀ m' m, K m' m ≠ 0 → q m ∈ S → q' m' ∈ S') :
    QuerySupportedOn q' S' (MatrixMap.conj K ρ) := by
  intro n n' hn
  rw [MatrixMap.conj_apply, Matrix.mul_apply] at hn
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hb₁ := left_ne_zero_of_mul hb
  have hb₂ := right_ne_zero_of_mul hb
  rw [Matrix.mul_apply] at hb₁
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb₁
  have hρ := h a b (right_ne_zero_of_mul ha)
  rw [Matrix.conjTranspose_apply, star_ne_zero] at hb₂
  exact ⟨hK n a (left_ne_zero_of_mul ha) hρ.1, hK n' b hb₂ hρ.2⟩

/-- A relabelling gate moves the read map along the bijection. -/
theorem branch_relabel [Fintype M] [Fintype M'] [DecidableEq M] [DecidableEq M'] {q : M → Z}
    {S : Set Z} {ρ : Matrix M M ℂ} (h : QuerySupportedOn q S ρ) (e : M ≃ M') :
    QuerySupportedOn (q ∘ e.symm) S ((SubInstrument.relabel e).branch () ρ) := by
  intro m m' hm
  rw [SubInstrument.relabel_branch_apply, submatrix_apply] at hm
  exact h _ _ hm

/-- A map acting on the first factor preserves support read through the second factor. -/
theorem amplify_snd {q : R → Z} {S : Set Z} {ρ : Matrix (A × R) (A × R) ℂ}
    (h : QuerySupportedOn (fun m : A × R ↦ q m.2) S ρ) (Φ : MatrixMap A B) :
    QuerySupportedOn (fun m : B × R ↦ q m.2) S (Φ.amplify R ρ) := by
  intro m m' hm
  have hblock : ρ.submatrix (·, m.2) (·, m'.2) ≠ 0 := by
    intro h0
    rw [MatrixMap.amplify_apply, h0, map_zero] at hm
    exact hm rfl
  obtain ⟨a, b, hab⟩ : ∃ a b, ρ (a, m.2) (b, m'.2) ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hblock (Matrix.ext hc)
  exact h _ _ hab

/-- A map acting on the first factor that moves support read through `q` on `S` to support read
through `q'` on `S'` does so on the first factor of the framed register. -/
theorem amplify_fst {q : A → Z} {q' : B → Z'} {S : Set Z} {S' : Set Z'} {Φ : MatrixMap A B}
    (hΦ : ∀ σ, QuerySupportedOn q S σ → QuerySupportedOn q' S' (Φ σ))
    {ρ : Matrix (A × R) (A × R) ℂ} (h : QuerySupportedOn (fun m : A × R ↦ q m.1) S ρ) :
    QuerySupportedOn (fun m : B × R ↦ q' m.1) S' (Φ.amplify R ρ) := by
  rintro ⟨b, r⟩ ⟨b', r'⟩ hm
  rw [MatrixMap.amplify_apply] at hm
  exact hΦ _ (h.block r r') b b' hm

end QuerySupportedOn

/-! ## Support on small databases -/

section database

variable {X Y M : Type*} [Fintype X]

/-- The condition `P_t` of ePrint 2025/2166 for operators on `M × Database X Y`: every nonzero
entry sits between databases with at most `t` nonempty cells. -/
abbrev DatabaseSupportedOn (t : ℕ) (ρ : Matrix (M × Database X Y) (M × Database X Y) ℂ) : Prop :=
  QuerySupportedOn (fun m : M × Database X Y ↦ m.2.size) (Set.Iic t) ρ

theorem DatabaseSupportedOn.mono {t s : ℕ} {ρ : Matrix (M × Database X Y) (M × Database X Y) ℂ}
    (h : DatabaseSupportedOn t ρ) (hts : t ≤ s) : DatabaseSupportedOn s ρ :=
  QuerySupportedOn.mono h (Set.Iic_subset_Iic.mpr hts)

/-- A map acting on `M` alone preserves `P_t`. -/
theorem DatabaseSupportedOn.amplify {B : Type*} {t : ℕ}
    {ρ : Matrix (M × Database X Y) (M × Database X Y) ℂ} (h : DatabaseSupportedOn t ρ)
    (Φ : MatrixMap M B) : DatabaseSupportedOn t (Φ.amplify (Database X Y) ρ) :=
  QuerySupportedOn.amplify_snd (q := Database.size) h Φ

/-- An operator on `M` tensored with the empty database satisfies `P_0`. -/
theorem databaseSupportedOn_kronecker_single_empty [DecidableEq Y] (ρ : Matrix M M ℂ) :
    DatabaseSupportedOn 0
      (ρ ⊗ₖ Matrix.single (Database.empty : Database X Y) Database.empty (1 : ℂ)) := by
  intro p p' hp
  rw [kroneckerMap_apply] at hp
  have h := right_ne_zero_of_mul hp
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · exact ⟨show p.2.size ≤ 0 by rw [← he.1, Database.size_empty],
      show p'.2.size ≤ 0 by rw [← he.2, Database.size_empty]⟩
  · exact absurd rfl h

end database

/-! ## Calls to the compressed oracle -/

section compressed

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A nonzero entry of the compressed oracle relates two databases that differ at most in the
queried cell. -/
theorem eq_update_of_compressedOracle_apply_ne_zero {m m' : X × Y} {D D' : Database X Y}
    (h : compressedOracle X Y (m, D) (m', D') ≠ 0) : D = Function.update D' m'.1 (D m'.1) := by
  rw [compressedOracle_eq_controlled, controlled_mul_standardOracle_mul_controlled_apply] at h
  obtain ⟨D₁, -, hD₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hD₁ with hm
  · rw [compressAt_apply, compressAt_apply] at hD₁
    split_ifs at hD₁ with h₁ h₂
    · exact Function.eq_update_iff.mpr ⟨rfl, fun j hj ↦ (h₁ j hj).trans (h₂ j hj)⟩
    all_goals simp at hD₁
  · exact absurd rfl hD₁

/-- A nonzero entry of the compressed oracle increases the size of the database by at most
one. -/
theorem size_le_of_compressedOracle_apply_ne_zero {p p' : (X × Y) × Database X Y}
    (h : compressedOracle X Y p p' ≠ 0) : p.2.size ≤ p'.2.size + 1 :=
  (congrArg Database.size (eq_update_of_compressedOracle_apply_ne_zero h)).trans_le
    (Database.size_update_le _ _ _)

/-- A call to the compressed oracle takes `P_t` to `P_(t + 1)`. -/
theorem DatabaseSupportedOn.conj_compressedOracle {t : ℕ}
    {ρ : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ}
    (h : DatabaseSupportedOn t ρ) :
    DatabaseSupportedOn (t + 1) (MatrixMap.conj (compressedOracle X Y) ρ) :=
  QuerySupportedOn.conj h fun _ _ hK hp ↦
    (size_le_of_compressedOracle_apply_ne_zero hK).trans (Nat.add_le_add_right hp 1)

/-- A call to the compressed oracle, with a remainder `E` carried along, takes support on
databases with at most `t` nonempty cells to support on databases with at most `t + 1`. -/
theorem QuerySupportedOn.amplify_conj_compressedOracle {E : Type*} {t : ℕ}
    {σ : Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ}
    (h : QuerySupportedOn (fun m : ((X × Y) × Database X Y) × E ↦ m.1.2.size) (Set.Iic t) σ) :
    QuerySupportedOn (fun m : ((X × Y) × Database X Y) × E ↦ m.1.2.size) (Set.Iic (t + 1))
      ((MatrixMap.conj (compressedOracle X Y)).amplify E σ) :=
  QuerySupportedOn.amplify_fst (q := fun m : (X × Y) × Database X Y ↦ m.2.size)
    (fun _ hσ ↦ DatabaseSupportedOn.conj_compressedOracle hσ) h

end compressed

/-! ## The size invariant for the compressed runtime -/

section compressedRuntime

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- **One call.** A call of the compressed runtime, with any remainder `E` of the program
register carried along, takes `P_t` to `P_(t + 1)`. -/
theorem DatabaseSupportedOn.queryStep_compressedRuntime {A : QReg} {t : ℕ} (E : QReg)
    (ℓ : A ≃ (qromSpec X Y).In () × E) (r : (qromSpec X Y).Result ())
    {ρ : Matrix (A × Database X Y) (A × Database X Y) ℂ} (h : DatabaseSupportedOn t ρ) :
    DatabaseSupportedOn (t + 1) (((compressedRuntime X Y).queryStep () E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ (Database X Y))).imp
    (q' := fun m : ((X × Y) × Database X Y) × E ↦ m.1.2.size) (S' := Set.Iic t) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (Database X Y)).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  refine (h₁.amplify_conj_compressedOracle.branch_relabel
    (QuantumRuntime.queryEquivOut _ (Database X Y) E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ (Database X Y) E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The size invariant.** A program that makes at most `q` calls on every path, run against the
compressed runtime, takes an operator satisfying `P_t` to operators satisfying `P_(t + q)` on
every branch. -/
theorem DatabaseSupportedOn.run_compressedRuntime (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) {t : ℕ}
    {ρ : Matrix (A × Database X Y) (A × Database X Y) ℂ} (hρ : DatabaseSupportedOn t ρ)
    (p : Σ u, W u) :
    DatabaseSupportedOn (t + q) (((compressedRuntime X Y).run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn generalizing q t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono (Nat.le_add_right t q)
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun b ↦ ih b (fun i ↦ hx i b) (hρ.amplify _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i E ℓ k _).mp hx
    have hb : Function.update (fun _ : Unit ↦ q) i (q - 1) = fun _ ↦ q - 1 :=
      funext fun j ↦ by cases i; cases j; exact Function.update_self ..
    rw [hb] at hk
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    cases i
    have h := ih r (hk r) (hρ.queryStep_compressedRuntime E ℓ r)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' hq] at h

/-- **The size invariant at the calls.** Every call of a program that makes at most `q` calls on
every path, run against the compressed runtime from an operator satisfying `P_t`, receives an
operator supported on databases with at most `n` nonempty cells, for any `n` with
`t + q ≤ n + 1`. -/
theorem forallQueries_compressedRuntime (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) {t n : ℕ} (htn : t + q ≤ n + 1)
    {ρ : Matrix (A × Database X Y) (A × Database X Y) ℂ} (hρ : DatabaseSupportedOn t ρ) :
    (compressedRuntime X Y).ForallQueries I
      (fun _ E σ ↦ QuerySupportedOn (fun m : ((X × Y) × Database X Y) × E ↦ m.1.2.size)
        (Set.Iic n) σ) x ρ := by
  induction x using QuantumComp.inductionOn generalizing q t with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (fun i ↦ hx i b) htn (hρ.amplify _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i E ℓ k _).mp hx
    have hb : Function.update (fun _ : Unit ↦ q) i (q - 1) = fun _ ↦ q - 1 :=
      funext fun j ↦ by cases i; cases j; exact Function.update_self ..
    rw [hb] at hk
    cases i
    refine ⟨(hρ.branch_relabel _).imp fun m hm ↦ ?_, fun r ↦
      ih r (hk r) (by omega) (hρ.queryStep_compressedRuntime E ℓ r)⟩
    obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (Database X Y)).surjective m
    rw [Function.comp_apply, Equiv.symm_apply_apply] at hm
    exact le_trans (show y.2.size ≤ t from hm) (by omega)

/-- **The size invariant from the empty database.** After a program that makes at most `q` calls
on every path, run against the compressed runtime from `ρ` and the empty database, the joint state
at every leaf is supported on databases with at most `q` nonempty cells. -/
theorem databaseSupportedOn_jointPost_compressedRuntime (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q)
    (ρ : SubState A) (p : Σ u, W u) :
    DatabaseSupportedOn q ((compressedRuntime X Y).jointPost I x ρ p).matrix := by
  rw [QuantumRuntime.matrix_jointPost]
  have h := (databaseSupportedOn_kronecker_single_empty (X := X) (Y := Y)
    ρ.matrix).run_compressedRuntime I hx p
  rwa [Nat.zero_add] at h

/-- From the empty database, every call of a program that makes at most `q` calls on every path
receives an operator supported on databases with at most `q - 1` nonempty cells. -/
theorem forallQueries_compressedRuntime_prod_init (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q)
    (ρ : SubState A) :
    (compressedRuntime X Y).ForallQueries I
      (fun _ E σ ↦ QuerySupportedOn (fun m : ((X × Y) × Database X Y) × E ↦ m.1.2.size)
        (Set.Iic (q - 1)) σ) x (ρ.prod (compressedRuntime X Y).init).matrix :=
  forallQueries_compressedRuntime I hx (by omega)
    (databaseSupportedOn_kronecker_single_empty (X := X) (Y := Y) ρ.matrix)

end compressedRuntime

end Quantum
