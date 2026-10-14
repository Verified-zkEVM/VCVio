/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.LinearAlgebra.UnitaryGroup
public import VCVio.Quantum.Oracle.Basis

/-!
# The oracle unitary of a function

A quantum algorithm queries a function `H : X → Y` into an additive group `Y` on a register
`X × Y`: a query input and a response register. The query is the permutation of the
computational basis that adds the value of `H` into the response register,
`|x, y⟩ ↦ |x, y + H x⟩`. For `Y` a vector space over `ZMod 2` this is the XOR oracle. A program
keeps the rest of its register outside the call (`Quantum.QuantumComp.query` carries it along),
so the query register has no workspace.

## Main definitions

* `Quantum.oracleEquiv H`: the permutation `(x, y) ↦ (x, y + H x)` of the basis.
* `Quantum.oracleUnitary H`: its permutation matrix. It is unitary
  (`Quantum.oracleUnitary_mem_unitaryGroup`), and `H ↦ oracleUnitary H` turns addition of
  functions into multiplication (`Quantum.oracleUnitary_add`, `Quantum.oracleUnitary_zero`).
* `Quantum.oracleQuery H`: the query as a lossless quantum computation without outcome.
* `Quantum.QuerySupportedOn q S ρ`: the operator `ρ` vanishes outside the query inputs in `S`,
  read off each basis element by `q`. On such operators the query, also with an ancilla, only
  depends on the restriction of `H` to `S` (`Quantum.conj_oracleUnitary_congr`,
  `Quantum.amplify_conj_oracleUnitary_congr`).
-/

public section

open Matrix
open scoped ComplexOrder

namespace Quantum

variable {X Y M R : Type*}

/-! ## The basis permutation -/

section oracleEquiv

variable [AddGroup Y]

/-- The permutation of the basis of the register `X × Y` that adds `H x` into the response
register: `(x, y) ↦ (x, y + H x)`. -/
@[expose]
def oracleEquiv (H : X → Y) : X × Y ≃ X × Y where
  toFun m := (m.1, m.2 + H m.1)
  invFun m := (m.1, m.2 - H m.1)
  left_inv m := by simp
  right_inv m := by simp

/-- The oracle permutation adds `H x` into the response register. -/
@[simp]
theorem oracleEquiv_apply (H : X → Y) (m : X × Y) :
    oracleEquiv H m = (m.1, m.2 + H m.1) :=
  rfl

/-- The inverse of the oracle permutation subtracts `H x` from the response register. -/
@[simp]
theorem oracleEquiv_symm_apply (H : X → Y) (m : X × Y) :
    (oracleEquiv H).symm m = (m.1, m.2 - H m.1) :=
  rfl

/-- The oracle permutation of the zero function is the identity. -/
@[simp]
theorem oracleEquiv_zero : oracleEquiv (0 : X → Y) = Equiv.refl (X × Y) :=
  Equiv.ext fun m ↦ by simp

/-- The oracle permutation of a sum applies the oracle permutations one after the other. -/
theorem oracleEquiv_add (H H' : X → Y) :
    oracleEquiv (H + H') = (oracleEquiv H).trans (oracleEquiv H') :=
  Equiv.ext fun m ↦ by simp [add_assoc]

/-- The oracle permutation of the negated function is the inverse permutation. -/
theorem oracleEquiv_neg (H : X → Y) : oracleEquiv (-H) = (oracleEquiv H).symm :=
  Equiv.ext fun m ↦ by simp [sub_eq_add_neg]

end oracleEquiv

/-! ## The unitary -/

section oracleUnitary

variable [AddCommGroup Y] [DecidableEq X] [DecidableEq Y]

/-- The oracle unitary of `H : X → Y` on the register `X × Y`: the permutation matrix sending the
basis vector `|x, y⟩` to `|x, y + H x⟩`. -/
@[expose]
def oracleUnitary (H : X → Y) : Matrix (X × Y) (X × Y) ℂ :=
  basisMatrix (oracleEquiv H)

/-- The entry of the oracle unitary at `(m, m')` is one when `m` is `m'` with `H` added into the
response register, and zero otherwise. -/
theorem oracleUnitary_apply (H : X → Y) (m m' : X × Y) :
    oracleUnitary H m m' = if m = (m'.1, m'.2 + H m'.1) then 1 else 0 :=
  rfl

/-- The oracle unitary of the zero function is the identity matrix. -/
@[simp]
theorem oracleUnitary_zero : oracleUnitary (0 : X → Y) = (1 : Matrix (X × Y) _ ℂ) := by
  rw [oracleUnitary, oracleEquiv_zero]
  exact basisMatrix_id

/-- The adjoint of the oracle unitary of `H` is the oracle unitary of `-H`. -/
theorem conjTranspose_oracleUnitary (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y) _ ℂ)ᴴ = oracleUnitary (-H) := by
  rw [oracleUnitary, conjTranspose_basisMatrix_equiv, oracleUnitary, oracleEquiv_neg]

/-- Conjugation by the oracle unitary relabels rows and columns by subtracting `H` from the
response register. -/
theorem conj_oracleUnitary_apply [Fintype X] [Fintype Y] (H : X → Y)
    (ρ : Matrix (X × Y) (X × Y) ℂ) (m m' : X × Y) :
    MatrixMap.conj (oracleUnitary H) ρ m m' = ρ (m.1, m.2 - H m.1) (m'.1, m'.2 - H m'.1) := by
  rw [oracleUnitary, conj_basisMatrix_equiv]
  rfl

variable [Fintype X] [Fintype Y]

/-- The oracle unitary sends the basis vector `|x, y⟩` to `|x, y + H x⟩`. -/
theorem oracleUnitary_mulVec_single (H : X → Y) (m : X × Y) :
    oracleUnitary H *ᵥ Pi.single m 1 = Pi.single (m.1, m.2 + H m.1) 1 :=
  basisMatrix_mulVec_single _ m

/-- The oracle unitary of a sum of functions is the product of the oracle unitaries. -/
theorem oracleUnitary_add (H H' : X → Y) :
    (oracleUnitary (H + H') : Matrix (X × Y) _ ℂ) = oracleUnitary H * oracleUnitary H' := by
  rw [oracleUnitary, add_comm, oracleEquiv_add, Equiv.coe_trans, basisMatrix_comp]
  rfl

/-- The oracle unitaries of two functions commute. -/
theorem oracleUnitary_mul_comm (H H' : X → Y) :
    (oracleUnitary H : Matrix (X × Y) _ ℂ) * oracleUnitary H' =
      oracleUnitary H' * oracleUnitary H := by
  rw [← oracleUnitary_add, ← oracleUnitary_add, add_comm]

/-- The oracle unitary is an isometry. -/
theorem conjTranspose_oracleUnitary_mul_self (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y) _ ℂ)ᴴ * oracleUnitary H = 1 :=
  conjTranspose_basisMatrix_mul_self (oracleEquiv H).injective

/-- The oracle unitary is a coisometry. -/
theorem oracleUnitary_mul_conjTranspose_self (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y) _ ℂ) * (oracleUnitary H)ᴴ = 1 := by
  rw [conjTranspose_oracleUnitary, ← oracleUnitary_add, add_neg_cancel, oracleUnitary_zero]

/-- The oracle unitary is a unitary matrix. -/
theorem oracleUnitary_mem_unitaryGroup (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y) _ ℂ) ∈ Matrix.unitaryGroup (X × Y) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (oracleUnitary_mul_conjTranspose_self H)

/-! ## The query as a quantum computation -/

/-- One query to `H` on the register `X × Y`: the gate of the oracle unitary. -/
@[expose]
noncomputable def oracleQuery (H : X → Y) : SubInstrument (X × Y) (X × Y) Unit :=
  SubInstrument.ofIsometry (oracleUnitary H) (conjTranspose_oracleUnitary_mul_self H)

/-- The unique branch of a query is conjugation by the oracle unitary. -/
@[simp]
theorem branch_oracleQuery_apply (H : X → Y) (u : Unit) :
    (oracleQuery H : SubInstrument (X × Y) (X × Y) Unit).branch u =
      MatrixMap.conj (oracleUnitary H) :=
  SubInstrument.branch_ofIsometry_apply ..

/-- A query is lossless. -/
theorem lossless_oracleQuery (H : X → Y) :
    (oracleQuery H : SubInstrument (X × Y) (X × Y) Unit).Lossless :=
  SubInstrument.lossless_ofIsometry _ _

/-- A query to the zero function returns without touching the register. -/
theorem oracleQuery_zero :
    (oracleQuery (0 : X → Y) : SubInstrument (X × Y) (X × Y) Unit) =
      SubInstrument.pure () :=
  SubInstrument.ext <| funext fun ⟨⟩ ↦ by simp

/-- A query to `H` followed by a query to `H'` is one query to `H + H'`. -/
theorem oracleQuery_bind_oracleQuery (H H' : X → Y) :
    ((oracleQuery H : SubInstrument (X × Y) (X × Y) Unit).bind fun _ ↦ oracleQuery H') =
      oracleQuery (H + H') :=
  SubInstrument.ext <| funext fun u ↦ by
    rw [SubInstrument.branch_bind_unit, branch_oracleQuery_apply, branch_oracleQuery_apply,
      branch_oracleQuery_apply, ← MatrixMap.conj_mul, ← oracleUnitary_add, add_comm]

/-- A query sends the basis state at `(x, y)` to the basis state at `(x, y + H x)`. -/
theorem post_oracleQuery_basis (H : X → Y) (m : X × Y) :
    (oracleQuery H).post (SubState.basis m) () = SubState.basis (m.1, m.2 + H m.1) :=
  SubState.ext <| by
    rw [SubInstrument.matrix_post, branch_oracleQuery_apply, SubState.matrix_basis, oracleUnitary,
      conj_basisMatrix_equiv_single]
    rfl

end oracleUnitary

/-! ## Operators supported on a set of query inputs -/

section QuerySupportedOn

/-- The operator `ρ` on a register with basis `M` is supported on the query inputs in `S`, where
`q : M → X` reads the query input of a basis element: an entry is nonzero only when the query
inputs of its row and of its column lie in `S`. For a normalized state, of trace one, this says
that measuring the query input yields an element of `S` with certainty; for a substate, that the
measurement gives zero weight to inputs outside `S`. -/
@[expose]
def QuerySupportedOn (q : M → X) (S : Set X) (ρ : Matrix M M ℂ) : Prop :=
  ∀ m m', ρ m m' ≠ 0 → q m ∈ S ∧ q m' ∈ S

/-- Every operator is supported on the set of all query inputs. -/
theorem querySupportedOn_univ (q : M → X) (ρ : Matrix M M ℂ) : QuerySupportedOn q Set.univ ρ :=
  fun _ _ _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- Support on a set of query inputs passes to larger sets. -/
theorem QuerySupportedOn.mono {q : M → X} {S T : Set X} {ρ : Matrix M M ℂ}
    (hρ : QuerySupportedOn q S ρ) (hST : S ⊆ T) : QuerySupportedOn q T ρ :=
  fun m m' h ↦ ⟨hST (hρ m m' h).1, hST (hρ m m' h).2⟩

/-- The zero operator is supported on every set of query inputs. -/
theorem querySupportedOn_zero (q : M → X) (S : Set X) : QuerySupportedOn q S (0 : Matrix M M ℂ) :=
  fun _ _ h ↦ absurd rfl h

/-- A basis state is supported on any set containing its query input. -/
theorem querySupportedOn_single [DecidableEq M] {q : M → X} {S : Set X} {m : M} (hm : q m ∈ S) :
    QuerySupportedOn q S (Matrix.single m m (1 : ℂ)) := by
  intro a b h
  rw [Matrix.single_apply] at h
  split_ifs at h with hab
  · exact ⟨hab.1 ▸ hm, hab.2 ▸ hm⟩
  · exact absurd rfl h

/-- A block of an operator on `M × R` that is supported through the `M` component is supported
on the same query inputs. -/
theorem QuerySupportedOn.block {q : M → X} {S : Set X} {ρ : Matrix (M × R) (M × R) ℂ}
    (hρ : QuerySupportedOn (fun m : M × R ↦ q m.1) S ρ) (r r' : R) :
    QuerySupportedOn q S (ρ.submatrix (·, r) (·, r')) :=
  fun m m' h ↦ hρ (m, r) (m', r') h

variable [AddCommGroup Y] [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- On an operator supported on the query inputs in `S`, conjugation by the oracle unitary only
depends on the restriction of the function to `S`. -/
theorem conj_oracleUnitary_congr {S : Set X} {H H' : X → Y} (hH : Set.EqOn H H' S)
    {ρ : Matrix (X × Y) (X × Y) ℂ} (hρ : QuerySupportedOn Prod.fst S ρ) :
    MatrixMap.conj (oracleUnitary H) ρ = MatrixMap.conj (oracleUnitary H') ρ := by
  ext m m'
  rw [conj_oracleUnitary_apply, conj_oracleUnitary_apply]
  by_cases h : m.1 ∈ S ∧ m'.1 ∈ S
  · rw [hH h.1, hH h.2]
  · have h₁ := of_not_not fun h₀ ↦ h (hρ (m.1, m.2 - H m.1) (m'.1, m'.2 - H m'.1) h₀)
    have h₂ := of_not_not fun h₀ ↦ h (hρ (m.1, m.2 - H' m.1) (m'.1, m'.2 - H' m'.1) h₀)
    exact h₁.trans h₂.symm

/-- On an operator of the query register and an ancilla that is supported on the query inputs
in `S`, the query with the ancilla left alone only depends on the restriction of the function
to `S`. -/
theorem amplify_conj_oracleUnitary_congr {S : Set X} {H H' : X → Y} (hH : Set.EqOn H H' S)
    {ρ : Matrix ((X × Y) × R) ((X × Y) × R) ℂ}
    (hρ : QuerySupportedOn (fun m : (X × Y) × R ↦ m.1.1) S ρ) :
    (MatrixMap.conj (oracleUnitary H)).amplify R ρ =
      (MatrixMap.conj (oracleUnitary H')).amplify R ρ := by
  ext m m'
  rw [MatrixMap.amplify_apply, MatrixMap.amplify_apply,
    conj_oracleUnitary_congr hH (hρ.block m.2 m'.2)]

/-- A query keeps an operator supported on the query inputs in `S`. -/
theorem QuerySupportedOn.conj_oracleUnitary {S : Set X} {ρ : Matrix (X × Y) (X × Y) ℂ}
    (hρ : QuerySupportedOn Prod.fst S ρ) (H : X → Y) :
    QuerySupportedOn Prod.fst S (MatrixMap.conj (oracleUnitary H) ρ) := fun m m' h ↦ by
  rw [conj_oracleUnitary_apply] at h
  exact hρ (m.1, m.2 - H m.1) (m'.1, m'.2 - H m'.1) h

/-- On a substate supported on the query inputs in `S`, a query only depends on the restriction
of the function to `S`. -/
theorem post_oracleQuery_congr {S : Set X} {H H' : X → Y} (hH : Set.EqOn H H' S)
    {ρ : SubState (X × Y)} (hρ : QuerySupportedOn Prod.fst S ρ.matrix) :
    (oracleQuery H).post ρ () = (oracleQuery H').post ρ () :=
  SubState.ext <| by
    rw [SubInstrument.matrix_post, SubInstrument.matrix_post, branch_oracleQuery_apply,
      branch_oracleQuery_apply, conj_oracleUnitary_congr hH hρ]

end QuerySupportedOn

end Quantum
