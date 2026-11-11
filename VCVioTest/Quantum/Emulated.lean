/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Classical
public import VCVio.Quantum.Oracle.ClassicalRead
public import VCVio.Quantum.Oracle.Emulated
public import VCVio.Quantum.Oracle.EmulatedTensor

/-!
# Emulated oracle regression tests

A two-port emulated oracle on qubits with a qubit of private state: port `0` is the identity,
port `1` swaps the port qubit with the private qubit. Its runtime has lossless steps given by the
Kraus maps of the unitaries; extending it by a further port keeps the old ports; adjoining an
untouched register agrees with the general runtime combinator.

A program making one call of port `1` is translated to the coherent port: the translation runs
as the original program, makes at most `∑ i, 1` coherent calls, has the per-port query masses as
its masses, puts no mass on the index `0`, and satisfies the budget form of Remark 4.2.

Classical calls from inside an experiment elaborate against the signature of unitary ports: a
basis call is lossless and makes one call, a conjunction of checks over a set of indices adds
their budgets, a classical algorithm answered by basis calls is within `n` times the budget of
one call, and the classical reading of a fixed-register program keeps its budget.

## Semantic checks

* Against any emulated oracle, the branch of a basis call at a reading is the sum, over the
  port outputs `o` giving that reading, of the Kraus map of `1_B ⊗ ⟨o|U_p|a⟩`: the held register
  `B` is untouched and the private register is acted on by a block of the port's unitary.
* A basis call of the identity port keeps a held register entangled with the private state, off
  -diagonal entries included.
* A basis call of the swap port on the input `0` reads the private value and leaves `0` in the
  private register, on a basis state with distinct values and on a held register entangled with
  the private state.
* A conjunction whose first check fails still runs the second check, which writes into the
  private register.
* On the tensor-product interface, a query with the index in superposition moves the coherence
  between the two index branches along with the answers.
-/

public section

open Quantum Matrix
open scoped ENNReal ComplexOrder Kronecker

namespace VCVioTest.QuantumEmulated

/- Registers and signatures are written as notations rather than constants, so that no
finiteness instance is evaluated when the module is loaded. -/

/-- The qubit register. -/
local notation "Qubit" => QReg.of (Fin 2)

/-- The signature of two unitary ports on qubits. -/
local notation "spec2" => uSpec (Fin 2) fun _ ↦ QReg.of (Fin 2)

/-- Ports of a sum of signatures are the sum of the ports. -/
example : ((spec2).sum (uSpec Unit fun _ ↦ Qubit)).Port = (Fin 2 ⊕ Unit) :=
  rfl

/-- The ports of the two signatures of a sum may live in different universes. -/
example : ((spec2).sum (uSpec (ULift.{1} Unit) fun _ ↦ Qubit)).Port = (Fin 2 ⊕ ULift.{1} Unit) :=
  rfl

/-- Unitary ports return no classical result. -/
example (i : Fin 2) : (spec2).Result i = Unit :=
  rfl

/-- The unitaries of the swap oracle: the identity on port `0`, the swap of the port qubit with
the private qubit on port `1`. -/
noncomputable def swapU (i : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  if i = 0 then 1 else basisMatrix (Equiv.prodComm (Fin 2) (Fin 2))

/-- The unitaries of the swap oracle are unitary. -/
theorem swapU_mem_unitaryGroup (i : Fin 2) :
    swapU i ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  unfold swapU
  split_ifs
  · exact one_mem _
  · exact Matrix.mem_unitaryGroup_iff'.mpr
      (conjTranspose_basisMatrix_mul_self (Equiv.injective _))

/-- The swap oracle: two ports on qubits, one qubit of private state starting in `|0⟩`. It is
reducible so that its private register is seen to be a qubit. -/
@[expose, reducible] noncomputable def swapOracle : EmulatedOracle (Fin 2) fun _ ↦ Qubit where
  S := Qubit
  init := SubState.basis 0
  U := swapU
  unitary := swapU_mem_unitaryGroup

/-- The steps of the runtime are lossless. -/
example (i : Fin 2) : (swapOracle.toRuntime.step i).Lossless :=
  swapOracle.lossless_toRuntime_step i

/-- Each step is the Kraus map of its unitary. -/
example (i : Fin 2) (r : Unit) :
    (swapOracle.toRuntime.step i).branch r = MatrixMap.conj (swapU i) :=
  swapOracle.toRuntime_step_branch i r

/-- Extending by a further identity port keeps the old ports. -/
example :
    (swapOracle.extend (P' := Unit) (In' := fun _ ↦ Qubit) (fun _ ↦ 1)
      (fun _ ↦ one_mem _)).toRuntime.step (.inl 1) = swapOracle.toRuntime.step 1 :=
  swapOracle.toRuntime_extend_step_inl _ _ 1

/-- Extending by a port indexed in another universe needs no lifting of the old ports. -/
example :
    (swapOracle.extend (P' := ULift.{1} Unit) (In' := fun _ ↦ Qubit) (fun _ ↦ 1)
      (fun _ ↦ one_mem _)).toRuntime.step (.inr ⟨()⟩) =
      SubInstrument.ofIsometry 1 (Matrix.mem_unitaryGroup_iff'.mp (one_mem _)) :=
  swapOracle.toRuntime_extend_step_inr _ _ (ULift.up ())

/-- The general extension of a runtime answers the new ports by the added steps. -/
example (s : Unit → SubInstrument (Qubit × swapOracle.toRuntime.D)
      (Qubit × swapOracle.toRuntime.D) Unit) :
    ((swapOracle.toRuntime.extend (t := uSpec Unit fun _ ↦ Qubit) s).step (.inr ())) = s () :=
  rfl

/-- The two ways of adjoining an untouched register agree. -/
example :
    (swapOracle.addRegister Qubit (SubState.basis 1)).toRuntime =
      swapOracle.toRuntime.addRegister Qubit (SubState.basis 1) :=
  swapOracle.toRuntime_addRegister _ _

/-- The register of a program holding one qubit and nothing beside it. -/
local notation "Reg" => QReg.of (Fin 2 × Unit)

/-- One call of the swap port on the program's qubit. -/
noncomputable def oneCall :=
  QuantumComp.query (L := LocalSig.instruments.{0}) (spec := spec2) (A := Reg) 1 (QReg.of Unit)
    (Equiv.refl _)

/-- One call of the swap port is within a budget of one call per port. -/
theorem isQueryBound_oneCall : oneCall.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos

/-- The coherent translation makes at most the total budget of calls. -/
theorem isQueryBound_toCoherent_oneCall :
    oneCall.toCoherent.IsQueryBound fun _ ↦ ∑ _ : Fin 2, 1 :=
  QuantumComp.isQueryBound_toCoherent isQueryBound_oneCall

/-- The coherent translation runs as the original program. -/
example :
    swapOracle.coherent.toRuntime.run .instruments oneCall.toCoherent =
      swapOracle.toRuntime.run .instruments oneCall :=
  swapOracle.run_toCoherent oneCall

/-- The masses of the coherent translation are the per-port query masses. -/
example (ρ : Matrix (Reg × swapOracle.S) (Reg × swapOracle.S) ℂ) (i : Fin 2) :
    swapOracle.totalMass .instruments oneCall.toCoherent ρ i =
      swapOracle.toRuntime.queryMass .instruments oneCall ρ i :=
  swapOracle.totalMass_toCoherent oneCall ρ i

/-- A call of port `1` puts no mass on the index `0`. -/
theorem totalMass_toCoherent_oneCall_zero {ρ : Matrix (Reg × swapOracle.S) (Reg × swapOracle.S) ℂ}
    (hρ : ρ.PosSemidef) : swapOracle.totalMass .instruments oneCall.toCoherent ρ 0 = 0 := by
  rw [swapOracle.totalMass_toCoherent]
  have h : oneCall.IsQueryBound (Pi.single 1 1) :=
    (QuantumComp.isQueryBound_query_iff _ _ _ _).mpr (by simp)
  have h0 := swapOracle.toRuntime.queryMass_le_of_isQueryBoundAt .instruments (h 0) hρ
  simpa using h0

/-- The masses are the index masses of the index projectors, so the vanishing mass on the index
`0` is a vanishing index mass, in the form consumed by the hybrid bounds with index masses. -/
example {ρ : Matrix (Reg × swapOracle.S) (Reg × swapOracle.S) ℂ} (hρ : ρ.PosSemidef) :
    swapOracle.coherent.toRuntime.indexMass .instruments
      (fun _ ↦ EmulatedOracle.cohIndexProj fun _ : Fin 2 ↦ Qubit) oneCall.toCoherent ρ
        ⟨(), 0⟩ = 0 := by
  rw [← swapOracle.totalMass_eq_indexMass]
  exact totalMass_toCoherent_oneCall_zero hρ

/-- The index projectors of the coherent oracle form a coherent index that its unitary
respects. -/
example :
    Hybrid.RespectsIndex (spec := EmulatedOracle.cohSpec fun _ : Fin 2 ↦ Qubit)
      (fun _ ↦ EmulatedOracle.cohIndexProj _) (fun _ ↦ EmulatedOracle.cohIndexProj _)
      fun _ _ ↦ swapOracle.coherent.U () - swapOracle.coherent.U () :=
  swapOracle.respectsIndex_coherent_U.sub swapOracle.respectsIndex_coherent_U

/-- **Remark 4.2 with a budget.** The masses on the indices add up to at most the number of
coherent calls times the trace. -/
example {ρ : Matrix (Reg × swapOracle.S) (Reg × swapOracle.S) ℂ} (hρ : ρ.PosSemidef) :
    ∑ i, swapOracle.totalMass .instruments oneCall.toCoherent ρ i ≤
      (∑ _ : Fin 2, 1 : ℕ) * ENNReal.ofReal ρ.trace.re :=
  swapOracle.sum_totalMass_le .instruments (isQueryBound_toCoherent_oneCall ()) hρ

/-- A basis call of the swap port on the input `|0⟩`, reading the output qubit. -/
noncomputable def swapCall : QComp spec2 (QReg.of Unit) (QReg.of Unit) (Fin 2) :=
  QComp.callBasis (spec := spec2) 1 (QReg.of Unit) 0 fun o _ ↦ o

/-- A basis call is lossless. -/
example : swapCall.Lossless .instruments :=
  QComp.lossless_callBasis _ _ _ _

/-- A basis call makes one call of its port. -/
example : swapCall.IsQueryBound (Pi.single 1 1) :=
  QComp.isQueryBound_callBasis_single _ _ _ _

/-- Check that a basis call of every port on the input `|0⟩` returns `0`. -/
noncomputable def allZero : QComp spec2 (QReg.of Unit) (QReg.of Unit) Bool :=
  QComp.allIn Finset.univ fun i : Fin 2 ↦
    QComp.callBasis (spec := spec2) i (QReg.of Unit) 0 fun o _ ↦ decide (o = 0)

/-- The conjunction of checks adds their budgets. -/
example : allZero.IsQueryBound (∑ i : Fin 2, Pi.single i 1) :=
  QComp.isQueryBound_allIn _ _ fun _ _ ↦ QComp.isQueryBound_callBasis_single _ _ _ _

/-- The conjunction of lossless checks is lossless. -/
example : allZero.Lossless .instruments :=
  QComp.lossless_allIn _ _ fun _ _ ↦ QComp.lossless_callBasis _ _ _ _

/-- Answer the classical queries `t : Fin 2` by basis calls of port `t` on the input `|t⟩`. -/
noncomputable def basisImpl :
    QueryImpl (Fin 2 →ₒ Fin 2) (QComp spec2 (QReg.of Unit) (QReg.of Unit)) :=
  fun t ↦ QComp.callBasis (spec := spec2) t (QReg.of Unit) t fun o _ ↦ o

/-- A classical algorithm making `n` queries runs within `n` basis calls of every port. -/
example {oa : OracleComp (Fin 2 →ₒ Fin 2) Bool} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n) :
    (oa.toQuantumAt basisImpl).IsQueryBound (n • fun _ ↦ 1) :=
  OracleComp.isQueryBound_toQuantumAt (fun _ ↦ QComp.isQueryBound_callBasis Nat.one_pos _ _ _) h

/-- A classical algorithm that returns at once runs to the program that returns at once. -/
example (b : Bool) :
    (pure b : OracleComp (Fin 2 →ₒ Fin 2) Bool).toQuantumAt basisImpl = QuantumComp₂.pure b :=
  OracleComp.toQuantumAt_pure basisImpl b

/-- Reading a fixed-register program as a general program keeps its budget. -/
example : swapCall.forgetReg.IsQueryBound (Pi.single 1 1) :=
  QuantumComp₂.isQueryBound_forgetReg (QComp.isQueryBound_callBasis_single _ _ _ _)

/-! ## Semantics of a basis call -/

section callBasis

variable {P : Type} {In : P → QReg} (E : EmulatedOracle P In)

/-- The block `⟨o|U_p|a⟩` of the unitary of port `p` on the private register. -/
noncomputable def block (p : P) (o a : In p) : Matrix E.S E.S ℂ :=
  (E.U p).submatrix (fun d ↦ (o, d)) fun d ↦ (a, d)

/-- **A basis call against an emulated oracle.** The branch at `c` of a basis call of port `p`
on the input `a`, beside a held register `B`, sums the Kraus maps of `1_B ⊗ ⟨o|U_p|a⟩` over the
outputs `o` read as `c`. -/
theorem branch_run₂_callBasis {β : Type} [DecidableEq β] (p : P) (B : QReg) (a : In p)
    (read : In p → Unit → β) (c : β) :
    (E.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec P In) p B a read)).branch c =
      ∑ o, if read o () = c then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ block E p o a)
        else 0 := by
  rw [QComp.run₂_callBasis, DSubInstrument.branch_bind_unit, DSubInstrument.branch_bind_unit,
    SubInstrument.bind_pure, E.toRuntime.queryStep_branch_eq_conj (M := E.U p) rfl]
  simp only [QComp.callBasisPrep, QComp.callBasisMeasure, DSubInstrument.branch_bind_unit,
    DSubInstrument.branch_bind_bind_unit_ret, DSubInstrument.classical,
    DSubInstrument.branch_map_apply_univ, cast_eq, dite_eq_ite,
    DSubInstrument.branch_frame_apply,
    DSubInstrument.branch_ofKraus_apply, SubInstrument.branch_relabel, ite_true,
    Fintype.sum_unique, ← Finset.sum_filter, MatrixMap.amplify_sum, MatrixMap.amplify_comp,
    MatrixMap.amplify_conj, ← MatrixMap.conj_mul]
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  simp only [← LinearMap.comp_apply, ← MatrixMap.conj_mul]
  refine congrArg (MatrixMap.conj · ρ) ?_
  have hR : ((single a () (1 : ℂ) ⊗ₖ (1 : Matrix B B ℂ)) *
      basisMatrix (Equiv.uniqueProd B Unit).symm) ⊗ₖ (1 : Matrix E.S E.S ℂ) =
      basisMatrix fun x : B × E.S ↦ ((a, x.1), x.2) := by
    ext ⟨⟨i, b⟩, d⟩ ⟨b', d'⟩
    simp only [kroneckerMap_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply,
      Fintype.sum_prod_type, basisMatrix_apply]
    split_ifs <;> simp_all
  have hL : (basisMatrix (Equiv.uniqueProd B Unit) ⊗ₖ (1 : Matrix E.S E.S ℂ)) *
      ((single () o (1 : ℂ) ⊗ₖ (1 : Matrix B B ℂ)) ⊗ₖ (1 : Matrix E.S E.S ℂ)) =
      (basisMatrix fun x : B × E.S ↦ ((o, x.1), x.2))ᴴ := by
    ext ⟨b, d⟩ ⟨⟨i, b'⟩, d'⟩
    simp only [kroneckerMap_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply,
      Fintype.sum_prod_type, basisMatrix_apply, conjTranspose_apply]
    split_ifs <;> first | (simp_all; done) | (simp_all; tauto)
  rw [hR, ← Matrix.mul_assoc, hL]
  simp only [Matrix.mul_assoc]
  rw [← basisMatrix_comp, basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut _ _ _),
    ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← basisMatrix_comp, ← Matrix.mul_assoc,
    conjTranspose_basisMatrix_mul_mul_basisMatrix]
  ext ⟨b, d⟩ ⟨b', d'⟩
  simp [block, QuantumRuntime.queryEquivOut, Matrix.one_apply]

end callBasis

/-- The blocks of the identity port. -/
theorem block_swap_zero (o a : Fin 2) : block swapOracle 0 o a = if o = a then 1 else 0 := by
  refine Matrix.ext fun (d' d : Fin 2) ↦ ?_
  change swapU 0 (o, d') (a, d) = (if o = a then (1 : Matrix (Fin 2) (Fin 2) ℂ) else 0) d' d
  by_cases h : o = a <;> simp [swapU, Matrix.one_apply, h, Prod.ext_iff]

/-- The blocks of the swap port: `⟨o|U_1|a⟩ = |a⟩⟨o|` on the private qubit. -/
theorem block_swap_one (o a : Fin 2) : block swapOracle 1 o a = Matrix.single a o 1 := by
  refine Matrix.ext fun (d' d : Fin 2) ↦ ?_
  change swapU 1 (o, d') (a, d) = (Matrix.single a o 1 : Matrix (Fin 2) (Fin 2) ℂ) d' d
  simp [swapU, Matrix.single_apply, Prod.ext_iff, eq_comm, and_comm]

/-- **A held register stays entangled through a basis call.** A basis call of the identity port
reads its input with certainty and leaves the held register and the private register as they
were, coherences included. -/
theorem branch_identityCall (B : QReg) (a o : Fin 2) :
    (swapOracle.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := spec2) 0 B a fun o _ ↦ o)).branch o =
      if o = a then LinearMap.id else 0 := by
  rw [branch_run₂_callBasis, Fintype.sum_ite_eq', block_swap_zero]
  split_ifs
  · rw [Matrix.one_kronecker_one, MatrixMap.conj_one]
  · rw [Matrix.kronecker_zero, MatrixMap.conj_zero]

/-- The basis state `|b, d⟩` of a held qubit and the private qubit. -/
noncomputable def ket (b d : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.single (b, d) (b, d) 1

/-- The maximally entangled state `(|00⟩ + |11⟩)(⟨00| + ⟨11|) / 2` of a held qubit and the
private qubit. -/
noncomputable def bell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y ↦ if x.1 = x.2 ∧ y.1 = y.2 then 1 / 2 else 0

/-- The entangled state has an off-diagonal entry. -/
example : bell (0, 0) (1, 1) = 1 / 2 := by
  simp [bell]

/-- A basis call of the identity port keeps the entangled state, off-diagonal entries included. -/
example : (swapOracle.toRuntime.run₂ .instruments
    (QComp.callBasis (spec := spec2) 0 Qubit 1 fun o _ ↦ o)).branch 1 bell = bell := by
  rw [branch_identityCall]
  simp only [↓reduceIte, LinearMap.id_apply]

/-- **A swap call with distinct input and private values.** On `|b, 1⟩`, a basis call of the swap
port on the input `0` reads the private value `1` and leaves `0` in the private register. -/
theorem branch_swapCall_ket (b : Fin 2) :
    (swapOracle.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := spec2) 1 Qubit 0 fun o _ ↦ o)).branch 1 (ket b 1) =
      ket b 0 := by
  rw [branch_run₂_callBasis, Fintype.sum_ite_eq', block_swap_one]
  change MatrixMap.conj (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (ket b 1) = ket b 0
  refine Matrix.ext fun ((c, d) : Fin 2 × Fin 2) ((c', d') : Fin 2 × Fin 2) ↦ ?_
  fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases c' <;> fin_cases d' <;>
    simp [ket, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.single_apply, Fin.sum_univ_two]

/-- **A swap call on a held register entangled with the private state.** Each reading `o` has
weight `1/2`, the held qubit collapses to `o` with the private qubit it was entangled with, and
the private register holds the input `0`. -/
theorem branch_swapCall_bell (o : Fin 2) :
    (swapOracle.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := spec2) 1 Qubit 0 fun o _ ↦ o)).branch o bell =
      (1 / 2 : ℂ) • ket o 0 := by
  rw [branch_run₂_callBasis, Fintype.sum_ite_eq', block_swap_one]
  change MatrixMap.conj (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
    (Matrix.single 0 o 1 : Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      bell = (1 / 2 : ℂ) • ket o 0
  refine Matrix.ext fun ((c, d) : Fin 2 × Fin 2) ((c', d') : Fin 2 × Fin 2) ↦ ?_
  fin_cases o <;> fin_cases c <;> fin_cases d <;> fin_cases c' <;> fin_cases d' <;>
    simp [ket, bell, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.single_apply,
      Fin.sum_univ_two]

/-! ## A conjunction runs every check -/

/-- Two checks: the identity port on the input `0` read as "is `1`", which fails, then the swap
port on the input `1`, which accepts and writes `1` into the private register. -/
noncomputable def failThenWrite : QComp spec2 (QReg.of Unit) (QReg.of Unit) Bool :=
  QComp.allIn Finset.univ
    ![QComp.callBasis (spec := spec2) 0 (QReg.of Unit) 0 fun o _ ↦ decide (o = 1),
      QComp.callBasis (spec := spec2) 1 (QReg.of Unit) 1 fun _ _ ↦ true]

/-- The private register in the basis state `|d⟩`, beside the trivial register. -/
noncomputable def priv (d : Fin 2) :
    Matrix (QReg.of Unit × swapOracle.toRuntime.D) (QReg.of Unit × swapOracle.toRuntime.D) ℂ :=
  Matrix.single ((), d) ((), d) 1

/-- The failing check reports `false` and changes nothing. -/
theorem branch_check0 (x : Bool) :
    (swapOracle.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := spec2) 0 (QReg.of Unit) 0 fun o _ ↦ decide (o = 1))).branch x =
      if x then 0 else LinearMap.id := by
  rw [branch_run₂_callBasis, Fin.sum_univ_two, block_swap_zero, block_swap_zero]
  cases x <;> simp [MatrixMap.conj_one]

/-- The writing check, from `|0⟩`, reports `true` and leaves `|1⟩`. -/
theorem branch_check1 (y : Bool) :
    (swapOracle.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := spec2) 1 (QReg.of Unit) 1 fun _ _ ↦ true)).branch y (priv 0) =
      if y then priv 1 else 0 := by
  rw [branch_run₂_callBasis]
  cases y
  · simp only [Bool.true_eq_false, ite_false, Finset.sum_const_zero]
    rfl
  · simp only [ite_true, block_swap_one]
    change (∑ o : Fin 2, MatrixMap.conj (((1 : Matrix Unit Unit ℂ) ⊗ₖ
      (Matrix.single 1 o 1 : Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ))
        (Matrix.single ((), 0) ((), 0) 1 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ) =
        (Matrix.single ((), 1) ((), 1) 1 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)
    refine Matrix.ext fun ((u, d) : Unit × Fin 2) ((u', d') : Unit × Fin 2) ↦ ?_
    fin_cases d <;> fin_cases d' <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.single_apply, Fin.sum_univ_two]

/-- **No short-circuit.** From `|0⟩`, the conjunction reports `false` with certainty and leaves
the private register in `|1⟩`: the second check ran after the first one failed. -/
theorem branch_failThenWrite :
    (swapOracle.toRuntime.run₂ .instruments failThenWrite).branch false (priv 0) = priv 1 := by
  simp only [failThenWrite, QComp.allIn]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finset.mem_univ, ↓reduceIte,
    QuantumComp₂.map_eq, List.finRange_succ, Fin.isValue, List.finRange_zero, List.map_nil,
    List.map_cons, Fin.succ_zero_eq_one, List.foldlM_cons, Bool.true_and, cons_val_zero,
    cons_val_one, cons_val_fin_one, List.foldlM_nil, QuantumComp₂.pure_eq, QuantumComp₂.bind_eq,
    QuantumComp₂.bind_pure, QuantumRuntime.run₂_bind, QuantumRuntime.run₂_map]
  rw [DSubInstrument.branch_bind_apply_univ, Fintype.sum_bool]
  simp only [DSubInstrument.branch_map_apply_univ, cast_eq, dite_eq_ite, branch_check0]
  simp only [Fintype.univ_bool, Bool.true_and, Finset.sum_ite_eq', Finset.mem_insert,
    Bool.false_eq_true, Finset.mem_singleton, or_true, ↓reduceIte, Bool.true_eq_false, or_false,
    LinearMap.comp_zero, Bool.false_and, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, LinearMap.comp_id, zero_add, Fin.isValue, LinearMap.add_apply]
  rw [branch_check1, branch_check1]
  simp

/-! ## The tensor-product interface -/

/-- The contents `(0, 0)` of the two port registers. -/
def x00 : ∀ _ : Fin 2, Fin 2 := ![0, 0]

/-- The contents `(0, 1)` of the two port registers. -/
def x01 : ∀ _ : Fin 2, Fin 2 := ![0, 1]

/-- The tensor-product query register beside the private register. -/
local notation "TReg" => (EmulatedOracle.tensIn (fun _ : Fin 2 ↦ Qubit) × swapOracle.S : Type)

/-- The query `|0, (0, 0), 1⟩ + |1, (0, 0), 1⟩`, with the index in superposition. -/
noncomputable def ψin : TReg → ℂ := Pi.single ((0, x00), 1) 1 + Pi.single ((1, x00), 1) 1

/-- The answer `|0, (0, 0), 1⟩ + |1, (0, 1), 0⟩`: port `0` leaves its branch alone and port `1`
swaps its register with the private qubit. -/
noncomputable def ψout : TReg → ℂ := Pi.single ((0, x00), 1) 1 + Pi.single ((1, x01), 0) 1

/-- The tensor-product unitary on the branch with index `0`. -/
theorem tensor_U_col0 :
    (fun z ↦ swapOracle.tensor.U () z ((0, x00), 1)) = Pi.single ((0, x00), 1) 1 := by
  funext ⟨⟨i, x⟩, d⟩
  rw [EmulatedOracle.tensor_U_apply]
  by_cases hi : i = 0
  · subst hi
    simp [swapU, x00, Pi.single_apply, Prod.ext_iff, funext_iff, Fin.forall_fin_two,
      Matrix.one_apply]
    split_ifs <;> simp_all
  · simp [hi, Prod.ext_iff]

/-- The tensor-product unitary on the branch with index `1`. -/
theorem tensor_U_col1 :
    (fun z ↦ swapOracle.tensor.U () z ((1, x00), 1)) = Pi.single ((1, x01), 0) 1 := by
  funext ⟨⟨i, x⟩, d⟩
  rw [EmulatedOracle.tensor_U_apply]
  by_cases hi : i = 1
  · subst hi
    simp [swapU, x00, x01, Pi.single_apply, Prod.ext_iff, funext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all
  · simp [hi, Prod.ext_iff]

/-- The tensor-product unitary sends the query to the answer. -/
theorem tensor_U_mulVec : swapOracle.tensor.U () *ᵥ ψin = ψout := by
  rw [ψin, ψout, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  exact congrArg₂ (· + ·) tensor_U_col0 tensor_U_col1

/-- **A coherent query.** A call of the tensor-product port sends the pure state of the query to
the pure state of the answer. -/
theorem step_tensor_superposition :
    (swapOracle.tensor.toRuntime.step ()).branch ()
      ((1 / 2 : ℂ) • Matrix.vecMulVec ψin (star ψin)) =
      (1 / 2 : ℂ) • Matrix.vecMulVec ψout (star ψout) := by
  rw [EmulatedOracle.toRuntime_step_branch, map_smul, MatrixMap.conj_apply, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, ← Matrix.star_mulVec, tensor_U_mulVec]

/-- The query has an off-diagonal entry between its two index branches. -/
example : ((1 / 2 : ℂ) • Matrix.vecMulVec ψin (star ψin)) ((0, x00), 1) ((1, x00), 1) = 1 / 2 := by
  simp [ψin, Matrix.vecMulVec_apply, x00]

/-- The off-diagonal entry moves with the answers; a dephased index would make it zero. -/
example :
    ((1 / 2 : ℂ) • Matrix.vecMulVec ψout (star ψout)) ((0, x00), 1) ((1, x01), 0) = 1 / 2 := by
  simp [ψout, Matrix.vecMulVec_apply, x00, x01, funext_iff, Fin.forall_fin_two]

/-- The register of a program holding a tensor-product query and nothing beside it. -/
local notation "TProgReg" => QReg.of (EmulatedOracle.tensIn (fun _ : Fin 2 ↦ Qubit) × Unit)

/-- One call of the tensor-product port. -/
noncomputable def oneTensorCall :=
  QuantumComp.query (L := LocalSig.instruments.{0})
    (spec := EmulatedOracle.tensSpec fun _ : Fin 2 ↦ Qubit) (A := TProgReg) () (QReg.of Unit)
    (Equiv.refl _)

/-- Its translation to the direct-sum port runs as the tensor-product program. -/
example :
    swapOracle.coherent.toRuntime.run .instruments oneTensorCall.tensorToCoherent =
      swapOracle.tensor.toRuntime.run .instruments oneTensorCall :=
  swapOracle.run_tensorToCoherent oneTensorCall

/-- Its translation has the per-index masses of the tensor-product program. -/
example (ρ : Matrix (TProgReg × swapOracle.S) (TProgReg × swapOracle.S) ℂ) (i : Fin 2) :
    swapOracle.totalMass .instruments oneTensorCall.tensorToCoherent ρ i =
      swapOracle.tensorMass .instruments oneTensorCall ρ i :=
  swapOracle.totalMass_tensorToCoherent oneTensorCall ρ i

/-- The masses on the tensor-product interface are the index masses of its index projectors. -/
example (ρ : Matrix (TProgReg × swapOracle.S) (TProgReg × swapOracle.S) ℂ) (i : Fin 2) :
    swapOracle.tensorMass .instruments oneTensorCall ρ i =
      swapOracle.tensor.toRuntime.indexMass .instruments
        (fun _ ↦ EmulatedOracle.tensIndexProj fun _ : Fin 2 ↦ Qubit) oneTensorCall ρ ⟨(), i⟩ :=
  swapOracle.tensorMass_eq_indexMass _ _ _ _

/-! ## Projective reads and total calls -/

/-- An identity service with a private qubit. -/
@[expose, reducible]
noncomputable def readOracle : EmulatedOracle Unit (fun _ ↦ Qubit) where
  S := Qubit
  init := SubState.basis 0
  U _ := 1
  unitary _ := one_mem _

/-- Both addresses read the same private qubit in the computational basis. -/
noncomputable def qubitAnswers : ProjectiveClassicalAnswers readOracle Bool (Fin 2) where
  A _ a := Matrix.diagonal fun d ↦ if d = a then 1 else 0
  hermitian _ a := by
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  orthogonal _ a b := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp
  complete _ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  commute_cells _ a _ b := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  commute_ordinary _ _ _ := by simp

/-- A runtime read collapses both halves of an entangled pair, with weight one half. -/
theorem branch_read_bell (a : Fin 2) :
    (readOracle.read qubitAnswers false Qubit).branch a bell = (1 / 2 : ℂ) • ket a a := by
  rw [EmulatedOracle.read_branch]
  change MatrixMap.conj ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
    Matrix.diagonal (fun d ↦ if d = a then 1 else 0)) bell = _
  ext ⟨b, d⟩ ⟨b', d'⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases b' <;> fin_cases d' <;>
    simp [MatrixMap.conj_apply, ket, bell, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]

/-- The read's two branches exhaust the Bell state's mass. -/
example : (∑ a, (readOracle.read qubitAnswers false Qubit).branch a bell).trace = 1 := by
  calc
    _ = (∑ a : Fin 2, (1 / 2 : ℂ) • ket a a).trace :=
      congrArg Matrix.trace (Finset.sum_congr rfl fun a _ ↦ branch_read_bell a)
    _ = 1 := by norm_num [ket, Fin.sum_univ_two, Matrix.trace, Fintype.sum_prod_type]

/-- Both ordinary and read steps are lossless in the concrete mixed runtime. -/
example (p : (withReadSpec (EmulatedOracle.cohSpec (fun _ : Unit ↦ Qubit)) Bool (Fin 2)).Port) :
    ((readOracle.withClassicalReads qubitAnswers).step p).Lossless :=
  readOracle.lossless_withClassicalReads_step qubitAnswers p

/-- Two distinct classical addresses consume two calls. -/
noncomputable def twoReads : QuantumComp LocalSig.instruments
    (withReadSpec (EmulatedOracle.cohSpec (fun _ : Unit ↦ Qubit)) Bool (Fin 2))
    (fun _ ↦ Unit) (QReg.of (Unit × Unit)) :=
  QuantumComp.queryBind (.inr false) (QReg.of Unit) (Equiv.refl _) fun _ ↦
    QuantumComp.queryBind (.inr true) (QReg.of Unit) (Equiv.refl _) fun _ ↦
      QuantumComp.pure ()

/-- A per-port budget of one permits the two reads. -/
example : twoReads.IsQueryBound (fun _ ↦ 1) := by
  intro p
  apply (QuantumComp.isQueryBoundAt_queryBind_iff _ _ _ _ _ _).mpr
  constructor
  · intro h
    subst p
    refine ⟨by decide, fun _ ↦ ?_⟩
    apply (QuantumComp.isQueryBoundAt_queryBind_iff _ _ _ _ _ _).mpr
    simp
  · intro _ _
    apply (QuantumComp.isQueryBoundAt_queryBind_iff _ _ _ _ _ _).mpr
    exact ⟨fun _ ↦ ⟨Nat.one_pos, fun _ ↦ QuantumComp.isQueryBoundAt_pure _ _ _⟩,
      fun _ _ ↦ QuantumComp.isQueryBoundAt_pure _ _ _⟩

/-- The total budget rejects those two reads at budget one. -/
example : ¬ twoReads.IsTotalQueryBound 1 := by
  intro h
  have h₁ := (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mp h
  have h₂ := (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mp (h₁.2 (0 : Fin 2))
  exact h₂.1.false

/-- The exact total budget accepts them at budget two. -/
example : twoReads.IsTotalQueryBound 2 := by
  apply (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
  refine ⟨by decide, fun _ ↦ ?_⟩
  apply (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
  exact ⟨by decide, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩

/-- Left injection preserves execution of any ordinary program in the concrete mixed runtime. -/
example {X : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments (EmulatedOracle.cohSpec (fun _ : Unit ↦ Qubit)) X A) :
    (readOracle.withClassicalReads qubitAnswers).run .instruments x.liftOrdinary =
      readOracle.coherent.toRuntime.run .instruments x :=
  readOracle.coherent.toRuntime.run_liftOrdinary
    (t := classicalReadSpec Bool (Fin 2)) .instruments qubitAnswers.step x

end VCVioTest.QuantumEmulated
