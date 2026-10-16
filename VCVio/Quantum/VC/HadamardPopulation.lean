/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardLocality
public import VCVio.Quantum.VC.Proof.Commutativity

/-!
# Population support for the extended witness

The repair note's population argument uses locality of the ordinary ports and diagonality of
the extraction port. It applies to arbitrary unitary empty-sector responses.
-/

public section

open Matrix OracleSpec
open scoped Kronecker

universe v w

namespace Quantum

open EmulatedOracle (cohSpec)

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (U : Matrix Y Y ℂ) (hU : U ∈ unitaryGroup Y ℂ)
  {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (Fin k → Database X Y))
  (code : TpDCode k Dm Z)

/-- Every port, including coherent extraction, raises each database population by at most one. -/
theorem extendedVCOracle_withExtract_U_size_le (i : Fin k) (p : Fin k ⊕ Unit)
    (a a' : extIn k X Y Cm Z p) (d d' : Fin k → Database X Y)
    (h : ((extendedVCOracle k X Y U hU).withExtract ME code).U p (a', d') (a, d) ≠ 0) :
    (d' i).size ≤ (d i).size + 1 := by
  rcases p with j | u
  · exact extendedVCPort_size_le U j i a' a d' d h
  · obtain ⟨tic', z'⟩ := a'
    obtain ⟨tic, z⟩ := a
    change extractUnitary ME code ((tic', z'), d') ((tic, z), d) ≠ 0 at h
    rw [extractUnitary_apply] at h
    split_ifs at h with hc
    · rw [hc.2.2]
      exact Nat.le_succ _
    · exact absurd rfl h

/-- **The size invariant for `EO^(Ext)`.** After a program that makes at most `t` calls to the
coherent port of `EO^(Ext)` for the k compressed oracles, the joint state at every outcome is
supported on tuples of databases whose `i`-th database has at most `t` nonempty cells. -/
theorem querySupportedOn_jointPost₂_extendedVCOracle_withExtract (i : Fin k) {A B : QReg}
    {α : Type w} (x : QuantumComp₂ LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) A B α)
    {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) (a : α) :
    QuerySupportedOn (fun m : B × (Fin k → Database X Y) ↦ (m.2 i).size) (Set.Iic t)
      (((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.jointPost₂
        .instruments x ρ a).matrix := by
  set F := ((extendedVCOracle k X Y U hU).withExtract ME code)
  have hR := F.coherent.querySupportedOn_toRuntime_step (fun d : Fin k → Database X Y ↦ (d i).size)
    fun j b b' d d' h ↦ F.coherent_U_grade (fun d : Fin k → Database X Y ↦ (d i).size)
      (fun p b b' d d' h ↦ extendedVCOracle_withExtract_U_size_le U hU ME code i p b b' d d' h)
      j b b' d d' h
  have h0 : QuerySupportedOn (fun m : A × (Fin k → Database X Y) ↦ (m.2 i).size) (Set.Iic 0)
      (ρ.matrix ⊗ₖ F.coherent.toRuntime.init.matrix) := by
    intro m m' hm
    change (ρ.matrix ⊗ₖ (SubState.basis fun _ : Fin k ↦ (Database.empty : Database X Y)).matrix)
      m m' ≠ 0 at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · refine ⟨?_, ?_⟩
      · change (m.2 i).size ≤ 0
        rw [← he.1]
        simp
      · change (m'.2 i).size ≤ 0
        rw [← he.2]
        simp
    · exact absurd rfl h
  have h := QuerySupportedOn.run_of_step F.coherent.toRuntime
    (fun d : Fin k → Database X Y ↦ (d i).size) hR .instruments hx h0 ⟨B, rfl, a⟩
  rw [QuantumRuntime.matrix_jointPost₂, QuantumRuntime.branch_run₂]
  simp only [Finset.univ_unique, Finset.sum_singleton, zero_add] at h
  exact h


end Quantum
