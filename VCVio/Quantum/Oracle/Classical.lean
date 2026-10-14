/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.Quantum.Oracle.Model

/-!
# Classical oracle algorithms in the quantum random-oracle model

A classical algorithm with oracle access to a function `X → Y` is an `OracleComp (X →ₒ Y) α`.
`OracleComp.toQuantum oa` is the quantum program over `Quantum.qromSpec X Y` that runs it on the
trivial register, by `simulateQ`: each query `t` is answered by `Quantum.classicalQuery t`, which
prepares the basis state `|t, 0⟩`, calls the oracle on it, reads the register in the
computational basis, returns the response, and discards the register. The program is adaptive
exactly as `oa` is: its continuation after each call is the continuation of `oa` at the response.

No query bound, workspace or default value is needed: the program tree is the tree of `oa`.

The embedding is a program over instruments (`Quantum.QComp`): its local steps, the preparation
of `|t, 0⟩` and the measurement of the register, are subinstruments, and it returns the value of
`oa` on the trivial register. The theorems below are stated for this fixed-register form and the
law of its value (`Quantum.qromLaw₂`), which is the general law of the quantum random-oracle model
(`Quantum.qromLawWith`) read through the value of each leaf.

## Main results

* `OracleComp.lossless_toQuantum` and `OracleComp.isQueryBound_toQuantum`: the program is
  lossless, and an algorithm making at most `n` queries runs to a program with budget `n`.
* `Quantum.outcomeLaw_toQuantum_of_basis`: against any runtime that answers a call on a basis
  state `|x, y⟩` with `|x, y + H x⟩`, leaves its private register alone and starts it in a basis
  state, the program reports `evalWithAnswerFn (QueryImpl.ofFn H) oa` with certainty.
* `Quantum.outcomeLaw_xorRuntime_toQuantum`: against the oracle unitary of `H`, the program
  reports `evalWithAnswerFn (QueryImpl.ofFn H) oa`, the value of `oa` when every query is answered
  by `H`, with certainty.
* `Quantum.qromLaw₂_toQuantum`: its law in the quantum random-oracle model is the output measure
  of the classical experiment that samples `H` uniformly and evaluates `oa` against it.
* `Quantum.qromLaw₂_toQuantum_eq_randomOracle`: this is also the output measure of `oa` under
  VCVio's lazily sampled, cached random oracle `randomOracle`.
-/

public section

open MeasureTheory OracleSpec
open scoped ENNReal Kronecker

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-! ## The embedding -/

/-- A classical query `t` as a quantum program on the trivial register: prepare `|t, 0⟩`, call
the oracle, read the register in the computational basis, return the response and discard the
register. -/
@[expose]
noncomputable def classicalQuery (t : X) :
    QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit) Y :=
  (QComp.act (B := QReg.of (X × Y))
      (SubInstrument.classical (fun _ : Unit ↦ (t, (0 : Y))) fun _ ↦ ())).bind fun _ ↦
    (QuantumComp₂.query (L := LocalSig.instruments) (spec := qromSpec X Y) () (QReg.of Unit)
        (Equiv.prodPUnit (X × Y)).symm).bind fun _ ↦
      QComp.act (A := QReg.of ((X × Y) × Unit))
        (SubInstrument.classical (fun _ ↦ ()) fun m : (X × Y) × Unit ↦ m.1.2)

/-- The implementation of the classical oracle `X →ₒ Y` by quantum programs on the trivial
register: query `t` is answered by `Quantum.classicalQuery t`. -/
@[expose]
noncomputable def classicalImpl :
    QueryImpl (X →ₒ Y) (QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit)) :=
  fun t ↦ classicalQuery t

/-- A classical query is a lossless program. -/
theorem lossless_classicalQuery (t : X) :
    (classicalQuery (Y := Y) t).Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_classical _ _)) fun _ ↦
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_query _ _ _) fun _ ↦
      QComp.lossless_act (SubInstrument.lossless_classical _ _)

/-- A classical query makes one call. -/
theorem isQueryBound_classicalQuery (t : X) :
    (classicalQuery (Y := Y) t).IsQueryBound fun _ ↦ 1 := by
  rw [classicalQuery, QComp.isQueryBound_act_bind_iff]
  intro _
  refine (QuantumComp₂.isQueryBound_bind (b₁ := fun _ ↦ 1) (b₂ := 0) ?_
    fun _ ↦ QComp.isQueryBound_act _ _).mono (add_zero _).le
  exact (QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos

end Quantum

namespace OracleComp

open Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A classical oracle algorithm as a quantum program over the random-oracle signature, on the
trivial register: every query is answered by `Quantum.classicalQuery`. -/
@[expose]
noncomputable def toQuantum (oa : OracleComp (X →ₒ Y) α) :
    QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit) α :=
  simulateQ classicalImpl oa

/-- A computation that returns at once runs to the program that returns at once. -/
@[simp]
theorem toQuantum_pure (a : α) :
    (pure a : OracleComp (X →ₒ Y) α).toQuantum = QuantumComp₂.pure a :=
  rfl

/-- A query followed by a continuation runs to the classical query followed by the programs of
the continuation. -/
@[simp]
theorem toQuantum_query_bind (t : X) (k : Y → OracleComp (X →ₒ Y) α) :
    (liftM ((X →ₒ Y).query t) >>= k : OracleComp (X →ₒ Y) α).toQuantum =
      (classicalQuery t).bind fun y ↦ (k y).toQuantum := by
  rw [toQuantum, simulateQ_bind, simulateQ_spec_query]
  rfl

/-- The quantum program of a classical algorithm is lossless. -/
theorem lossless_toQuantum (oa : OracleComp (X →ₒ Y) α) : oa.toQuantum.Lossless .instruments := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact QuantumComp₂.lossless_pure a
  | query_bind t k ih =>
    rw [toQuantum_query_bind]
    exact QuantumComp₂.lossless_bind (lossless_classicalQuery t) ih

/-- A classical algorithm making at most `n` queries runs to a program making at most `n`
calls. -/
theorem isQueryBound_toQuantum {oa : OracleComp (X →ₒ Y) α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : oa.toQuantum.IsQueryBound fun _ ↦ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact QuantumComp₂.isQueryBound_pure a _
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [toQuantum_query_bind]
    refine (QuantumComp₂.isQueryBound_bind (isQueryBound_classicalQuery t)
      fun y ↦ ih y (h.2 y)).mono fun _ ↦ ?_
    simp only [Pi.add_apply]
    omega

end OracleComp

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-! ## Runs against the oracle unitary -/

/-- The oracle unitary of `H` on a basis matrix. -/
private theorem branch_oracleQuery_single (H : X → Y) (m : X × Y) :
    (oracleQuery H).branch () (Matrix.single m m 1) =
      Matrix.single (m.1, m.2 + H m.1) (m.1, m.2 + H m.1) 1 := by
  have h := congrArg SubState.matrix (post_oracleQuery_basis H m)
  rwa [SubInstrument.matrix_post, SubState.matrix_basis, SubState.matrix_basis] at h

/-- Against a runtime that answers a call on a basis state `|x, y⟩` by moving it to
`|x, y + H x⟩` and leaves its private register alone, a classical query `t` from the trivial
state reports `H t` with weight one and returns to the trivial state. -/
theorem run_classicalQuery_branch_of_basis (H : X → Y) {R : QuantumRuntime (qromSpec X Y)}
    (hR : ∀ (m : X × Y) (d : R.D), (R.step ()).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1)
    (t : X) (d : R.D) (y : Y) :
    (R.run₂ .instruments (classicalQuery t)).branch y (Matrix.single ((), d) ((), d) 1) =
      if H t = y then Matrix.single ((), d) ((), d) 1 else 0 := by
  rw [classicalQuery, QuantumRuntime.run₂_act_bind, SubInstrument.branch_bind_unit,
    LinearMap.comp_apply, SubInstrument.branch_frame_single, SubInstrument.branch_classical_basis]
  simp only [↓reduceIte]
  rw [Matrix.single_kronecker_single, one_mul, QuantumRuntime.run₂_query_bind,
    SubInstrument.branch_bind_unit, LinearMap.comp_apply, QuantumRuntime.queryStep_branch_apply,
    SubInstrument.branch_relabel, SubInstrument.branch_relabel, conj_basisMatrix_equiv_single]
  simp only [QuantumRuntime.queryEquivIn_apply, Equiv.prodPUnit_symm_apply]
  rw [SubInstrument.branch_frame_single, hR, Matrix.single_kronecker_single, one_mul,
    conj_basisMatrix_equiv_single, QuantumRuntime.run₂_act, SubInstrument.bind_pure]
  simp only [QuantumRuntime.queryEquivOut_apply]
  rw [SubInstrument.branch_frame_single, SubInstrument.branch_classical_basis]
  by_cases h : H t = y <;> simp [h, Matrix.single_kronecker_single]

/-- The oracle unitary of `H`, framed by the trivial register, on a basis matrix. -/
private theorem frame_oracleQuery_branch_single (H : X → Y) (m : X × Y) (d : Unit) :
    ((oracleQuery H).frame Unit).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1 := by
  rw [SubInstrument.branch_frame_single, branch_oracleQuery_single, Matrix.single_kronecker_single,
    one_mul]

/-- The oracle runtime answers a call on a basis state `|x, y⟩` by moving it to
`|x, y + H x⟩`. -/
theorem xorRuntime_step_branch_single (H : X → Y) (m : X × Y) (d : (xorRuntime H).D) :
    ((xorRuntime H).step ()).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1 :=
  frame_oracleQuery_branch_single H m d

/-- Against a runtime that answers a call on a basis state `|x, y⟩` by moving it to
`|x, y + H x⟩` and leaves its private register alone, the program of a classical algorithm from
the trivial state reports the value of the algorithm against `H` with weight one. -/
theorem run_toQuantum_branch_of_basis [DecidableEq α] (H : X → Y)
    {R : QuantumRuntime (qromSpec X Y)}
    (hR : ∀ (m : X × Y) (d : R.D), (R.step ()).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1)
    (oa : OracleComp (X →ₒ Y) α) (d : R.D) (a : α) :
    (R.run₂ .instruments oa.toQuantum).branch a (Matrix.single ((), d) ((), d) 1) =
      if evalWithAnswerFn (QueryImpl.ofFn H) oa = a then Matrix.single ((), d) ((), d) 1
      else 0 := by
  induction oa using OracleComp.inductionOn with
  | pure b =>
    rw [OracleComp.toQuantum_pure, QuantumRuntime.run₂_pure, evalWithAnswerFn_pure]
    by_cases h : b = a
    · subst h
      simp
    · simp [h, SubInstrument.branch_pure_of_ne (Ne.symm h)]
  | query_bind t k ih =>
    rw [OracleComp.toQuantum_query_bind, QuantumRuntime.run₂_bind,
      SubInstrument.branch_bind_apply, tsum_eq_single (H t) fun y hy ↦ by
        simp [run_classicalQuery_branch_of_basis H hR, Ne.symm hy],
      run_classicalQuery_branch_of_basis H hR]
    simp only [↓reduceIte]
    rw [ih, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
    rfl

/-- Against a runtime that answers basis queries by `H`, leaves its private register alone and
starts it in a basis state, the program of a classical algorithm from the trivial state reports
the value of the algorithm against `H` with certainty. -/
theorem outcomeLaw_toQuantum_of_basis [MeasurableSpace α] (H : X → Y)
    {R : QuantumRuntime (qromSpec X Y)}
    (hR : ∀ (m : X × Y) (d : R.D), (R.step ()).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1)
    {d₀ : R.D} (hinit : R.init = SubState.basis d₀) (oa : OracleComp (X →ₒ Y) α) :
    R.outcomeLaw₂ .instruments oa.toQuantum (SubState.basis ()) =
      Measure.dirac (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  classical
  rw [QuantumRuntime.outcomeLaw₂, hinit, SubState.basis_prod_basis]
  ext t ht
  rw [SubInstrument.outcomeMeasure_apply _ _ ht,
    tsum_eq_single (evalWithAnswerFn (QueryImpl.ofFn H) oa) fun b hb ↦ by
      simp [SubState.matrix_basis, run_toQuantum_branch_of_basis H hR, Ne.symm hb],
    Measure.dirac_apply' _ ht]
  simp [SubState.matrix_basis, run_toQuantum_branch_of_basis H hR]

/-- Against the oracle unitary of `H`, the program of a classical algorithm reports the value of
the algorithm against `H` with certainty. -/
theorem outcomeLaw_xorRuntime_toQuantum [MeasurableSpace α] (H : X → Y)
    (oa : OracleComp (X →ₒ Y) α) :
    (xorRuntime H).outcomeLaw₂ .instruments oa.toQuantum (SubState.basis ()) =
      Measure.dirac (evalWithAnswerFn (QueryImpl.ofFn H) oa) :=
  outcomeLaw_toQuantum_of_basis H (xorRuntime_step_branch_single H) (xorRuntime_init H) oa

/-! ## Agreement with the classical random-oracle model -/

variable [SampleableType (X → Y)]

/-- **The quantum random-oracle model agrees with the classical one on classical algorithms.**
The law, in the quantum random-oracle model, of the program of a classical algorithm is the
output measure of the classical experiment that samples a function `H : X → Y` uniformly and
evaluates the algorithm with every query answered by `H`. No query bound is needed. -/
theorem qromLaw₂_toQuantum [MeasurableSpace α] (oa : OracleComp (X →ₒ Y) α) :
    qromLaw₂ .instruments oa.toQuantum (SubState.basis ()) =
      𝒟[do let H ← $ᵗ (X → Y); pure (evalWithAnswerFn (QueryImpl.ofFn H) oa)] := by
  let : MeasurableSpace (X → Y) := ⊤
  rw [evalDist_bind_of_discrete, qromLaw₂, sampledLaw₂_eq_bind]
  congr 1
  funext H
  rw [evalDist_pure]
  exact outcomeLaw_xorRuntime_toQuantum H oa

/-- The law, in the quantum random-oracle model, of the program of a classical algorithm is the
output measure of the algorithm under the lazily sampled, cached random oracle. -/
theorem qromLaw₂_toQuantum_eq_randomOracle [SampleableType Y] [MeasurableSpace α]
    (oa : OracleComp (X →ₒ Y) α) :
    qromLaw₂ .instruments oa.toQuantum (SubState.basis ()) =
      𝒟[(simulateQ randomOracle oa).run' ∅] := by
  rw [qromLaw₂_toQuantum, OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable]

end Quantum
