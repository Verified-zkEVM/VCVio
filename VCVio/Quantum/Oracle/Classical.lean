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

A classical algorithm with access to a function oracle `X → Y` is an `OracleComp (X →ₒ Y) α`: its
only source of randomness is the oracle, so it is deterministic once the oracle's answers are
fixed. `OracleComp.toQuantum oa` runs it as a quantum program over `Quantum.qromSpec X Y` on the
trivial register. It is built with VCVio's handler `simulateQ`: each query `t` becomes
`Quantum.classicalQuery t`, which prepares `|t, 0⟩`, calls the oracle, measures the register in the
computational basis, returns the response and discards the register. The program is adaptive
exactly as `oa` is, and needs no query bound, workspace or default value.

Against `Quantum.additiveOracleRuntime H`, the measured response is `H t`, so the program returns
the value of `oa` when every query is answered by `H`. Averaging over `H` gives the distribution of
`oa` under VCVio's lazily sampled random oracle `randomOracle`. So the quantum random-oracle model,
restricted to classical algorithms, is the classical random-oracle model.

## Main results

* `OracleComp.lossless_toQuantum` and `OracleComp.isQueryBound_toQuantum`: the program is lossless,
  and an algorithm making at most `n` queries gives a program with budget `n`.
* `Quantum.evalDist_toQuantum_of_basis`: against any runtime that answers a call on a basis state
  `|x, y⟩` with `|x, y + H x⟩`, leaves its private register alone and starts it in a basis state,
  the program returns `evalWithAnswerFn (QueryImpl.ofFn H) oa` with certainty.
* `Quantum.evalDist_additiveOracleRuntime_toQuantum`: the case of the oracle of `H`.
* `Quantum.qromEvalDist₂_toQuantum`: the distribution in the QROM is the distribution of the
  classical experiment that samples `H` uniformly and runs `oa` against it.
* `Quantum.qromEvalDist₂_toQuantum_eq_randomOracle`: this is the distribution of `oa` under
  `randomOracle`.

## Not covered

* **Private randomness.** Algorithms that also sample coins, `OracleComp (unifSpec + (X →ₒ Y)) α`,
  are not embedded.
* **Result universes.** The result type is `α : Type`. Allowing any universe needs universe
  generalizations in the classical layer (`simulateQ`, `evalWithAnswerFn`, `IsTotalQueryBound`,
  `randomOracle`) first.
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
      (DSubInstrument.classical (B := fun _ ↦ X × Y) (fun _ : Unit ↦ ())
        (fun _ ↦ (t, (0 : Y))))).bind fun _ ↦
    (QuantumComp₂.query (L := LocalSig.instruments) (spec := qromSpec X Y) () (QReg.of Unit)
        (Equiv.prodPUnit (X × Y)).symm).bind fun _ ↦
      QComp.act (A := QReg.of ((X × Y) × Unit))
        (DSubInstrument.classical (B := fun _ ↦ Unit) (fun m : (X × Y) × Unit ↦ m.1.2) (fun _ ↦ ()))

/-- The implementation of the classical oracle `X →ₒ Y` by quantum programs on the trivial
register: query `t` is answered by `Quantum.classicalQuery t`. -/
@[expose]
noncomputable def classicalImpl :
    QueryImpl (X →ₒ Y) (QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit)) :=
  fun t ↦ classicalQuery t

/-- A classical query is a lossless program. -/
theorem lossless_classicalQuery (t : X) :
    (classicalQuery (Y := Y) t).Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (DSubInstrument.lossless_classical _ _)) fun _ ↦
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_query _ _ _) fun _ ↦
      QComp.lossless_act (DSubInstrument.lossless_classical _ _)

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

/-- The classical algorithm `oa`, run as a quantum program on the trivial register. It is
`simulateQ` with each query `t` answered by `Quantum.classicalQuery t`: prepare `|t, 0⟩`, call the
oracle, measure the response in the computational basis, return it and discard the register. The
continuations of `oa`, adaptive queries included, are kept as they are.

Against `additiveOracleRuntime H` the program returns the value of `oa` against `H`, and its
distribution in the QROM is the distribution of `oa` under `randomOracle`
(`Quantum.qromEvalDist₂_toQuantum_eq_randomOracle`), with no query-bound hypothesis. The algorithm
uses no randomness besides the oracle, and its result type lies in `Type`. -/
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
  rwa [DSubInstrument.matrix_post, SubState.matrix_basis, SubState.matrix_basis] at h

/-- Against a runtime that answers a call on a basis state `|x, y⟩` by moving it to
`|x, y + H x⟩` and leaves its private register alone, a classical query `t` from the trivial
state reports `H t` with weight one and returns to the trivial state. -/
theorem run_classicalQuery_branch_of_basis (H : X → Y) {R : QuantumRuntime (qromSpec X Y)}
    (hR : ∀ (m : X × Y) (d : R.D), (R.step ()).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1)
    (t : X) (d : R.D) (y : Y) :
    (R.run₂ .instruments (classicalQuery t)).branch y (Matrix.single ((), d) ((), d) 1) =
      if H t = y then Matrix.single ((), d) ((), d) 1 else 0 := by
  rw [classicalQuery, QuantumRuntime.run₂_act_bind, DSubInstrument.branch_bind_unit,
    LinearMap.comp_apply, DSubInstrument.branch_frame_single, DSubInstrument.branch_classical_basis]
  simp only [↓reduceDIte, cast_eq]
  rw [Matrix.single_kronecker_single, one_mul, QuantumRuntime.run₂_query_bind,
    DSubInstrument.branch_bind_unit, LinearMap.comp_apply, QuantumRuntime.queryStep_branch_apply,
    SubInstrument.branch_relabel, SubInstrument.branch_relabel, conj_basisMatrix_equiv_single]
  simp only [QuantumRuntime.queryEquivIn_apply, Equiv.prodPUnit_symm_apply]
  rw [DSubInstrument.branch_frame_single, hR, Matrix.single_kronecker_single, one_mul,
    conj_basisMatrix_equiv_single, QuantumRuntime.run₂_act, SubInstrument.bind_pure]
  simp only [QuantumRuntime.queryEquivOut_apply]
  rw [DSubInstrument.branch_frame_single, DSubInstrument.branch_classical_basis]
  by_cases h : H t = y <;> simp [h, Matrix.single_kronecker_single]

/-- The oracle unitary of `H`, framed by the trivial register, on a basis matrix. -/
private theorem frame_oracleQuery_branch_single (H : X → Y) (m : X × Y) (d : Unit) :
    ((oracleQuery H).frame Unit).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1 := by
  rw [DSubInstrument.branch_frame_single, branch_oracleQuery_single, Matrix.single_kronecker_single,
    one_mul]

/-- The oracle runtime answers a call on a basis state `|x, y⟩` by moving it to
`|x, y + H x⟩`. -/
theorem additiveOracleRuntime_step_branch_single (H : X → Y) (m : X × Y) (d :
  (additiveOracleRuntime H).D) :
    ((additiveOracleRuntime H).step ()).branch () (Matrix.single (m, d) (m, d) 1) =
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
      DSubInstrument.branch_bind_apply, tsum_eq_single (H t) fun y hy ↦ by
        simp [run_classicalQuery_branch_of_basis H hR, Ne.symm hy],
      run_classicalQuery_branch_of_basis H hR]
    simp only [↓reduceIte]
    rw [ih, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
    rfl

/-- Against a runtime that answers basis queries by `H`, leaves its private register alone and
starts it in a basis state, the program of a classical algorithm from the trivial state reports
the value of the algorithm against `H` with certainty. -/
theorem evalDist_toQuantum_of_basis [MeasurableSpace α] (H : X → Y)
    {R : QuantumRuntime (qromSpec X Y)}
    (hR : ∀ (m : X × Y) (d : R.D), (R.step ()).branch () (Matrix.single (m, d) (m, d) 1) =
      Matrix.single ((m.1, m.2 + H m.1), d) ((m.1, m.2 + H m.1), d) 1)
    {d₀ : R.D} (hinit : R.init = SubState.basis d₀) (oa : OracleComp (X →ₒ Y) α) :
    R.evalDist₂ .instruments oa.toQuantum (SubState.basis ()) =
      Measure.dirac (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  classical
  rw [QuantumRuntime.evalDist₂, hinit, SubState.basis_prod_basis]
  ext t ht
  rw [DSubInstrument.outcomeMeasure_apply _ _ ht,
    tsum_eq_single (evalWithAnswerFn (QueryImpl.ofFn H) oa) fun b hb ↦ by
      simp [SubState.matrix_basis, run_toQuantum_branch_of_basis H hR, Ne.symm hb],
    Measure.dirac_apply' _ ht]
  simp [SubState.matrix_basis, run_toQuantum_branch_of_basis H hR]

/-- Against the oracle unitary of `H`, the program of a classical algorithm reports the value of
the algorithm against `H` with certainty. -/
theorem evalDist_additiveOracleRuntime_toQuantum [MeasurableSpace α] (H : X → Y)
    (oa : OracleComp (X →ₒ Y) α) :
    (additiveOracleRuntime H).evalDist₂ .instruments oa.toQuantum (SubState.basis ()) =
      Measure.dirac (evalWithAnswerFn (QueryImpl.ofFn H) oa) :=
  evalDist_toQuantum_of_basis H (additiveOracleRuntime_step_branch_single H)
    (additiveOracleRuntime_init H) oa

/-! ## Agreement with the classical random-oracle model -/

variable [SampleableType (X → Y)]

/-- **The quantum random-oracle model agrees with the classical one on classical algorithms.**
The distribution, in the quantum random-oracle model, of the program of a classical algorithm is the
output measure of the classical experiment that samples a function `H : X → Y` uniformly and
evaluates the algorithm with every query answered by `H`. No query bound is needed. -/
theorem qromEvalDist₂_toQuantum [MeasurableSpace α] (oa : OracleComp (X →ₒ Y) α) :
    qromEvalDist₂ .instruments oa.toQuantum (SubState.basis ()) =
      𝒟[do let H ← $ᵗ (X → Y); pure (evalWithAnswerFn (QueryImpl.ofFn H) oa)] := by
  let : MeasurableSpace (X → Y) := ⊤
  rw [evalDist_bind_of_discrete, qromEvalDist₂, sampledEvalDist₂_eq_bind_uniformSample]
  congr 1
  funext H
  rw [evalDist_pure]
  exact evalDist_additiveOracleRuntime_toQuantum H oa

/-- The distribution, in the quantum random-oracle model, of the program of a classical algorithm is
the output measure of the algorithm under the lazily sampled, cached random oracle. -/
theorem qromEvalDist₂_toQuantum_eq_randomOracle [SampleableType Y] [MeasurableSpace α]
    (oa : OracleComp (X →ₒ Y) α) :
    qromEvalDist₂ .instruments oa.toQuantum (SubState.basis ()) =
      𝒟[(simulateQ randomOracle oa).run' ∅] := by
  rw [qromEvalDist₂_toQuantum,
    OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable]

end Quantum
