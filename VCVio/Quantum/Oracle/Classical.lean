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

## Classical calls from inside an experiment

The challengers of ePrint 2025/2166, §7 (p. 51) make classical calls while holding the
adversary's register. Over any signature and any held register `B`:

* `Quantum.QComp.callBasis p B a read`: prepare the basis input `a` of port `p` beside `B`, call
  `p`, measure and discard the port register, and return `read` of the reading and the result.
  It is lossless and makes one call of `p` (`Quantum.QComp.isQueryBound_callBasis_single`).
* `OracleComp.toQuantumAt oa q`: the classical algorithm `oa` with each query answered by the
  program `q t`; `OracleComp.toQuantum` is the case `B = Unit`, `q = Quantum.classicalImpl`
  (`OracleComp.toQuantum_eq_toQuantumAt`), and `n` queries within budget `b` each give budget
  `n • b` (`OracleComp.isQueryBound_toQuantumAt`).
* `Quantum.QComp.allIn W f`: the conjunction of the checks `f i`, `i ∈ W`, without
  short-circuit, within the sum of their budgets (`Quantum.QComp.isQueryBound_allIn`).
* `Quantum.QuantumComp₂.forgetReg x`: a fixed-register program read as a general program, with
  the same observed laws (`Quantum.QuantumRuntime.outcomeLawWith_forgetReg`).
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

/-! ## Classical calls from inside an experiment

The challengers of the security experiments of ePrint 2025/2166 (§7, p. 51) make classical
calls on a chosen port while the adversary's final register `B` is held, and run classical
verifiers whose oracle queries are such calls. The constructions below work over any signature
and any register `B`; `Quantum.classicalQuery` and `OracleComp.toQuantum` are the case of the
random-oracle signature on the trivial register (`OracleComp.toQuantum_eq_toQuantumAt`). -/

universe u v u₁ v₁ w

namespace Quantum

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {β : Type w}

/-- The preparation of a basis call: on `B`, adjoin the port register of `p` in the basis state
`|a⟩`. It relabels `B` as `Unit × B` and prepares `|a⟩` on the factor `Unit`. -/
@[expose]
noncomputable def callBasisPrep (p : spec.Port) (B : QReg) (a : spec.In p) :
    SubInstrument B (spec.In p × B) PUnit.{w + 1} :=
  (SubInstrument.relabel (Equiv.uniqueProd B Unit).symm).bind fun _ ↦
    (SubInstrument.classical (fun _ : Unit ↦ a) fun _ ↦ PUnit.unit).frame B

/-- The read-out of a basis call with result `r`: measure the port register in the computational
basis, report `read o r` on reading `o`, and discard the port register. -/
@[expose]
noncomputable def callBasisMeasure (p : spec.Port) (B : QReg)
    (read : spec.Out p → spec.Result p → β) (r : spec.Result p) :
    SubInstrument (spec.Out p × B) B β :=
  ((SubInstrument.classical (fun _ : spec.Out p ↦ ()) fun o ↦ read o r).frame B).bind fun c ↦
    (SubInstrument.relabel (Equiv.uniqueProd B Unit)).bind fun _ ↦ SubInstrument.pure c

/-- **A classical call beside a held register.** Prepare the basis input `a` of port `p` beside
`B`, call `p`, measure the port register in the computational basis, discard it, and return
`read o r` for the reading `o` and the classical result `r` of the call. It is built from the
same pieces as `Quantum.classicalQuery`: relabellings, a classical preparation framed by `B`,
and `Quantum.QuantumComp₂.query p B (Equiv.refl _)`. -/
@[expose]
noncomputable def callBasis (p : spec.Port) (B : QReg) (a : spec.In p)
    (read : spec.Out p → spec.Result p → β) : QComp spec B B β :=
  (QComp.act (B := QReg.of (spec.In p × B)) (callBasisPrep p B a)).bind fun _ ↦
    (QuantumComp₂.query (L := LocalSig.instruments.{w}) p B (Equiv.refl _)).bind fun r ↦
      QComp.act (A := QReg.of (spec.Out p × B)) (callBasisMeasure p B read r)

/-- The preparation of a basis call is lossless. -/
theorem lossless_callBasisPrep (p : spec.Port) (B : QReg) (a : spec.In p) :
    (callBasisPrep.{u₁, v₁, w} p B a).Lossless :=
  (SubInstrument.lossless_relabel _).bind fun _ ↦
    (SubInstrument.lossless_classical _ _).frame B

/-- The read-out of a basis call is lossless. -/
theorem lossless_callBasisMeasure (p : spec.Port) (B : QReg)
    (read : spec.Out p → spec.Result p → β) (r : spec.Result p) :
    (callBasisMeasure p B read r).Lossless :=
  ((SubInstrument.lossless_classical _ _).frame B).bind fun _ ↦
    (SubInstrument.lossless_relabel _).bind fun _ ↦ SubInstrument.lossless_pure _

/-- A basis call is a lossless program. -/
theorem lossless_callBasis (p : spec.Port) (B : QReg) (a : spec.In p)
    (read : spec.Out p → spec.Result p → β) :
    (callBasis p B a read).Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (lossless_callBasisPrep p B a)) fun _ ↦
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_query _ _ _) fun r ↦
      QComp.lossless_act (lossless_callBasisMeasure p B read r)

/-- A basis call on port `p` is within every budget that allows a call of `p`. -/
theorem isQueryBound_callBasis {p : spec.Port} {b : spec.Port → ℕ} (hb : 0 < b p) (B : QReg)
    (a : spec.In p) (read : spec.Out p → spec.Result p → β) :
    (callBasis p B a read).IsQueryBound b := by
  rw [callBasis, QComp.isQueryBound_act_bind_iff]
  intro _
  refine (QuantumComp₂.isQueryBound_bind (b₁ := b) (b₂ := 0) ?_
    fun _ ↦ QComp.isQueryBound_act _ _).mono (add_zero _).le
  exact (QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr hb

/-- A basis call on port `p` makes one call of `p` and no other call. -/
theorem isQueryBound_callBasis_single [DecidableEq spec.Port] (p : spec.Port) (B : QReg)
    (a : spec.In p) (read : spec.Out p → spec.Result p → β) :
    (callBasis p B a read).IsQueryBound (Pi.single p 1) :=
  isQueryBound_callBasis (by simp) B a read

/-- The run of a basis call: the framed preparation, the call, and the framed read-out. -/
theorem run₂_callBasis (R : QuantumRuntime spec) (p : spec.Port) (B : QReg) (a : spec.In p)
    (read : spec.Out p → spec.Result p → β) :
    R.run₂ .instruments (callBasis p B a read) =
      ((callBasisPrep.{u₁, v₁, w} p B a).frame R.D).bind fun _ ↦
        (R.queryStep (A := QReg.of (spec.In p × B)) p B (Equiv.refl _)).bind fun r ↦
          ((callBasisMeasure p B read r).frame R.D).bind fun c ↦ SubInstrument.pure c := by
  simp only [callBasis, QuantumRuntime.run₂_act_bind, QuantumRuntime.run₂_query_bind,
    QuantumRuntime.run₂_act]

/-- **Conjunction of classical checks.** Run `f i` for every `i ∈ W` in increasing order of `i`,
without short-circuit, so that the calls of every check happen, and return the conjunction of
their results. This is `⋀_{i ∈ W}` of the experiments of ePrint 2025/2166 (§7, p. 51). -/
@[expose]
noncomputable def allIn {k : ℕ} {B : QReg} (W : Finset (Fin k))
    (f : Fin k → QComp spec B B Bool) : QComp spec B B Bool :=
  (List.finRange k).foldlM (fun acc i ↦ if i ∈ W then (acc && ·) <$> f i else pure acc) true

section allIn

variable {k : ℕ} {B : QReg} (W : Finset (Fin k)) (f : Fin k → QComp spec B B Bool)

/-- The fold behind `allIn`, along any list, is within the sum of the budgets of the checks it
runs. -/
private theorem isQueryBound_foldlM {b : Fin k → spec.Port → ℕ}
    (hf : ∀ i ∈ W, (f i).IsQueryBound (b i)) (l : List (Fin k)) (acc : Bool) :
    (l.foldlM (fun acc i ↦ if i ∈ W then (acc && ·) <$> f i else pure acc) acc).IsQueryBound
      ((l.filter (· ∈ W)).map b).sum := by
  induction l generalizing acc with
  | nil => exact QuantumComp₂.isQueryBound_pure acc _
  | cons i l ih =>
    rw [List.foldlM_cons, List.filter_cons]
    by_cases hi : i ∈ W
    · simp only [hi, ↓reduceIte, decide_true, List.map_cons, List.sum_cons]
      refine (QuantumComp₂.isQueryBound_bind (b₁ := b i + 0)
        (QuantumComp₂.isQueryBound_bind (hf i hi) fun _ ↦ QuantumComp₂.isQueryBound_pure _ _)
        fun s ↦ ih s).mono (by rw [add_zero])
    · simp only [hi, ↓reduceIte, decide_false, Bool.false_eq_true]
      exact ih acc

/-- The fold behind `allIn` is lossless when the checks it runs are. -/
private theorem lossless_foldlM (hf : ∀ i ∈ W, (f i).Lossless .instruments) (l : List (Fin k))
    (acc : Bool) :
    (l.foldlM (fun acc i ↦ if i ∈ W then (acc && ·) <$> f i else pure acc) acc).Lossless
      .instruments := by
  induction l generalizing acc with
  | nil => exact QuantumComp₂.lossless_pure acc
  | cons i l ih =>
    rw [List.foldlM_cons]
    by_cases hi : i ∈ W
    · simp only [hi, ↓reduceIte]
      exact QuantumComp₂.lossless_bind (QuantumComp₂.lossless_bind (hf i hi) fun _ ↦
        QuantumComp₂.lossless_pure _) ih
    · simp only [hi, ↓reduceIte]
      exact ih acc

/-- The conjunction of checks is within the sum, over `W`, of the budgets of the checks. -/
theorem isQueryBound_allIn {b : Fin k → spec.Port → ℕ} (hf : ∀ i ∈ W, (f i).IsQueryBound (b i)) :
    (allIn W f).IsQueryBound (∑ i ∈ W, b i) := by
  have h := isQueryBound_foldlM W f hf (List.finRange k) true
  rw [← List.sum_toFinset _ ((List.nodup_finRange k).filter _), List.toFinset_filter,
    List.toFinset_finRange] at h
  simp only [decide_eq_true_eq] at h
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at h
  exact h

/-- The conjunction of checks within a common budget `b` is within `#W • b`. -/
theorem isQueryBound_allIn_const {b : spec.Port → ℕ} (hf : ∀ i ∈ W, (f i).IsQueryBound b) :
    (allIn W f).IsQueryBound (W.card • b) := by
  have h := isQueryBound_allIn W f (b := fun _ ↦ b) hf
  rwa [Finset.sum_const] at h

/-- The conjunction of lossless checks is lossless. -/
theorem lossless_allIn (hf : ∀ i ∈ W, (f i).Lossless .instruments) :
    (allIn W f).Lossless .instruments :=
  lossless_foldlM W f hf _ true

end allIn

end QComp

namespace QuantumComp₂

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {A B : QReg} {α : Type w}

/-- Read a fixed-register program as a general program whose leaves carry its value on any
register: the leaf `⟨B, rfl, a⟩` becomes `⟨B, a⟩`. This lets a fixed-register challenger follow
a general adversary whose final register depends on its outcome. -/
@[expose]
def forgetReg (x : QuantumComp₂ L spec A B α) : QuantumComp L spec (fun _ ↦ α) A :=
  QuantumComp.bind x fun _ p ↦ QuantumComp.pure p.2

/-- Forgetting the register keeps losslessness. -/
theorem lossless_forgetReg {I : L.Interp} {x : QuantumComp₂ L spec A B α}
    (hx : x.Lossless I) : x.forgetReg.Lossless I :=
  QuantumComp.Lossless.bind hx fun _ _ ↦ trivial

/-- Forgetting the register keeps every query budget. -/
theorem isQueryBound_forgetReg {x : QuantumComp₂ L spec A B α} {b : spec.Port → ℕ}
    (hx : x.IsQueryBound b) : x.forgetReg.IsQueryBound b :=
  (hx.bind fun _ _ ↦ QuantumComp.isQueryBound_pure _ 0).mono (add_zero b).le

end QuantumComp₂

namespace QuantumRuntime

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {A B : QReg} {α : Type w}
  (R : QuantumRuntime spec) (I : L.Interp)

/-- The run of a program with its register forgotten is the run of the program, reindexed along
`⟨u, ⟨h, a⟩⟩ ↦ ⟨u, a⟩`. -/
theorem run_forgetReg (x : QuantumComp₂ L spec A B α) :
    R.run I x.forgetReg =
      (R.run I x).map (C := fun q : Σ _ : QReg, α ↦ q.1 × R.D)
        fun p : Σ u, QuantumComp₂.Leaf B α u ↦ ⟨p.1, p.2.2⟩ := by
  exact run_bind R I x _

/-- The joint post-state of a program with its register forgotten, at the leaf `⟨u, a⟩` read off
the leaf `⟨u, ⟨h, a⟩⟩` of the program, is the joint post-state of the program there. -/
theorem matrix_jointPost_forgetReg (x : QuantumComp₂ L spec A B α) (ρ : SubState A)
    (p : Σ u, QuantumComp₂.Leaf B α u) :
    (R.jointPost I x.forgetReg ρ ⟨p.1, p.2.2⟩).matrix = (R.jointPost I x ρ p).matrix := by
  refine (matrix_jointPost R I _ ρ _).trans (Eq.trans ?_ (matrix_jointPost R I x ρ p).symm)
  rw [run_forgetReg, DSubInstrument.map_eq_bind_ret,
    DSubInstrument.branch_bind_apply, tsum_eq_single p fun p' hp' ↦ ?_]
  · rw [DSubInstrument.branch_ret_self, LinearMap.id_apply]
  · obtain ⟨u, h, a⟩ := p
    obtain ⟨u', h', a'⟩ := p'
    subst h h'
    have ha : a ≠ a' := fun ha ↦ hp' (by rw [ha])
    rw [DSubInstrument.branch_ret_of_ne _ fun he ↦ ha (eq_of_heq (Sigma.mk.inj he).2),
      LinearMap.zero_apply]

/-- The joint post-state of a program with its register forgotten vanishes at a leaf that no
leaf of the program reads to. -/
theorem matrix_jointPost_forgetReg_of_notMem (x : QuantumComp₂ L spec A B α) (ρ : SubState A)
    {q : Σ _ : QReg, α} (hq : q ∉ Set.range fun p : Σ u, QuantumComp₂.Leaf B α u ↦
      (⟨p.1, p.2.2⟩ : Σ _ : QReg, α)) :
    (R.jointPost I x.forgetReg ρ q).matrix = 0 := by
  rw [matrix_jointPost, run_forgetReg, DSubInstrument.map_eq_bind_ret,
    DSubInstrument.branch_bind_apply]
  refine (tsum_congr fun p ↦ ?_).trans tsum_zero
  rw [DSubInstrument.branch_ret_of_ne _ fun he ↦ hq ⟨p, he.symm⟩, LinearMap.zero_apply]

/-- **Forgetting the register changes no observed law.** Observing `f` on the leaves of the
program with its register forgotten is observing `f ⟨u, a⟩` on the leaves `⟨u, ⟨h, a⟩⟩` of the
program. -/
theorem outcomeLawWith_forgetReg {γ : Type*} [MeasurableSpace γ] (x : QuantumComp₂ L spec A B α)
    (ρ : SubState A) (f : (Σ _ : QReg, α) → γ) :
    R.outcomeLawWith I x.forgetReg ρ f = R.outcomeLawWith I x ρ fun p ↦ f ⟨p.1, p.2.2⟩ := by
  ext s hs
  refine (outcomeLawWith_apply R I _ ρ f hs).trans
    (Eq.trans ?_ (outcomeLawWith_apply R I x ρ (fun p ↦ f ⟨p.1, p.2.2⟩) hs).symm)
  have hg : Function.Injective fun p : Σ u, QuantumComp₂.Leaf B α u ↦
      (⟨p.1, p.2.2⟩ : Σ _ : QReg, α) := by
    rintro ⟨u, h, a⟩ ⟨u', h', a'⟩ he
    subst h h'
    cases eq_of_heq (Sigma.mk.inj he).2
    rfl
  refine (hg.tsum_eq fun q hq ↦ ?_).symm.trans (tsum_congr fun p ↦ ?_)
  · by_contra hq'
    refine hq ?_
    beta_reduce
    rw [matrix_jointPost_forgetReg_of_notMem R I x ρ hq', Matrix.trace_zero, Complex.zero_re,
      ENNReal.ofReal_zero, zero_mul]
  · simp only [matrix_jointPost_forgetReg]

end QuantumRuntime

end Quantum

namespace OracleComp

open Quantum

section toQuantumAt

variable {ι : Type u} {ospec : OracleSpec.{u, v} ι} {α : Type v}
  {spec : QuantumOracleSpec.{u₁, v₁}} {B : QReg}

/-- **A classical algorithm run from inside an experiment.** Run the classical oracle algorithm
`oa` as a quantum program on the held register `B`, answering each query `t` with the program
`q t`, for instance a basis call `Quantum.QComp.callBasis`. -/
@[expose]
noncomputable def toQuantumAt (oa : OracleComp ospec α) (q : QueryImpl ospec (QComp spec B B)) :
    QComp spec B B α :=
  simulateQ q oa

variable (q : QueryImpl ospec (QComp spec B B))

/-- A computation that returns at once runs to the program that returns at once. -/
@[simp]
theorem toQuantumAt_pure (a : α) :
    (pure a : OracleComp ospec α).toQuantumAt q = QuantumComp₂.pure a :=
  rfl

/-- A query followed by a continuation runs to the answer program followed by the programs of
the continuation. -/
@[simp]
theorem toQuantumAt_query_bind (t : ospec.Domain) (k : ospec.Range t → OracleComp ospec α) :
    (liftM (ospec.query t) >>= k : OracleComp ospec α).toQuantumAt q =
      (q t).bind fun y ↦ (k y).toQuantumAt q := by
  rw [toQuantumAt, simulateQ_bind, simulateQ_spec_query]
  rfl

/-- A classical algorithm whose queries are answered by lossless programs runs to a lossless
program. -/
theorem lossless_toQuantumAt {q : QueryImpl ospec (QComp spec B B)}
    (hq : ∀ t, (q t).Lossless .instruments) (oa : OracleComp ospec α) :
    (oa.toQuantumAt q).Lossless .instruments := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact QuantumComp₂.lossless_pure a
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    exact QuantumComp₂.lossless_bind (hq t) ih

end toQuantumAt

/-- A classical algorithm making at most `n` queries, each answered by a program within the
budget `b`, runs to a program within the budget `n • b`. -/
theorem isQueryBound_toQuantumAt {ι : Type u} {ospec : OracleSpec.{u, u} ι} {α : Type u}
    {spec : QuantumOracleSpec.{u₁, v₁}} {B : QReg} {q : QueryImpl ospec (QComp spec B B)}
    {b : spec.Port → ℕ} (hq : ∀ t, (q t).IsQueryBound b) {oa : OracleComp ospec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : (oa.toQuantumAt q).IsQueryBound (n • b) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact QuantumComp₂.isQueryBound_pure a _
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    refine (QuantumComp₂.isQueryBound_bind (hq t) fun y ↦ ih y (h.2 y)).mono fun i ↦ ?_
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero h.1.ne'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel]
    rw [Nat.succ_mul, add_comm]

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The embedding of classical algorithms on the trivial register is the case `B = Unit` with
queries answered by `Quantum.classicalQuery`. -/
theorem toQuantum_eq_toQuantumAt (oa : OracleComp (X →ₒ Y) α) :
    oa.toQuantum = oa.toQuantumAt classicalImpl :=
  rfl

end OracleComp
