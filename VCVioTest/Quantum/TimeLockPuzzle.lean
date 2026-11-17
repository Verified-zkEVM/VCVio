/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.TimeLockPuzzle.QuantumClassical
public import Mathlib.Data.ZMod.Basic

/-!
# Quantum time-lock puzzle experiment regressions

A stateful counter oracle checks that preprocessing, honest generation, and online execution
compose on one persistent oracle register. Separate phase budgets and joint observations retain
hidden generator data without exposing it as an online argument or renormalizing lost mass.
-/

public section

open Quantum Quantum.TimeLockPuzzle Matrix MeasureTheory OracleComp OracleSpec
open scoped ENNReal Kronecker ComplexOrder

namespace VCVioTest.QuantumTimeLockPuzzle

/-- Trivial query registers make the private counter the only changing quantum system. -/
@[expose, reducible]
def counterSpec : QuantumOracleSpec := uBatchSpec Unit (fun _ ↦ QReg.of Unit)

/-- The register left by each width-one call. -/
@[expose, reducible]
def callReg : QReg := QReg.of ((Fin 1 → Unit) × Unit)

instance : Unique callReg := by
  change Unique ((Fin 1 → Unit) × Unit)
  exact { default := (fun _ : Fin 1 ↦ (), ()), uniq := by intro a; exact Subsingleton.elim _ _ }

instance : Unique (counterSpec.In ((), 1) × QReg.of Unit) := by
  change Unique ((Fin 1 → Unit) × Unit)
  exact inferInstanceAs (Unique callReg)

/-- A call charges its requested width to a five-element persistent private counter. -/
@[expose, reducible]
noncomputable def counterRuntime : QuantumRuntime counterSpec where
  D := QReg.of (ZMod 5)
  init := SubState.basis 0
  step p := SubInstrument.relabel
    { toFun := fun a ↦ (a.1, a.2 + p.2)
      invFun := fun a ↦ (a.1, a.2 - p.2)
      left_inv := by intro a; simp
      right_inv := by intro a; simp }

/-- One width-one call from any trivial public register. -/
@[expose, reducible]
noncomputable def oneCall {A : QReg} [Unique A] :
    QuantumComp LocalSig.instruments counterSpec (fun _ ↦ Unit) A :=
  QuantumComp.queryBind ((), 1) (QReg.of Unit) (Equiv.ofUnique _ _) fun _ ↦
    QuantumComp.pure ()

/-- Honest generation adds a call, publishes no information and retains a hidden marker. -/
@[expose, reducible]
noncomputable def counterPuzzle : Quantum.TimeLockPuzzle counterSpec Unit Unit where
  Secret := Bool
  gen := QuantumComp₂.queryBind ((), 1) (QReg.of Unit) (Equiv.ofUnique _ _) fun _ ↦
    (QComp.act (A := callReg) (B := QReg.of Unit)
      (SubInstrument.relabel (Equiv.ofUnique _ _))).bind fun _ ↦
      QuantumComp₂.pure ((), (), true)
  solve _ := QuantumComp₂.pure (some ())

/-- Preprocessing and online execution each make one call; retained register witnesses prevent
an unrelated register from being substituted between phases. -/
@[expose, reducible]
noncomputable def counterAdversary : TwoPhaseAdversary counterSpec Unit Unit where
  initialReg := QReg.of Unit
  initialState := SubState.basis ()
  State M := PLift (M = callReg)
  preprocess := QuantumComp.queryBind ((), 1) (QReg.of Unit) (Equiv.ofUnique _ _) fun _ ↦
    QuantumComp.pure ⟨rfl⟩
  online M state _ := by
    rcases state with ⟨h⟩
    subst M
    exact oneCall

/-- The syntactic phase clocks count preprocessing and online execution independently. -/
example : counterAdversary.IsQueryBound ⟨1, 1, 1, 1⟩ := by
  constructor
  · simp [counterAdversary]
  · intro M state puzzle
    rcases state with ⟨h⟩
    subst M
    simp [oneCall]

/-- Honest generation cannot consume the online round budget on behalf of the adversary. -/
example : ¬ counterAdversary.IsQueryBound ⟨1, 0, 1, 1⟩ := by
  intro h
  have hb := (h.2 callReg ⟨rfl⟩ ()).1
  simp [oneCall] at hb

/-- Preprocessing cannot borrow an unused online point budget. -/
example : ¬ counterAdversary.IsQueryBound ⟨0, 1, 2, 2⟩ := by
  intro h
  simpa [counterAdversary] using h.1

/-- The unique successful classical transcript includes the hidden generator marker. -/
@[expose, reducible]
noncomputable def counterTranscript : DelayTranscript counterPuzzle counterAdversary :=
  ⟨callReg, ⟨rfl⟩, (), (), true, callReg, ()⟩

/-- One physical call increments the private register and leaves the unique public basis fixed. -/
private theorem counter_queryStep {A : QReg} [Unique A]
    (e : A ≃ counterSpec.In ((), 1) × QReg.of Unit)
    (ρ : Matrix (A × counterRuntime.D) (A × counterRuntime.D) ℂ)
    (a b : callReg × counterRuntime.D) :
    ((counterRuntime.queryStep ((), 1) (QReg.of Unit) e).branch () ρ) a b =
      ρ (default, a.2 - 1) (default, b.2 - 1) := by
  rw [QuantumRuntime.queryStep_branch_apply]
  simp only [Nat.cast_one, DSubInstrument.branch_frame_apply,
    SubInstrument.relabel_branch_apply, Matrix.submatrix_apply, MatrixMap.amplify_apply,
    Matrix.submatrix_submatrix, Equiv.symm_mk, Equiv.coe_fn_mk, Function.comp_apply]
  congr 1 <;> exact Prod.ext (Subsingleton.elim _ _) rfl

/-- Honest generation shifts private memory without measuring the retained spectator. -/
private theorem counter_generation (M : QReg)
    (ρ : Matrix (M × counterRuntime.D) (M × counterRuntime.D) ℂ)
    (marker : Bool) (a b : M × counterRuntime.D) :
    ((generationInstrument counterRuntime counterPuzzle M).branch ((), (), marker) ρ) a b =
      if marker then ρ (a.1, a.2 - 1) (b.1, b.2 - 1) else 0 := by
  rw [generationInstrument, SubInstrument.branch_reindex_apply,
    DSubInstrument.branch_frame_apply]
  simp only [Matrix.submatrix_apply, Equiv.symm_symm]
  rw [MatrixMap.amplify_apply]
  simp only [QuantumRuntime.run₂_queryBind, QuantumRuntime.run₂_bind,
    QuantumRuntime.run₂_act, QuantumRuntime.run₂_pure, SubInstrument.bind_pure]
  rw [DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    DSubInstrument.branch_frame_apply]
  cases marker with
  | false => simp
  | true =>
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply, MatrixMap.amplify_apply,
      SubInstrument.relabel_branch_apply]
    simp only [Matrix.submatrix_apply]
    rw [counter_queryStep (A := QReg.of Unit)]
    rfl

/-- Generation preserves off-diagonal adversary/oracle correlations rather than tracing out
and rebuilding the spectator register. -/
example :
    (generationInstrument counterRuntime counterPuzzle (QReg.of Bool)).branch ((), (), true)
        (Matrix.single (false, (0 : ZMod 5)) (true, (1 : ZMod 5)) 1) =
      Matrix.single (false, (1 : ZMod 5)) (true, (2 : ZMod 5)) 1 := by
  ext ⟨a, da⟩ ⟨b, db⟩
  rw [counter_generation]
  norm_num [Matrix.single_apply, Prod.mk.injEq, eq_sub_iff_add_eq]
  simp only [eq_comm]

/-- All three phases share one private counter: one call in each phase finishes at three. -/
theorem counter_three_phases :
    ((delayInstrument counterRuntime counterPuzzle counterAdversary).branch counterTranscript
      (Matrix.single ((), (0 : ZMod 5)) ((), (0 : ZMod 5)) 1)) =
        Matrix.single ((default : callReg), (3 : ZMod 5))
          ((default : callReg), (3 : ZMod 5)) 1 := by
  have hfalse : (generationInstrument counterRuntime counterPuzzle callReg).branch
      ((), (), false) = 0 := by
    apply LinearMap.ext
    intro ρ
    ext a b
    exact counter_generation callReg ρ false a b
  unfold delayInstrument counterAdversary
  simp only [QuantumRuntime.run_queryBind, QuantumRuntime.run_pure,
    DSubInstrument.bind_assoc, DSubInstrument.ret_bind]
  rw [DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    DSubInstrument.branch_bind_apply_univ]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool,
    hfalse, LinearMap.comp_zero, add_zero, DSubInstrument.branch_bind_unit,
    counterTranscript, DSubInstrument.branch_ret_self, LinearMap.id_comp]
  ext a b
  simp only [LinearMap.comp_apply]
  rw [counter_queryStep (A := callReg), counter_generation,
    counter_queryStep (A := QReg.of Unit)]
  rcases a with ⟨a, da⟩
  rcases b with ⟨b, db⟩
  have ha : a = default := Subsingleton.elim _ _
  have hb : b = default := Subsingleton.elim _ _
  norm_num [Matrix.single_apply, Prod.mk.injEq, ha, hb, eq_sub_iff_add_eq]

/-- With no preprocessing, fixed hidden classical data is retained by the joint observer. -/
@[expose, reducible]
def hiddenGenerator : OracleComp (unifSpec + (Unit →ₒ ZMod 3).batch)
    (Unit × Fin 2 × Fin 2) := do
  let b ← liftM ((unifSpec + (Unit →ₒ ZMod 3).batch).query (.inl 1))
  pure ((), b, b)

/-- The online program sees a unit puzzle and can only make its fixed zero guess. -/
@[expose, reducible]
noncomputable def hiddenOnline (_ : Unit) :
    QuantumComp LocalSig.instruments (qromBatchSpec Unit (ZMod 3)) (fun _ ↦ Fin 2)
      (QReg.of Unit) := QuantumComp.pure 0

/-- Both the sampled key and its auxiliary copy are hidden from the online program. -/
@[expose, reducible]
noncomputable def hiddenPuzzle := ofClassicalGenerator hiddenGenerator
  (fun _ ↦ QuantumComp₂.pure none)

/-- A half-mass input has no postselection normalization. -/
@[expose, reducible]
noncomputable def halfInput : SubState Unit where
  matrix := Matrix.diagonal fun _ ↦ (1 / 2 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro u; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag]

private theorem evalDistMap_pure {spec : QuantumOracleSpec} {Out : Type} {A : QReg}
    (R : QuantumRuntime spec) (ρ : SubState A) (out : Out)
    (f : (Σ _B : QReg, Out) → Bool) :
    R.evalDistMap .instruments (QuantumComp.pure out) ρ f {true} =
      ENNReal.ofReal (ρ.prod R.init).matrix.trace.re *
        (if f ⟨A, out⟩ then 1 else 0) := by
  classical
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton true),
    tsum_eq_single ⟨A, out⟩]
  · simp [QuantumRuntime.matrix_jointPost, QuantumRuntime.run_pure,
      DSubInstrument.branch_ret_self]
    split <;> simp_all
  · intro p hp
    simp [QuantumRuntime.matrix_jointPost, QuantumRuntime.run_pure,
      DSubInstrument.branch_ret_of_ne _ hp]

private theorem hiddenGenerator_probability (H : Unit → ZMod 3) (z : Unit × Fin 2 × Fin 2) :
    Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' hiddenGenerator}[a = z] =
      if z.2.1 = z.2.2 then 1 / 2 else 0 := by
  simp only [hiddenGenerator, simulateQ_bind, simulateQ_query, simulateQ_pure]
  change Pr{let a ← (ProbComp.uniformFin 1)}[((), a, a) = z] = _
  rw [ProbComp.prEvent_uniformFin]
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [hu]
  rcases z with ⟨⟨⟩, b, c⟩
  fin_cases b <;> fin_cases c <;> norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- A hidden random bit and a half-mass input give recovery probability one quarter. -/
theorem hidden_bit_half_mass :
    delayAdvantage (parallelOracleRuntime (fun _ : Unit ↦ (2 : ZMod 3))) hiddenPuzzle
      (TwoPhaseAdversary.withoutPreprocessing (QReg.of Unit) halfInput hiddenOnline) = 1 / 4 := by
  let R := parallelOracleRuntime (fun _ : Unit ↦ (2 : ZMod 3))
  have ht : (halfInput.prod R.init).matrix.trace.re = 1 / 2 := by
    change (halfInput.prod (SubState.basis ())).matrix.trace.re = 1 / 2
    rw [SubState.trace_re_prod, SubState.trace_basis]
    norm_num [halfInput, Matrix.trace, Matrix.diag]
  rw [hiddenPuzzle, delayAdvantage_withoutPreprocessing_ofClassicalGenerator]
  simp only [hiddenOnline, evalDistMap_pure, hiddenGenerator_probability, tsum_fintype]
  change (∑ z : Unit × Fin 2 × Fin 2,
    (if z.2.1 = z.2.2 then (1 / 2 : ℝ≥0∞) else 0) *
      (ENNReal.ofReal (halfInput.prod R.init).matrix.trace.re *
        (if decide (0 = z.2.1) then 1 else 0))) = 1 / 4
  rw [ht]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, ENNReal.ofReal_div_of_pos,
    div_eq_mul_inv, ← ENNReal.mul_inv]

/-- The observer retains the exact key/secret correlation: resampling either hidden copy
independently would halve this event's probability. -/
theorem hidden_key_secret_joint :
    delayLawWith (parallelOracleRuntime (fun _ : Unit ↦ (2 : ZMod 3))) hiddenPuzzle
      (TwoPhaseAdversary.withoutPreprocessing (QReg.of Unit) halfInput hiddenOnline)
      (fun t ↦ decide (t.key = t.secret)) {true} = 1 / 2 := by
  let R := parallelOracleRuntime (fun _ : Unit ↦ (2 : ZMod 3))
  have ht : (halfInput.prod R.init).matrix.trace.re = 1 / 2 := by
    change (halfInput.prod (SubState.basis ())).matrix.trace.re = 1 / 2
    rw [SubState.trace_re_prod, SubState.trace_basis]
    norm_num [halfInput, Matrix.trace, Matrix.diag]
  unfold hiddenPuzzle
  rw [delayLawWith_withoutPreprocessing_ofClassicalGenerator
    (f := fun z _ ↦ decide (z.2.1 = z.2.2))]
  rw [Measure.sum_apply _ (MeasurableSet.singleton true)]
  simp only [Measure.smul_apply, smul_eq_mul, hiddenOnline, evalDistMap_pure,
    hiddenGenerator_probability, tsum_fintype]
  change (∑ z : Unit × Fin 2 × Fin 2,
    (if z.2.1 = z.2.2 then (1 / 2 : ℝ≥0∞) else 0) *
      (ENNReal.ofReal (halfInput.prod R.init).matrix.trace.re *
        (if decide (z.2.1 = z.2.2) then 1 else 0))) = 1 / 2
  rw [ht]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, ENNReal.ofReal_div_of_pos,
    div_eq_mul_inv, ← ENNReal.mul_inv]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

end VCVioTest.QuantumTimeLockPuzzle
