/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import QuantumFoundations.DSubInstrument
public import QuantumFoundations.SubInstrument
public import VCVio.Quantum.Oracle.Classical
public import VCVio.Quantum.Oracle.Emulated
import VCVio.OracleComp.EvalDist.Sum

/-!
# Coins, sequencing and basis calls for experiments

Helpers for running randomized classical algorithms from inside a quantum experiment, as the
challengers of the security experiments of ePrint 2025/2166 (§7, p. 51) do.

* **Coins.** QuantumFoundations’ `Quantum.SubInstrument.uniform Ω A` draws a uniform outcome
  in `Ω` and leaves the register `A` untouched; each branch is the map `ρ ↦ ρ / |Ω|`. It is the
  measurement of a fresh uniform register, and answers the queries of `unifSpec` through
  `Quantum.QComp.coinImpl`, so a `ProbComp` or an `OracleComp (unifSpec + _)` runs inside an
  experiment by `OracleComp.toQuantumAt`. For a `ProbComp`, every branch is its classical
  output probability times the identity (`Quantum.branch_run₂_toQuantumAt_coinImpl`), and the
  outcome measure is its classical law scaled by the input trace
  (`Quantum.outcomeMeasure_run₂_toQuantumAt_coinImpl`).
* **Sequencing.** `Quantum.QComp.pi f` runs the programs `f 0, …, f (k - 1)` in order on a held
  register and returns the dependent tuple of their results.
* **Lifting outcomes.** `Quantum.QuantumComp.liftInstruments` reads a program over instruments
  with outcomes in `Type v` as one over instruments with outcomes in `Type (max v w)`, by lifting
  the outcomes of every local operation with `ULift`; it runs as the original program
  (`Quantum.QuantumComp.run_liftInstruments`). It sequences a challenger with small outcomes
  after an adversary in a larger universe.
* **Basis calls against an emulated oracle.** The branch of `Quantum.QComp.callBasis` at a
  reading is the sum, over the port outputs giving that reading, of the Kraus map of
  `1_B ⊗ ⟨o|U_p|a⟩` (`Quantum.EmulatedOracle.branch_run₂_callBasis`).

## Main definitions

* `Quantum.QComp.coinImpl`, `Quantum.QComp.pi`,
  `Quantum.LocalSig.InstrumentOp.lift`, `Quantum.QuantumComp.liftInstruments`,
  `Quantum.EmulatedOracle.block`.

## Main results

* `Quantum.QComp.lossless_pi`, `Quantum.QComp.isQueryBound_pi`.
* `Quantum.branch_run₂_toQuantumAt_coinImpl`,
  `Quantum.outcomeMeasure_run₂_toQuantumAt_coinImpl`.
* `Quantum.QuantumComp.run_liftInstruments`, `Quantum.QuantumComp.isQueryBound_liftInstruments_iff`,
  `Quantum.QuantumComp.lossless_liftInstruments_iff`.
* `Quantum.EmulatedOracle.branch_run₂_callBasis`.
-/

public section

open Matrix OracleSpec OracleComp
open scoped Kronecker ENNReal

universe u v u₁ v₁ w w₁

namespace Quantum

/-! ## Coins and sequencing in programs -/

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {B : QReg}

/-- **Coins inside an experiment.** The query `n` of `unifSpec` (a uniform element of
`Fin (n + 1)`) is answered by a uniform coin that leaves the held register `B` untouched. -/
@[expose]
noncomputable def coinImpl (spec : QuantumOracleSpec.{u₁, v₁}) (B : QReg) :
    QueryImpl unifSpec (QComp.{u₁, v₁, 0} spec B B) :=
  fun n ↦ QComp.act (SubInstrument.uniform (Fin (n + 1)) B)

/-- Coins are lossless. -/
theorem lossless_coinImpl (n : ℕ) : (coinImpl spec B n).Lossless .instruments :=
  QComp.lossless_act (SubInstrument.lossless_uniform _ _)

/-- Coins make no call. -/
theorem isQueryBound_coinImpl (n : ℕ) (b : spec.Port → ℕ) :
    (coinImpl spec B n).IsQueryBound b :=
  QComp.isQueryBound_act _ b

/-- **Sequencing over `Fin k`.** Run `f 0, …, f (k - 1)` in order on the held register and
return the dependent tuple of their results. -/
@[expose]
noncomputable def pi : {k : ℕ} → {β : Fin k → Type w} →
    ((i : Fin k) → QComp spec B B (β i)) →
    QComp spec B B ((i : Fin k) → β i) :=
  IPFunctor.FreeM₂.seqPi

/-- Sequencing an empty tuple returns the empty tuple. -/
@[simp]
theorem pi_zero {β : Fin 0 → Type w} (f : (i : Fin 0) → QComp spec B B (β i)) :
    pi f = QuantumComp₂.pure fun i ↦ i.elim0 :=
  rfl

/-- Sequencing a nonempty tuple runs its first component, then the remaining components. -/
theorem pi_succ {k : ℕ} {β : Fin (k + 1) → Type w}
    (f : (i : Fin (k + 1)) → QComp spec B B (β i)) :
    pi f = (f 0).bind fun b ↦ (pi fun i ↦ f i.succ).bind fun bs ↦
      QuantumComp₂.pure (Fin.cons b bs) :=
  rfl

/-- Sequencing lossless programs is lossless. -/
theorem lossless_pi : {k : ℕ} → {β : Fin k → Type w} →
    {f : (i : Fin k) → QComp spec B B (β i)} →
    (∀ i, (f i).Lossless .instruments) → (pi f).Lossless .instruments :=
  IPFunctor.FreeM₂.isRollBound_seqPi_unit

/-- The sequence of the programs `f i` is within the sum of their budgets. -/
theorem isQueryBound_pi : {k : ℕ} → {β : Fin k → Type w} →
    {f : (i : Fin k) → QComp spec B B (β i)} → {b : Fin k → spec.Port → ℕ} →
    (∀ i, (f i).IsQueryBound (b i)) → (pi f).IsQueryBound (∑ i, b i) := by
  intro k β f b hf p
  rw [Finset.sum_apply]
  exact IPFunctor.FreeM₂.isChargeBound_seqPi (fun i ↦ b i p) (fun i ↦ hf i p)

end QComp

/-! ## Classical sampling laws -/

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {B : QReg}

/-- A classical sampler run with uniform coins has each branch equal to its classical output
probability times the identity on the held and runtime registers. -/
theorem branch_run₂_toQuantumAt_coinImpl {α : Type} (oa : ProbComp α) (a : α) :
    (R.run₂ .instruments (oa.toQuantumAt (QComp.coinImpl spec B))).branch a =
      ((Pr{let x ← oa}[x = a]).toReal : ℂ) • LinearMap.id := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
    rw [toQuantumAt_pure, QuantumRuntime.run₂_pure, prEvent_pure]
    by_cases h : a = x
    · subst h
      simp
    · simp [Ne.symm h, SubInstrument.branch_pure_of_ne h]
  | query_bind t k ih =>
    have hcoin (y : Fin (t + 1)) :
        (R.run₂ .instruments (QComp.coinImpl spec B t)).branch y =
          ((Fintype.card (Fin (t + 1)) : ℂ)⁻¹) • LinearMap.id := by
      rw [QComp.coinImpl, QuantumRuntime.run₂_act, SubInstrument.bind_pure,
        DSubInstrument.branch_frame_apply]
      refine LinearMap.ext fun ρ ↦ ?_
      ext x x'
      simp [SubInstrument.branch_uniform_apply]
    have hp (y : Fin (t + 1)) :
        Pr{let x ← (liftM (unifSpec.query t) : ProbComp (Fin (t + 1)))}[x = y] =
          (Fintype.card (Fin (t + 1)) : ℝ≥0∞)⁻¹ := by
      simpa [Finset.filter_eq'] using
        (prEvent_liftM_query_eq_card_div (spec := unifSpec) t (fun x ↦ x = y))
    rw [toQuantumAt_query_bind, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply_univ,
      prEvent_bind_eq_sum_fintype]
    simp only [hp]
    rw [ENNReal.toReal_sum (fun y _ ↦ ENNReal.mul_ne_top (by simp) (prEvent_ne_top _))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    refine LinearMap.ext fun ρ ↦ ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, ih, hcoin, LinearMap.smul_apply,
      LinearMap.id_apply, smul_smul, Finset.sum_smul, mul_comm]

/-- The complete outcome measure of a classical sampler is its classical output measure scaled
by the trace of the joint input substate. -/
theorem outcomeMeasure_run₂_toQuantumAt_coinImpl {α : Type} [MeasurableSpace α]
    (oa : ProbComp α) (ρ : SubState (B × R.D)) :
    (R.run₂ .instruments (oa.toQuantumAt (QComp.coinImpl spec B))).outcomeMeasure ρ =
      ENNReal.ofReal ρ.matrix.trace.re • 𝒟[oa] := by
  classical
  ext s hs
  rw [DSubInstrument.outcomeMeasure_apply _ _ hs, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  simp_rw [branch_run₂_toQuantumAt_coinImpl, LinearMap.smul_apply, LinearMap.id_apply,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (prEvent_ne_top _)]
  calc
    _ = ENNReal.ofReal ρ.matrix.trace.re *
        ∑' a, if a ∈ s then Pr{let x ← oa}[x = a] else 0 := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun a ↦ ?_
      by_cases ha : a ∈ s <;> simp [ha, mul_comm]
    _ = _ := by
      congr 1
      rw [← OracleComp.prEvent_eq_tsum_ite]
      exact prEvent_eq_evalDist oa (· ∈ s) hs.mem

/-- Every outcome of a classical sampler has its classical probability times the trace of the
joint input substate as its weight, including inputs correlated with the runtime register. -/
theorem outcomeMeasure_run₂_toQuantumAt_coinImpl_apply_singleton {α : Type}
    [MeasurableSpace α] [MeasurableSingletonClass α] (oa : ProbComp α)
    (ρ : SubState (B × R.D)) (a : α) :
    (R.run₂ .instruments (oa.toQuantumAt (QComp.coinImpl spec B))).outcomeMeasure ρ {a} =
      Pr{let x ← oa}[x = a] * ENNReal.ofReal ρ.matrix.trace.re := by
  rw [outcomeMeasure_run₂_toQuantumAt_coinImpl, MeasureTheory.Measure.smul_apply,
    smul_eq_mul, ← prEvent_eq_evalDist_singleton, mul_comm]

namespace LocalSig

/-- An operation of the signature of instruments with its outcomes lifted to
`Type (max v w)`: the same dependent subinstrument, on the outcomes `ULift ι`. -/
@[expose, reducible]
noncomputable def InstrumentOp.lift {A : QReg} (o : InstrumentOp.{v} A) :
    InstrumentOp.{max v w} A :=
  ⟨ULift.{w} o.1, fun b ↦ o.2.1 b.down, o.2.2.comap ULift.down ULift.down_injective⟩

end LocalSig

namespace QuantumComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {X : QReg → Type w₁}

/-- Recursion for `Quantum.QuantumComp.liftInstruments` on the underlying trees. -/
@[expose]
noncomputable def liftInstrumentsAux : {A : QReg} →
    IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{v} spec) X A →
      QuantumComp LocalSig.instruments.{max v w} spec X A
  | _, .pure y => QuantumComp.pure y
  | _, .liftBind (.prim o) k =>
      QuantumComp.primBind (L := LocalSig.instruments.{max v w}) o.lift fun b ↦
        liftInstrumentsAux (k (ULift.up b.down))
  | _, .liftBind (.query i E ℓ) k =>
      QuantumComp.queryBind i E ℓ fun r ↦ liftInstrumentsAux (k (ULift.up r))

/-- **Lifting the outcomes of local operations.** A program over instruments with outcomes in
`Type v` as a program over instruments with outcomes in `Type (max v w)`: every local operation
is the same dependent subinstrument on the lifted outcomes (`LocalSig.InstrumentOp.lift`), and
calls and leaves are kept. It runs as the original program (`run_liftInstruments`). This is how a
program whose local operations have small outcomes, such as a challenger, is sequenced after a
program in a larger universe. -/
@[expose]
noncomputable def liftInstruments {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} spec X A) :
    QuantumComp LocalSig.instruments.{max v w} spec X A :=
  liftInstrumentsAux x

/-- A leaf is lifted to itself. -/
@[simp]
theorem liftInstruments_pure {A : QReg} (y : X A) :
    ((QuantumComp.pure (L := LocalSig.instruments.{v}) (spec := spec) y).liftInstruments :
      QuantumComp LocalSig.instruments.{max v w} spec X A) = QuantumComp.pure y :=
  rfl

/-- A local operation is lifted to the same operation on lifted outcomes. -/
@[simp]
theorem liftInstruments_primBind {A : QReg} (o : LocalSig.instruments.{v}.Op A)
    (k : (b : LocalSig.instruments.{v}.Outcome o) →
      QuantumComp LocalSig.instruments.{v} spec X (LocalSig.instruments.{v}.next o b)) :
    ((QuantumComp.primBind o k).liftInstruments :
      QuantumComp LocalSig.instruments.{max v w} spec X A) =
      QuantumComp.primBind (L := LocalSig.instruments.{max v w}) o.lift fun b ↦
        (k b.down).liftInstruments :=
  rfl

/-- A call is kept. -/
@[simp]
theorem liftInstruments_queryBind {A : QReg} (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i →
      QuantumComp LocalSig.instruments.{v} spec X (QReg.of (spec.Out i × E))) :
    ((QuantumComp.queryBind i E ℓ k).liftInstruments :
      QuantumComp LocalSig.instruments.{max v w} spec X A) =
      QuantumComp.queryBind i E ℓ fun r ↦ (k r).liftInstruments :=
  rfl

/-- **Lifted programs run as the original.** -/
theorem run_liftInstruments (R : QuantumRuntime spec) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} spec X A) :
    R.run .instruments
      (x.liftInstruments : QuantumComp LocalSig.instruments.{max v w} spec X A) =
      R.run .instruments x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [liftInstruments_primBind, QuantumRuntime.run_primBind, QuantumRuntime.run_primBind]
    simp only [ih]
    exact DSubInstrument.comap_down_bind ((o.2.2).frame R.D) fun b ↦ R.run .instruments (k b)
  | queryBind _ i E ℓ k ih =>
    rw [liftInstruments_queryBind, QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
    simp only [ih]

/-- Lifting keeps every query budget. -/
theorem isQueryBound_liftInstruments_iff {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} spec X A} {b : spec.Port → ℕ} :
    (x.liftInstruments : QuantumComp LocalSig.instruments.{max v w} spec X A).IsQueryBound b ↔
      x.IsQueryBound b := by
  classical
  induction x using QuantumComp.inductionOn generalizing b with
  | pure _ _ => exact iff_of_true (isQueryBound_pure _ _) (isQueryBound_pure _ _)
  | primBind _ o k ih =>
    rw [liftInstruments_primBind, isQueryBound_primBind_iff, isQueryBound_primBind_iff]
    exact ⟨fun h c ↦ ih c |>.mp (h ⟨c⟩), fun h c ↦ ih c.down |>.mpr (h c.down)⟩
  | queryBind _ i E ℓ k ih =>
    rw [liftInstruments_queryBind, isQueryBound_queryBind_iff, isQueryBound_queryBind_iff]
    exact and_congr_right fun _ ↦ forall_congr' fun r ↦ ih r

/-- Lifting keeps losslessness. -/
theorem lossless_liftInstruments_iff {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} spec X A} :
    (x.liftInstruments : QuantumComp LocalSig.instruments.{max v w} spec X A).Lossless
      .instruments ↔ x.Lossless .instruments := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => exact Iff.rfl
  | primBind _ o k ih =>
    rw [liftInstruments_primBind, lossless_primBind_iff, lossless_primBind_iff]
    exact and_congr ⟨fun h ↦ h.comap (f := ULift.up.{w}) ULift.up_bijective,
      fun h ↦ h.comap ULift.down_bijective⟩
      ⟨fun h c ↦ ih c |>.mp (h ⟨c⟩), fun h c ↦ ih c.down |>.mpr (h c.down)⟩
  | queryBind _ i E ℓ k ih =>
    rw [liftInstruments_queryBind, lossless_queryBind_iff, lossless_queryBind_iff]
    exact forall_congr' fun r ↦ ih r

end QuantumComp

/-! ## Basis calls against an emulated oracle -/

namespace EmulatedOracle

variable {P : Type u} {In : P → QReg} (E : EmulatedOracle P In)

/-- The block `⟨o|U_p|a⟩` of the unitary of port `p` on the private register. -/
@[expose]
noncomputable def block (p : P) (o a : In p) : Matrix E.S E.S ℂ :=
  (E.U p).submatrix (fun d ↦ (o, d)) fun d ↦ (a, d)

/-- The entries of a block. -/
@[simp]
theorem block_apply (p : P) (o a : In p) (d d' : E.S) : E.block p o a d d' = E.U p (o, d) (a, d') :=
  rfl

/-- **The branch of a basis call against an emulated oracle**: at the reading `c`, the sum over
the port outputs `o` with `read o () = c` of the Kraus map of `1_B ⊗ ⟨o|U_p|a⟩`. The held
register `B` is untouched, and the private register is acted on by a block of the port's
unitary. -/
theorem branch_run₂_callBasis {β : Type} [DecidableEq β] (p : P) (B : QReg) (a : In p)
    (read : In p → Unit → β) (c : β) :
    (E.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec P In) p B a read)).branch c =
      ∑ o, if read o () = c then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ E.block p o a)
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
    split_ifs <;>
      simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, not_and,
        and_imp, Finset.univ_unique, PUnit.default_eq_unit, Equiv.coe_uniqueProd, mul_ite,
        mul_one, mul_zero, ↓reduceIte, Finset.sum_ite_eq', Finset.sum_ite_irrel,
        Finset.sum_const, Finset.card_singleton, one_smul, smul_zero,
        star_zero, star_one, ite_eq_right_iff, one_ne_zero, imp_false, ite_self,
        not_true_eq_false]
    tauto
  rw [hR, ← Matrix.mul_assoc, hL]
  simp only [Matrix.mul_assoc]
  rw [← basisMatrix_comp, basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut _ _ _),
    ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← basisMatrix_comp, ← Matrix.mul_assoc,
    conjTranspose_basisMatrix_mul_mul_basisMatrix]
  ext ⟨b, d⟩ ⟨b', d'⟩
  simp [block, QuantumRuntime.queryEquivOut, Matrix.one_apply]

end EmulatedOracle

end Quantum
