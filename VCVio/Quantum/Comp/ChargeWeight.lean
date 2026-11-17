/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.RoundBound

/-!
# Query weights under pathwise port charges

A natural-number charge is assigned to each oracle port, with local operations free.
A pathwise charge budget bounds the sum of all query weights whenever a call's weight is
at most its charge times its input trace. The proof follows the residual budget along
adaptive branches, preserving arbitrary mixed or subnormalized states and trace loss.

For batches, charging the width gives a total-point bound without adding per-port maxima.
Zero-width calls may occur without consuming points; their bounded query weight is zero.
-/

public section

open IPFunctor Matrix
open scoped ENNReal ComplexOrder

universe u v u₁ v₁ w w₁

namespace Quantum
namespace QuantumComp

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}}
  {W : QReg → Type w} {A : QReg}

/-- Charge an oracle call by its port, and charge local operations zero. -/
@[expose]
def Cmd.portCharge (c : spec.Port → ℕ) : {A : QReg} → Cmd L spec A → ℕ
  | _, .prim _ => 0
  | _, .query i _ _ => c i

/-- Every execution prefix spends at most `n` in oracle-port charges, including zero-weight
branches and calls with no possible answer. -/
@[expose]
def IsQueryChargeBound (x : QuantumComp L spec W A) (c : spec.Port → ℕ) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound x (fun _ cmd ↦ cmd.portCharge c) n

/-- Returning spends no port charge. -/
@[simp]
theorem isQueryChargeBound_pure (a : W A) (c : spec.Port → ℕ) (n : ℕ) :
    (QuantumComp.pure a : QuantumComp L spec W A).IsQueryChargeBound c n :=
  IFreeM.isChargeBound_pure a n

/-- Local operations preserve the charge budget on every continuation. -/
@[simp]
theorem isQueryChargeBound_primBind_iff (o : L.Op A)
    (next : (b : L.Outcome o) → QuantumComp L spec W (L.next o b))
    (c : spec.Port → ℕ) (n : ℕ) :
    (primBind o next).IsQueryChargeBound c n ↔ ∀ b, (next b).IsQueryChargeBound c n := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := toIPFunctor L spec)
    (c := fun _ cmd ↦ cmd.portCharge c) (.prim o) (onDown next) n).trans ?_
  simp only [Cmd.portCharge, Nat.zero_le, Nat.sub_zero, true_and]
  exact ULift.forall

/-- A call spends its port charge and each continuation fits in the residual budget. -/
@[simp]
theorem isQueryChargeBound_queryBind_iff (i : spec.Port) (E : QReg)
    (e : A ≃ spec.In i × E)
    (next : spec.Result i → QuantumComp L spec W (QReg.of (spec.Out i × E)))
    (c : spec.Port → ℕ) (n : ℕ) :
    (queryBind i E e next).IsQueryChargeBound c n ↔
      c i ≤ n ∧ ∀ r, (next r).IsQueryChargeBound c (n - c i) := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := toIPFunctor L spec)
    (c := fun _ cmd ↦ cmd.portCharge c) (.query i E e) (onDown next) n).trans ?_
  exact and_congr_right' ULift.forall

/-- A port-charge budget may be increased. -/
theorem IsQueryChargeBound.mono {x : QuantumComp L spec W A} {c : spec.Port → ℕ}
    {n m : ℕ} (hx : x.IsQueryChargeBound c n) (hnm : n ≤ m) :
    x.IsQueryChargeBound c m :=
  IFreeM.IsChargeBound.mono hx hnm

/-- Port-charge budgets add under sequencing, including dependent final registers. -/
theorem IsQueryChargeBound.bind {Z : QReg → Type w₁}
    {x : QuantumComp L spec W A} {next : ∀ B, W B → QuantumComp L spec Z B}
    {c : spec.Port → ℕ} {n m : ℕ} (hx : x.IsQueryChargeBound c n)
    (hn : ∀ B a, (next B a).IsQueryChargeBound c m) :
    (x.bind next).IsQueryChargeBound c (n + m) := by
  rw [bind_eq_iFreeM_bind]
  exact IFreeM.isChargeBound_bind hx hn

/-- Charging every port one is the total oracle-call budget. -/
theorem isQueryChargeBound_one_iff (x : QuantumComp L spec W A) (n : ℕ) :
    x.IsQueryChargeBound (fun _ ↦ 1) n ↔ x.IsTotalQueryBound n := by
  unfold IsQueryChargeBound IsTotalQueryBound
  have hcharge : (fun A (cmd : Cmd L spec A) ↦ cmd.portCharge (fun _ ↦ 1)) =
      (fun _ cmd ↦ cmd.queryCharge) := by
    funext A cmd
    cases cmd <;> rfl
  exact iff_of_eq (congrArg
    (fun charge ↦ IFreeM.IsChargeBound (P := toIPFunctor L spec) x charge n) hcharge)

/-- The width charge is the total-point budget on batches. -/
theorem isQueryChargeBound_width_iff {P : Type*} {In : P → QReg}
    (x : QuantumComp L (uBatchSpec P In) W A) (n : ℕ) :
    x.IsQueryChargeBound (fun ik ↦ ik.2) n ↔ x.IsPointBound n := by
  unfold IsQueryChargeBound IsPointBound
  have hcharge : (fun A (cmd : Cmd L (uBatchSpec P In) A) ↦
      Cmd.portCharge (spec := uBatchSpec P In) (fun ik : P × ℕ ↦ ik.2) cmd) =
      (fun _ cmd ↦ cmd.pointCharge) := by
    funext A cmd
    cases cmd <;> rfl
  exact iff_of_eq (congrArg
    (fun charge ↦ IFreeM.IsChargeBound (P := toIPFunctor L (uBatchSpec P In)) x charge n)
    hcharge)

end QuantumComp

namespace QuantumRuntime

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}}
  (R : QuantumRuntime spec) (I : L.Interp) {W : QReg → Type w} {A : QReg}

/-- A pathwise port-charge budget bounds all call weights by budget times input trace.
The estimate uses the charge of each actual call and permits zero-charge calls. -/
theorem totalWeight_le_of_isQueryChargeBound (c : spec.Port → ℕ)
    {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ c i * ENNReal.ofReal σ.trace.re)
    {x : QuantumComp L spec W A} {n : ℕ} (hx : x.IsQueryChargeBound c n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w x ρ ≤ n * ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => simp
  | primBind _ o next ih =>
    rw [QuantumComp.isQueryChargeBound_primBind_iff] at hx
    rw [totalWeight_primBind]
    refine (ENNReal.tsum_le_tsum fun b ↦
      ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ)).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul le_rfl
      (((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) bot_le bot_le
  | queryBind _ i E e next ih =>
    rw [QuantumComp.isQueryChargeBound_queryBind_iff] at hx
    rw [totalWeight_queryBind]
    refine (add_le_add (hw i _ (posSemidef_callInput e hρ))
      (ENNReal.tsum_le_tsum fun r ↦
        ih r (hx.2 r) ((R.queryStep i E e).posSemidef_branch_apply r hρ))).trans ?_
    rw [trace_callInput, ENNReal.tsum_mul_left]
    calc
      _ ≤ (c i : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re +
          (n - c i : ℕ) * ENNReal.ofReal ρ.trace.re := by
        gcongr
        exact (R.queryStep i E e).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
      _ = _ := by rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hx.1]

/-- A total-point budget bounds all weights of an adaptive batch program when a width-`k`
call has weight at most `k` times its input trace. -/
theorem totalWeight_le_of_isPointBound {P : Type*} {In : P → QReg}
    (R : QuantumRuntime (uBatchSpec P In))
    {w : ∀ i, Matrix ((uBatchSpec P In).In i × R.D)
      ((uBatchSpec P In).In i × R.D) ℂ → ℝ≥0∞}
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ i.2 * ENNReal.ofReal σ.trace.re)
    {x : QuantumComp L (uBatchSpec P In) W A} {n : ℕ} (hx : x.IsPointBound n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w x ρ ≤ n * ENNReal.ofReal ρ.trace.re :=
  R.totalWeight_le_of_isQueryChargeBound I (fun ik ↦ ik.2) hw
    ((QuantumComp.isQueryChargeBound_width_iff x n).mpr hx) hρ

end QuantumRuntime
end Quantum
