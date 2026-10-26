/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.IPFunctor.Free.Lens
public import VCVio.Quantum.Oracle.Emulated

/-!
# Total call budgets

The budget is PolyFun's `IPFunctor.IFreeM.IsChargeBound`: every oracle call consumes one unit,
independently of its port. Local operations consume none.
Left injection into a sum signature preserves the tree and its execution weights.
-/

public section

open IPFunctor
open scoped ENNReal ComplexOrder

universe u v u₁ u₂ v₁ w w₁

namespace Quantum
namespace QuantumComp

variable {L : LocalSig.{u, v}} {s : QuantumOracleSpec.{u₁, v₁}}
  {t : QuantumOracleSpec.{u₂, v₁}} {X : QReg → Type w} {Y : QReg → Type w₁} {A : QReg}

/-- The charge of a command: one for a query and zero for a local operation. -/
@[expose]
def Cmd.queryCharge : {A : QReg} → Cmd L s A → ℕ
  | _, .prim _ => 0
  | _, .query _ _ _ => 1

/-- Every path makes at most `n` oracle calls in total, including zero-weight paths. -/
@[expose]
def IsTotalQueryBound (x : QuantumComp L s X A) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound x (fun _ c ↦ c.queryCharge) n

/-- Returning consumes no calls. -/
@[simp]
theorem isTotalQueryBound_pure (a : X A) (n : ℕ) :
    (QuantumComp.pure a : QuantumComp L s X A).IsTotalQueryBound n :=
  IFreeM.isChargeBound_pure a n

/-- Local operations preserve the available budget. -/
@[simp]
theorem isTotalQueryBound_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L s X (L.next o b)) (n : ℕ) :
    (primBind o k).IsTotalQueryBound n ↔ ∀ b, (k b).IsTotalQueryBound n := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := toIPFunctor L s)
    (c := fun _ c ↦ c.queryCharge) (.prim o) (onDown k) n).trans ?_
  simp only [Cmd.queryCharge, Nat.zero_le, Nat.sub_zero, true_and]
  exact ULift.forall

/-- Every query consumes one call, regardless of its port. -/
@[simp]
theorem isTotalQueryBound_queryBind_iff (i : s.Port) (B : QReg) (e : A ≃ s.In i × B)
    (k : s.Result i → QuantumComp L s X (QReg.of (s.Out i × B))) (n : ℕ) :
    (queryBind i B e k).IsTotalQueryBound n ↔
      0 < n ∧ ∀ r, (k r).IsTotalQueryBound (n - 1) := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := toIPFunctor L s)
    (c := fun _ c ↦ c.queryCharge) (.query i B e) (onDown k) n).trans ?_
  exact and_congr Nat.succ_le_iff ULift.forall

/-- Increasing a total call budget preserves the bound. -/
theorem IsTotalQueryBound.mono {x : QuantumComp L s X A} {n m : ℕ}
    (hx : x.IsTotalQueryBound n) (h : n ≤ m) : x.IsTotalQueryBound m :=
  IFreeM.IsChargeBound.mono hx h

/-- Total call budgets add under sequencing. -/
theorem IsTotalQueryBound.bind {x : QuantumComp L s X A}
    {k : ∀ B, X B → QuantumComp L s Y B} {n m : ℕ}
    (hx : x.IsTotalQueryBound n) (hk : ∀ B a, (k B a).IsTotalQueryBound m) :
    (x.bind k).IsTotalQueryBound (n + m) := by
  have hbind : x.bind k = IFreeM.bind x k := by
    clear hx
    induction x using IFreeM.inductionOn with
    | pure _ _ => rfl
    | liftBind _ c r ih => exact congrArg (IFreeM.liftBind c) (funext ih)
  rw [hbind]
  exact IFreeM.isChargeBound_bind hx hk

/-- On a single port, the per-port and total budgets coincide. -/
theorem isTotalQueryBound_iff_isQueryBound [Unique s.Port] (x : QuantumComp L s X A) (n : ℕ) :
    x.IsTotalQueryBound n ↔ x.IsQueryBound (fun _ ↦ n) := by
  have h : ∀ (i : s.Port), x.IsTotalQueryBound n ↔ x.IsQueryBoundAt i n := by
    intro i
    induction x using QuantumComp.inductionOn generalizing n with
    | pure _ _ => exact Iff.rfl
    | primBind _ o k ih =>
      rw [isTotalQueryBound_primBind_iff, isQueryBoundAt_primBind_iff]
      exact forall_congr' fun b ↦ ih b n
    | queryBind _ j B e k ih =>
      rw [isTotalQueryBound_queryBind_iff, isQueryBoundAt_queryBind_iff]
      simp only [Subsingleton.elim j i, true_implies, ne_self_iff_false, false_implies, and_true]
      exact and_congr Iff.rfl (forall_congr' fun r ↦ ih r (n - 1))
  exact ⟨fun hx i ↦ (h i).mp hx, fun hx ↦ (h default).mpr (hx default)⟩

/-- The command lens embedding ordinary ports on the left of a sum signature. -/
@[expose]
def ordinaryLens : Lens (toIPFunctor L s) (toIPFunctor L (s.sum t)) where
  toFunA _
    | .prim o => .prim o
    | .query i B e => .query (.inl i) B e
  toFunB _ c := by cases c <;> exact id
  src_eq _ c _ := by cases c <;> rfl

/-- Inject a program into the left ports without adding operations or changing outcomes. -/
@[expose]
def liftOrdinary : {A : QReg} → QuantumComp L s X A → QuantumComp L (s.sum t) X A :=
  fun {_} x ↦ IFreeM.mapLens ordinaryLens x

/-- Left injection preserves return values. -/
@[simp]
theorem liftOrdinary_pure (a : X A) :
    liftOrdinary (t := t) (QuantumComp.pure a : QuantumComp L s X A) = QuantumComp.pure a := rfl

/-- Left injection preserves local operations. -/
@[simp]
theorem liftOrdinary_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L s X (L.next o b)) :
    (primBind o k).liftOrdinary (t := t) = primBind o (fun b ↦ (k b).liftOrdinary) := rfl

/-- Left injection changes only the port label of a query. -/
@[simp]
theorem liftOrdinary_queryBind (i : s.Port) (B : QReg) (e : A ≃ s.In i × B)
    (k : s.Result i → QuantumComp L s X (QReg.of (s.Out i × B))) :
    (queryBind i B e k).liftOrdinary (t := t) =
      queryBind (spec := s.sum t) (.inl i) B e (fun r ↦ (k r).liftOrdinary) := rfl

/-- Left injection preserves exactly the total call budgets. -/
@[simp]
theorem isTotalQueryBound_liftOrdinary_iff (x : QuantumComp L s X A) (n : ℕ) :
    (x.liftOrdinary (t := t)).IsTotalQueryBound n ↔ x.IsTotalQueryBound n := by
  unfold IsTotalQueryBound IFreeM.IsChargeBound liftOrdinary IFreeM.mapLens
  refine (IFreeM.isRollBound_reindex_iff ordinaryLens.toReindexing (fun _ value ↦ value)
    (fun _ c ↦ by cases c <;> exact fun answer ↦ ⟨answer, rfl⟩) x n).trans ?_
  exact IFreeM.isRollBound_congr (fun _ c _ ↦ by cases c <;> rfl)
    (fun _ c _ ↦ by cases c <;> rfl)

/-- Per-port call counts on the left are preserved as well. -/
@[simp]
theorem isQueryBoundAt_liftOrdinary_inl_iff (x : QuantumComp L s X A) (i : s.Port) (n : ℕ) :
    (x.liftOrdinary (t := t)).IsQueryBoundAt (.inl i) n ↔ x.IsQueryBoundAt i n := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => exact Iff.rfl
  | primBind _ o k ih =>
    rw [liftOrdinary_primBind, isQueryBoundAt_primBind_iff, isQueryBoundAt_primBind_iff]
    exact forall_congr' fun b ↦ ih b n
  | queryBind _ j B e k ih =>
    rw [liftOrdinary_queryBind, isQueryBoundAt_queryBind_iff j]
    refine (isQueryBoundAt_queryBind_iff (spec := s.sum t) (.inl j) B e
      (fun r ↦ (k r).liftOrdinary) (.inl i) n).trans ?_
    simp only [ne_eq, _root_.Sum.inl.injEq]
    exact and_congr
      (imp_congr_right fun _ ↦ and_congr Iff.rfl (forall_congr' fun r ↦ ih r (n - 1)))
      (imp_congr_right fun _ ↦ forall_congr' fun r ↦ ih r n)

/-- A left-injected program never calls a right port. -/
@[simp]
theorem isQueryBoundAt_liftOrdinary_inr (x : QuantumComp L s X A) (i : t.Port) (n : ℕ) :
    (x.liftOrdinary (t := t)).IsQueryBoundAt (.inr i) n := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => exact isQueryBoundAt_pure _ _ _
  | primBind _ o k ih =>
    rw [liftOrdinary_primBind, isQueryBoundAt_primBind_iff]
    exact fun b ↦ ih b
  | queryBind _ j B e k ih =>
    rw [liftOrdinary_queryBind]
    refine (isQueryBoundAt_queryBind_iff (spec := s.sum t) (.inl j) B e
      (fun r ↦ (k r).liftOrdinary) (.inr i) n).2 ?_
    exact ⟨fun h ↦ (Sum.inl_ne_inr h).elim, fun _ r ↦ ih r⟩

end QuantumComp

namespace QuantumRuntime

variable {L : LocalSig.{u, v}} {s : QuantumOracleSpec.{u₁, v₁}}
  {t : QuantumOracleSpec.{u₂, v₁}} (R : QuantumRuntime s) (I : L.Interp)
  {X : QReg → Type w} {A : QReg}
  (step : ∀ i : t.Port, SubInstrument (t.In i × R.D) (t.Out i × R.D) (t.Result i))

/-- An extension executes a left-injected program exactly as the original runtime does. -/
@[simp]
theorem run_liftOrdinary (x : QuantumComp L s X A) :
    (R.extend step).run I x.liftOrdinary = R.run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih => exact congrArg (((I o).frame R.D).bind) (funext ih)
  | queryBind _ i B e k ih =>
    change (DSubInstrument.bind (R.queryStep i B e) fun r ↦
      (R.extend step).run I ((k r).liftOrdinary (t := t))) = _
    congr 1
    funext r
    exact ih r

/-- Selected weights are unchanged when the weights on the left ports agree. -/
theorem queryWeight_liftOrdinary
    (w : ∀ i, Matrix (s.In i × R.D) (s.In i × R.D) ℂ → ℝ≥0∞)
    (w' : ∀ i, Matrix ((s.sum t).In i × R.D) ((s.sum t).In i × R.D) ℂ → ℝ≥0∞)
    (hw : ∀ i σ, w' (.inl i) σ = w i σ) (x : QuantumComp L s X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    (R.extend step).queryWeight I w' x.liftOrdinary ρ j = R.queryWeight I w x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih => exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ i B e k ih =>
    cases j with
    | zero => exact hw i _
    | succ j => exact tsum_congr fun r ↦ ih r _ j

/-- Summed selected masses are preserved by left injection. -/
theorem totalWeight_liftOrdinary
    (w : ∀ i, Matrix (s.In i × R.D) (s.In i × R.D) ℂ → ℝ≥0∞)
    (w' : ∀ i, Matrix ((s.sum t).In i × R.D) ((s.sum t).In i × R.D) ℂ → ℝ≥0∞)
    (hw : ∀ i σ, w' (.inl i) σ = w i σ) (x : QuantumComp L s X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    (R.extend step).totalWeight I w' x.liftOrdinary ρ = R.totalWeight I w x ρ :=
  tsum_congr fun j ↦ R.queryWeight_liftOrdinary I step w w' hw x ρ j

variable {w : ∀ i, Matrix (s.In i × R.D) (s.In i × R.D) ℂ → ℝ≥0∞}

/-- No query weight occurs at or beyond the total call budget. -/
theorem queryWeight_eq_zero_of_isTotalQueryBound {x : QuantumComp L s X A} {n j : ℕ}
    (hx : x.IsTotalQueryBound n) (hj : n ≤ j) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryWeight I w x ρ j = 0 := by
  induction x using QuantumComp.inductionOn generalizing n j with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [QuantumComp.isTotalQueryBound_primBind_iff] at hx
    exact ENNReal.tsum_eq_zero.mpr fun b ↦ ih b (hx b) hj _
  | queryBind _ i B e k ih =>
    rw [QuantumComp.isTotalQueryBound_queryBind_iff] at hx
    cases j with
    | zero => have := hx.1; omega
    | succ j => exact ENNReal.tsum_eq_zero.mpr fun r ↦ ih r (hx.2 r) (by omega) _

/-- Trace-bounded weights summed over a bounded program are at most budget times trace. -/
theorem totalWeight_le_of_isTotalQueryBound
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ ENNReal.ofReal σ.trace.re)
    {x : QuantumComp L s X A} {n : ℕ} (hx : x.IsTotalQueryBound n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w x ρ ≤ n * ENNReal.ofReal ρ.trace.re := by
  rw [totalWeight, tsum_eq_sum (s := Finset.range n) (fun j hj ↦
    R.queryWeight_eq_zero_of_isTotalQueryBound I hx (by simpa using hj) ρ)]
  calc
    _ ≤ ∑ _j ∈ Finset.range n, ENNReal.ofReal ρ.trace.re :=
      Finset.sum_le_sum fun j _ ↦ R.queryWeight_le_ofReal_trace I hw x hρ j
    _ = _ := by simp

/-- The total mass, summed over every port, is bounded by total calls times input trace. -/
theorem tsum_queryMass_le_of_isTotalQueryBound
    {x : QuantumComp L s X A} {n : ℕ} (hx : x.IsTotalQueryBound n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, R.queryMass I x ρ i ≤ n * ENNReal.ofReal ρ.trace.re := by
  classical
  simp only [queryMass, ENNReal.tsum_comm (f := fun i j ↦ R.queryMassAt I x ρ i j)]
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj ↦ ?_)]
  · calc
      _ ≤ ∑ _j ∈ Finset.range n, ENNReal.ofReal ρ.trace.re :=
        Finset.sum_le_sum fun j _ ↦ R.tsum_queryMassAt_le I x hρ j
      _ = _ := by simp
  · exact ENNReal.tsum_eq_zero.mpr fun i ↦
      R.queryWeight_eq_zero_of_isTotalQueryBound I hx (by simpa using hj) ρ

end QuantumRuntime
end Quantum
