/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import PolyFun.IPFunctor.Free.Bound.Substitution
public import VCVio.Quantum.Comp.Parallel
public import VCVio.Quantum.Comp.TotalQueryBound

/-!
# Point and width budgets for ordered batches

`QuantumComp.IsPointBound` charges a batch its width, while `QuantumComp.IsWidthBound`
caps each individual batch width. These are syntactic bounds on every branch, including
zero-weight branches. A total call bound counts batches as rounds, so a width cap `k` and
a round bound `r` give a point bound `k * r` even when the program is adaptive.
-/

public section

open IPFunctor

universe u v u₁ w w₁

namespace Quantum
namespace QuantumComp

variable {L : LocalSig.{u, v}} {P : Type u₁} {In : P → QReg}
  {X : QReg → Type w} {Y : QReg → Type w₁} {A : QReg}

/-- The point charge of a batch command is its width; local operations have charge zero. -/
@[expose]
def Cmd.pointCharge : {A : QReg} → Cmd L (uBatchSpec P In) A → ℕ
  | _, .prim _ => 0
  | _, .query ik _ _ => ik.2

/-- Every branch uses at most `n` points, adding the widths of all its batches. -/
@[expose]
def IsPointBound (x : QuantumComp L (uBatchSpec P In) X A) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound x (fun _ c ↦ c.pointCharge) n

/-- Returning consumes no points. -/
@[simp]
theorem isPointBound_pure (a : X A) (n : ℕ) :
    (QuantumComp.pure a : QuantumComp L (uBatchSpec P In) X A).IsPointBound n :=
  IFreeM.isChargeBound_pure a n

/-- A local operation preserves the point budget on each continuation. -/
@[simp]
theorem isPointBound_primBind_iff (o : L.Op A)
    (next : (b : L.Outcome o) → QuantumComp L (uBatchSpec P In) X (L.next o b)) (n : ℕ) :
    (primBind o next).IsPointBound n ↔ ∀ b, (next b).IsPointBound n := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := toIPFunctor L (uBatchSpec P In))
    (c := fun _ c ↦ c.pointCharge) (.prim o) (onDown next) n).trans ?_
  simp only [Cmd.pointCharge, Nat.zero_le, Nat.sub_zero, true_and]
  exact ULift.forall

/-- A batch spends exactly its width, including when the width is zero. -/
@[simp]
theorem isPointBound_queryBind_iff (ik : P × ℕ) (E : QReg)
    (e : A ≃ (uBatchSpec P In).In ik × E)
    (next : (uBatchSpec P In).Result ik →
      QuantumComp L (uBatchSpec P In) X (QReg.of ((uBatchSpec P In).Out ik × E))) (n : ℕ) :
    (queryBind ik E e next).IsPointBound n ↔
      ik.2 ≤ n ∧ ∀ r, (next r).IsPointBound (n - ik.2) := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := toIPFunctor L (uBatchSpec P In))
    (c := fun _ c ↦ c.pointCharge) (.query ik E e) (onDown next) n).trans ?_
  exact and_congr_right' ULift.forall

/-- A local operation uses no points. -/
@[simp]
theorem isPointBound_prim (o : L.Op A) (n : ℕ) :
    (prim (spec := uBatchSpec P In) o).IsPointBound n := by
  simp [prim]

/-- A single batch fits exactly when its width fits. -/
@[simp]
theorem isPointBound_query_iff (ik : P × ℕ) (E : QReg)
    (e : A ≃ (uBatchSpec P In).In ik × E) (n : ℕ) :
    (query (L := L) ik E e).IsPointBound n ↔ ik.2 ≤ n := by
  simp [query]

/-- Increasing the available point budget preserves the bound. -/
theorem IsPointBound.mono {x : QuantumComp L (uBatchSpec P In) X A} {n m : ℕ}
    (hx : x.IsPointBound n) (hnm : n ≤ m) : x.IsPointBound m :=
  IFreeM.IsChargeBound.mono hx hnm

/-- Point budgets add under sequencing. -/
theorem IsPointBound.bind {x : QuantumComp L (uBatchSpec P In) X A}
    {next : ∀ B, X B → QuantumComp L (uBatchSpec P In) Y B} {n m : ℕ}
    (hx : x.IsPointBound n) (hn : ∀ B a, (next B a).IsPointBound m) :
    (x.bind next).IsPointBound (n + m) := by
  rw [bind_eq_iFreeM_bind]
  exact IFreeM.isChargeBound_bind hx hn

/-- Every batch at every node has width at most `k`; the width cap is never spent. -/
@[expose]
def IsWidthBound (x : QuantumComp L (uBatchSpec P In) X A) (k : ℕ) : Prop :=
  IFreeM.IsRollBound x k (fun _ c n ↦ c.pointCharge ≤ n) (fun _ _ n ↦ n)

/-- Returning satisfies every width cap. -/
@[simp]
theorem isWidthBound_pure (a : X A) (k : ℕ) :
    (QuantumComp.pure a : QuantumComp L (uBatchSpec P In) X A).IsWidthBound k :=
  IFreeM.isRollBound_pure a k

/-- Local operations preserve the width cap on every continuation. -/
@[simp]
theorem isWidthBound_primBind_iff (o : L.Op A)
    (next : (b : L.Outcome o) → QuantumComp L (uBatchSpec P In) X (L.next o b)) (k : ℕ) :
    (primBind o next).IsWidthBound k ↔ ∀ b, (next b).IsWidthBound k := by
  refine (IFreeM.isRollBound_liftBind_iff (P := toIPFunctor L (uBatchSpec P In))
    (canRoll := fun _ c n ↦ c.pointCharge ≤ n) (cost := fun _ _ n ↦ n)
    (.prim o) (onDown next) k).trans ?_
  simp only [Cmd.pointCharge, Nat.zero_le, true_and]
  exact ULift.forall

/-- A batch and all its continuations must satisfy the same width cap. -/
@[simp]
theorem isWidthBound_queryBind_iff (ik : P × ℕ) (E : QReg)
    (e : A ≃ (uBatchSpec P In).In ik × E)
    (next : (uBatchSpec P In).Result ik →
      QuantumComp L (uBatchSpec P In) X (QReg.of ((uBatchSpec P In).Out ik × E))) (k : ℕ) :
    (queryBind ik E e next).IsWidthBound k ↔
      ik.2 ≤ k ∧ ∀ r, (next r).IsWidthBound k := by
  refine (IFreeM.isRollBound_liftBind_iff (P := toIPFunctor L (uBatchSpec P In))
    (canRoll := fun _ c n ↦ c.pointCharge ≤ n) (cost := fun _ _ n ↦ n)
    (.query ik E e) (onDown next) k).trans ?_
  exact and_congr_right' ULift.forall

/-- A local operation satisfies every width cap. -/
@[simp]
theorem isWidthBound_prim (o : L.Op A) (k : ℕ) :
    (prim (spec := uBatchSpec P In) o).IsWidthBound k := by
  simp [prim]

/-- A single batch satisfies the width cap exactly when its width does. -/
@[simp]
theorem isWidthBound_query_iff (ik : P × ℕ) (E : QReg)
    (e : A ≃ (uBatchSpec P In).In ik × E) (k : ℕ) :
    (query (L := L) ik E e).IsWidthBound k ↔ ik.2 ≤ k := by
  simp [query]

/-- A width cap may be increased. -/
theorem IsWidthBound.mono {x : QuantumComp L (uBatchSpec P In) X A} {k k' : ℕ}
    (hx : x.IsWidthBound k) (hkk' : k ≤ k') : x.IsWidthBound k' :=
  IFreeM.IsRollBound.mono_of_rel (· ≤ ·) (fun _ _ _ _ h hc ↦ hc.trans h)
    (fun _ _ _ _ h _ ↦ h) hx hkk'

/-- Sequencing preserves a shared width cap. -/
theorem IsWidthBound.bind {x : QuantumComp L (uBatchSpec P In) X A}
    {next : ∀ B, X B → QuantumComp L (uBatchSpec P In) Y B} {k : ℕ}
    (hx : x.IsWidthBound k) (hn : ∀ B a, (next B a).IsWidthBound k) :
    (x.bind next).IsWidthBound k := by
  rw [bind_eq_iFreeM_bind]
  have h := IFreeM.isRollBound_bind (P := toIPFunctor L (uBatchSpec P In)) max
    (canRoll := fun _ c n ↦ Cmd.pointCharge c ≤ n) (cost := fun _ _ n ↦ n)
    (fun _ _ _ _ _ hc ↦ ⟨hc.trans (Nat.le_max_right _ _), hc.trans (Nat.le_max_left _ _)⟩)
    (fun _ _ _ _ _ _ ↦ ⟨rfl, rfl⟩) hx hn
  simpa only [IsWidthBound, max_self] using h

/-- A total point budget bounds the width of every individual round on every branch. -/
theorem IsPointBound.isWidthBound {x : QuantumComp L (uBatchSpec P In) X A} {n : ℕ}
    (hx : x.IsPointBound n) : x.IsWidthBound n := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => exact isWidthBound_pure _ _
  | primBind _ o next ih =>
      rw [isPointBound_primBind_iff] at hx
      rw [isWidthBound_primBind_iff]
      exact fun b ↦ ih b (hx b)
  | queryBind _ ik E e next ih =>
      rw [isPointBound_queryBind_iff] at hx
      rw [isWidthBound_queryBind_iff]
      exact ⟨hx.1, fun r ↦ (ih r (hx.2 r)).mono (Nat.sub_le _ _)⟩

/-- A width cap and a total round bound imply a point bound on every adaptive branch. -/
theorem IsTotalQueryBound.isPointBound {x : QuantumComp L (uBatchSpec P In) X A}
    {r k : ℕ} (hr : x.IsTotalQueryBound r) (hw : x.IsWidthBound k) :
    x.IsPointBound (k * r) := by
  induction x using QuantumComp.inductionOn generalizing r with
  | pure _ a => exact isPointBound_pure a _
  | primBind _ o next ih =>
      rw [isTotalQueryBound_primBind_iff] at hr
      rw [isWidthBound_primBind_iff] at hw
      exact (isPointBound_primBind_iff o next _).mpr fun b ↦ ih b (hr b) (hw b)
  | queryBind _ ik E e next ih =>
      rw [isTotalQueryBound_queryBind_iff] at hr
      rw [isWidthBound_queryBind_iff] at hw
      have hbudget : k * (r - 1) + ik.2 ≤ k * r := by
        calc
          _ ≤ k * (r - 1) + k := Nat.add_le_add_left hw.1 _
          _ = k * r := by rw [← Nat.mul_succ]; congr 1; omega
      refine (isPointBound_queryBind_iff ik E e next _).mpr
        ⟨le_trans (Nat.le_add_left _ _) hbudget, fun b ↦ ?_⟩
      exact (ih b (hr.2 b) (hw.2 b)).mono (Nat.le_sub_of_add_le hbudget)

end QuantumComp
end Quantum
