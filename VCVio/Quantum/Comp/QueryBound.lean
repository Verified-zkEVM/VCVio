/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Runtime

/-!
# Query budgets and operation costs of quantum programs

A program `x` has query budget `b : spec.Port → ℕ` when, along every path of its tree and on
every branch, it calls each port `i` at most `b i` times. The budget is a property of the tree,
not a type index: the number of calls may depend on classical outcomes, and only its worst case
over paths is bounded.

A cost function `c` on the local operations of a signature (for a gate set, `c o = 1` for every
gate) bounds the cost of a program in the same way: `x.IsCostBound c n` says that along every
path, the costs of the local operations add up to at most `n`. Costs are read off the tree and do
not depend on an interpretation.

Paths include branches that are reached with weight zero, so both bounds are syntactic, and they
hold against every interpretation and every runtime.

## Implementation note

PolyFun's `PFunctor.FreeM.IsRollBound` bounds the commands of the non-indexed free monad
`PFunctor.FreeM`. Programs are trees of the indexed free monad `IPFunctor.IFreeM`, so
`IsRollBound` does not apply directly; transporting through `IFreeM.toSigmaFreeM` would carry
the indices of the leaves through every statement. The bounds are therefore defined by recursion
on the tree, the query budget one port at a time (`Quantum.QuantumComp.IsQueryBoundAt`).
Counting one port at a time needs no decidable equality on ports.

## Main definitions

* `Quantum.QuantumComp.IsQueryBoundAt x i n`: every path of `x` calls port `i` at most `n`
  times.
* `Quantum.QuantumComp.IsQueryBound x b`: every path of `x` calls each port `i` at most `b i`
  times.
* `Quantum.QuantumComp.IsCostBound c x n`: along every path of `x`, the costs `c o` of the local
  operations add up to at most `n`.

## Main statements

* `IsQueryBound.mono`, `isQueryBound_pure`, `isQueryBound_primBind_iff`, `isQueryBound_query_iff`
  and `IsQueryBound.bind` (budgets add under sequencing), with the fixed-register forms
  `QuantumComp₂.isQueryBound_bind` and, for programs over instruments, `QComp.isQueryBound_act`.
* `IsCostBound.mono` and `IsCostBound.bind` (costs add under sequencing).
* `Quantum.QuantumRuntime.run_congr_of_isQueryBound`: two runtimes on the same register whose
  steps agree on every port with a nonzero budget run a program within that budget to the same
  dependent subinstrument; `outcomeLaw_congr_of_isQueryBound`: from the same initial substate,
  the outcome laws agree.
-/

public section

open IPFunctor

universe u v u₁ v₁ w w₁

namespace Quantum

namespace QuantumComp

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {X : QReg → Type w}
  {Y : QReg → Type w₁} {A : QReg}

/-! ## Budgets on one port -/

/-- Every path of the tree calls port `i` at most `n` times. -/
@[expose]
def isQueryBoundAtAux (i : spec.Port) :
    {A : QReg} → IFreeM (toIPFunctor L spec) X A → ℕ → Prop
  | _, .pure _, _ => True
  | _, .liftBind (.prim _) k, n => ∀ b, isQueryBoundAtAux i (k (ULift.up b)) n
  | _, .liftBind (.query j _ _) k, n =>
      (j = i → 0 < n ∧ ∀ r, isQueryBoundAtAux i (k (ULift.up r)) (n - 1)) ∧
        (j ≠ i → ∀ r, isQueryBoundAtAux i (k (ULift.up r)) n)

/-- Every path of `x`, including paths reached with weight zero, calls port `i` at most `n`
times. -/
@[expose]
def IsQueryBoundAt (x : QuantumComp L spec X A) (i : spec.Port) (n : ℕ) : Prop :=
  isQueryBoundAtAux i x n

/-- A program that stops at once makes no call. -/
@[simp]
theorem isQueryBoundAt_pure (x : X A) (i : spec.Port) (n : ℕ) :
    (QuantumComp.pure x : QuantumComp L spec X A).IsQueryBoundAt i n :=
  trivial

/-- A local operation followed by a continuation is bounded when every continuation is. -/
@[simp]
theorem isQueryBoundAt_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)) (i : spec.Port) (n : ℕ) :
    (primBind o k).IsQueryBoundAt i n ↔ ∀ b, (k b).IsQueryBoundAt i n :=
  Iff.rfl

/-- A call of port `j` followed by a continuation: if `j = i` it uses one unit of the budget,
and the continuations must fit in the rest. -/
theorem isQueryBoundAt_queryBind_iff (j : spec.Port) (E : QReg) (ℓ : A ≃ spec.In j × E)
    (k : spec.Result j → QuantumComp L spec X (QReg.of (spec.Out j × E))) (i : spec.Port)
    (n : ℕ) :
    (queryBind j E ℓ k).IsQueryBoundAt i n ↔
      (j = i → 0 < n ∧ ∀ r, (k r).IsQueryBoundAt i (n - 1)) ∧
        (j ≠ i → ∀ r, (k r).IsQueryBoundAt i n) :=
  Iff.rfl

/-- A budget on one port can be enlarged. -/
theorem IsQueryBoundAt.mono {x : QuantumComp L spec X A} {i : spec.Port} {n m : ℕ}
    (hx : x.IsQueryBoundAt i n) (hnm : n ≤ m) : x.IsQueryBoundAt i m := by
  induction x using QuantumComp.inductionOn generalizing n m with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (hx b) hnm
  | queryBind _ j E ℓ k ih =>
    rw [isQueryBoundAt_queryBind_iff] at hx ⊢
    exact ⟨fun hj ↦ ⟨lt_of_lt_of_le (hx.1 hj).1 hnm, fun r ↦ ih r ((hx.1 hj).2 r)
      (Nat.sub_le_sub_right hnm 1)⟩, fun hj r ↦ ih r (hx.2 hj r) hnm⟩

/-- Budgets on one port add under sequencing. -/
theorem IsQueryBoundAt.bind {x : QuantumComp L spec X A} {k : ∀ u, X u → QuantumComp L spec Y u}
    {i : spec.Port} {n m : ℕ} (hx : x.IsQueryBoundAt i n)
    (hk : ∀ u y, (k u y).IsQueryBoundAt i m) : (x.bind k).IsQueryBoundAt i (n + m) := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ y => exact (hk _ y).mono (Nat.le_add_left m n)
  | primBind _ o k' ih => exact fun b ↦ ih b (hx b)
  | queryBind _ j E ℓ k' ih =>
    rw [isQueryBoundAt_queryBind_iff] at hx
    rw [queryBind_bind, isQueryBoundAt_queryBind_iff]
    refine ⟨fun hj ↦ ⟨Nat.add_pos_left (hx.1 hj).1 m, fun r ↦ ?_⟩,
      fun hj r ↦ ih r (hx.2 hj r)⟩
    rw [Nat.sub_add_comm (hx.1 hj).1]
    exact ih r ((hx.1 hj).2 r)

/-! ## Budgets on all ports -/

/-- **Query budget.** Every path of `x`, including paths reached with weight zero, calls each
port `i` at most `b i` times. -/
@[expose]
def IsQueryBound (x : QuantumComp L spec X A) (b : spec.Port → ℕ) : Prop :=
  ∀ i, x.IsQueryBoundAt i (b i)

/-- A budget can be enlarged. -/
theorem IsQueryBound.mono {x : QuantumComp L spec X A} {b b' : spec.Port → ℕ}
    (hx : x.IsQueryBound b) (hb : b ≤ b') : x.IsQueryBound b' :=
  fun i ↦ (hx i).mono (hb i)

/-- A program that stops at once has every budget. -/
@[simp]
theorem isQueryBound_pure (x : X A) (b : spec.Port → ℕ) :
    (QuantumComp.pure x : QuantumComp L spec X A).IsQueryBound b :=
  fun _ ↦ trivial

/-- A local operation followed by a continuation is within a budget when every continuation
is. -/
@[simp]
theorem isQueryBound_primBind_iff (o : L.Op A)
    (k : (c : L.Outcome o) → QuantumComp L spec X (L.next o c)) (b : spec.Port → ℕ) :
    (primBind o k).IsQueryBound b ↔ ∀ c, (k c).IsQueryBound b :=
  forall_comm

/-- The generic local operation has every budget. -/
@[simp]
theorem isQueryBound_prim (o : L.Op A) (b : spec.Port → ℕ) :
    (prim (spec := spec) o).IsQueryBound b :=
  fun _ _ ↦ trivial

/-- A single call of port `i` is within a budget exactly when the budget of `i` is nonzero. -/
@[simp]
theorem isQueryBound_query_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (b : spec.Port → ℕ) : (query (L := L) i E ℓ).IsQueryBound b ↔ 0 < b i :=
  ⟨fun h ↦ ((h i).1 rfl).1, fun h _ ↦
    ⟨fun hij ↦ ⟨hij ▸ h, fun _ ↦ trivial⟩, fun _ _ ↦ trivial⟩⟩

/-- Budgets add under sequencing. -/
theorem IsQueryBound.bind {x : QuantumComp L spec X A} {k : ∀ u, X u → QuantumComp L spec Y u}
    {b₁ b₂ : spec.Port → ℕ} (hx : x.IsQueryBound b₁) (hk : ∀ u y, (k u y).IsQueryBound b₂) :
    (x.bind k).IsQueryBound (b₁ + b₂) :=
  fun i ↦ (hx i).bind fun u y ↦ hk u y i

/-- A call of port `i` followed by continuations within a budget `b` uses part of the budget of
`i`: the budget of `i` is nonzero, and the continuations are within `b`. -/
theorem IsQueryBound.of_queryBind {i : spec.Port} {E : QReg} {ℓ : A ≃ spec.In i × E}
    {k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))} {b : spec.Port → ℕ}
    (h : (queryBind i E ℓ k).IsQueryBound b) : 0 < b i ∧ ∀ r, (k r).IsQueryBound b := by
  have h' := fun j ↦ (isQueryBoundAt_queryBind_iff i E ℓ k j (b j)).mp (h j)
  refine ⟨((h' i).1 rfl).1, fun r j ↦ ?_⟩
  by_cases hij : i = j
  · subst hij
    exact (((h' i).1 rfl).2 r).mono (Nat.sub_le _ 1)
  · exact (h' j).2 hij r

/-- A call of port `i` followed by continuations is within the budget `b` exactly when the
budget of `i` is nonzero and the continuations are within `b` with one call of `i` spent. -/
theorem isQueryBound_queryBind_iff [DecidableEq spec.Port] (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))) (b : spec.Port → ℕ) :
    (queryBind i E ℓ k).IsQueryBound b ↔
      0 < b i ∧ ∀ r, (k r).IsQueryBound (Function.update b i (b i - 1)) := by
  constructor
  · intro h
    have h' := fun j ↦ (isQueryBoundAt_queryBind_iff i E ℓ k j (b j)).mp (h j)
    refine ⟨((h' i).1 rfl).1, fun r j ↦ ?_⟩
    by_cases hij : j = i
    · subst hij
      rw [Function.update_self]
      exact ((h' j).1 rfl).2 r
    · rw [Function.update_of_ne hij]
      exact (h' j).2 (Ne.symm hij) r
  · rintro ⟨hb, hk⟩ j
    refine (isQueryBoundAt_queryBind_iff i E ℓ k j (b j)).mpr ⟨fun hij ↦ ?_, fun hij r ↦ ?_⟩
    · subst hij
      exact ⟨hb, fun r ↦ by simpa using hk r i⟩
    · simpa [Function.update_of_ne (Ne.symm hij)] using hk r j

/-! ## Costs of local operations -/

/-- Along every path of the tree, the costs of the local operations add up to at most `n`. -/
@[expose]
def isCostBoundAux (c : ∀ ⦃A : QReg⦄, L.Op A → ℕ) :
    {A : QReg} → IFreeM (toIPFunctor L spec) X A → ℕ → Prop
  | _, .pure _, _ => True
  | _, .liftBind (.prim o) k, n => c o ≤ n ∧ ∀ b, isCostBoundAux c (k (ULift.up b)) (n - c o)
  | _, .liftBind (.query _ _ _) k, n => ∀ r, isCostBoundAux c (k (ULift.up r)) n

/-- **Cost bound.** Along every path of `x`, including paths reached with weight zero, the costs
`c o` of the local operations add up to at most `n`. With `c o = 1` for every operation of a
gate set, this bounds the number of gates. -/
@[expose]
def IsCostBound (c : ∀ ⦃A : QReg⦄, L.Op A → ℕ) (x : QuantumComp L spec X A) (n : ℕ) : Prop :=
  isCostBoundAux c x n

variable {c : ∀ ⦃A : QReg⦄, L.Op A → ℕ}

/-- A program that stops at once costs nothing. -/
@[simp]
theorem isCostBound_pure (x : X A) (n : ℕ) :
    (QuantumComp.pure x : QuantumComp L spec X A).IsCostBound c n :=
  trivial

/-- A local operation followed by a continuation costs at most `n` when the operation costs at
most `n` and every continuation fits in the rest. -/
@[simp]
theorem isCostBound_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)) (n : ℕ) :
    (primBind o k).IsCostBound c n ↔ c o ≤ n ∧ ∀ b, (k b).IsCostBound c (n - c o) :=
  Iff.rfl

/-- A call followed by a continuation costs what its continuations cost. -/
@[simp]
theorem isCostBound_queryBind_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))) (n : ℕ) :
    (queryBind i E ℓ k).IsCostBound c n ↔ ∀ r, (k r).IsCostBound c n :=
  Iff.rfl

/-- The generic local operation `o` costs at most `c o`. -/
theorem isCostBound_prim (o : L.Op A) : (prim (spec := spec) o).IsCostBound c (c o) :=
  ⟨le_rfl, fun _ ↦ trivial⟩

/-- A call costs nothing. -/
theorem isCostBound_query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) (n : ℕ) :
    (query (L := L) i E ℓ).IsCostBound c n :=
  fun _ ↦ trivial

/-- A cost bound can be enlarged. -/
theorem IsCostBound.mono {x : QuantumComp L spec X A} {n m : ℕ} (hx : x.IsCostBound c n)
    (hnm : n ≤ m) : x.IsCostBound c m := by
  induction x using QuantumComp.inductionOn generalizing n m with
  | pure _ _ => trivial
  | primBind _ o k ih =>
    exact ⟨hx.1.trans hnm, fun b ↦ ih b (hx.2 b) (Nat.sub_le_sub_right hnm _)⟩
  | queryBind _ i E ℓ k ih => exact fun r ↦ ih r (hx r) hnm

/-- **Costs add under sequencing.** -/
theorem IsCostBound.bind {x : QuantumComp L spec X A} {k : ∀ u, X u → QuantumComp L spec Y u}
    {n m : ℕ} (hx : x.IsCostBound c n) (hk : ∀ u y, (k u y).IsCostBound c m) :
    (x.bind k).IsCostBound c (n + m) := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ y => exact (hk _ y).mono (Nat.le_add_left m n)
  | primBind _ o k' ih =>
    refine ⟨hx.1.trans (Nat.le_add_right n m), fun b ↦ ?_⟩
    rw [Nat.sub_add_comm hx.1]
    exact ih b (hx.2 b)
  | queryBind _ i E ℓ k' ih => exact fun r ↦ ih r (hx r)

end QuantumComp

/-! ## Fixed-register programs and programs over instruments -/

namespace QuantumComp₂

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {A B C : QReg} {α : Type w}
  {β : Type w₁}

/-- A program that returns at once has every budget. -/
@[simp]
theorem isQueryBound_pure (a : α) (b : spec.Port → ℕ) :
    (QuantumComp₂.pure a : QuantumComp₂ L spec A A α).IsQueryBound b :=
  fun _ ↦ trivial

/-- A single call of port `i` is within a budget exactly when the budget of `i` is nonzero. -/
@[simp]
theorem isQueryBound_query_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (b : spec.Port → ℕ) : (query (L := L) i E ℓ).IsQueryBound b ↔ 0 < b i :=
  QuantumComp.isQueryBound_query_iff i E ℓ b

/-- Budgets on one port add under sequencing of fixed-register programs. -/
theorem isQueryBoundAt_bind {x : QuantumComp₂ L spec A B α} {k : α → QuantumComp₂ L spec B C β}
    {i : spec.Port} {n m : ℕ} (hx : x.IsQueryBoundAt i n) (hk : ∀ a, (k a).IsQueryBoundAt i m) :
    (x.bind k).IsQueryBoundAt i (n + m) :=
  QuantumComp.IsQueryBoundAt.bind hx fun _ ⟨h, a⟩ ↦ by
    subst h
    exact hk a

/-- Budgets add under sequencing of fixed-register programs. -/
theorem isQueryBound_bind {x : QuantumComp₂ L spec A B α} {k : α → QuantumComp₂ L spec B C β}
    {b₁ b₂ : spec.Port → ℕ} (hx : x.IsQueryBound b₁) (hk : ∀ a, (k a).IsQueryBound b₂) :
    (x.bind k).IsQueryBound (b₁ + b₂) :=
  fun i ↦ isQueryBoundAt_bind (hx i) fun a ↦ hk a i

/-- Costs add under sequencing of fixed-register programs. -/
theorem isCostBound_bind {c : ∀ ⦃A : QReg⦄, L.Op A → ℕ} {x : QuantumComp₂ L spec A B α}
    {k : α → QuantumComp₂ L spec B C β} {n m : ℕ} (hx : x.IsCostBound c n)
    (hk : ∀ a, (k a).IsCostBound c m) : (x.bind k).IsCostBound c (n + m) :=
  QuantumComp.IsCostBound.bind hx fun _ ⟨h, a⟩ ↦ by
    subst h
    exact hk a

end QuantumComp₂

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {A B C : QReg} {α β : Type w}

/-- A local subinstrument followed by a continuation is bounded on port `i` when every
continuation is. -/
@[simp]
theorem isQueryBoundAt_act_bind_iff (p : SubInstrument A B β) (k : β → QComp spec B C α)
    (i : spec.Port) (n : ℕ) :
    ((act p).bind k).IsQueryBoundAt i n ↔ ∀ b, (k b).IsQueryBoundAt i n :=
  Iff.rfl

/-- A local subinstrument has every budget. -/
@[simp]
theorem isQueryBound_act (p : SubInstrument A B α) (b : spec.Port → ℕ) :
    (act (spec := spec) p).IsQueryBound b :=
  fun _ _ ↦ trivial

/-- A local subinstrument followed by a continuation is within a budget when every
continuation is. -/
@[simp]
theorem isQueryBound_act_bind_iff (p : SubInstrument A B β) (k : β → QComp spec B C α)
    (b : spec.Port → ℕ) : ((act p).bind k).IsQueryBound b ↔ ∀ c, (k c).IsQueryBound b :=
  forall_comm

end QComp

/-! ## Unused ports -/

namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A B : QReg} {α : Type w}

/-- **Unused ports do not matter.** Two runtimes on the same register whose steps agree on every
port with a nonzero budget run every program within that budget to the same dependent
subinstrument. The initial substates may differ: `run` does not read them. -/
theorem run_congr_of_isQueryBound {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (hs : ∀ i, b i ≠ 0 → s₁ i = s₂ i) :
    (QuantumRuntime.mk D σ₁ s₁).run I x = (QuantumRuntime.mk D σ₂ s₂).run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [QuantumComp.isQueryBound_primBind_iff] at hx
    rw [run_primBind, run_primBind]
    exact congrArg _ (funext fun c ↦ ih c (hx c))
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hb, hk⟩ := hx.of_queryBind
    rw [run_queryBind, run_queryBind]
    have hstep : (QuantumRuntime.mk D σ₁ s₁).queryStep i E ℓ =
        (QuantumRuntime.mk D σ₂ s₂).queryStep i E ℓ := by
      simp only [queryStep, hs i hb.ne']
    rw [hstep]
    exact congrArg _ (funext fun r ↦ ih r (hk r))

/-- **Unused ports do not matter**, for fixed-register programs: the two runtimes run the program
to the same subinstrument. -/
theorem run₂_congr_of_isQueryBound {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {x : QuantumComp₂ L spec A B α} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (hs : ∀ i, b i ≠ 0 → s₁ i = s₂ i) :
    (QuantumRuntime.mk D σ₁ s₁).run₂ I x = (QuantumRuntime.mk D σ₂ s₂).run₂ I x :=
  SubInstrument.toD_injective <| by
    rw [toD_run₂, toD_run₂, run_congr_of_isQueryBound I hx hs]

/-- Two runtimes with the same initial substate whose steps agree on every port with a nonzero
budget give every program within that budget the same outcome law. -/
theorem outcomeLaw_congr_of_isQueryBound [MeasurableSpace (Σ u, X u)] {D : QReg}
    {σ : SubState D} {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (hs : ∀ i, b i ≠ 0 → s₁ i = s₂ i) (ρ : SubState A) :
    (QuantumRuntime.mk D σ s₁).outcomeLaw I x ρ = (QuantumRuntime.mk D σ s₂).outcomeLaw I x ρ :=
  congrArg (fun p ↦ DSubInstrument.outcomeMeasure p (ρ.prod σ))
    (run_congr_of_isQueryBound (σ₁ := σ) (σ₂ := σ) I hx hs)

/-- Two runtimes with the same initial substate whose steps agree on every port with a nonzero
budget give every fixed-register program within that budget the same outcome law. -/
theorem outcomeLaw₂_congr_of_isQueryBound [MeasurableSpace α] {D : QReg} {σ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {x : QuantumComp₂ L spec A B α} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (hs : ∀ i, b i ≠ 0 → s₁ i = s₂ i) (ρ : SubState A) :
    (QuantumRuntime.mk D σ s₁).outcomeLaw₂ I x ρ = (QuantumRuntime.mk D σ s₂).outcomeLaw₂ I x ρ :=
  congrArg (fun p ↦ SubInstrument.outcomeMeasure p (ρ.prod σ))
    (run₂_congr_of_isQueryBound (σ₁ := σ) (σ₂ := σ) I hx hs)

end QuantumRuntime

end Quantum
