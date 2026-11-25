/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Weighted

/-! # Weighted query-bound regressions

Two copies of the uniform oracle give two kinds independently of their query arguments.
The handler test charges three target queries for the left kind and none for the right. A query
with no possible answer separates the weighted budget from the completed-path bound.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.WeightedQueryBound

universe u

/-- Two left queries and one right query cost at most twice the left cost plus the right cost. -/
theorem two_kind_cost_bound (c : Bool → ℕ) :
    let A : OracleComp (unifSpec + unifSpec) Unit := do
      let _ ← (unifSpec + unifSpec).query (.inl 1)
      let _ ← (unifSpec + unifSpec).query (.inr 2)
      let _ ← (unifSpec + unifSpec).query (.inl 3)
      pure ()
    WorstCaseCostBound A ⟨fun t => c (t.isLeft)⟩ (c true * 2 + c false) := by
  dsimp only
  have h := worstCaseCostBound_of_per_kind (spec := unifSpec + unifSpec)
    Sum.isLeft c (fun k => if k then 2 else 1)
    (oa := do
      let _ ← (unifSpec + unifSpec).query (.inl 1)
      let _ ← (unifSpec + unifSpec).query (.inr 2)
      let _ ← (unifSpec + unifSpec).query (.inl 3)
      pure ()) (by intro k; cases k <;> simp)
  simpa [Fintype.sum_bool, Nat.add_comm] using h

/-- A stateful handler spends three queries on the left kind and zero on the right kind. -/
theorem three_zero_handler_bound :
    let h : QueryImpl (unifSpec + unifSpec) (StateT ℕ (OracleComp unifSpec)) :=
      ⟨fun t s => match t with
      | .inl n => do
        let a ← unifSpec.query n
        let _ ← unifSpec.query 0
        let _ ← unifSpec.query 0
        pure (a, s + 1)
      | .inr n => pure ((0 : Fin (n + 1)), s)⟩
    let A : OracleComp (unifSpec + unifSpec) Unit := do
      let _ ← (unifSpec + unifSpec).query (.inl 1)
      let _ ← (unifSpec + unifSpec).query (.inr 2)
      let _ ← (unifSpec + unifSpec).query (.inl 3)
      pure ()
    IsQueryBoundP ((simulateQ h A).run 7) (fun _ => True) 6 := by
  dsimp only
  refine (isQueryBoundP_iff_isChargeBound _ _ _).2 <| isChargeBound_run_simulateQ
    (c := fun t => if t.isLeft then 3 else 0)
    (fun t s => (isQueryBoundP_iff_isChargeBound _ _ _).1 ?_) ?_ 7
  · rcases t with n | n <;> simp [StateT.run]
  · have h := isChargeBound_of_per_kind (spec := unifSpec + unifSpec)
      Sum.isLeft (fun k => if k then 3 else 0) (fun k => if k then 2 else 1)
      (oa := do
        let _ ← (unifSpec + unifSpec).query (.inl 1)
        let _ ← (unifSpec + unifSpec).query (.inr 2)
        let _ ← (unifSpec + unifSpec).query (.inl 3)
        pure ()) (by intro k; cases k <;> simp)
    convert h using 1
    simp

/-- Indicator charges recover the unit-step stateful transfer, with no answer assumptions. -/
theorem unit_weight_transfer {ι ι' : Type u} {spec : OracleSpec.{u, u} ι}
    {spec' : OracleSpec.{u, u} ι'} {α σ : Type u}
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {A : OracleComp spec α} {n : ℕ}
    (hA : IsQueryBoundP A p n)
    (hp : ∀ t, p t → ∀ s, IsQueryBoundP ((impl t).run s) q 1)
    (hnp : ∀ t, ¬ p t → ∀ s, IsQueryBoundP ((impl t).run s) q 0) (s : σ) :
    IsQueryBoundP ((simulateQ impl A).run s) q n := by
  rw [isQueryBoundP_iff_isChargeBound] at hA ⊢
  refine isChargeBound_run_simulateQ (fun t st => ?_) hA s
  rw [← isQueryBoundP_iff_isChargeBound]
  by_cases ht : p t
  · simpa [ht] using hp t ht st
  · simpa [ht] using hnp t ht st

/-- A query with no possible answer completes no path, so its worst-case cost is `0`, but it still
spends its weight: the weighted budget `0` fails. So `WorstCaseCostBound` does not supply the
weighted premise of `isChargeBound_run_simulateQ`. -/
theorem empty_answer_separates :
    let spec : OracleSpec Unit := fun _ => Empty
    let A : OracleComp spec Unit := do
      let _ ← spec.query ()
      pure ()
    WorstCaseCostBound A ⟨fun _ => 1⟩ 0 ∧
      ¬ PFunctor.FreeM.IsChargeBound A (fun _ => 1) 0 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [worstCaseCostBound_query_bind_iff]
    intro a
    exact a.elim
  · rw [PFunctor.FreeM.isChargeBound_iff_isRollBound_nat, ← isQueryBound_iff_isRollBound,
      isQueryBound_query_bind_iff]
    simp

end VCVioTest.WeightedQueryBound
