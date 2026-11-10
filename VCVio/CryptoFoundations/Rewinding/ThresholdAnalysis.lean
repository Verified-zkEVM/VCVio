/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.ThresholdSound
public import VCVio.CryptoFoundations.Rewinding.ThresholdEager
public import VCVio.CryptoFoundations.Rewinding.ThresholdStep
public import VCVio.CryptoFoundations.Rewinding.ThresholdBounds

/-!
# Counted semantics of recursive threshold extraction

The complete-run counter records only acceptance-oracle queries. Each recursive node composes
independent counted child attempts, preserving both their successes and their costs.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Rewinding

/-- Interpreting a threshold finder counts each acceptance call and leaves sampling free. -/
theorem simulateQ_counted_thresholdFinderWithPools (n : ℕ) (C : Fin n → Type)
    (k : Fin n → ℕ) (pools : (i : Fin n) → List (C i)) (f : ((i : Fin n) → C i) → Bool) :
    simulateQ (coins (S := ℕ) + counted f) (thresholdFinderWithPools n C k pools) =
      thresholdProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n C k pools (counted f) := by
  rw [simulateQ_thresholdFinderWithPools]
  rfl

/-- Starting a recursive attempt with an offset adds that offset to its final cost. -/
theorem thresholdProgram_counted_run (n : ℕ) (C : Fin n → Type)
    (k : Fin n → ℕ) (pools : (i : Fin n) → List (C i))
    (f : ((i : Fin n) → C i) → Bool) (count : ℕ) :
    (thresholdProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n C k pools
      (counted f)).run count =
      (fun z => (z.1, count + z.2)) <$> runFinder (thresholdFinderWithPools n C k pools) f := by
  rw [← simulateQ_counted_thresholdFinderWithPools]
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm, runFinder] using
    counted_run_add f (thresholdFinderWithPools n C k pools) 0 count

/-- The counted successor round is a threshold step over independently counted child attempts.
-/
theorem runFinder_thresholdFinderWithPools_succ (n : ℕ) (C : Fin (n + 1) → Type)
    (k : Fin (n + 1) → ℕ) (pools : (i : Fin (n + 1)) → List (C i))
    (f : ((i : Fin (n + 1)) → C i) → Bool) :
    runFinder (thresholdFinderWithPools (n + 1) C k pools) f =
      (fun z => (z.1.bind assembleChildren, z.2)) <$>
        (thresholdChildren (fun j => StateT.lift (ProbComp.uniformFin j))
          (chargedChild (fun c =>
            (fun z => (z.1.map (fun t => (c, t)), z.2)) <$>
              runFinder (thresholdFinderWithPools n (fun i => C i.succ)
                (fun i => k i.succ) (fun i => pools i.succ)) (fun q => f (Fin.cons c q))))
          (k 0) (pools 0)).run 0 := by
  rw [runFinder, simulateQ_counted_thresholdFinderWithPools, thresholdProgram]
  have hchild : (fun c => do
      let t ← thresholdProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n
        (fun i => C i.succ) (fun i => k i.succ) (fun i => pools i.succ)
        (fun q => counted f (Fin.cons c q))
      pure (t.map (fun t => (c, t)))) =
      chargedChild (fun c =>
        (fun z => (z.1.map (fun t => (c, t)), z.2)) <$>
          runFinder (thresholdFinderWithPools n (fun i => C i.succ)
            (fun i => k i.succ) (fun i => pools i.succ)) (fun q => f (Fin.cons c q))) := by
    funext c
    apply StateT.ext
    intro count
    change ((do
      let t ← thresholdProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n
        (fun i => C i.succ) (fun i => k i.succ) (fun i => pools i.succ)
        (counted (fun q => f (Fin.cons c q)))
      pure (t.map (fun t => (c, t)))) : StateT ℕ ProbComp _).run count = _
    rw [StateT.run_bind, thresholdProgram_counted_run]
    simp only [chargedChild, StateT.run_mk, StateT.run_pure,
      bind_pure_comp, Functor.map_map]
  rw [hchild]
  simp only [bind_pure_comp, StateT.run_map]

/-- Successful stateful threshold attempts return exactly the requested number of children. -/
theorem length_thresholdChildren_run {C W : Type}
    (sample : (j : ℕ) → ProbComp (Fin (j + 1))) (child : C → StateT ℕ ProbComp (Option W))
    (k : ℕ) (pool : List C) (count : ℕ) (z : Option (List W) × ℕ)
    (hz : z ∈ support
      ((thresholdChildren (fun j => StateT.lift (sample j)) child k pool).run count))
    (ws : List W) (hws : z.1 = some ws) : ws.length = k := by
  cases k with
  | zero =>
    simp only [thresholdChildren, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    simpa using hws.symm
  | succ r =>
    cases pool with
    | nil =>
      simp only [thresholdChildren, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      simp at hws
    | cons c cs =>
      simp only [thresholdChildren, StateT.run_bind, StateT.run_lift,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨i, _, v, _, hz⟩ := hz
      cases hv : v.1 with
      | none =>
        simp only [hv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst z
        simp at hws
      | some w =>
        simp only [hv, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨tail, _, hz⟩ := hz
        subst z
        split at hws
        next h =>
          simp only [Option.some.injEq] at hws
          subst ws
          simpa using h
        next h => simp at hws

/-- Assembling a correctly sized child list preserves whether an attempt succeeded. -/
theorem prEvent_assembleChildren {n : ℕ} {C : Fin (n + 1) → Type}
    {k : Fin (n + 1) → ℕ}
    (mx : ProbComp (Option (List
      (C 0 × VecTree (fun i : Fin n => C i.succ) (fun i => k i.succ))) × ℕ))
    (hlen : ∀ z ∈ support mx, ∀ ws, z.1 = some ws → ws.length = k 0) :
    Pr{let z ← (fun z => (z.1.bind assembleChildren, z.2)) <$> mx}[z.1.isSome] =
      Pr{let z ← mx}[z.1.isSome] := by
  rw [prEvent_map]
  apply prEvent_congr_of_support
  intro z hz
  cases h : z.1 with
  | none => simp
  | some ws => simp [assembleChildren, hlen z hz ws h]

/-- The executable challenge pool lists exactly the finite challenge set. -/
theorem toFinset_challengePool (C : Type) [SampleableType C] [DecidableEq C] [Fintype C] :
    (challengePool C).toFinset = Finset.univ := by
  ext c
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_challengePool c

/-- The executable challenge pool has the cardinality of its challenge type. -/
theorem length_challengePool (C : Type) [SampleableType C] [DecidableEq C] [Fintype C] :
    (challengePool C).length = Fintype.card C := by
  rw [← List.toFinset_card_of_nodup (nodup_challengePool C), toFinset_challengePool]
  rfl

/-- Summing over the executable challenge pool is the finite sum over all challenges. -/
theorem sum_challengePool {C M : Type} [SampleableType C] [DecidableEq C] [Fintype C]
    [AddCommMonoid M] (g : C → M) :
    ((challengePool C).map g).sum = ∑ c, g c := by
  rw [← List.sum_toFinset g (nodup_challengePool C), toFinset_challengePool]

end Rewinding
