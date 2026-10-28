/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.ThresholdSound
public import VCVio.CryptoFoundations.Rewinding.ThresholdAnalysis
public import VCVio.CryptoFoundations.Rewinding.ThresholdStep
meta import VCVio.CryptoFoundations.Rewinding.ThresholdSound
import VCVio.OracleComp.RunIO
meta import VCVio.OracleComp.RunIO

/-!
# One-round threshold extraction regression

A binary fork on three challenges accepts exactly challenges zero and one. The tree finder
returns two distinct accepting challenges whenever it succeeds, and every inspected challenge
is charged, including an initial rejection.
-/

public section

open OracleComp OracleSpec Rewinding

namespace VCVioTest.ThresholdFinder

/-- One round has three possible verifier challenges. -/
abbrev challenges (_ : Fin 1) := Fin 3

/-- Each fork requires two different accepting challenges. -/
abbrev branching (_ : Fin 1) : ℕ := 2

/-- The executable challenge pool in the unique round. -/
@[expose] def pools (_ : Fin 1) : List (Fin 3) := [0, 1, 2]

/-- Exactly the first two challenges accept. -/
@[expose] def accepts (q : (i : Fin 1) → challenges i) : Bool := decide (q 0 ≠ 2)

/-- The actual recursive challenge-tree finder on the explicit three-element pool. -/
@[expose] def finder := thresholdFinderWithPools 1 challenges branching pools

/-- The finder together with its complete-query counter. -/
@[expose] def attempt := runFinder finder accepts

/-- Every tree returned by the concrete finder has distinct siblings and accepting leaves. -/
theorem structured (z : Option (VecTree challenges branching) × ℕ)
    (hz : z ∈ support attempt) (t : VecTree challenges branching) (ht : z.1 = some t) :
    t.IsStructured (fun _ ch => Function.Injective ch) ∧ ∀ p, accepts (t.leaf p) = true := by
  have hz' : some t ∈ support (Prod.fst <$> attempt) := by
    rw [support_map]
    exact ⟨z, hz, ht⟩
  rw [attempt, runFinder, counted_fst, finder, simulateQ_thresholdFinderWithPools] at hz'
  apply thresholdProgram_sound _ 1 challenges branching pools _ accepts
    (fun _ => by change ([0, 1, 2] : List (Fin 3)).Nodup; decide) _ t hz'
  intro q hq
  change true ∈ support (pure (accepts q) : ProbComp Bool) at hq
  simpa only [support_pure, Set.mem_singleton_iff, eq_comm] using hq

/-- The single-round Boolean finder has unconditional expected cost at most two. -/
theorem oneRound_cost :
    expectedCalls ((simulateQ (coins (S := ℕ) + counted (fun c : Fin 3 => decide (c ≠ 2)))
      (thresholdRound 2 [0, 1, 2])).run 0) ≤ 2 := by
  convert expectedCalls_thresholdRound (fun c : Fin 3 => decide (c ≠ 2)) 1 0 [1, 2] using 1
  norm_num

/-- The actual recursive tree finder has unconditional expected cost at most two. -/
theorem tree_cost : expectedCalls attempt ≤ 2 := by
  rw [attempt, finder, runFinder_thresholdFinderWithPools_succ]
  rw [expectedCalls_map_output (fun children : Option (List _) => children.bind assembleChildren)]
  have h := expectedCalls_thresholdChildren
    (fun c : challenges 0 =>
      (fun z => (z.1.map (fun t => (c, t)), z.2)) <$>
        runFinder (thresholdFinderWithPools 0 (fun i : Fin 0 => challenges i.succ)
          (fun i => branching i.succ) (fun i => pools i.succ))
          (fun q => accepts (Fin.cons c q))) (branching 0) (pools 0)
  apply h.trans
  have hchild (c : challenges 0) :
      expectedCalls ((fun z => (z.1.map (fun t => (c, t)), z.2)) <$>
        runFinder (thresholdFinderWithPools 0 (fun i : Fin 0 => challenges i.succ)
          (fun i => branching i.succ) (fun i => pools i.succ))
          (fun q => accepts (Fin.cons c q))) = 1 := by
    rw [expectedCalls_map_output (Option.map (fun t => (c, t))), runFinder,
      simulateQ_counted_thresholdFinderWithPools]
    simp [thresholdProgram, counted, StateT.run_modify, expectedCalls, AddWriterT.expectedCostNat,
      AddWriterT.expectedCost, AddWriterT.costs_def]
  simp only [hchild]
  norm_num [pools, branching]
  rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
  norm_num

/-- The concrete acceptance table gives success probability exactly two thirds. -/
theorem oneRound_success :
    Pr{let z ← (simulateQ (coins (S := ℕ) + counted (fun c : Fin 3 => decide (c ≠ 2)))
      (thresholdRound 2 [0, 1, 2])).run 0}[z.1.isSome] = 2 / 3 := by
  rw [prEvent_thresholdRound]
  norm_num

/-- Execute the recursive tree finder and inspect its actual leaves, sibling distinction, and
complete-query counter. Initial rejection and successful two-leaf extraction are both allowed. -/
def runCheck : IO Unit := do
  for _ in List.range 24 do
    let (tree, count) ← OracleComp.runIO attempt
    match tree with
    | none =>
        unless count == 1 do
          throw <| IO.userError "threshold finder rejected after an unexpected query count"
    | some t =>
        let c₀ := t.leaf (fun _ => 0) 0
        let c₁ := t.leaf (fun _ => 1) 0
        unless c₀ != c₁ && c₀ != 2 && c₁ != 2 && (count == 2 || count == 3) do
          throw <| IO.userError "threshold finder returned an invalid accepting fork"

run_cmd liftM runCheck

end VCVioTest.ThresholdFinder
