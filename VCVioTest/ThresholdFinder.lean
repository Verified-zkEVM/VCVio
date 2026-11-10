/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.ThresholdFinder
public import VCVio.CryptoFoundations.Rewinding.FinderBridge
public import VCVio.CryptoFoundations.Rewinding.FixedTape
meta import VCVio.CryptoFoundations.Rewinding.ThresholdFinder

/-!
# Threshold extraction regressions

A binary fork on three challenges accepts exactly challenges zero and one. The tree finder
returns two distinct accepting challenges whenever it succeeds, and every inspected challenge
is charged, including an initial rejection. Its exact outcome list is checked by enumerating
the finder's coins.

A prover that guesses one challenge per round is accepted at exactly the threshold error, and no
tree of accepting challenges exists, so it is never extracted and the scaled bound
`ε ≤ κ + (1 − κ) p` holds with equality. This is checked for one round on the explicit pool and
for the computable `thresholdFinder`, with its sampler-derived challenge pools, on two rounds of
four challenges, where an acceptance function that accepts everything is always extracted with
exactly four calls. A consumer instantiates the tree-finder contract and transfers it to frozen
reruns.
-/

public section

open OracleComp OracleSpec Rewinding
open scoped ENNReal

namespace VCVioTest.ThresholdFinder

/-! ## One round on an explicit pool -/

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

/-- The finder together with its acceptance-oracle call counter. -/
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

/-- Check every outcome of the finder, in the order of its coins: the root challenges of the two
leaves of a returned tree, and the number of acceptance-oracle calls. A first child at challenge
zero or one is followed by one or two further calls before the other accepting challenge is found;
a first child at challenge two rejects and aborts after one call. A finder that keeps searching
after a rejected first child has `(some (0, 1), 3)` and `(some (1, 0), 3)` in place of
`(none, 1)`, and a finder that never succeeds has only the outcome `(none, 1)`. -/
def outcomeCheck : IO Unit := do
  let outcomes := (samplerOutcomes attempt).map fun z =>
    (z.1.map fun t => (t.leaf (fun _ => 0) 0, t.leaf (fun _ => 1) 0), z.2)
  unless outcomes =
      [(some (0, 1), 2), (some (0, 1), 3), (some (1, 0), 2), (some (1, 0), 3), (none, 1)] do
    throw <| IO.userError s!"threshold finder: unexpected outcome list {outcomes}"

run_cmd liftM outcomeCheck

/-! ## The threshold error is attained -/

/-- A prover that guesses challenge zero is accepted on one challenge in three. -/
@[expose] def onlyZero (q : (i : Fin 1) → challenges i) : Bool := decide (q 0 = 0)

/-- Guessing one challenge attains the threshold error `1 − (1 − 1/3) = 1/3`. -/
theorem rate_eq_error : acceptRate onlyZero = thresholdError challenges branching := by
  have hcard : (Finset.univ.filter fun c : (i : Fin 1) → challenges i =>
      onlyZero c = true).card = 1 := by decide
  rw [acceptRate, hcard, thresholdError]
  simp only [Finset.univ_unique, Finset.prod_singleton, Fintype.card_pi, Fintype.card_fin]
  norm_num
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top (ENNReal.inv_le_one.mpr (by norm_num))]

/-- The one-round threshold attempt never succeeds against the guessing prover's acceptance table:
one accepting challenge cannot form a binary fork. With `rate_eq_error`, the scaled bound
`ε ≤ κ + (1 − κ) p` holds with equality, so the threshold error cannot be lowered. -/
theorem success_zero :
    Pr{let z ← (simulateQ (coins (S := ℕ) + counted (fun c : Fin 3 => decide (c = 0)))
      (thresholdRound 2 [0, 1, 2])).run 0}[z.1.isSome] = 0 := by
  rw [prEvent_thresholdRound]
  simp

/-! ## The computable finder on two rounds -/

/-- Two rounds of four challenges each. -/
abbrev fourChallenges (_ : Fin 2) := Fin 4

/-- Each round forks into two branches. -/
abbrev twoBranches (_ : Fin 2) : ℕ := 2

/-- An acceptance function that accepts every challenge vector. -/
@[expose] def acceptAll (_ : (i : Fin 2) → fourChallenges i) : Bool := true

/-- Attema, Cramer and Kohl's cheating prover (Section 3.3): it guesses challenge zero in each
round and is accepted when either guess is right. -/
@[expose] def guessZero (q : (i : Fin 2) → fourChallenges i) : Bool := decide (q 0 = 0 ∨ q 1 = 0)

/-- The guessing prover's acceptance rate `7/16` is the threshold error `1 − (3/4)²`. -/
theorem rate_guessZero : acceptRate guessZero = thresholdError fourChallenges twoBranches := by
  have hcard : (Finset.univ.filter fun c : (i : Fin 2) → fourChallenges i =>
      guessZero c = true).card = 7 := by decide
  rw [acceptRate, hcard, thresholdError]
  simp only [Fin.prod_univ_two, Fintype.card_pi, Fintype.card_fin]
  norm_num
  have h4 : (4 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
  have hm : (1 - (4 : ℝ≥0∞)⁻¹) * (1 - 4⁻¹) ≤ 1 := mul_le_one' tsub_le_self tsub_le_self
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
    ENNReal.toReal_sub_of_le hm ENNReal.one_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le h4 ENNReal.one_ne_top, ENNReal.toReal_inv, ENNReal.toReal_div]
  norm_num

/-- Enumerate the computable finder's coins against both acceptance functions. Against `acceptAll`
every outcome is a tree found with exactly four calls, the size of the tree. Against `guessZero`
no outcome is a tree, although its acceptance rate is the threshold error (`rate_guessZero`). -/
def twoRoundsCheck : IO Unit := do
  let all := samplerOutcomes (runFinder (thresholdFinder fourChallenges twoBranches) acceptAll)
  unless all.all fun z => z.1.isSome && z.2 == 4 do
    throw <| IO.userError
      "threshold finder: an accepting run failed or did not make exactly four calls"
  let guess := samplerOutcomes (runFinder (thresholdFinder fourChallenges twoBranches) guessZero)
  unless guess.all fun z => !z.1.isSome do
    throw <| IO.userError "threshold finder: the guessing prover was extracted"

run_cmd liftM twoRoundsCheck

/-! ## A consumer of the contract -/

/-- The tree-finder contract for the computable finder on two rounds of four challenges, at the
threshold error and the tree size `2 · 2 = 4`. -/
theorem isTreeFinder_twoRounds :
    IsTreeFinder twoBranches (fun _ ch => Function.Injective ch)
      (thresholdFinder fourChallenges twoBranches)
      (thresholdError fourChallenges twoBranches) 4 := by
  convert isTreeFinder_thresholdFinder fourChallenges twoBranches
    (fun _ => (by simp : 1 ≤ 2 ∧ 2 ≤ Fintype.card (Fin 4))) using 1
  rw [Fin.prod_univ_two]
  norm_num

/-- Against frozen reruns of a fixed-tape prover, the honest acceptance probability averaged over
the sixteen challenge vectors is at most the threshold error plus its complement times the
success probability, and the expected number of complete runs is at most four. -/
example (run : ((i : Fin 2) → fourChallenges i) → ProbComp Bool) :
    (∑ c, Pr{let b ← (do (simulateQ (coins (S := Unit)) (run c)).run' (← pure ()))}[b = true]) /
          Fintype.card ((i : Fin 2) → fourChallenges i) ≤
        thresholdError fourChallenges twoBranches +
          (1 - thresholdError fourChallenges twoBranches) *
            Pr{let z ← (fixedTape.attempt run
              (thresholdFinder fourChallenges twoBranches))}[z.1.isSome] ∧
      expectedCalls (fixedTape.attempt run (thresholdFinder fourChallenges twoBranches)) ≤ 4 :=
  fixedTape.finder_bounds_honest run isTreeFinder_twoRounds

end VCVioTest.ThresholdFinder
