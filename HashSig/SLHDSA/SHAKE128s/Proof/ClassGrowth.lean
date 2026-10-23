/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.AdversaryQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge

/-!
# The split class counter

`classCost` counts the hash calls at inputs of one class, and `splitCost` charges a class to one
slot of the counter and its complement to another, so that a single run carries both counts. The
sum of the two slots is the run's own hash count (`countAllHashes_eq_readOff`), so the split
counted run is the all-hashes-counted run with its count resolved into two parts, and one budget
pays for both. The counts are read off the same `Security.countQueries` instrumentation the rest
of the accounting uses.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ClassGrowth

variable {α : Type}

open Security GrowthCharge

open scoped Classical in
/-- One unit for a hash call at an input of the class, nothing for anything else. -/
noncomputable def classCost (inClass : Bytes → Prop) : OracleWorld.Domain → Counts
  | .inl _ => 0
  | .inr input => if inClass input then Counts.single .hash 1 else 0

/-! ## Both sides of one split, on one counter

`classCost` counts one class and discards the other, so the two sides of a split can only be
read off two differently instrumented runs — and counts on two different runs do not add
pathwise. `splitCost` charges the class to one slot of the counter and its complement to
another, so a single run carries both, and the sum of the two slots is the run's own hash
count. That sum is what one budget pays for.

The two slots are parameters rather than a fixed pair: nothing here reads a slot's name, and
leaving them free keeps the counter usable whichever two the caller has to spare. -/

open scoped Classical in
/-- **The two-slot class counter.** One unit of `inside` for a hash call at an input of the
class, one unit of `outside` for a hash call anywhere else, nothing for a coin. -/
noncomputable def splitCost (inClass : Bytes → Prop) (inside outside : QueryKind) :
    OracleWorld.Domain → Counts
  | .inl _ => 0
  | .inr input => if inClass input then Counts.single inside 1 else Counts.single outside 1

open scoped Classical in
theorem splitCost_inl (inClass : Bytes → Prop) (inside outside : QueryKind)
    (coin : unifSpec.Domain) : splitCost inClass inside outside (Sum.inl coin) = 0 := rfl

open scoped Classical in
/-- **The two slots add to the hash cost.** Every hash call is charged exactly one unit, to
exactly one of the two slots, and a coin is charged nothing — so the two class counts of a run
add to that run's own hash-query count rather than each equalling it. -/
theorem splitCost_add_eq_hashCost (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (queried : OracleWorld.Domain) :
    (splitCost inClass inside outside queried) inside +
        (splitCost inClass inside outside queried) outside = hashCost queried := by
  classical
  rcases queried with coin | input
  · rw [splitCost_inl]
    rfl
  · rw [splitCost]
    by_cases hmember : inClass input
    · rw [if_pos hmember, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne hne.symm]
      rfl
    · rw [if_neg hmember, Counts.single, Pi.single_eq_of_ne hne, Pi.single_eq_same]
      rfl

/-! ## The split counter is the total counter

The two class counts are only worth separating if their *sum* is something the budget already
speaks about. It is: every query is charged its hash cost, split between the two slots, so any
linear readout of the split counter that recovers the hash cost run for run recovers
`countAllHashes`. The split-counted run is not a new experiment, so whatever bounds the total
bounds the two parts together, with no second budget anywhere. -/

/-- **A linear readout that recovers the hash cost recovers the total count.** -/
theorem countAllHashes_eq_readOff {α : Type} (cost : OracleWorld.Domain → Counts)
    (readOff : Counts → Nat) (hzero : readOff 0 = 0)
    (hadd : ∀ left right : Counts, readOff (left + right) = readOff left + readOff right)
    (hcost : ∀ input, readOff (cost input) = hashCost input)
    (computation : OracleComp OracleWorld α) :
    (fun result : α × Counts => (result.1, readOff result.2)) <$>
        countQueries cost computation = countAllHashes computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    rw [VerificationBudget.countQueries_pure, GrowthBudget.countAllHashes_pure, map_pure, hzero]
  | query_bind queried next ih =>
    rw [WarmedSplit.countQueries_query_bind, GrowthBudget.countAllHashes_query_bind, map_bind]
    refine congrArg (fun step => liftM (OracleWorld.query queried) >>= step) ?_
    funext answer
    rw [← ih answer, Functor.map_map, Functor.map_map]
    refine congrArg (fun step => step <$> countQueries cost (next answer)) ?_
    funext inner
    simp only [hadd, hcost]

/-- **The split-counted run is the all-hashes-counted run.** Summing the two class slots turns
one into the other, so an event about the plain run is an event about the split-counted one and
the plain run's budget is a budget for the two counts together. -/
theorem run_countQueries_eq_map_readOff {α : Type} (cost : OracleWorld.Domain → Counts)
    (readOff : Counts → Nat) (hzero : readOff 0 = 0)
    (hadd : ∀ left right : Counts, readOff (left + right) = readOff left + readOff right)
    (hcost : ∀ input, readOff (cost input) = hashCost input)
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec) :
    (fun result : (α × Counts) × QueryCache HashSpec =>
          ((result.1.1, readOff result.1.2), result.2)) <$>
        (simulateQ KeygenUniform.rom (countQueries cost computation)).run initialCache =
      (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache := by
  rw [← countAllHashes_eq_readOff cost readOff hzero hadd hcost computation, simulateQ_map,
    StateT.run_map]

open scoped Classical in
/-- The sum of the two class slots is a readout of the kind `countAllHashes_eq_readOff` wants. -/
theorem splitSum_add (inside outside : QueryKind) (left right : Counts) :
    (left + right) inside + (left + right) outside =
      (left inside + left outside) + (right inside + right outside) := by
  simp only [Pi.add_apply]
  omega

open scoped Classical in
/-- **The split-counted run, read as the plain run.** -/
theorem run_splitCost_eq_map (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) :
    (fun result : (α × Counts) × QueryCache HashSpec =>
          ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)) <$>
        (simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run initialCache =
      (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache :=
  run_countQueries_eq_map_readOff (splitCost inClass inside outside)
    (fun counts => counts inside + counts outside) rfl (splitSum_add inside outside)
    (splitCost_add_eq_hashCost inClass hne) computation initialCache

open scoped Classical in
/-- **The two class counts of a split-counted run are the plain run's own count.** Whatever
bounds the plain run's count therefore bounds the two class counts together — one budget, two
charges. -/
theorem mem_support_countAllHashes_of_splitCost (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside) {α : Type}
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) computation)).run initialCache)) :
    ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) ∈
      support ((simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache) := by
  rw [← run_splitCost_eq_map inClass hne computation initialCache, support_map]
  exact ⟨result, hmem, rfl⟩

end SlhDsaSecurity.ClassGrowth
