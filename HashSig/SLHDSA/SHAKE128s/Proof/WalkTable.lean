/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Target
public import HashSig.SLHDSA.SHAKE128s.Proof.ReplayGate

/-!
# The walk, as a drawn table

The walk is a uniform draw of a cells-and-padding pair:
`CanonicalGraph.Programming.warmup_seed_uniform` says so, and `walkOfTable` is the walk that
pair determines. Its secret seed is the table's own `secretSeed` cell, its cells are the
table's cells, and its cache is the canonical entries of them. `evalDist_graphWalk` is the
whole of what the shape change costs: one equality of laws
`𝒟[graphWalk] = 𝒟[tableWalk]`, after which the walk's randomness is a `$ᵗ (Cells × Padding)` a
charge that draws its table itself can consume.

Two things the presentation has to get right, each of which would be a silent failure.

* **The seed is recovered, not re-drawn.** The walk's value carries the secret seed, and the
  table's law does not. What makes them the same presentation is that on the walk's own support
  the seed is the `secretSeed` cell (`secretSeed_of_mem_support`), because the traversal never
  overwrites it, so the value may be read off the table rather than carried beside it.
  `evalDist_bind_congr_support` is the one step where that support fact is used, and it is used
  in one direction only.
* **The seeds are drawn in the other order.** `WarmedGame.seeds` draws the secret seed first;
  the table's law wants it drawn last, after the public seed its canonical inputs mention. The
  two orders agree because the draws are independent, which is `evalDist_bind_comm` twice and
  nothing else.

`mem_support_graphWalk_walkOfTable` is what keeps the rest of the development usable here. Every
per-walk fact is stated for a walk in `support graphWalk`, and a drawn table names such a walk,
so none of them has to be restated at the new shape.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.WalkTable

variable {α β : Type}

open Security CanonicalGraph WarmedGame

/-! ## A support-wise congruence under a bind

The seed is recovered from the table on the walk's support, so the step that replaces it has to
be allowed to use where the run can be. -/

/-- **Continuations that agree where the run can be give the same law.** -/
theorem evalDist_bind_congr_support {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a ∈ support oa, f a =ᵈ g a) : oa >>= f =ᵈ oa >>= g :=
  OracleComp.EvalDistEq.bind_congr_of_support oa h

/-! ## The walk a table determines -/

/-- **A table's cells are the cells of its own full output table.** -/
theorem cellsOfOutputs_fullOutput (table : Cells × Padding) :
    Programming.cellsOfOutputs (table.1 Node.secretSeed) (fullOutput table.1 table.2) =
      table.1 := by
  funext node
  cases node with
  | secretSeed => rfl
  | structural parent => exact truncate_fullOutput _ _ _

/-- The walk a cells-and-padding pair determines: the table's own secret seed, the two seeds
drawn beside it, the table's cells, and the canonical entries of those cells. -/
@[expose] noncomputable def walkOfTable (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec :=
  (((table.1 Node.secretSeed, prfSeed, publicSeed), table.1),
    Programming.cacheFrom publicSeed table.1 (fullOutput table.1 table.2)
      Programming.order ∅)

/-- The walk, drawn as a table. -/
@[expose] noncomputable def tableWalk :
    ProbComp (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) := do
  let prfSeed ← ($ᵗ Digest : ProbComp Digest)
  let publicSeed ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  pure (walkOfTable prfSeed publicSeed table)

/-- **A drawn table names a walk the run could have taken.** -/
theorem mem_support_graphWalk_walkOfTable (prfSeed publicSeed : Digest)
    (table : Cells × Padding) : walkOfTable prfSeed publicSeed table ∈ support graphWalk := by
  classical
  rw [graphWalk_eq]
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
  refine ⟨(table.1 Node.secretSeed, prfSeed, publicSeed), by simp [seeds],
    (table.1, Programming.cacheFrom publicSeed table.1 (fullOutput table.1 table.2)
      Programming.order ∅), ?_, rfl⟩
  rw [Averaging.support_eq_of_evalDistEq
    (Programming.warmup_uniform publicSeed (table.1 Node.secretSeed)), support_map]
  refine ⟨fullOutput table.1 table.2, by simp, ?_⟩
  simp only [cellsOfOutputs_fullOutput]

/-! ## The walk's law

The secret seed is read off the table rather than carried beside it, and the three draws are
reordered so the table's own law applies. -/

/-- **The walk's seed is its table's `secretSeed` cell.** -/
theorem secretSeed_of_mem_support (publicSeed secretSeed : Digest)
    (result : Cells × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅)) :
    result.1 Node.secretSeed = secretSeed := by
  rw [Averaging.support_eq_of_evalDistEq (Programming.warmup_uniform publicSeed secretSeed),
    support_map] at hresult
  obtain ⟨outputs, -, houtputs⟩ := hresult
  rw [← houtputs]
  rfl

/-- **The walk at fixed seeds is a drawn table.** -/
theorem evalDist_warmup_table (prfSeed publicSeed : Digest) :
    (do
        let secretSeed ← ($ᵗ Digest : ProbComp Digest)
        let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
        pure (((secretSeed, prfSeed, publicSeed), result.1), result.2)) =ᵈ
      (do
        let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
        pure (walkOfTable prfSeed publicSeed table)) := by
  classical
  have hseed : (do
      let secretSeed ← ($ᵗ Digest : ProbComp Digest)
      let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
      pure (((secretSeed, prfSeed, publicSeed), result.1), result.2)) =ᵈ
    (do
      let secretSeed ← ($ᵗ Digest : ProbComp Digest)
      let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
      pure (((result.1 Node.secretSeed, prfSeed, publicSeed), result.1), result.2)) := by
    refine EvalDistEq.bind_right _ fun secretSeed => ?_
    refine evalDist_bind_congr_support _ _ _ fun result hresult => ?_
    rw [secretSeed_of_mem_support publicSeed secretSeed result hresult]
  refine hseed.trans ?_
  rw [← bind_assoc]
  refine ((Programming.warmup_seed_uniform publicSeed).bind_left _).trans ?_
  rw [bind_map_left]
  exact EvalDistEq.rfl

/-- **The walk is a drawn table.** -/
theorem evalDist_graphWalk : graphWalk =ᵈ tableWalk := by
  classical
  have hwalk : graphWalk = (do
      let secretSeed ← ($ᵗ Digest : ProbComp Digest)
      let prfSeed ← ($ᵗ Digest : ProbComp Digest)
      let publicSeed ← ($ᵗ Digest : ProbComp Digest)
      let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
      pure (((secretSeed, prfSeed, publicSeed), result.1), result.2)) := by
    rw [graphWalk_eq, seeds]
    simp only [bind_assoc, pure_bind]
  rw [hwalk, tableWalk]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun prfSeed => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun publicSeed => ?_
  exact evalDist_warmup_table prfSeed publicSeed

end SlhDsaSecurity.WalkTable
