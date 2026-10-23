/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.StrippedGame
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedSplit

/-!
# The adversary's charged work and the counted run

The game's own counters report something other than the total hash count: `Outcome.counts.work`
is the adversary's direct calls plus the verifier's, charged inside the run rather than around
it. Key generation and the signer hash without being charged, which is what makes the honest
phase free, and a signing *request* is charged on the `.signing` counter, which `Counts.work`
does not read. `Counts.single .signing 1` has `work = 0`, so the signing charge never collides
with the work budget.

This file holds the arithmetic of `Counts.work` (`work_add`, `work_single_*`), the factoring of
a counted run at a sequencing point that keeps both counts (`mem_support_counted_bind_count`),
the adversary's own charged oracle `adversaryImpl`, and `servedCount`, the number of requests
the signer served, read off the signing log.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.AdversaryQueries

variable {α β : Type}

open Security

/-! ## Charged work, as a number -/

theorem work_add (left right : Counts) :
    (left + right).work = left.work + right.work := by
  simp only [Counts.work, Pi.add_apply]
  omega

theorem work_single_hash (count : Nat) : (Counts.single .hash count).work = count := by
  simp [Counts.work, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem work_single_verification (count : Nat) :
    (Counts.single .verification count).work = count := by
  simp [Counts.work, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem work_single_signing (count : Nat) : (Counts.single .signing count).work = 0 := by
  simp [Counts.work, Counts.single, Pi.single_eq_of_ne]

/-! ## Splitting a counted run, keeping both counts -/

theorem countAllHashes_map {α β : Type} (computation : OracleComp OracleWorld α) (f : α → β) :
    countAllHashes (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> countAllHashes computation := by
  rw [map_eq_bind_pure_comp, GrowthBudget.countAllHashes_bind]
  simp only [Function.comp_def, GrowthBudget.countAllHashes_pure, pure_bind,
    map_eq_bind_pure_comp, Nat.add_zero]

/-- **A counted run factors at every sequencing point, with both counts kept.** The variant of
`WarmedSplit.mem_support_counted_bind` that remembers how the total splits. -/
theorem mem_support_counted_bind_count {α β : Type} (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec)
    (result : (β × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (computation >>= next))).run cache)) :
    ∃ (value : α) (middleCache : QueryCache HashSpec) (first second : Nat),
      ((value, first), middleCache) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes computation)).run cache) ∧
      ((result.1.1, second), result.2) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes (next value))).run middleCache) ∧
      result.1.2 = first + second := by
  rw [GrowthBudget.countAllHashes_bind, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨first, hfirst, hrest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨second, hsecond, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  refine ⟨first.1.1, first.2, first.1.2, second.1.2, hfirst, ?_, by rw [hpure]⟩
  rw [show result.1.1 = second.1.1 from by rw [hpure],
    show result.2 = second.2 from by rw [hpure]]
  exact hsecond

/-! ## The adversary's own charges -/

/-- The adversary's own oracle: forward the query to the game's world and charge the hash. -/
noncomputable def adversaryImpl : QueryImpl OracleWorld CountedRun :=
  (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
    (fun input => Counts.single .hash (hashCost input))

/-- The adversary's own oracle, as the run it performs. -/
theorem run_adversaryImpl (queried : OracleWorld.Domain) (log : SigningLog) :
    ((WriterT.run (adversaryImpl queried)).run log) =
      (fun value =>
        ((value, Multiplicative.ofAdd (Counts.single .hash (hashCost queried))), log)) <$>
        (liftM (OracleWorld.query queried) : OracleComp OracleWorld (OracleWorld.Range queried)) := by
  simp only [adversaryImpl, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply, WriterT.run_bind,
    AddWriterT.run_addTell, StateT.run_bind, StateT.run_pure, pure_bind,
    StrippedGame.run_liftM_state, StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def, mul_one]

/-! ## What the signer spends

A request whose context is too long is refused before any query; a request that is served is
charged **two** hashes, its randomiser's and its message digest's, and both calls are the
signer's, so the work budget never sees either. The log says how many requests were served,
since the answer it records is `some` exactly when the frame was. -/

/-- The number of requests the signer served, read off the log it left. -/
def servedCount (log : SigningLog) : Nat :=
  (log.filter fun entry => entry.2.isSome).length

theorem servedCount_append (log : SigningLog) (request : Message) (answer : Option Bytes) :
    servedCount (log ++ [⟨request, answer⟩]) =
      servedCount log + (if answer.isSome then 1 else 0) := by
  rcases answer with _ | value <;> simp [servedCount]

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

attribute [local irreducible] WarmedGame.afterSeeds

end SlhDsaSecurity.AdversaryQueries
