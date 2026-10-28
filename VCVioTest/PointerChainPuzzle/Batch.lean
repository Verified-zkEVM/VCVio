/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Batch

/-!
# Rounds of parallel queries

Checks of `OracleSpec.batch`, its handlers and its budgets on small concrete programs: a round
mixing oracles with different answer types, the order in which a round's points are submitted,
the empty round, a round with a repeated point, free uniform queries, and a two-round program that
no one-round budget admits, whatever its point budget. Budgets are checked to be exact: each point
is charged, so a budget one short fails. The typed rounds `queryRound₂`, `queryRound` and
`queryPoint` are checked against a fixed answer table and against their budgets.
-/

public section

namespace VCVioTest.PointerChainPuzzle.Batch

open OracleComp OracleSpec

/-- Two oracles with different answer types: `true` answers in `Fin 3`, `false` in `Bool`. -/
abbrev hetSpec : OracleSpec Bool := fun b => if b then Fin 3 else Bool

/-- Both answer types are sampled through `Fin`, so loading this module enumerates no type. -/
instance : ∀ t, SampleableType (hetSpec.Range t)
  | true => SampleableType.Fin 2
  | false => @SampleableType.ofEquiv _ _ (SampleableType.Fin 1) finTwoEquiv

instance : ∀ t, Inhabited (hetSpec.Range t)
  | true => inferInstanceAs (Inhabited (Fin 3))
  | false => inferInstanceAs (Inhabited Bool)

/-- A deterministic handler for `hetSpec`. -/
def hetImpl : QueryImpl hetSpec Id
  | true => (2 : Fin 3)
  | false => true

/-- A deterministic handler for local coins, always answering `0`. -/
def zeroCoins : QueryImpl unifSpec Id := fun _ => (0 : Fin _)

/-- One round to both oracles; the answers are read at their own types. -/
def hetRound : OracleComp (unifSpec + hetSpec.batch) (Fin 3 × Bool) := do
  let us ← liftM ((unifSpec + hetSpec.batch).query (.inr [true, false]))
  pure (us ⟨0, by decide⟩, us ⟨1, by decide⟩)

/-! ## Heterogeneous answers -/

/-- A batched deterministic handler answers each point at its own type. -/
example : (hetImpl.batch [true, false]).run ⟨0, by decide⟩ = (2 : Fin 3) := rfl

example : (hetImpl.batch [true, false]).run ⟨1, by decide⟩ = true := rfl

example : @id (Fin 3) ((hetImpl.batch [false, true, true]).run ⟨2, Nat.lt_succ_self 2⟩) = 2 := by
  decide

/-- The same through `batch_id_apply`, for an arbitrary position. -/
example (j : Fin 2) :
    (hetImpl.batch [true, false]).run j = (hetImpl [true, false][j]).run :=
  QueryImpl.batch_id_apply hetImpl [true, false] j

/-- Running the round through the batched handler reads both answers. -/
example : simulateQ (zeroCoins + hetImpl).batch' hetRound = ((2 : Fin 3), true) := rfl

/-- Unbatching the round first and running the single queries gives the same result. -/
example : simulateQ (zeroCoins + hetImpl) (simulateQ hetSpec.unbatch hetRound) =
    ((2 : Fin 3), true) := by
  rw [QueryImpl.simulateQ_simulateQ_unbatch]
  rfl

/-- One round with two points uses one round and two points. -/
example : IsOnlineQueryBound hetRound (1, 2) := by
  simp [hetRound]

/-- Unbatched, the round makes two queries to `hetSpec`. -/
example : IsQueryBoundP (simulateQ hetSpec.unbatch hetRound) (·.isRight) 2 := by
  refine IsOnlineQueryBound.isQueryBoundP_simulateQ_unbatch (r := 1) ?_
  simp [hetRound]

/-- One query to `hetSpec` does not suffice for the unbatched two-point round. -/
example : ¬ IsQueryBoundP (simulateQ hetSpec.unbatch hetRound) (·.isRight) 1 := by
  simp [hetRound, isQueryBoundP_query_bind_iff]

/-- An online point budget, rewritten as single queries, is a preprocessing budget. -/
example {α : Type} {oa : OracleComp (unifSpec + hetSpec.batch) α} {r q : ℕ}
    (h : IsOnlineQueryBound oa (r, q)) :
    IsPreprocessingQueryBound (simulateQ hetSpec.unbatch oa) q :=
  h.isQueryBoundP_simulateQ_unbatch

/-- In the random oracle model, unbatching a program is batching the random oracle. -/
example {α : Type} (oa : OracleComp (unifSpec + hetSpec.batch) α) :
    simulateQ hetSpec.romImpl (simulateQ hetSpec.unbatch oa) =
      simulateQ (unifFwdImpl hetSpec + hetSpec.randomOracle.batch) oa :=
  simulateQ_romImpl_simulateQ_unbatch oa

/-! ## Execution order -/

/-- Oracles indexed by points `ℕ`, answering in `ℕ`. -/
abbrev pointSpec : OracleSpec ℕ := fun _ => ℕ

/-- A stateful handler that appends each submitted point to a trace and answers with the number
of points submitted before it. -/
def traceImpl : QueryImpl pointSpec (StateM (List ℕ)) := fun t => do
  let s ← get
  set (s ++ [t])
  pure s.length

/-- The points of a round are submitted in the order of its list. -/
example : ((traceImpl.batch [5, 7, 9]).run []).2 = [5, 7, 9] := rfl

/-- Each answer sits at the position of its point: the `j`-th point is answered `j`. -/
example : ((traceImpl.batch [5, 7, 9]).run []).1 ⟨0, by decide⟩ = 0 := rfl

example : ((traceImpl.batch [5, 7, 9]).run []).1 ⟨1, by decide⟩ = 1 := rfl

example : ((traceImpl.batch [5, 7, 9]).run []).1 ⟨2, by decide⟩ = 2 := rfl

/-! ## The empty round -/

/-- The empty round has exactly one answer. -/
example (us vs : hetSpec.batch.Range []) : us = vs :=
  (eq_batchNil us).trans (eq_batchNil vs).symm

example : hetImpl.batch [] = pure batchNil := rfl

/-- An empty round. -/
def emptyRound : OracleComp (unifSpec + hetSpec.batch) Unit := do
  let _ ← liftM ((unifSpec + hetSpec.batch).query (.inr []))
  pure ()

/-- The empty round costs one round and no points. -/
example : IsOnlineQueryBound emptyRound (1, 0) := by
  simp [emptyRound]

/-- It still costs a round. -/
example : ¬ IsOnlineQueryBound emptyRound (0, 5) := by
  simp [emptyRound]

/-- Unbatched, it makes no query to `hetSpec`. -/
example : IsQueryBoundP (simulateQ hetSpec.unbatch emptyRound) (·.isRight) 0 := by
  refine IsOnlineQueryBound.isQueryBoundP_simulateQ_unbatch (r := 1) ?_
  simp [emptyRound]

/-! ## Repeated points -/

/-- A round asking the `true` oracle twice. -/
def dupRound : OracleComp (unifSpec + hetSpec.batch) (Fin 3 × Fin 3) := do
  let us ← liftM ((unifSpec + hetSpec.batch).query (.inr [true, true]))
  pure (us ⟨0, by decide⟩, us ⟨1, by decide⟩)

/-- A repeated point counts once per occurrence. -/
example : IsOnlineQueryBound dupRound (1, 2) := by
  simp [dupRound]

example : ¬ IsOnlineQueryBound dupRound (1, 1) := by
  simp [dupRound]

/-- Unbatched, the repeated point is queried twice. -/
example : IsQueryBoundP (simulateQ hetSpec.unbatch dupRound) (·.isRight) 2 := by
  refine IsOnlineQueryBound.isQueryBoundP_simulateQ_unbatch (r := 1) ?_
  simp [dupRound]

/-- A deterministic handler gives a repeated point the same answer. -/
example : simulateQ (zeroCoins + hetImpl).batch' dupRound = ((2 : Fin 3), (2 : Fin 3)) := rfl

/-- The lazy random oracle, batched, answers a repeated point from its cache: both answers agree
on every run. -/
example : ∀ z ∈ support ((hetSpec.randomOracle.batch [true, true]).run ∅),
    z.1 ⟨0, by decide⟩ = z.1 ⟨1, by decide⟩ := by
  intro z hz
  simp only [QueryImpl.batch_cons, QueryImpl.batch_nil, StateT.run_bind, randomOracle.run_eq,
    QueryCache.empty_apply, QueryCache.cacheQuery_self, StateT.run_pure, bind_assoc,
    pure_bind] at hz
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨u, -, rfl⟩ := hz
  rfl

/-! ## Free uniform queries -/

/-- Local coins around a single round. -/
def coinsThenRound : OracleComp (unifSpec + hetSpec.batch) Bool := do
  let a : Fin 6 ← liftM ((unifSpec + hetSpec.batch).query (.inl 5))
  let b : Fin 8 ← liftM ((unifSpec + hetSpec.batch).query (.inl 7))
  let us ← liftM ((unifSpec + hetSpec.batch).query (.inr [false]))
  let c : Fin 2 ← liftM ((unifSpec + hetSpec.batch).query (.inl 1))
  pure (decide (a.val = b.val) && us ⟨0, by decide⟩ && decide (c = 0))

/-- Uniform queries cost neither rounds nor points. -/
example : IsOnlineQueryBound coinsThenRound (1, 1) := by
  simp [coinsThenRound]

/-- Uniform queries in the preprocessing phase are free. -/
example : IsPreprocessingQueryBound (spec := hetSpec)
    (do
      let _ ← liftM ((unifSpec + hetSpec).query (.inl 3))
      liftM ((unifSpec + hetSpec).query (.inl 4))) 0 := by
  simp

/-- A query to `hetSpec` in the preprocessing phase is charged. -/
example : ¬ IsPreprocessingQueryBound
    (liftM ((unifSpec + hetSpec).query (.inr true)) : OracleComp (unifSpec + hetSpec) _) 0 := by
  simp

/-- Unbatching keeps uniform queries free. -/
example : IsQueryBoundP (simulateQ hetSpec.unbatch coinsThenRound) (·.isRight) 1 := by
  refine IsOnlineQueryBound.isQueryBoundP_simulateQ_unbatch (r := 1) ?_
  simp [coinsThenRound]

/-! ## Two rounds -/

/-- Two rounds, the point of the second chosen from the answer to the first. -/
def twoRounds : OracleComp (unifSpec + hetSpec.batch) Unit := do
  let us ← liftM ((unifSpec + hetSpec.batch).query (.inr [false]))
  let _ ← liftM ((unifSpec + hetSpec.batch).query (.inr [us ⟨0, by decide⟩]))
  pure ()

/-- It fits two rounds of two points in total. -/
theorem twoRounds_isOnlineQueryBound : IsOnlineQueryBound twoRounds (2, 2) := by
  simp [twoRounds]

/-- It fits no one-round budget, whatever the point budget. -/
example (q : ℕ) : ¬ IsOnlineQueryBound twoRounds (1, q) := by
  simp only [twoRounds, isOnlineQueryBound_query_bind_inr_iff, not_and, not_forall]
  intro _
  exact ⟨default, by simp⟩

/-! ## Lifting through a `SubSpec` inclusion -/

/-- The inclusion of `hetSpec` into `hetSpec + unifSpec` lifts to rounds. -/
example : hetSpec.batch ⊂ₒ (hetSpec + unifSpec).batch := inferInstance

example : hetSpec.batch ˡ⊂ₒ (hetSpec + unifSpec).batch := inferInstance

/-- A lifted round asks the translated points. -/
example : (inferInstance : hetSpec.batch ⊂ₒ (hetSpec + unifSpec).batch).onQuery [true, false] =
    [.inl true, .inl false] := rfl

/-- Lifting preserves the online budget. -/
example : IsOnlineQueryBound (liftComp twoRounds (unifSpec + (hetSpec + unifSpec).batch)) (2, 2) :=
  twoRounds_isOnlineQueryBound.liftComp

/-! ## Rounds with typed answers -/

/-- One round to both oracles through `queryRound₂`; each answer is read at its own type, with no
cast. -/
def typedRound : OracleComp (unifSpec + hetSpec.batch) (Fin 3 × Bool) := do
  let us ← queryRound₂ (fun _ : Fin 1 => true) (fun _ : Fin 1 => false)
  pure (us.1 0, us.2 0)

example : simulateQ (zeroCoins + hetImpl).batch' typedRound = ((2 : Fin 3), true) := rfl

/-- Against a fixed table, a single-point round returns the table's answer. -/
example : simulateQ (unifFwdAnswerImpl hetImpl).batch' (queryPoint (spec := hetSpec) false) =
    pure true := by
  rw [simulateQ_queryPoint]
  rfl

/-- A typed round costs one round and one point per point it holds. -/
example : IsOnlineQueryBound (queryRound₂ (spec := hetSpec) (fun _ : Fin 1 => true)
    (fun _ : Fin 2 => false)) (1, 3) :=
  isOnlineQueryBound_queryRound₂ _ _

example : ¬ IsOnlineQueryBound (queryPoint (spec := hetSpec) true) (1, 0) := by
  simp [queryPoint, queryRound, queryRound₂, isQueryBound_map_iff]

/-- Two single-point rounds in sequence fit two rounds of two points. -/
example : IsOnlineQueryBound (do
    let _ ← queryPoint (spec := hetSpec) true
    queryPoint (spec := hetSpec) false) (2, 2) :=
  isOnlineQueryBound_bind_le (1, 1) (1, 1) (isOnlineQueryBound_queryPoint _)
    (fun _ => isOnlineQueryBound_queryPoint _) ⟨le_rfl, le_rfl⟩

/-- Local coins lifted from `ProbComp` submit no rounds. -/
example : IsOnlineQueryBound (liftComp ($ᵗ Fin 4) (unifSpec + hetSpec.batch)) (0, 0) :=
  isOnlineQueryBound_liftComp _ _

end VCVioTest.PointerChainPuzzle.Batch
