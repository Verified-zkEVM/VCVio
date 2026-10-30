/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute

/-!
# Fixed private randomness

The private tape contains an independent stream for each uniform-query size. A rerun's cursor
records how many entries of each stream it has consumed. The persistent cache samples a tape
entry only on its first use and preserves it for every later rerun.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

namespace FixedTape

/-- Tape entries indexed by uniform-query size and occurrence within that size's stream. -/
@[expose, reducible] def spec : OracleSpec (ℕ × ℕ) := fun p => Fin (p.1 + 1)

/-- The number of entries consumed in each size's private stream. -/
abbrev Cursor := ℕ → ℕ

/-- Advance the stream selected by a uniform query. -/
@[expose] def advance (c : Cursor) (q : ℕ) : Cursor := Function.update c q (c q + 1)

/-- Read the next private-tape entry, sampling and retaining it on first use. -/
@[expose] def answer : QueryImpl unifSpec (StateT (spec.QueryCache × Cursor) ProbComp) :=
  fun q => StateT.mk fun s =>
    (fun z => (z.1, (z.2, advance s.2 q))) <$> (spec.randomOracle (q, s.2 q)).run s.1

/-- The tape step is a lazy random-oracle lookup followed by a deterministic cursor update. -/
theorem answer_run (q : ℕ) (w : spec.QueryCache) (c : Cursor) :
    (answer q).run (w, c) =
      (fun z => (z.1, (z.2, advance c q))) <$> (spec.randomOracle (q, c q)).run w := rfl

/-- No previously sampled entries lie at or beyond the current position of any stream. -/
def Fresh (w : spec.QueryCache) (c : Cursor) : Prop :=
  ∀ n k, c n ≤ k → w (n, k) = none

private theorem fresh_cacheQuery {w : spec.QueryCache} {c : Cursor} (h : Fresh w c)
    (q : ℕ) (u : Fin (q + 1)) : Fresh (w.cacheQuery (q, c q) u) (advance c q) := by
  intro n k hk
  have hne : (n, k) ≠ (q, c q) := by
    intro heq
    cases heq
    simp [advance] at hk
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  apply h
  by_cases hn : n = q
  · subst n
    simp only [advance, Function.update_self] at hk
    omega
  · simpa [advance, Function.update_of_ne hn] using hk

/-- A run that starts beyond every sampled entry draws fresh honest coins. -/
theorem run'_eq {α : Type} (oa : ProbComp α) (w : spec.QueryCache) (c : Cursor)
    (h : Fresh w c) : (simulateQ answer oa).run' (w, c) = oa := by
  induction oa using OracleComp.inductionOn generalizing w c with
  | pure a => simp
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_bind', answer_run]
    rw [randomOracle.run_eq, h q (c q) le_rfl]
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
    exact bind_congr fun u => ih u _ _ (fresh_cacheQuery h q u)

/-- A single fixed-tape execution has the honest private-coin distribution. -/
theorem faithful {α : Type} (oa : ProbComp α) :
    (simulateQ answer oa).run' (∅, fun _ => 0) =ᵈ
      (do (simulateQ (coins (S := Unit)) oa).run' (← pure ())) := by
  rw [run'_eq oa _ _ (fun _ _ _ => rfl)]
  simp [coins, simulateQ_liftTarget]

/-- Fresh external coins can be interleaved with a single honest private-tape execution. -/
theorem run'_add_eq {α : Type} (oa : OracleComp (unifSpec + unifSpec) α)
    (w : spec.QueryCache) (c : Cursor) (h : Fresh w c) :
    (simulateQ (coins (S := spec.QueryCache × Cursor) + answer) oa).run' (w, c) =
      (simulateQ (coins (S := Unit) + coins (S := Unit)) oa).run' () := by
  induction oa using OracleComp.inductionOn generalizing w c with
  | pure a => simp
  | query_bind q k ih =>
    cases q with
    | inl q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
        StateT.run'_bind', coins, QueryImpl.liftTarget_apply_run, bind_map_left]
      exact bind_congr fun u => ih u _ _ h
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
        StateT.run'_bind', coins, QueryImpl.liftTarget_apply_run, bind_map_left]
      rw [answer_run, randomOracle.run_eq, h q (c q) le_rfl]
      simp only [map_bind, map_pure, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u _ _ (fresh_cacheQuery h q u)

/-- Interleaving fresh external coins preserves the honest distribution of one execution. -/
theorem faithful_add {α : Type} (oa : OracleComp (unifSpec + unifSpec) α) :
    (simulateQ (coins (S := spec.QueryCache × Cursor) + answer) oa).run' (∅, fun _ => 0) =ᵈ
      (do (simulateQ (coins (S := Unit) + coins (S := Unit)) oa).run' (← pure ())) := by
  rw [run'_add_eq oa _ _ (fun _ _ _ => rfl)]

/-- Answering a private query preserves every tape entry already sampled. -/
theorem grows (q : ℕ) (w : spec.QueryCache) (c : Cursor) (z)
    (hz : z ∈ support ((answer q).run (w, c))) : w ≤ z.2.1 := by
  rw [answer_run, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact QueryImpl.withCaching_cache_le uniformSampleImpl _ _ _ hy

/-- Every sampled tape entry and cursor update can be replayed in every larger tape. -/
theorem frozen (q : ℕ) (w w' : spec.QueryCache) (c : Cursor) (z)
    (hz : z ∈ support ((answer q).run (w, c))) (hle : z.2.1 ≤ w') :
    (answer q).run (w', c) = pure (z.1, (w', z.2.2)) := by
  rw [answer_run, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hc := QueryImpl.withCaching_run_caches uniformSampleImpl (q, c q) w y hy
  rw [answer_run, QueryImpl.withCaching_run_some uniformSampleImpl (hle hc), map_pure]

/-- Private-tape entries can be discovered in either order with the same joint distribution. -/
theorem commute (q₁ q₂ : ℕ) (c₁ c₂ : Cursor) (w : spec.QueryCache) :
    (do
      let z₁ ← (answer q₁).run (w, c₁)
      let z₂ ← (answer q₂).run (z₁.2.1, c₂)
      pure ((z₁.1, z₁.2.2), (z₂.1, z₂.2.2), z₂.2.1)) =ᵈ
    (do
      let z₂ ← (answer q₂).run (w, c₂)
      let z₁ ← (answer q₁).run (z₂.2.1, c₁)
      pure ((z₁.1, z₁.2.2), (z₂.1, z₂.2.2), z₁.2.1)) := by
  apply evalDistEq_iff_evalDist_eq.mpr
  let : MeasurableSpace
    ((Fin (q₁ + 1) × Cursor) × (Fin (q₂ + 1) × Cursor) × spec.QueryCache) := ⊤
  simp only [answer_run, bind_map_left]
  exact randomOracle.evalDist_run_bind_run_swap (q₁, c₁ q₁) (q₂, c₂ q₂) w
    (fun u₁ u₂ w' => pure ((u₁, advance c₁ q₁), (u₂, advance c₂ q₂), w'))

end FixedTape

/-- Freeze the prover's private uniform randomness for all complete reruns of one attempt. -/
@[expose] def fixedTape : ResetPolicy (pure ()) (coins (S := Unit)) where
  World := FixedTape.spec.QueryCache
  empty := ∅
  Cursor := FixedTape.Cursor
  begin := fun _ => 0
  answer := FixedTape.answer
  faithful := FixedTape.faithful
  faithful_coins := FixedTape.faithful_add
  grows := FixedTape.grows
  frozen := FixedTape.frozen
  commute := FixedTape.commute

end Rewinding
