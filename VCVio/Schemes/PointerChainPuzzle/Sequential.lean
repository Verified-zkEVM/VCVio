/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Handler

/-!
# Sequentiality of the ideal handler (Claim 1)

Claim 1 of the delay proof of the pointer-chain puzzle: under the ideal handler (`idealImpl`), no
path value `v` is reached before round `ρ(v)` (`PathValue.rho`). The handler judges every point of
a round against the reached set at the submission of the round and adds the newly reached path
values only at its end, so a path value reached in round `r` has all its predecessors reached by
round `r - 1`; with `ρ(v) = max_{w ∈ preds v} ρ(w) + 1` (`PathValue.rho_eq_sup_preds`) the claim
follows by induction on the rounds.

## Main results

* `IdealState.RhoBounded`: every reached path value `v` has `ρ(v)` at most the round counter. This
  is the invariant of Claim 1.
* `preservesInv_idealImpl_rhoBounded`: the ideal handler preserves it (the induction step of
  Claim 1).
* `rho_le_round_of_mem_support`: in every run of the online phase from the initial state, every
  reached path value `v` has `ρ(v)` at most the final round counter (Claim 1).
* `round_le_of_isOnlineQueryBound`: under an online budget of `r` rounds the counter goes up by at
  most `r`.
* `key_not_mem_reached_of_isOnlineQueryBound`: with fewer than `keyRound n m` online rounds, the
  key is not reached at the end of any run (the conclusion of Claim 1 used in the delay proof).
* `prEvent_idealOutcomeExperiment_keyReached`, `prEvent_idealExperiment_keyReached`: in the ideal
  experiment of an adversary with fewer than `keyRound n m` online rounds, for outputs of any type
  and for a delay adversary, the key is reached with probability `0`.
-/

public section

open OracleSpec OracleComp

namespace PointerChainPuzzle

variable {n m : ℕ} {S L Salt Ctx : Type}

/-- A path value whose predecessors all have `ρ` at most `k` has `ρ` at most `k + 1`. -/
lemma PathValue.rho_le_succ_of_preds [NeZero n] {v : PathValue n m} {k : ℕ}
    (h : ∀ w ∈ v.preds, w.rho ≤ k) : v.rho ≤ k + 1 := by
  by_cases hv : v = PathValue.firstStart
  · subst hv
    rw [PathValue.rho_firstStart]
    omega
  · rw [PathValue.rho_eq_sup_preds hv]
    exact Nat.add_le_add_right (Finset.sup_le h) 1

namespace IdealState

/-- **Claim 1, the invariant.** Every reached path value `v` has `ρ(v)` at most the number of
online rounds so far: no path value is reached before round `ρ(v)`. -/
@[expose]
def RhoBounded (s : IdealState n m S L Salt Ctx) : Prop :=
  ∀ v ∈ s.reached, v.rho ≤ s.round

/-- The invariant of Claim 1 holds at the start of the online phase, where nothing is reached. -/
lemma rhoBounded_init (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (init c : IdealState n m S L Salt Ctx).RhoBounded := by
  simp [RhoBounded]

variable {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]

/-- **Claim 1, one round.** A round preserves the invariant: a path value newly reached in a round
has all its predecessors in the reached set at the submission of the round, so its `ρ` is at most
one more than the round counter before the round. -/
lemma RhoBounded.afterRound {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {s : IdealState n m S L Salt Ctx} (h : s.RhoBounded) (ts : List (Point n S L Salt Ctx))
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (s.afterRound m mkCtx initAcc P ℓ ts c).RhoBounded := by
  intro v hv
  rw [afterRound_reached, Finset.mem_union, mem_newlyReached] at hv
  rw [afterRound_round]
  rcases hv with hv | ⟨hR, -⟩
  · exact (h v hv).trans (Nat.le_succ _)
  · exact PathValue.rho_le_succ_of_preds fun w hw => h w (hR hw)

end IdealState

section Handler

variable {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] {P : Puzzle n S L Salt} {ℓ : Labels n m S L}

/-- **Claim 1, the induction step.** The ideal handler preserves the invariant of Claim 1: uniform
queries leave the state unchanged, and a round is handled atomically (`RhoBounded.afterRound`). -/
lemma preservesInv_idealImpl_rhoBounded :
    QueryImpl.PreservesInv (idealImpl m mkCtx initAcc P ℓ) IdealState.RhoBounded := by
  intro t s hs z hz
  rcases t with k | ts
  · rw [eq_of_mem_support_idealImpl_inl hz]
    exact hs
  · obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hz
    rw [hc]
    exact hs.afterRound ts c

/-- **Claim 1.** In every run of an online phase under the ideal handler from the initial state,
every reached path value `v` has `ρ(v)` at most the final number of online rounds: no path value is
reached before round `ρ(v)`. -/
theorem rho_le_round_of_mem_support {α : Type}
    (oa : OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α)
    (c : (oracleSpec n S L Salt Ctx).QueryCache)
    {z : α × IdealState n m S L Salt Ctx}
    (hz : z ∈ support ((simulateQ (idealImpl m mkCtx initAcc P ℓ) oa).run (IdealState.init c)))
    {v : PathValue n m} (hv : v ∈ z.2.reached) : v.rho ≤ z.2.round :=
  simulateQ_run_preservesInv _ _ preservesInv_idealImpl_rhoBounded oa _
    (IdealState.rhoBounded_init c) z hz v hv

/-- Under an online budget of `b.1` rounds, the round counter of the ideal handler goes up by at
most `b.1`. -/
theorem round_le_of_isOnlineQueryBound {α : Type}
    {oa : OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α} {b : ℕ × ℕ}
    (h : IsOnlineQueryBound oa b) (s : IdealState n m S L Salt Ctx)
    {z : α × IdealState n m S L Salt Ctx}
    (hz : z ∈ support ((simulateQ (idealImpl m mkCtx initAcc P ℓ) oa).run s)) :
    z.2.round ≤ s.round + b.1 := by
  induction oa using OracleComp.inductionOn generalizing b s with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Nat.le_add_right _ _
  | query_bind t mx ih =>
      have hz' : z ∈ support
          (((simulateQ (idealImpl m mkCtx initAcc P ℓ)
                (OracleSpec.query t : OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch)
                  ((unifSpec + (oracleSpec n S L Salt Ctx).batch).Range t))).run s) >>=
            fun us => (simulateQ (idealImpl m mkCtx initAcc P ℓ) (mx us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      obtain ⟨us, hus, hzc⟩ := (mem_support_bind_iff _ _ _).1 hz'
      have hus' : us ∈ support ((idealImpl m mkCtx initAcc P ℓ t).run s) := by
        simpa [simulateQ_spec_query] using hus
      rcases t with k | ts
      · have := ih us.1 (h.2 us.1) us.2 hzc
        rw [eq_of_mem_support_idealImpl_inl hus'] at this
        exact this
      · obtain ⟨⟨h₁, -⟩, hk⟩ := h
        obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hus'
        have := ih us.1 (b := (b.1 - 1, b.2 - ts.length)) (hk us.1) us.2 hzc
        rw [hc, IdealState.afterRound_round] at this
        dsimp only at this
        omega

/-- **Claim 1, conclusion.** In every run of an online phase with at most `r < keyRound n m` online
rounds under the ideal handler from the initial state, the key is not reached. -/
theorem key_not_mem_reached_of_isOnlineQueryBound {α : Type}
    {oa : OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α} {r q : ℕ}
    (h : IsOnlineQueryBound oa (r, q)) (hr : r < keyRound n m)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) {z : α × IdealState n m S L Salt Ctx}
    (hz : z ∈ support ((simulateQ (idealImpl m mkCtx initAcc P ℓ) oa).run (IdealState.init c))) :
    PathValue.key ∉ z.2.reached := by
  intro hkey
  have h₁ := rho_le_round_of_mem_support oa c hz hkey
  have h₂ := round_le_of_isOnlineQueryBound h _ hz
  rw [PathValue.rho_key] at h₁
  simp only [IdealState.init_round, zero_add] at h₂
  omega

end Handler

section OutcomeExperiment

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType Salt]
  {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

/-- **Claim 1, in the ideal experiment for any output.** If the online phase of the adversary, with
outputs of any type, submits at most `r < keyRound n m` rounds, the key is reached in the ideal
experiment with probability `0`. -/
theorem prEvent_idealOutcomeExperiment_keyReached {Out : Type}
    {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec n S L Salt Ctx)
      (Puzzle n S L Salt) Out} {r q : ℕ}
    (hbound : ∀ σ P, IsOnlineQueryBound (adv.online σ P) (r, q)) (hr : r < keyRound n m) :
    Pr{let res ← idealOutcomeExperiment adv m mkCtx initAcc}[res.keyReached = true] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun res hres => ?_
  rw [idealOutcomeExperiment, mem_support_bind_iff] at hres
  obtain ⟨s, -, hres⟩ := hres
  rw [idealOutcomeRest, support_map] at hres
  obtain ⟨z, hz, rfl⟩ := hres
  simpa using key_not_mem_reached_of_isOnlineQueryBound (hbound _ _) hr _ hz

end OutcomeExperiment

section Experiment

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType Salt]
  {adv : TimeLockPuzzle.Adversary (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S}
  {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

/-- **Claim 1, in the ideal experiment.** If the online phase of the adversary submits at most
`r < keyRound n m` rounds, the key is reached in the ideal experiment with probability `0`. -/
theorem prEvent_idealExperiment_keyReached {r q : ℕ}
    (hbound : ∀ σ P, IsOnlineQueryBound (adv.online σ P) (r, q)) (hr : r < keyRound n m) :
    Pr{let res ← idealExperiment adv m mkCtx initAcc}[res.keyReached = true] = 0 := by
  rw [idealExperiment_eq_map_toResult, prEvent_map]
  exact prEvent_idealOutcomeExperiment_keyReached hbound hr

end Experiment

end PointerChainPuzzle
