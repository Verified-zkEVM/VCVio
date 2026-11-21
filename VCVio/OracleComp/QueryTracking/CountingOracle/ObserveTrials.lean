/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.AdaptiveMoment
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Counting trials without changing a stateful caller

The decision to count a query uses the state before its reply is known.
The same reply determines whether a counted trial succeeded.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace OracleComp.BernoulliMoment

variable {ι σ : Type} {spec : OracleSpec ι}

/-- Count at most q eligible trials, recording success from the underlying handler's answer. -/
@[expose] def update (q : ℕ) (eligible : ι → σ → Bool) (accept : ∀ t, spec.Range t → Bool)
    (t : ι) (s : σ) (y : spec.Range t) (_ : σ) (counts : ℕ × ℕ) : ℕ × ℕ :=
  if eligible t s && counts.1 < q then
    (counts.1 + 1, if accept t y then counts.2 + 1 else counts.2)
  else counts

/-- A passive observer of a stateful oracle, with separate trial and success counts. -/
@[expose] def observe (so : QueryImpl spec (StateT σ ProbComp)) (q : ℕ)
    (eligible : ι → σ → Bool) (accept : ∀ t, spec.Range t → Bool) :=
  so.extendState (update q eligible accept)

/-- Every marked step is either ignored or counts a single trial with the prescribed probability. -/
theorem counts_observe (so : QueryImpl spec (StateT σ ProbComp)) (q : ℕ)
    (eligible : ι → σ → Bool) (accept : ∀ t, spec.Range t → Bool) (p : ℝ)
    (rate : ∀ t s, eligible t s → Pr{let z ← (so t).run s}[accept t z.1] = ENNReal.ofReal p) :
    CountsTrials (observe so q eligible accept) (fun s => s.2.1) (fun s => s.2.2) p q := by
  intro t ⟨s, n, v⟩
  by_cases active : eligible t s = true ∧ n < q
  · refine Or.inr ⟨active.2, ?_, ?_⟩
    · simp only [observe, QueryImpl.extendState_apply, bind_pure_comp, prEvent_norm, update,
        active.1, active.2, decide_true, Bool.and_self, ite_true]
      convert rate t s active.1 using 1
      apply congrArg prEvent
      apply congrArg (fun f : spec.Range t × σ → Prop => f <$> (so t).run s)
      funext z
      cases accept t z.1 <;> simp
    · intro z hz
      have cnt := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 hz |>.2
      change z.2.2 = update q eligible accept t s z.1 z.2.1 (n, v) at cnt
      simp only [update, active.1, active.2, decide_true, Bool.and_self, ite_true] at cnt
      cases ok : accept t z.1 <;> simp only [ok, Bool.false_eq_true, ite_false, ite_true] at cnt
      · exact ⟨congrArg Prod.fst cnt, Or.inr (show z.2.2.2 = v from congrArg Prod.snd cnt)⟩
      · exact ⟨congrArg Prod.fst cnt, Or.inl (congrArg Prod.snd cnt)⟩
  · left
    intro z hz
    have cnt := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 hz |>.2
    change z.2.2 = update q eligible accept t s z.1 z.2.1 (n, v) at cnt
    have unchanged : z.2.2 = (n, v) := by simpa [update, active] using cnt
    exact ⟨congrArg Prod.fst unchanged, congrArg Prod.snd unchanged⟩

end OracleComp.BernoulliMoment
