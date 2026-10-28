/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Soundness

/-! # Adaptive exceptional-challenge bound

Only fresh live hashes can cancel their explanation's coefficient. Private randomness and
simulated signing preserve this event. The adversary's explicit hash budget plus the final
verification query bounds the total loss by `(qH + 1) / |F|`.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional
open scoped ENNReal

namespace Schnorr.AGM.Reduction

variable {F G M : Type}

/-- Select the adversary's live hash calls for the explicit query budget. -/
@[expose] def hashRequest (q : Explained F (Request M) (Group G)) : Bool :=
  match q.value.data with | .hash _ => true | _ => false

private theorem read_bad [Field F]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]
    (s : State F G M) (hb : s.bad = false) (key : M × G) (a : AffineForm F) :
    Pr{let p ← (read key a).run s}[p.2.bad = true] ≤ (Fintype.card F : ENNReal)⁻¹ := by
  cases hc : s.cache key with
  | some e => simp [read, StateT.run, hc, hb]
  | none =>
      simp only [read, StateT.run, hc, bind_pure_comp, prEvent_map,
        record, hb, Bool.false_or, decide_eq_true_eq, bad_challenge_iff]
      exact (SampleableType.prEvent_uniformSample_eq_singleton (-a.lin)).le

private theorem handler_bad [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]
    (g pk : G) (s : State F G M) (hb : s.bad = false)
    (q : Explained F (Request M) (Group G)) :
    Pr{let p ← (handler g pk q).run s}[p.2.bad = true] ≤
      if hashRequest q then (Fintype.card F : ENNReal)⁻¹ else 0 := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      by_cases he : groups () = [] <;>
        simp [handler, StateT.run, hashRequest, he, rejected, hb]
  | hash m =>
      simp only [handler, StateT.run, hashRequest, ite_true]
      split
      · rename_i R coeff hR hcoeff
        simpa only [bind_pure_comp, prEvent_map, Function.comp_def, StateT.run] using
          read_bad s hb (m, R) (flatten coeff s.representations)
      · simp [rejected, hb]
  | sign m =>
      by_cases he : groups () = []
      · simp only [handler, StateT.run, hashRequest, he, ne_eq, not_true_eq_false, ite_false]
        apply le_of_eq
        apply prEvent_eq_zero_of_forall_mem_support
        intro p hp hbad
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨c, _, z, _, rfl⟩ := hp
        simp [signedState, hb] at hbad
      · simp [handler, StateT.run, hashRequest, he, rejected, hb]

/-- The bound counts all hash calls, so it is valid under arbitrary adaptive repeats. -/
private theorem simulate_bad [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]
    (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (n : Nat) (hq : IsQueryBoundP program (fun q => hashRequest q = true) n)
    (s : State F G M) (hb : s.bad = false) :
    Pr{let p ← (simulateQ (handler g pk) program).run s}[p.2.bad = true] ≤
      (n : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  induction program using OracleComp.inductionOn generalizing s n with
  | pure out => simp [hb]
  | query_bind q next ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have hstep := handler_bad g pk s hb q
      have htail : ∀ p ∈ support ((handler g pk q).run s), ¬p.2.bad = true →
          Pr{let z ← (simulateQ (handler g pk) (next p.1)).run p.2}[z.2.bad = true] ≤
            ((if hashRequest q = true then n - 1 else n : Nat) : ENNReal) *
              (Fintype.card F : ENNReal)⁻¹ := by
        intro p _ hp
        exact ih p.1 _ (hq.2 p.1) p.2 (by simpa using hp)
      have hsplit := prEvent_bind_le_prEvent_add_of_support _ _ _ _ htail
      refine hsplit.trans ((add_le_add hstep le_rfl).trans ?_)
      by_cases hh : hashRequest q = true
      · have hn : 0 < n := hq.1.resolve_left (not_not.mpr hh)
        simp only [hh, ite_true]
        rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add]
        have he : 1 + (n - 1) = n := by omega
        rw [he]
      · simp [hh]

private theorem finish_bad [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]
    (g pk : G) (s : State F G M) (hb : s.bad = false)
    (out : Explained F (M × F) (Group G)) :
    Pr{let p ← (finish g pk out).run s}[p.2.bad = true] ≤
      (Fintype.card F : ENNReal)⁻¹ := by
  unfold finish
  split
  · rename_i R coeff hR hcoeff
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
    simpa only [bind_pure_comp, prEvent_map, Function.comp_def] using
      read_bad s hb (out.value.data.1, R) (flatten coeff s.representations)
  · simp [hb]

/-- The final verifier query adds one opportunity for the exceptional challenge. -/
theorem run_bad [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]
    (g pk : G) (adv : Schnorr.AlgebraicAdversary F G M) (qH : Nat)
    (hq : IsQueryBoundP (adv.main (initial g pk)) (fun q => hashRequest q = true) qH) :
    Pr{let p ← run g pk adv}[p.2.bad = true] ≤
      (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  simp only [run, StateT.run_bind]
  have htail : ∀ p ∈ support ((simulateQ (handler g pk) (adv.main (initial g pk))).run {}),
      ¬p.2.bad = true → Pr{let z ← (finish g pk p.1).run p.2}[z.2.bad = true] ≤
        (Fintype.card F : ENNReal)⁻¹ := by
    intro p _ hp
    exact finish_bad g pk p.2 (by simpa using hp) p.1
  refine (prEvent_bind_le_prEvent_add_of_support _ _ _ _ htail).trans ?_
  have hbody := simulate_bad g pk (adv.main (initial g pk)) qH hq {} rfl
  simpa only [add_mul, one_mul] using add_le_add hbody (le_refl (Fintype.card F : ENNReal)⁻¹)

/-- Accepted executions are bounded by correct extraction and one exceptional-challenge
term per hash query, including the final verification query. -/
theorem run_success_le [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]
    (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (adv : Schnorr.AlgebraicAdversary F G M) (qH : Nat)
    (hq : IsQueryBoundP (adv.main (initial g (x • g))) (fun q => hashRequest q = true) qH) :
    Pr{let p ← run g (x • g) adv}[p.1.1 = true] ≤
      Pr{let p ← run g (x • g) adv}[p.1.2 = x] +
        (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  have hsplit : Pr{let p ← run g (x • g) adv}[p.1.1 = true] ≤
      Pr{let p ← run g (x • g) adv}[p.1.2 = x] +
        Pr{let p ← run g (x • g) adv}[p.2.bad = true] := by
    refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le _ _ _)
    intro p hp hw
    by_cases hb : p.2.bad = true
    · exact Or.inr hb
    · exact Or.inl (run_extract g hg x adv p.1 p.2 hp hw (by simpa using hb))
  exact hsplit.trans (add_le_add le_rfl (run_bad g (x • g) adv qH hq))


/-- Averaging the single-pass bound gives the named reduction's success probability in
VCVio's existing discrete-log experiment, with the same exceptional-challenge loss. -/
theorem run_success_le_dlogExperiment [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]
    (g : G) (hg : Function.Injective (fun x : F => x • g))
    (A : Schnorr.AlgebraicAdversary F G M) (qH : ℕ)
    (hH : ∀ pk, IsQueryBoundP (A.main (initial g pk)) (fun q => hashRequest q = true) qH) :
    Pr{let x ← $ᵗ F; let p ← run g (x • g) A}[p.1.1 = true] ≤
      Pr{let b ← DiffieHellman.dlogExperiment g (Schnorr.agmReduction g A)}[b = true] +
        (qH + 1 : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace F := ⊤
  have h := MeasureTheory.lintegral_mono (μ := 𝒟[($ᵗ F : ProbComp F)])
    (fun x => run_success_le g hg x A qH (hH (x • g)))
  rw [MeasureTheory.lintegral_add_left Measurable.of_discrete,
    MeasureTheory.lintegral_const] at h
  simpa only [MeasureTheory.measure_univ, mul_one, prEvent_bind_of_discrete,
    DiffieHellman.dlogExperiment, Schnorr.agmReduction, prEvent_norm, decide_eq_true_eq] using h

end Schnorr.AGM.Reduction
