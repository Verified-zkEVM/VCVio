/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import ToMathlib.Probability.Divergence.RenyiChain
public import VCVio.OracleComp.SimSemantics.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.MeasureTVDist.Event
public import VCVio.EvalDist.MeasureTVDist.Bind

/-!
# Rényi and total-variation budgets along oracle simulations

`renyiMGF_simulateQ_le_of_pathSum` is the adaptive Rényi hybrid over the queries of an oracle
computation in budget form (Lemma 16 of De Almeida Braga, Fouque, Lachguel and Prest, ePrint
2026/1531): if every valid query `t` has its answer under `implQ` within Rényi MGF `exp(c · w t)` of
its answer under `implP`, every query made along every execution is valid (`AllQueriesSatisfy`),
and the weights of the queries made along every execution sum to at most `S` (`PathSum`), then the
simulated outputs are within `exp(c · S)`. The queries and their weights may depend on earlier
answers. Answers and outputs are discrete. Each step pairs a query with its continuation and
applies the different-kernel chain rule `InformationTheory.renyiMGF_bind_le`. `PathSum.bind` adds
budgets along `>>=`, and `PathSum.simulateQ_of_step` carries a budget through a simulation.

`measureETVDist_simulateQ_le_queryBoundP_mul` is the total-variation counterpart for
stateless handlers: handlers within `ε` on each charged query and equal on the others keep the
simulations of a computation making at most `n` charged queries within `n · ε`.

`IsQueryBoundP.simulateQ_of_step_le` carries a charged-query bound through a simulation whose
charged steps make at most `c` charged queries each.
-/

public section

open MeasureTheory InformationTheory OracleSpec
open scoped ENNReal

namespace OracleComp

section PathSum

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Along every execution of `oa`, the weights `w t` of the queries made sum to at most `S`. -/
inductive PathSum (w : ι → ℝ) : {α : Type} → OracleComp spec α → ℝ → Prop
  | pure {α : Type} (x : α) {S : ℝ} (h : 0 ≤ S) : PathSum w (pure x) S
  | query_bind {α : Type} (t : ι) (k : spec.Range t → OracleComp spec α) {S : ℝ}
      (h : ∀ u, PathSum w (k u) (S - w t)) : PathSum w (liftM (spec.query t) >>= k) S

/-- Raising the budget keeps a path sum. -/
theorem PathSum.weaken {w : ι → ℝ} {α : Type} {oa : OracleComp spec α} {S S' : ℝ}
    (h : PathSum w oa S) (hS : S ≤ S') : PathSum w oa S' := by
  induction h generalizing S' with
  | pure x h0 => exact .pure x (h0.trans hS)
  | query_bind t k _ ih => exact .query_bind t k fun u => ih u (by linarith)

/-- Path sums add along `>>=`. -/
theorem PathSum.bind {w : ι → ℝ} {α β : Type} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {S₁ S₂ : ℝ} (h₁ : PathSum w oa S₁)
    (h₂ : ∀ x, PathSum w (ob x) S₂) : PathSum w (oa >>= ob) (S₁ + S₂) := by
  induction h₁ with
  | pure x hS =>
    rw [pure_bind]
    exact (h₂ x).weaken (by linarith)
  | @query_bind t k S _ ih =>
    rw [bind_assoc]
    exact .query_bind t _ fun u => by
      have := ih u
      rwa [show S - w t + S₂ = S + S₂ - w t by ring] at this

/-- A computation whose queries all have weight `0` has path sum `0`. -/
theorem pathSum_zero_of_allQueriesSatisfy {w : ι → ℝ} {α : Type} {oa : OracleComp spec α}
    (h : AllQueriesSatisfy oa fun t => w t = 0) : PathSum w oa 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact .pure x le_rfl
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff t k _).1 h
    exact .query_bind t k fun u => by rw [ht, sub_zero]; exact ih u (hk u)

/-- A simulation whose charged steps have path sum at most `s₀ ≥ 0` and whose other steps have
path sum `0` has path sum at most `n · s₀` when the source makes at most `n` charged queries. -/
theorem PathSum.simulateQ_of_step {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} {w : ι' → ℝ}
    {p : ι → Prop} [DecidablePred p] {impl : QueryImpl spec (OracleComp spec')} {α : Type}
    {oa : OracleComp spec α} {n : ℕ} {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → PathSum w (impl t) s₀) (hstep_np : ∀ t, ¬ p t → PathSum w (impl t) 0) :
    PathSum w (simulateQ impl oa) (n * s₀) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => rw [simulateQ_pure]; exact .pure x (by positivity)
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    by_cases hpt : p t
    · have hn0 : 0 < n := h.1.resolve_left (not_not.2 hpt)
      have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn0, Nat.cast_one]
      refine ((hstep_p t hpt).bind fun u => ih u (by simpa [hpt] using h.2 u)).weaken
        (le_of_eq ?_)
      rw [hc]; ring
    · simpa using (hstep_np t hpt).bind fun u => ih u (by simpa [hpt] using h.2 u)

variable [∀ t, Countable (spec.Range t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Adaptive Rényi hybrid along executions.** If every valid query `t` has answer MGF at most
`exp(c · w t)`, every query along every execution is valid, and the weights along every
execution sum to at most `S`, the simulated outputs have MGF at most `exp(c · S)`. -/
theorem renyiMGF_simulateQ_le_of_pathSum {a : ℝ} (ha : 1 < a) (implQ implP : QueryImpl spec m)
    (V : ι → Prop) (w : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ t, V t → @renyiMGF _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (Real.exp (c * w t)))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp spec α) (hV : AllQueriesSatisfy oa V) {S : ℝ} (h : PathSum w oa S) :
    renyiMGF a 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] ≤
      ENNReal.ofReal (Real.exp (c * S)) := by
  induction h with
  | pure x hS =>
    simp only [simulateQ_pure, evalDist_pure]
    rw [renyiMGF_self, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hc hS))
  | @query_bind t k S _ ih =>
    obtain ⟨hVt, hVk⟩ := (allQueriesSatisfy_query_bind_iff t k V).1 hV
    let : MeasurableSpace (spec.Range t) := ⊤
    have : MeasurableSingletonClass (spec.Range t) := ⟨fun _ => trivial⟩
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    calc _ ≤ renyiMGF a 𝒟[implQ t] 𝒟[implP t] * ENNReal.ofReal (Real.exp (c * (S - w t))) :=
          renyiMGF_bind_le ha _ _ _ _ (fun _ => evalDist_apply_univ_le_one _)
            (fun _ => evalDist_apply_univ_le_one _) fun u => ih u (hVk u)
      _ ≤ ENNReal.ofReal (Real.exp (c * w t)) * ENNReal.ofReal (Real.exp (c * (S - w t))) := by
          gcongr; exact hB t hVt
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2; ring

end PathSum

section QueryBounds

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'} {α : Type}

/-- A simulation whose `p`-steps make at most `c` charged queries and whose other steps make none
makes at most `n · c` charged queries when the source makes at most `n` `p`-queries. -/
theorem IsQueryBoundP.simulateQ_of_step_le {p : ι → Prop} [DecidablePred p] {q : ι' → Prop}
    [DecidablePred q] {impl : QueryImpl spec (OracleComp spec')} {oa : OracleComp spec α}
    {n c : ℕ} (h : IsQueryBoundP oa p n) (hstep_p : ∀ t, p t → IsQueryBoundP (impl t) q c)
    (hstep_np : ∀ t, ¬ p t → IsQueryBoundP (impl t) q 0) :
    IsQueryBoundP (simulateQ impl oa) q (n * c) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    by_cases hpt : p t
    · have hn0 : 0 < n := h.1.resolve_left (not_not.2 hpt)
      have hbind := isQueryBoundP_bind (hstep_p t hpt)
        fun u _ => ih u (by simpa [hpt] using h.2 u)
      refine hbind.mono (le_of_eq ?_)
      conv_rhs => rw [← Nat.sub_add_cancel hn0]
      ring
    · have hbind := isQueryBoundP_bind (hstep_np t hpt)
        fun u _ => ih u (by simpa [hpt] using h.2 u)
      simpa using hbind

end QueryBounds

section TotalVariation

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
  [OracleSpec.AnswerMeasure spec'] {α : Type}

/-- **Query-bounded total-variation budget, stateless handlers.** Handlers within `ε` on each
charged query and equal on the others keep the simulations of a computation making at most `n`
charged queries within `n · ε`. -/
theorem measureETVDist_simulateQ_le_queryBoundP_mul [MeasurableSpace α]
    (impl₁ impl₂ : QueryImpl spec (OracleComp spec')) (S : ι → Prop) [DecidablePred S]
    {ε : ℝ≥0∞}
    (h_step_S : ∀ t, S t →
      letI : MeasurableSpace (spec.Range t) := ⊤
      measureETVDist (impl₁ t) (impl₂ t) ≤ ε)
    (h_step_nS : ∀ t, ¬ S t → impl₁ t = impl₂ t)
    (oa : OracleComp spec α) {n : ℕ} (h_qb : IsQueryBoundP oa S n) :
    measureETVDist (simulateQ impl₁ oa) (simulateQ impl₂ oa) ≤ n * ε := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp [measureETVDist_self]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h_qb
    obtain ⟨h_can, h_cont⟩ := h_qb
    simp only [simulateQ_bind, simulateQ_spec_query]
    let : MeasurableSpace (spec.Range t) := ⊤
    have : DiscreteMeasurableSpace (spec.Range t) := ⟨fun _ => trivial⟩
    set n' := if S t then n - 1 else n
    have hswap : measureETVDist (impl₁ t >>= fun u => simulateQ impl₂ (k u))
        (impl₂ t >>= fun u => simulateQ impl₂ (k u)) ≤ if S t then ε else 0 := by
      refine (measureETVDist_bind_le _ _ _ Measurable.of_discrete).trans ?_
      split_ifs with hS
      · exact h_step_S t hS
      · rw [h_step_nS t hS, measureETVDist_self]
    have hcont : measureETVDist (impl₁ t >>= fun u => simulateQ impl₁ (k u))
        (impl₁ t >>= fun u => simulateQ impl₂ (k u)) ≤ n' * ε := by
      refine (measureETVDist_bind_bind_le_lintegral _ _ _ Measurable.of_discrete
        Measurable.of_discrete (fun _ => n' * ε)
        (Filter.Eventually.of_forall fun u => ih u (h_cont u))).trans ?_
      rw [lintegral_const]
      exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
    calc _ ≤ _ := measureETVDist_triangle _ _ _
      _ ≤ n' * ε + if S t then ε else 0 := add_le_add hcont hswap
      _ ≤ n * ε := by
          by_cases hS : S t
          · have hpos : 0 < n := h_can.resolve_left (not_not.2 hS)
            have hq : ((n - 1 : ℕ) : ℝ≥0∞) + 1 = n := by
              exact_mod_cast Nat.sub_add_cancel hpos
            simp only [n', hS, ↓reduceIte]
            rw [← hq, add_mul, one_mul]
          · simp only [n', hS, ↓reduceIte, add_zero, le_refl]

end TotalVariation

end OracleComp
