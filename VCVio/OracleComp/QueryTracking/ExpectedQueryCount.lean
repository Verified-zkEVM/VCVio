/-
Copyright (c) 2026 Emile. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emile
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Expected number of charged queries under a stateful probabilistic simulation

Ported from `formal/xmss/XmssSecurity/Proof/ExpectedQueryCount.lean` in
`github.com/leanEthereum/leanVM`, with every statement and proof restated in the
successful-output measure API.

`expectedSimulatedQueryCount so charged oa s` averages, over the runs of `oa` interpreted by
`so` from state `s`, the number of queries whose index satisfies `charged`.  The recursion is
structural in `oa` and the average over one interpreted step is a `lintegral` against that
step's successful-output measure, so nothing here needs the interpretation to be lossless.

The point of the definition is `expectedSimulatedQueryCount_le_of_isQueryBoundP`: a *pathwise*
charged-query budget `IsQueryBoundP oa charged q`, which is a syntactic property of `oa` alone,
already bounds the expected charged-query count in *every* stateful probabilistic
interpretation.  `lintegral_resource_le_add_expectedSimulatedQueryCount` then converts that
count into a bound on any resource that a charged step increases by at most one, which is the
shape a charging argument consumes.

Three statements expose an `∫⁻ … ∂𝒟[…]` and pin its measurable-space argument to `⊤` by a
`letI` inside the statement rather than taking it as an instance argument, so that the state
type stays unconstrained: `expectedSimulatedQueryCount_query_bind`,
`expectedSimulatedQueryCount_bind` and `lintegral_resource_le_add_expectedSimulatedQueryCount`.
A consumer of those three must repeat the pin in its own statement, and no bridge removes that
obligation: at a concrete state type an ambient instance does exist, but it is
`Prod.instMeasurableSpace`, a different term from `⊤` even where both of its components are
themselves `⊤`, so a statement that lets the instance be inferred does not typecheck against
these three.  The pin is not a formality a consumer can drop.  Every other statement here
mentions no measure and carries no pin.
-/

public section

open MeasureTheory OracleSpec
open scoped ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β σ : Type}

/-! ### Integrals against a subprobability measure -/

/-- A uniform bound on the integrand bounds its integral against a subprobability measure. -/
private lemma lintegral_evalDist_le_of_le {γ : Type} [MeasurableSpace γ] (mx : ProbComp γ)
    {f : γ → ℝ≥0∞} {c : ℝ≥0∞} (hf : ∀ z, f z ≤ c) : ∫⁻ z, f z ∂𝒟[mx] ≤ c :=
  calc ∫⁻ z, f z ∂𝒟[mx] ≤ ∫⁻ _, c ∂𝒟[mx] := lintegral_mono hf
    _ = c * 𝒟[mx] Set.univ := lintegral_const c
    _ ≤ c * 1 := by gcongr; exact evalDist_apply_univ_le_one mx
    _ = c := mul_one c

/-- A bound holding on every possible output bounds the integral against a subprobability
measure. -/
private lemma lintegral_evalDist_le_of_le_of_mem_support {γ : Type} [MeasurableSpace γ]
    [DiscreteMeasurableSpace γ] (mx : ProbComp γ) {f : γ → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ z ∈ support mx, f z ≤ c) :
    ∫⁻ z, f z ∂𝒟[mx] ≤ c :=
  calc ∫⁻ z, f z ∂𝒟[mx] ≤ ∫⁻ _, c ∂𝒟[mx] :=
        lintegral_mono_ae (evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete hf)
    _ = c * 𝒟[mx] Set.univ := lintegral_const c
    _ ≤ c * 1 := by gcongr; exact evalDist_apply_univ_le_one mx
    _ = c := mul_one c

/-! ### The expected charged-query count -/

/-- The expected number of queries with a `charged` index made by `oa` when it is interpreted by
the stateful probabilistic implementation `so` started from state `s`.  Each interpreted step
contributes the indicator of its index and the average of the remaining count over that step's
successful outputs. -/
@[expose]
noncomputable def expectedSimulatedQueryCount (so : QueryImpl spec (StateT σ ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (oa : OracleComp spec α)
    (s : σ) : ℝ≥0∞ :=
  OracleComp.recOn (motive := fun _ => σ → ℝ≥0∞) oa (fun _ _ => 0)
    (fun t _ tail s' =>
      letI : MeasurableSpace (spec.Range t × σ) := ⊤
      (if charged t then 1 else 0) + ∫⁻ z, tail z.1 z.2 ∂𝒟[(so t).run s']) s

variable (so : QueryImpl spec (StateT σ ProbComp)) (charged : spec.Domain → Prop)
  [DecidablePred charged]

@[simp]
theorem expectedSimulatedQueryCount_pure (x : α) (s : σ) :
    expectedSimulatedQueryCount so charged (pure x : OracleComp spec α) s = 0 :=
  rfl

/-- The defining equation of `expectedSimulatedQueryCount` on a query step. -/
@[simp]
theorem expectedSimulatedQueryCount_query_bind (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) (s : σ) :
    letI : MeasurableSpace (spec.Range t × σ) := ⊤
    expectedSimulatedQueryCount so charged (liftM (spec.query t) >>= k) s =
      (if charged t then 1 else 0) +
        ∫⁻ z, expectedSimulatedQueryCount so charged (k z.1) z.2 ∂𝒟[(so t).run s] :=
  rfl

/-- A single query contributes exactly the indicator of its index.  This is the `pure`-free
companion of `expectedSimulatedQueryCount_query_bind`, which `simp` cannot reach on its own
because `bind_pure` normalises away the `>>= k` shape that equation matches. -/
@[simp]
theorem expectedSimulatedQueryCount_query (t : spec.Domain) (s : σ) :
    expectedSimulatedQueryCount so charged
        (liftM (spec.query t) : OracleComp spec (spec.Range t)) s =
      if charged t then 1 else 0 := by
  let _ : MeasurableSpace (spec.Range t × σ) := ⊤
  rw [show (liftM (spec.query t) : OracleComp spec (spec.Range t)) =
      liftM (spec.query t) >>= pure from (bind_pure _).symm,
    expectedSimulatedQueryCount_query_bind]
  simp

/-- **A pathwise charged-query bound controls the expected count in every interpretation.**
`IsQueryBoundP oa charged q` constrains `oa` alone, yet bounds the expected charged-query count
of `oa` under an arbitrary stateful probabilistic implementation started from an arbitrary
state. -/
theorem expectedSimulatedQueryCount_le_of_isQueryBoundP (oa : OracleComp spec α) (s : σ) (q : ℕ)
    (hq : oa.IsQueryBoundP charged q) :
    expectedSimulatedQueryCount so charged oa s ≤ q := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure x => simp
  | query_bind t k ih =>
    let _ : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [expectedSimulatedQueryCount_query_bind]
    by_cases ht : charged t
    · have hq1 : 1 ≤ q := hq.1.resolve_left (not_not.mpr ht)
      simp only [ht, ite_true]
      rw [← Nat.cast_one (R := ℝ≥0∞), ← Nat.add_sub_of_le hq1, Nat.cast_add]
      exact add_le_add le_rfl (lintegral_evalDist_le_of_le ((so t).run s) fun z =>
        ih z.1 z.2 (q - 1) (by simpa [ht] using hq.2 z.1))
    · simp only [ht, ite_false, zero_add]
      exact lintegral_evalDist_le_of_le ((so t).run s) fun z =>
        ih z.1 z.2 q (by simpa [ht] using hq.2 z.1)

/-- Enlarging the charged predicate can only increase the expected count. -/
theorem expectedSimulatedQueryCount_mono (left right : spec.Domain → Prop) [DecidablePred left]
    [DecidablePred right] (hsub : ∀ t, left t → right t) (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so left oa s ≤ expectedSimulatedQueryCount so right oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
    refine add_le_add ?_ (lintegral_mono fun z => ih z.1 z.2)
    by_cases hl : left t
    · simp [hl, hsub t hl]
    · simp [hl]

/-- The tower law: the expected count of a bind is the count of its head plus the average
continuation count over the head's interpreted outputs. -/
theorem expectedSimulatedQueryCount_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (s : σ) :
    letI : MeasurableSpace (α × σ) := ⊤
    expectedSimulatedQueryCount so charged (oa >>= ob) s =
      expectedSimulatedQueryCount so charged oa s +
        ∫⁻ z, expectedSimulatedQueryCount so charged (ob z.1) z.2
          ∂𝒟[(simulateQ so oa).run s] := by
  let _ : MeasurableSpace (α × σ) := ⊤
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    let _ : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [bind_assoc, expectedSimulatedQueryCount_query_bind,
      expectedSimulatedQueryCount_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
    simp only [ih]
    rw [lintegral_add_left Measurable.of_discrete, add_assoc]

@[simp]
theorem expectedSimulatedQueryCount_map (f : α → β) (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so charged (f <$> oa) s =
      expectedSimulatedQueryCount so charged oa s := by
  rw [map_eq_bind_pure_comp, expectedSimulatedQueryCount_bind]
  simp

/-- **Charging a resource against the expected count.**  A resource that grows by at most one on
each interpreted charged step, and not at all on an uncharged one, has expected final value at
most its initial value plus the expected charged-query count. -/
theorem lintegral_resource_le_add_expectedSimulatedQueryCount (resource : σ → ℝ≥0∞)
    (hstep : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s),
      resource z.2 ≤ resource s + if charged t then 1 else 0)
    (oa : OracleComp spec α) (s : σ) :
    letI : MeasurableSpace (α × σ) := ⊤
    ∫⁻ z, resource z.2 ∂𝒟[(simulateQ so oa).run s] ≤
      resource s + expectedSimulatedQueryCount so charged oa s := by
  let _ : MeasurableSpace (α × σ) := ⊤
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    let _ : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete,
      expectedSimulatedQueryCount_query_bind]
    calc ∫⁻ z, ∫⁻ w, resource w.2 ∂𝒟[(simulateQ so (k z.1)).run z.2] ∂𝒟[(so t).run s]
        ≤ ∫⁻ z, (resource z.2 + expectedSimulatedQueryCount so charged (k z.1) z.2)
            ∂𝒟[(so t).run s] := lintegral_mono fun z => ih z.1 z.2
      _ = (∫⁻ z, resource z.2 ∂𝒟[(so t).run s]) +
            ∫⁻ z, expectedSimulatedQueryCount so charged (k z.1) z.2 ∂𝒟[(so t).run s] :=
          lintegral_add_left Measurable.of_discrete _
      _ ≤ (resource s + if charged t then 1 else 0) +
            ∫⁻ z, expectedSimulatedQueryCount so charged (k z.1) z.2 ∂𝒟[(so t).run s] :=
          add_le_add (lintegral_evalDist_le_of_le_of_mem_support _ (hstep t s)) le_rfl
      _ = resource s + ((if charged t then 1 else 0) +
            ∫⁻ z, expectedSimulatedQueryCount so charged (k z.1) z.2 ∂𝒟[(so t).run s]) :=
          add_assoc _ _ _

/-- Expected counts add exactly over disjoint charged predicates. -/
theorem expectedSimulatedQueryCount_or_of_disjoint (left right : spec.Domain → Prop)
    [DecidablePred left] [DecidablePred right] (hdisj : ∀ t, ¬(left t ∧ right t))
    (oa : OracleComp spec α) (s : σ) :
    expectedSimulatedQueryCount so (fun t => left t ∨ right t) oa s =
      expectedSimulatedQueryCount so left oa s + expectedSimulatedQueryCount so right oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    let _ : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind,
      expectedSimulatedQueryCount_query_bind]
    have hind : (if left t ∨ right t then (1 : ℝ≥0∞) else 0) =
        (if left t then 1 else 0) + (if right t then 1 else 0) := by
      by_cases hl : left t <;> by_cases hr : right t
      · exact absurd ⟨hl, hr⟩ (hdisj t)
      all_goals simp [hl, hr]
    simp only [ih, hind]
    rw [lintegral_add_left Measurable.of_discrete]
    ac_rfl

end OracleComp
