/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.MeasureTVDist.Bind
public import ToMathlib.MeasureTheory.Integral.Countable

/-!
# Output-mass sums of oracle computations

An oracle computation with finite answer types reaches finitely many outputs, so its output
measure is the sum of its singleton masses. The integral of a functional is then the sum
`∑' x, Pr{let y ← oa}[y = x] * f x` over the whole output type, with no countability assumption on
that type. This module states that identity and the sum forms of the bind, `pure`, map and total
variation laws, for arguments that are clearest as weighted sums over outputs.

The integral forms (`∫⁻ x, f x ∂𝒟[oa]`, `lintegral_evalDist_bind`, `wp`) remain the primary API;
these sums are equal to them.
-/

public section

open MeasureTheory
open scoped ENNReal

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.IsMeasureSpec spec] {α β : Type}

/-- The output measure is concentrated on the reachable outputs. -/
theorem evalDist_ae_mem_support [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (oa : OracleComp spec α) : ∀ᵐ x ∂𝒟[oa], x ∈ support oa :=
  evalDist.ae_of_forall_mem_support oa (· ∈ support oa) MeasurableSet.of_discrete fun _ h ↦ h

variable [∀ t, Finite (spec.Range t)]

/-- An integral against the output measure is the sum of the singleton masses times the
integrand. -/
theorem lintegral_evalDist_eq_tsum [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (oa : OracleComp spec α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂𝒟[oa] = ∑' x, Pr{let y ← oa}[y = x] * f x := by
  rw [lintegral_eq_tsum_mul_of_ae_mem_countable (support_finite oa).countable
    (evalDist_ae_mem_support oa)]
  simp only [prEvent_eq_evalDist_singleton]

/-- The singleton masses of an oracle computation sum to one. -/
@[simp]
theorem tsum_prEvent_eq_one (oa : OracleComp spec α) : ∑' x, Pr{let y ← oa}[y = x] = 1 := by
  let : MeasurableSpace α := ⊤
  have h := lintegral_evalDist_eq_tsum oa fun _ ↦ 1
  simp only [mul_one, lintegral_const, one_mul] at h
  rw [← h, ← prEvent_true_eq_evalDist_apply_univ, prEvent_true_eq_one]

/-- The singleton masses of an oracle computation sum to at most one. -/
theorem tsum_prEvent_le_one (oa : OracleComp spec α) : ∑' x, Pr{let y ← oa}[y = x] ≤ 1 :=
  (tsum_prEvent_eq_one oa).le

/-- An event after a bind is the weighted sum, over the prefix's outputs, of the continuation's
event. The prefix's output type needs no countability. -/
theorem prEvent_bind_eq_tsum (oa : OracleComp spec α) (g : α → OracleComp spec β)
    (p : β → Prop) :
    Pr{let y ← oa >>= g}[p y] = ∑' x, Pr{let z ← oa}[z = x] * Pr{let y ← g x}[p y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, lintegral_evalDist_eq_tsum]

/-- A bind of event computations is the prefix-weighted sum of the continuation's events. This is
the form events take after `simp` pushes the event inside a bind. -/
theorem prEvent_bind_eq_tsum_prEvent (oa : OracleComp spec α) (g : α → OracleComp spec Prop) :
    prEvent (oa >>= g) = ∑' x, Pr{let z ← oa}[z = x] * prEvent (g x) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_of_discrete, lintegral_evalDist_eq_tsum]

/-- An event is the sum of the singleton masses of the outputs satisfying it. -/
theorem prEvent_eq_tsum_ite (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr{let y ← oa}[p y] = ∑' x, if p x then Pr{let y ← oa}[y = x] else 0 := by
  have h := prEvent_bind_eq_tsum oa pure p
  rw [bind_pure] at h
  rw [h]
  refine tsum_congr fun x ↦ ?_
  rw [prEvent_pure]
  split_ifs <;> simp

/-- First-moment (Markov) bound: a weight that is at least one on the event bounds the event's
probability by the weighted sum. -/
theorem prEvent_le_tsum_prEvent_mul_cost (oa : OracleComp spec α) (p : α → Prop) (c : α → ℝ≥0∞)
    (hc : ∀ x, p x → 1 ≤ c x) : Pr{let y ← oa}[p y] ≤ ∑' x, Pr{let y ← oa}[y = x] * c x := by
  classical
  rw [prEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  split_ifs with hx
  · exact le_mul_of_one_le_right' (hc x hx)
  · exact zero_le

/-- A weighted sum over the outputs of a bind is the weighted sum over the prefix's outputs of the
continuation's weighted sums. -/
theorem tsum_prEvent_bind_mul (oa : OracleComp spec α) (g : α → OracleComp spec β)
    (f : β → ℝ≥0∞) :
    ∑' z, Pr{let y ← oa >>= g}[y = z] * f z =
      ∑' x, Pr{let y ← oa}[y = x] * ∑' z, Pr{let y ← g x}[y = z] * f z := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  simp only [← lintegral_evalDist_eq_tsum]
  exact lintegral_evalDist_bind_of_discrete oa g .of_discrete

/-- A weighted sum over the outputs of a map is the weighted sum over the source outputs. -/
theorem tsum_prEvent_map_mul (oa : OracleComp spec α) (h : α → β) (f : β → ℝ≥0∞) :
    ∑' z, Pr{let y ← h <$> oa}[y = z] * f z = ∑' x, Pr{let y ← oa}[y = x] * f (h x) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  simp only [← lintegral_evalDist_eq_tsum]
  exact lintegral_evalDist_map_of_discrete oa h f

/-- A weighted sum over the outputs of `pure a` is the weight at `a`. -/
theorem tsum_prEvent_pure_mul (a : α) (f : α → ℝ≥0∞) :
    ∑' z, Pr{let y ← (pure a : OracleComp spec α)}[y = z] * f z = f a := by
  let : MeasurableSpace α := ⊤
  rw [← lintegral_evalDist_eq_tsum, evalDist_pure, lintegral_dirac]

/-- A functional constant on the reachable outputs has that constant as its weighted sum. -/
theorem tsum_prEvent_mul_of_const_on_support (oa : OracleComp spec α) {f : α → ℝ≥0∞}
    {c : ℝ≥0∞} (h : ∀ x ∈ support oa, f x = c) : ∑' x, Pr{let y ← oa}[y = x] * f x = c := by
  let : MeasurableSpace α := ⊤
  rw [← lintegral_evalDist_eq_tsum,
    lintegral_congr_ae ((evalDist_ae_mem_support oa).mono fun x hx ↦ h x hx), lintegral_const,
    ← prEvent_true_eq_evalDist_apply_univ, prEvent_true_eq_one, mul_one]

/-- A pointwise bound `f ≤ C + g` bounds the weighted sums, the constant counted once. -/
theorem tsum_prEvent_mul_le_add_of_le (oa : OracleComp spec α) {f g : α → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ x, f x ≤ C + g x) :
    ∑' x, Pr{let y ← oa}[y = x] * f x ≤ C + ∑' x, Pr{let y ← oa}[y = x] * g x := by
  let : MeasurableSpace α := ⊤
  simp only [← lintegral_evalDist_eq_tsum]
  calc ∫⁻ x, f x ∂𝒟[oa] ≤ ∫⁻ x, C + g x ∂𝒟[oa] := lintegral_mono h
    _ = C * 𝒟[oa] Set.univ + ∫⁻ x, g x ∂𝒟[oa] := by
      rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ C + ∫⁻ x, g x ∂𝒟[oa] := by
      gcongr
      exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one oa)

/-- The total variation after a common prefix is at most the prefix-weighted sum of the
continuations' total variations. -/
theorem measureETVDist_bind_left_le_tsum [MeasurableSpace β] (oa : OracleComp spec α)
    (f g : α → OracleComp spec β) :
    measureETVDist (oa >>= f) (oa >>= g) ≤
      ∑' x, Pr{let y ← oa}[y = x] * measureETVDist (f x) (g x) := by
  let : MeasurableSpace α := ⊤
  rw [← lintegral_evalDist_eq_tsum]
  exact measureETVDist_bind_bind_le_lintegral oa f g .of_discrete .of_discrete _
    (Filter.Eventually.of_forall fun _ ↦ le_rfl)

end OracleComp
