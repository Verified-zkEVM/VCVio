/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.Probability.ProbabilityMassFunction.TotalVariation
public import VCVio.EvalDist.Defs.Basic
public import VCVio.EvalDist.Monad.Basic
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Defs.Instances

/-!
# Total Variation Distance for SPMFs and Monadic Computations

This file extends the TV distance from `PMF` (defined in
`ToMathlib.Probability.ProbabilityMassFunction.TotalVariation`) to:

1. `SPMF.tvDist` — on sub-probability mass functions (via `toPMF`)
2. `tvDist` — on any monad with `MonadLiftT m SPMF` (via `evalSPMF`)
-/

@[expose] public section

noncomputable section

open ENNReal

universe u v

/-! ### SPMF.tvDist -/

namespace SPMF

variable {α : Type*}

/-- Total variation distance on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def tvDist (p q : SPMF α) : ℝ := p.toPMF.tvDist q.toPMF

@[simp] lemma tvDist_self (p : SPMF α) : p.tvDist p = 0 := PMF.tvDist_self _
lemma tvDist_comm (p q : SPMF α) : p.tvDist q = q.tvDist p := PMF.tvDist_comm _ _
lemma tvDist_nonneg (p q : SPMF α) : 0 ≤ p.tvDist q := PMF.tvDist_nonneg _ _

lemma tvDist_triangle (p q r : SPMF α) :
    p.tvDist r ≤ p.tvDist q + q.tvDist r := PMF.tvDist_triangle _ _ _

lemma tvDist_le_one (p q : SPMF α) : p.tvDist q ≤ 1 := PMF.tvDist_le_one _ _

@[simp] lemma tvDist_eq_zero_iff {p q : SPMF α} : p.tvDist q = 0 ↔ p.toPMF = q.toPMF :=
  PMF.tvDist_eq_zero_iff

universe w in
lemma tvDist_map_le {α' : Type w} {β : Type w} (f : α' → β)
    (p q : SPMF α') : SPMF.tvDist (f <$> p) (f <$> q) ≤ SPMF.tvDist p q := by
  simpa only [SPMF.tvDist, SPMF.toPMF_map] using PMF.tvDist_map_le (Option.map f) p.toPMF q.toPMF

universe w in
lemma tvDist_bind_right_le {α' : Type w} {β : Type w} (f : α' → SPMF β)
    (p q : SPMF α') : SPMF.tvDist (p >>= f) (q >>= f) ≤ SPMF.tvDist p q := by
  simpa only [SPMF.tvDist, SPMF.toPMF_bind, Option.elimM, PMF.monad_bind_eq_bind] using
    PMF.tvDist_bind_right_le _ p.toPMF q.toPMF

end SPMF

/-! ### Monadic tvDist -/

section monadic

variable {m : Type u → Type v} [MonadLiftT m SPMF] {α : Type u}

/-- Total variation distance between two monadic computations,
defined via their evaluation distributions. -/
noncomputable def tvDist (mx my : m α) : ℝ :=
  SPMF.tvDist (𝒮[mx]) (𝒮[my])

@[simp] lemma tvDist_self (mx : m α) : tvDist mx mx = 0 := SPMF.tvDist_self _

@[simp] lemma tvDist_eq_zero_iff (mx my : m α) :
    tvDist mx my = 0 ↔ 𝒮[mx] = 𝒮[my] := by
  simp only [tvDist, SPMF.tvDist_eq_zero_iff, SPMF.toPMF_inj]

lemma tvDist_comm (mx my : m α) : tvDist mx my = tvDist my mx :=
  SPMF.tvDist_comm _ _

lemma tvDist_nonneg (mx my : m α) : 0 ≤ tvDist mx my := SPMF.tvDist_nonneg _ _

lemma tvDist_triangle (mx my mz : m α) :
    tvDist mx mz ≤ tvDist mx my + tvDist my mz :=
  SPMF.tvDist_triangle _ _ _

lemma tvDist_le_one (mx my : m α) : tvDist mx my ≤ 1 := SPMF.tvDist_le_one _ _

lemma tvDist_map_le [Monad m] [LawfulMonadLiftT m SPMF] [LawfulMonad m] {β : Type u}
    (f : α → β) (mx my : m α) :
    tvDist (f <$> mx) (f <$> my) ≤ tvDist mx my := by
  simpa only [tvDist, evalSPMF_map] using SPMF.tvDist_map_le f (𝒮[mx]) (𝒮[my])

lemma tvDist_bind_right_le [Monad m] [LawfulMonadLiftT m SPMF] [LawfulMonad m] {β : Type u}
    (f : α → m β) (mx my : m α) :
    tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my := by
  simpa only [tvDist, evalSPMF_bind] using SPMF.tvDist_bind_right_le _ _ _

/-! ### TV distance bounds -/

/-- Total variation distance is bounded by the probability of an event `p` whenever the two
computations have equal output distribution off `p` (and equal probability of `p`). -/
lemma tvDist_le_probEvent_of_probOutput_eq_of_not [Monad m]
    {mx my : m α} [NeverFail mx] [NeverFail my]
    (p : α → Prop) (h_eq : ∀ x, ¬p x → Pr[= x | mx] = Pr[= x | my])
    (h_event_eq : Pr[ p | mx] = Pr[ p | my]) :
    tvDist mx my ≤ Pr[ p | mx].toReal := by
  classical
  rw [tvDist, SPMF.tvDist, PMF.tvDist]
  refine ENNReal.toReal_mono probEvent_ne_top ?_
  rw [PMF.etvDist, tsum_option _ ENNReal.summable]
  have hfailx : (𝒮[mx]).toPMF none = 0 := by
    simpa only [← SPMF.run_eq_toPMF, probFailure_def] using probFailure_eq_zero (mx := mx)
  have hfaily : (𝒮[my]).toPMF none = 0 := by
    simpa only [← SPMF.run_eq_toPMF, probFailure_def] using probFailure_eq_zero (mx := my)
  have hsum :
      (∑' x, ENNReal.absDiff ((𝒮[mx]).toPMF (some x)) ((𝒮[my]).toPMF (some x))) =
        ∑' x, ENNReal.absDiff (Pr[= x | mx]) (Pr[= x | my]) := by
    refine tsum_congr fun x => ?_
    simp [probOutput_def, SPMF.apply_eq_toPMF_some]
  rw [hfailx, hfaily, ENNReal.absDiff_self, zero_add, hsum]
  calc
    (∑' x, ENNReal.absDiff (Pr[= x | mx]) (Pr[= x | my])) / 2
      ≤ (∑' x, if p x then (Pr[= x | mx] + Pr[= x | my]) else 0) / 2 := by
          gcongr with x
          by_cases hx : p x
          · simpa [hx] using ENNReal.absDiff_le_add (Pr[= x | mx]) (Pr[= x | my])
          · simp [hx, h_eq x hx, ENNReal.absDiff_self]
    _ = (Pr[ p | mx] + Pr[ p | my]) / 2 := by
        rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
        exact congrArg (· / 2) (tsum_congr fun x => by by_cases hx : p x <;> simp [hx])
    _ = Pr[ p | mx] := by
        rw [← h_event_eq, ← two_mul, mul_div_assoc]
        simp [ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top]

end monadic

/-! ### TV distance for bind (left) -/

private lemma pmf_etvDist_bind_left_le {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    (p.bind f).etvDist (p.bind g) ≤ ∑' a, (f a).etvDist (g a) * p a := by
  have hrhs :
      (∑' a, (f a).etvDist (g a) * p a) =
        (∑' a, (∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) / 2 := by
    simp only [PMF.etvDist, div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_right_comm]
  rw [PMF.etvDist, hrhs]
  refine ENNReal.div_le_div_right ?_ 2
  calc ∑' y, ENNReal.absDiff (∑' x, p x * (f x) y) (∑' x, p x * (g x) y)
      ≤ ∑' y, ∑' x, ENNReal.absDiff (p x * (f x) y) (p x * (g x) y) :=
        ENNReal.tsum_le_tsum fun y => ENNReal.absDiff_tsum_le _ _
    _ ≤ ∑' y, ∑' x, ENNReal.absDiff ((f x) y) ((g x) y) * p x :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun x => by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            ENNReal.absDiff_mul_right_le ((f x) y) ((g x) y) (p x)
    _ = ∑' x, ∑' y, ENNReal.absDiff ((f x) y) ((g x) y) * p x := ENNReal.tsum_comm
    _ = ∑' x, (∑' y, ENNReal.absDiff ((f x) y) ((g x) y)) * p x := by
        simp_rw [ENNReal.tsum_mul_right]

private lemma pmf_tvDist_bind_left_le
    {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    PMF.tvDist (p.bind f) (p.bind g) ≤ ∑' a, (p a).toReal * PMF.tvDist (f a) (g a) := by
  simp only [PMF.tvDist]
  refine le_trans (ENNReal.toReal_mono ?_ (pmf_etvDist_bind_left_le p f g)) ?_
  · exact ne_top_of_le_ne_top one_ne_top (le_trans
      (ENNReal.tsum_le_tsum fun a => mul_le_mul' (PMF.etvDist_le_one _ _) le_rfl)
      (by simp [p.tsum_coe]))
  · refine le_of_eq ?_
    calc
      ((∑' a, (f a).etvDist (g a) * p a)).toReal
          = ∑' a, ((f a).etvDist (g a) * p a).toReal :=
            ENNReal.tsum_toReal_eq fun a =>
              ENNReal.mul_ne_top (PMF.etvDist_ne_top _ _) (PMF.apply_ne_top _ _)
      _ = ∑' a, (p a).toReal * PMF.tvDist (f a) (g a) := by
              refine tsum_congr fun a => ?_
              rw [ENNReal.toReal_mul, PMF.tvDist]
              ac_rfl

private lemma spmf_tvDist_bind_left_le_liftM
    {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    SPMF.tvDist
        ((liftM p : SPMF α) >>= fun a => liftM (f a))
        ((liftM p : SPMF α) >>= fun a => liftM (g a)) ≤
      ∑' a, (p a).toReal * SPMF.tvDist (liftM (f a)) (liftM (g a)) := by
  have h := pmf_tvDist_bind_left_le p (fun a => PMF.map Option.some (f a))
    (fun a => PMF.map Option.some (g a))
  simp_rw [← PMF.bind_pure_comp] at h
  simpa [SPMF.tvDist, SPMF.toPMF_bind, SPMF.toPMF_liftM, Option.elimM,
    PMF.monad_bind_eq_bind, Function.comp_def] using h

lemma tvDist_bind_left_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} {β : Type u}
    (mx : m α) (f g : α → m β) :
    tvDist (mx >>= f) (mx >>= g) ≤ ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a) := by
  rw [tvDist, evalSPMF_bind, evalSPMF_bind]
  simp_rw [evalSPMF_def]
  calc
    SPMF.tvDist
        ((liftM (liftM mx : PMF α) : SPMF α) >>= fun a => liftM (liftM (f a) : PMF β))
        ((liftM (liftM mx : PMF α) : SPMF α) >>= fun a => liftM (liftM (g a) : PMF β))
      ≤ ∑' a, ((liftM mx : PMF α) a).toReal *
          SPMF.tvDist (liftM (liftM (f a) : PMF β)) (liftM (liftM (g a) : PMF β)) :=
            spmf_tvDist_bind_left_le_liftM (liftM mx : PMF α)
              (fun a => (liftM (f a) : PMF β)) (fun a => (liftM (g a) : PMF β))
    _ = ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a) := by
          refine tsum_congr fun a => ?_
          have h1 : ((liftM mx : PMF α) a).toReal = Pr[= a | mx].toReal := by
            congr 1
            rw [probOutput_def, evalSPMF_def]
            exact (SPMF.liftM_apply (liftM mx : PMF α) a).symm
          have h2 : (liftM (liftM (f a) : PMF β) : SPMF β).tvDist
              (liftM (liftM (g a) : PMF β) : SPMF β) = tvDist (f a) (g a) := by
            rw [tvDist, evalSPMF_def, evalSPMF_def]
            rfl
          rw [h1, h2]

/-! ### TV distance for bind with a constant bound -/

/-- Total-variation distance is convex over a shared `bind`: if `tvDist (f a) (g a) ≤ c` for every
`a ∈ support mx`, then `tvDist (mx >>= f) (mx >>= g) ≤ c`. The real-valued root of the `const`
bound, with `ℝ≥0∞` companion `ofReal_tvDist_bind_left_le_const`. -/
theorem tvDist_bind_left_le_const
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadAttach m] [EvalDistCompatible m]
    {α β : Type u} (mx : m α) (f g : α → m β) (c : ℝ)
    (hfg : ∀ a, a ∈ support mx → tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c := by
  classical
  have hprob_ne_top : ∀ a : α, Pr[= a | mx] ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top one_ne_top (probOutput_le_one (mx := mx) (x := a))
  have hp_sum_ne_top : (∑' a : α, Pr[= a | mx]) ≠ ⊤ := by
    rw [tsum_probOutput_of_liftM_PMF]; exact one_ne_top
  have hp_summable : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal hp_sum_ne_top
  have hp_sum_toReal : (∑' a : α, Pr[= a | mx].toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq hprob_ne_top, tsum_probOutput_of_liftM_PMF, ENNReal.toReal_one]
  have hlhs_nonneg : ∀ a : α, 0 ≤ Pr[= a | mx].toReal * tvDist (f a) (g a) :=
    fun _ => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)
  have hlhs_le_p : ∀ a : α,
      Pr[= a | mx].toReal * tvDist (f a) (g a) ≤ Pr[= a | mx].toReal :=
    fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have hlhs_summable :
      Summable (fun a : α => Pr[= a | mx].toReal * tvDist (f a) (g a)) :=
    Summable.of_nonneg_of_le hlhs_nonneg hlhs_le_p hp_summable
  have hrhs_summable : Summable (fun a : α => Pr[= a | mx].toReal * c) :=
    Summable.mul_right _ hp_summable
  refine (tvDist_bind_left_le mx f g).trans ?_
  calc
    (∑' a : α, Pr[= a | mx].toReal * tvDist (f a) (g a))
        ≤ ∑' a : α, Pr[= a | mx].toReal * c :=
          Summable.tsum_le_tsum
            (fun a => by
              by_cases ha : a ∈ support mx
              · exact mul_le_mul_of_nonneg_left (hfg a ha) ENNReal.toReal_nonneg
              · rw [probOutput_eq_zero_of_not_mem_support ha]; simp)
            hlhs_summable hrhs_summable
    _ = (∑' a : α, Pr[= a | mx].toReal) * c := Summable.tsum_mul_right _ hp_summable
    _ = c := by rw [hp_sum_toReal, one_mul]

/-- `ℝ≥0∞` form of `tvDist_bind_left_le_const`, matching the quantitative APIs: a per-`a` bound
`ENNReal.ofReal (tvDist (f a) (g a)) ≤ ε` on the support of `mx` lifts through the shared bind. -/
theorem ofReal_tvDist_bind_left_le_const
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadAttach m] [EvalDistCompatible m]
    {α β : Type u}
    (mx : m α) (f g : α → m β) (ε : ℝ≥0∞)
    (hfg : ∀ a, a ∈ support mx → ENNReal.ofReal (tvDist (f a) (g a)) ≤ ε) :
    ENNReal.ofReal (tvDist (mx >>= f) (mx >>= g)) ≤ ε := by
  classical
  by_cases htop : ε = (⊤ : ℝ≥0∞)
  · simp [htop]
  · have hreal : tvDist (mx >>= f) (mx >>= g) ≤ ε.toReal :=
      tvDist_bind_left_le_const mx f g ε.toReal
        (fun a ha => (ENNReal.ofReal_le_iff_le_toReal htop).mp (hfg a ha))
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hreal

/-! ### TV distance for bind with a bad event -/

/-- Bound the weighted TV sum from `tvDist_bind_left_le` by the probability of a bad event
when the two continuations are distributionally equal off that event. -/
lemma tsum_probOutput_toReal_mul_tvDist_le_probEvent
    {m : Type u → Type v} [Monad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} {β : Type u}
    (mx : m α) (f g : α → m β) (bad : α → Prop)
    (h_eq : ∀ a, ¬ bad a → 𝒮[f a] = 𝒮[g a]) :
    (∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a))
      ≤ Pr[bad | mx].toReal := by
  classical
  have h_p_summable : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
  calc (∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a))
      ≤ ∑' a, if bad a then Pr[= a | mx].toReal else 0 := by
        refine Summable.tsum_le_tsum (fun a => ?_)
          (h_p_summable.of_nonneg_of_le
            (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
            (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)))
          (h_p_summable.of_nonneg_of_le
            (fun a => by by_cases ha : bad a <;> simp [ha, ENNReal.toReal_nonneg])
            (fun a => by by_cases ha : bad a <;> simp [ha, ENNReal.toReal_nonneg]))
        by_cases ha : bad a
        · simpa [ha] using
            mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one (f a) (g a))
        · simp [ha, (tvDist_eq_zero_iff (f a) (g a)).2 (h_eq a ha)]
    _ = Pr[bad | mx].toReal := by
        rw [probEvent_eq_tsum_ite, ENNReal.tsum_toReal_eq fun a => by
          by_cases ha : bad a
          · simp [ha, ne_top_of_le_ne_top one_ne_top (probOutput_le_one (mx := mx) (x := a))]
          · simp [ha]]
        exact tsum_congr fun a => by by_cases ha : bad a <;> simp [ha]

/-- If two continuations are equal off a bad event, binding them over the same base
computation changes TV distance by at most the probability of that bad event. -/
lemma tvDist_bind_left_event_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} {β : Type u}
    (mx : m α) (f g : α → m β) (bad : α → Prop)
    (h_eq : ∀ a, ¬ bad a → 𝒮[f a] = 𝒮[g a]) :
    tvDist (mx >>= f) (mx >>= g) ≤ Pr[bad | mx].toReal :=
  le_trans (tvDist_bind_left_le mx f g)
    (tsum_probOutput_toReal_mul_tvDist_le_probEvent mx f g bad h_eq)

/-- Bind/event TV bound with different base computations: the base TV distance plus the
bad-event probability controls the whole bind. -/
lemma tvDist_bind_event_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} {β : Type u}
    (mx my : m α) (f g : α → m β) (bad : α → Prop)
    (h_eq : ∀ a, ¬ bad a → 𝒮[f a] = 𝒮[g a]) :
    tvDist (mx >>= f) (my >>= g) ≤ Pr[bad | mx].toReal + tvDist mx my := by
  calc
    tvDist (mx >>= f) (my >>= g)
        ≤ tvDist (mx >>= f) (mx >>= g) + tvDist (mx >>= g) (my >>= g) :=
          tvDist_triangle _ _ _
    _ ≤ Pr[bad | mx].toReal + tvDist mx my :=
        add_le_add (tvDist_bind_left_event_le mx f g bad h_eq)
          (tvDist_bind_right_le g mx my)

/-- Bind/event TV bound with different base computations, charging the bad-event
probability under the right base computation. This is the symmetric orientation of
`tvDist_bind_event_le`, useful when the bad event is introduced by the simulated side. -/
lemma tvDist_bind_event_right_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} {β : Type u}
    (mx my : m α) (f g : α → m β) (bad : α → Prop)
    (h_eq : ∀ a, ¬ bad a → 𝒮[f a] = 𝒮[g a]) :
    tvDist (mx >>= f) (my >>= g) ≤ tvDist mx my + Pr[bad | my].toReal := by
  calc
    tvDist (mx >>= f) (my >>= g)
        ≤ tvDist (mx >>= f) (my >>= f) + tvDist (my >>= f) (my >>= g) :=
          tvDist_triangle _ _ _
    _ ≤ tvDist mx my + Pr[bad | my].toReal :=
        add_le_add (tvDist_bind_right_le f mx my)
          (tvDist_bind_left_event_le my f g bad h_eq)

/-- `ENNReal` form of `tvDist_bind_event_right_le`. -/
lemma ofReal_tvDist_bind_event_right_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} {β : Type u}
    (mx my : m α) (f g : α → m β) (bad : α → Prop)
    (h_eq : ∀ a, ¬ bad a → 𝒮[f a] = 𝒮[g a]) :
    ENNReal.ofReal (tvDist (mx >>= f) (my >>= g))
      ≤ ENNReal.ofReal (tvDist mx my) + Pr[bad | my] := by
  refine le_trans (ENNReal.ofReal_le_ofReal
    (tvDist_bind_event_right_le mx my f g bad h_eq)) ?_
  rw [ENNReal.ofReal_add (tvDist_nonneg mx my) ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal probEvent_ne_top]

section bool_tvdist

variable {m : Type → Type v} [MonadLiftT m SPMF]

/-- For any `Bool` computation, the difference of `Pr[= true]` values is bounded by
TV distance. -/
lemma abs_probOutput_toReal_sub_le_tvDist
    (game₁ game₂ : m Bool) :
    |Pr[= true | game₁].toReal - Pr[= true | game₂].toReal| ≤ tvDist game₁ game₂ := by
  simp only [probOutput_def, SPMF.apply_eq_toPMF_some, tvDist, SPMF.tvDist, PMF.tvDist]
  have happ : ∀ (p : PMF (Option Bool)),
      ((fun x : Option Bool => if x = some true then some () else none) <$> p) (some ()) =
        p (some true) := fun p => by
    simp [PMF.map_apply_eq, tsum_fintype]
  rw [← ENNReal.absDiff_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  apply ENNReal.toReal_mono (PMF.etvDist_ne_top _ _)
  rw [← happ (𝒮[game₁]).toPMF, ← happ (𝒮[game₂]).toPMF,
      ← PMF.etvDist_option_punit]
  exact PMF.etvDist_map_le (fun x : Option Bool => if x = some true then some () else none)
    (𝒮[game₁]).toPMF (𝒮[game₂]).toPMF

end bool_tvdist

end

/-! ## Total variation through a public projection

Two computations observed through maps that agree whenever the second output is the public
projection of the first and is not bad have total variation distance at most that of the public
projection plus the probability of the bad event. The supporting discrete lemmas collapse
lossless prefixes and condition a distribution on the fibers of a map. -/

universe u v

namespace OracleComp.ProgramLogic.Relational

universe w in
lemma spmf_bind_const_of_no_failure {α' β' : Type w}
    {p : SPMF α'} (hp : Pr[⊥ | p] = 0) (q : SPMF β') :
    (p >>= fun _ => q) = q := by
  apply SPMF.ext; intro y
  have h : Pr[= y | p >>= fun _ => q] = Pr[= y | q] := by
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, hp,
      tsub_zero, one_mul]
  simpa only [probOutput_def, evalSPMF_def, monadLift_self] using h

universe w in
lemma spmf_map_const_of_no_failure {α' β' : Type w}
    {p : SPMF α'} (hp : Pr[⊥ | p] = 0) (b : β') :
    ((fun _ : α' => b) <$> p) = (pure b : SPMF β') :=
  spmf_bind_const_of_no_failure hp (pure b : SPMF β')

universe w in
lemma spmf_bind_bind_const_of_no_failure {α' β' γ' : Type w}
    {p : SPMF α'} (hp : Pr[⊥ | p] = 0) (q : α' → SPMF β')
    (hq : ∀ a, Pr[⊥ | q a] = 0) (r : SPMF γ') :
    (p >>= fun a => q a >>= fun _ => r) = r := by
  calc
    (p >>= fun a => q a >>= fun _ => r)
        = p >>= fun _ => r := bind_congr fun a => spmf_bind_const_of_no_failure (hq a) r
    _ = r := spmf_bind_const_of_no_failure hp r

lemma probFailure_evalSPMF_eq_zero
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} (mx : m α) :
    Pr[⊥ | 𝒮[mx]] = 0 := by
  simpa only [probFailure_evalSPMF] using probFailure_eq_zero (mx := mx)

namespace PMF

/-- Fiber of a deterministic observation map. -/
def fiber {α β : Type*} (f : α → β) (b : β) : Set α := {a | f a = b}

/-- Conditional distribution of a PMF along a deterministic observation map.

For an observation value outside the support of `f <$> p`, the choice of
distribution is irrelevant; we use an arbitrary support point of `p`. -/
noncomputable def condOnMap {α β : Type*} (p : PMF α) (f : α → β) (b : β) : PMF α := by
    classical
    exact
      if h : ∃ a ∈ fiber f b, a ∈ p.support then
        p.filter (fiber f b) h
      else
        pure p.support_nonempty.some

lemma condOnMap_apply_of_not_mem_fiber {α β : Type*} (p : PMF α) (f : α → β)
    (b : β) {a : α} (ha : a ∉ fiber f b)
    (hb : ∃ a ∈ fiber f b, a ∈ p.support) :
    condOnMap p f b a = 0 := by
  rw [condOnMap, dite_eq_left hb]
  exact PMF.filter_apply_eq_zero_of_notMem (p := p) (s := fiber f b) (h := hb) ha

lemma condOnMap_apply_of_mem_support {α β : Type*} (p : PMF α) (f : α → β)
    {a : α} (ha : a ∈ p.support) :
    condOnMap p f (f a) a = p a * ((PMF.map f p) (f a))⁻¹ := by
  classical
  let : DecidableEq β := Classical.decEq β
  have hb : ∃ x ∈ fiber f (f a), x ∈ p.support := ⟨a, rfl, ha⟩
  rw [condOnMap, dite_eq_left hb, PMF.filter_apply,
    Set.indicator_of_mem (show a ∈ fiber f (f a) from rfl)]
  simp only [PMF.map_apply, Set.indicator_apply, fiber, Set.mem_ofPred_eq, eq_comm]

lemma map_bind_condOnMap {α β : Type*} (p : PMF α) (f : α → β) :
    (PMF.map f p).bind (condOnMap p f) = p := by
  classical
  ext a
  rw [PMF.bind_apply]
  by_cases ha : a ∈ p.support
  · have hsingle : ∀ b, b ≠ f a → (PMF.map f p) b * condOnMap p f b a = 0 := by
      intro b hb
      by_cases hbmem : ∃ x ∈ fiber f b, x ∈ p.support
      · rw [condOnMap_apply_of_not_mem_fiber p f b (fun h => hb h.symm) hbmem, mul_zero]
      · rw [show (PMF.map f p) b = 0 by
          rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
          exact fun ⟨x, hx, hfx⟩ => hbmem ⟨x, hfx, hx⟩, zero_mul]
    rw [tsum_eq_single (f a) hsingle, condOnMap_apply_of_mem_support p f ha, mul_comm, mul_assoc,
      ENNReal.inv_mul_cancel
        (by rw [← PMF.mem_support_iff, PMF.mem_support_map_iff]; exact ⟨a, ha, rfl⟩)
        (PMF.apply_ne_top _ _), mul_one]
  · rw [(PMF.apply_eq_zero_iff _ _).2 ha, ENNReal.tsum_eq_zero]
    intro b
    by_cases hbmem : ∃ x ∈ fiber f b, x ∈ p.support
    · rw [show condOnMap p f b a = 0 by
        rw [condOnMap, dite_eq_left hbmem, PMF.filter_apply_eq_zero_iff]; exact Or.inr ha, mul_zero]
    · rw [show (PMF.map f p) b = 0 by
        rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
        exact fun ⟨x, hx, hfx⟩ => hbmem ⟨x, hfx, hx⟩, zero_mul]

end PMF

namespace PMF

/-- Conditional output kernel induced by a deterministic observation map.

When the observation value is not in the support of `f <$> p`, the fallback
is used. Since the observation has zero mass there, this does not affect the
rebuilt distribution, but it makes pointwise continuation equalities easier
to state. -/
noncomputable def mapKernelWithFallback {α β γ : Type*}
    (p : PMF α) (f : α → β) (out : α → γ) (fallback : β → γ) (b : β) : PMF γ := by
    classical
    exact
      if h : ∃ a ∈ fiber f b, a ∈ p.support then
        PMF.map out (p.filter (fiber f b) h)
      else
        pure (fallback b)

lemma map_bind_mapKernelWithFallback {α β γ : Type*}
    (p : PMF α) (f : α → β) (out : α → γ) (fallback : β → γ) :
    (PMF.map f p).bind (mapKernelWithFallback p f out fallback) = PMF.map out p := by
  let K : β → PMF γ := fun b => PMF.map out (condOnMap p f b)
  have hbind :
      (PMF.map f p).bind (mapKernelWithFallback p f out fallback) =
        (PMF.map f p).bind K := by
    refine PMF.bind_congr (PMF.map f p) _ _ ?_
    intro b hb
    obtain ⟨a, ha, hfa⟩ := (PMF.mem_support_map_iff f p b).1 hb
    have hex : ∃ a ∈ fiber f b, a ∈ p.support := ⟨a, hfa, ha⟩
    simp only [K, mapKernelWithFallback, condOnMap, dite_eq_left hex]
  rw [hbind]
  simp only [K, ← PMF.map_bind, map_bind_condOnMap]

lemma mapKernelWithFallback_eq_pure_of {α β γ : Type*}
    (p : PMF α) (f : α → β) (out : α → γ) (fallback : β → γ)
    (bad : β → Prop)
    (h_eq : ∀ a b, f a = b → ¬ bad b → out a = fallback b)
    (b : β) (hb : ¬ bad b) :
    mapKernelWithFallback p f out fallback b = pure (fallback b) := by
  by_cases hex : ∃ a ∈ fiber f b, a ∈ p.support
  · rw [mapKernelWithFallback, dite_eq_left hex]
    refine PMF.eq_pure_of_forall_ne_eq_zero _ (fallback b) ?_
    intro y hy
    rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
    rintro ⟨a, ha, rfl⟩
    exact hy (h_eq a b ((PMF.mem_support_filter_iff hex).1 ha).1 hb)
  · rw [mapKernelWithFallback, dite_eq_right hex]

end PMF

theorem ofReal_tvDist_map_private_right_bad_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α β γ : Type u}
    (oa : m α) (ob : m β)
    (pub : α → β) (fa : α → γ) (fb : β → γ) (bad : β → Prop)
    (h_eq : ∀ a b, pub a = b → ¬ bad b → fa a = fb b) :
    ENNReal.ofReal (tvDist (fa <$> oa) (fb <$> ob))
      ≤ ENNReal.ofReal (tvDist (pub <$> oa) ob) + Pr[bad | ob] := by
  let p : PMF α := liftM oa
  let q : PMF β := liftM ob
  let K : β → PMF γ := PMF.mapKernelWithFallback p pub fa fb
  have hstep : ∀ b, ¬ bad b → 𝒮[K b] = 𝒮[(pure (fb b) : PMF γ)] := fun b hb =>
    congrArg evalSPMF (PMF.mapKernelWithFallback_eq_pure_of p pub fa fb bad h_eq b hb)
  have h :=
    ofReal_tvDist_bind_event_right_le
      (m := PMF) (mx := PMF.map pub p) (my := q)
      (f := K) (g := fun b => (pure (fb b) : PMF γ)) bad hstep
  have hK : (PMF.map pub p).bind K = PMF.map fa p :=
    PMF.map_bind_mapKernelWithFallback p pub fa fb
  have hq : q.bind (fun b => (pure (fb b) : PMF γ)) = PMF.map fb q := by
    simpa [Function.comp_def] using PMF.bind_pure_comp fb q
  have hp_pub : (liftM (pub <$> oa) : PMF β) = PMF.map pub p :=
    MonadHom.mmap_map (F := MonadHom.ofLift _ PMF) (x := oa) (g := pub)
  have hp_fa : (liftM (fa <$> oa) : PMF γ) = PMF.map fa p :=
    MonadHom.mmap_map (F := MonadHom.ofLift _ PMF) (x := oa) (g := fa)
  have hq_fb : (liftM (fb <$> ob) : PMF γ) = PMF.map fb q :=
    MonadHom.mmap_map (F := MonadHom.ofLift _ PMF) (x := ob) (g := fb)
  have hleft :
      tvDist (fa <$> oa) (fb <$> ob) =
        tvDist ((PMF.map pub p).bind K) (q.bind fun b => (pure (fb b) : PMF γ)) := by
    unfold tvDist
    rw [evalSPMF_def (fa <$> oa),
      evalSPMF_def (fb <$> ob),
      PMF.evalSPMF_eq ((PMF.map pub p).bind K),
      PMF.evalSPMF_eq (q.bind fun b => (pure (fb b) : PMF γ)),
      show (liftM (fa <$> oa) : SPMF γ) = liftM ((liftM (fa <$> oa) : PMF γ)) from rfl,
      show (liftM (fb <$> ob) : SPMF γ) = liftM ((liftM (fb <$> ob) : PMF γ)) from rfl,
      hp_fa, hq_fb, hK, hq]
  have hbase :
      tvDist (pub <$> oa) ob = tvDist (PMF.map pub p) q := by
    unfold tvDist
    rw [evalSPMF_def (pub <$> oa),
      evalSPMF_def ob,
      PMF.evalSPMF_eq (PMF.map pub p),
      PMF.evalSPMF_eq q,
      show (liftM (pub <$> oa) : SPMF β) = liftM ((liftM (pub <$> oa) : PMF β)) from rfl,
      show (liftM ob : SPMF β) = liftM ((liftM ob : PMF β)) from rfl,
      hp_pub]
  have hbad : Pr[bad | q] = Pr[bad | ob] := by
    rw [probEvent_def, probEvent_def]
    rfl
  simpa [hleft, hbase, hbad] using h

end OracleComp.ProgramLogic.Relational
