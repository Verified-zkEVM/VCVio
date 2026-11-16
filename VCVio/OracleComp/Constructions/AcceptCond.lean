/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import VCVio.OracleComp.Constructions.RetryLoop
import VCVio.OracleComp.Constructions.UniformFinMeasure

/-! # The accept-conditional of a rejection sampler

For an attempt `attempt : ProbComp (Option α)` that accepts with positive probability,
`acceptCond attempt` is a `ProbComp α` whose law is that of `attempt` conditioned on acceptance:
`Pr[acceptCond attempt = x] = Pr[attempt = some x] / (1 - Pr[attempt = none])`. The attempt
resamples to it (`ResamplesTo`), and its support lies in the accepted outputs of `attempt`.

Existence (`exists_acceptCond`) needs every finitely supported law with rational point masses
to be the law of a `ProbComp`. When `attempt` rejects with probability one, `acceptCond`
returns `default`.
-/

public section

open OracleComp ENNReal

namespace ProbComp

variable {α : Type}

/-- Every `ProbComp` has the law of a function of a uniform draw from a nonempty finite type:
its point masses times `card D` are the fibre sizes of `f`. -/
private theorem exists_fintype_repr {β : Type} (oa : ProbComp β) :
    ∃ (D : Type) (_ : Fintype D) (f : D → β), 0 < Fintype.card D ∧
      ∀ x, Pr{let y ← oa}[y = x] * Fintype.card D = Nat.card {d // f d = x} := by
  classical
  induction oa using ProbComp.inductionOn with
  | pure a =>
    refine ⟨Unit, inferInstance, fun _ => a, Fintype.card_pos, fun x => ?_⟩
    rw [prEvent_pure, Nat.card_eq_fintype_card, Fintype.card_subtype]
    by_cases h : a = x <;> simp [h]
  | query_bind n mx ih =>
    choose D hD f hpos hf using ih
    have hf' : ∀ m x, Pr{let y ← mx m}[y = x] * Fintype.card (D m) =
        ((Finset.univ.filter fun d => f m d = x).card : ℝ≥0∞) := fun m x => by
      rw [hf m x, Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine ⟨Fin (n + 1) × ((m : Fin (n + 1)) → D m), inferInstance,
      fun g => f g.1 (g.2 g.1), Fintype.card_pos_iff.mpr
        ⟨(0, fun m => Classical.choice (Fintype.card_pos_iff.mp (hpos m)))⟩, fun x => ?_⟩
    have hu : ∀ m, Pr{let i ← $[0..n]}[i = m] = ((n : ℝ≥0∞) + 1)⁻¹ := fun m => by
      rw [ProbComp.prEvent_uniformFin, Finset.card_eq_one.mpr ⟨m, Finset.ext fun i => by simp⟩,
        Nat.cast_one, one_div]
    have hcount : ∀ m : Fin (n + 1),
        (Finset.univ.filter fun g : (m : Fin (n + 1)) → D m => f m (g m) = x).card =
          (Finset.univ.filter fun d => f m d = x).card *
            ∏ j ∈ Finset.univ.erase m, Fintype.card (D j) := fun m => by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g m)
        (t := Finset.univ.filter fun d => f m d = x) (fun g hg => by simpa using hg),
        Finset.card_eq_sum_ones (Finset.univ.filter fun d => f m d = x), Finset.sum_mul, one_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.filter_filter]
      have hfil : (Finset.univ.filter fun g : (m : Fin (n + 1)) → D m =>
          f m (g m) = x ∧ g m = a) =
          (Fintype.piFinset fun j => (Finset.univ : Finset (D j))).filter fun g => g m = a := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
          forall_const] at ha ⊢
        exact ⟨fun h => h.2, fun h => ⟨h ▸ ha, h⟩⟩
      rw [hfil]
      convert Fintype.card_filter_piFinset_eq_of_mem (fun j => (Finset.univ : Finset (D j))) m
        (Finset.mem_univ a) using 1
      simp only [Finset.card_univ]
    have hprod : (Finset.univ.filter fun g : Fin (n + 1) × ((m : Fin (n + 1)) → D m) =>
        f g.1 (g.2 g.1) = x).card =
        ∑ m, (Finset.univ.filter fun g : (m : Fin (n + 1)) → D m => f m (g m) = x).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun m _ => (Finset.card_filter _ _).symm
    rw [prEvent_bind_eq_sum_fintype, Fintype.card_prod, Fintype.card_fin, Fintype.card_pi,
      Nat.card_eq_fintype_card, Fintype.card_subtype, hprod]
    simp only [hcount, hu]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (Fintype.card (D j) : ℝ≥0∞))
      (Finset.mem_univ m), ← hf' m x]
    have hinv : ((n : ℝ≥0∞) + 1)⁻¹ * ((n : ℝ≥0∞) + 1) = 1 :=
      ENNReal.inv_mul_cancel (by simp) (by simp)
    calc ((n : ℝ≥0∞) + 1)⁻¹ * Pr{let y ← mx m}[y = x] *
          (((n : ℝ≥0∞) + 1) * ((Fintype.card (D m) : ℝ≥0∞) *
            ∏ j ∈ Finset.univ.erase m, (Fintype.card (D j) : ℝ≥0∞)))
        = (((n : ℝ≥0∞) + 1)⁻¹ * ((n : ℝ≥0∞) + 1)) *
            (Pr{let y ← mx m}[y = x] * Fintype.card (D m)) *
              ∏ j ∈ Finset.univ.erase m, (Fintype.card (D j) : ℝ≥0∞) := by ring
      _ = _ := by rw [hinv, one_mul]

/-- **An accept-conditional exists.** If `attempt` rejects with probability below one, some
`cond : ProbComp α` has the law of `attempt` conditioned on acceptance, is resampled to by
`attempt`, and is supported on the accepted outputs of `attempt`. -/
theorem exists_acceptCond (attempt : ProbComp (Option α))
    (h : Pr{let o ← attempt}[o = none] < 1) :
    ∃ cond : ProbComp α, ResamplesTo attempt cond ∧
      (∀ x, Pr{let y ← cond}[y = x] =
        Pr{let o ← attempt}[o = some x] / (1 - Pr{let o ← attempt}[o = none])) ∧
      ∀ x ∈ support cond, some x ∈ support attempt := by
  classical
  obtain ⟨D, _, f, hpos, hf⟩ := exists_fintype_repr attempt
  set N : ℕ := Fintype.card D with hNdef
  have hN : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpos.ne'
  have hNt : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hmass : ∀ o, Pr{let y ← attempt}[y = o] =
      ((Finset.univ.filter fun d => f d = o).card : ℝ≥0∞) / N := fun o =>
    (ENNReal.eq_div_iff hN hNt).mpr (by
      rw [mul_comm, hf o, Nat.card_eq_fintype_card, Fintype.card_subtype])
  obtain ⟨d₀, hd₀⟩ : ∃ d, f d ≠ none := by
    by_contra hno
    push Not at hno
    have h1 : Pr{let o ← attempt}[o = none] = 1 := by
      rw [hmass, Finset.filter_true_of_mem (fun d _ => hno d), Finset.card_univ]
      exact ENNReal.div_self hN hNt
    exact (lt_irrefl _) (h1 ▸ h)
  obtain ⟨a₀, -⟩ := Option.ne_none_iff_exists'.mp hd₀
  let P : D → Prop := fun d => f d ≠ none
  let F : D → α := fun d => (f d).getD a₀
  have : Nonempty {d // P d} := ⟨⟨d₀, hd₀⟩⟩
  have : Nonempty D := ⟨d₀⟩
  let : SampleableType D := SampleableType.ofFintype D
  let hS : SampleableType {d // P d} := SampleableType.ofFintype _
  have hg : (fun d => if P d then some (F d) else none) = f := funext fun d => by
    by_cases hd : f d = none
    · simp [P, hd]
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hd
      simp [P, F, ha]
  have hres := ResamplesTo.uniform_filter P F
  rw [hg] at hres
  set cond : ProbComp α := (fun δ : {d // P d} => F δ.1) <$> ($ᵗ {d // P d}) with hcond
  have hatt : f <$> ($ᵗ D) =ᵈ attempt := OracleComp.evalDistEq_of_forall_prEvent_eq_output
    fun o => by rw [hmass, prEvent_map, SampleableType.prEvent_uniformSample]
  -- the counts: `Z` rejecting, `K` accepting, `A` accepting with value `x`
  have hcard : ∀ x, Fintype.card {δ : {d // P d} // F δ.1 = x} =
      (Finset.univ.filter fun d => f d = some x).card := fun x => by
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter P fun d => F d = x),
      ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun d => ?_)
    by_cases hd : f d = none
    · simp [P, hd]
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hd
      simp [P, F, ha]
  have hK : Fintype.card {d // P d} + (Finset.univ.filter fun d => f d = none).card = N := by
    have hZ : (Finset.univ.filter fun d => f d = none) = Finset.univ.filter fun d => ¬ P d := by
      ext d
      simp [P]
    rw [Fintype.card_subtype, hZ, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  refine ⟨cond, ?_, fun x => ?_, fun x hx => ?_⟩
  · unfold ResamplesTo at hres ⊢
    exact (EvalDistEq.bind_left hatt.symm _).trans hres
  · rw [hcond, prEvent_map, SampleableType.prEvent_uniformSample, ← Fintype.card_subtype,
      hcard, hmass, hmass]
    set K := Fintype.card {d // P d}
    set Z := (Finset.univ.filter fun d => f d = none).card
    have h1 : 1 - (Z : ℝ≥0∞) / N = K / N := by
      rw [← ENNReal.div_self hN hNt, ← ENNReal.sub_div (fun _ _ => hN), ← ENNReal.natCast_sub,
        ← hK, Nat.add_sub_cancel]
    rw [h1]
    exact (ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.mpr hNt)
      (ENNReal.inv_ne_top.mpr hN)).symm
  · have hpos' : 0 < Pr{let y ← cond}[y = x] := (prEvent_pos_iff _ _).mpr ⟨x, hx, rfl⟩
    have hmem : 0 < Pr{let y ← attempt}[y = some x] := by
      rw [hcond, prEvent_map, SampleableType.prEvent_uniformSample, ← Fintype.card_subtype,
        hcard] at hpos'
      rw [hmass]
      exact ENNReal.div_pos (by
        intro h0; rw [h0, ENNReal.zero_div] at hpos'; exact lt_irrefl _ hpos') hNt
    obtain ⟨y, hy, hyx⟩ := (prEvent_pos_iff _ _).mp hmem
    exact hyx ▸ hy

open Classical in
/-- The accept-conditional of `attempt` (`exists_acceptCond`), or `default` when `attempt`
rejects with probability one. -/
noncomputable def acceptCond [Inhabited α] (attempt : ProbComp (Option α)) : ProbComp α :=
  if h : Pr{let o ← attempt}[o = none] < 1 then Classical.choose (exists_acceptCond attempt h)
  else pure default

/-- The defining properties of `acceptCond`. -/
theorem acceptCond_spec [Inhabited α] (attempt : ProbComp (Option α))
    (h : Pr{let o ← attempt}[o = none] < 1) :
    ResamplesTo attempt (acceptCond attempt) ∧
      (∀ x, Pr{let y ← acceptCond attempt}[y = x] =
        Pr{let o ← attempt}[o = some x] / (1 - Pr{let o ← attempt}[o = none])) ∧
      ∀ x ∈ support (acceptCond attempt), some x ∈ support attempt := by
  unfold acceptCond
  rw [dite_eq_left h]
  exact Classical.choose_spec (exists_acceptCond attempt h)

end ProbComp

end
