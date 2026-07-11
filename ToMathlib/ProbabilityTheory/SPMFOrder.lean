/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.ProbabilityTheory.SPMF
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# The Subprobability Order on `SPMF`

The pointwise order on subprobability distributions — `p ≤ q` iff every output of `p`
has no more mass than under `q` — with `failure` (all mass missing) as the bottom
element, and its ω-complete partial order structure: every increasing chain has a
least upper bound, constructed by taking pointwise suprema of output masses and
assigning the residual to the missing-mass fiber (monotone convergence keeps the
total at `1`).

This is the classic subprobability domain. It is deliberately **not** a lattice —
the pointwise join of two subdistributions can exceed total mass `1` — so chains are
the honest completeness structure. `bind` is monotone in both arguments and
ω-continuous in each (`ωSup_bind`, `bind_ωSup`), which is what fuelled-run suprema
and their fixpoint equations need.

The file also provides `SPMF.joinOption`, merging an `Option` layer of *outcomes*
into the failure mass (`none ↦ failure`): the quotient along which fuel-exhaustion of
a truncated run is identified with missing mass, making fuelled machine runs monotone
in their fuel (see `VCVio.OracleComp.Coinductive.RunLimit`).

`ENNReal.tsum_iSup_of_monotone` (monotone convergence for `tsum` along ℕ-chains) is
proved here and is a candidate for upstreaming to Mathlib.
-/

@[expose] public section

open ENNReal OmegaCompletePartialOrder

universe u

variable {α β : Type u}

namespace ENNReal

/-- Monotone convergence for `tsum` over a monotone ℕ-indexed family: the sum of
pointwise suprema is the supremum of the sums. Candidate for upstreaming (the
directed-index generalization is the Mathlib-preferred form). -/
theorem tsum_iSup_of_monotone {ι : Type*} {f : ℕ → ι → ℝ≥0∞} (hf : Monotone f) :
    ∑' x, ⨆ k, f k x = ⨆ k, ∑' x, f k x := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  refine iSup_congr fun s => ?_
  exact ENNReal.finsetSum_iSup_of_monotone fun x i j h => hf h x

end ENNReal

namespace SPMF

/-! ## The pointwise order -/

noncomputable instance : PartialOrder (SPMF α) :=
  PartialOrder.lift (fun p => (p : α → ℝ≥0∞)) DFunLike.coe_injective

lemma le_iff_forall {p q : SPMF α} : p ≤ q ↔ ∀ x, p x ≤ q x := Iff.rfl

lemma le_of_forall {p q : SPMF α} (h : ∀ x, p x ≤ q x) : p ≤ q := h

lemma apply_le_apply {p q : SPMF α} (h : p ≤ q) (x : α) : p x ≤ q x := h x

noncomputable instance : OrderBot (SPMF α) where
  bot := failure
  bot_le p x := by simp

@[simp] lemma bot_eq_failure : (⊥ : SPMF α) = failure := rfl

/-- The total output mass of a subdistribution is at most one. -/
lemma tsum_apply_le_one (p : SPMF α) : ∑' x, p x ≤ 1 :=
  le_of_le_of_eq (le_add_self) (run_none_add_tsum_run_some p)

/-- Larger subdistributions have smaller missing mass. -/
lemma gap_antitone {p q : SPMF α} (h : p ≤ q) : q.gap ≤ p.gap := by
  rw [gap_eq_one_sub_tsum, gap_eq_one_sub_tsum]
  exact tsub_le_tsub_left (ENNReal.tsum_le_tsum fun x => h x) 1

/-- The total output mass is one exactly when nothing is missing. -/
lemma tsum_apply_eq_one_of_gap_eq_zero {p : SPMF α} (h : p.gap = 0) : ∑' x, p x = 1 := by
  refine le_antisymm (tsum_apply_le_one p) ?_
  rw [gap_eq_one_sub_tsum, tsub_eq_zero_iff_le] at h
  exact h

/-- Dirac masses have no missing mass. -/
@[simp] lemma gap_pure (x : α) : (pure x : SPMF α).gap = 0 := by
  rw [gap_eq_one_sub_tsum,
    tsum_eq_single x fun y hy => (pure_apply_eq_zero_iff x y).mpr hy]
  simp

/-- Lifted full distributions have no missing mass. -/
@[simp] lemma gap_liftM (p : PMF α) : (liftM p : SPMF α).gap = 0 := by
  rw [gap_eq_one_sub_tsum]
  simp [SPMF.liftM_apply, p.tsum_coe]

/-- Binding a lossless subdistribution into a constant continuation is that constant. -/
lemma bind_const_of_gap_eq_zero {p : SPMF α} (h : p.gap = 0) (q : SPMF β) :
    (p >>= fun _ => q) = q := by
  refine SPMF.ext fun y => ?_
  rw [bind_apply_eq_tsum, ENNReal.tsum_mul_right, tsum_apply_eq_one_of_gap_eq_zero h,
    one_mul]

/-- Full-mass subdistributions are maximal in the pointwise order. -/
lemma eq_of_le_of_gap_eq_zero {p q : SPMF α} (h : p ≤ q) (hp : p.gap = 0) : p = q := by
  refine SPMF.ext fun x => le_antisymm (h x) (not_lt.mp fun hx => ?_)
  have hps : ∑' y, p y = 1 := tsum_apply_eq_one_of_gap_eq_zero hp
  have hlt : ∑' y, p y < ∑' y, q y :=
    ENNReal.tsum_lt_tsum (hps ▸ one_ne_top) (fun y => h y) hx
  exact absurd (hlt.trans_le (tsum_apply_le_one q)) (by simp [hps])

/-- `SPMF.bind` respects equality on the support. -/
protected lemma bind_congr {p : SPMF α} {f g : α → SPMF β}
    (h : ∀ x, p x ≠ 0 → f x = g x) : p >>= f = p >>= g := by
  refine SPMF.ext fun y => ?_
  simp only [bind_apply_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : p x = 0
  · simp [hx]
  · rw [h x hx]

/-- The missing mass of a bind: mass already missing from `p`, plus mass lost by the
continuation on each output. -/
lemma gap_bind (p : SPMF α) (f : α → SPMF β) :
    (p >>= f).gap = p.gap + ∑' x, p x * (f x).gap := by
  show (p >>= f).toPMF none = _
  rw [toPMF_bind]
  show (p.toPMF.bind fun o => o.elim (PMF.pure none) (fun x => (f x).toPMF)) none = _
  rw [PMF.bind_apply, tsum_option _ ENNReal.summable]
  simp only [Option.elim]
  simp [SPMF.gap, SPMF.apply_eq_toPMF_some]

/-! ## The ω-complete partial order -/

/-- The least upper bound of a chain of subdistributions: pointwise suprema of output
masses, with the residual mass (`1` minus the total, which stays at most `1` by
monotone convergence) on the missing-mass fiber. -/
noncomputable def chainSup (c : Chain (SPMF α)) : SPMF α :=
  SPMF.mk ⟨fun o => o.elim (1 - ∑' x, ⨆ k, c k x) (fun x => ⨆ k, c k x), by
    have hmono : Monotone fun k => ((c k : SPMF α) : α → ℝ≥0∞) :=
      fun i j h x => c.monotone h x
    have hS : (∑' x, ⨆ k, c k x) = ⨆ k, ∑' x, c k x :=
      ENNReal.tsum_iSup_of_monotone hmono
    have hle : (∑' x : α, ⨆ k, c k x) ≤ 1 := by
      rw [hS]
      exact iSup_le fun k => tsum_apply_le_one (c k)
    rw [Summable.hasSum_iff ENNReal.summable, tsum_option _ ENNReal.summable]
    simp only [Option.elim]
    exact tsub_add_cancel_of_le hle⟩

@[simp] lemma chainSup_apply (c : Chain (SPMF α)) (x : α) :
    chainSup c x = ⨆ k, c k x := rfl

noncomputable instance : OmegaCompletePartialOrder (SPMF α) where
  ωSup := chainSup
  le_ωSup c k := le_of_forall fun x => le_iSup (fun k => c k x) k
  ωSup_le _ _ h := le_of_forall fun x => iSup_le fun k => h k x

@[simp] lemma ωSup_apply (c : Chain (SPMF α)) (x : α) : ωSup c x = ⨆ k, c k x := rfl

/-- The missing mass of a chain's limit is the infimum of the missing masses. -/
lemma gap_ωSup (c : Chain (SPMF α)) : (ωSup c).gap = ⨅ k, (c k).gap := by
  have hmono : Monotone fun k => ((c k : SPMF α) : α → ℝ≥0∞) :=
    fun i j h x => c.monotone h x
  show (ωSup c).gap = _
  rw [gap_eq_one_sub_tsum]
  show (1 - ∑' x, ⨆ k, c k x) = _
  rw [ENNReal.tsum_iSup_of_monotone hmono, ENNReal.sub_iSup one_ne_top]
  exact iInf_congr fun k => (gap_eq_one_sub_tsum (c k)).symm

/-- A chain that is constant from `k` on has limit `c k`. -/
lemma ωSup_eq_of_eventually_const {c : Chain (SPMF α)} {k : ℕ}
    (h : ∀ m, k ≤ m → c m = c k) : ωSup c = c k := by
  refine le_antisymm (ωSup_le c _ fun m => ?_) (le_ωSup c k)
  rcases Nat.lt_or_ge m k with hm | hm
  · exact c.monotone hm.le
  · exact (h m hm).le

/-- The successor-shifted chain. -/
def _root_.OmegaCompletePartialOrder.Chain.shift {γ : Type*} [Preorder γ]
    (c : Chain γ) : Chain γ :=
  ⟨fun k => c (k + 1), fun _ _ h => c.monotone (Nat.succ_le_succ h)⟩

@[simp] lemma _root_.OmegaCompletePartialOrder.Chain.shift_apply {γ : Type*} [Preorder γ]
    (c : Chain γ) (k : ℕ) : c.shift k = c (k + 1) := rfl

/-- Shifting a chain does not change its limit. -/
lemma ωSup_shift (c : Chain (SPMF α)) : ωSup c.shift = ωSup c := by
  refine SPMF.ext fun x => ?_
  simp only [ωSup_apply, Chain.shift_apply]
  exact le_antisymm (iSup_le fun k => le_iSup (fun k => c k x) (k + 1))
    (iSup_le fun k => (c.monotone (Nat.le_succ k) x).trans
      (le_iSup (fun k => c (k + 1) x) k))

/-! ## Monotonicity and ω-continuity of `bind` -/

/-- `bind` is monotone in both arguments. -/
lemma bind_le_bind {p p' : SPMF α} {f f' : α → SPMF β}
    (hp : p ≤ p') (hf : ∀ x, f x ≤ f' x) : p >>= f ≤ p' >>= f' :=
  le_of_forall fun y => by
    simp only [bind_apply_eq_tsum]
    exact ENNReal.tsum_le_tsum fun x => mul_le_mul' (hp x) (hf x y)

/-- Left ω-continuity of `bind`. -/
lemma ωSup_bind (c : Chain (SPMF α)) (f : α → SPMF β) :
    ωSup c >>= f = ωSup (c.map ⟨(· >>= f), fun _ _ h => bind_le_bind h fun _ => le_rfl⟩) := by
  refine SPMF.ext fun y => ?_
  have hR : ωSup (c.map ⟨(· >>= f), fun _ _ h => bind_le_bind h fun _ => le_rfl⟩) y
      = ⨆ k, ∑' x, c k x * f x y := by
    rw [ωSup_apply]
    exact iSup_congr fun k => by
      show (c k >>= f) y = _
      rw [bind_apply_eq_tsum]
  rw [hR, bind_apply_eq_tsum]
  calc ∑' x, (ωSup c) x * f x y
      = ∑' x, ⨆ k, c k x * f x y := by
        refine tsum_congr fun x => ?_
        rw [ωSup_apply, ENNReal.iSup_mul]
    _ = ⨆ k, ∑' x, c k x * f x y :=
        ENNReal.tsum_iSup_of_monotone fun i j h x =>
          mul_le_mul' (c.monotone h x) le_rfl

/-- Right ω-continuity of `bind`: the direction fixpoint unfoldings use. -/
lemma bind_ωSup (p : SPMF α) (c : α → Chain (SPMF β)) :
    (p >>= fun x => ωSup (c x)) =
      ωSup ⟨fun k => p >>= fun x => c x k,
        fun _ _ h => bind_le_bind le_rfl fun x => (c x).monotone h⟩ := by
  refine SPMF.ext fun y => ?_
  have hR : ωSup (⟨fun k => p >>= fun x => c x k,
        fun _ _ h => bind_le_bind le_rfl fun x => (c x).monotone h⟩ : Chain (SPMF β)) y
      = ⨆ k, ∑' x, p x * c x k y := by
    rw [ωSup_apply]
    exact iSup_congr fun k => by
      show (p >>= fun x => c x k) y = _
      rw [bind_apply_eq_tsum]
  rw [hR, bind_apply_eq_tsum]
  calc ∑' x, p x * (ωSup (c x)) y
      = ∑' x, ⨆ k, p x * c x k y := by
        refine tsum_congr fun x => ?_
        rw [ωSup_apply, ENNReal.mul_iSup]
    _ = ⨆ k, ∑' x, p x * c x k y :=
        ENNReal.tsum_iSup_of_monotone fun i j h x =>
          mul_le_mul' le_rfl ((c x).monotone h y)

/-- ω-continuity of `map`. -/
lemma map_ωSup (f : α → β) (c : Chain (SPMF α)) :
    f <$> ωSup c = ωSup (c.map ⟨(f <$> ·), fun _ _ h =>
      by simpa only [map_eq_bind_pure_comp] using bind_le_bind h fun _ => le_rfl⟩) := by
  simp only [map_eq_bind_pure_comp]
  exact ωSup_bind c (pure ∘ f)

/-! ## Merging optional outcomes into the failure mass -/

/-- Merge an `Option` layer of *outcomes* into the failure mass: a `none` result
becomes missing mass. This is the quotient identifying fuel-exhaustion of a truncated
run with failure — the presentation under which fuelled runs are monotone in fuel. -/
noncomputable def joinOption (p : SPMF (Option α)) : SPMF α :=
  p >>= fun o => o.elim failure pure

@[simp] lemma joinOption_pure (o : Option α) :
    joinOption (pure o : SPMF (Option α)) = o.elim failure pure :=
  pure_bind o _

@[simp] lemma joinOption_apply (p : SPMF (Option α)) (x : α) :
    joinOption p x = p (some x) := by
  simp only [joinOption, bind_apply_eq_tsum]
  refine (tsum_eq_single (some x) fun o ho => ?_).trans (by simp)
  match o with
  | none => simp
  | some y =>
    rw [show (some y).elim failure pure = (pure y : SPMF α) from rfl,
      (pure_apply_eq_zero_iff y x).mpr fun hxy => ho (by rw [hxy]), mul_zero]

/-- The missing mass after the merge: mass already missing, plus mass on the `none`
outcome. -/
@[simp] lemma gap_joinOption (p : SPMF (Option α)) :
    (joinOption p).gap = p.gap + p none := by
  rw [joinOption, gap_bind]
  congr 1
  refine (tsum_eq_single none fun o ho => ?_).trans (by simp [SPMF.gap])
  match o with
  | none => exact absurd rfl ho
  | some y => simp [show (some y).elim failure pure = (pure y : SPMF α) from rfl, SPMF.gap]

@[simp] lemma joinOption_map_some (p : SPMF α) : joinOption (some <$> p) = p := by
  simp only [joinOption, map_eq_bind_pure_comp, bind_assoc, Function.comp]
  simp only [pure_bind]
  exact bind_pure p

lemma joinOption_bind (p : SPMF α) (f : α → SPMF (Option β)) :
    joinOption (p >>= f) = p >>= fun x => joinOption (f x) :=
  bind_assoc p f _

/-- A subdistribution with no mass on the `none` outcome is the `some`-image of its
merge. -/
lemma eq_map_some_of_apply_none_eq_zero {p : SPMF (Option α)} (h : p none = 0) :
    p = some <$> joinOption p := by
  refine SPMF.ext fun o => ?_
  have hmap : ∀ o' : Option α, (some <$> joinOption p) o' =
      ∑' y, joinOption p y * (pure (some y) : SPMF (Option α)) o' := fun o' => by
    simp only [map_eq_bind_pure_comp, bind_apply_eq_tsum, Function.comp]
  match o with
  | none =>
    rw [h, hmap]
    refine (ENNReal.tsum_eq_zero.mpr fun y => ?_).symm
    rw [(pure_apply_eq_zero_iff _ _).mpr (by simp), mul_zero]
  | some x =>
    rw [hmap]
    refine ((tsum_eq_single x fun y hy => ?_).trans (by simp)).symm
    rw [(pure_apply_eq_zero_iff _ _).mpr (by simpa using fun hxy => hy hxy.symm), mul_zero]

end SPMF
