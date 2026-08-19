/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork
public import VCVio.EvalDist.IndepProduct
public import VCVio.OracleComp.Constructions.WithoutReplacement

/-!
# The coordinate-wise rewinding extractor as a resampling loop

`coordForkOp` is Figure 11 of Fenzi–Moghaddas–Nguyen against a fixed acceptance table: sample a
challenge `c₀`, abort if it is rejected, and otherwise resample each coordinate *without
replacement* until `k - 1` further accepting values have been found there, or that coordinate is
exhausted. It reports how many table entries it looked at, so the query count is part of its
output rather than an external accounting.

`VCVio/CryptoFoundations/CoordinateFork.lean` has the same success condition as a total lookup:
`coordForkCore` reads the whole column and keeps the first `k - 1` accepting values in enumeration
order. The two agree on what matters. `probEvent_isSome_coordForkOp` shows the loop succeeds with
exactly the core's probability — the sampled column order is irrelevant, because the loop stops
only on success or exhaustion — and `coordForkOp_success` shows a successful run returns a
coordinate-wise `k`-special sound set of accepting challenges, via the shared
`coordFamily_success`.

So the success and output clauses of Lemma 7.1 hold for the paper's actual algorithm and not only
for the table model. This is against a *fixed* acceptance table, which is the setting §7.1 needs:
its own analysis treats the adversary as a function of the challenge. See
`CoordinateFork/Realizability.lean` for where such a table comes from.

The expected-query clause is still open. The count is returned (`coordForkOp` pairs its result with
the number of lookups) and `ProbComp.expectedLength_drawUntil` computes each coordinate's
contribution, but nothing here assembles those into the paper's `1 + ℓ(k - 1)` bound.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist ProbComp

open scoped ENNReal

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable {k : ℕ} {ρ : (ι → S) → Bool} {c₀ : ι → S} {d : ι → List S}

/-! ## The pool of alternatives -/

/-- The values a coordinate can be resampled to: everything except the one already in use. -/
noncomputable def altPool (c₀ : ι → S) (j : ι) : List S := (Finset.univ.erase (c₀ j)).toList

omit [DecidableEq ι] [Fintype ι] in
theorem nodup_altPool (c₀ : ι → S) (j : ι) : (altPool c₀ j).Nodup := Finset.nodup_toList _

omit [DecidableEq ι] [Fintype ι] in
theorem mem_altPool {x : S} {j : ι} : x ∈ altPool c₀ j ↔ x ≠ c₀ j := by
  simp [altPool]

omit [DecidableEq ι] [Fintype ι] in
theorem length_altPool (c₀ : ι → S) (j : ι) : (altPool c₀ j).length = Fintype.card S - 1 := by
  rw [altPool, Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

omit [Fintype ι] in
/-- The pool's accepting values are exactly the replacements the deterministic core sees. -/
theorem countP_altPool (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) :
    (altPool c₀ j).countP (fun x => ρ (Function.update c₀ j x)) = (hitSet ρ c₀ j).card := by
  rw [altPool, Finset.countP_toList, hitSet]

/-! ## The loop -/

/-- The resampling loop at one coordinate. -/
noncomputable def coordDraws (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) :
    ProbComp (List S) :=
  drawUntil (fun x => ρ (Function.update c₀ j x)) (k - 1) (altPool c₀ j)

/-- The accepting values a run collected at coordinate `j`. -/
noncomputable def collected (ρ : (ι → S) → Bool) (c₀ : ι → S) (d : ι → List S) (j : ι) :
    Finset S :=
  ((d j).filter fun x => ρ (Function.update c₀ j x)).toFinset

/-- The loop once the challenge has been drawn: abort on a rejecting challenge, and otherwise
resample every coordinate and report what was collected together with the number of table entries
examined. -/
noncomputable def coordForkOpAt (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    ProbComp (Option (Finset (ι → S)) × ℕ) :=
  if ρ c₀ then do
    let d ← Fintype.mPi (coordDraws k ρ c₀)
    let cost : ℕ := 1 + ∑ j, (d j).length
    if ∀ j, (collected ρ c₀ d j).card = k - 1 then
      return (some (coordFamily c₀ (collected ρ c₀ d)), cost)
    else return (none, cost)
  else return (none, 1)

/-- **Figure 11 of Fenzi–Moghaddas–Nguyen**, against a fixed acceptance table. -/
noncomputable def coordForkOp [SampleableType (ι → S)] (k : ℕ) (ρ : (ι → S) → Bool) :
    ProbComp (Option (Finset (ι → S)) × ℕ) :=
  ($ᵗ (ι → S)) >>= coordForkOpAt k ρ

/-! ## What a run collects -/

theorem mem_support_coordDraws (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) (j : ι) :
    d j ∈ support (coordDraws k ρ c₀ j) :=
  mem_support_mPi _ d hd j

/-- The loop collects as many accepting values as it was asked for, or as many as the coordinate
had. This is the only fact about the loop the success analysis uses. -/
theorem card_collected (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) (j : ι) :
    (collected ρ c₀ d j).card = min (k - 1) ((hitSet ρ c₀ j).card) := by
  classical
  have hj := mem_support_coordDraws hd j
  have hnodup : (d j).Nodup :=
    nodup_of_mem_support_drawUntil _ _ _ _ rfl (nodup_altPool c₀ j) _ hj
  have hcount := countP_of_mem_support_drawUntil
    (fun x => ρ (Function.update c₀ j x)) (altPool c₀ j).length (k - 1) _ rfl _ hj
  rw [collected, List.toFinset_card_of_nodup (hnodup.filter _), ← List.countP_eq_length_filter,
    hcount, countP_altPool]

theorem mem_altPool_of_mem_collected (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀)))
    {j : ι} {x : S} (hx : x ∈ collected ρ c₀ d j) : x ∈ altPool c₀ j := by
  classical
  rw [collected, List.mem_toFinset, List.mem_filter] at hx
  exact mem_of_mem_support_drawUntil _ (altPool c₀ j).length (k - 1) _ rfl _
    (mem_support_coordDraws hd j) x hx.1

theorem notMem_collected (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) (j : ι) :
    c₀ j ∉ collected ρ c₀ d j := fun hx =>
  (mem_altPool.mp (mem_altPool_of_mem_collected hd hx)) rfl

omit [Fintype ι] [Fintype S] in
theorem accept_of_mem_collected {j : ι} {x : S} (hx : x ∈ collected ρ c₀ d j) :
    ρ (Function.update c₀ j x) := by
  classical
  rw [collected, List.mem_toFinset, List.mem_filter] at hx
  exact hx.2

/-! ## Success and output -/

section Op

variable [SampleableType (ι → S)]

omit [SampleableType (ι → S)] in
/-- On an accepting centre the loop succeeds exactly when the centre is good — that is, exactly
when the deterministic core succeeds. The order the coordinate was resampled in cannot matter,
because the loop stops only on success or on exhaustion. -/
theorem forall_card_collected_iff (hacc : ρ c₀)
    (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) :
    (∀ j, (collected ρ c₀ d j).card = k - 1) ↔ c₀ ∈ goodSet k ρ := by
  rw [mem_goodSet_iff_of_accept hacc]
  refine forall_congr' fun j => ?_
  rw [card_collected hd j]
  omega

omit [SampleableType (ι → S)] in
/-- **The output guarantee.** A successful run returns a coordinate-wise `k`-special sound set of
challenges the table accepts. -/
theorem coordForkOpAt_success {X : Finset (ι → S)} {cost : ℕ}
    (h : (some X, cost) ∈ support (coordForkOpAt k ρ c₀)) :
    IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c := by
  classical
  rw [coordForkOpAt] at h
  by_cases hacc : ρ c₀
  · rw [if_pos hacc, mem_support_bind_iff] at h
    obtain ⟨d, hd, h⟩ := h
    by_cases hcond : ∀ j, (collected ρ c₀ d j).card = k - 1
    · rw [if_pos hcond] at h
      obtain rfl : X = coordFamily c₀ (collected ρ c₀ d) := by
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at h
        exact h.1
      exact coordFamily_success hacc (notMem_collected hd) hcond
        fun _ _ hx => accept_of_mem_collected hx
    · rw [if_neg hcond] at h
      simp at h
  · rw [if_neg hacc] at h
    simp at h

theorem coordForkOp_success {X : Finset (ι → S)} {cost : ℕ}
    (h : (some X, cost) ∈ support (coordForkOp k ρ)) :
    IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c := by
  rw [coordForkOp, mem_support_bind_iff] at h
  obtain ⟨c₀, hc₀, hAt⟩ := h
  exact coordForkOpAt_success hAt

/-! ## The success probability -/

omit [SampleableType (ι → S)] in
/-- On a fixed challenge the loop succeeds with certainty or not at all, according to whether that
challenge is good. Which values the coordinate resampling happened to draw does not matter. -/
theorem probEvent_isSome_coordForkOpAt (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    Pr[fun r => r.1.isSome | coordForkOpAt k ρ c₀] = if c₀ ∈ goodSet k ρ then 1 else 0 := by
  classical
  by_cases hacc : ρ c₀
  · rw [coordForkOpAt, if_pos hacc]
    by_cases hgood : c₀ ∈ goodSet k ρ
    · refine (probEvent_eq_one ⟨probFailure_of_liftM_PMF _, fun r hr => ?_⟩).trans
        (if_pos hgood).symm
      rw [mem_support_bind_iff] at hr
      obtain ⟨d, hd, hr⟩ := hr
      rw [if_pos ((forall_card_collected_iff hacc hd).mpr hgood)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
    · refine (probEvent_eq_zero fun r hr => ?_).trans (if_neg hgood).symm
      rw [mem_support_bind_iff] at hr
      obtain ⟨d, hd, hr⟩ := hr
      rw [if_neg fun hc => hgood ((forall_card_collected_iff hacc hd).mp hc)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  · have hgood : c₀ ∉ goodSet k ρ := by simp [goodSet, hacc]
    rw [coordForkOpAt, if_neg hacc, if_neg hgood]
    simp

/-- **The success probability of Figure 11.** The loop succeeds exactly as often as the
deterministic table core: on `goodSet k ρ`, the challenges whose every column holds at least `k`
accepting values. -/
theorem probEvent_isSome_coordForkOp (k : ℕ) (ρ : (ι → S) → Bool) :
    Pr[fun r => r.1.isSome | coordForkOp k ρ]
      = ((goodSet k ρ).card : ℝ≥0∞) / Fintype.card (ι → S) := by
  classical
  rw [coordForkOp, probEvent_bind_eq_tsum]
  simp only [probEvent_isSome_coordForkOpAt, probOutput_uniformSample]
  rw [ENNReal.tsum_mul_left, tsum_fintype (L := .unconditional _), Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one, div_eq_mul_inv, mul_comm]

/-- **Lemma 7.1 for the paper's algorithm**, at a fixed acceptance table: the resampling loop
returns a coordinate-wise `k`-special sound set of accepting challenges with probability at least
`ε - ℓ(k-1)/N`, where `ε` is the table's accepting ratio.

The output is guaranteed by `coordForkOp_success`; what is still missing is the expected number of
table lookups, which the returned count makes available but no theorem here bounds. -/
theorem sub_div_le_probEvent_isSome_coordForkOp [Nonempty S] (k : ℕ) (ρ : (ι → S) → Bool) :
    ((Finset.univ.filter fun c : ι → S => ρ c).card : ℝ≥0∞) / Fintype.card (ι → S)
        - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr[fun r => r.1.isSome | coordForkOp k ρ] := by
  rw [probEvent_isSome_coordForkOp]
  exact CoordinateWise.sub_div_le_div_card_filter (accept := fun c => ρ c = true) k

end Op

end OracleComp
