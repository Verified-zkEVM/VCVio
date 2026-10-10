/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.DiscreteInstances
public import VCVio.EvalDist.Lossless
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.Constructions.WithoutReplacement.Basic

/-!
# The draw loop is exchangeable, and the per-element draw probabilities that follow

`VCVio.OracleComp.Constructions.WithoutReplacement.Basic` gives the loop and its expected number of
draws. This module resolves that total into the individual values: how often the loop draws any one
element of the pool, and what those probabilities sum to across a family of pools.

The argument runs in three steps. Every draw is uniform over what is left, so an outcome's weight
depends only on how many draws it took (`evalDist_drawUntil_apply`); therefore the loop's law is a
function of the pool's *set* of values, not of the list presenting them
(`evalDist_drawUntil_congr`), and is invariant under relabelling by an acceptance-preserving
permutation (`evalDist_drawUntil_map_perm`). Swapping two values the acceptance test cannot tell
apart gives **exchangeability** (`evalDist_mem_drawUntil_congr`): they are equally likely to be
drawn. Two aggregate totals then pin the individual probabilities down completely, since the
accepting values share `min r (pool's supply)` draws between them
(`evalDist_mem_drawUntil_mul_countP`) and the rejecting values share what is left
(`evalDist_mem_drawUntil_mul_countP_not`).

`sum_evalDist_mem_erase_le` is what a cost bound consumes. Summed over every accepting centre `v`,
with the loop run on the pool `univ.erase v`, no single value is drawn more than `r` times in
expectation. `sum_lintegral_sum_map_erase_le` is its weighted form, and is the shape the
coordinate-wise fork's expected-lookup bound is assembled from.

Observing the drawn list itself, rather than a numeric summary of it, needs a σ-algebra on
`List S`; `ToMathlib.MeasureTheory.DiscreteInstances` supplies the discrete one for a countable
alphabet, which is why `[Countable S]` appears throughout.
-/

public section

open scoped ENNReal
open MeasureTheory

namespace Finset

/-- Counting a `Finset`'s elements through its list is filtering it. -/
theorem countP_toList {α : Type*} (s : Finset α) (p : α → Bool) :
    s.toList.countP p = (s.filter fun x => p x).card := by
  classical
  rw [List.countP_eq_sum_map, Finset.sum_map_toList, Finset.card_filter]

end Finset

namespace ProbComp

-- Every statement below observes the drawn list itself, so the pool's alphabet carries the
-- discrete measurable structure of `ToMathlib.MeasureTheory.DiscreteInstances`.
variable {S : Type} [Countable S]

/-- **The loop is lossless.** It only ever samples an index of a nonempty pool, so its
successful-output measure is a probability measure. -/
theorem isProbabilityMeasure_evalDist_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → IsProbabilityMeasure 𝒟[drawUntil accept r l] := by
  induction n with
  | zero =>
      intro r l hl
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      rw [drawUntil_nil]
      infer_instance
  | succ n ih =>
      intro r l hl
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
        cases l with
        | nil => simp at hl
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hxs : xs.length = n := by simpa using hl
      cases r with
      | zero => rw [drawUntil_zero]; infer_instance
      | succ r =>
          rw [drawUntil_cons]
          refine evalDist.isProbabilityMeasure_bind _ _ fun i => ?_
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          have := ih (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
            ((x :: xs).eraseIdx i) (by rw [List.length_eraseIdx_of_lt hi]; simpa using hxs)
          exact evalDist.isProbabilityMeasure_map _ Measurable.of_discrete

/-! ## The loop is uniform over its outcomes

Each draw is uniform over what is left, so any two runs that made the same number of draws are
equally likely — whatever they drew, and whatever the pool's order was. `evalDist_drawUntil_apply`
records that: the weight of an outcome depends only on its length.

This is what makes the loop's law a function of the pool's *set* of values rather than of the list
presenting it, which the recursion on `List` otherwise hides. -/

private theorem evalDist_cons_map_self (y : S) (mx : ProbComp (List S)) (d : List S) :
    𝒟[(y :: ·) <$> mx] {y :: d} = 𝒟[mx] {d} := by
  rw [evalDist_map_apply_of_discrete mx _ MeasurableSet.of_discrete,
    show (fun l : List S => y :: l) ⁻¹' {y :: d} = {d} from
      Set.ext fun l => by simp]

private theorem evalDist_cons_map_of_ne {y z : S} (hyz : y ≠ z) (mx : ProbComp (List S))
    (d : List S) : 𝒟[(y :: ·) <$> mx] {z :: d} = 0 := by
  refine evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete fun l hl hmem => ?_
  rw [support_map] at hl
  obtain ⟨d', -, rfl⟩ := hl
  exact hyz (List.cons_eq_cons.mp hmem).1

private theorem evalDist_cons_map_nil (y : S) (mx : ProbComp (List S)) :
    𝒟[(y :: ·) <$> mx] {([] : List S)} = 0 := by
  refine evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete fun l hl hmem => ?_
  rw [support_map] at hl
  obtain ⟨d, -, rfl⟩ := hl
  simp at hmem

omit [Countable S] in
/-- A run against a nonempty pool draws at some index, and what follows is a run against the pool
with that index removed. -/
theorem mem_support_drawUntil_cons_iff (accept : S → Bool) (r : ℕ) (x : S) (xs : List S)
    {d : List S} :
    d ∈ support (drawUntil accept (r + 1) (x :: xs)) ↔
      ∃ i : Fin (xs.length + 1),
        d = ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) :: d.tail ∧
          d.tail ∈ support (drawUntil accept
            (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
            ((x :: xs).eraseIdx i)) := by
  rw [drawUntil_cons, mem_support_bind_iff]
  constructor
  · rintro ⟨i, -, hd⟩
    rw [support_map] at hd
    obtain ⟨rest, hrest, rfl⟩ := hd
    exact ⟨i, rfl, hrest⟩
  · rintro ⟨i, hd, hrest⟩
    refine ⟨i, by simp, ?_⟩
    rw [support_map]
    exact ⟨d.tail, hrest, hd.symm⟩

omit [Countable S] in
theorem ne_nil_of_mem_support_drawUntil_cons (accept : S → Bool) (r : ℕ) (x : S) (xs : List S)
    {d : List S} (hd : d ∈ support (drawUntil accept (r + 1) (x :: xs))) : d ≠ [] := by
  obtain ⟨i, hi, -⟩ := (mem_support_drawUntil_cons_iff accept r x xs).mp hd
  rw [hi]
  exact List.cons_ne_nil _ _

omit [Countable S] in
/-- An unreachable outcome has zero mass. -/
private theorem evalDist_singleton_eq_zero {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] {mx : ProbComp α} {d : α} (hd : d ∉ support mx) :
    𝒟[mx] {d} = 0 :=
  evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete
    fun _ hx hmem => hd (hmem ▸ hx)

omit [Countable S] in
/-- A uniform index draw averages its continuation's mass over the index. -/
private theorem evalDist_uniformFin_bind_apply {α : Type} [MeasurableSpace α]
    (n : ℕ) (f : Fin (n + 1) → ProbComp α) {s : Set α} (hs : MeasurableSet s) :
    𝒟[uniformFin n >>= f] s = (∑ i, 𝒟[f i] s) / (n + 1) := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply hs (Measurable.of_discrete (f := fun i => 𝒟[f i])).aemeasurable,
    lintegral_evalDist_uniformFin]

/-- **Every outcome of a given length is equally likely.** Against a pool of `n` distinct values, a
run that made `d.length` draws has weight the reciprocal of `n` falling `d.length` — the number of
ordered choices those draws had. The weight does not depend on *what* was drawn, nor on the order
the pool was presented in. -/
theorem evalDist_drawUntil_apply (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → l.Nodup →
      ∀ d ∈ support (drawUntil accept r l),
        𝒟[drawUntil accept r l] {d} = ((n.descFactorial d.length : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  induction n with
  | zero =>
      intro r l hl _ d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      rw [drawUntil_nil] at hd ⊢
      obtain rfl : d = [] := by simpa using hd
      simp
  | succ n ih =>
      intro r l hl hnd d hd
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
        cases l with
        | nil => simp at hl
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hxs : xs.length = n := by simpa using hl
      subst hxs
      cases r with
      | zero =>
          rw [drawUntil_zero] at hd ⊢
          obtain rfl : d = [] := by simpa using hd
          simp
      | succ r =>
          obtain ⟨i₀, hi₀, hrest⟩ := (mem_support_drawUntil_cons_iff accept r x xs).mp hd
          obtain ⟨z, d', rfl⟩ : ∃ z d', d = z :: d' := by
            cases d with
            | nil => exact absurd rfl (ne_nil_of_mem_support_drawUntil_cons accept r x xs hd)
            | cons z d' => exact ⟨z, d', rfl⟩
          have hz : ((x :: xs)[(i₀ : ℕ)]'(by simpa using i₀.isLt)) = z :=
            ((List.cons_eq_cons.mp hi₀).1).symm
          simp only [List.tail_cons] at hrest
          have hlenEr : ((x :: xs).eraseIdx i₀).length = xs.length := by
            have hi : (i₀ : ℕ) < (x :: xs).length := by simpa using i₀.isLt
            rw [List.length_eraseIdx_of_lt hi]; simp
          rw [hz] at hrest
          rw [drawUntil_cons, evalDist_uniformFin_bind_apply _ _ MeasurableSet.of_discrete]
          have hvanish : ∀ i ∈ (Finset.univ : Finset (Fin (xs.length + 1))), i ≠ i₀ →
              𝒟[(((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) :: ·) <$>
                  drawUntil accept
                    (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
                    ((x :: xs).eraseIdx i)] {z :: d'} = 0 := by
            intro i _ hne
            refine evalDist_cons_map_of_ne (fun heq => ?_) _ _
            exact hne (Fin.ext (hnd.getElem_inj_iff.mp (heq.trans hz.symm)))
          rw [Finset.sum_eq_single i₀ hvanish (fun h => absurd (Finset.mem_univ _) h), hz,
            evalDist_cons_map_self,
            ih _ ((x :: xs).eraseIdx i₀) hlenEr (hnd.eraseIdx _) d' hrest,
            List.length_cons, Nat.succ_descFactorial_succ]
          push_cast
          rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)),
            ENNReal.div_eq_inv_mul, mul_comm]

/-! ## The law depends only on the pool's values

Every draw is uniform over what is left, so the order the pool was presented in is invisible.
`support_drawUntil_congr` says the reachable outcomes are the same for two nodup pools with the
same values, and with `evalDist_drawUntil_apply` that upgrades to `evalDist_drawUntil_congr`: the
whole law is a function of the pool's set of values. -/

omit [Countable S] in
private theorem mem_eraseIdx_iff_of_nodup {l : List S} (hnd : l.Nodup) {i : ℕ}
    (hi : i < l.length) {y : S} : y ∈ l.eraseIdx i ↔ y ∈ l ∧ y ≠ l[i] := by
  rw [List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨j, hj, hne, rfl⟩
    exact ⟨List.getElem_mem hj, fun h => hne (hnd.getElem_inj_iff.mp h)⟩
  · rintro ⟨hy, hne⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    exact ⟨j, hj, fun h => hne (by subst h; rfl), rfl⟩

omit [Countable S] in
private theorem support_drawUntil_subset (accept : S → Bool) (n : ℕ)
    (ih : ∀ (r : ℕ) (l l' : List S), l.length = n → l'.length = n → l.Nodup → l'.Nodup →
      (∀ y, y ∈ l ↔ y ∈ l') → support (drawUntil accept r l) = support (drawUntil accept r l'))
    (r : ℕ) : ∀ (u v : List S), u.length = n + 1 → v.length = n + 1 → u.Nodup → v.Nodup →
      (∀ y, y ∈ u ↔ y ∈ v) →
        support (drawUntil accept (r + 1) u) ⊆ support (drawUntil accept (r + 1) v) := by
  intro u v hu hv hndu hndv huv
  obtain ⟨p, ps, rfl⟩ : ∃ p ps, u = p :: ps := by
    cases u with
    | nil => simp at hu
    | cons p ps => exact ⟨p, ps, rfl⟩
  obtain ⟨q, qs, rfl⟩ : ∃ q qs, v = q :: qs := by
    cases v with
    | nil => simp at hv
    | cons q qs => exact ⟨q, qs, rfl⟩
  intro d hd
  obtain ⟨i, hdeq, hrest⟩ := (mem_support_drawUntil_cons_iff accept r p ps).mp hd
  have hi : (i : ℕ) < (p :: ps).length := by simpa using i.isLt
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem ((huv _).mp (List.getElem_mem hi))
  have hjlt : j < qs.length + 1 := by simpa using hj
  refine (mem_support_drawUntil_cons_iff accept r q qs).mpr ⟨⟨j, hjlt⟩, ?_, ?_⟩
  · rw [hdeq]; congr 1; exact hjeq.symm
  · rw [show (q :: qs)[((⟨j, hjlt⟩ : Fin (qs.length + 1)) : ℕ)] = (p :: ps)[(i : ℕ)] from hjeq]
    have hsub : support (drawUntil accept
          (if accept ((p :: ps)[(i : ℕ)]) then r else r + 1) ((p :: ps).eraseIdx i))
        = support (drawUntil accept
          (if accept ((p :: ps)[(i : ℕ)]) then r else r + 1) ((q :: qs).eraseIdx j)) := by
      refine ih _ _ _ ?_ ?_ (hndu.eraseIdx _) (hndv.eraseIdx _) fun y => ?_
      · rw [List.length_eraseIdx_of_lt hi]; simpa using hu
      · rw [List.length_eraseIdx_of_lt hj]; simpa using hv
      · rw [mem_eraseIdx_iff_of_nodup hndu hi, mem_eraseIdx_iff_of_nodup hndv hj, hjeq, huv y]
    rwa [← hsub]

omit [Countable S] in
/-- Two nodup pools holding the same values admit the same runs. -/
theorem support_drawUntil_congr (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l l' : List S), l.length = n → l'.length = n → l.Nodup → l'.Nodup →
      (∀ y, y ∈ l ↔ y ∈ l') →
        support (drawUntil accept r l) = support (drawUntil accept r l') := by
  induction n with
  | zero =>
      intro r l l' hl hl' _ _ _
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      obtain rfl : l' = [] := List.length_eq_zero_iff.mp hl'
      rfl
  | succ n ih =>
      intro r l l' hl hl' hnd hnd' hmem
      cases r with
      | zero => rw [drawUntil_zero, drawUntil_zero]
      | succ r =>
          exact Set.Subset.antisymm
            (support_drawUntil_subset accept n ih r l l' hl hl' hnd hnd' hmem)
            (support_drawUntil_subset accept n ih r l' l hl' hl hnd' hnd
              fun y => (hmem y).symm)

/-- **The loop's law depends only on the pool's values.** -/
theorem evalDist_drawUntil_congr (accept : S → Bool) (n : ℕ) (r : ℕ) (l l' : List S)
    (hl : l.length = n) (hl' : l'.length = n) (hnd : l.Nodup) (hnd' : l'.Nodup)
    (hmem : ∀ y, y ∈ l ↔ y ∈ l') :
    𝒟[drawUntil accept r l] = 𝒟[drawUntil accept r l'] := by
  classical
  have hsupp := support_drawUntil_congr accept n r l l' hl hl' hnd hnd' hmem
  refine Measure.ext_of_singleton fun d => ?_
  by_cases hd : d ∈ support (drawUntil accept r l)
  · rw [evalDist_drawUntil_apply accept n r l hl hnd d hd,
      evalDist_drawUntil_apply accept n r l' hl' hnd' d (hsupp ▸ hd)]
  · rw [evalDist_singleton_eq_zero hd,
      evalDist_singleton_eq_zero (hsupp ▸ hd)]

/-! ## Relabelling, and exchangeability within accept classes

Relabelling the pool relabels the run: `drawUntil_map` is a program identity, since the index the
loop samples does not depend on what the values are. Composed with `evalDist_drawUntil_congr` it
gives `evalDist_mem_drawUntil_congr`, the fact the weighted analyses need — two values the pool
treats alike are equally likely to be drawn. -/

omit [Countable S] in
/-- Relabelling the pool relabels its runs. Stated between two pools because the sub-pool a run
descends into is not itself closed under the relabelling — only the correspondence is. -/
theorem map_mem_support_drawUntil (accept : S → Bool) (σ : Equiv.Perm S) (n : ℕ) :
    ∀ (r : ℕ) (l l' : List S), l.length = n → l'.length = n → l.Nodup → l'.Nodup →
      (∀ y, y ∈ l ↔ σ y ∈ l') →
        ∀ d ∈ support (drawUntil (fun y => accept (σ y)) r l),
          d.map σ ∈ support (drawUntil accept r l') := by
  induction n with
  | zero =>
      intro r l l' hl hl' _ _ _ d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      obtain rfl : l' = [] := List.length_eq_zero_iff.mp hl'
      rw [drawUntil_nil] at hd ⊢
      obtain rfl : d = [] := by simpa using hd
      simp
  | succ n ih =>
      intro r l l' hl hl' hnd hnd' hcorr d hd
      cases r with
      | zero =>
          rw [drawUntil_zero] at hd ⊢
          obtain rfl : d = [] := by simpa using hd
          simp
      | succ r =>
          obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
            cases l with
            | nil => simp at hl
            | cons x xs => exact ⟨x, xs, rfl⟩
          obtain ⟨x', xs', rfl⟩ : ∃ x' xs', l' = x' :: xs' := by
            cases l' with
            | nil => simp at hl'
            | cons x' xs' => exact ⟨x', xs', rfl⟩
          obtain ⟨i, hdeq, hrest⟩ :=
            (mem_support_drawUntil_cons_iff (fun y => accept (σ y)) r x xs).mp hd
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          obtain ⟨j, hj, hjeq⟩ :=
            List.getElem_of_mem ((hcorr _).mp (List.getElem_mem hi))
          have hjlt : j < xs'.length + 1 := by simpa using hj
          refine (mem_support_drawUntil_cons_iff accept r x' xs').mpr ⟨⟨j, hjlt⟩, ?_, ?_⟩
          · rw [hdeq, List.map_cons, List.tail_cons]
            congr 1
            exact hjeq.symm
          · rw [hdeq, List.map_cons, List.tail_cons,
              show (x' :: xs')[((⟨j, hjlt⟩ : Fin (xs'.length + 1)) : ℕ)]
                = σ ((x :: xs)[(i : ℕ)]) from hjeq]
            refine ih _ ((x :: xs).eraseIdx i) ((x' :: xs').eraseIdx j) ?_ ?_
              (hnd.eraseIdx _) (hnd'.eraseIdx _) (fun y => ?_) _ hrest
            · rw [List.length_eraseIdx_of_lt hi]; simpa using hl
            · rw [List.length_eraseIdx_of_lt hj]; simpa using hl'
            · rw [mem_eraseIdx_iff_of_nodup hnd hi, mem_eraseIdx_iff_of_nodup hnd' hj, hjeq,
                hcorr y]
              exact and_congr_right fun _ => not_congr σ.injective.eq_iff.symm

omit [Countable S] in
/-- A permutation preserving acceptance and the pool's values maps runs to runs, bijectively. -/
theorem map_mem_support_drawUntil_iff (accept : S → Bool) (σ : Equiv.Perm S)
    (hacc : ∀ y, accept (σ y) = accept y) (r : ℕ) (l : List S) (hnd : l.Nodup)
    (hmem : ∀ y, σ y ∈ l ↔ y ∈ l) {d : List S} :
    d.map σ ∈ support (drawUntil accept r l) ↔ d ∈ support (drawUntil accept r l) := by
  have hfun : (fun y => accept (σ y)) = accept := funext hacc
  have hfun' : (fun y => accept (σ.symm y)) = accept := by
    funext y; rw [← hacc (σ.symm y), Equiv.apply_symm_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := map_mem_support_drawUntil accept σ.symm l.length r l l rfl rfl hnd hnd
      (fun y => by rw [← hmem (σ.symm y), Equiv.apply_symm_apply]) _ (by rwa [hfun'])
    simpa [List.map_map, Function.comp_def] using this
  · exact map_mem_support_drawUntil accept σ l.length r l l rfl rfl hnd hnd
      (fun y => (hmem y).symm) d (by rwa [hfun])

/-- Relabelling by a permutation that preserves acceptance and the pool's values leaves the law
alone. -/
theorem evalDist_drawUntil_map_perm (accept : S → Bool) (σ : Equiv.Perm S)
    (hacc : ∀ y, accept (σ y) = accept y) (r : ℕ) (l : List S) (hnd : l.Nodup)
    (hmem : ∀ y, σ y ∈ l ↔ y ∈ l) :
    𝒟[(·.map σ) <$> drawUntil accept r l] = 𝒟[drawUntil accept r l] := by
  classical
  have hinj : Function.Injective (fun d : List S => d.map σ) :=
    fun d₁ d₂ h => by simpa [List.map_map, Function.comp_def] using congrArg (·.map σ.symm) h
  refine Measure.ext_of_singleton fun d => ?_
  rw [evalDist_map_apply_of_discrete _ _ MeasurableSet.of_discrete,
    show (fun d : List S => d.map σ) ⁻¹' {d} = {d.map σ.symm} from
      Set.ext fun e => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => by rw [← h]; simp [List.map_map, Function.comp_def],
          fun h => by rw [h]; simp [List.map_map, Function.comp_def]⟩]
  by_cases hd : d ∈ support (drawUntil accept r l)
  · have hpre : (d.map σ.symm).map σ = d := by simp [List.map_map, Function.comp_def]
    have hmem' : (d.map σ.symm) ∈ support (drawUntil accept r l) := by
      refine (map_mem_support_drawUntil_iff accept σ hacc r l hnd hmem).mp ?_
      rw [hpre]; exact hd
    rw [evalDist_drawUntil_apply accept l.length r l rfl hnd _ hmem',
      evalDist_drawUntil_apply accept l.length r l rfl hnd d hd, List.length_map]
  · refine (evalDist_singleton_eq_zero fun hmem' => hd ?_).trans
      (evalDist_singleton_eq_zero hd).symm
    have := (map_mem_support_drawUntil_iff accept σ hacc r l hnd hmem).mpr hmem'
    simpa [List.map_map, Function.comp_def] using this

/-! ## Expected number of draws -/

/-- **Exchangeability.** Two values of the pool that the acceptance test cannot tell apart are
equally likely to be drawn. -/
theorem evalDist_mem_drawUntil_congr (accept : S → Bool) (r : ℕ) (l : List S) (hnd : l.Nodup)
    {a b : S} (ha : a ∈ l) (hb : b ∈ l) (hab : accept a = accept b) :
    𝒟[drawUntil accept r l] {d | a ∈ d} = 𝒟[drawUntil accept r l] {d | b ∈ d} := by
  let _ : DecidableEq S := Classical.decEq S
  set σ : Equiv.Perm S := Equiv.swap a b with hσ
  have hacc : ∀ y, accept (σ y) = accept y := by
    intro y
    rcases eq_or_ne y a with rfl | hya
    · rw [hσ, Equiv.swap_apply_left, hab]
    rcases eq_or_ne y b with rfl | hyb
    · rw [hσ, Equiv.swap_apply_right, hab]
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hmem : ∀ y, σ y ∈ l ↔ y ∈ l := by
    intro y
    rcases eq_or_ne y a with rfl | hya
    · rw [hσ, Equiv.swap_apply_left]; exact ⟨fun _ => ha, fun _ => hb⟩
    rcases eq_or_ne y b with rfl | hyb
    · rw [hσ, Equiv.swap_apply_right]; exact ⟨fun _ => hb, fun _ => ha⟩
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hpred : (fun d : List S => b ∈ d) ∘ (·.map σ) = fun d : List S => a ∈ d := by
    funext d
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨z, hz, hzb⟩ := List.mem_map.mp h
      have hza : z = a := by
        have hzz := congrArg σ hzb
        rwa [hσ, Equiv.swap_apply_self, Equiv.swap_apply_right] at hzz
      exact hza ▸ hz
    · exact List.mem_map.mpr ⟨a, h, by rw [hσ, Equiv.swap_apply_left]⟩
  have hlaw := evalDist_drawUntil_map_perm accept σ hacc r l hnd hmem
  conv_rhs => rw [← hlaw]
  rw [evalDist_map_apply_of_discrete _ _ MeasurableSet.of_discrete,
    show (fun d : List S => d.map σ) ⁻¹' {d | b ∈ d} = {d | a ∈ d} from
      Set.ext fun d => Iff.of_eq (congrFun hpred d)]

/-! ## Per-element draw probabilities

Exchangeability pins the individual draw probabilities down completely, once the two aggregate
totals are known: over the whole pool they sum to the expected number of draws, and over the
pool's accepting values they sum to the number of accepting draws the loop makes — which is its
budget or the pool's supply, whichever is smaller. -/

/-- A functional that agrees with another on every reachable output integrates the same. -/
private theorem lintegral_evalDist_congr_of_support {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] {f g : α → ℝ≥0∞} (mx : ProbComp α)
    (h : ∀ x ∈ support mx, f x = g x) : ∫⁻ x, f x ∂𝒟[mx] = ∫⁻ x, g x ∂𝒟[mx] :=
  lintegral_congr_ae (evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete h)

/-- The weighted total of what a run drew, resolved into per-value draw probabilities. -/
theorem lintegral_sum_map_drawUntil [DecidableEq S] (accept : S → Bool) (r : ℕ) (l : List S)
    (hnd : l.Nodup) (g : S → ℝ≥0∞) :
    ∫⁻ d, (d.map g).sum ∂𝒟[drawUntil accept r l]
      = ∑ x ∈ l.toFinset, g x * 𝒟[drawUntil accept r l] {d | x ∈ d} := by
  classical
  have hpt : ∀ d ∈ support (drawUntil accept r l),
      (d.map g).sum = ∑ x ∈ l.toFinset, (if x ∈ d then g x else 0) := by
    intro d hd
    have hsub : ∀ y ∈ d, y ∈ l := mem_of_mem_support_drawUntil accept l.length r l rfl d hd
    have hdn : d.Nodup := nodup_of_mem_support_drawUntil accept l.length r l rfl hnd d hd
    rw [← Finset.sum_filter, show l.toFinset.filter (fun x => x ∈ d) = d.toFinset from
      Finset.ext fun x => by
        simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩]
    exact (List.sum_toFinset g hdn).symm
  rw [lintegral_evalDist_congr_of_support _ hpt,
    lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show (fun d : List S => if x ∈ d then g x else 0)
      = Set.indicator {d : List S | x ∈ d} (fun _ => g x) from funext fun d => by
        by_cases hx : x ∈ d <;> simp [Set.indicator, hx],
    lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]

/-- Summed over the pool, the draw probabilities are the expected number of draws. -/
theorem sum_evalDist_mem_drawUntil [DecidableEq S] (accept : S → Bool) (r : ℕ) (l : List S)
    (hnd : l.Nodup) :
    ∑ x ∈ l.toFinset, 𝒟[drawUntil accept r l] {d | x ∈ d}
      = NegHypergeom.expectedDraws l.length (l.countP accept) r := by
  classical
  have h := lintegral_sum_map_drawUntil accept r l hnd (fun _ => (1 : ℝ≥0∞))
  simp only [one_mul] at h
  rw [← h, lintegral_evalDist_congr_of_support (f := fun d : List S =>
      (d.map (fun _ => (1 : ℝ≥0∞))).sum) (g := fun d => (d.length : ℝ≥0∞)) _ fun d _ => by simp,
    ← lintegral_evalDist_map_of_discrete (drawUntil accept r l) (f := List.length)
      (g := fun n : ℕ => (n : ℝ≥0∞)),
    lintegral_evalDist_length_drawUntil accept l.length r l rfl]

/-- Summed over the pool's accepting values, they are the number of accepting values the loop
collects: its budget, or the pool's supply. -/
theorem sum_evalDist_mem_drawUntil_accept [DecidableEq S] (accept : S → Bool) (r : ℕ)
    (l : List S) (hnd : l.Nodup) :
    ∑ x ∈ l.toFinset.filter (fun x => accept x), 𝒟[drawUntil accept r l] {d | x ∈ d}
      = ((min r (l.countP accept) : ℕ) : ℝ≥0∞) := by
  classical
  have hg := lintegral_sum_map_drawUntil accept r l hnd (fun x => if accept x then 1 else 0)
  rw [Finset.sum_filter]
  simp only [ite_mul, one_mul, zero_mul] at hg
  rw [← hg, lintegral_evalDist_congr_of_support _ (fun d hd => ?_), lintegral_const,
    (isProbabilityMeasure_evalDist_drawUntil accept l.length r l rfl).measure_univ, mul_one]
  rw [show ((d.map fun x => if accept x then (1 : ℝ≥0∞) else 0).sum)
      = ((d.countP accept : ℕ) : ℝ≥0∞) from ?_,
    countP_of_mem_support_drawUntil accept l.length r l rfl d hd]
  clear hd
  induction d with
  | nil => simp
  | cons y ys ihd =>
      rw [List.map_cons, List.sum_cons, ihd, List.countP_cons]
      cases accept y
      · simp
      · simp; ring

omit [Countable S] in
private theorem card_filter_toFinset [DecidableEq S] (l : List S) (hnd : l.Nodup) (p : S → Bool) :
    (l.toFinset.filter (fun x => p x)).card = l.countP p := by
  classical
  rw [← List.toFinset_filter, List.toFinset_card_of_nodup (hnd.filter _),
    List.countP_eq_length_filter]

/-- **The accepting values are drawn with equal probability**, so each is drawn as often as the
loop's accepting draws allow, divided by the pool's supply of them. -/
theorem evalDist_mem_drawUntil_mul_countP (accept : S → Bool) (r : ℕ)
    (l : List S) (hnd : l.Nodup) {x : S} (hx : x ∈ l) (hacc : accept x) :
    𝒟[drawUntil accept r l] {d | x ∈ d} * (l.countP accept : ℝ≥0∞)
      = ((min r (l.countP accept) : ℕ) : ℝ≥0∞) := by
  let _ : DecidableEq S := Classical.decEq S
  have hconst : ∀ y ∈ l.toFinset.filter (fun y => accept y),
      𝒟[drawUntil accept r l] {d | y ∈ d} = 𝒟[drawUntil accept r l] {d | x ∈ d} := by
    intro y hy
    rw [Finset.mem_filter, List.mem_toFinset] at hy
    exact evalDist_mem_drawUntil_congr accept r l hnd hy.1 hx (by rw [hy.2, hacc])
  rw [← sum_evalDist_mem_drawUntil_accept accept r l hnd, Finset.sum_congr rfl hconst,
    Finset.sum_const, card_filter_toFinset l hnd accept, nsmul_eq_mul, mul_comm]

/-- The rejecting values likewise, with the loop's remaining draws to share out. -/
theorem evalDist_mem_drawUntil_mul_countP_not (accept : S → Bool) (r : ℕ)
    (l : List S) (hnd : l.Nodup) {x : S} (hx : x ∈ l) (hrej : accept x = false) :
    𝒟[drawUntil accept r l] {d | x ∈ d} * (l.countP (fun y => !accept y) : ℝ≥0∞)
        + ((min r (l.countP accept) : ℕ) : ℝ≥0∞)
      = NegHypergeom.expectedDraws l.length (l.countP accept) r := by
  let _ : DecidableEq S := Classical.decEq S
  have hconst : ∀ y ∈ l.toFinset.filter (fun y => ¬ (accept y = true)),
      𝒟[drawUntil accept r l] {d | y ∈ d} = 𝒟[drawUntil accept r l] {d | x ∈ d} := by
    intro y hy
    rw [Finset.mem_filter, List.mem_toFinset] at hy
    exact evalDist_mem_drawUntil_congr accept r l hnd hy.1 hx
      (by rw [hrej, Bool.eq_false_iff]; exact fun h => hy.2 h)
  have hcard : (l.toFinset.filter (fun y => ¬ (accept y = true))).card
      = l.countP (fun y => !accept y) := by
    rw [← card_filter_toFinset l hnd (fun y => !accept y)]
    exact congrArg Finset.card (Finset.filter_congr fun y _ => by simp)
  rw [← sum_evalDist_mem_drawUntil accept r l hnd,
    ← Finset.sum_filter_add_sum_filter_not l.toFinset (fun y => accept y),
    sum_evalDist_mem_drawUntil_accept accept r l hnd, Finset.sum_congr rfl hconst,
    Finset.sum_const, nsmul_eq_mul, hcard]
  ring

/-! ## The column bound

A *column* is a coordinate's worth of values: `Fintype.card S` of them, of which `countP` accept.
A resampling loop centred on an accepting value `v` draws from the rest of the column, so across
all the accepting centres a fixed value `x` can be drawn many times over.
`sum_evalDist_mem_erase_le` says it is drawn at most `r` times in total — the same budget one loop
has.

That is the counting step of a *weighted* cost bound: charge each drawn value a weight, and the
column's total charge is at most `r` times the column's total weight, whatever the weights are. -/

section Column

variable [DecidableEq S] [Fintype S]

omit [DecidableEq S] [Fintype S] in
theorem evalDist_mem_drawUntil_eq_zero (a : S → Bool) (r : ℕ) (l : List S) {x : S}
    (hx : x ∉ l) : 𝒟[drawUntil a r l] {d | x ∈ d} = 0 :=
  evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete fun d hd hxd =>
    hx (mem_of_mem_support_drawUntil a l.length r l rfl d hd x hxd)

omit [Countable S] in
theorem countP_toList_erase (a : S → Bool) {v : S} (hv : a v) :
    ((Finset.univ.erase v).toList).countP a = (Finset.univ.filter fun y => a y).card - 1 := by
  classical
  have hmem : v ∈ Finset.univ.filter (fun y => a y) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  rw [Finset.countP_toList,
    show (Finset.univ.erase v).filter (fun y => a y)
      = (Finset.univ.filter fun y => a y).erase v from by
        refine Finset.ext fun y => ?_
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        tauto,
    Finset.card_erase_of_mem hmem]

omit [Countable S] in
theorem length_toList_erase (v : S) :
    ((Finset.univ.erase v).toList).length = Fintype.card S - 1 := by
  rw [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

omit [Countable S] in
theorem countP_not_toList_erase (a : S → Bool) {v : S} (hv : a v) :
    ((Finset.univ.erase v).toList).countP (fun y => !a y)
      = Fintype.card S - (Finset.univ.filter fun y => a y).card := by
  have hlen : ((Finset.univ.erase v).toList).length
      = ((Finset.univ.erase v).toList).countP a
        + ((Finset.univ.erase v).toList).countP (fun y => !a y) := by
    simpa using List.length_eq_countP_add_countP a (l := (Finset.univ.erase v).toList)
  rw [length_toList_erase, countP_toList_erase a hv] at hlen
  have hHpos : 0 < (Finset.univ.filter fun y => a y).card :=
    Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  have hHle : (Finset.univ.filter fun y => a y).card ≤ Fintype.card S := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.filter_subset _ _)
  have hNpos : 0 < Fintype.card S := lt_of_lt_of_le hHpos hHle
  omega

open OracleComp.EvalDist in
/-- **The column bound.** Summed over the accepting centres of a column, the chance that a
resampling loop starting there draws a fixed value `x` is at most the loop's own budget. -/
theorem sum_evalDist_mem_erase_le (a : S → Bool) (r : ℕ) (x : S) :
    ∑ v ∈ Finset.univ.filter (fun v => a v),
        𝒟[drawUntil a r ((Finset.univ.erase v).toList)] {d | x ∈ d}
      ≤ (r : ℝ≥0∞) := by
  classical
  set A : Finset S := Finset.univ.filter (fun v => a v) with hA
  set H : ℕ := A.card with hH
  set N : ℕ := Fintype.card S with hN
  have hHle : H ≤ N := by
    have hc : A.card ≤ (Finset.univ : Finset S).card :=
      Finset.card_le_card (by rw [hA]; exact Finset.filter_subset _ _)
    simpa [hH, hN] using hc
  set P : ℝ≥0∞ :=
    ∑ v ∈ A, 𝒟[drawUntil a r ((Finset.univ.erase v).toList)] {d | x ∈ d} with hP
  by_cases hax : a x
  · -- `x` accepts: only the other `H - 1` accepting centres can draw it, and they share out the
    -- loop's accepting draws.
    have hxA : x ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax⟩
    rcases Nat.lt_or_ge H 2 with hH1 | hH2
    · have hAx : A = {x} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hxA, fun y hy => Finset.card_le_one.mp (by omega) y hy x hxA⟩
      rw [hP, hAx, Finset.sum_singleton, evalDist_mem_drawUntil_eq_zero a r _ (by simp)]
      exact zero_le
    · have hterm : ∀ v ∈ A,
          𝒟[drawUntil a r ((Finset.univ.erase v).toList)] {d | x ∈ d}
              * ((H - 1 : ℕ) : ℝ≥0∞)
            = if v = x then 0 else ((min r (H - 1) : ℕ) : ℝ≥0∞) := by
        intro v hv
        have hav : a v := (Finset.mem_filter.mp hv).2
        by_cases hvx : v = x
        · rw [ite_eq_left hvx, hvx, evalDist_mem_drawUntil_eq_zero a r _ (by simp), zero_mul]
        · rw [ite_eq_right hvx, ← countP_toList_erase a hav]
          exact evalDist_mem_drawUntil_mul_countP a r _ (Finset.nodup_toList _)
            (by simp [Ne.symm hvx]) hax
      have hsum : P * ((H - 1 : ℕ) : ℝ≥0∞)
          = ((H - 1 : ℕ) : ℝ≥0∞) * ((min r (H - 1) : ℕ) : ℝ≥0∞) := by
        rw [hP, Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.sum_erase_add A _ hxA,
          ite_eq_left rfl, add_zero,
          Finset.sum_congr rfl (fun v hv => ite_eq_right (Finset.ne_of_mem_erase hv)),
          Finset.sum_const, Finset.card_erase_of_mem hxA, nsmul_eq_mul]
      refine (ENNReal.mul_le_mul_iff_left
        (show ((H - 1 : ℕ) : ℝ≥0∞) ≠ 0 by exact_mod_cast (by omega : (H - 1 : ℕ) ≠ 0))
        (by finiteness)).mp ?_
      rw [hsum, mul_comm]
      exact mul_le_mul' (by exact_mod_cast Nat.min_le_left r (H - 1)) le_rfl
  · -- `x` rejects: every accepting centre can draw it.
    have hxA : x ∉ A := fun h => hax (Finset.mem_filter.mp h).2
    have hHlt : H < N := by
      refine lt_of_le_of_ne hHle fun h => hxA ?_
      have hAu : A = Finset.univ := Finset.eq_univ_of_card A (by rw [← hH, h, hN])
      rw [hAu]
      exact Finset.mem_univ _
    rcases Nat.lt_or_ge r H with hrH | hHr
    · have hterm : ∀ v ∈ A,
          𝒟[drawUntil a r ((Finset.univ.erase v).toList)] {d | x ∈ d}
              * ((N - H : ℕ) : ℝ≥0∞) + (r : ℝ≥0∞)
            = NegHypergeom.expectedDraws (N - 1) (H - 1) r := by
        intro v hv
        have hav : a v := (Finset.mem_filter.mp hv).2
        have h := evalDist_mem_drawUntil_mul_countP_not a r ((Finset.univ.erase v).toList)
          (Finset.nodup_toList _) (x := x)
          (by
            have hne : x ≠ v := fun h => hax (by rw [h]; exact hav)
            simp [hne])
          (by simpa using hax)
        rwa [countP_not_toList_erase a hav, countP_toList_erase a hav, length_toList_erase,
          show min r (H - 1) = r from Nat.min_eq_left (by omega)] at h
      have hED : (H : ℝ≥0∞) * NegHypergeom.expectedDraws (N - 1) (H - 1) r
          = (r : ℝ≥0∞) * N := by
        have h := NegHypergeom.mul_expectedDraws (N - 1) (H - 1) r (by omega) (by omega)
        have hc1 : ((H - 1 : ℕ) : ℝ≥0∞) + 1 = (H : ℝ≥0∞) := by
          have hh : (H - 1 : ℕ) + 1 = H := by omega
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh
        have hc2 : ((N - 1 : ℕ) : ℝ≥0∞) + 1 = (N : ℝ≥0∞) := by
          have hh : (N - 1 : ℕ) + 1 = N := by omega
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh
        rwa [hc1, hc2] at h
      have hstep : P * ((N - H : ℕ) : ℝ≥0∞) + (H : ℝ≥0∞) * (r : ℝ≥0∞) = (r : ℝ≥0∞) * N := by
        have h1 := Finset.sum_congr rfl hterm
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul, ← hP, ← hH, hED] at h1
        exact h1
      have hrN : (r : ℝ≥0∞) * N
          = (r : ℝ≥0∞) * ((N - H : ℕ) : ℝ≥0∞) + (H : ℝ≥0∞) * (r : ℝ≥0∞) := by
        have hc : (N : ℝ≥0∞) = ((N - H : ℕ) : ℝ≥0∞) + (H : ℝ≥0∞) := by
          have hh : N = (N - H : ℕ) + H := by omega
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh
        rw [hc, mul_add, mul_comm (r : ℝ≥0∞) (H : ℝ≥0∞)]
      rw [hrN] at hstep
      have hP' : P * ((N - H : ℕ) : ℝ≥0∞) = (r : ℝ≥0∞) * ((N - H : ℕ) : ℝ≥0∞) :=
        (ENNReal.add_left_inj (by finiteness)).mp hstep
      refine (ENNReal.mul_le_mul_iff_left
        (show ((N - H : ℕ) : ℝ≥0∞) ≠ 0 by exact_mod_cast (by omega : (N - H : ℕ) ≠ 0))
        (by finiteness)).mp (le_of_eq hP')
    · calc P ≤ ∑ _v ∈ A, (1 : ℝ≥0∞) := Finset.sum_le_sum fun v _ => evalDist_apply_le_one _ _
        _ = (H : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hH]
        _ ≤ (r : ℝ≥0∞) := by exact_mod_cast hHr

open OracleComp.EvalDist in
/-- **The weighted column bound.** Charge every drawn value a weight; summed over the accepting
centres, a column's expected charge is at most `r` times the column's total weight, whatever the
weights are.

This is the form a weighted cost bound consumes: `sum_evalDist_mem_erase_le` says no value is
drawn more than `r` times across the centres, and weights are then just linear. -/
theorem sum_lintegral_sum_map_erase_le (a : S → Bool) (r : ℕ) (g : S → ℝ≥0∞) :
    ∑ v ∈ Finset.univ.filter (fun v => a v),
        ∫⁻ d, (d.map g).sum ∂𝒟[drawUntil a r ((Finset.univ.erase v).toList)]
      ≤ (r : ℝ≥0∞) * ∑ x : S, g x := by
  classical
  have hterm : ∀ v : S,
      ∫⁻ d, (d.map g).sum ∂𝒟[drawUntil a r ((Finset.univ.erase v).toList)]
        = ∑ x : S, g x * 𝒟[drawUntil a r ((Finset.univ.erase v).toList)] {d | x ∈ d} := by
    intro v
    rw [lintegral_sum_map_drawUntil a r _ (Finset.nodup_toList _) g,
      Finset.toList_toFinset]
    refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
    have hxv : x = v := by
      by_contra hne
      exact hx (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    rw [hxv, evalDist_mem_drawUntil_eq_zero a r _ (by simp), mul_zero]
  calc ∑ v ∈ Finset.univ.filter (fun v => a v),
        ∫⁻ d, (d.map g).sum ∂𝒟[drawUntil a r ((Finset.univ.erase v).toList)]
      = ∑ v ∈ Finset.univ.filter (fun v => a v), ∑ x : S,
          g x * 𝒟[drawUntil a r ((Finset.univ.erase v).toList)] {d | x ∈ d} :=
        Finset.sum_congr rfl fun v _ => hterm v
    _ = ∑ x : S, g x * ∑ v ∈ Finset.univ.filter (fun v => a v),
          𝒟[drawUntil a r ((Finset.univ.erase v).toList)] {d | x ∈ d} := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum ..).symm
    _ ≤ ∑ x : S, g x * (r : ℝ≥0∞) :=
        Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (sum_evalDist_mem_erase_le a r x)
    _ = (r : ℝ≥0∞) * ∑ x : S, g x := by rw [← Finset.sum_mul, mul_comm]

end Column

end ProbComp
