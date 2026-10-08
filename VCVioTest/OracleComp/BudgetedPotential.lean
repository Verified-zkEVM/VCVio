/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The budgeted expected-potential bound on small instances

* **A lottery.**  Each query to a coin oracle draws a uniform `Bool` and sets a sticky flag when
  the coin is `true`.  The potential `if flag then 1 else n / 2` is spent at one budget level per
  query, so a computation making at most `n` queries ends with the flag set with probability at
  most `n / 2`, whatever the computation does with the answers.
* **The additive resource bound.**  A resource on the state that grows by at most one on a
  charged step and not at all on an uncharged one has expected final value at most its initial
  value plus the query budget.  It is derived once from
  `OracleComp.lintegral_run_le_of_isQueryBoundP` with the potential `resource s + n`, and once
  from the two expected-count lemmas.
* **The hit potential.**  An adversary consumes `u` designated slots one at a time, choosing a
  value for each (uncharged); a fresh uniform draw from `Y` (charged) hits every consumed value
  equal to it, and a cached derivation (charged) draws nothing.  The potential
  `(n / |Y|) ^ (pending + unhit)`, which drops to `0` once two consumed values coincide, gives
  probability at most `(n / |Y|) ^ u` that every slot is consumed and hit after at most `n`
  charged queries.  Its step inequality is Mathlib's `pow_add_mul_le_add_pow`, also checked at
  `ℕ` and at `ℝ≥0∞` below.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace BudgetedPotentialTest

/-! ## A lottery -/

/-- A coin oracle: each query draws a uniform `Bool`, returns it, and sets the flag if it is
`true`. -/
def coinImpl : QueryImpl (Unit →ₒ Bool) (StateT Bool ProbComp) := fun _ =>
  StateT.mk fun s => (fun b => (b, s || b)) <$> ($ᵗ Bool)

/-- The lottery potential at remaining budget `n`: `1` once the flag is set, `n / 2` before. -/
noncomputable def coinPotential (n : ℕ) (s : Bool) : ℝ≥0∞ :=
  if s then 1 else n * 2⁻¹

theorem coinPotential_step (t : Unit) (s : Bool) (n : ℕ) :
    ∫⁻ r, r ∂𝒟[(fun z => coinPotential n z.2) <$> (coinImpl t).run s] ≤
      coinPotential (n + if (fun _ : Unit => True) t then 1 else 0) s := by
  simp only [↓reduceIte]
  let _ : MeasurableSpace (Bool × Bool) := ⊤
  let _ : MeasurableSpace Bool := ⊤
  cases s with
  | true =>
    rw [show (coinImpl t).run true = (fun b => (b, true || b)) <$> ($ᵗ Bool) from rfl,
      Functor.map_map]
    exact lintegral_id_evalDist_map_le_of_le _ fun b => by simp [coinPotential]
  | false =>
    rw [show (coinImpl t).run false = (fun b => (b, b)) <$> ($ᵗ Bool) from rfl,
      Functor.map_map, lintegral_id_evalDist_map, lintegral_fintype]
    simp only [Fintype.univ_bool, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
      SampleableType.evalDist_uniformSample_singleton, Fintype.card_bool, coinPotential,
      ↓reduceIte, Bool.false_eq_true, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_mul]
    rw [add_mul, one_mul, add_comm]
    gcongr
    exact mul_le_of_le_one_right' (ENNReal.inv_le_one.mpr one_le_two)

/-- A computation making at most `n` coin queries sets the flag with probability at most
`n / 2`. -/
theorem prEvent_coin_le {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) (n : ℕ)
    (hq : oa.IsQueryBoundP (fun _ => True) n) :
    Pr{let z ← (simulateQ coinImpl oa).run false}[z.2 = true] ≤ n * 2⁻¹ := by
  simpa [coinPotential] using prEvent_run_le_of_isQueryBoundP coinImpl (fun _ => True) coinPotential
    (fun s a b hab => by
      cases s
      · simpa [coinPotential] using mul_le_mul_left (Nat.cast_le.mpr hab) _
      · simp [coinPotential])
    coinPotential_step (fun z => z.2 = true) (fun z hz => by simp [coinPotential, hz]) oa n hq
    false

/-! ## The additive resource bound -/

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- The additive resource bound, from the budgeted potential `resource s + n`. -/
theorem lintegral_resource_le_add_of_budget (so : QueryImpl spec (StateT σ ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (resource : σ → ℝ≥0∞)
    (hstep : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s),
      resource z.2 ≤ resource s + if charged t then 1 else 0)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP charged n) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (simulateQ so oa).run s] ≤ resource s + n := by
  have key := lintegral_run_le_of_isQueryBoundP so charged (fun n s => resource s + n)
    (fun s a b hab => by dsimp only; gcongr)
    (fun t s n => by
      rw [lintegral_id_evalDist_map_add]
      calc (∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (so t).run s]) +
            ∫⁻ r, r ∂𝒟[(fun _ => (n : ℝ≥0∞)) <$> (so t).run s]
          ≤ (resource s + if charged t then 1 else 0) + n :=
            add_le_add (lintegral_id_evalDist_map_le_of_le_of_mem_support _ (hstep t s))
              (lintegral_id_evalDist_map_le_of_le _ fun _ => le_rfl)
        _ = resource s + ((n + if charged t then 1 else 0 : ℕ) : ℝ≥0∞) := by
          split_ifs <;> push_cast <;> ring)
    oa n hq s
  simpa using key

/-- The same bound from the landed expected-count lemmas. -/
theorem lintegral_resource_le_add_of_expectedCount (so : QueryImpl spec (StateT σ ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (resource : σ → ℝ≥0∞)
    (hstep : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s),
      resource z.2 ≤ resource s + if charged t then 1 else 0)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP charged n) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (simulateQ so oa).run s] ≤ resource s + n :=
  (lintegral_resource_le_add_expectedSimulatedQueryCount so charged resource hstep oa s).trans
    (add_le_add le_rfl (expectedSimulatedQueryCount_le_of_isQueryBoundP so charged oa s n hq))

/-! ## The hit potential -/

section Hit

variable {Y : Type} [Fintype Y] [DecidableEq Y] [SampleableType Y] [Inhabited Y]

/-- The hit state: `none` once two consumed values coincide, otherwise `some (k, P)` with `k`
designated slots not yet consumed and `P` the consumed values not yet hit. -/
abbrev HitState (Y : Type) := Option (ℕ × Finset Y)

/-- Consumption of the next designated slot with the value `y`. -/
def consume (y : Y) : HitState Y → HitState Y
  | none => none
  | some (k, P) => if k = 0 then some (k, P) else if y ∈ P then none else some (k - 1, insert y P)

/-- The hit oracle: `none` is a fresh draw, which hits the consumed value it equals; `some none`
is a cached derivation, which draws nothing; `some (some y)` consumes a slot with the value `y`.
-/
def hitImpl : QueryImpl (Option (Option Y) →ₒ Y) (StateT (HitState Y) ProbComp)
  | none => StateT.mk fun s => (fun y => (y, s.map fun p => (p.1, p.2.erase y))) <$> ($ᵗ Y)
  | some none => StateT.mk fun s => pure (default, s)
  | some (some y) => StateT.mk fun s => pure (y, consume y s)

/-- Fresh draws and cached derivations are charged; consumption is not. -/
def hitCharged : Option (Option Y) → Prop := fun t => t = none ∨ t = some none

instance : DecidablePred (hitCharged (Y := Y)) := fun t =>
  inferInstanceAs (Decidable (t = none ∨ t = some none))

/-- The hit potential at remaining budget `n`: `(n / |Y|) ^ (k + |P|)`, and `0` once two
consumed values coincide. -/
noncomputable def hitPot (n : ℕ) : HitState Y → ℝ≥0∞
  | none => 0
  | some (k, P) => ((n : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (k + P.card)

omit [DecidableEq Y] [SampleableType Y] [Inhabited Y] in
theorem hitPot_mono (s : HitState Y) : Monotone fun n => hitPot n s := by
  intro a b hab
  rcases s with _ | ⟨k, P⟩
  · simp [hitPot]
  · simp only [hitPot]
    gcongr

omit [SampleableType Y] [Inhabited Y] in
theorem hitPot_consume (n : ℕ) (y : Y) (s : HitState Y) :
    hitPot n (consume y s) ≤ hitPot n s := by
  rcases s with _ | ⟨k, P⟩
  · simp [consume, hitPot]
  · simp only [consume]
    split_ifs with hk hy
    · exact le_rfl
    · simp [hitPot]
    · simp only [hitPot]
      rw [Finset.card_insert_of_notMem hy]
      apply le_of_eq
      congr 1
      omega

theorem hitPot_step (t : Option (Option Y)) (s : HitState Y) (n : ℕ) :
    ∫⁻ r, r ∂𝒟[(fun z => hitPot n z.2) <$> (hitImpl t).run s] ≤
      hitPot (n + if hitCharged t then 1 else 0) s := by
  rcases t with _ | _ | y
  · simp only [hitCharged, true_or, ↓reduceIte]
    rw [show (hitImpl (none : Option (Option Y))).run s =
        (fun y => (y, s.map fun p => (p.1, p.2.erase y))) <$> ($ᵗ Y) from rfl, Functor.map_map]
    rcases s with _ | ⟨k, P⟩
    · exact lintegral_id_evalDist_map_le_of_le _ fun _ => by simp [hitPot]
    set c : ℝ≥0∞ := (Fintype.card Y : ℝ≥0∞)⁻¹
    set x : ℝ≥0∞ := (n : ℝ≥0∞) * c
    set u := k + P.card
    let _ : MeasurableSpace Y := ⊤
    rw [lintegral_id_evalDist_map]
    have hpt : ∀ y : Y, hitPot n (some (k, P.erase y)) ≤
        x ^ u + (P : Set Y).indicator (fun _ => x ^ (u - 1)) y := by
      intro y
      simp only [hitPot]
      by_cases hy : y ∈ P
      · rw [Finset.card_erase_of_mem hy, Set.indicator_of_mem (by simpa using hy)]
        have : k + (P.card - 1) = u - 1 := by
          have := Finset.card_pos.mpr ⟨y, hy⟩
          omega
        rw [this]
        exact le_add_self
      · rw [Finset.erase_eq_of_notMem hy]
        exact le_self_add
    calc ∫⁻ y, hitPot n (some (k, P.erase y)) ∂𝒟[($ᵗ Y : ProbComp Y)]
        ≤ ∫⁻ y, (x ^ u + (P : Set Y).indicator (fun _ => x ^ (u - 1)) y)
            ∂𝒟[($ᵗ Y : ProbComp Y)] := lintegral_mono hpt
      _ = x ^ u * 𝒟[($ᵗ Y : ProbComp Y)] Set.univ +
            x ^ (u - 1) * 𝒟[($ᵗ Y : ProbComp Y)] P := by
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_indicator_const MeasurableSet.of_discrete]
      _ ≤ x ^ u + x ^ (u - 1) * (P.card * c) := by
          gcongr
          · exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
          · rw [SampleableType.evalDist_uniformSample_eq_encard_div,
              Set.encard_coe_eq_coe_finsetCard, div_eq_mul_inv]
            simp [c]
      _ ≤ x ^ u + u * x ^ (u - 1) * c := by
          have hPu : (P.card : ℝ≥0∞) ≤ u := by exact_mod_cast Nat.le_add_left _ _
          calc x ^ u + x ^ (u - 1) * (P.card * c) ≤ x ^ u + x ^ (u - 1) * (u * c) := by gcongr
            _ = x ^ u + u * x ^ (u - 1) * c := by ring
      _ ≤ (x + c) ^ u := pow_add_mul_le_add_pow zero_le zero_le u
      _ = hitPot (n + 1) (some (k, P)) := by
          simp only [hitPot, x, u]
          push_cast
          ring
  · simp only [hitCharged, reduceCtorEq, or_true, ↓reduceIte]
    refine lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun z hz => ?_
    simp only [hitImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simpa using hitPot_mono s (Nat.le_succ n)
  · simp only [hitCharged, reduceCtorEq, Option.some.injEq, or_self, ↓reduceIte, add_zero]
    refine lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun z hz => ?_
    simp only [hitImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hitPot_consume n y s

/-- All `u` designated slots consumed and hit, after at most `n` charged queries, has
probability at most `(n / |Y|) ^ u`. -/
theorem prEvent_allHit_le {α : Type} (oa : OracleComp (Option (Option Y) →ₒ Y) α) (n u : ℕ)
    (hq : oa.IsQueryBoundP hitCharged n) :
    Pr{let z ← (simulateQ hitImpl oa).run (some (u, ∅))}[z.2 = some (0, ∅)] ≤
      ((n : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹) ^ u := by
  simpa [hitPot] using prEvent_run_le_of_isQueryBoundP hitImpl hitCharged hitPot hitPot_mono
    hitPot_step (fun z => z.2 = some (0, ∅)) (fun z hz => by simp [hz, hitPot]) oa n hq
    (some (u, ∅))

end Hit

/-! ## The step inequality of the hit potential -/

example (n u : ℕ) : n ^ (u + 1) + (u + 1) * n ^ u ≤ (n + 1) ^ (u + 1) := by
  simpa using pow_add_mul_le_add_pow (a := n) (b := 1) (Nat.zero_le _) (Nat.zero_le _) (u + 1)

example (x : ℝ≥0∞) (u : ℕ) : x ^ (u + 1) + (u + 1) * x ^ u ≤ (x + 1) ^ (u + 1) := by
  simpa using pow_add_mul_le_add_pow (a := x) (b := 1) zero_le zero_le (u + 1)

end BudgetedPotentialTest
