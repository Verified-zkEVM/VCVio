/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The joint potential on a one-node graph

A public random oracle on `R` has one derivation `()` and one node `()`, whose only child is the
derivation and whose point at children values `vs` is `vs.headD default`; every public point is
at the node's key. A forger makes one public query `g` first, and the honest code then touches
the derivation and the node's label, so both are drawn only in the end fill. The final state
fires a conflict exactly when the derivation is drawn at `g`, and a target collision exactly when
the label is drawn at the forger's answer.

* With `R = Bool` the run, with its single public entry at the node's key, fires either hazard
  with probability `3/4`, more than `1/|R| = 1/2`. This is also the probability of the event of
  `CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_and_le` with the coefficient `1` in place of
  `2`, no draw, no hazard and the budget `1/2`, so the coefficient `2` of `2 · #keyEntries / |R|`
  cannot be lowered to `1` (`JointPotentialToy.not_oneChargeBound`).
* With a secret drawn uniformly from `R` after the end fill and the seed hazard "the secret is a
  cached public point", the joint bound gives `3/|R|` for the three hazards together, which is
  `3/8 < 1` at `R = Fin 8`.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace JointPotentialToy

/-- One node, whose only child is the derivation and whose point at children values `vs` is
`vs.headD default`. -/
def G (R : Type) [Inhabited R] : CanonicalGraph (R →ₒ R) Unit Unit R where
  ch _ := [.inl ()]
  pt _ vs := vs.headD default
  range_eq _ _ := rfl
  pt_inj {_ _ vs vs'} h h' hpt := by
    match vs, vs', h, h' with
    | [v], [v'], _, _ => exact ⟨rfl, by simpa using hpt⟩

/-- Every public point is at the key of the one node. -/
def nk (R : Type) [Inhabited R] : (G R).NodeKeys where
  node _ := some ()
  node_pt _ := rfl
  range_eq _ := rfl

variable {R : Type}

/-- A public query at `g`, then a touch of the derivation and of the node's label. -/
def forgerFirst (g : R) : OracleComp ((R →ₒ R).withLabels Unit Unit R) Unit := do
  let _ ← ((R →ₒ R).withLabels Unit Unit R).query (.inl (.inl (.inr g)))
  let _ ← ((R →ₒ R).withLabels Unit Unit R).query (.inr (.inl (.inl ())))
  let _ ← ((R →ₒ R).withLabels Unit Unit R).query (.inr (.inl (.inr ())))
  pure ()

/-- In the deferred game the forger's query is cached as a public answer and both touches are
recorded. -/
theorem deferredImpl_run_forgerFirst [Inhabited R] [DecidableEq R] [SampleableType R] (g : R) :
    (simulateQ (G R).deferredImpl (forgerFirst g)).run ((∅, ∅), []) =
      (fun a ↦ ((), (((∅ : (R →ₒ R).QueryCache).cacheQuery g a, ∅),
        [Sum.inl (), Sum.inr ()]))) <$> ($ᵗ R) := by
  have h0 : ¬∃ k vs, (G R).childVals ((∅, ∅) : RelabelState (R →ₒ R) Unit Unit R) k =
      some vs ∧ (G R).pt k vs = g := by
    rintro ⟨k, vs, hk, -⟩
    obtain _ | ⟨hv, -⟩ := (G R).childVals_eq_some_iff.1 hk
    exact absurd hv (Option.some_ne_none _).symm
  simp only [forgerFirst, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, CanonicalGraph.deferredImpl_run_touch, pure_bind]
  rw [(G R).deferredImpl_run_inl, (G R).relabelImpl_run_pub_of_not_exists h0,
    randomOracle.run_eq]
  simp [map_eq_bind_pure_comp, QueryCache.empty_apply]

/-- The end fill of the two touched cells draws the derivation and then the label. -/
theorem endFill_forgerFirst [SampleableType R] (C : (R →ₒ R).QueryCache) :
    RelabelState.endFill ((C, ∅), [Sum.inl (), Sum.inr ()]) =
      ($ᵗ R) >>= fun v ↦ ($ᵗ R) >>= fun l ↦
        pure (C, ((∅ : ((Unit ⊕ Unit) →ₒ R).QueryCache).cacheQuery (Sum.inl ()) v).cacheQuery
          (Sum.inr ()) l) := by
  rw [RelabelState.endFill_eq]
  simp [map_eq_bind_pure_comp, QueryCache.empty_apply]

/-- In the final state the forger's single entry fires a conflict exactly when the derivation is
drawn at its input, and a target collision exactly when the label is drawn at its answer. -/
theorem conflict_or_tcHazard_iff [Inhabited R] [DecidableEq R] (g a v ℓ : R) :
    ((G R).Conflict ((∅ : (R →ₒ R).QueryCache).cacheQuery g a,
        ((∅ : ((Unit ⊕ Unit) →ₒ R).QueryCache).cacheQuery (.inl ()) v).cacheQuery (.inr ()) ℓ) ∨
      (nk R).TCHazard ((∅ : (R →ₒ R).QueryCache).cacheQuery g a,
        ((∅ : ((Unit ⊕ Unit) →ₒ R).QueryCache).cacheQuery (.inl ()) v).cacheQuery (.inr ()) ℓ)) ↔
      (v = g ∨ ℓ = a) := by
  set st : RelabelState (R →ₒ R) Unit Unit R :=
    ((∅ : (R →ₒ R).QueryCache).cacheQuery g a,
      ((∅ : ((Unit ⊕ Unit) →ₒ R).QueryCache).cacheQuery (.inl ()) v).cacheQuery (.inr ()) ℓ)
  have hD1 : st.2 (.inl ()) = some v := by simp [st]
  have hD2 : st.2 (.inr ()) = some ℓ := by simp [st]
  have hch : (G R).childVals st () = some [v] := (G R).childVals_eq_some_iff.2 (.cons hD1 .nil)
  have hC : ∀ t, st.1 t = if t = g then some a else none := by
    intro t
    by_cases h : t = g
    · subst h; simp [st]
    · simp [st, h]
  constructor
  · rintro (⟨k, vs, hk, hCk⟩ | ⟨t, k, ℓ', hk, hℓ', hCk⟩)
    · rw [hch] at hk
      cases hk
      left
      by_contra h
      simp [G, hC, h] at hCk
    · rw [hD2] at hℓ'
      cases hℓ'
      right
      rw [hC] at hCk
      split_ifs at hCk
      exact (Option.some_inj.1 hCk).symm
  · rintro (rfl | rfl)
    · exact Or.inl ⟨(), [v], hch, by simp [G, hC]⟩
    · exact Or.inr ⟨g, (), ℓ, rfl, hD2, by simp [hC]⟩

/-- A cache with one entry has at most one entry at a node key. -/
theorem encard_keyEntries_le [Inhabited R] [DecidableEq R] (g a : R) :
    ((nk R).keyEntries ((∅ : (R →ₒ R).QueryCache).cacheQuery g a)).encard ≤ 1 := by
  refine (Set.encard_le_encard (t := {g}) fun t ht ↦ ?_).trans (Set.encard_singleton g).le
  by_contra h
  simp [CanonicalGraph.NodeKeys.keyEntries, QueryCache.cacheQuery_of_ne _ _ h] at ht

/-! ## The coefficient `2` is needed -/

/-- Three independent uniform bits are one uniform triple. -/
theorem prEvent_three_bits (p : Bool → Bool → Bool → Prop) :
    Pr{let a ← $ᵗ Bool; let v ← $ᵗ Bool; let ℓ ← $ᵗ Bool}[p a v ℓ] =
      Pr{let z ← $ᵗ (Bool × Bool × Bool)}[p z.1 z.2.1 z.2.2] := by
  rw [SampleableType.prEvent_uniformSample_prod (fun z : Bool × Bool × Bool ↦ p z.1 z.2.1 z.2.2)]
  have h := prEvent_bind_congr ($ᵗ Bool)
    (fun a ↦ do let v ← $ᵗ Bool; let ℓ ← $ᵗ Bool; return p a v ℓ)
    (fun a ↦ do let y ← $ᵗ (Bool × Bool); return p a y.1 y.2) id id fun a ↦ by
      simpa only [bind_assoc, pure_bind, id_eq, bind_pure] using
        (SampleableType.prEvent_uniformSample_prod (fun y : Bool × Bool ↦ p a y.1 y.2)).symm
  simpa only [bind_assoc, pure_bind, id_eq, bind_pure] using h

/-- With one public entry at the node's key, made before the honest code, a conflict or a target
collision has probability `3/4` at `|R| = 2`. -/
theorem prEvent_forgerFirst_bool :
    Pr{let z ← (simulateQ (G Bool).deferredImpl (forgerFirst false)).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[((G Bool).Conflict st ∨ (nk Bool).TCHazard st) ∧
         ((nk Bool).keyEntries st.1).encard ≤ 1] = 3 / 4 := by
  rw [deferredImpl_run_forgerFirst]
  simp only [bind_map_left, endFill_forgerFirst, bind_assoc, pure_bind,
    conflict_or_tcHazard_iff, encard_keyEntries_le, and_true]
  rw [prEvent_three_bits (fun a v ℓ ↦ v = false ∨ ℓ = a), SampleableType.prEvent_uniformSample]
  have hc : (Finset.univ.filter
      (fun z : Bool × Bool × Bool ↦ z.2.1 = false ∨ z.2.2 = z.1)).card = 6 := by decide
  rw [hc]
  simp only [Fintype.card_prod, Fintype.card_bool]
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The single public entry exceeds a one-charge bound `#keyEntries / |R|`. -/
theorem one_charge_lt_prEvent_forgerFirst_bool :
    (1 : ℝ≥0∞) / Nat.card Bool <
      Pr{let z ← (simulateQ (G Bool).deferredImpl (forgerFirst false)).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[((G Bool).Conflict st ∨ (nk Bool).TCHazard st) ∧
           ((nk Bool).keyEntries st.1).encard ≤ 1] := by
  rw [prEvent_forgerFirst_bool, Nat.card_eq_fintype_card, Fintype.card_bool]
  have : ((1 : ℝ≥0∞) / (2 : ℕ)).toReal < ((3 : ℝ≥0∞) / 4).toReal := by
    rw [ENNReal.toReal_div, ENNReal.toReal_div]; norm_num
  exact (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
    (ENNReal.div_ne_top (by simp) (by simp))).1 this

/-- `CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_and_le` on the one-node graph over `Bool`,
with the coefficient `1` in place of `2`: the event bounded by `B` is charged
`#keyEntries / |R| + c` instead of `2 · #keyEntries / |R| + c`. -/
def OneChargeBound : Prop :=
  ∀ {S α : Type} (ms : ProbComp S) (H : S → (Bool →ₒ Bool).QueryCache → Prop)
    (c : (Bool →ₒ Bool).QueryCache → ℝ≥0∞), (∀ C, Pr{let s ← ms}[H s C] ≤ c C) →
    ∀ (oa : OracleComp ((Bool →ₒ Bool).withLabels Unit Unit Bool) α) (B : ℝ≥0∞), B ≠ ⊤ →
      Pr{let w ← (G Bool).deferredFillDraw ms oa}[
        ((G Bool).Conflict w.2.1 ∨ (nk Bool).TCHazard w.2.1 ∨ H w.2.2 w.2.1.1) ∧
          (((nk Bool).keyEntries w.2.1.1).encard : ℝ≥0∞) / Nat.card Bool + c w.2.1.1 ≤ B] ≤ B

/-- With no draw, no hazard and the budget `1/2`, the event of `OneChargeBound` on the run with
one public entry at the node's key has probability `3/4`. -/
theorem prEvent_deferredFillDraw_oneCharge_bool :
    Pr{let w ← (G Bool).deferredFillDraw (pure ()) (forgerFirst false)}[
      ((G Bool).Conflict w.2.1 ∨ (nk Bool).TCHazard w.2.1 ∨ False) ∧
        (((nk Bool).keyEntries w.2.1.1).encard : ℝ≥0∞) / Nat.card Bool + 0 ≤ 1 / 2] = 3 / 4 := by
  have key : ∀ st : RelabelState (Bool →ₒ Bool) Unit Unit Bool,
      (((G Bool).Conflict st ∨ (nk Bool).TCHazard st ∨ False) ∧
        (((nk Bool).keyEntries st.1).encard : ℝ≥0∞) / Nat.card Bool + 0 ≤ 1 / 2) ↔
      (((G Bool).Conflict st ∨ (nk Bool).TCHazard st) ∧
        ((nk Bool).keyEntries st.1).encard ≤ 1) := by
    intro st
    simp only [or_false, add_zero, Nat.card_eq_fintype_card, Fintype.card_bool, Nat.cast_ofNat]
    refine and_congr Iff.rfl ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
      ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, ← ENat.toENNReal_one,
      ENat.toENNReal_le]
  rw [← prEvent_forgerFirst_bool]
  simp only [CanonicalGraph.deferredFillDraw, bind_assoc, pure_bind, key]

/-- `OneChargeBound` fails: the coefficient `2` of
`CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_and_le` cannot be lowered to `1`. -/
theorem not_oneChargeBound : ¬OneChargeBound := fun h ↦ by
  have h1 := prEvent_deferredFillDraw_oneCharge_bool.symm.trans_le
    (h (pure ()) (fun _ _ ↦ False) (fun _ ↦ 0)
      (fun _ ↦ le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ h ↦ h)) (forgerFirst false)
      (1 / 2) (ENNReal.div_ne_top ENNReal.one_ne_top two_ne_zero))
  have h2 : ((1 : ℝ≥0∞) / 2).toReal < ((3 : ℝ≥0∞) / 4).toReal := by
    rw [ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num
  exact absurd h1 (not_le.2 ((ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
    (ENNReal.div_ne_top (by simp) (by simp))).1 h2))

/-! ## A seed hazard after the end fill -/

/-- The seed hazard: the secret is a public point the cache holds. -/
def SeedHit (s : R) (C : (R →ₒ R).QueryCache) : Prop := (C s).isSome

/-- The seed hazard's charge: the cached public points over `|R|`. -/
noncomputable def seedCharge (C : (R →ₒ R).QueryCache) : ℝ≥0∞ :=
  ({t | (C t).isSome}.encard : ℝ≥0∞) / Nat.card R

/-- A uniform secret is a cached public point with probability at most `seedCharge`. -/
theorem prEvent_seedHit_le [SampleableType R] (C : (R →ₒ R).QueryCache) :
    Pr{let s ← $ᵗ R}[SeedHit s C] ≤ seedCharge C := by
  let _ : MeasurableSpace R := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  exact SampleableType.evalDist_uniformSample_le_encard_div _

/-- With a uniform secret drawn after the end fill, a conflict, a target collision at the node's
key or a seed hit has probability at most `3/|R|`. -/
theorem prEvent_forgerFirst_seedHit_le [Inhabited R] [DecidableEq R] [SampleableType R]
    (g : R) :
    Pr{let w ← (G R).deferredFillDraw ($ᵗ R) (forgerFirst g)}[
      (G R).Conflict w.2.1 ∨ (nk R).TCHazard w.2.1 ∨ SeedHit w.2.2 w.2.1.1] ≤
      3 / Nat.card R := by
  have hcard : (Nat.card R : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
    exact ⟨inferInstance, inferInstance⟩
  refine (nk R).prEvent_deferredFillDraw_le_of_budget ($ᵗ R) SeedHit seedCharge
    prEvent_seedHit_le (forgerFirst g) _ (ENNReal.div_ne_top (by simp) hcard) fun z hz ↦ ?_
  rw [deferredImpl_run_forgerFirst, support_map] at hz
  obtain ⟨a, -, rfl⟩ := hz
  have hcache : ({t | ((∅ : (R →ₒ R).QueryCache).cacheQuery g a t).isSome}.encard : ℝ≥0∞) ≤ 1 :=
    by
      refine ENat.toENNReal_le.2 ((Set.encard_le_encard (t := {g}) fun t ht ↦ ?_).trans
        (Set.encard_singleton g).le) |>.trans_eq ENat.toENNReal_one
      by_contra h
      simp [QueryCache.cacheQuery_of_ne _ _ h] at ht
  have hkey := ENat.toENNReal_le.2 (encard_keyEntries_le g a)
  rw [ENat.toENNReal_one] at hkey
  dsimp only
  calc 2 * (((nk R).keyEntries ((∅ : (R →ₒ R).QueryCache).cacheQuery g a)).encard : ℝ≥0∞) /
        Nat.card R + seedCharge ((∅ : (R →ₒ R).QueryCache).cacheQuery g a)
      ≤ 2 * 1 / Nat.card R + 1 / Nat.card R := by
        unfold seedCharge
        gcongr
    _ = 3 / Nat.card R := by
        rw [← ENNReal.add_div]
        norm_num

/-- At `R = Fin 8` the joint bound is `3/8 < 1`. -/
example :
    Pr{let w ← (G (Fin 8)).deferredFillDraw ($ᵗ Fin 8) (forgerFirst 0)}[
      (G (Fin 8)).Conflict w.2.1 ∨ (nk (Fin 8)).TCHazard w.2.1 ∨ SeedHit w.2.2 w.2.1.1] ≤ 3 / 8 ∧
      (3 / 8 : ℝ≥0∞) < 1 := by
  refine ⟨(prEvent_forgerFirst_seedHit_le 0).trans_eq ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_ofNat]
  · rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    norm_num

end JointPotentialToy
