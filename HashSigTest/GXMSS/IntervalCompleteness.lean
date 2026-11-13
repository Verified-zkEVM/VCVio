/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Completeness

/-!
# Active-epoch correctness with a finite failing encoding

A fair randomizer succeeds exactly on true. Two retries give success mass three quarters at
both active boundaries of a height-three interior interval. Inactive epochs and zero retries
retain zero success mass.
-/

public section

namespace GXMSS.IntervalCompletenessTest

open IncomparableEncoding IntervalMerkle ENNReal OracleComp

/-- The inclusive height-three interval with active boundary epochs three and four. -/
@[expose] def middle : Interval 3 := ⟨3, 4, by decide⟩

/-- A finite common hash instance preserves separated chain and tree tweak domains. -/
@[expose] def hash : HashInstance Unit ((Fin 8 × Fin 1 × Fin 1) ⊕ (Fin 4 × Fin 8))
    (Bool ⊕ ((Bool × Bool) ⊕ (Fin 1 → Bool))) Bool 3 1 1 where
  thf := ⟨pure (), fun _ _ input => match input with | .inl x => !x | .inr _ => false⟩
  digestInput := ⟨Sum.inl, Sum.inl_injective⟩
  pairInput := ⟨fun pair => Sum.inr (Sum.inl pair),
    Function.Injective.comp Sum.inr_injective Sum.inl_injective⟩
  vectorInput := ⟨fun vector => Sum.inr (Sum.inr vector),
    Function.Injective.comp Sum.inr_injective Sum.inr_injective⟩
  chainTweak := ⟨Sum.inl, Sum.inl_injective⟩
  treeTweak := ⟨Sum.inr, Sum.inr_injective⟩
  chain_ne_tree := fun c t => Sum.inl_ne_inr (a := c) (b := t)

/-- The true randomizer returns the singleton zero word; false is returned failure. -/
@[expose] def enc : IncomparableEncoding Unit Unit Bool (Fin 8) 1 2 where
  code := {fun _ => 0}
  incomparable := by
    intro x hx y hy
    have hx' : x = fun _ => 0 := Set.mem_singleton_iff.mp hx
    have hy' : y = fun _ => 0 := Set.mem_singleton_iff.mp hy
    subst x y
    intro hne
    exact (hne rfl).elim
  encode := fun _ _ r _ => if r then some ⟨fun _ => 0, Set.mem_singleton _⟩ else none

private theorem failure_half (pp : Unit) (msg : Unit) (ep : Fin 8) :
    enc.failureMass ProbCompRuntime.probComp ($ᵗ Bool) pp msg ep = 2⁻¹ := by
  rw [IncomparableEncoding.failureMass_eq_probability, ProbCompRuntime.probComp_evalDist,
    evalDist_map_apply ($ᵗ Bool) Measurable.of_discrete (measurableSet_singleton true)]
  change 𝒟[$ᵗ Bool] {r | enc.failed pp msg ep r = true} = 2⁻¹
  rw [← prEvent_eq_evalDist_of_discrete]
  have heq : ∀ r : Bool, enc.failed pp msg ep r = true ↔ r = false := by
    intro r
    cases r <;> simp [IncomparableEncoding.failed, IncomparableEncoding.value, enc]
  simp_rw [heq]
  exact SampleableType.prEvent_uniformSample_eq_singleton false

private theorem error_half :
    enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ Bool) 2⁻¹ := by
  refine ⟨uniformSampler_uniformSample Bool, (uniformSampler_uniformSample Bool).1, ?_⟩
  intro pp msg ep
  exact le_of_eq (failure_half pp msg ep)

private theorem quarter_complement : (1 : ℝ≥0∞) - 4⁻¹ = 3 / 4 := by
  apply ENNReal.sub_eq_of_eq_add' ENNReal.one_ne_top
  rw [← one_div, ENNReal.div_add_div_same]
  norm_num [ENNReal.div_self]

/-- The finite construction satisfies the joint active-epoch correctness bound. -/
theorem active_correctness :
    (Interval.scheme hash enc 2 middle).CompleteOn ProbCompRuntime.probComp
      (Epoch.IsActive middle) (4 : ℝ≥0∞)⁻¹ := by
  have h := Interval.complete_isActive hash enc 2 middle 2⁻¹
    ((enc.uniformErrorAtMost_uniformSample_iff _).1 error_half)
  norm_num [← ENNReal.inv_pow] at h ⊢
  exact h

/-- The same finite construction also satisfies per-generated-key active correctness. -/
theorem active_correctnessPerKey :
    (Interval.scheme hash enc 2 middle).CompleteOnPerKey ProbCompRuntime.probComp
      (Epoch.IsActive middle) (4 : ℝ≥0∞)⁻¹ := by
  have h := Interval.completePerKey_isActive hash enc 2 middle 2⁻¹
    ((enc.uniformErrorAtMost_uniformSample_iff _).1 error_half)
  norm_num [← ENNReal.inv_pow] at h ⊢
  exact h

/-- The two active boundaries accept with exact retry success mass, while inactive and zero-budget
requests have zero success mass under the same consistent raw key. -/
theorem boundary_masses :
    let ks := Interval.keys hash middle () (fun _ _ => false) (fun _ => false)
    (Interval.scheme hash enc 2 middle).successMass ProbCompRuntime.probComp ks 3 () = 3 / 4 ∧
    (Interval.scheme hash enc 2 middle).successMass ProbCompRuntime.probComp ks 4 () = 3 / 4 ∧
    (Interval.scheme hash enc 2 middle).successMass ProbCompRuntime.probComp ks 2 () = 0 ∧
    (Interval.scheme hash enc 0 middle).successMass ProbCompRuntime.probComp ks 3 () = 0 := by
  let ks := Interval.keys hash middle () (fun _ _ => false) (fun _ => false)
  have hc : Interval.Consistent hash middle ks.1 ks.2 := Interval.consistent_keys _ _ _ _ _
  have h3 : Epoch.IsActive middle 3 := by decide
  have h4 : Epoch.IsActive middle 4 := by decide
  have h2 : ¬ Epoch.IsActive middle 2 := by decide
  refine ⟨?_, ?_, Interval.successMass_not_isActive hash enc 2 middle ks 2 h2 (), ?_⟩
  · rw [Interval.successMass_eq_one_sub_pow_isActive hash enc 2 middle ks hc 3 h3,
      failure_half]
    rw [← ENNReal.inv_pow]
    norm_num only [OfNat.ofNat, pow_two, Nat.reduceMul]
    exact quarter_complement
  · rw [Interval.successMass_eq_one_sub_pow_isActive hash enc 2 middle ks hc 4 h4,
      failure_half]
    rw [← ENNReal.inv_pow]
    norm_num only [OfNat.ofNat, pow_two, Nat.reduceMul]
    exact quarter_complement
  · rw [Interval.successMass_eq_one_sub_pow_isActive hash enc 0 middle ks hc 3 h3]
    simp

end GXMSS.IntervalCompletenessTest
