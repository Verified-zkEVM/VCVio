/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform sampling on the fibers of a map

`SampleableType.uniformFiber f b` samples uniformly from the fiber `{a | f a = b}` of `f : α → β`,
and falls back to a uniform sample of `α` when the fiber is empty. A uniform sample `a` of `α` is
distributed as its image `f a` followed by a uniform point of that image's fiber
(`SampleableType.uniformSample_pair_evalDistEq_uniformFiber`). A reduction that sees only `f a`
can therefore reproduce the rest of `a` exactly by sampling the fiber.
-/

public section

open OracleComp ENNReal

namespace SampleableType

variable {α β : Type} [SampleableType α]

/-- A uniform sample from the fiber `{a | f a = b}`, or a uniform sample of `α` when that fiber is
empty. -/
noncomputable def uniformFiber (f : α → β) (b : β) : ProbComp α := by
  classical
  exact if h : ∃ a, f a = b then
    letI : Nonempty {a // f a = b} := ⟨⟨h.choose, h.choose_spec⟩⟩
    letI : Fintype {a // f a = b} := Fintype.ofFinite _
    Subtype.val <$> (@uniformSample {a // f a = b} (SampleableType.ofFintype _))
  else $ᵗ α

/-- On the fiber of `f a`, the uniform fiber sample is the uniform sample of the fiber. -/
theorem uniformFiber_apply (f : α → β) (a : α) :
    letI : Nonempty {a' // f a' = f a} := ⟨⟨a, rfl⟩⟩
    letI : Fintype {a' // f a' = f a} := Fintype.ofFinite _
    uniformFiber f (f a) =
      Subtype.val <$> (@uniformSample {a' // f a' = f a} (SampleableType.ofFintype _)) := by
  have h : ∃ a', f a' = f a := ⟨a, rfl⟩
  simp only [uniformFiber, h, ↓reduceDIte]

/-- The uniform fiber sample of `f a` puts mass `1 / |f⁻¹(f a)|` on each point of that fiber. -/
theorem prEvent_uniformFiber_eq_of_eq (f : α → β) {a x : α} (hx : f x = f a) :
    Pr{let y ← uniformFiber f (f a)}[y = x] = (Nat.card {a' // f a' = f a} : ℝ≥0∞)⁻¹ := by
  let : Nonempty {a' // f a' = f a} := ⟨⟨a, rfl⟩⟩
  let : Fintype {a' // f a' = f a} := Fintype.ofFinite _
  let : SampleableType {a' // f a' = f a} := SampleableType.ofFintype _
  rw [uniformFiber_apply, prEvent_map]
  rw [show (fun y : {a' // f a' = f a} => y.1 = x) = fun y => y = ⟨x, hx⟩ from
    funext fun y => propext (Subtype.ext_iff (a1 := y) (a2 := ⟨x, hx⟩)).symm]
  exact prEvent_uniformSample_eq_singleton_natCard (⟨x, hx⟩ : {a' // f a' = f a})

/-- The uniform fiber sample of `f a` puts no mass outside that fiber. -/
theorem prEvent_uniformFiber_eq_zero_of_ne (f : α → β) {a x : α} (hx : f x ≠ f a) :
    Pr{let y ← uniformFiber f (f a)}[y = x] = 0 := by
  let : Nonempty {a' // f a' = f a} := ⟨⟨a, rfl⟩⟩
  let : Fintype {a' // f a' = f a} := Fintype.ofFinite _
  let : SampleableType {a' // f a' = f a} := SampleableType.ofFintype _
  rw [uniformFiber_apply, prEvent_map]
  exact prEvent_eq_zero_of_forall_mem_support _ _ fun y _ hy => hx (hy ▸ y.2)

/-- **A uniform sample is its image followed by a uniform point of that image's fiber.** For a
uniform `a`, the pair `(f a, a)` has the distribution of `(f a, a')` with `a'` drawn by
`uniformFiber f (f a)`. -/
theorem uniformSample_pair_evalDistEq_uniformFiber (f : α → β) :
    (do let a ← $ᵗ α; return (f a, a) : ProbComp (β × α)) =ᵈ
      (do let a ← $ᵗ α; let a' ← uniformFiber f (f a); return (f a, a')) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun bx => ?_
  obtain ⟨b, x⟩ := bx
  rw [prEvent_bind_eq_sum_fintype, prEvent_bind_eq_sum_fintype]
  simp only [prEvent_uniformSample_eq_singleton, ← Finset.mul_sum]
  congr 1
  have hterm : ∀ a, Pr{let y ← (do let a' ← uniformFiber f (f a); return (f a, a') :
      ProbComp (β × α))}[y = (b, x)] =
      if f a = b then (if f x = b then (Fintype.card {a' // f a' = b} : ℝ≥0∞)⁻¹ else 0)
      else 0 := by
    intro a
    rw [bind_pure_comp, prEvent_map]
    by_cases hab : f a = b
    · subst hab
      simp only [Prod.mk.injEq, true_and, ite_true]
      by_cases hxb : f x = f a
      · simp only [hxb, ite_true]
        rw [prEvent_uniformFiber_eq_of_eq f hxb, Nat.card_eq_fintype_card]
      · simp only [hxb, ite_false]
        exact prEvent_uniformFiber_eq_zero_of_ne f hxb
    · simp only [hab, ite_false, Prod.mk.injEq, false_and]
      exact prEvent_eq_zero_of_forall_mem_support _ _ fun _ _ h => h
  simp only [hterm, prEvent_pure, Prod.mk.injEq]
  by_cases hxb : f x = b
  · have : Nonempty {a' // f a' = b} := ⟨⟨x, hxb⟩⟩
    have hpos : (Fintype.card {a' // f a' = b} : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have h1 : Fintype.card {y // f y = b ∧ y = x} = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨⟨x, hxb, rfl⟩, fun y => Subtype.ext y.2.2⟩
    simp only [hxb, ite_true, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    rw [← Fintype.card_subtype, ← Fintype.card_subtype, h1, Nat.cast_one, mul_one,
      ENNReal.mul_inv_cancel hpos (ENNReal.natCast_ne_top _)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have h : ¬ (f a = b ∧ a = x) := fun h => hxb (h.2 ▸ h.1)
    simp only [h, hxb, ite_false, ite_self]

/-- The bind form of `uniformSample_pair_evalDistEq_uniformFiber`: a continuation of a uniform `a`
that depends on `a` through `f a` and `a` itself sees the same distribution when `a` is replaced by
a uniform point of the fiber of `f a`. -/
theorem uniformSample_bind_evalDistEq_uniformFiber {γ : Type} (f : α → β)
    (k : β → α → ProbComp γ) :
    (do let a ← $ᵗ α; k (f a) a) =ᵈ
      (do let a ← $ᵗ α; let a' ← uniformFiber f (f a); k (f a) a') := by
  simpa only [bind_assoc, pure_bind] using
    (uniformSample_pair_evalDistEq_uniformFiber f).bind_left fun ba => k ba.1 ba.2

end SampleableType
