/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Aeneas.Data.Coinductive.ITreeWP.Taxonomy
public import Interop.Aeneas.ITree
public import PolyFun.ITree.WP.Bind

/-!
# Aeneas's weakest preconditions are PolyFun's readings

Aeneas specifies each effect by an `EffectWP E`: a predicate transformer per operation, over a
state threaded through the effects. That is a PolyFun per-operation spec on `E.toPFunctor`, over
the lattice `θ.State → Prop` (`Aeneas.Data.Coinductive.EffectWP.toOpSpec`). Aeneas's total
correctness `DWP` and partial correctness `DWLP` are the least and greatest fixed points of a
functional on its trees. Along `ITree.toPolyFun`, they are PolyFun's readings:
* `DWP θ t Q` is `ITree.wpTotal θ.toOpSpec t.toPolyFun Q`;
* `DWLP θ t Q` is `ITree.wpPartial θ.toOpSpec t.toPolyFun Q`.

Aeneas's divergence `div` becomes `ITree.diverge`, which the readings send to `⊥` and `⊤`, as
Aeneas sends `div` to `False` and `True`. Each equality is proved by two fixed-point arguments
with only Aeneas's public API. They give exact `bind` laws for `DWP` and `DWLP`, where Aeneas
proves one direction (`DWP.bind`, `DWLP.bind`).

## Main definitions

* `Aeneas.Data.Coinductive.EffectWP.toOpSpec`: an Aeneas effect specification as a PolyFun spec.

## Main results

* `Aeneas.Data.Coinductive.DWP_eq_wpTotal`, `Aeneas.Data.Coinductive.DWLP_eq_wpPartial`.
* `Aeneas.Data.Coinductive.DWP_bind`, `Aeneas.Data.Coinductive.DWLP_bind`: exact `bind` laws.
-/

@[expose] public section

namespace Aeneas.Data.Coinductive

universe u v w

variable {E : Effect.{v}} {α : Type u}

/-- An Aeneas effect specification as a PolyFun per-operation spec over `θ.State → Prop`. -/
def EffectWP.toOpSpec (θ : EffectWP.{w, v} E) : PFunctor.OpSpec E.toPFunctor (θ.State → Prop) :=
  fun a k => θ.wp a k

theorem EffectWP.toOpSpec_monotone (θ : EffectWP.{w, v} E) [θ.Monotonic] :
    θ.toOpSpec.Monotone :=
  fun _ _ _ h _ hs => θ.wp_monotonic (fun b s' hb => h b s' hb) hs

variable (θ : EffectWP.{w, v} E) [θ.Monotonic] (Q : θ.Post α)

/-- Aeneas's total correctness is PolyFun's total reading of the tree. -/
theorem DWP_eq_wpTotal (t : ITree E α) :
    DWP θ t Q = _root_.ITree.wpTotal θ.toOpSpec t.toPolyFun Q := by
  have hΦ := θ.toOpSpec_monotone
  funext s
  apply propext
  constructor
  · -- `DWP` is below every prefixed point, in particular the PolyFun reading.
    refine fun h => DWP.least (X := fun t s => _root_.ITree.wpTotal θ.toOpSpec t.toPolyFun Q s)
      ?_ t s h
    intro t s ht
    cases t using ITree.cases with
    | ret v =>
      rw [ITree.pure_eq_ret, FunctionalWP.ret] at ht
      change _root_.ITree.wpTotal θ.toOpSpec (ITree.toPolyFun (ITree.ret v)) Q s
      rw [ITree.toPolyFun_ret, _root_.ITree.wpTotal_pure hΦ]
      exact ht
    | div => rw [FunctionalWP.div] at ht; exact ht.elim
    | vis e k =>
      rw [FunctionalWP.vis] at ht
      rw [ITree.toPolyFun_vis, _root_.ITree.wpTotal_query hΦ]
      exact ht
  · -- The PolyFun reading is below every prefixed point, in particular the infimum of `DWP` over
    -- the trees with the same image.
    refine fun h => (_root_.ITree.wpTotal_le_of_wpStepFun_le
      (X := fun u s => ∀ t : ITree E α, t.toPolyFun = u → DWP θ t Q s) ?_ t.toPolyFun) s h t rfl
    intro u s hu t ht
    subst ht
    cases t using ITree.cases with
    | ret v =>
      change _root_.ITree.wpStepFun θ.toOpSpec Q _ (ITree.toPolyFun (ITree.ret v)) s at hu
      rw [ITree.toPolyFun_ret, _root_.ITree.wpStepFun_pure] at hu
      exact (DWP.ret_iff).mpr hu
    | div =>
      rw [ITree.toPolyFun_div, _root_.ITree.wpStepFun, _root_.ITree.shape'_diverge] at hu
      exact hu .div ITree.toPolyFun_div
    | vis e k =>
      rw [ITree.toPolyFun_vis, _root_.ITree.wpStepFun_query] at hu
      exact DWP.vis (θ.wp_monotonic (fun b s' hb => hb (k b) rfl) hu)

/-- Aeneas's partial correctness is PolyFun's partial reading of the tree. -/
theorem DWLP_eq_wpPartial (t : ITree E α) :
    DWLP θ t Q = _root_.ITree.wpPartial θ.toOpSpec t.toPolyFun Q := by
  have hΦ := θ.toOpSpec_monotone
  funext s
  apply propext
  constructor
  · -- `DWLP` is a postfixed point of the PolyFun equations, through the trees with each image.
    refine fun h => _root_.ITree.le_wpPartial_of_le_wpStepFun
      (X := fun u s => ∃ t : ITree E α, t.toPolyFun = u ∧ DWLP θ t Q s) ?_ t.toPolyFun s
      ⟨t, rfl, h⟩
    rintro u s ⟨t, rfl, ht⟩
    cases t using ITree.cases with
    | ret v =>
      change _root_.ITree.wpStepFun θ.toOpSpec Q _ (ITree.toPolyFun (ITree.ret v)) s
      rw [ITree.toPolyFun_ret, _root_.ITree.wpStepFun_pure]
      exact (DWLP.ret_iff).mp ht
    | div =>
      rw [ITree.toPolyFun_div, _root_.ITree.wpStepFun, _root_.ITree.shape'_diverge]
      exact ⟨.div, ITree.toPolyFun_div, DWLP.div⟩
    | vis e k =>
      rw [ITree.toPolyFun_vis, _root_.ITree.wpStepFun_query]
      exact θ.wp_monotonic (fun b s' hb => ⟨k b, rfl, hb⟩) (DWLP.vis_view ht)
  · -- The PolyFun reading is a postfixed point of Aeneas's functional, so it is below `DWLP`.
    refine fun h => DWLP.greatest
      (X := fun t s => _root_.ITree.wpPartial θ.toOpSpec t.toPolyFun Q s) ?_ t s h
    intro t s ht
    cases t using ITree.cases with
    | ret v =>
      rw [ITree.pure_eq_ret, FunctionalWP.ret]
      change _root_.ITree.wpPartial θ.toOpSpec (ITree.toPolyFun (ITree.ret v)) Q s at ht
      rwa [ITree.toPolyFun_ret, _root_.ITree.wpPartial_pure hΦ] at ht
    | div => rw [FunctionalWP.div]; trivial
    | vis e k =>
      rw [FunctionalWP.vis]
      change _root_.ITree.wpPartial θ.toOpSpec (ITree.toPolyFun (ITree.vis e k)) Q s at ht
      rwa [ITree.toPolyFun_vis, _root_.ITree.wpPartial_query hΦ] at ht

/-- Aeneas's total correctness distributes over `bind` exactly. Aeneas proves one direction
(`DWP.bind`); the other comes through PolyFun. -/
theorem DWP_bind {β : Type u} (t : ITree E α) (k : α → ITree E β) (Q : θ.Post β) :
    DWP θ (t >>= k) Q = DWP θ t fun a => DWP θ (k a) Q := by
  rw [DWP_eq_wpTotal, ITree.toPolyFun_bind, _root_.ITree.wpTotal_bind θ.toOpSpec_monotone,
    DWP_eq_wpTotal]
  congr 1
  funext a
  rw [DWP_eq_wpTotal]

/-- Aeneas's partial correctness distributes over `bind` exactly. -/
theorem DWLP_bind {β : Type u} (t : ITree E α) (k : α → ITree E β) (Q : θ.Post β) :
    DWLP θ (t >>= k) Q = DWLP θ t fun a => DWLP θ (k a) Q := by
  rw [DWLP_eq_wpPartial, ITree.toPolyFun_bind, _root_.ITree.wpPartial_bind θ.toOpSpec_monotone,
    DWLP_eq_wpPartial]
  congr 1
  funext a
  rw [DWLP_eq_wpPartial]

end Aeneas.Data.Coinductive
