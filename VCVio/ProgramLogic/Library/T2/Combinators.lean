/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.ProgramLogic.Library.T1.RunNF

/-!
# Specifications for handler combinators

Weakest-precondition rules for the handler combinators that build stateful handlers out of other
handlers, stated for every `WPMonad` base and assertion language, so they apply under every
reading:

* `QueryImpl.add` (sum handlers `impl₁ + impl₂`): a query of a summand is that summand's call
  (`add_inl_wp`, `add_inr_wp`); frames of sums come from T1's `QueryImpl.MonotoneState.add`.
* `QueryImpl.liftTarget`: a lifted stateless handler leaves the state alone.
* `QueryImpl.extendState`: the base handler runs on the first component and the auxiliary update
  writes the second.
* `QueryImpl.withBadFlag` and `QueryImpl.withBadUpdate`: the bad flag is threaded unchanged, or
  or-updated. Over `OracleComp` both are `QueryImpl.MonotoneState` for "the flag is never
  lowered", so T1's frame steps over an opaque run, also of a sum of such handlers;
  `simulateQ_withBadFlag_wp` is the sharper frame "the flag is unchanged".

Each `wp` rule's precondition is the weakest precondition of the underlying handler, so `vcgen`
continues with that handler's own rule. The `mem_support_*_run_iff` lemmas split a reachable step
of the combinator into a reachable step of the underlying handler.
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary

universe u v w z z' u' v'

namespace QueryImpl

section anyBase

variable {m : Type w → Type v} [Monad m] {Pred : Type z} {EPred : Type z'} [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred]

section add

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{u, w} ι₂}

/-- A left query of a sum handler is a call of the left summand. The postcondition is typed at
the sum's answer type and the summand's call at its own, which `vcgen` needs to match both. -/
@[spec]
theorem add_inl_wp (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) (t : spec₁.Domain)
    (post : (spec₁ + spec₂).Range (.inl t) → Pred) (epost : EPred) :
    ⦃ wp (impl₁ t) (fun u : spec₁.Range t => post u) epost ⦄ (impl₁ + impl₂) (.inl t)
      ⦃ post; epost ⦄ :=
  ⟨Lean.Order.PartialOrder.rel_refl⟩

/-- A right query of a sum handler is a call of the right summand. -/
@[spec]
theorem add_inr_wp (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) (t : spec₂.Domain)
    (post : (spec₁ + spec₂).Range (.inr t) → Pred) (epost : EPred) :
    ⦃ wp (impl₂ t) (fun u : spec₂.Range t => post u) epost ⦄ (impl₁ + impl₂) (.inr t)
      ⦃ post; epost ⦄ :=
  ⟨Lean.Order.PartialOrder.rel_refl⟩

end add

variable {ι : Type u} {spec : OracleSpec.{u, w} ι} {σ : Type w}

/-- A stateless handler lifted into `StateT` answers as the handler and keeps the state. -/
@[spec]
theorem liftTarget_wp (so : QueryImpl spec m) (t : spec.Domain)
    (post : spec.Range t → σ → Pred) (epost : EPred) :
    ⦃ fun s => wp (so t) (fun u => post u s) epost ⦄ so.liftTarget (StateT σ m) t
      ⦃ post; epost ⦄ := by
  refine ⟨fun s => ?_⟩
  rw [StateT.wp_apply_eq, liftTarget_apply, OracleComp.liftM_run_StateT]
  refine Lean.Order.PartialOrder.rel_trans ?_ (WPMonad.bind_le_wp_bind (m := m) _ _ _ epost)
  exact WP.wp_consequence _ _ _ epost fun u =>
    WPMonad.pure_le_wp_pure (m := m) (u, s) (fun x : spec.Range t × σ => post x.1 x.2) epost

/-- A bad-flag lift runs the handler on the first component and keeps the flag. -/
@[spec]
theorem withBadFlag_wp (impl : QueryImpl spec (StateT σ m)) (t : spec.Domain)
    (post : spec.Range t → σ × Bool → Pred) (epost : EPred) :
    ⦃ fun s => wp (impl t) (fun u s' => post u (s', s.2)) epost s.1 ⦄ impl.withBadFlag t
      ⦃ post; epost ⦄ :=
  ⟨fun ⟨s, b⟩ => WPMonad.map_le_wp_map (m := m) (fun vs : spec.Range t × σ => (vs.1, vs.2, b))
    ((impl t).run s) (fun x : spec.Range t × σ × Bool => post x.1 x.2) epost⟩

/-- A bad-flag update runs the handler on the first component and or-updates the flag with the
predicate evaluated on the pre-state and the answer. -/
@[spec]
theorem withBadUpdate_wp (impl : QueryImpl spec (StateT σ m))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool) (t : spec.Domain)
    (post : spec.Range t → σ × Bool → Pred) (epost : EPred) :
    ⦃ fun s => wp (impl t) (fun u s' => post u (s', s.2 || f t s.1 u)) epost s.1 ⦄
      impl.withBadUpdate f t ⦃ post; epost ⦄ :=
  ⟨fun ⟨s, b⟩ => WPMonad.map_le_wp_map (m := m)
    (fun vs : spec.Range t × σ => (vs.1, vs.2, b || f t s vs.1)) ((impl t).run s)
    (fun x : spec.Range t × σ × Bool => post x.1 x.2) epost⟩

end anyBase

section extend

variable {m : Type u → Type v} [Monad m] {Pred : Type z} {EPred : Type z'} [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] {ι : Type u} {spec : OracleSpec.{u, u} ι}
  {σ Q : Type u}

/-- An extended handler runs the base handler on the first component and writes the auxiliary
update into the second. -/
@[spec]
theorem extendState_wp (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) (t : spec.Domain)
    (post : spec.Range t → σ × Q → Pred) (epost : EPred) :
    ⦃ fun s => wp (so t) (fun u s' => post u (s', aux t s.1 u s' s.2)) epost s.1 ⦄
      extendState so aux t ⦃ post; epost ⦄ := by
  refine ⟨fun s => ?_⟩
  rw [StateT.wp_apply_eq, StateT.wp_apply_eq, extendState_apply]
  refine Lean.Order.PartialOrder.rel_trans ?_ (WPMonad.bind_le_wp_bind (m := m) _ _ _ epost)
  exact WP.wp_consequence _ _ _ epost fun p =>
    WPMonad.pure_le_wp_pure (m := m) (p.1, (p.2, aux t s.1 p.1 p.2 s.2))
      (fun x : spec.Range t × σ × Q => post x.1 x.2) epost

end extend

/-! ## Support of combinator steps over `OracleComp` -/

section oracleCompBase

variable {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}

variable {ι : Type u} {spec : OracleSpec.{u, w} ι} {σ : Type w}

/-- A reachable bad-flag step is a reachable step of the handler with the flag unchanged. -/
theorem mem_support_withBadFlag_run_iff (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    {t : spec.Domain} {s s' : σ} {b b' : Bool} {u : spec.Range t} :
    (u, s', b') ∈ support ((impl.withBadFlag t).run (s, b)) ↔
      (u, s') ∈ support ((impl t).run s) ∧ b' = b := by
  rw [withBadFlag_apply_run, support_map]
  constructor
  · rintro ⟨⟨u, s'⟩, h, h'⟩
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨(u, s'), h, rfl⟩

/-- A reachable bad-flag update is a reachable step of the handler with the flag or-updated. -/
theorem mem_support_withBadUpdate_run_iff (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool) {t : spec.Domain} {s s' : σ}
    {b b' : Bool} {u : spec.Range t} :
    (u, s', b') ∈ support ((impl.withBadUpdate f t).run (s, b)) ↔
      (u, s') ∈ support ((impl t).run s) ∧ b' = (b || f t s u) := by
  rw [withBadUpdate_apply_run, support_map]
  constructor
  · rintro ⟨⟨u, s'⟩, h, h'⟩
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨(u, s'), h, rfl⟩

/-- A bad-flag lift never lowers the flag, the frame it shares with `withBadUpdate`. -/
instance monotoneState_withBadFlag (impl : QueryImpl spec (StateT σ (OracleComp spec'))) :
    impl.withBadFlag.MonotoneState fun s s' => s.2 = true → s'.2 = true :=
  .of_inv fun _ ⟨_, _⟩ hb ⟨_, _, _⟩ hz => ((mem_support_withBadFlag_run_iff impl).1 hz).2 ▸ hb

/-- A bad-flag update never lowers the flag. -/
instance monotoneState_withBadUpdate (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool) :
    (impl.withBadUpdate f).MonotoneState fun s s' => s.2 = true → s'.2 = true :=
  .of_inv fun _ ⟨_, b⟩ hb ⟨_, _, _⟩ hz => by
    rw [((mem_support_withBadUpdate_run_iff impl f).1 hz).2]
    simp_all

/-- A run of a bad-flag lift keeps the flag, whatever the program. Sharper than the instance
frame; pass it to `vcgen` explicitly. -/
theorem simulateQ_withBadFlag_wp {α : Type w} (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (oa : OracleComp spec α) (post : α → σ × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ a s', s'.2 = s.2 → post a s' ⦄ (simulateQ impl.withBadFlag oa)
      ⦃ post; epost ⦄ :=
  OracleComp.ProgramLogic.triple_simulateQ_frame _ (fun s s' : σ × Bool => s'.2 = s.2)
    (fun _ => rfl) (fun _ _ _ h₁₂ h₂₃ => by exact h₂₃.trans h₁₂)
    (fun _ s z hz => ((mem_support_withBadFlag_run_iff impl).1 (by exact hz)).2) oa

end oracleCompBase

section extendSupport

variable {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'} {ι : Type u} {spec : OracleSpec.{u, u} ι}
  {σ Q : Type u}

/-- A reachable step of an extended handler is a reachable base step with the auxiliary update
written into the second component. -/
theorem mem_support_extendState_run_iff (so : QueryImpl spec (StateT σ (OracleComp spec')))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) {t : spec.Domain} {s : σ × Q}
    {u : spec.Range t} {s' : σ × Q} :
    (u, s') ∈ support ((extendState so aux t).run s) ↔
      (u, s'.1) ∈ support ((so t).run s.1) ∧ s'.2 = aux t s.1 u s'.1 s.2 := by
  rw [extendState_apply, mem_support_bind_iff]
  constructor
  · rintro ⟨⟨u', s₁⟩, h, h'⟩
    rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨h, rfl⟩
  · rintro ⟨h, h'⟩
    refine ⟨(u, s'.1), h, ?_⟩
    rw [support_pure, Set.mem_singleton_iff]
    exact Prod.ext rfl (Prod.ext rfl h')

end extendSupport

attribute [simulateQ_nf] withBadFlag_apply_run withBadUpdate_apply_run extendState_apply

end QueryImpl
