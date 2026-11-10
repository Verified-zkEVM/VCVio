/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Aeneas.Data.Coinductive.ITree
public import PolyFun.Control.Monad.Hom
public import PolyFun.ITree.Bisim.Bind
public import PolyFun.ITree.Construct

/-!
# Aeneas's interaction trees as PolyFun's

Aeneas's coinductive library has its own interaction trees, `Aeneas.Data.Coinductive.ITree E α`,
over an effect `E` with operations `E.I` and answers `E.O`. A node is a return, a visible effect, or
an explicit divergence `div`, which is the bottom element for `partial_fixpoint`; there are no
silent steps. PolyFun's `ITree F α` is the final coalgebra over a polynomial functor `F`, with
silent steps.

An effect is a polynomial functor (`Aeneas.Data.Coinductive.Effect.toPFunctor`), and every Aeneas
tree is a PolyFun tree with the same returns and effects, `div` becoming the silent divergence
`ITree.diverge`. The map preserves `pure` and `bind` exactly, not only up to weak bisimulation,
because divergence is the only place an Aeneas tree becomes a PolyFun tree with silent steps.

## Main definitions

* `Aeneas.Data.Coinductive.Effect.toPFunctor`: an effect as a polynomial functor.
* `Aeneas.Data.Coinductive.ITree.toPolyFun`: the map, by corecursion, and `toPolyFunHom` bundled
  as a monad morphism.

## Main results

* `toPolyFun_ret`, `toPolyFun_div`, `toPolyFun_vis`: the map on each kind of node.
* `toPolyFun_bind`: the map commutes with `bind`.
-/

public section

namespace Aeneas.Data.Coinductive

universe u v

/-- An effect as a polynomial functor: the operations are the positions, and the answers to an
operation are its directions. -/
@[expose, reducible]
def Effect.toPFunctor (E : Effect.{v}) : _root_.PFunctor.{v, v} :=
  ⟨E.I, E.O⟩

namespace ITree

variable {E : Effect.{v}} {α β : Type u}

/-- One layer of `toPolyFun`: a return is a leaf, an effect is a query with the same
continuation, and `div` is a silent step back to the same tree. -/
@[expose]
def toPolyFunStep (t : ITree E α) : (_root_.ITree.ViewPoly E.toPFunctor α).Obj (ITree E α) :=
  match t.unfold with
  | .ret r => ⟨.pure r, PEmpty.elim⟩
  | .div => ⟨.step, fun _ => t⟩
  | .vis i k => ⟨.query i, k⟩

/-- An Aeneas interaction tree as a PolyFun interaction tree. -/
@[expose]
def toPolyFun (t : ITree E α) : _root_.ITree E.toPFunctor α :=
  _root_.ITree.corec toPolyFunStep t

@[simp]
theorem toPolyFun_ret (r : α) : toPolyFun (ret r : ITree E α) = _root_.ITree.pure r := by
  apply _root_.ITree.eq_of_shape'_eq
  rw [toPolyFun, _root_.ITree.shape'_corec_eq _ _ (by simp only [toPolyFunStep, unfold_ret]; rfl),
    _root_.ITree.shape'_pure]
  exact PFunctor.Obj.ext rfl (heq_of_eq (funext fun direction => direction.elim))

@[simp]
theorem toPolyFun_pure (r : α) : toPolyFun (pure r : ITree E α) = pure r :=
  toPolyFun_ret r

@[simp]
theorem toPolyFun_vis (i : E.I) (k : E.O i → ITree E α) :
    toPolyFun (vis i k) = _root_.ITree.query (F := E.toPFunctor) i (fun o => toPolyFun (k o)) := by
  apply _root_.ITree.eq_of_shape'_eq
  rw [toPolyFun, _root_.ITree.shape'_corec_eq _ _ (by simp only [toPolyFunStep, unfold_vis]; rfl),
    _root_.ITree.shape'_query]
  rfl

/-- The image of `div` is a silent step in front of itself. -/
theorem toPolyFun_div_eq_step :
    toPolyFun (div : ITree E α) = _root_.ITree.step (toPolyFun (div : ITree E α)) := by
  apply _root_.ITree.eq_of_shape'_eq
  rw [toPolyFun, _root_.ITree.shape'_corec_eq _ _ (by simp only [toPolyFunStep, unfold_tau]; rfl),
    _root_.ITree.shape'_step]

@[simp]
theorem toPolyFun_div : toPolyFun (div : ITree E α) = _root_.ITree.diverge := by
  refine _root_.ITree.bisim
    (fun a b => a = toPolyFun (div : ITree E α) ∧ b = _root_.ITree.diverge) ?_ _ _
    ⟨rfl, rfl⟩
  rintro _ _ ⟨rfl, rfl⟩
  refine ⟨.step, fun _ => toPolyFun (div : ITree E α), fun _ => _root_.ITree.diverge, ?_,
    _root_.ITree.shape'_diverge, fun _ => ⟨rfl, rfl⟩⟩
  conv_lhs => rw [toPolyFun_div_eq_step, _root_.ITree.shape'_step]

/-- The map commutes with `bind`. -/
theorem toPolyFun_bind (t : ITree E α) (f : α → ITree E β) :
    toPolyFun (t >>= f) = toPolyFun t >>= fun a => toPolyFun (f a) := by
  refine _root_.ITree.bisim (fun a b => a = b ∨
      ∃ t : ITree E α, a = toPolyFun (t >>= f) ∧ b = toPolyFun t >>= fun a => toPolyFun (f a))
    ?_ _ _ (.inr ⟨t, rfl, rfl⟩)
  have refl (a : _root_.ITree E.toPFunctor β) : ∃ shape leftNext rightNext,
      a.shape' = .mk shape leftNext ∧ a.shape' = .mk shape rightNext ∧
        ∀ direction, leftNext direction = rightNext direction ∨ ∃ t : ITree E α,
          leftNext direction = toPolyFun (t >>= f) ∧
            rightNext direction = toPolyFun t >>= fun a => toPolyFun (f a) :=
    ⟨_, _, _, rfl, rfl, fun _ => .inl rfl⟩
  rintro _ _ (rfl | ⟨t, rfl, rfl⟩)
  · exact refl _
  · cases t using ITree.cases with
    | ret r =>
      rw [pure_bind, toPolyFun_pure, _root_.ITree.bind_eq_bind, _root_.ITree.pure_eq_pure,
        _root_.ITree.bind_pure_left]
      exact refl _
    | div =>
      refine ⟨.step, fun _ => toPolyFun (div : ITree E β),
        fun _ => toPolyFun (div : ITree E α) >>= fun a => toPolyFun (f a), ?_, ?_,
        fun _ => .inr ⟨div, by rw [div_bind], rfl⟩⟩
      · conv_lhs => rw [div_bind, toPolyFun_div_eq_step, _root_.ITree.shape'_step]
      · conv_lhs => rw [_root_.ITree.bind_eq_bind, toPolyFun_div_eq_step, _root_.ITree.bind_step,
          _root_.ITree.shape'_step]
        rfl
    | vis i k =>
      rw [vis_bind, toPolyFun_vis, toPolyFun_vis, _root_.ITree.bind_eq_bind,
        _root_.ITree.bind_query]
      exact ⟨.query i, _, _, _root_.ITree.shape'_query _ _, _root_.ITree.shape'_query _ _,
        fun o => .inr ⟨k o, rfl, rfl⟩⟩

/-- The map is injective: an Aeneas tree is determined by its PolyFun image. Two trees with the
same image agree at every depth of approximation. -/
theorem toPolyFun_injective :
    Function.Injective (toPolyFun : ITree E α → _root_.ITree E.toPFunctor α) := by
  suffices h : ∀ n (t₁ t₂ : ITree E α), toPolyFun t₁ = toPolyFun t₂ →
      t₁.approx n = t₂.approx n from
    fun t₁ t₂ heq => CoInd.ext _ _ _ fun n => h n t₁ t₂ heq
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t₁ t₂ heq
    have hshape := congrArg _root_.ITree.shape heq
    cases t₁ using ITree.cases <;> cases t₂ using ITree.cases <;>
      simp only [toPolyFun_pure, _root_.ITree.pure_eq_pure, toPolyFun_div, toPolyFun_vis,
        _root_.ITree.shape_pure,
        _root_.ITree.shape_diverge, _root_.ITree.shape_query, reduceCtorEq,
        _root_.ITree.Shape.pure.injEq, _root_.ITree.Shape.query.injEq] at hshape heq ⊢
    case succ.ret.ret r₁ r₂ => rw [hshape]
    case succ.vis.vis i₁ k₁ i₂ k₂ =>
      subst hshape
      have hk := eq_of_heq (Sigma.mk.inj (congrArg _root_.ITree.shape' heq)).2
      simp only [vis_approx_1]
      exact congrArg (ITreeF.vis i₁) (funext fun o => ih _ _ (congrFun hk o))

/-- The map as a bundled monad morphism. -/
@[expose]
def toPolyFunHom : ITree.{u} E →ᵐ _root_.ITree E.toPFunctor where
  toFun _ := toPolyFun
  toFun_pure' := toPolyFun_pure
  toFun_bind' := toPolyFun_bind

@[simp]
theorem toPolyFunHom_apply (t : ITree E α) : toPolyFunHom t = toPolyFun t :=
  rfl

end ITree

end Aeneas.Data.Coinductive
