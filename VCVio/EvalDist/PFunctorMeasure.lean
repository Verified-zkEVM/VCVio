/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.ProbabilityMassFunction.Measure
public import VCVio.EvalDist.PFunctor

/-!
# Measure semantics for polynomial free monads

`VCVio.EvalDist.PFunctor` interprets a polynomial free program in `PMF`, folding it with
`FreeM.liftM` through a `Handler PMF P`. This module gives the same programs a denotation as a
Mathlib `Measure`.

## Why a separate fold

`Measure α` becomes a type only after `α` receives a `MeasurableSpace`, so a measure-valued
denotation cannot be a `MonadLiftT _ (Type u → Type u)` the way the `PMF` one is, and
`FreeM.liftM` — which asks for `[Monad m] [LawfulMonad m]` — does not apply. `denote` is
therefore an explicit recursion over the free monad, using `Measure.bind` at each operation.
Its `pure` / `liftBind` shape is the same one `PFunctor.FreeM.instEvalDistCompatible` inducts
over.

This is the intended trade. Mathlib's probability library is stated for `Measure` over an
ambient `MeasurableSpace`, so a denotation in that form reaches the library directly, whereas
any wrapper chosen to preserve the monad shape would have to restate it.

## Generality

`IsMeasureSpec` requires only that answer types be measurable, not that they be discrete. A
continuous oracle — an operation answering with, say, `ProbabilityTheory.gaussianReal` — is
therefore expressible, which no `Handler PMF P` can be.

Discreteness buys away the side conditions rather than the expressiveness. `Measurable.of_discrete`
needs `DiscreteMeasurableSpace` on the *domain* only, so discrete answer types make the
monad-morphism laws unconditional while leaving the output type an arbitrary measurable space.
The general laws carry the measurability hypothesis explicitly; the `*_of_discrete` corollaries
discharge it.

## Main definitions

* `PFunctor.IsMeasureSpec P` — per-operation answer measures.
* `PFunctor.FreeM.denote` — the measure denoted by a free program.

## Main statements

* `PFunctor.FreeM.denote_bind_of_discrete` — `denote` is a monad morphism into the Giry monad.
* `PFunctor.FreeM.denote_eq_toMeasure` — agreement with the `PMF` denotation of
  `VCVio.EvalDist.PFunctor`.
-/

@[expose] public section

open MeasureTheory ENNReal

universe u uA

namespace PFunctor

/-- Per-operation answer measures for a polynomial interface.

The measurable structure on answer types is a separate parameter rather than a field, mirroring
Mathlib's separation of `MeasurableSpace` from the measures carried on it. Answer types are not
required to be discrete; see the module docstring. -/
class IsMeasureSpec (P : PFunctor.{uA, u}) [∀ a, MeasurableSpace (P.B a)] where
  /-- The distribution of answers to an operation. -/
  toMeasure : (a : P.A) → Measure (P.B a)
  /-- Answering an operation is lossless. -/
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (toMeasure a)

attribute [instance] IsMeasureSpec.isProbabilityMeasure

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  {α β : Type u}

/-- The measure denoted by a polynomial free program: `pure` is a Dirac mass, and each
operation is the Giry bind of its answer measure with the denotation of the continuation. -/
noncomputable def denote [MeasurableSpace α] : FreeM P α → Measure α
  | .pure x => Measure.dirac x
  | .liftBind a cont => Measure.bind (IsMeasureSpec.toMeasure a) fun b => denote (cont b)

@[simp]
theorem denote_pure [MeasurableSpace α] (x : α) :
    denote (pure x : FreeM P α) = Measure.dirac x := rfl

@[simp]
theorem denote_liftBind [MeasurableSpace α] (a : P.A) (cont : P.B a → FreeM P α) :
    denote (FreeM.liftBind a cont)
      = Measure.bind (IsMeasureSpec.toMeasure a) fun b => denote (cont b) := rfl

/-! ### The monad-morphism laws

`denote` sends `pure` to `dirac` definitionally. For `bind` it must know that the continuation
is measurable, in two places: at the output type, and at each operation's answer type. The
general statement carries the first as a hypothesis; discreteness of the answer types
discharges the second, and `denote_bind_of_discrete` discharges both. -/

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

theorem denote_bind [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → FreeM P β)
    (hf : Measurable fun x => denote (f x)) :
    denote (program >>= f) = Measure.bind (denote program) fun x => denote (f x) := by
  induction program with
  | pure x => simpa using (Measure.dirac_bind hf x).symm
  | lift_bind a cont ih =>
      change Measure.bind (IsMeasureSpec.toMeasure a) (fun b => denote (cont b >>= f))
          = Measure.bind (Measure.bind (IsMeasureSpec.toMeasure a) fun b => denote (cont b))
              fun x => denote (f x)
      rw [Measure.bind_bind (Measurable.of_discrete).aemeasurable hf.aemeasurable]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

/-- `denote` is a monad morphism into the Giry monad, with no side conditions, whenever the
output type is discrete as well as the answer types. -/
theorem denote_bind_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (program : FreeM P α) (f : α → FreeM P β) :
    denote (program >>= f) = Measure.bind (denote program) fun x => denote (f x) :=
  denote_bind program f Measurable.of_discrete

/-! ### Agreement with the `PMF` denotation

For a polynomial interface carrying both interpretations compatibly, the measure denotation is
the measure of the `PMF` denotation. This is what lets a `Pr[…]` statement proved against
`VCVio.EvalDist.PFunctor` be transported here rather than reproved. -/

theorem denote_eq_toMeasure [P.IsProbabilitySpec] [∀ a, Countable (P.B a)] [MeasurableSpace α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) :
    denote program = (program.liftM IsProbabilitySpec.toPMF).toMeasure := by
  induction program with
  | pure x => simpa using (PMF.toMeasure_pure x).symm
  | lift_bind a cont ih =>
      change Measure.bind (IsMeasureSpec.toMeasure a) (fun b => denote (cont b))
          = ((IsProbabilitySpec.toPMF a).bind
              fun u => (cont u).liftM IsProbabilitySpec.toPMF).toMeasure
      rw [PMF.toMeasure_bind, h a]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

end FreeM
end PFunctor
