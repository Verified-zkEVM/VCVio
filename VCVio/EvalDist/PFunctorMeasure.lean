/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.ProbabilityMassFunction.Measure
public import VCVio.EvalDist.PFunctor
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

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
* `PFunctor.FreeM.isProbabilityMeasure_denote` — discrete programs denote probability measures.
* `PFunctor.FreeM.denote_eq_toMeasure` — agreement with the `PMF` denotation of
  `VCVio.EvalDist.PFunctor`.
* `PFunctor.FreeM.denote_apply_setOf` — existing `Pr[...]` facts are measurable-event facts.
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

/-- A one-operation program is a probability measure whenever its continuation is an
almost-everywhere measurable family of probability measures.

This is the continuous composition boundary. For discrete answer types the hypotheses are
automatic; for a genuinely continuous oracle they are precisely the obligations represented by
a Mathlib `Kernel`. -/
theorem isProbabilityMeasure_denote_liftBind [MeasurableSpace α] (a : P.A)
    (cont : P.B a → FreeM P α)
    (hMeasurable : AEMeasurable (fun b => denote (cont b)) (IsMeasureSpec.toMeasure a))
    (hProbability : ∀ᵐ b ∂IsMeasureSpec.toMeasure a,
      IsProbabilityMeasure (denote (cont b))) :
    IsProbabilityMeasure (denote (FreeM.liftBind a cont)) :=
  MeasureTheory.isProbabilityMeasure_bind hMeasurable hProbability

/-- Every free program denotes a subprobability measure, even before a measurability invariant is
available for its continuations. `Measure.bind_apply_le` gives exactly the one-sided bound needed
here; measurability is only needed to strengthen this to a probability-measure equality. -/
theorem denote_apply_univ_le_one [MeasurableSpace α] (program : FreeM P α) :
    denote program Set.univ ≤ 1 := by
  induction program with
  | pure _ => simp
  | lift_bind a cont ih =>
      refine (Measure.bind_apply_le _ MeasurableSet.univ).trans ?_
      calc
        (∫⁻ b, denote (cont b) Set.univ ∂IsMeasureSpec.toMeasure a) ≤
            ∫⁻ _b, 1 ∂IsMeasureSpec.toMeasure a := lintegral_mono ih
        _ = 1 := by simp

/-- The direct free-monad fold supplies the primary measure semantics whenever an
`IsMeasureSpec` is available. Its priority is above the generic finite-distribution adapter, so
installing a measure specification makes `𝒟[…]` unfold to `denote`; computations that only have
the legacy probability specification continue to use the adapter. -/
noncomputable instance (priority := 20) instEvalDistSemanticsFreeM :
    EvalDistSemantics (FreeM P) where
  denote := denote
  apply_univ_le_one := denote_apply_univ_le_one

/-- With a measure specification in scope, primary notation is definitionally the direct
free-monad measure fold. -/
@[simp]
theorem evalDist_eq_denote [MeasurableSpace α] (program : FreeM P α) :
    𝒟[program] = denote program := rfl

/-! ### The monad-morphism laws

`denote` sends `pure` to `dirac` definitionally. For `bind` it must know that the continuation
is measurable, in two places: at the output type, and at each operation's answer type. The
general statement carries the first as a hypothesis; discreteness of the answer types
discharges the second, and `denote_bind_of_discrete` discharges both. -/

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Every program over discrete answer types denotes a probability measure.

This theorem is deliberately stated as a theorem rather than a global instance: a program with a
continuous answer type needs a measurability argument for each continuation, and typeclass search
must not hide that boundary. -/
theorem isProbabilityMeasure_denote [MeasurableSpace α] (program : FreeM P α) :
    IsProbabilityMeasure (denote program) := by
  induction program with
  | pure _ => exact ⟨by simp⟩
  | lift_bind a cont ih =>
      exact isProbabilityMeasure_denote_liftBind a cont
        Measurable.of_discrete.aemeasurable
        (Filter.Eventually.of_forall ih)

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

/-- Over a discrete-answer interface, the direct measure semantics satisfies the Giry monad
laws. -/
noncomputable instance (priority := 20) instLawfulEvalDistSemanticsFreeM :
    LawfulEvalDistSemantics (FreeM P) where
  denote_pure := denote_pure
  denote_bind := denote_bind

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

/-- Every `PMF`-valued interpretation induces a measure-valued one, by taking the measure of
each answer distribution.

Deliberately not an instance, matching `PFunctor.IsUniformSpec.ofFintypeInhabited`: measure
semantics stay an explicit opt-in rather than being derived silently wherever a `PMF`
interpretation happens to be in scope. Introduce it with `letI` at a use site; the agreement
hypothesis of `denote_eq_toMeasure` then holds by `rfl`. -/
@[instance_reducible]
noncomputable def _root_.PFunctor.IsProbabilitySpec.toMeasureSpec (P : PFunctor.{uA, u})
    [∀ a, MeasurableSpace (P.B a)] [P.IsProbabilitySpec] : P.IsMeasureSpec where
  toMeasure a := (IsProbabilitySpec.toPMF a).toMeasure
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

/-- The measure of a singleton is the output probability.

This is the bridge that lets an existing `Pr[= x | _]` result be read off the measure
denotation instead of reproved against it. -/
theorem denote_apply_singleton [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (x : α) :
    denote program {x} = Pr[= x | program] := by
  rw [denote_eq_toMeasure h program,
    PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x)]
  rw [probOutput_def]
  exact (SPMF.liftM_apply _ x).symm

/-- The primary measure notation assigns the existing point probability to a singleton whenever
the measure and probability query specifications agree. -/
theorem evalDist_apply_singleton [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (x : α) :
    𝒟[program] {x} = Pr[= x | program] :=
  denote_apply_singleton h program x

/-- The measure denotation of a measurable predicate is the existing `Pr[...]` value.

The result keeps predicate notation convenient for discrete cryptographic proofs while presenting
the semantics to Mathlib as an ordinary measurable event. -/
theorem denote_apply_setOf [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (p : α → Prop) (hp : MeasurableSet {x | p x}) :
    denote program {x | p x} = Pr[p | program] := by
  rw [denote_eq_toMeasure h program,
    (program.liftM IsProbabilitySpec.toPMF).toMeasure_apply hp,
    probEvent_eq_tsum_indicator]
  apply tsum_congr
  intro x
  by_cases hx : p x
  · simp only [Set.indicator, Set.mem_ofPred_eq, hx, ↓reduceIte]
    rw [probOutput_def]
    exact (SPMF.liftM_apply _ x).symm
  · simp [Set.indicator, hx]

/-- The primary measure notation assigns the existing predicate probability to any measurable
event whenever the measure and probability query specifications agree. -/
theorem evalDist_apply_setOf [P.IsProbabilitySpec] [∀ a, Countable (P.B a)]
    [MeasurableSpace α]
    (h : ∀ a : P.A, IsMeasureSpec.toMeasure a = (IsProbabilitySpec.toPMF a).toMeasure)
    (program : FreeM P α) (p : α → Prop) (hp : MeasurableSet {x | p x}) :
    𝒟[program] {x | p x} = Pr[p | program] :=
  denote_apply_setOf h program p hp

end FreeM
end PFunctor
