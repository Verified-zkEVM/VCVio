/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Foxglove.Adequacy
public import Foxglove.Interp.Bernoulli.Split
public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.OracleComp.SimSemantics.Measure
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Foxglove's semantics of `OracleComp` is VCVio's

Foxglove reasons about any monad that compiles to biased coin flips, `BernoulliM`. An
`OracleComp` program compiles by *simulation*: `BernoulliImpl` implements each oracle by coin
flips, and the program runs as `simulateQ` of that implementation. This file shows that the
two semantics agree.

* `lawOf_eq_evalDist`: a coin program's tape law is VCVio's output measure, once each flip has
  its Bernoulli answer measure. `BernoulliM` is a `PFunctor.FreeM`, as `OracleComp` is.
* `LawfulBernoulliImpl`: an implementation is lawful when each query's coin program has the
  answer measure VCVio assigns to the query. `unifSpec` (rejection sampling `split`),
  `coinSpec` (a fair flip) and sums of lawful implementations are lawful.
* `evalDist_interp`, `lawOf_interp`: for a lawful implementation, compiling to coins preserves
  every program's output measure, by `OracleComp.evalDist_simulateQ_eq_of_forall`.
-/

@[expose] public section

namespace Foxglove

open ProbSpace MeasureTheory ProbabilityTheory unitInterval OracleSpec OracleComp Interp
open scoped ENNReal

noncomputable section

/-! ## Coin programs -/

/-- **A flip is a Bernoulli trial.** The answer measure of the coin oracle `Flip r`: `true`
with probability `r`. With it, VCVio's measure semantics `𝒟[·]` applies to `BernoulliM`. -/
instance : PFunctor.AnswerMeasure BernoulliPFunctor where
  toMeasure | .Flip r => (bernoulliWeights r).toMeasure
  isProbabilityMeasure | .Flip _ => inferInstance

@[simp]
lemma toMeasure_flip (r : I) :
    PFunctor.AnswerMeasure.toMeasure (P := BernoulliPFunctor) (.Flip r) =
      (bernoulliWeights r).toMeasure :=
  rfl

/-- A flip is distributed as `bernoulliWeights` under VCVio's measure semantics, as under the
tape semantics (`WP_FLIP`). -/
@[simp]
lemma evalDist_flip (r : I) : 𝒟[Interp.flip r] = (bernoulliWeights r).toMeasure :=
  PFunctor.FreeM.evalDist_lift (P := BernoulliPFunctor) (.Flip r)

/-- **Tape agreement.** The law a coin program's tape run puts on `a` is the mass VCVio's
measure semantics puts on `a`: both fold the program, flip by flip, with the same weights. -/
theorem lawOf_eq_evalDist {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (t : BernoulliM α) (a : α) : ProbTree.lawOf t a = 𝒟[t] {a} := by
  induction t with
  | pure x =>
    rw [ProbTree.lawOf_pure]
    split_ifs with h <;> simp [h, Ne.symm]
  | liftBind op cont ih =>
    -- one flip: both sides weigh the two continuations by the flip's law
    rcases op with ⟨r⟩
    rw [ProbTree.lawOf_liftBind,
      PFunctor.FreeM.evalDist_liftBind _ cont Measurable.of_discrete.aemeasurable,
      Measure.bind_apply (measurableSet_singleton a) Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool]
    simp [ih, ProbTree.flipWeight_eq_bernoulliWeights, mul_comm]

/-- The tape law `lawPMF`, as a measure, is VCVio's output measure. -/
theorem toMeasure_lawPMF {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (t : BernoulliM α) : (lawPMF t).toMeasure = 𝒟[t] :=
  Measure.ext_of_singleton fun a ↦ by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), lawPMF_apply,
      lawOf_eq_evalDist]

/-! ## Compiling `OracleComp` to coins -/

/-- **A coin-flip implementation of an oracle specification.** An `OracleComp` program
compiles to `BernoulliM` by simulating each query with `impl`. -/
class BernoulliImpl {ι : Type} (oSpec : OracleSpec ι) where
  /-- The coin program answering each query. -/
  impl : QueryImpl oSpec BernoulliM

/-- `OracleComp` programs compile to coins by `simulateQ`, a monad morphism. -/
instance {ι : Type} {oSpec : OracleSpec ι} [BernoulliImpl oSpec] :
    LawfulBernoulliInterpretable (OracleComp oSpec) where
  interp oa := simulateQ BernoulliImpl.impl oa
  interp_pure _ := rfl
  interp_bind oa f := simulateQ_bind _ oa f

@[simp]
lemma interp_eq_simulateQ {ι α : Type} {oSpec : OracleSpec ι} [BernoulliImpl oSpec]
    (oa : OracleComp oSpec α) :
    BernoulliInterpretable.interp oa = simulateQ BernoulliImpl.impl oa :=
  rfl

/-- The uniform oracle, by rejection sampling. -/
instance : BernoulliImpl unifSpec := ⟨fun n ↦ split n⟩

/-- The fair-coin oracle, by a fair flip. -/
instance : BernoulliImpl coinSpec := ⟨fun _ ↦ Interp.flip half⟩

/-- A sum of specifications, by the summands' implementations. -/
instance {ι₁ ι₂ : Type} {oSpec₁ : OracleSpec ι₁} {oSpec₂ : OracleSpec ι₂}
    [BernoulliImpl oSpec₁] [BernoulliImpl oSpec₂] : BernoulliImpl (oSpec₁ + oSpec₂) :=
  ⟨QueryImpl.add BernoulliImpl.impl BernoulliImpl.impl⟩

/-! ## Lawful implementations -/

/-- **A lawful implementation** gives each query the answer measure VCVio assigns to it.
Answers carry the discrete σ-algebra `⊤`, as in `OracleSpec.AnswerMeasure`. -/
class LawfulBernoulliImpl {ι : Type} (oSpec : OracleSpec ι) [BernoulliImpl oSpec]
    [oSpec.AnswerMeasure] : Prop where
  evalDist_impl (t : oSpec.Domain) :
    @evalDist BernoulliM _ (oSpec.Range t) ⊤ (BernoulliImpl.impl t) = AnswerMeasure.toMeasure t

/-- Sums of lawful implementations are lawful (`OracleSpec.AnswerMeasure.add`). -/
instance {ι₁ ι₂ : Type} {oSpec₁ : OracleSpec ι₁} {oSpec₂ : OracleSpec ι₂}
    [BernoulliImpl oSpec₁] [BernoulliImpl oSpec₂] [oSpec₁.AnswerMeasure] [oSpec₂.AnswerMeasure]
    [LawfulBernoulliImpl oSpec₁] [LawfulBernoulliImpl oSpec₂] :
    LawfulBernoulliImpl (oSpec₁ + oSpec₂) where
  evalDist_impl
    | .inl t => LawfulBernoulliImpl.evalDist_impl (oSpec := oSpec₁) t
    | .inr t => LawfulBernoulliImpl.evalDist_impl (oSpec := oSpec₂) t

section Agreement

variable {ι α : Type} {oSpec : OracleSpec ι} [BernoulliImpl oSpec] [oSpec.AnswerMeasure]
  [LawfulBernoulliImpl oSpec]

/-- **Compiling to coins preserves the output measure** of every program. -/
@[simp]
theorem evalDist_interp [MeasurableSpace α] (oa : OracleComp oSpec α) :
    𝒟[BernoulliInterpretable.interp oa] = 𝒟[oa] :=
  evalDist_simulateQ_eq_of_forall _ LawfulBernoulliImpl.evalDist_impl oa

/-- **Foxglove's law of a program is VCVio's.** -/
theorem lawOf_interp [MeasurableSpace α] [MeasurableSingletonClass α] (oa : OracleComp oSpec α)
    (a : α) : ProbTree.lawOf (BernoulliInterpretable.interp oa) a = 𝒟[oa] {a} := by
  rw [lawOf_eq_evalDist, evalDist_interp]

/-- `lawOf_interp` in VCVio's event notation. -/
theorem lawOf_interp_eq_prEvent (oa : OracleComp oSpec α) (a : α) :
    ProbTree.lawOf (BernoulliInterpretable.interp oa) a = Pr{let x ← oa}[x = a] := by
  let : MeasurableSpace α := ⊤
  rw [lawOf_interp, prEvent_eq_evalDist_singleton]

/-- The compiled program's tape law is VCVio's output measure. -/
theorem toMeasure_lawPMF_interp [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (oa : OracleComp oSpec α) : (lawPMF (BernoulliInterpretable.interp oa)).toMeasure = 𝒟[oa] := by
  rw [toMeasure_lawPMF, evalDist_interp]

end Agreement

/-! ## The uniform and fair-coin oracles are lawful -/

/-- **`split n` has VCVio's uniform measure.** -/
lemma evalDist_split (n : ℕ) : 𝒟[split n] = uniformOn (Set.univ : Set (Fin (n + 1))) :=
  Measure.ext_of_singleton fun i ↦ by simp [← lawOf_eq_evalDist, lawOf_split, uniformOn_univ]

instance : LawfulBernoulliImpl unifSpec :=
  ⟨fun n ↦ (evalDist_split n).trans (AnswerMeasure.toMeasure_eq_uniformOn n).symm⟩

instance : LawfulBernoulliImpl coinSpec := ⟨fun _ ↦ by
  change 𝒟[Interp.flip half] = _
  rw [evalDist_flip, AnswerMeasure.toMeasure_eq_uniformOn]
  refine Measure.ext_of_singleton fun b ↦ ?_
  have hcount : Measure.count ({false, true} : Set Bool) = 2 := by
    rw [show ({false, true} : Set Bool) = Set.univ from Set.eq_univ_of_forall fun b ↦ by
      cases b <;> simp, Measure.count_univ]
    simp
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), bernoulliWeights_apply]
  cases b <;> simp [uniformOn, cond_apply, hcount, Helper.halfNN_coe, ENNReal.one_sub_inv_two]⟩

end

end Foxglove
