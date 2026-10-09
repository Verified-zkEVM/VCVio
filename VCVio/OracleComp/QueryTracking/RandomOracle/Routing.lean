/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.EvalDist.Monad.UniformTable

/-!
# Injective input routing for finite random oracles

A polynomial lens may alias distinct oracle inputs. Injective encodings preserve the full
output measure for every adaptive client of an initially empty finite random oracle.
Disjoint encodings supply the corresponding law for two domains sharing a target service.
The structural routing API is universe polymorphic. The measure results use the finite-table
sampling API in `Type 0` and make no claim about arbitrary preloaded caches.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory

namespace OracleComp.RandomOracleRouting

universe u

section Structural

variable {A B R X : Type u}

/-- Route inputs through an encoding while retaining each response unchanged. -/
@[expose]
def lens (encode : A → B) :
    PFunctor.Lens (A →ₒ R).toPFunctor (B →ₒ R).toPFunctor where
  toFunA := encode
  toFunB _ := id

/-- Apply an input encoding at every query of an adaptive client. -/
@[expose]
def route (encode : A → B) (program : OracleComp (A →ₒ R) X) :
    OracleComp (B →ₒ R) X := program.mapLens (lens encode)

/-- Routed table execution equals source execution against the restricted table. -/
theorem evalWithAnswerFn_route (encode : A → B) (program : OracleComp (A →ₒ R) X)
    (table : B → R) :
    evalWithAnswerFn (QueryImpl.ofFn table) (route encode program) =
      evalWithAnswerFn (QueryImpl.ofFn (table ∘ encode)) program := by
  induction program using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind a k ih =>
      change evalWithAnswerFn (QueryImpl.ofFn table)
        (.queryBind (encode a) fun r => route encode (k r)) = _
      exact ih (table (encode a))

end Structural

variable {A B R X : Type}

/-- Injective input routing preserves the full output measure under eager table sampling. -/
theorem evalDist_route_eager [Finite A] [Finite B] [Finite R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R] [MeasurableSpace X]
    [SampleableType (A → R)] [SampleableType (B → R)]
    (encode : A → B) (hinj : Function.Injective encode)
    (program : OracleComp (A →ₒ R) X) :
    𝒟[(fun table => evalWithAnswerFn (QueryImpl.ofFn table) (route encode program))
      <$> ($ᵗ (B → R))] =
    𝒟[(fun table => evalWithAnswerFn (QueryImpl.ofFn table) program) <$> ($ᵗ (A → R))] := by
  have h := evalDist_map_table_comp_injective ($ᵗ (A → R)) ($ᵗ (B → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample hinj
  simp_rw [evalWithAnswerFn_route]
  have hm := congrArg (fun μ : Measure (A → R) =>
    μ.map (fun table => evalWithAnswerFn (QueryImpl.ofFn table) program)) h
  rw [← evalDist_map_of_discrete, ← evalDist_map_of_discrete, Functor.map_map] at hm
  exact hm

/-- Injective input routing preserves the full output measure of an initially empty lazy oracle. -/
theorem evalDist_route_lazy [DecidableEq A] [DecidableEq B]
    [Finite A] [Finite B] [Finite R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R] [MeasurableSpace X]
    [SampleableType R] [SampleableType (A → R)] [SampleableType (B → R)]
    (encode : A → B) (hinj : Function.Injective encode)
    (program : OracleComp (A →ₒ R) X) :
    𝒟[(simulateQ randomOracle (route encode program)).run' ∅] =
      𝒟[(simulateQ randomOracle program).run' ∅] := by
  rw [evalDist_simulateQ_randomOracle_run'_eq_tableExtending,
      evalDist_simulateQ_randomOracle_run'_eq_tableExtending]
  simp only [tableExtending_empty, bind_pure_comp]
  exact evalDist_route_eager encode hinj program

/-- Disjoint injective encodings preserve an adaptive client's two-domain oracle law. -/
theorem evalDist_route_sum {L K B R X : Type}
    [DecidableEq L] [DecidableEq K] [DecidableEq B]
    [Finite L] [Finite K] [Finite B] [Finite R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R] [MeasurableSpace X]
    [SampleableType R] [SampleableType (L ⊕ K → R)] [SampleableType (B → R)]
    (left : L → B) (right : K → B)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hdisjoint : ∀ l k, left l ≠ right k)
    (program : OracleComp (L ⊕ K →ₒ R) X) :
    𝒟[(simulateQ randomOracle (route (Sum.elim left right) program)).run' ∅] =
      𝒟[(simulateQ randomOracle program).run' ∅] :=
  evalDist_route_lazy _ (hleft.sumElim hright hdisjoint) program

end OracleComp.RandomOracleRouting
