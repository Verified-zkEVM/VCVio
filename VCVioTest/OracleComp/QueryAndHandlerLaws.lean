/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio

/-!
# Query-log projections, lift routes and stateful handlers

Projections of sum-interface logs simplify, two lift routes agreeing on queries give one lift,
handlers over two base monads with equal local laws have equal run laws, and an invariant holds on
the final states of a handler over an arbitrary base monad with an exact support.
-/

open OracleComp OracleSpec

namespace VCVioTest.QueryAndHandlerLaws

variable {α σ ι : Type}

example {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} (l : QueryLog spec₁)
    (r : QueryLog (spec₁ + spec₂)) :
    (QueryLog.inl l ++ r).fst = l ++ r.fst ∧ (QueryLog.inl l ++ r).snd = r.snd := by
  simp

example {ι₁ ι₂ ι₃ : Type} {a : OracleSpec ι₁} {b : OracleSpec ι₂} {c : OracleSpec ι₃}
    (p : OracleComp a α) :
    liftComp (liftComp p (a + b)) ((a + b) + c) = liftComp p ((a + b) + c) :=
  liftComp_liftComp (spec₁ := a) (spec₂ := a + b) (spec₃ := (a + b) + c) (fun _ => rfl) p

example {ι₁ ι₂ ι₃ : Type} {a : OracleSpec ι₁} {b : OracleSpec ι₂} {c : OracleSpec ι₃}
    (ha : QueryImpl a ProbComp) (hb : QueryImpl b ProbComp) (hc : QueryImpl c ProbComp)
    (p : OracleComp a α) :
    simulateQ ((ha + hb) + hc) (liftComp p ((a + b) + c)) = simulateQ ha p :=
  simulateQ_add_add_liftComp_left ha hb hc p

example {spec : OracleSpec ι} [MeasurableSpace (α × σ)]
    (impl : QueryImpl spec (StateT σ ProbComp))
    (other : QueryImpl spec (StateT σ (OptionT ProbComp)))
    (hstep : ∀ q s, (impl q).run s =ᵈ (other q).run s) (oa : OracleComp spec α) (s : σ) :
    𝒟[(simulateQ impl oa).run s] = 𝒟[(simulateQ other oa).run s] :=
  evalDist_simulateQ_run_congr impl other hstep oa s

example {spec : OracleSpec ι} {spec' : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (himpl : QueryImpl.PreservesInv impl Inv) (oa : OracleComp spec α) (s : σ) (hs : Inv s)
    (z : α × σ) (hz : z ∈ support ((simulateQ impl oa).run s)) : Inv z.2 :=
  simulateQ_run_preservesInv impl Inv himpl oa s hs z hz

end VCVioTest.QueryAndHandlerLaws
