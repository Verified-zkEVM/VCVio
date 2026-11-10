/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.OracleComp.Coercions.SubSpec.Routing
public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Query-log projections, lift routes and stateful handlers

Projections of sum-interface logs simplify, two lift routes agreeing on queries give one lift,
handlers over two base monads with equal local laws have equal run laws, and an invariant holds on
the final states of a handler over an arbitrary lawful attached base monad.
-/

open OracleComp OracleSpec

namespace VCVioTest.QueryAndHandlerLaws

variable {α σ ι : Type}

example {ι₁ ι₂ ι₃ : Type} {a : OracleSpec ι₁} {b : OracleSpec ι₂} {c : OracleSpec ι₃}
    (p : OracleComp a α) :
    liftComp (liftComp p (a + b)) ((a + b) + c) = liftComp p ((a + b) + c) :=
  liftComp_liftComp (spec₁ := a) (spec₂ := a + b) (spec₃ := (a + b) + c) (fun _ => rfl) p

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

/-- Incrementing a counter before an optional draw preserves positivity, including under
handler sums, composition, and a passive log extension. No probability interpretation of the
forwarded interface is required. -/
example (draw : OptionT ProbComp Bool) {spec : OracleSpec ι}
    (forward : QueryImpl spec (OracleComp (coinSpec + coinSpec))) :
    let bump : QueryImpl coinSpec (StateT ℕ (OptionT ProbComp)) := fun _ => do
      let n ← get
      set (n + 1)
      monadLift draw
    let idle : QueryImpl coinSpec (StateT ℕ (OptionT ProbComp)) := fun _ => pure false
    QueryImpl.PreservesInv
      ((bump + idle).extendState (fun _ _ _ _ (count : ℕ) => count + 1) ∘ₛ forward)
      (fun state => 0 < state.1) := by
  dsimp only
  apply QueryImpl.PreservesInv.compose
  apply QueryImpl.PreservesInv.extendState
  apply QueryImpl.PreservesInv.add
  · intro q
    apply StateT.preservesInv_get_bind
    intro n hn
    exact StateT.preservesInv_bind
      (set (n + 1) : StateT ℕ (OptionT ProbComp) PUnit)
      (fun _ => monadLift draw) (0 < ·)
      (StateT.preservesInv_set_of _ (by omega))
      (fun _ => StateT.preservesInv_monadLift draw _)
  · intro q
    exact StateT.preservesInv_pure false _

end VCVioTest.QueryAndHandlerLaws
