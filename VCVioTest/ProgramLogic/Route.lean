/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio
public meta import VCVio.ProgramLogic.Tactics.Route

/-!
# Routes of program-logic goals

One check per row of the route table of `VCVio.ProgramLogic.Tactics.Common.Route`, and
regressions for goals the `find?`-based classifiers misroute: a triple among the premises, and
triples over a `Prop` carrier.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal

namespace VCVioTest.ProgramLogic.Route

/-! ## Names -/

-- every constant the classifier names exists
example : List Lean.Name := [``Std.WP.Triple, ``Std.WP.WP.wp, ``Std.WP.WPMonad.toWP, ``Lean.Order.PartialOrder.rel,
  ``OracleComp.ProgramLogic.Triple, ``OracleComp.ProgramLogic.wp,
  ``OracleComp.ProgramLogic.Relational.RelTriple, ``VCVio.ProgramLogic.RelTriple,
  ``OracleComp.ProgramLogic.Relational.RelWP, ``OracleComp.ProgramLogic.Relational.CouplingPost,
  ``OracleComp.ProgramLogic.Relational.ApproxRelTriple, ``OracleComp.ProgramLogic.Relational.eRelWP,
  ``EvalDistEq, ``OracleComp.IsQueryBound, ``OracleComp.IsTotalQueryBound,
  ``PFunctor.FreeM.IsRollBound, ``PFunctor.FreeM.IsTotalRollBound, ``prEvent, ``evalDist,
  ``measureETVDist, ``MonadAttach.support, ``OracleComp.Lower.instWP,
  ``OracleComp.Necessary.instWP, ``OracleComp.Probabilistic.instWP_prob,
  ``ExpectationWP.Lower.instWP, ``MonadAttach.toWPMonadDemonic, ``MonadAttach.toWPMonadAngelic,
  ``ExactWPMonad.dual, ``simulateQ]

/-! ## Events, by reading -/

#guard_route ∀ (oa : ProbComp Bool), Pr{let b ← oa}[b = true] = 1 => "necessary"
#guard_route ∀ (oa : ProbComp Bool), 0 < Pr{let b ← oa}[b = true] => "possible"
#guard_route ∀ (oa : ProbComp Bool), Pr{let b ← oa}[b = true] ≠ 0 => "possible"
#guard_route ∀ (oa : ProbComp Bool), (2⁻¹ : ℝ≥0∞) ≤ Pr{let b ← oa}[b = true] => "lower"
#guard_route ∀ (oa : ProbComp Bool), Pr{let b ← oa}[b = true] ≥ (2⁻¹ : ℝ≥0∞) => "lower"
#guard_route ∀ (oa : ProbComp Bool), Pr{let b ← oa}[b = true] ≤ 2⁻¹ => "upper"
#guard_route ∀ (oa : ProbComp Bool), Pr{let b ← oa}[b = true] = 0 => "upper"
#guard_route ∀ (oa : ProbComp Bool), Pr{let b ← oa}[b = true] = 2⁻¹ => "lowerUpper"
#guard_route ∀ (oa : ProbComp Bool), 𝒟[oa] {true} = 2⁻¹ => "lowerUpper"

/-! ## Independence (Foxglove) -/

#guard_route ∀ (f : Bool → ProbComp Bool),
    𝒟[do let b ← ($ᵗ Bool); let b' ← f b; return decide (b = b')] {true} = 2⁻¹ => "lowerUpper+fox"
#guard_route ∀ (oa : ProbComp (Bool × Bool)), Pr{let x ← oa}[x.1 = x.2] = 2⁻¹ => "lowerUpper+fox"

/-! ## Conjunctions, support conclusions, raw `wp` bounds -/

#guard_route ∀ (oa : ProbComp Bool), (2⁻¹ : ℝ≥0∞) ≤ Pr{let b ← oa}[b = true] ∧ True => "lower"
#guard_route ∀ (oa : ProbComp Bool), true ∈ support oa => "possible"
#guard_route ∀ (oa : ProbComp Bool), wp oa (fun b ↦ propInd (b = true)) ≤ 2⁻¹ => "upper"

-- an equation of programs in a generic monad, through a handler
#guard_route ∀ {m : Type → Type} [Monad m] (impl : QueryImpl unifSpec m) (oc : OracleComp unifSpec Bool),
    simulateQ impl oc = simulateQ impl oc => "handler"

/-! ## Relational -/

#guard_route ∀ (oa ob : ProbComp Bool), Pr{let b ← oa}[b = true] = Pr{let b ← ob}[b = true] => "relational"
#guard_route ∀ (oa ob : ProbComp Bool), 𝒟[oa] = 𝒟[ob] => "relational"
#guard_route ∀ (oa ob : ProbComp Bool), oa =ᵈ ob => "relational"
#guard_route ∀ (oa ob : ProbComp Bool), Relational.RelTriple oa ob (fun a b ↦ a = b) => "relational"
#guard_route ∀ (oa ob : ProbComp Bool), Relational.ApproxRelTriple (2⁻¹) oa ob (fun a b ↦ a = b) => "eRHL"
#guard_route ∀ (oa ob : ProbComp Bool), measureETVDist oa ob ≤ 2⁻¹ => "upToBad"

/-! ## Triples, by carrier and interpretation -/

#guard_route ∀ (oa : ProbComp Bool), Triple 1 oa (fun b ↦ propInd (b = true)) => "vcTriple"

section
open scoped OracleComp.Necessary Std.WP
#guard_route ∀ (oa : ProbComp Bool), ⦃ True ⦄ oa ⦃ fun b ↦ b = true ⦄ => "core:necessary"
end

section
open scoped OracleComp.Lower Std.WP
#guard_route ∀ (oa : ProbComp Bool), ⦃ (1 : ℝ≥0∞) ⦄ oa ⦃ fun b ↦ propInd (b = true) ⦄ => "core:lower"
end

/-! ## Handlers and query bounds -/

#guard_route ∀ (impl : QueryImpl unifSpec ProbComp) (oc : OracleComp unifSpec Bool),
    simulateQ impl oc = simulateQ impl oc => "handler"
#guard_route ∀ oc : OracleComp unifSpec Bool, IsTotalQueryBound oc 3 => "queryBound"

/-! ## Regressions: premises -/

-- a triple among the premises does not make the goal a triple goal
#guard_route ∀ (oa : ProbComp Bool), Triple 1 oa (fun b ↦ propInd (b = true)) →
    (2⁻¹ : ℝ≥0∞) ≤ Pr{let b ← oa}[b = true] => "lower"

-- a support premise with a plain conclusion is a necessary-reading invariant
#guard_route ∀ (oa : ProbComp Bool), ∀ b ∈ support oa, b = true => "necessary"
#guard_route ∀ (impl : QueryImpl unifSpec ProbComp) (oc : OracleComp unifSpec Bool),
    ∀ b ∈ support (simulateQ impl oc), b = true => "necessary"

-- other equations of programs are program algebra
#guard_route ∀ (oa : ProbComp Bool), (oa >>= pure) = oa => "progAlgebra"

-- statements outside the program logic have no route
#guard_route (1 : ℕ) + 1 = 2 => "none"

end VCVioTest.ProgramLogic.Route
