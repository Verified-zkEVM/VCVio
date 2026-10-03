/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.Quantitative
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Relational oracle algebra canaries

The qualitative measure coupling algebra supports the generic relational interface, including
uncountable output types and weighted zero-mass branches. It requires no discrete backend.
-/

public section

open OracleSpec OracleComp
open OracleComp.ProgramLogic.Relational

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PMF then
    throwError "relational oracle algebra unexpectedly imports PMF"

namespace VCVioTest.ProgramLogic.MeasureOracleRelWP

example (a b : ℝ) (R : ℝ → ℝ → Prop) :
    MAlgRelOrdered.RelWP (pure a : ProbComp ℝ) (pure b : ProbComp ℝ) R ↔ R a b := by
  simp

example (mx : ProbComp ℝ) : MAlgRelOrdered.RelWP mx mx (· = ·) := by simp

example (mx : ProbComp ℝ) : CouplingPost mx mx (· = ·) := by simp

example (mx my : ProbComp ℝ) (f g : ℝ → ProbComp ℝ) (R : ℝ → ℝ → Prop)
    (h : MAlgRelOrdered.RelWP mx my fun a b ↦ MAlgRelOrdered.RelWP (f a) (g b) R) :
    MAlgRelOrdered.RelWP (mx >>= f) (my >>= g) R :=
  MAlgRelOrdered.relWP_bind_le mx my f g R h

/-- Equality couplings of real-valued computations identify every event probability. -/
example (mx my : ProbComp ℝ) (h : RelTriple mx my (EqRel ℝ)) (p : ℝ → Prop) :
    Pr{let x ← mx}[p x] = Pr{let y ← my}[p y] :=
  prEvent_eq_of_relTriple_eqRel h p

/-- An implication along a coupling bounds one real-valued event by another. -/
example (mx : ProbComp ℝ) (p q : ℝ → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let y ← mx}[q y] :=
  prEvent_le_of_relTriple (relTriple_refl mx) fun _ _ h hp ↦ h ▸ hpq _ hp

/-- Pure real-valued computations have their post-expectation as coupled expectation. -/
example (a b : ℝ) (g : ℝ → ℝ → ENNReal) :
    eRelWP (pure a : ProbComp ℝ) (pure b : ProbComp ℝ) g = g a b :=
  eRelWP_pure a b g

/-- Coupled expectations of real-valued computations compose through bind. -/
example (mx my : ProbComp ℝ) (f g : ℝ → ProbComp ℝ) (post : ℝ → ℝ → ENNReal) :
    eRelWP mx my (fun a b => eRelWP (f a) (g b) post) ≤ eRelWP (mx >>= f) (my >>= g) post :=
  eRelWP_bind_le mx my f g post

/-- Total variation between real-valued outputs is the complement of the best coupled
probability of equal outputs, with no measurable structure chosen on the outputs. -/
example (mx my : ProbComp ℝ) :
    etvDist mx my = 1 - eRelWP mx my (RelPost.indicator (EqRel ℝ)) :=
  etvDist_eq_one_sub_eRelWP_eqRel mx my

/-- A total variation bound on real-valued outputs is an approximate equality coupling. -/
example (mx my : ProbComp ℝ) (ε : ENNReal) (h : etvDist mx my ≤ ε) :
    ApproxRelTriple ε mx my (EqRel ℝ) :=
  approxRelTriple_eqRel_iff_etvDist_le.2 h

/-- A finite oracle whose true branch is operationally possible but has zero mass. -/
abbrev weightedSpec : OracleSpec (Fin 1) := Fin 1 →ₒ Bool

noncomputable local instance : AnswerMeasure weightedSpec where
  toMeasure _ := MeasureTheory.Measure.dirac false
  isProbabilityMeasure _ := inferInstance

example : MAlgRelOrdered.RelWP (weightedSpec.query 0 : OracleComp weightedSpec Bool)
    (pure false : OracleComp weightedSpec Bool) (· = ·) := by
  simp only [relWP_iff_couplingPost, CouplingPost, ExpectationWP.RelWP,
    OracleComp.evalDist_liftM_query, MeasureTheory.trim_eq_self, evalDist_pure,
    AnswerMeasure.toMeasure, PFunctor.AnswerMeasure.toMeasure]
  exact ExpectationWP.couplingPost_refl (MeasureTheory.Measure.dirac false)

/-- The possible answer `true` has mass zero and does not obstruct the coupling, so the anchoring
rules relating couplings to the support need uniform answer measures. -/
example : RelTriple (pure false : OracleComp weightedSpec Bool)
      (weightedSpec.query 0 : OracleComp weightedSpec Bool) (· = ·) ∧
    true ∈ support (weightedSpec.query 0 : OracleComp weightedSpec Bool) := by
  refine ⟨fun _ ↦ ?_, by simp⟩
  have h : MAlgRelOrdered.RelWP (weightedSpec.query 0 : OracleComp weightedSpec Bool)
      (pure false : OracleComp weightedSpec Bool) (· = ·) := by
    simp only [relWP_iff_couplingPost, CouplingPost, ExpectationWP.RelWP,
      OracleComp.evalDist_liftM_query, MeasureTheory.trim_eq_self, evalDist_pure,
      AnswerMeasure.toMeasure, PFunctor.AnswerMeasure.toMeasure]
    exact ExpectationWP.couplingPost_refl (MeasureTheory.Measure.dirac false)
  exact relTriple_iff_relWP.1 (relTriple_post_mono (relTriple_symm (relTriple_iff_relWP.2 h))
    fun _ _ h ↦ h.symm)

/-- A pure side anchors the coupled expectation to the unary expectation, which gives the
possible answer of mass zero no weight. -/
example (post : Bool → Bool → ENNReal) :
    eRelWP (pure false : OracleComp weightedSpec Bool)
        (weightedSpec.query 0 : OracleComp weightedSpec Bool) post =
      wp⟦(weightedSpec.query 0 : OracleComp weightedSpec Bool)⟧
        (post false) :=
  eRelWP_pure_left false _ post

example (a b : ℝ) (R : ℝ → ℝ → Prop) :
    MAlgRelOrdered.RelWP (pure a : OracleComp weightedSpec ℝ)
      (pure b : OracleComp weightedSpec ℝ) R ↔ R a b := by
  simp

example (mx my : OracleComp weightedSpec ℝ)
    (f g : ℝ → OracleComp weightedSpec ℝ) (R : ℝ → ℝ → Prop)
    (h : MAlgRelOrdered.RelWP mx my fun a b ↦ MAlgRelOrdered.RelWP (f a) (g b) R) :
    MAlgRelOrdered.RelWP (mx >>= f) (my >>= g) R :=
  MAlgRelOrdered.relWP_bind_le mx my f g R h

end VCVioTest.ProgramLogic.MeasureOracleRelWP
