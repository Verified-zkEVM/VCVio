/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.Quantitative
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Native relational oracle algebra canaries

The qualitative measure coupling algebra supports the generic relational interface, including
uncountable output types and weighted zero-mass branches. It requires no discrete backend.
-/

public section

open OracleSpec OracleComp
open OracleComp.ProgramLogic.Relational

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native relational oracle algebra unexpectedly imports {name}"

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

/-- A finite oracle whose true branch is operationally possible but has zero mass. -/
abbrev weightedSpec : OracleSpec (Fin 1) := Fin 1 →ₒ Bool

noncomputable local instance : IsMeasureSpec weightedSpec where
  toMeasure _ := MeasureTheory.Measure.dirac false
  isProbabilityMeasure _ := inferInstance

example : MAlgRelOrdered.RelWP (weightedSpec.query 0 : OracleComp weightedSpec Bool)
    (pure false : OracleComp weightedSpec Bool) (· = ·) := by
  simp only [relWP_iff_couplingPost, CouplingPost, MeasureProgramLogic.RelWP,
    OracleComp.evalDist_liftM_query, evalDist_pure, IsMeasureSpec.toMeasure,
    PFunctor.IsMeasureSpec.toMeasure]
  exact MeasureProgramLogic.couplingPost_refl (MeasureTheory.Measure.dirac false)

/-- The zero-mass reachable answer `true` does not obstruct the coupling, so the anchoring rules
relating couplings to structural support need uniform response measures. -/
example : RelTriple (pure false : OracleComp weightedSpec Bool)
      (weightedSpec.query 0 : OracleComp weightedSpec Bool) (· = ·) ∧
    true ∈ support (weightedSpec.query 0 : OracleComp weightedSpec Bool) := by
  refine ⟨fun _ ↦ ?_, by simp⟩
  have h : MAlgRelOrdered.RelWP (weightedSpec.query 0 : OracleComp weightedSpec Bool)
      (pure false : OracleComp weightedSpec Bool) (· = ·) := by
    simp only [relWP_iff_couplingPost, CouplingPost, MeasureProgramLogic.RelWP,
      OracleComp.evalDist_liftM_query, evalDist_pure, IsMeasureSpec.toMeasure,
      PFunctor.IsMeasureSpec.toMeasure]
    exact MeasureProgramLogic.couplingPost_refl (MeasureTheory.Measure.dirac false)
  exact relTriple_iff_relWP.1 (relTriple_post_mono (relTriple_symm (relTriple_iff_relWP.2 h))
    fun _ _ h ↦ h.symm)

/-- A pure side anchors the coupled expectation to the unary expectation, which gives the
zero-mass reachable answer no weight. -/
example (post : Bool → Bool → ENNReal) :
    eRelWP (pure false : OracleComp weightedSpec Bool)
        (weightedSpec.query 0 : OracleComp weightedSpec Bool) post =
      OracleComp.ProgramLogic.wp (weightedSpec.query 0 : OracleComp weightedSpec Bool)
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
