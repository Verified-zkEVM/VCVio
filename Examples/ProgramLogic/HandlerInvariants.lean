/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Handler invariants and ranked potentials

A simulation `simulateQ handler oa` runs an oracle computation `oa` against a stateful handler.
Its program logic is a statement about the handler's state: an invariant every query preserves
(`Spec.simulateQ`, the rule `vcgen` applies when the `invariants` clause supplies the invariant),
or, under the upper-bound reading, a potential that each query may spend one unit of
(`simulateQ_triple_ranked`, applied by hand since its budget is a proof-side fact).

* a flag that stays raised: an invariant of the necessary reading, through `prvcgen`;
* a lazily sampled random oracle whose fresh answers land in a target set with probability at
  most `q * |T| / |R|` over `q` adaptive queries: a union bound as a ranked potential;
* a triple read against the support of the run (`triple_stateT_iff_forall_support`).
-/

public section

open OracleSpec OracleComp Std.WP ENNReal OrderDual OracleComp.ProgramLogic

namespace Examples.ProgramLogic.HandlerInvariants

/-- A handler that samples a coin and raises its flag on heads. -/
def flagHandler : QueryImpl (Unit →ₒ Bool) (StateT Bool ProbComp) := fun _ => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let s ← get
  set (s || b)
  return b

/-- A raised flag stays raised through any computation: the invariant is passed to `vcgen`
through `prvcgen`, which continues into the handler's body at each query. -/
example {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) :
    ⦃ fun s => s = true ⦄ (simulateQ flagHandler oa : StateT Bool ProbComp α)
      ⦃ fun _ s => s = true ⦄ := by
  prvcgen [flagHandler] invariants
    · fun s => s = true
  simp_all

section RankedPotential

open scoped OracleComp.Upper

variable {D R : Type} [DecidableEq D] [SampleableType R] [Fintype R] [DecidableEq R]

/-- A lazily sampled random oracle that records whether a fresh answer lands in `T`. -/
def hitOracle (T : Finset R) : QueryImpl (D →ₒ R) (StateT ((D → Option R) × Bool) ProbComp) :=
  fun t => do
    let st ← get
    match st.1 t with
    | some u => pure u
    | none => do
      let u ← ($ᵗ R : ProbComp R)
      set (Function.update st.1 t (some u), st.2 || decide (u ∈ T))
      pure u

/-- The potential: the flag's indicator plus the budget of `k` remaining queries. -/
noncomputable def potential (T : Finset R) (k : ℕ) (st : (D → Option R) × Bool) : ℝ≥0∞ᵒᵈ :=
  toDual (propInd (st.2 = true) + k * (T.card / Fintype.card R))

/-- Averaging a flag update over a finite uniform draw: the union bound's one step. -/
theorem avg_or_le {β : Type} [Fintype β] [Nonempty β] (P : β → Prop) [DecidablePred P]
    (b : Bool) (c : ℝ≥0∞) :
    (∑ x, (propInd ((b || decide (P x)) = true) + c)) / (Fintype.card β : ℝ≥0∞) ≤
      propInd (b = true) + ((Finset.univ.filter P).card / (Fintype.card β : ℝ≥0∞) + c) := by
  have hc0 : (Fintype.card β : ℝ≥0∞) ≠ 0 := by simp
  have hct : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := by simp
  rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm, ENNReal.mul_div_cancel_right hc0 hct, ← add_assoc]
  gcongr
  cases b
  · simp [propInd_eq_ite]
  · simp [propInd_eq_ite, ENNReal.div_self hc0 hct]

/-- One query spends one unit of the budget: a cache hit keeps the potential, a fresh answer
averages the flag update. -/
theorem hitOracle_step [Nonempty R] (T : Finset R) (t : D) (k : ℕ) :
    ⦃ potential T (k + 1) ⦄ hitOracle (D := D) T t ⦃ fun _ => potential T k ⦄ := by
  unfold hitOracle potential
  vcgen [OracleComp.Upper.Spec.uniformSample_avg]
  · simp only [upper_readback]
    gcongr
    simp
  · simp only [upper_readback, StateT.wp_apply_eq, StateT.run_bind, StateT.run_set,
      StateT.run_pure, ExactWPMonad.wp_bind, ExactWPMonad.wp_pure]
    refine (avg_or_le (· ∈ T) _ _).trans_eq ?_
    simp [add_mul, add_comm]

/-- `q` adaptive queries: the fresh answers land in `T` with probability at most
`q * |T| / |R|`. The whole-program lift spends the budget one query at a time. -/
theorem hitOracle_run_le [Nonempty R] (T : Finset R) {α : Type} (adv : OracleComp (D →ₒ R) α)
    (q : ℕ) (hq : adv.IsTotalQueryBound q) :
    Pr{let z ← (simulateQ (hitOracle T) adv).run (fun _ => none, false)}[z.2.2 = true] ≤
      q * (T.card / Fintype.card R) := by
  have h := (simulateQ_triple_ranked (hitOracle T) (potential T) (hitOracle_step T)
    (fun k st => by simp only [OracleComp.Upper.rel_iff, potential, ofDual_toDual]; simp) adv q
    hq).le_wp (fun _ => none, false)
  rw [OracleComp.Upper.rel_iff] at h
  simpa [potential, StateT.wp_apply_eq, OracleComp.Upper.wp_eq] using h

end RankedPotential

/-- A triple of a stateful program is a statement about the support of its run, the form the
relational lifts consume. -/
example {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) :
    ∀ s, s = true → ∀ (a : α) (s' : Bool),
      (a, s') ∈ support ((simulateQ flagHandler oa : StateT Bool ProbComp α).run s) →
        s' = true := by
  refine (triple_stateT_iff_forall_support _ _ _ ⟨⟩).mp ?_
  prvcgen [flagHandler] invariants
    · fun s => s = true
  simp_all

end Examples.ProgramLogic.HandlerInvariants
