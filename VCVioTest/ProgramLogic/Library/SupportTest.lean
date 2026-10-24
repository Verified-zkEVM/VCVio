/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.RunNF
public import VCVio.ProgramLogic.Library.T1.Support

/-!
# Tests for the support calculus of simulated runs
-/

public section

open OracleSpec OracleComp

universe u w u' v'

namespace SupportTest

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{u, w} ι₂}
  {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'} {σ α : Type w}

/-- Destructuring a two-query run under a sum handler with `simulateQ_nf`. -/
example (h₁ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (h₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))) (t₁ : spec₁.Domain) (t₂ : spec₂.Domain)
    (s : σ) (z) (hz : z ∈ support ((simulateQ (h₁ + h₂) (do
      let a ← query (spec := spec₁ + spec₂) (.inl t₁)
      let b ← query (spec := spec₁ + spec₂) (.inr t₂)
      pure (a, b))).run s)) :
    ∃ s₁, (z.1.1, s₁) ∈ support ((h₁ t₁).run s) ∧ (z.1.2, z.2) ∈ support ((h₂ t₂).run s₁) := by
  simp only [simulateQ_nf] at hz
  obtain ⟨p, hp, q, hq, rfl⟩ := hz
  exact ⟨p.2, hp, hq⟩

/-- The same destructuring through the one-step rules. -/
example (h : QueryImpl spec₁ (StateT σ (OracleComp spec'))) (oa : OracleComp spec₁ α)
    (t : spec₁.Domain) (s : σ) (z) (hz : z ∈ support ((simulateQ h (do
      let a ← oa
      let u ← query t
      pure (a, u))).run s)) :
    ∃ s₁, (z.1.1, s₁) ∈ support ((simulateQ h oa).run s) ∧
      (z.1.2, z.2) ∈ support ((h t).run s₁) := by
  obtain ⟨a, s₁, ha, hz⟩ := (mem_support_simulateQ_run_bind_iff ..).1 hz
  obtain ⟨u, s₂, hu, hz⟩ := (mem_support_simulateQ_run_query_bind_iff ..).1 hz
  rw [mem_support_simulateQ_run_pure_iff] at hz
  exact hz ▸ ⟨s₁, ha, hu⟩

/-- A per-query monotonicity fact gives monotonicity of every run, for an arbitrary program. -/
example [Preorder σ] (h : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (hstep : ∀ t s, ∀ z ∈ support ((h t).run s), s ≤ z.2) (oa : OracleComp spec₁ α) (s : σ) :
    ∀ z ∈ support ((simulateQ h oa).run s), s ≤ z.2 :=
  fun _ hz ↦ le_of_mem_support_simulateQ_run hstep hz

/-- An invariant of both summands holds along every run of the sum handler. -/
example (h₁ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (h₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (hstep₁ : ∀ t s, Inv s → ∀ z ∈ support ((h₁ t).run s), Inv z.2)
    (hstep₂ : ∀ t s, Inv s → ∀ z ∈ support ((h₂ t).run s), Inv z.2)
    (oa : OracleComp (spec₁ + spec₂) α) (s : σ) (hs : Inv s) :
    ∀ z ∈ support ((simulateQ (h₁ + h₂) oa).run s), Inv z.2 :=
  fun _ hz ↦ inv_of_mem_support_simulateQ_add_run hstep₁ hstep₂ hs hz

/-- A handler counting its calls, forwarding each query. -/
def countImpl {ι : Type} {spec : OracleSpec.{0, 0} ι} :
    QueryImpl spec (StateT ℕ (OracleComp spec)) := fun t ↦ do
  modify (· + 1)
  monadLift (liftM (spec.query t) : OracleComp spec (spec.Range t))

/-- The count of a call is one more than the count before it. -/
theorem countImpl_step {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) (n : ℕ) :
    ∀ z ∈ support ((countImpl t : StateT ℕ (OracleComp spec) _).run n), z.2 = n + 1 := by
  intro z hz
  simp only [countImpl, simulateQ_nf] at hz
  obtain ⟨u, -, rfl⟩ := hz
  rfl

/-- The count only grows along an arbitrary program; a handler adding a ghost flag is simulated
by the plain counter along the projection `Prod.fst`. -/
example {ι : Type} {spec : OracleSpec.{0, 0} ι} (oa : OracleComp spec ℕ) (n : ℕ) (b : Bool)
    (ghost : QueryImpl spec (StateT (ℕ × Bool) (OracleComp spec)))
    (hghost : ∀ t s, ∀ z ∈ support ((ghost t).run s),
      (z.1, z.2.1) ∈ support ((countImpl t).run s.1)) (z)
    (hz : z ∈ support ((simulateQ ghost oa).run (n, b))) :
    n ≤ z.2.1 ∧ z.1 ∈ support oa := by
  have hz' := mem_support_simulateQ_run_of_proj Prod.fst hghost hz
  exact ⟨le_of_mem_support_simulateQ_run
    (fun t s z hz ↦ (countImpl_step t s z hz).symm ▸ Nat.le_succ s) hz',
    fst_mem_support_of_mem_support_simulateQ_run _ hz⟩

/-- A logging handler: each call records its input. -/
def logImpl {ι : Type} {spec : OracleSpec.{0, 0} ι} :
    QueryImpl spec (WriterT (List ι) (OracleComp spec)) := fun t ↦ do
  tell [t]
  monadLift (liftM (spec.query t) : OracleComp spec (spec.Range t))

/-- Every input recorded by the logging handler belongs to a set containing all inputs of the
program's queries; a predicate closed under `++` lifts from one call to every run. -/
example {ι : Type} {spec : OracleSpec.{0, 0} ι} (S : Set ι) (hS : ∀ t, t ∈ S)
    (oa : OracleComp spec ℕ) (z) (hz : z ∈ support (simulateQ logImpl oa).run) :
    ∀ x ∈ z.2, x ∈ S := by
  refine prop_of_mem_support_simulateQ_writerT_run_append (P := fun l ↦ ∀ x ∈ l, x ∈ S)
    (by simp) (fun a b ha hb x hx ↦ ?_) (fun t z _ x _ ↦ hS x) hz
  rcases List.mem_append.1 hx with hx | hx
  exacts [ha x hx, hb x hx]

/-- The state-projection equation of a ghost component gives forward simulation of runs. -/
example (h₁ : QueryImpl spec₁ (StateT (σ × Bool) (OracleComp spec')))
    (h₂ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (hproj : ∀ t s, Prod.map id Prod.fst <$> (h₁ t).run s = (h₂ t).run s.1)
    (oa : OracleComp spec₁ α) (s : σ × Bool) (z) (hz : z ∈ support ((simulateQ h₁ oa).run s)) :
    z.1 ∈ support ((simulateQ h₂ oa).run' s.1) :=
  (mem_support_simulateQ_run'_iff ..).2 ⟨_, mem_support_simulateQ_run_of_map_eq _ hproj hz⟩


end SupportTest
