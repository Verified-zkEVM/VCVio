/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.ProgramLogic.Library.T1.RunNF
public import VCVio.ProgramLogic.Unary.WP.NecessarySpecs

/-!
# Tests for whole-run triples of simulated programs
-/

public section

open OracleSpec OracleComp Std.WP OracleComp.ProgramLogic

open scoped OracleComp.Necessary

set_option experimental.vcgen true

namespace LiftsTest

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- A handler counting its calls, forwarding each query. -/
def countImpl : QueryImpl spec (StateT ℕ (OracleComp spec)) := fun t ↦ do
  modify (· + 1)
  monadLift (liftM (spec.query t) : OracleComp spec (spec.Range t))

theorem countImpl_step (t : spec.Domain) (n : ℕ) :
    ∀ z ∈ support ((countImpl t : StateT ℕ (OracleComp spec) _).run n), n ≤ z.2 := by
  intro z hz
  simp only [countImpl, simulateQ_nf] at hz
  obtain ⟨u, -, rfl⟩ := hz
  exact Nat.le_succ n

instance : (countImpl : QueryImpl spec (StateT ℕ (OracleComp spec))).MonotoneState (· ≤ ·) :=
  .of_le countImpl_step

/-- An opaque program followed by a query: the instance frame steps over the opaque part. -/
example (oa : OracleComp spec ℕ) (t : spec.Domain) :
    ⦃ fun n ↦ 0 < n ⦄
      (simulateQ countImpl (do let _ ← oa; query t) : StateT ℕ (OracleComp spec) _)
    ⦃ fun _ n ↦ 1 < n ⦄ := by
  vcgen [countImpl] with finish

/-- The instance frame under a sum handler: the sum inherits `MonotoneState`. -/
example (oa : OracleComp (spec + spec) ℕ) :
    ⦃ fun n ↦ 2 ≤ n ⦄
      (simulateQ (countImpl (spec := spec) + countImpl (spec := spec)) oa :
        StateT ℕ (OracleComp spec) _)
    ⦃ fun _ n ↦ 1 ≤ n ⦄ := by
  vcgen with finish

/-- The class gives the support consequence directly. -/
example (oa : OracleComp spec ℕ) (n : ℕ) (z) (hz : z ∈ support ((simulateQ countImpl oa).run n)) :
    n ≤ z.2 :=
  QueryImpl.MonotoneState.rel_of_mem_support hz

universe u w u' v'

variable {ι₁ : Type u} {spec₁ : OracleSpec.{u, w} ι₁} {ι' : Type u'}
  {spec' : OracleSpec.{u', v'} ι'} {σ : Type w}

/-- The explicit frame for a handler without an instance, at arbitrary universes. -/
example (h : QueryImpl spec₁ (StateT σ (OracleComp spec'))) (R : σ → σ → Prop)
    (hrefl : ∀ s, R s s) (htrans : ∀ s₁ s₂ s₃, R s₁ s₂ → R s₂ s₃ → R s₁ s₃)
    (hstep : ∀ t s, ∀ z ∈ support ((h t).run s), R s z.2) (P : σ → Prop)
    (hP : ∀ s s', R s s' → P s → P s') (Q : σ → Prop) (t : spec₁.Domain)
    (hq : ⦃ fun s ↦ P s ⦄ h t ⦃ fun _ s ↦ Q s ⦄) (oa : OracleComp spec₁ (ULift.{w} ℕ)) :
    ⦃ fun s ↦ P s ⦄ simulateQ h (do let _ ← oa; query t) ⦃ fun _ s ↦ Q s ⦄ := by
  vcgen [triple_simulateQ_frame h R hrefl htrans hstep oa, hq]
  grind

/-- An invariant of every call is an invariant of every simulation. -/
example (h : QueryImpl spec₁ (StateT σ (OracleComp spec'))) (I : σ → Prop)
    (hh : ∀ t, ⦃ fun s ↦ I s ⦄ h t ⦃ fun _ s ↦ I s ⦄) (oa : OracleComp spec₁ (ULift.{w} ℕ)) :
    ⦃ fun s ↦ I s ⦄ simulateQ h oa ⦃ fun _ s ↦ I s ⦄ :=
  triple_simulateQ_inv hh oa

/-- A logging handler: each call records its input. -/
def logImpl : QueryImpl spec (WriterT (List ι) (OracleComp spec)) := fun t ↦ do
  tell [t]
  monadLift (liftM (spec.query t) : OracleComp spec (spec.Range t))

open scoped WriterT.AppendWP in
/-- The writer frame: inputs logged by an arbitrary program stay in a set containing them all. -/
example (S : Set ι) (hS : ∀ t, t ∈ S) (oa : OracleComp spec ℕ) :
    ⦃ fun l ↦ ∀ x ∈ l, x ∈ S ⦄ simulateQ logImpl oa ⦃ fun _ l ↦ ∀ x ∈ l, x ∈ S ⦄ := by
  vcgen [triple_simulateQ_writerT_frame_append logImpl (fun l ↦ ∀ x ∈ l, x ∈ S)
    (fun _ h ↦ (List.not_mem_nil h).elim)
    (fun a b ha hb x hx ↦ (List.mem_append.1 hx).elim (ha x) (hb x)) (fun _ _ _ x _ ↦ hS x) oa]
    with finish

/-- A ghost-state handler inherits the triples of the plain counter through `Prod.fst`. -/
example (ghost : QueryImpl spec (StateT (ℕ × Bool) (OracleComp spec)))
    (hghost : ∀ t s, ∀ z ∈ support ((ghost t).run s),
      (z.1, z.2.1) ∈ support ((countImpl t).run s.1)) (oa : OracleComp spec ℕ) (n₀ : ℕ) :
    ⦃ fun s ↦ n₀ ≤ s.1 ⦄ simulateQ ghost oa ⦃ fun _ s ↦ n₀ ≤ s.1 ⦄ :=
  triple_simulateQ_of_proj Prod.fst hghost (P := fun n ↦ n₀ ≤ n) (Q := fun _ n ↦ n₀ ≤ n)
    (by vcgen with finish)


/-- A handler preserving an invariant, through `MonotoneState.of_inv`: the frame carries the
invariant over an opaque program. -/
example (h : QueryImpl spec (StateT ℕ (OracleComp spec)))
    (hstep : ∀ t s, Even s → ∀ z ∈ support ((h t).run s), Even z.2) (oa : OracleComp spec ℕ) :
    ⦃ fun n ↦ Even n ⦄ simulateQ h oa ⦃ fun _ n ↦ Even n ⦄ := by
  have := QueryImpl.MonotoneState.of_inv hstep
  vcgen with finish

end LiftsTest
