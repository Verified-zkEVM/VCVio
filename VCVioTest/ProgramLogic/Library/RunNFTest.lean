/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.RunNF

/-!
# Tests for the `simulateQ_nf` simp set
-/

public section

open OracleSpec OracleComp

universe u w u' v'

namespace RunNFTest

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{u, w} ι₂}
  {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'} {σ α : Type w}

/-- A two-query program under a sum handler, with queries lifted from the summands, runs into a
bind chain over the summand handlers. -/
example (h₁ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (h₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))) (t₁ : spec₁.Domain) (t₂ : spec₂.Domain)
    (s : σ) :
    (simulateQ (h₁ + h₂) (do
      let a ← liftM (spec₁.query t₁)
      let b ← liftM (spec₂.query t₂)
      pure (a, b) : OracleComp (spec₁ + spec₂) _)).run s =
      (h₁ t₁).run s >>= fun p ↦ (h₂ t₂).run p.2 >>= fun q ↦ pure ((p.1, q.1), q.2) := by
  simp only [simulateQ_nf]

/-- Direct-style queries through the summand lifts, in a support hypothesis about `run'`. -/
example (h₁ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (h₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))) (t₁ : spec₁.Domain) (t₂ : spec₂.Domain)
    (s : σ) (z) (hz : z ∈ support ((simulateQ (h₁ + h₂) (do
      let a ← (query t₁ : OracleComp (spec₁ + spec₂) _)
      let b ← (query t₂ : OracleComp (spec₁ + spec₂) _)
      pure (a, b))).run' s)) :
    ∃ p ∈ support ((h₁ t₁).run s), ∃ q ∈ support ((h₂ t₂).run p.2), z = (p.1, q.1) := by
  simpa only [simulateQ_nf] using hz

/-- Queries to the sum specification itself dispatch through `QueryImpl.add_apply_inl`; the
answer types are those of the sum specification, so the witnesses are repackaged by `obtain`. -/
example (h₁ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (h₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))) (t₁ : spec₁.Domain) (t₂ : spec₂.Domain)
    (s : σ) (z) (hz : z ∈ support ((simulateQ (h₁ + h₂) (do
      let a ← query (spec := spec₁ + spec₂) (.inl t₁)
      let b ← query (spec := spec₁ + spec₂) (.inr t₂)
      pure (a, b))).run s)) :
    ∃ p ∈ support ((h₁ t₁).run s), ∃ q ∈ support ((h₂ t₂).run p.2),
      z = ((p.1, q.1), q.2) := by
  simp only [simulateQ_nf] at hz
  obtain ⟨p, hp, q, hq, rfl⟩ := hz
  exact ⟨p, hp, q, hq, rfl⟩

/-- A monoid-log handler: the logs of the two calls multiply. -/
example {ω : Type w} [Monoid ω] (h : QueryImpl spec₁ (WriterT ω (OracleComp spec')))
    (t₁ t₂ : spec₁.Domain) (z) (hz : z ∈ support ((simulateQ h (do
      let a ← query t₁
      let b ← query t₂
      pure (a, b) : OracleComp spec₁ _)).run)) :
    ∃ p ∈ support (h t₁).run, ∃ q ∈ support (h t₂).run, z = ((p.1, q.1), p.2 * q.2) := by
  simpa only [simulateQ_nf] using hz

/-- An append-log handler: the logs of the two calls concatenate. -/
example {ω : Type w} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (h : QueryImpl spec₁ (WriterT ω (OracleComp spec'))) (t₁ t₂ : spec₁.Domain) (z)
    (hz : z ∈ support ((simulateQ h (do
      let a ← query t₁
      let b ← query t₂
      pure (a, b) : OracleComp spec₁ _)).run)) :
    ∃ p ∈ support (h t₁).run, ∃ q ∈ support (h t₂).run, z = ((p.1, q.1), p.2 ++ q.2) := by
  simpa only [simulateQ_nf] using hz

/-- Handler bodies: `get`, `set`, `modify` and base-monad lifts run step by step. -/
example (h : QueryImpl spec₁ (StateT σ (OracleComp spec'))) (oa : OracleComp spec' α)
    (t : spec₁.Domain) (s : σ) :
    (do
      let a ← (liftM oa : StateT σ (OracleComp spec') α)
      let s' ← get
      set s'
      let u ← h t
      modify id
      pure (a, u)).run s =
      oa >>= fun a ↦ (h t).run s >>= fun p ↦ pure ((a, p.1), p.2) := by
  simp only [simulateQ_nf, id_eq]

/-- Conditionals in the simulated program become conditionals of runs. -/
example (h : QueryImpl spec₁ (StateT σ (OracleComp spec'))) (t : spec₁.Domain) (c : Prop)
    [Decidable c] (u : spec₁.Range t) (s : σ) :
    (simulateQ h (if c then query t else pure u)).run s =
      if c then (h t).run s else pure (u, s) := by
  simp only [simulateQ_nf]

end RunNFTest
