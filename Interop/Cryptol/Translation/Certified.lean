/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Contracts

/-!
# Certified total implementations of resolved source

A certificate retains the source being specified and a finite implementation.
Its proof identifies the complete represented result on represented data
inputs. Arbitrary preconditions and postconditions then transfer through the
existing contract API. Producing a candidate implementation is not a proof.
-/

public section

namespace Interop.Cryptol.Finite

/-- A source function with a checked finite implementation on represented data. -/
structure CertifiedFunction {a b : Ty} (ha : DataShape a) (hb : DataShape b) where
  /-- The resolved source whose semantics is claimed. -/
  source : Resolved.Term [] (.arrow a.core b.core)
  /-- A total implementation, retaining its finite syntax for execution and export. -/
  implementation : Term [] (.arrow a b)
  /-- Source evaluation produces every component of the implementation's result. -/
  correct : ∀ x, DomainResult.applyContinuous (Resolved.denote source Environment.empty)
    (encodeData ha x) = encodeData hb (implementation.denote Env.empty x)

namespace CertifiedFunction

variable {a b : Ty} {ha : DataShape a} {hb : DataShape b}

/-- A finite description certifies its own compact source translation. -/
@[expose] noncomputable def ofTerm (ha : DataShape a) (hb : DataShape b)
    (f : Term [] (.arrow a b)) : CertifiedFunction ha hb where
  source := f.source
  implementation := f
  correct x := by
    obtain ⟨fn, hf, hfn⟩ := f.source_correct Env.empty Environment.empty envRepresents_empty
    rw [hf, DomainResult.applyContinuous_value]
    exact Represents.eq_encodeData hb (hfn x _ (represents_encodeData ha x))

/-- The certified meaning is also the meaning of the operational core lowering. -/
theorem lower_apply (f : CertifiedFunction ha hb) (x : a.Native) :
    DomainResult.applyContinuous ((Resolved.lower f.source).denote Environment.empty)
      (encodeData ha x) = encodeData hb (f.implementation.denote Env.empty x) := by
  rw [Resolved.lower_correct]
  exact f.correct x

/-- Arbitrary specifications can be pulled or pushed through a certified source function. -/
theorem contract_iff (f : CertifiedFunction ha hb) (g : a.Native → b.Native)
    (h : ∀ x, f.implementation.denote Env.empty x = g x)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataContract ha (Resolved.lower f.source) pre post ↔ ∀ x, pre x → post x (g x) := by
  let semantic : CertifiedMeaning ha hb :=
    ⟨(Resolved.lower f.source).denote Environment.empty,
      f.implementation.denote Env.empty, f.lower_apply⟩
  exact semantic.contract_iff g h pre post

end CertifiedFunction

end Interop.Cryptol.Finite
