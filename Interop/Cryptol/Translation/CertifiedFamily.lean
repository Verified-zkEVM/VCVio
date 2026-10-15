/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolySpecialization
public import Interop.Cryptol.Translation.SemanticCertificate
public import Interop.Cryptol.Translation.FiniteSource

/-!
# Certificates for one finite polymorphic source

A family interface specifies the admitted instantiations and represented input
and output shapes. A certificate retains one finite source description and
proves correspondence for every instance of that interface. Restricting the
interface restricts the claim; unlisted instantiations are not certified.
-/

public section

namespace Interop.Cryptol.Finite

open Polymorphic

/-- The checked instances on which a polymorphic source is to be specified. -/
structure FamilyInterface {w : Polymorphic.Scope} (s : w.ValueSort) (I : Type) where
  /-- Assignment of the source's free parameters. -/
  assignment : I → w.Assignment
  /-- Represented input shape at each instance. -/
  input : I → Ty
  /-- Represented output shape at each instance. -/
  output : I → Ty
  /-- Inputs are finite data, not arbitrary functions. -/
  inputData : ∀ i, DataShape (input i)
  /-- Outputs are finite data, not arbitrary functions. -/
  outputData : ∀ i, DataShape (output i)
  /-- Ordered arguments and constraint evidence reaching the instance's function type. -/
  specialization : ∀ i, Specialization s (assignment i).val
    (.arrow (input i).core (output i).core)

/-- All-input semantic correspondence for one finite polymorphic description. -/
structure CertifiedFamily {w : Polymorphic.Scope} {s : w.ValueSort} {I : Type}
    (interface : FamilyInterface s I) where
  /-- The single finite source, before any instantiation. -/
  source : Polymorphic.Term w [] s
  /-- Executable finite implementations for the admitted instances. -/
  implementation : ∀ i, Term [] (.arrow (interface.input i) (interface.output i))
  /-- Every instance and represented input has the full represented result. -/
  correct : ∀ i x, DomainResult.applyContinuous
    (source.observe (interface.assignment i) (interface.specialization i)
      (Polymorphic.Env.empty _)) (encodeData (interface.inputData i) x) =
        encodeData (interface.outputData i) ((implementation i).denote Env.empty x)

namespace CertifiedFamily

variable {w : Polymorphic.Scope} {s : w.ValueSort} {I : Type}
  {interface : FamilyInterface s I}

/-- Expose the shared semantic certificate at one checked instance. -/
@[expose] noncomputable def meaningAt (f : CertifiedFamily interface) (i : I) :
    CertifiedMeaning (interface.inputData i) (interface.outputData i) where
  meaning := f.source.observe (interface.assignment i) (interface.specialization i)
    (Polymorphic.Env.empty _)
  implementation := (f.implementation i).denote Env.empty
  correct := f.correct i

/-- Pull or push an arbitrary specification at any admitted instantiation. -/
theorem contract_iff (f : CertifiedFamily interface) (i : I)
    (g : (interface.input i).Native → (interface.output i).Native)
    (h : ∀ x, (f.implementation i).denote Env.empty x = g x)
    (pre : (interface.input i).Native → Prop)
    (post : (interface.input i).Native → (interface.output i).Native → Prop) :
    DataMeaningContract (interface.inputData i) (f.meaningAt i).meaning pre post ↔
      ∀ x, pre x → post x (g x) :=
  (f.meaningAt i).contract_iff g h pre post

end CertifiedFamily
end Interop.Cryptol.Finite
