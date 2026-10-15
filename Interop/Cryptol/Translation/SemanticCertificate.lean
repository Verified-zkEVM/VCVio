/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Representation

/-!
# Specifications of represented semantic functions

Contract transfer depends on a semantic equality and a faithful representation.
It is independent of the syntax used to produce that meaning. Source-specific
certificates retain their descriptions and supply this common semantic evidence.
-/

public section

namespace Interop.Cryptol.Finite

/-- Total correctness of a semantic function on represented data inputs. -/
@[expose] def DataMeaningContract {a b : Ty} (ha : DataShape a)
    (f : Computation (.arrow a.core b.core))
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) : Prop :=
  ∀ x, pre x → ∃ y, Represents b y
    (DomainResult.applyContinuous f (encodeData ha x)) ∧ post x y

/-- Semantic correspondence on an explicit admissible set of inputs.
No behavior is asserted outside `valid`; source errors and divergence remain possible there. -/
@[expose] def CorrespondsOn {a b : Ty} (ha : DataShape a) (hb : DataShape b)
    (valid : a.Native → Prop) (meaning : Computation (.arrow a.core b.core))
    (implementation : a.Native → b.Native) : Prop :=
  Control.Semantics.CorrespondsOn (dataEmbedding ha) (dataEmbedding hb) valid
    (DomainResult.applyContinuous meaning) implementation

namespace CorrespondsOn

variable {a b : Ty} {ha : DataShape a} {hb : DataShape b}
  {valid : a.Native → Prop} {meaning : Computation (.arrow a.core b.core)}
  {implementation : a.Native → b.Native}

/-- Restrict an admissibility profile without changing source or implementation. -/
theorem mono (h : CorrespondsOn ha hb valid meaning implementation)
    {valid' : a.Native → Prop} (hvalid : ∀ x, valid' x → valid x) :
    CorrespondsOn ha hb valid' meaning implementation :=
  Control.Semantics.CorrespondsOn.mono h hvalid

/-- An implementation equality is needed only on the certified domain. -/
theorem congr (h : CorrespondsOn ha hb valid meaning implementation)
    {other : a.Native → b.Native} (he : ∀ x, valid x → implementation x = other x) :
    CorrespondsOn ha hb valid meaning other :=
  Control.Semantics.CorrespondsOn.congr h he

/-- Preconditions and postconditions transfer when the precondition implies admissibility. -/
theorem contract_iff (h : CorrespondsOn ha hb valid meaning implementation)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop)
    (admissible : ∀ x, pre x → valid x) :
    DataMeaningContract ha meaning pre post ↔ ∀ x, pre x → post x (implementation x) := by
  have transfer := Control.Semantics.CorrespondsOn.contract_iff h pre post admissible
  refine Iff.trans ?_ transfer
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    exact ⟨y, Represents.eq_encodeData hb hy, hp⟩
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    exact ⟨y, hy ▸ represents_encodeData hb y, hp⟩

/-- A source Boolean proposition is true exactly when its native counterpart is true.
Truth here means a fully defined `true`, never error or divergence. -/
theorem property_iff {meaning : Computation (.arrow a.core .bit)}
    {implementation : a.Native → Bool}
    (h : CorrespondsOn ha .bit valid meaning implementation) (x : a.Native) (hx : valid x) :
    DomainResult.applyContinuous meaning (encodeData ha x) = encodeData .bit true ↔
      implementation x = true :=
  Control.Semantics.CorrespondsOn.eq_iff h x hx true

end CorrespondsOn

/-- A total native function and its all-input semantic representation theorem. -/
structure CertifiedMeaning {a b : Ty} (ha : DataShape a) (hb : DataShape b) where
  /-- The source function's potentially partial denotation. -/
  meaning : Computation (.arrow a.core b.core)
  /-- The total native function used in specifications. -/
  implementation : a.Native → b.Native
  /-- Every represented input produces the entire represented native result. -/
  correct : ∀ x, DomainResult.applyContinuous meaning (encodeData ha x) =
    encodeData hb (implementation x)

/-- The language-independent certificate instantiated with Cryptol's data representations. -/
@[expose] noncomputable def CertifiedMeaning.semanticCertificate {a b : Ty}
    {ha : DataShape a} {hb : DataShape b} (f : CertifiedMeaning ha hb) :
    Control.Semantics.CertifiedMeaning (dataEmbedding ha) (dataEmbedding hb) where
  meaning := DomainResult.applyContinuous f.meaning
  implementation := f.implementation
  correct := f.correct

/-- An all-input certificate supplies every restricted admissibility profile. -/
theorem CertifiedMeaning.correspondsOn {a b : Ty} {ha : DataShape a} {hb : DataShape b}
    (f : CertifiedMeaning ha hb) (valid : a.Native → Prop) :
    CorrespondsOn ha hb valid f.meaning f.implementation :=
  f.semanticCertificate.correspondsOn valid

/-- Preconditions and postconditions transfer in both directions through the certificate. -/
theorem CertifiedMeaning.contract_iff {a b : Ty} {ha : DataShape a} {hb : DataShape b}
    (f : CertifiedMeaning ha hb) (g : a.Native → b.Native)
    (h : ∀ x, f.implementation x = g x)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataMeaningContract ha f.meaning pre post ↔ ∀ x, pre x → post x (g x) :=
  ((f.correspondsOn pre).congr (fun x _ => h x)).contract_iff pre post (fun _ hx => hx)

end Interop.Cryptol.Finite
