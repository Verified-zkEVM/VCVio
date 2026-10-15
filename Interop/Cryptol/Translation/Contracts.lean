/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.SemanticCertificate
public import Interop.Cryptol.Translation.FiniteSource

/-!
# Total contracts across finite descriptions and native functions

Contracts require a fully defined output word. The transfer theorem permits
arbitrary Lean preconditions and postconditions; text export additionally
requires a finite Boolean description of the property.
-/

public section

namespace Interop.Cryptol.Finite

/-- Total correctness for arbitrary represented data, including tupled arguments and arrays. -/
@[expose] def DataContract {a b : Ty} (ha : DataShape a)
    (f : ClosedExpr [] (.arrow a.core b.core))
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) : Prop :=
  DataMeaningContract ha (f.denote Environment.empty) pre post

/-- Preconditions and postconditions transfer in either direction across an all-input equality. -/
theorem Term.dataContract_iff {a b : Ty} (ha : DataShape a) (hb : DataShape b)
    (f : Term [] (.arrow a b)) (g : a.Native → b.Native)
    (h : ∀ x, f.denote Env.empty x = g x)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataContract ha f.lower pre post ↔ ∀ x, pre x → post x (g x) := by
  obtain ⟨fn, hf, hfn⟩ := f.lower_correct Env.empty Environment.empty envRepresents_empty
  have hr (x : a.Native) : Represents b (g x)
      (DomainResult.applyContinuous (f.lower.denote Environment.empty) (encodeData ha x)) := by
    rw [hf, DomainResult.applyContinuous_value]
    rw [← h x]
    exact hfn x _ (represents_encodeData ha x)
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    have he := Represents.functional hb hy (hr x)
    simpa only [he] using hp
  · intro hp x hx
    exact ⟨g x, hr x, hp x hx⟩

/-- The compact source route supports the same contracts on tupled and array data. -/
theorem Term.source_dataContract_iff {a b : Ty} (ha : DataShape a) (hb : DataShape b)
    (f : Term [] (.arrow a b)) (g : a.Native → b.Native)
    (h : ∀ x, f.denote Env.empty x = g x)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataContract ha (Resolved.lower f.source) pre post ↔ ∀ x, pre x → post x (g x) := by
  obtain ⟨fn, hf, hfn⟩ := f.source_lower_correct Env.empty Environment.empty envRepresents_empty
  have hr (x : a.Native) : Represents b (g x)
      (DomainResult.applyContinuous ((Resolved.lower f.source).denote Environment.empty)
        (encodeData ha x)) := by
    rw [hf, DomainResult.applyContinuous_value]
    rw [← h x]
    exact hfn x _ (represents_encodeData ha x)
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    have he := Represents.functional hb hy (hr x)
    simpa only [he] using hp
  · intro hp x hx
    exact ⟨g x, hr x, hp x hx⟩

/-- Total correctness for a core word function on represented inputs. -/
@[expose] def TotalContract {n m : Nat}
    (f : ClosedExpr [] (.arrow (.seq (Length.finite n) .bit) (.seq (Length.finite m) .bit)))
    (pre : BitVec n → Prop) (post : BitVec n → BitVec m → Prop) : Prop :=
  ∀ x, pre x → ∃ y, (Expr.app f (.word x)).denote Environment.empty =
    .value (wordValue y) ∧ post x y

/-- Total contracts can be pulled or pushed across a proved native correspondence. -/
theorem Term.totalContract_iff {n m : Nat}
    (f : Term [] (.arrow (.word n) (.word m))) (g : BitVec n → BitVec m)
    (h : ∀ x, f.denote Env.empty x = g x)
    (pre : BitVec n → Prop) (post : BitVec n → BitVec m → Prop) :
    TotalContract f.lower pre post ↔ ∀ x, pre x → post x (g x) := by
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    rw [Term.denote_apply_word, h x] at hy
    have he : g x = y := wordValue_injective (Sum.inr.inj (WithBot.coe_inj.mp hy))
    simpa [he] using hp
  · intro hp x hx
    exact ⟨g x, by rw [Term.denote_apply_word, h x], hp x hx⟩

/-- A represented result guarantees termination of each in-range bit observation. -/
theorem Term.bit_observation_terminates {n m : Nat}
    (f : Term [] (.arrow (.word n) (.word m))) (x : BitVec n) (i : Fin m) :
    ∃ w, Evaluates (Expr.index (.app f.lower (.word x)) (.integer i.val)) (.ok w) ∧
      w.denote = (⟨(f.denote Env.empty x).getMsbD i.val⟩ : Value .bit) := by
  apply (Expr.adequacy_value _ _).mp
  exact Expr.denote_index_word _ _ _ (f.denote_apply_word x) i _ rfl

/-- A finite Boolean property has an equivalent core semantic truth assertion. -/
theorem Term.property_iff {n : Nat} (p : Term [] (.arrow (.word n) .bit)) :
    (∀ x, p.denote Env.empty x = true) ↔
      ∀ x, (Expr.app p.lower (.word x)).denote Environment.empty = .value ⟨true⟩ := by
  constructor
  · intro h x
    rw [p.denote_apply_bit, h x]
  · intro h x
    have hx := h x
    have hh := (p.denote_apply_bit x).symm.trans hx
    exact DiscreteOrder.mk.inj (Sum.inr.inj (WithBot.coe_inj.mp hh))

end Interop.Cryptol.Finite
