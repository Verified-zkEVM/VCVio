/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Finite
public import PolyFun.Control.Semantics.Correspondence

/-!
# Total data representations

Finite words, tuples and arrays have canonical fully defined representations.
The function relation in `Finite.Represents` remains extensional on represented
arguments. Data results are unique, which is the boundary needed to transfer
arbitrary preconditions and postconditions.
-/

public section

namespace Interop.Cryptol.Finite

/-- Data types exclude function values but allow nested tuples and finite arrays. -/
inductive DataShape : Ty → Type where
  | bit : DataShape .bit
  | word (n : Nat) : DataShape (.word n)
  | prod {a b : Ty} : DataShape a → DataShape b → DataShape (.prod a b)
  | seq (n : Nat) {a : Ty} : DataShape a → DataShape (.seq n a)

/-- Canonical embedding of a fully defined data value into the partial semantics. -/
@[expose] noncomputable def encodeData : {a : Ty} → DataShape a → a.Native → Computation a.core
  | _, .bit, b => .value ⟨b⟩
  | _, .word _, x => .value (wordValue x)
  | _, .prod ha hb, x => .value (encodeData ha x.1, encodeData hb x.2)
  | _, .seq _ ha, xs => .value (fun i => encodeData ha (xs i))

/-- Every canonical data embedding satisfies the logical relation. -/
theorem represents_encodeData {a : Ty} (ha : DataShape a) (x : a.Native) :
    Represents a x (encodeData ha x) := by
  induction ha with
  | bit => rfl
  | word n => rfl
  | prod ha hb iha ihb => exact ⟨_, _, rfl, iha x.1, ihb x.2⟩
  | seq n ha ih => exact ⟨_, rfl, fun i => ih (x i)⟩

/-- A fully represented data computation determines its unique native value. -/
theorem Represents.functional {a : Ty} (ha : DataShape a) {x y : a.Native}
    {d : Computation a.core} (hx : Represents a x d) (hy : Represents a y d) : x = y := by
  induction ha with
  | bit =>
      exact DiscreteOrder.mk.inj (DomainResult.value_inj.mp (hx.symm.trans hy))
  | word n => exact wordValue_injective (DomainResult.value_inj.mp (hx.symm.trans hy))
  | prod ha hb iha ihb =>
      obtain ⟨dx, dx', hdx, hx, hx'⟩ := hx
      obtain ⟨dy, dy', hdy, hy, hy'⟩ := hy
      have hd := DomainResult.value_inj.mp (hdx.symm.trans hdy)
      have hl : dx = dy := congrArg Prod.fst hd
      have hr : dx' = dy' := congrArg Prod.snd hd
      subst dy
      subst dy'
      exact Prod.ext (iha hx hy) (ihb hx' hy')
  | seq n ha ih =>
      obtain ⟨dx, hdx, hx⟩ := hx
      obtain ⟨dy, hdy, hy⟩ := hy
      have hd := DomainResult.value_inj.mp (hdx.symm.trans hdy)
      subst dy
      funext i
      exact ih (hx i) (hy i)

/-- A total data relation identifies the entire partial value with its canonical embedding. -/
theorem Represents.eq_encodeData {a : Ty} (ha : DataShape a) {x : a.Native}
    {d : Computation a.core} (h : Represents a x d) : d = encodeData ha x := by
  induction ha with
  | bit => exact h
  | word n => exact h
  | prod ha hb iha ihb =>
      obtain ⟨dx, dy, hd, hx, hy⟩ := h
      rw [hd, iha hx, ihb hy]
      rfl
  | seq n ha ih =>
      obtain ⟨ds, hd, hs⟩ := h
      rw [hd]
      apply congrArg DomainResult.value
      funext i
      exact ih (hs i)

/-- Fully defined data embeds faithfully into Cryptol's partial semantic carrier. -/
@[expose] noncomputable def dataEmbedding {a : Ty} (ha : DataShape a) :
    a.Native ↪ Computation a.core where
  toFun := encodeData ha
  inj' := by
    intro x y he
    exact Represents.functional ha (represents_encodeData ha x)
      (he ▸ represents_encodeData ha y)

/-- Apply a lowered finite function to any fully defined data argument. -/
theorem Term.denote_apply_data {a b : Ty} (ha : DataShape a) (hb : DataShape b)
    (f : Term [] (.arrow a b)) (x : a.Native) :
    DomainResult.applyContinuous (f.lower.denote Environment.empty) (encodeData ha x) =
      encodeData hb (f.denote Env.empty x) := by
  obtain ⟨fn, hf, hfn⟩ := f.lower_correct Env.empty Environment.empty envRepresents_empty
  rw [hf, DomainResult.applyContinuous_value]
  exact Represents.eq_encodeData hb (hfn x _ (represents_encodeData ha x))

/-- Quotation of native data uses only finite syntax. -/
@[expose] def Term.quoteData {Γ : List Ty} : {a : Ty} → DataShape a → a.Native → Term Γ a
  | _, .bit, b => .bit b
  | _, .word _, x => .word x
  | _, .prod ha hb, x => .pair (quoteData ha x.1) (quoteData hb x.2)
  | _, .seq n ha, xs => .sequence n (fun i => quoteData ha (xs i))

/-- Data quotation preserves native values without an evaluator assumption. -/
@[simp] theorem Term.denote_quoteData {Γ : List Ty} {a : Ty} (ha : DataShape a)
    (x : a.Native) (ρ : Env Γ) : (quoteData ha x).denote ρ = x := by
  induction ha with
  | bit => rfl
  | word n => rfl
  | prod ha hb iha ihb =>
      change ((quoteData ha x.1).denote ρ, (quoteData hb x.2).denote ρ) = x
      rw [iha, ihb]
      rfl
  | seq n ha ih =>
      funext i
      exact ih (x i)

end Interop.Cryptol.Finite
