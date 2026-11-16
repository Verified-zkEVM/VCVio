/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Basic
import Lean.Elab.Tactic.Omega

/-!
# Nonmaximum outputs and nontrivial codes

A code with two distinct incomparable words has at least two coordinates and radix at least two.
It also excludes the all-maximum word from every successful encoding output, whether or not both
witness words can actually be emitted.
-/

public section

namespace IncomparableEncoding

variable {PP M R E : Type*} {n radix : ℕ}

/-- Every emitted word has a coordinate strictly below the greatest digit. -/
@[expose] def NoMaximumOutput (enc : IncomparableEncoding PP M R E n radix) : Prop :=
  ∀ pp msg randomizer ep word, enc.value pp msg randomizer ep = some word →
    ∃ i : Fin n, (word i).val < radix - 1

/-- Two distinct members of a global incomparable code exclude maximum emitted words. -/
theorem noMaximumOutput_of_two_codewords (enc : IncomparableEncoding PP M R E n radix)
    (htwo : ∃ x y : Codeword n radix, x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y) :
    enc.NoMaximumOutput := by
  obtain ⟨x, y, hx, hy, hxy⟩ := htwo
  intro pp msg randomizer ep word hword
  have hw : word ∈ enc.code := enc.mem_code_of_value_eq_some pp msg randomizer ep hword
  have hother : ∃ z : Codeword n radix, z ∈ enc.code ∧ word ≠ z := by
    by_cases h : word = x
    · exact ⟨y, hy, by simpa [h] using hxy⟩
    · exact ⟨x, hx, h⟩
  obtain ⟨z, hz, hwz⟩ := hother
  obtain ⟨i, hi⟩ := (enc.incomparable hw hz hwz).1
  exact ⟨i, by have := (z i).isLt; omega⟩

/-- Two distinct incomparable codewords require at least two coordinates. -/
theorem two_le_length_of_two_codewords (enc : IncomparableEncoding PP M R E n radix)
    (htwo : ∃ x y : Codeword n radix, x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y) : 2 ≤ n := by
  obtain ⟨x, y, hx, hy, hxy⟩ := htwo
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := enc.incomparable hx hy hxy
  have hne : i.val ≠ j.val := by
    intro heq
    have hij : i = j := Fin.ext heq
    subst j
    exact lt_asymm hi hj
  have hiLt := i.isLt
  have hjLt := j.isLt
  omega

/-- Two distinct incomparable codewords require at least two possible digit values. -/
theorem two_le_radix_of_two_codewords (enc : IncomparableEncoding PP M R E n radix)
    (htwo : ∃ x y : Codeword n radix, x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y) : 2 ≤ radix := by
  obtain ⟨x, y, hx, hy, hxy⟩ := htwo
  obtain ⟨i, hi⟩ := (enc.incomparable hx hy hxy).1
  have hyLt := (y i).isLt
  change (x i).val < (y i).val at hi
  omega

end IncomparableEncoding
