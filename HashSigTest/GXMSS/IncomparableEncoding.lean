/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Incomparable
public import Mathlib.Data.Fin.VecNotation

/-!
# Incomparable-encoding probes

A two-word code contains `(0, 1)` and `(1, 0)`. Its coordinates directly witness both strict
inequalities without using a fixed-sum construction. Boolean inputs distinguish successful
words, returned failure, and distinct messages with the same output. Empty codes and the empty
word over the empty alphabet require no positivity or nonemptiness assumptions.
-/

public section

namespace GXMSS.Encoding.IncomparableEncodingProbe

/-- The first word has digits zero and one. -/
@[expose] def first : Codeword 2 2 := ![0, 1]

/-- The second word has digits one and zero. -/
@[expose] def second : Codeword 2 2 := ![1, 0]

/-- The two explicit words differ at coordinate zero. -/
theorem first_ne_second : first ≠ second := by decide

/-- The finite two-word code is incomparable, by its explicit coordinates. -/
theorem pair_incomparable : IncomparableCode ({first, second} : Set (Codeword 2 2)) := by
  intro x hx y hy hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  · exact (hne rfl).elim

/-- False randomness fails; true randomness selects a word using the public parameter. -/
@[expose] def enc : IncomparableEncoding Bool Bool Bool Bool 2 2 where
  code := {first, second}
  incomparable := pair_incomparable
  encode p _ r _ := if r then
    if p then some ⟨second, by simp⟩ else some ⟨first, by simp⟩
    else none

/-- Returned encoding failure remains `none` after observing its value. -/
theorem failed_encoding : enc.value false true false true = none := by rfl

/-- Distinct inputs can produce the two distinct successful words. -/
theorem distinct_successes :
    enc.value false false true false = some first ∧
    enc.value true true true true = some second := by exact ⟨rfl, rfl⟩

/-- The successful pair has strict coordinates in both directions. -/
theorem successful_pair_incomparable : IncomparableWords first second := by
  exact enc.incomparableWords_of_successes false true false true true true false true
    distinct_successes.1 distinct_successes.2 first_ne_second

/-- Distinct messages can successfully encode to the identical value. -/
theorem distinct_messages_same_value :
    (false : Bool) ≠ true ∧ enc.value false false true false = some first ∧
    enc.value false true true false = some first := by decide

/-- Identical successful output words are not incomparable. -/
theorem identical_success_not_incomparable : ¬ IncomparableWords first first := by
  intro h
  obtain ⟨i, hi⟩ := h.1
  exact (lt_irrefl _) hi

/-- An empty global code permits an always-failing encoding at arbitrary dimensions. -/
@[expose] def emptyCode (n radix : ℕ) : IncomparableEncoding Unit Unit Unit Unit n radix where
  code := ∅
  incomparable := by simp [IncomparableCode]
  encode _ _ _ _ := none

/-- Encodings with an empty code return failure even for a nonempty length and empty alphabet. -/
theorem empty_code_failure : (emptyCode 1 0).encode () () () () = none := by rfl

/-- The empty word exists even when the alphabet is empty. -/
@[expose] def emptyWord : Codeword 0 0 := Fin.elim0

/-- A singleton code containing the empty word permits success without positive dimensions. -/
@[expose] def emptyWordSuccess : IncomparableEncoding Unit Unit Unit Unit 0 0 where
  code := {emptyWord}
  incomparable := by
    intro x hx y hy hne
    exact (hne (Subsingleton.elim _ _)).elim
  encode _ _ _ _ := some ⟨emptyWord, by simp⟩

/-- The empty-word singleton returns a successful empty word. -/
theorem zero_length_zero_radix_success :
    emptyWordSuccess.value () () () () = some emptyWord := by rfl

/-- A nonempty word over an empty alphabet cannot be returned by any encoding. -/
theorem positive_length_zero_radix_failure (enc : IncomparableEncoding Unit Unit Unit Unit 1 0) :
    enc.encode () () () () = none := by
  cases enc.encode () () () () with
  | none => rfl
  | some x => exact Fin.elim0 (x.val 0)

end GXMSS.Encoding.IncomparableEncodingProbe
