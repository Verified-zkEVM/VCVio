/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum

/-!
# Arithmetic for a possible FORS concentration argument

Touchard polynomials provide the raw moments of a Poisson load. This file checks the
polynomial values and a sixth-moment scalar inequality only. It does not establish a
Poisson coupling, a concentration theorem, or a bound for adaptive signing transcripts.
-/

public section

namespace SLHDSA.SHAKE128s.ForsMoments

/-- Row `n` of the triangle of Stirling numbers of the second kind, `S(n, 0), …, S(n, n)`,
computed row by row so that kernel evaluation does not unfold the two-term recurrence
exponentially. -/
@[expose] def stirlingRow : Nat → List Nat
  | 0 => [1]
  | n + 1 =>
      let previous := stirlingRow n
      List.ofFn fun k : Fin (n + 2) =>
        k.val * previous.getD k.val 0 +
          match k.val with
          | 0 => 0
          | j + 1 => previous.getD j 0

/-- Entry `k` of `stirlingRow n` is the Stirling number `S(n, k)`, and entries past the row are
zero. -/
theorem stirlingRow_getD (n k : Nat) :
    (stirlingRow n).getD k 0 = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [stirlingRow, Nat.stirlingSecond]
  | succ n ih =>
      have ih' (j : Nat) := ih j
      simp only [List.getD_eq_getElem?_getD] at ih'
      by_cases hk : k < n + 2
      · simp only [stirlingRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk,
          dite_true, Option.getD_some]
        cases k with
        | zero => simp [Nat.stirlingSecond]
        | succ k => simp only [Nat.stirlingSecond, ih']
      · simp only [stirlingRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk,
          dite_false, Option.getD_none]
        exact (Nat.stirlingSecond_eq_zero_of_lt (by omega)).symm

/-- The Touchard polynomial of the given degree evaluated at `mean`,
`∑ k ≤ degree, S(degree, k) * mean ^ k`: the raw moment of that degree of a Poisson variable
with integer mean `mean`. -/
@[expose] def touchard (degree mean : Nat) : Nat :=
  ∑ k ∈ Finset.range (degree + 1), Nat.stirlingSecond degree k * mean ^ k

/-- `touchard` with its Stirling coefficients read from the precomputed `stirlingRow`, the form
used for kernel evaluation. -/
@[expose] def cachedTouchard (degree mean : Nat) : Nat :=
  let row := stirlingRow degree
  ∑ k ∈ Finset.range (degree + 1), row.getD k 0 * mean ^ k

/-- The cached evaluation agrees with `touchard`. -/
theorem touchard_eq_cached (degree mean : Nat) :
    touchard degree mean = cachedTouchard degree mean := by
  simp only [touchard, cachedTouchard, stirlingRow_getD]

end SLHDSA.SHAKE128s.ForsMoments
