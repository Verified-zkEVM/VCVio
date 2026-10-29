/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.LeftOrRight

/-!
# Left-or-right challenge oracle checks

The challenge oracle over bit strings with length leakage: pairs of equal length are encrypted
under the hidden bit, pairs of different lengths are answered `none`, exchanging the messages
flips the bit, and without leakage no pair is refused.
-/

public section

namespace LeftOrRightTest

/-- A deterministic toy encryption of bit strings that flips every bit. -/
def flipAll (msg : List Bool) : Id (List Bool) := msg.map not

/-- The challenge oracle over bit strings with length leakage. -/
abbrev lengthOracle (b : Bool) : QueryImpl (LeftOrRight.spec (List Bool) (List Bool)) Id :=
  LeftOrRight.oracle flipAll List.length b

/-! ## Admissible pairs -/

example : lengthOracle false ([true, true], [false, true]) = some [false, false] := rfl

example : lengthOracle true ([true, true], [false, true]) = some [true, false] := rfl

example (m₀ m₁ : List Bool) (h : m₀.length = m₁.length) :
    lengthOracle true (m₀, m₁) = some <$> flipAll m₁ :=
  LeftOrRight.oracle_apply_of_leak_eq flipAll List.length true h

/-! ## Inadmissible pairs -/

example (b : Bool) : lengthOracle b ([true], [true, false]) = pure none := by
  cases b <;> rfl

example (b : Bool) (m₀ m₁ : List Bool) (h : m₀.length ≠ m₁.length) :
    lengthOracle b (m₀, m₁) = pure none :=
  LeftOrRight.oracle_apply_of_leak_ne flipAll List.length b h

/-! ## Exchanging the messages -/

example (b : Bool) (m₀ m₁ : List Bool) :
    lengthOracle b (m₁, m₀) = lengthOracle (!b) (m₀, m₁) :=
  LeftOrRight.oracle_apply_swap flipAll List.length b m₀ m₁

example : lengthOracle true ([false], [true]) = lengthOracle false ([true], [false]) := rfl

/-! ## No leakage -/

/-- Without leakage, even pairs of different lengths are encrypted. -/
example : LeftOrRight.oracle flipAll (fun _ => ()) true ([true], [true, false]) =
    some [false, true] := rfl

example (b : Bool) (mm : List Bool × List Bool) :
    LeftOrRight.oracle flipAll (fun _ => ()) b mm =
      some <$> flipAll (if b then mm.2 else mm.1) := by
  simp

end LeftOrRightTest
