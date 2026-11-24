/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.Schemes.MerkleDamgard

/-! # Merkle–Damgård over one-bit blocks

Checks for `VCVio.Schemes.MerkleDamgard` with blocks and chaining values in `Bool`.

No function `ℕ → Bool` is injective, so the security theorems cannot assume that the length
encoding is injective; they assume only that it separates the lengths of the messages the
adversary outputs. With `encodeLen n = decide (n = 0)` this holds for adversaries whose messages
have at most one block, and the theorem applies to every such adversary.

The compression function `fun p => p.1 || p.2` makes the messages `[]` and `[true]` collide. The
named reduction turns that collision into a collision of the compression function, checked by
evaluation. Conjunction makes the equal-length messages `[true, false]` and `[false, false]`
collide, which exercises the finder's equal-length branch.
-/

public section

open OracleComp CollisionResistance MerkleDamgard

namespace MerkleDamgardTest

/-- No length encoding into one-bit blocks is injective. -/
theorem not_injective_encodeLen (encodeLen : ℕ → Bool) : ¬ Function.Injective encodeLen :=
  not_injective_infinite_finite encodeLen

/-- A length encoding into one bit: whether the message is empty. -/
def encodeLen (n : ℕ) : Bool := decide (n = 0)

/-- The one-bit length encoding separates the lengths `0` and `1`. -/
theorem encodeLen_sep {a b : ℕ} (ha : a < 2) (hb : b < 2) (h : encodeLen a = encodeLen b) :
    a = b := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp_all [encodeLen]

/-- The security theorem applies to every adversary whose messages have at most one block. -/
theorem crAdvantage_le_of_length_lt_two (h : Bool × Bool → Bool) (iv : Bool)
    (adversary : CRAdversary (List Bool))
    (hlen : ∀ msgs ∈ support (m := ProbComp) adversary,
      msgs.1.length < 2 ∧ msgs.2.length < 2) :
    crAdvantage (hash h iv encodeLen) adversary ≤
      crAdvantage h (crReduction h iv encodeLen adversary) :=
  crAdvantage_le_crAdvantage_crReduction h iv encodeLen adversary fun msgs hmem =>
    encodeLen_sep (hlen msgs hmem).1 (hlen msgs hmem).2

/-- The compression function of the examples below. -/
def compress (p : Bool × Bool) : Bool := p.1 || p.2

/-- `[]` and `[true]` collide under the Merkle–Damgård hash of `compress`. -/
theorem hash_nil_eq_hash_true :
    hash compress true encodeLen [] = hash compress true encodeLen [true] := by
  decide

/-- The collision finder maps the colliding messages to a collision of `compress`. -/
theorem collisionFinder_nil_true :
    let p := collisionFinder compress true encodeLen [] [true]
    p.1 ≠ p.2 ∧ compress p.1 = compress p.2 := by
  decide

/-- The adversary that outputs the colliding pair `([], [true])`. -/
def collidingAdversary : CRAdversary (List Bool) := (pure ([], [true]) : ProbComp _)

/-- The theorem applies to `collidingAdversary`. -/
example :
    crAdvantage (hash compress true encodeLen) collidingAdversary ≤
      crAdvantage compress (crReduction compress true encodeLen collidingAdversary) :=
  crAdvantage_le_of_length_lt_two compress true collidingAdversary fun msgs hmem => by
    simp only [collidingAdversary, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    decide

/-- The compression function of the equal-length example. -/
def compressAnd (p : Bool × Bool) : Bool := p.1 && p.2

/-- `[true, false]` and `[false, false]` have the same length and collide under the
Merkle–Damgård hash of `compressAnd`. -/
theorem hash_true_false_eq_hash_false_false :
    hash compressAnd true encodeLen [true, false] =
      hash compressAnd true encodeLen [false, false] := by
  decide

/-- On equal-length colliding messages the finder returns the first compression inputs that
differ yet hash alike. -/
theorem collisionFinder_true_false_false_false :
    collisionFinder compressAnd true encodeLen [true, false] [false, false] =
      ((true, false), (false, false)) := by
  decide

end MerkleDamgardTest
