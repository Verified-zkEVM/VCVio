/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Binary recursive inner-product protocol

The protocol is the binary-fold specialization of §4.2 of Bootle, Cerulli,
Chaidos, Groth, and Petit, EUROCRYPT 2016. Group operations are additive:
`a • g` denotes the source paper's `g^a`. A depth `r` statement has
`2^(r+1)` coordinates and reveals two-coordinate witnesses at depth zero.

This module specifies verification, including the cross-term messages and
nonzero challenges. It does not assert knowledge soundness.
-/

public section

namespace InnerProduct

/-- Recursive coordinate indexing, with two coordinates in a terminal witness. -/
@[expose]
def Index : Nat → Type
  | 0 => Fin 2
  | r + 1 => Bool × Index r

instance instFintypeIndex (r : Nat) : Fintype (Index r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype (Fin 2))
  | succ r ih => exact inferInstanceAs (Fintype (Bool × Index r))

instance instDecidableEqIndex (r : Nat) : DecidableEq (Index r) := by
  induction r with
  | zero => exact inferInstanceAs (DecidableEq (Fin 2))
  | succ r ih => exact inferInstanceAs (DecidableEq (Bool × Index r))

/-- Two commitment bases and the claimed commitment and inner-product values. -/
structure Statement (F G : Type) (r : Nat) where
  /-- Bases for the commitment to the first opening vector. -/
  g : Index r → G
  /-- Bases for the commitment to the second opening vector. -/
  h : Index r → G
  /-- Commitment to the first opening vector. -/
  A : G
  /-- Commitment to the second opening vector. -/
  B : G
  /-- Claimed scalar inner product of the two openings. -/
  z : F

/-- Openings of both commitments. -/
structure Witness (F : Type) (r : Nat) where
  /-- Opening in the first commitment basis. -/
  a : Index r → F
  /-- Opening in the second commitment basis. -/
  b : Index r → F

/-- The nonconstant coefficients sent before a binary folding challenge. -/
structure FoldMessage (F G : Type) where
  /-- Coefficient with index −1 in the first commitment expression. -/
  aLow : G
  /-- Coefficient with index +1 in the first commitment expression. -/
  aHigh : G
  /-- Coefficient with index −1 in the second commitment expression. -/
  bLow : G
  /-- Coefficient with index +1 in the second commitment expression. -/
  bHigh : G
  /-- Coefficient with index −1 in the scalar inner-product expression. -/
  zLow : F
  /-- Coefficient with index +1 in the scalar inner-product expression. -/
  zHigh : F

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

open scoped BigOperators

/-- Opening and inner-product equations for a statement. -/
@[expose]
def Valid {r : Nat} (s : Statement F G r) (w : Witness F r) : Prop :=
  (∑ i, w.a i • s.g i) = s.A ∧
  (∑ i, w.b i • s.h i) = s.B ∧ (∑ i, w.a i * w.b i) = s.z

/-- The reduced statement after the nonzero challenge `x`. -/
@[expose]
def fold {r : Nat} (s : Statement F G (r + 1)) (msg : FoldMessage F G)
    (x : Fˣ) : Statement F G r where
  g i := ((↑x : F)⁻¹) • s.g (false, i) + ((↑x : F)⁻¹ ^ 2) • s.g (true, i)
  h i := (↑x : F) • s.h (false, i) + ((↑x : F) ^ 2) • s.h (true, i)
  A := ((↑x : F)⁻¹) • msg.aLow + s.A + (↑x : F) • msg.aHigh
  B := (↑x : F) • msg.bLow + s.B + ((↑x : F)⁻¹) • msg.bHigh
  z := (↑x : F) * msg.zLow + s.z + ((↑x : F)⁻¹) * msg.zHigh

/-- Public messages, challenges, and the final revealed witness. -/
inductive Transcript (F G : Type) [Field F] : Nat → Type where
  | terminal (w : Witness F 0) : Transcript F G 0
  | step {r : Nat} (msg : FoldMessage F G) (challenge : Fˣ)
      (tail : Transcript F G r) : Transcript F G (r + 1)

/-- Verifier acceptance, computed by folding the statement along the transcript. -/
@[expose]
def accepts [DecidableEq F] [DecidableEq G] :
    {r : Nat} → Statement F G r → Transcript F G r → Bool
  | 0, s, .terminal w => decide (
      (∑ i, w.a i • s.g i) = s.A ∧
      (∑ i, w.b i • s.h i) = s.B ∧ (∑ i, w.a i * w.b i) = s.z)
  | _ + 1, s, .step msg challenge tail => accepts (fold s msg challenge) tail

/-- A causal prover after its private seed has been fixed. -/
@[expose]
def Prover (F G : Type) [Field F] : Nat → Type
  | 0 => Witness F 0
  | r + 1 => FoldMessage F G × (Fˣ → Prover F G r)

/-- Prescribed public challenges, one for every remaining round. -/
@[expose]
def Challenges (C : Type) : Nat → Type
  | 0 => Unit
  | r + 1 => C × Challenges C r

/-- Execute the seeded prover on prescribed challenges. Future challenges are
only passed to the continuation after its current message has been fixed. -/
@[expose]
def respond : {r : Nat} → Prover F G r → Challenges Fˣ r → Transcript F G r
  | 0, w, _ => .terminal w
  | _ + 1, ⟨msg, next⟩, ⟨x, xs⟩ => .step msg x (respond (next x) xs)

omit [AddCommGroup G] [Module F G] in
/-- The messages preceding the next challenge depend only on the shared prefix. -/
theorem respond_step {r : Nat} (msg : FoldMessage F G) (next : Fˣ → Prover F G r)
    (x : Fˣ) (xs : Challenges Fˣ r) :
    respond (r := r + 1) (msg, next) (x, xs) = .step msg x (respond (next x) xs) := rfl

end InnerProduct
