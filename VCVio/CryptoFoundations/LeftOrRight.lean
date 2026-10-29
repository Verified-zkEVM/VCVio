/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# The left-or-right challenge oracle

This file defines the challenge interface `LeftOrRight.spec M C := M × M →ₒ Option C` of
left-or-right indistinguishability games and its oracle `LeftOrRight.oracle enc leak b`. A query
is a pair of messages `(m₀, m₁)`. When the two messages have the same leakage, the oracle answers
with `some c` for a ciphertext `c` drawn from `enc (if b then m₁ else m₀)`; otherwise it answers
`none`.

* **The key enters through `enc`.** The oracle takes an encryption function `enc : M → m C`, not
  a scheme and a key. A game supplies whatever its scheme encrypts with: `dem.encrypt k` under a
  uniform key `k` for a data encapsulation mechanism, `encrypt pk` for a public-key scheme, or an
  encryption under a key derived elsewhere in the game. The oracle is therefore shared by every
  left-or-right game, whatever its key distribution.
* **Admissibility is equal leakage.** A pair is admissible when `leak m₀ = leak m₁` for a leakage
  function `leak : M → Λ`. Left-or-right security is relative to an equivalence relation on
  messages, the information that a ciphertext may reveal, and every equivalence relation is
  equal leakage under its quotient map, so a leakage function loses no generality. It also keeps
  the exchange of the two messages a symmetry of the oracle (`LeftOrRight.oracle_apply_swap`).
  Variable-length encryption uses the message length; fixed-length encryption uses
  `leak := fun _ => ()`, under which every pair is admissible (`LeftOrRight.oracle_unit_apply`).
* **Inadmissible pairs are answered with `none`.** They are not excluded by a predicate on
  adversaries, so the oracle is total and a reduction forwards its adversary's challenge queries
  without proving that they are admissible.
* **The oracle does not count queries.** A query budget is a predicate on the adversary, such as
  an `OracleComp.IsQueryBoundP` bound on the challenge summand of its oracle specification.
-/

public section

open OracleSpec

universe u v w x

namespace LeftOrRight

/-- The challenge interface of a left-or-right game: a query is a pair of messages and its answer
is a ciphertext, or `none` when the pair is not admissible. -/
abbrev spec (M : Type u) (C : Type v) : OracleSpec (M × M) :=
  M × M →ₒ Option C

variable {M : Type u} {C : Type v} {Λ : Type x} {m : Type v → Type w} [Monad m]

/-- The left-or-right challenge oracle at hidden bit `b`, for an encryption function `enc` and a
leakage function `leak`. A pair `(m₀, m₁)` with `leak m₀ = leak m₁` is answered by encrypting
`m₁` when `b = true` and `m₀` when `b = false`; any other pair is answered with `none`. -/
@[expose]
def oracle [DecidableEq Λ] (enc : M → m C) (leak : M → Λ) (b : Bool) :
    QueryImpl (spec M C) m := fun mm =>
  if leak mm.1 = leak mm.2 then some <$> enc (if b then mm.2 else mm.1) else pure none

variable [DecidableEq Λ] (enc : M → m C) (leak : M → Λ)

/-- The oracle on a query, by cases on admissibility. -/
lemma oracle_apply (b : Bool) (m₀ m₁ : M) :
    oracle enc leak b (m₀, m₁) =
      if leak m₀ = leak m₁ then some <$> enc (if b then m₁ else m₀) else pure none :=
  rfl

/-- An admissible pair is answered by encrypting the message that the hidden bit selects. -/
@[simp]
lemma oracle_apply_of_leak_eq (b : Bool) {m₀ m₁ : M} (h : leak m₀ = leak m₁) :
    oracle enc leak b (m₀, m₁) = some <$> enc (if b then m₁ else m₀) := by
  simp [oracle_apply, h]

/-- A pair whose messages leak differently is answered with `none`. -/
@[simp]
lemma oracle_apply_of_leak_ne (b : Bool) {m₀ m₁ : M} (h : leak m₀ ≠ leak m₁) :
    oracle enc leak b (m₀, m₁) = pure none := by
  simp [oracle_apply, h]

/-- Exchanging the two messages of a query is the same as flipping the hidden bit. -/
lemma oracle_apply_swap (b : Bool) (m₀ m₁ : M) :
    oracle enc leak b (m₁, m₀) = oracle enc leak (!b) (m₀, m₁) := by
  by_cases h : leak m₀ = leak m₁
  · rw [oracle_apply_of_leak_eq enc leak b h.symm, oracle_apply_of_leak_eq enc leak (!b) h]
    cases b <;> rfl
  · rw [oracle_apply_of_leak_ne enc leak b (Ne.symm h), oracle_apply_of_leak_ne enc leak (!b) h]

/-- Without leakage every pair is admissible, so the oracle never answers `none`. -/
@[simp]
lemma oracle_unit_apply (b : Bool) (mm : M × M) :
    oracle enc (fun _ => ()) b mm = some <$> enc (if b then mm.2 else mm.1) := by
  simp [oracle]

end LeftOrRight
