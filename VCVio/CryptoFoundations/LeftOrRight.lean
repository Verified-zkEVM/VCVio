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

* **Left-or-right, not real-or-random.** The adversary chooses both messages and the hidden bit
  picks the one encrypted, as in the paper's game `Hide_β` (`fig:games` of the leanSeal paper),
  whose oracle returns `Seal(K, η, M_β)`. The game needs no distribution on messages or
  ciphertexts, which a real-or-random game would sample from, and a pair `(m, m)` is an ordinary
  encryption query, so one oracle gives multi-message chosen-plaintext security. A proof usually
  moves each branch to one ideal game whose view does not depend on the bit; the advantage, the
  distance between the two branches, is then at most twice the distance from a branch to that
  game, which is the factor `2` of the paper's hiding theorem (`thm:hiding`).
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
* **A cap is a handler of its own.** Some games count accepted requests inside the challenger
  instead: after `qEnc` accepted pairs, every further request is answered with `none`.
  `LeftOrRight.cap leak qEnc so` puts any challenge handler `so` behind such a cap, with the
  number of accepted pairs as state in `StateT ℕ`, and `LeftOrRight.cappedOracle` is the oracle
  behind the cap. Only accepted pairs, those with equal leakage, move the counter: a pair with
  unequal leakage is answered with `none` as before and costs nothing.

## Main definitions

* `LeftOrRight.spec`: the challenge interface.
* `LeftOrRight.oracle`: the left-or-right challenge oracle at a hidden bit.
* `LeftOrRight.cap`: a challenge handler behind a cap on the number of accepted pairs.
* `LeftOrRight.cappedOracle`: the challenge oracle behind such a cap.
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

/-! ## The capped challenger -/

section cap

variable {M : Type u} {C : Type} {Λ : Type x} [DecidableEq Λ] {m : Type → Type w} [Monad m]

/-- The challenge handler `so` behind a cap of `qEnc` accepted pairs. The state counts the pairs
accepted so far. A pair `(m₀, m₁)` with `leak m₀ = leak m₁`, asked while fewer than `qEnc` pairs
have been accepted, is accepted: it advances the counter and is answered by `so`. Every other
pair, one with unequal leakage or one asked after `qEnc` accepted pairs, is answered with `none`
and leaves the counter unchanged. -/
@[expose]
def cap (leak : M → Λ) (qEnc : ℕ) (so : QueryImpl (spec M C) m) :
    QueryImpl (spec M C) (StateT ℕ m) := fun mm => do
  let j ← get
  if leak mm.1 = leak mm.2 ∧ j < qEnc then
    set (j + 1)
    monadLift (so mm)
  else pure none

/-- The capped left-or-right challenge oracle at hidden bit `b`: the oracle
`LeftOrRight.oracle enc leak b` behind a cap of `qEnc` accepted pairs (`LeftOrRight.cap`). Run
from the counter `0`, it answers the first `qEnc` pairs with equal leakage by encrypting the
message that `b` selects, and every other pair with `none`. -/
@[expose]
def cappedOracle (enc : M → m C) (leak : M → Λ) (qEnc : ℕ) (b : Bool) :
    QueryImpl (spec M C) (StateT ℕ m) :=
  cap leak qEnc (oracle enc leak b)

variable [LawfulMonad m] (leak : M → Λ) (qEnc : ℕ)

/-- The capped handler on a pair from the counter `j`, by cases on acceptance. -/
lemma run_cap_apply (so : QueryImpl (spec M C) m) (mm : M × M) (j : ℕ) :
    (cap leak qEnc so mm).run j =
      if leak mm.1 = leak mm.2 ∧ j < qEnc then (·, j + 1) <$> so mm else pure (none, j) := by
  simp only [cap, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp

/-- A pair with equal leakage, asked below the cap, is answered by the handler and advances the
counter. -/
lemma run_cap_apply_of_leak_eq_of_lt (so : QueryImpl (spec M C) m) {m₀ m₁ : M} {j : ℕ}
    (h : leak m₀ = leak m₁) (hj : j < qEnc) :
    (cap leak qEnc so (m₀, m₁)).run j = (·, j + 1) <$> so (m₀, m₁) := by
  simp [run_cap_apply, h, hj]

/-- A pair with unequal leakage is answered with `none` and leaves the counter unchanged. -/
lemma run_cap_apply_of_leak_ne (so : QueryImpl (spec M C) m) {m₀ m₁ : M} (j : ℕ)
    (h : leak m₀ ≠ leak m₁) :
    (cap leak qEnc so (m₀, m₁)).run j = pure (none, j) := by
  simp [run_cap_apply, h]

/-- Once `qEnc` pairs have been accepted, every pair is answered with `none`. -/
lemma run_cap_apply_of_le (so : QueryImpl (spec M C) m) (mm : M × M) {j : ℕ} (hj : qEnc ≤ j) :
    (cap leak qEnc so mm).run j = pure (none, j) := by
  simp [run_cap_apply, Nat.not_lt.mpr hj]

/-- The capped oracle on a pair from the counter `j`, by cases on acceptance. -/
lemma run_cappedOracle_apply (enc : M → m C) (b : Bool) (m₀ m₁ : M) (j : ℕ) :
    (cappedOracle enc leak qEnc b (m₀, m₁)).run j =
      if leak m₀ = leak m₁ ∧ j < qEnc then
        (fun c => (some c, j + 1)) <$> enc (if b then m₁ else m₀)
      else pure (none, j) := by
  rw [cappedOracle, run_cap_apply]
  by_cases h : leak m₀ = leak m₁ ∧ j < qEnc
  · rw [ite_eq_left h, ite_eq_left h, oracle_apply_of_leak_eq enc leak b h.1, Functor.map_map]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Below the cap, the capped oracle answers as the oracle `LeftOrRight.oracle`: a pair with
equal leakage by the encryption, any other pair by `none`. -/
lemma run'_cappedOracle_apply_of_lt (enc : M → m C) (b : Bool) (mm : M × M) {j : ℕ}
    (hj : j < qEnc) : (cappedOracle enc leak qEnc b mm).run' j = oracle enc leak b mm := by
  by_cases h : leak mm.1 = leak mm.2 <;>
    simp [cappedOracle, StateT.run'_eq, run_cap_apply, oracle, h, hj]

end cap

end LeftOrRight
