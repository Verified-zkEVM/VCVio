/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SecExp
public import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Asymptotic Security Games

This file defines asymptotic security games whose advantage function is abstract — not tied to
any specific experiment. The same meta-theorems (reductions, game-hopping, hybrid arguments)
therefore apply to success, bias and distinguishing advantages alike.

## Main Definitions

- `SecurityGame Adv`: An advantage function `Adv → ℕ → ℝ≥0∞` with quantified security.

## Main Results

- `SecurityGame.secureAgainst_of_reduction`: Basic security reduction (tight).
- `SecurityGame.secureAgainst_of_poly_reduction`: Polynomial-loss security reduction.
- `SecurityGame.secureAgainst_of_close`: Game-hopping step.
- `SecurityGame.secureAgainst_of_hybrid`: Hybrid argument over a chain of games.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Filter

/-! ## Asymptotic Security Games

A security game is parameterized by an adversary type. The advantage function maps
each adversary and security parameter to a non-negative extended real.

The predicate `isPPT` is left abstract; users specialize it to `PolyQueries` or other
efficiency notions as appropriate. -/

/-- An asymptotic security game: maps each adversary and security parameter to an
advantage value. It stores the advantage rather than an experiment, so the same meta-theorems
work for success, bias and distinguishing advantages. -/
structure SecurityGame (Adv : Type*) where
  advantage : Adv → ℕ → ℝ≥0∞

namespace SecurityGame

variable {Adv : Type*}

/-- A game is **secure against a class of adversaries** (specified by `isPPT`)
if every adversary in that class has negligible advantage. -/
def secureAgainst (g : SecurityGame Adv) (isPPT : Adv → Prop) : Prop :=
  ∀ A, isPPT A → negligible (g.advantage A)

/-! ### Security reductions -/

/-- Basic security reduction: if there is a map `reduce : Adv → Adv'` that
preserves efficiency and the advantage of `g` is pointwise ≤ the advantage of `g'`
on the reduced adversary, then security of `g'` implies security of `g`. -/
theorem secureAgainst_of_reduction {Adv' : Type*}
    {g : SecurityGame Adv} {g' : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hbound : ∀ A n, g.advantage A n ≤ g'.advantage (reduce A) n)
    (hsecure : g'.secureAgainst isPPT') :
    g.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hbound A) (hsecure (reduce A) (hreduce A hA))

/-! ### Game hopping -/

/-- **Game-hopping step**: if the advantage of `g₁` at every security parameter is at most the
advantage of `g₂` plus some negligible `ε`, and `g₂` is secure, then `g₁` is secure.

This is the fundamental lemma for game-hopping proofs: each "hop" from `g₁` to `g₂`
introduces at most `ε(n)` advantage loss, and `ε` is absorbed because negligible functions
are closed under addition. -/
theorem secureAgainst_of_close
    {g₁ g₂ : SecurityGame Adv} {isPPT : Adv → Prop}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    (hclose : ∀ A, isPPT A → ∀ n, g₁.advantage A n ≤ g₂.advantage A n + ε n)
    (hsecure : g₂.secureAgainst isPPT) :
    g₁.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hclose A hA) (negligible_add (hsecure A hA) hε)

/-- Game-hopping step with a reduction: if the advantage of `g₁` with adversary `A` is at most
the advantage of `g₂` with reduced adversary plus `ε`, then security of `g₂` (against the
target class) implies security of `g₁`. Combines reduction and game hop. -/
theorem secureAgainst_of_close_reduction {Adv' : Type*}
    {g₁ : SecurityGame Adv} {g₂ : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hclose : ∀ A, isPPT A → ∀ n,
      g₁.advantage A n ≤ g₂.advantage (reduce A) n + ε n)
    (hsecure : g₂.secureAgainst isPPT') :
    g₁.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hclose A hA)
    (negligible_add (hsecure (reduce A) (hreduce A hA)) hε)

/-! ### Polynomial-loss reductions -/

/-- **Polynomial-loss security reduction**: if there is a reduction `reduce : Adv → Adv'`
that preserves efficiency and the advantage of `g` is at most `loss(n)` times the
advantage of `g'` on the reduced adversary, then security of `g'` implies security of `g`.

This handles reductions where the adversary's advantage is amplified by a polynomial factor,
e.g., from a hybrid argument guessing which of `poly(n)` steps to exploit. -/
theorem secureAgainst_of_poly_reduction {Adv' : Type*}
    {g : SecurityGame Adv} {g' : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    {loss : Polynomial ℕ}
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hbound : ∀ A n, g.advantage A n ≤ ↑(loss.eval n) * g'.advantage (reduce A) n)
    (hsecure : g'.secureAgainst isPPT') :
    g.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hbound A)
    (negligible_polynomial_mul (hsecure (reduce A) (hreduce A hA)) loss)

/-- Combined game-hopping step with polynomial advantage loss and reduction. -/
theorem secureAgainst_of_close_poly_reduction {Adv' : Type*}
    {g₁ : SecurityGame Adv} {g₂ : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    {loss : Polynomial ℕ}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hclose : ∀ A, isPPT A → ∀ n,
      g₁.advantage A n ≤ ↑(loss.eval n) * g₂.advantage (reduce A) n + ε n)
    (hsecure : g₂.secureAgainst isPPT') :
    g₁.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hclose A hA)
    (negligible_add (negligible_polynomial_mul (hsecure (reduce A) (hreduce A hA)) loss) hε)

/-! ### Hybrid argument -/

/-- **Hybrid argument**: given `k + 1` games indexed by `0, 1, ..., k`, if consecutive
games differ by at most `ε(n)` in advantage and the final game is secure, then the
first game is also secure.

The total advantage loss is at most `k · ε(n)`, which is negligible since `ε` is
negligible and `k` is constant. -/
theorem secureAgainst_of_hybrid
    {games : ℕ → SecurityGame Adv}
    {isPPT : Adv → Prop}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    {k : ℕ}
    (hconsec : ∀ j < k, ∀ A, isPPT A → ∀ n,
      (games j).advantage A n ≤ (games (j + 1)).advantage A n + ε n)
    (hsecure : (games k).secureAgainst isPPT) :
    (games 0).secureAgainst isPPT := by
  induction k with
  | zero => exact hsecure
  | succ k ih =>
    exact ih (fun j _ => hconsec j (by omega))
      (secureAgainst_of_close hε (hconsec k (by omega)) hsecure)

end SecurityGame
