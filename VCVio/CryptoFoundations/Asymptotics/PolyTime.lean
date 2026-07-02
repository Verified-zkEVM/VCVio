/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.OracleComp.Coinductive.PolyTime

/-!
# Security Against Polynomial-Time Adversaries

This file connects the Turing-machine-grounded polynomial-time layer
(`PolyTimeAdversary`, `OracleComp.IsPolyTime`) to the asymptotic security games of
`VCVio.CryptoFoundations.Asymptotics.Security`, in both of the intended usage styles:

* **Programs as adversaries**: `SecurityGame.secureAgainstPolyTime` instantiates the
  abstract `isPPT` slot of `SecurityGame.secureAgainst` with `OracleComp.IsPolyTime`.
* **Machines as adversaries**: a concrete one-shot game former `OneShotGame` produces a
  `SecurityGame` over program families (`OneShotGame.toProgGame`) and one directly over
  bundled polynomial-time adversaries (`OneShotGame.toPolyGame`). The connecting lemma
  `OneShotGame.advantage_toPolyGame_eq` shows an implementing adversary has exactly the
  advantage of the implemented program, so security transfers between the layers
  (`OneShotGame.secureAgainst_isPolyTime_of_polyGame`).
-/

universe u v w

open OracleComp OracleSpec Computability

variable {ι : Type} [DecidableEq ι]

namespace SecurityGame

/-- Security against Turing-machine-grounded polynomial-time adversaries:
`SecurityGame.secureAgainst` at the `isPPT` predicate `OracleComp.IsPolyTime`. -/
abbrev secureAgainstPolyTime {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type}
    (g : SecurityGame ((n : ℕ) → α n → OracleComp (spec n) (β n))) : Prop :=
  g.secureAgainst OracleComp.IsPolyTime

end SecurityGame

/-! ## One-shot games over both adversary presentations -/

/-- A one-shot game: sample an input, run the adversary against the game's oracle
implementation, and score the (possibly failed) result. Concrete enough to state the
advantage-transfer lemma between the program and machine presentations of the
adversary, general enough to capture standard single-phase experiments. -/
structure OneShotGame (spec : ℕ → OracleSpec.{0, 0} ι) (α β : ℕ → Type) where
  /-- The game's oracle implementation at each security parameter. -/
  oracle : (n : ℕ) → ProbHandler (spec n)
  /-- The input sampler. -/
  gen : (n : ℕ) → SPMF (α n)
  /-- The scoring of an adversary result (`none` = the run did not resolve). -/
  score : (n : ℕ) → α n → Option (β n) → SPMF Bool

namespace OneShotGame

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type}

/-- The game as a `SecurityGame` over program-family adversaries, via `simulateQ`. -/
noncomputable def toProgGame (G : OneShotGame spec α β) :
    SecurityGame ((n : ℕ) → α n → OracleComp (spec n) (β n)) where
  advantage oa n :=
    (G.gen n >>= fun x =>
      (some <$> simulateQ (G.oracle n) (oa n x)) >>= G.score n x) true

/-- The game as a `SecurityGame` over bundled polynomial-time adversaries, via the
machine run `PolyTimeAdversary.exec`. -/
noncomputable def toPolyGame (G : OneShotGame spec α β) :
    SecurityGame (PolyTimeAdversary spec α β) where
  advantage D n :=
    (G.gen n >>= fun x => D.exec n (G.oracle n) x >>= G.score n x) true

/-- **Advantage transfer**: a polynomial-time adversary implementing a program family
has exactly the program's advantage, by the master transfer equation
`PolyTimeAdversary.exec_eq_of_implements`. -/
theorem advantage_toPolyGame_eq (G : OneShotGame spec α β)
    {D : PolyTimeAdversary spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (h : D.Implements oa) (n : ℕ) :
    G.toPolyGame.advantage D n = G.toProgGame.advantage oa n := by
  refine congrArg (fun p : SPMF Bool => p true) (bind_congr fun x => ?_)
  rw [PolyTimeAdversary.exec_eq_of_implements h]

/-- **Security transfer**: if every bundled polynomial-time adversary has negligible
advantage in the machine-level game, then the program-level game is secure against
`OracleComp.IsPolyTime`. -/
theorem secureAgainst_isPolyTime_of_polyGame (G : OneShotGame spec α β)
    (hsec : ∀ D : PolyTimeAdversary spec α β, negligible (G.toPolyGame.advantage D)) :
    G.toProgGame.secureAgainstPolyTime := by
  rintro oa ⟨D, hImp, -⟩
  have heq : G.toProgGame.advantage oa = G.toPolyGame.advantage D :=
    funext fun n => (G.advantage_toPolyGame_eq hImp n).symm
  exact heq ▸ hsec D

end OneShotGame
