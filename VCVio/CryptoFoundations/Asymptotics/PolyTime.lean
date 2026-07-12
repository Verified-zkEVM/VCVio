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
`VCVio.CryptoFoundations.Asymptotics.Security`: `SecurityGame.secureAgainstPolyTime`
instantiates the abstract `isPPT` slot of `SecurityGame.secureAgainst` with
`OracleComp.IsPolyTime`, and the per-query-loss former
`secureAgainstPolyTime_of_advantage_le_mul_totalQueries` is where the query-bound
conjunct of the certificate does quantitative work. Concrete game formers over both
adversary presentations (programs and machines) live in
`VCVio.CryptoFoundations.Asymptotics.Game.Challenger` and `….Game.TwoPhase`.
-/

open OracleComp OracleSpec Computability ENNReal

variable {ι : ℕ → Type} [∀ n, DecidableEq (ι n)]

namespace SecurityGame

/-- Security against Turing-machine-grounded polynomial-time adversaries at the pinned
canonical boundaries `bd`: `SecurityGame.secureAgainst` at the `isPPT` predicate
`OracleComp.IsPolyTime bd`. The boundary data is an explicit parameter of the security
notion, per the statement-site discipline of the model. -/
abbrev secureAgainstPolyTime {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
    (bd : BoundaryData spec α β)
    (g : SecurityGame ((n : ℕ) → α n → OracleComp (spec n) (β n))) : Prop :=
  g.secureAgainst (OracleComp.IsPolyTime bd)

/-- Security of a game over bundled machine adversaries: every `MachineAdversary bd`
has negligible advantage. A machine adversary carries its own polynomial-time
witnesses — the four step-machine families and the round budget are fields of the
bundle — so the `isPPT` slot of `SecurityGame.secureAgainst` is trivially `True`;
quantifying over the adversary type is already quantifying over the polynomial-time
class. -/
abbrev secureAgainstMachines {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
    {bd : BoundaryData spec α β} (g : SecurityGame (MachineAdversary bd)) : Prop :=
  g.secureAgainst fun _ => True

/-- **Per-query loss composes with the polynomial round budget**: a game whose advantage
against every `k`-total-query-bounded family is at most `k * ε n` for negligible `ε` is
secure against all polynomial-time families. This is where the query-bound conjunct of
`OracleComp.IsPolyTime` and the `steps` polynomial do quantitative work: the adversary's
polynomially many queries turn per-query loss into `poly * negligible = negligible`. -/
theorem secureAgainstPolyTime_of_advantage_le_mul_totalQueries
    {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type} (bd : BoundaryData spec α β)
    (g : SecurityGame ((n : ℕ) → α n → OracleComp (spec n) (β n)))
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    (hadv : ∀ (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) (k : ℕ → ℕ),
      (∀ n x, OracleComp.IsTotalQueryBound (oa n x) (k n)) →
      ∀ n, g.advantage oa n ≤ (k n : ℝ≥0∞) * ε n) :
    g.secureAgainstPolyTime bd := by
  rintro oa ⟨w⟩
  exact negligible_of_le (hadv oa (fun n => w.A.steps.eval n) w.queryBound)
    (negligible_polynomial_mul hε w.A.steps)

end SecurityGame
