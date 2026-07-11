/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.PRG
import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.OracleComp.Coinductive.PolyTime

/-!
# Asymptotic PRG Security

The single-scheme, `ℝ`-valued distinguishing advantage of `VCVio.CryptoFoundations.PRG` lifted to
the asymptotic family layer used by the crypto reductions. A distinguisher is a program family over
the coin oracle (the textbook's random bit tape, so `PRGSecure` can quantify over
`OracleComp.IsPolyTime` families), and the real/ideal experiments interpret those coin queries
uniformly to land in `ProbComp`.

- `PPTPRGAdversary R`: the distinguisher family, one coin-oracle program per parameter.
- `prgRealExpFamily` / `prgIdealExpFamily`: the real (sees `gen s` for uniform seed `s`) and ideal
  (sees a uniform `r`) experiments as `ProbComp Bool` families.
- `prgSecurityGame` / `PRGSecure`: the distinguishing game via `SecurityGame.ofBoolDistGame` and
  its security against polynomial-time distinguishers.

The advantage former reuses the generic `ProbComp.boolDistAdvantage`, so the PRG game slots into the
same reduction/game-hopping meta-theorems as every other `SecurityGame`.
-/

open OracleComp OracleSpec ENNReal

namespace PRGScheme

variable {S R : ℕ → Type}

/-- An asymptotic PRG distinguisher family: at each security parameter a program over the coin
oracle receiving a single value and guessing whether it is a PRG output or uniform. Modeled over
`coinSpec` so `PRGSecure` can demand Turing-machine-grounded polynomial time. -/
def PPTPRGAdversary (R : ℕ → Type) := (n : ℕ) → R n → OracleComp coinSpec Bool

/-- Real PRG experiment family: sample a uniform seed, expand it with the generator, and run the
coin-oracle distinguisher against uniform coins. -/
noncomputable def prgRealExpFamily [∀ n, SampleableType (S n)]
    (prg : (n : ℕ) → PRGScheme (S n) (R n)) (A : PPTPRGAdversary R) (n : ℕ) : ProbComp Bool := do
  let s ← $ᵗ S n
  simulateQ uniformSampleImpl (A n ((prg n).gen s))

/-- Ideal PRG experiment family: run the coin-oracle distinguisher on a uniformly random value. -/
noncomputable def prgIdealExpFamily [∀ n, SampleableType (R n)]
    (A : PPTPRGAdversary R) (n : ℕ) : ProbComp Bool := do
  let r ← $ᵗ R n
  simulateQ uniformSampleImpl (A n r)

/-- The asymptotic PRG distinguishing game: advantage is the distinguishing advantage between the
real and ideal experiments (`ProbComp.boolDistAdvantage`), packaged with
`SecurityGame.ofBoolDistGame`. -/
noncomputable def prgSecurityGame [∀ n, SampleableType (S n)] [∀ n, SampleableType (R n)]
    (prg : (n : ℕ) → PRGScheme (S n) (R n)) : SecurityGame (PPTPRGAdversary R) :=
  SecurityGame.ofBoolDistGame (prgRealExpFamily prg) (prgIdealExpFamily (R := R))

/-- **PRG security**: every polynomial-time distinguisher family — at the pinned
canonical boundary `eR` for the distinguished values, per the statement-site discipline
of the machine model — has negligible advantage in the PRG distinguishing game. -/
def PRGSecure [∀ n, SampleableType (S n)] [∀ n, SampleableType (R n)]
    (eR : Computability.BitEncFam R) (prg : (n : ℕ) → PRGScheme (S n) (R n)) : Prop :=
  (prgSecurityGame prg).secureAgainst
    (OracleComp.IsPolyTime (BoundaryData.coin eR Computability.BitEncFam.bool))

end PRGScheme
