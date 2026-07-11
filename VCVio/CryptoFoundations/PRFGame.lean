/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.OracleComp.Coinductive.WireK

/-!
# Asymptotic PRF Security as a Stateful-Responder Game

The single-scheme distinguishing advantage of `VCVio.CryptoFoundations.PRF` lifted to the
asymptotic family layer, and presented as a **dynamical system**: the ideal PRF challenger is
a genuinely stateful probabilistic **responder** (`ProbResponder`) whose state is the lazy
random-oracle cache and whose per-query answer is drawn *jointly* with the cache update.
This is the first game-layer consumer of the stateful-responder machinery — the memoryless
`ProbHandler` embedding used by every prior game cannot express a cache whose stored entry
must equal the very answer it returned.

- `PPTPRFAdversary D R`: the oracle-access distinguisher family (one program per parameter).
- `prfRealExpFamily` / `prfIdealExpFamily`: the real (queries `F_k`) and ideal (queries a lazy
  random oracle) experiments as `ProbComp Bool` families — the definitional home of advantage.
- `prfSecurityGame` / `PRFSecure`: the distinguishing game via `SecurityGame.ofBoolDistGame`
  and its security against a class of distinguishers.
- `prfIdealResponder`: the ideal challenger as a `ProbResponder` (state = RO cache).
- `evalDist_prfIdealExpFamily_eq`: the **games-as-dynamical-systems** identity — the ideal
  experiment's output distribution *is* the state-marginalized `SPMF` run of the distinguisher
  against the ideal responder, from the empty cache. This is the payoff of the stateful-responder
  bridge `ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl`.

The advantage former reuses `ProbComp.boolDistAdvantage`, so the PRF game slots into the same
reduction/game-hopping meta-theorems as every other `SecurityGame`.

## Polynomial-time note

Unlike a PRG distinguisher (a coin-tape program over `coinSpec`), a PRF distinguisher carries
*oracle access* to a candidate function `D →ₒ R`, so its interface is the compound spec
`unifSpec + (D →ₒ R)`. The canonical fixed-width boundary encoding of that compound interface —
the `BoundaryData` needed to phrase `OracleComp.IsPolyTime` for oracle-access adversaries — is
not yet built, so `PRFSecure` is quantified over an abstract efficiency predicate `isPPT`,
matching the abstract-`isPPT` design of `SecurityGame.secureAgainst`. Instantiating `isPPT` with
a concrete machine-model boundary for the compound oracle spec is the deferred piece.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace PRFScheme

variable {K D R : ℕ → Type}

/-- An asymptotic PRF distinguisher family: at each security parameter a program with oracle
access to uniform sampling plus a candidate function `D n →ₒ R n`, guessing whether the function
is the real keyed PRF or a truly random function. -/
def PPTPRFAdversary (D R : ℕ → Type) := (n : ℕ) → PRFAdversary (D n) (R n)

/-- Real PRF experiment family: at each parameter, sample a key and let the distinguisher query
`F_k` (memorylessly, since the key is fixed). -/
noncomputable def prfRealExpFamily (F : (n : ℕ) → PRFScheme (K n) (D n) (R n))
    (A : PPTPRFAdversary D R) (n : ℕ) : ProbComp Bool :=
  (F n).prfRealExp (A n)

/-- Ideal PRF experiment family: at each parameter, let the distinguisher query a lazy random
oracle (a consistent random function realized as a cache). -/
noncomputable def prfIdealExpFamily [∀ n, DecidableEq (D n)] [∀ n, SampleableType (R n)]
    (A : PPTPRFAdversary D R) (n : ℕ) : ProbComp Bool :=
  prfIdealExp (A n)

/-- The asymptotic PRF distinguishing game: advantage is the distinguishing advantage between the
real and ideal experiments (`ProbComp.boolDistAdvantage`), packaged with
`SecurityGame.ofBoolDistGame`. -/
noncomputable def prfSecurityGame [∀ n, DecidableEq (D n)] [∀ n, SampleableType (R n)]
    (F : (n : ℕ) → PRFScheme (K n) (D n) (R n)) : SecurityGame (PPTPRFAdversary D R) :=
  SecurityGame.ofBoolDistGame (prfRealExpFamily F) prfIdealExpFamily

/-- **PRF security**: every distinguisher family in the efficiency class `isPPT` has negligible
advantage in the PRF distinguishing game. The efficiency class is abstract because the
machine-model boundary for oracle-access adversaries over the compound spec `unifSpec + (D →ₒ R)`
is deferred (see the module docstring). -/
def PRFSecure [∀ n, DecidableEq (D n)] [∀ n, SampleableType (R n)]
    (F : (n : ℕ) → PRFScheme (K n) (D n) (R n))
    (isPPT : PPTPRFAdversary D R → Prop) : Prop :=
  (prfSecurityGame F).secureAgainst isPPT

/-! ## The ideal challenger as a stateful responder

The ideal PRF challenger *is* a dynamical system: a stateful probabilistic responder whose
state is the random-oracle cache and whose answer to each query is drawn jointly with the cache
update. This is the game's wiring data in the coalgebraic presentation. -/

/-- The ideal PRF challenger presented as a genuinely stateful probabilistic responder: the state
is the lazy random-oracle cache `(D n →ₒ R n).QueryCache`, and each query jointly draws a
consistent uniform answer and the extended cache (`ProbResponder.ofStateQueryImpl` of the ideal
handler `PRFScheme.prfIdealQueryImpl`). The motivating instance of a challenger whose answer and
successor state must be drawn together. -/
noncomputable def prfIdealResponder [∀ n, DecidableEq (D n)] [∀ n, SampleableType (R n)]
    (n : ℕ) : ProbResponder (PRFOracleSpec (D n) (R n)) :=
  .ofStateQueryImpl (prfIdealQueryImpl (D := D n) (R := R n))

/-- **The ideal PRF game is the ideal responder's run** (games as dynamical systems): the ideal
experiment's output distribution *is* the state-marginalized `SPMF` run of the distinguisher
against the ideal responder, started from the empty cache. The `ProbComp` presentation (where the
distinguishing advantage is computed) and the `ProbResponder` presentation (the dynamical-system
wiring) compute one and the same distribution — via the stateful-responder probability bridge
`ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl`. -/
theorem evalDist_prfIdealExpFamily_eq [∀ n, DecidableEq (D n)] [∀ n, SampleableType (R n)]
    (A : PPTPRFAdversary D R) (n : ℕ) :
    𝒟[prfIdealExpFamily A n] =
      Prod.fst <$> (simulateQ (prfIdealResponder n).toQueryImpl (A n)).run
        (∅ : (D n →ₒ R n).QueryCache) := by
  rw [prfIdealExpFamily, prfIdealExp, StateT.run'_eq, evalDist_map,
    ← ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl]
  rfl

end PRFScheme
