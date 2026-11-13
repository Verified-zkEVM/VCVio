/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort
public import VCVio.OracleComp.Constructions.RetryLoop
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Ghost-layer machinery for Fiat-Shamir with aborts: Bodies

The cache-level signing bodies of the CMA-to-NMA hybrid chain (`realSignBody`,
`progSignBody`, `transSignBody`, `simSignBody`), which share the first-success retry loop
`ProbComp.firstSome`. This module opens the hybrid signing-body development and holds its
overview.

## Overview

The development provides the cache-level signing bodies of the CMA-to-NMA
hybrid chain for the Fiat-Shamir-with-aborts transform, together with the
run-level hybrid handlers (`hybridBaseImpl`, `hybridSignImpl`) and the
ghost-layer presentation of the reprogramming bodies used by the Prog → Trans
hop:

* `ghostSignBody` acts on a two-layer cache, writing accepted transcripts to
  the real layer and rejected-attempt programmings to the ghost layer; the
  projections `run_ghostSignBody_overlay` and `run_ghostSignBody_fst` recover
  `progSignBody` and the accepted-only programming loop of `transSignBody`.
* `ghostHybridImpl` instruments the adversary's oracles over the layered cache
  with a monotone bad flag firing on adversarial reads of the ghost layer,
  with per-step projections onto both hybrid games
  (`ghostHybridImpl_proj_prog`, `ghostHybridImpl_proj_trans`) and the
  ghost-domain invariant `ghostHybridImpl_preserves_signed_inv`.

The hybrid experiment itself and the hop lemmas live in the
`FiatShamir.WithAbort.Security` modules.

## Module layout

The development is split along its phases, each module publicly importing its
predecessor: `Bodies` (retry loops and the four signing bodies), `GhostLayer`
(the two-layer cache presentation and the ghost-instrumented handlers),
`Projections` (projections onto both hybrid games and the ghost-domain
invariant), `BodyBounds` (the body-level collision and deferred-sampling
bounds), and `NMAHandler` (the layered ghost-tagged NMA handler).
-/

public section

open OracleComp OracleSpec
open ProbComp (firstSome)
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)
variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))

/-! ## The hybrid signing bodies

All four hybrid games run the adversary against the same uniform-sampling and
random-oracle handlers, differing only in the signing-oracle body. Each body is a
cache-level state transformer on the random-oracle cache. Following Fig. 2 of the
paper (adapted to the bounded restart loop):

- `realSignBody` (Sign): the real signing loop, hashing each attempt's commitment
  through the caching random oracle. Aborted attempts also populate the cache.
- `progSignBody` (Prog): every attempt **overwrites** the cache at `(msg, w)` with a
  fresh uniform challenge, for rejected and accepted attempts alike, removing the
  dependency between the cached challenge and the accept event.
- `transSignBody` (Trans): the loop runs privately on `ids.honestExecution` (no cache
  interaction), and only the accepted transcript is programmed into the cache.
- `simSignBody` (Sim): as `transSignBody` with the per-attempt HVZK simulator in place
  of the honest execution; the secret key is no longer used. -/

/-- Real signing-oracle body: the cache-level semantics of `fsAbortSignLoop` under the
caching random oracle. Each attempt queries the random oracle at `(msg, w)`, so aborted
attempts leave their challenge in the cache exactly as in the real experiment. -/
@[expose] noncomputable def realSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
    (fsAbortSignLoop ids M pk sk msg maxAttempts)

/-- One signing attempt of the all-attempts-reprogramming hybrid: commit honestly, then
overwrite the cache at `(msg, w)` with a fresh uniform challenge before responding. -/
@[expose] noncomputable def progSignAttempt (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Commit × Option Resp) := do
  let (w, st) ← liftM (ids.commit pk sk)
  let c ← (liftM (uniformSample Chal) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
  modify fun cache => cache.cacheQuery (msg, w) c
  let oz ← liftM (ids.respond pk sk st c)
  pure (w, oz)

/-- Signing-oracle body of the all-attempts-reprogramming hybrid (Prog): run the restart
loop with `progSignAttempt`, so every attempt (accepted or rejected) reprograms the
random-oracle cache with a fresh challenge. -/
@[expose] noncomputable def progSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp))
  | 0 => pure none
  | n + 1 => do
    let (w, oz) ← progSignAttempt ids M pk sk msg
    match oz with
    | some z => pure (some (w, z))
    | none => progSignBody pk sk msg n

/-- Shared cache-programming continuation of `transSignBody` and `simSignBody`: program
the accepted transcript's challenge into the cache at `(msg, w)` and return the
signature `(w, z)`; an all-abort loop outcome produces no signature and no programming.

The continuation is a deterministic function of the loop outcome, so the gap between
the two hybrids reduces entirely to the gap between their private loops (see
`measureTVDist_run_transSignBody_simSignBody_le`). -/
@[expose] noncomputable def signProgramCont (msg : M) :
    Option (Commit × Chal × Resp) →
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp))
  | some (w, c, z) => do
    modify fun cache => cache.cacheQuery (msg, w) c
    pure (some (w, z))
  | none => pure none

/-- Signing-oracle body of the accepted-only-reprogramming hybrid (Trans): the restart
loop runs privately on honest executions (`ids.honestExecution`, which samples its own
uniform challenge and never touches the cache); only the accepted transcript is
programmed into the cache. Rejected attempts leave no trace. -/
@[expose] noncomputable def transSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (ids.honestExecution pk sk) maxAttempts) >>= signProgramCont M msg

/-- Signing-oracle body of the simulated hybrid (Sim): as `transSignBody`, with the
per-attempt HVZK simulator replacing the honest execution. The secret key is unused, so
this body can be run by the NMA reduction. -/
@[expose] noncomputable def simSignBody (pk : Stmt) (_sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (sim pk) maxAttempts) >>= signProgramCont M msg

end FiatShamirWithAbort
