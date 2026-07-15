/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Bodies
import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.GhostLayer
import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Projections
import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.BodyBounds
import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.NMAHandler

/-!
# Hybrid signing bodies and ghost-layer machinery for Fiat-Shamir with aborts

Cache-level signing bodies of the CMA-to-NMA hybrid chain for the
Fiat-Shamir-with-aborts transform (`realSignBody`, `progSignBody`,
`transSignBody`, `simSignBody`), together with the run-level hybrid handlers
(`hybridBaseImpl`, `hybridSignImpl`) and the ghost-layer presentation of the
reprogramming bodies used by the Prog → Trans hop:

* `ghostSignBody` acts on a two-layer cache, writing accepted transcripts to
  the real layer and rejected-attempt programmings to the ghost layer; the
  projections `run_ghostSignBody_overlay` and `run_ghostSignBody_fst` recover
  `progSignBody` and the accepted-only programming loop of `transSignBody`.
* `ghostHybridImpl` instruments the adversary's oracles over the layered cache
  with a monotone bad flag firing on adversarial reads of the ghost layer,
  with per-step projections onto both hybrid games
  (`ghostHybridImpl_proj_prog`, `ghostHybridImpl_proj_trans`) and the
  ghost-domain invariant `ghostHybridImpl_preserves_signed_inv`.

The hybrid experiment itself and the hop lemmas live in
`FiatShamir.WithAbort.Security`.

## Module layout

The development is split along its phases: `Bodies` (retry loops and the four
signing bodies), `GhostLayer` (the two-layer cache presentation and the
ghost-instrumented handlers), `Projections` (projections onto both hybrid
games and the ghost-domain invariant), `BodyBounds` (the body-level collision
and deferred-sampling bounds), and `NMAHandler` (the layered ghost-tagged NMA
handler). This umbrella module re-exports all of them.
-/
