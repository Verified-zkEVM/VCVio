/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.Loss
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.BodyHops
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.CouplingEngine
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.ReadRecording
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.TapeFactorization
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.HopLemmas
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.NMAReduction
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.Assembly

/-!
# EUF-CMA security of Fiat-Shamir with aborts

Statistical CMA-to-NMA reduction for the Fiat-Shamir-with-aborts transform,
following Theorem 3 of Barbosa et al. (CRYPTO 2023, ePrint 2023/246).
Instantiates `FiatShamir.signHashQueryBound` at the with-aborts signature type
and exposes `cmaToNmaLoss` plus `euf_cma_to_nma` (the managed-RO NMA interface),
together with the hybrid game chain (`hybridExpAtKey` over the signing bodies
`realSignBody`, `progSignBody`, `transSignBody`, `simSignBody`) that structures
the proof.

The quantitative parameters `ε` (per-key commitment-guessing probability),
`p_abort` (per-attempt abort probability), and `δ` (key-regularity failure
probability) are tied to the identification scheme by explicit hypotheses on a
"good key" event, mirroring the event `Γ` of the paper's Lemma 1: `δ` bounds
the probability that key generation falls outside the event, and `ε`/`p_abort`
bound the per-key quantities pointwise on it.

The scheme-specific NMA-to-hard-problem reduction lives with each concrete
scheme (e.g. `MLDSA.nma_security_short`).

## Module layout

The development is split along its proof phases: `Loss` (the loss functions),
`BodyHops` (the per-query Trans → Sim hop core and the verification tail),
`CouplingEngine` (the ghost-blind reduction, the deferred-draw handler, and the
per-body tape factorization), `ReadRecording` (the read-recording refinement and
the first-moment Markov step), `TapeFactorization` (the fold-level tape
factorization and the coincidence-count bound), `HopLemmas`, `NMAReduction`, and
`Assembly` (the headline `euf_cma_to_nma`). This umbrella module re-exports all
of them.
-/
