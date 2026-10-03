/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.ForkBounds
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Reduction

/-!
# Stateful Fiat-Shamir CMA-to-NMA chain

This file assembles the non-heap Fiat-Shamir EUF-CMA chain. The top-level
statement is factored so the H1/H2/H3 arithmetic is carried directly in the stateful
chain, while the H5 replay-forking boundary is a focused lemma.
-/
