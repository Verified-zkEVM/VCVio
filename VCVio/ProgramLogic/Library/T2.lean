/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.ProgramLogic.Library.T2.Caching
public import VCVio.ProgramLogic.Library.T2.RandomOracle
public import VCVio.ProgramLogic.Library.T2.Seeded
public import VCVio.ProgramLogic.Library.T2.Logging
public import VCVio.ProgramLogic.Library.T2.Counting
public import VCVio.ProgramLogic.Library.T2.CachingLogging
public import VCVio.ProgramLogic.Library.T2.Programming
public import VCVio.ProgramLogic.Library.T2.Combinators

/-!
# Program-logic library, tier 2: core handlers and handler combinators

WP-form one-query specs, `QueryImpl.MonotoneState` instances (whole-run frames), support
corollaries and distribution facts for the caching, random, seeded, eager, logging, counting,
cost, caching-logging and programming oracles, and for `QueryImpl.add`, `withBadFlag`,
`withBadUpdate`, `extendState` and `liftTarget`.
-/
