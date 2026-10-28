/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Defs
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Equality
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.KeyLog
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.QueryBudget

/-!
# Fixed-context SHAKE-128s wire bridge

The bridge forwards the byte-wire adversary's ambient oracle queries and attaches its valid
fixed context to signing requests and forgeries. The shared definitions also identify the
external signing and verification programs at that context. Generated keys carry matching
public fields, and context attachment preserves returned-pair freshness of the complete log.
The complete winning programs and advantages agree under one shared random oracle.
Syntactic wire budgets bound the real game's signing requests and selected work, including
the actual external verifier's universal 3929-call cap.
-/
