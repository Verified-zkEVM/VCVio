/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.HonestGrowth
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# What verification can cost, and what key generation must

Two bounds on hash calls, one in each direction, for the shared half's budget.

**Verification makes at most `3929` hash calls**, on every path and against every oracle
(`isQueryBoundP_verify`). The bound is structural — `OracleComp.IsQueryBoundP` — because it is
needed on games other than the real one, where nothing about the adversary's budget is known: a
signature is at most a message digest, fourteen FORS leaves with twelve-step paths and a root
compression, and seven layers of thirty-five WOTS chains of at most fifteen steps, a compression,
and a nine-step path.

**Key generation makes at least `36 · 2 ^ 9` hash calls** (`count_keygen_ge`): every one of the
top subtree's `512` leaves derives thirty-five WOTS secrets and compresses. That is more than
`512 + 3929`, which is the room the shared half needs to pay for verification out of key
generation's spend.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.VerifyBound

open Security

/-- The hash calls, among the game's oracle queries. -/
@[expose] def IsHash (queried : OracleWorld.Domain) : Prop := queried.isRight = true

/-- Whether a query is a hash call is decidable. -/
instance : DecidablePred IsHash := fun queried => by unfold IsHash; infer_instance

/-! ## Upper bounds, structurally -/

end SLHDSA.SHAKE128s.VerifyBound
