/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Security
public import HashSig.SLHDSA.SHAKE128s.Proof.WorkFinal

/-!
# Strong unforgeability of SLH-DSA-SHAKE-128s

`slhDsa_sufCma_127`: in the classical random-oracle model, SLH-DSA-SHAKE-128s
(`HashSig.SLHDSA.SHAKE128s.Statement.Scheme`) has 127 bits of strong unforgeability in the sense of
`SlhDsaSecurity.Security.HasSecurityBits`, counting the adversary's signing requests, its own hash
calls and the hash calls of verifying its forgery.
-/

@[expose] public section

namespace SlhDsaSecurity

open Security

/-- **SLH-DSA-SHAKE-128s has 127 bits of strong unforgeability**, counting the adversary's
signing requests, its hash calls and the verification of its forgery. -/
theorem slhDsa_sufCma_127 : HasSecurityBits adversaryWork 127 :=
  WorkFinal.hasSecurityBits_work

end SlhDsaSecurity
