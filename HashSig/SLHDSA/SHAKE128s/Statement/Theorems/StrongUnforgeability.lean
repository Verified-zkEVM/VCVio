/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
import HashSig.SLHDSA.SHAKE128s.Bridge.Scheme
import HashSig.SLHDSA.SHAKE128s.Proof.WorkFinal

/-!
# Strong unforgeability of SLH-DSA-SHAKE-128s

`slhDsa_sufCma_127`: the library's FIPS 205 SLH-DSA-SHAKE-128s (`SLHDSA.SHAKE128s.FIPS205.scheme`),
in pure mode, with deterministic signing and every SHAKE256 call one query of a single shared
random oracle on byte strings, has 127 bits of strong unforgeability in the sense of
`SLHDSA.SHAKE128s.Game.HasSecurityBits`: an adversary within `2 ^ 64` signing requests whose work is
at most `q ≥ 1` wins with probability at most `q / 2 ^ 127`, its work counting its signing
requests, its own hash calls and the hash calls of verifying its forgery (`Game.adversaryWork`).

The bound is proved on a transcription of the scheme with `240`-bit oracle answers
(`HashSig.SLHDSA.SHAKE128s.Statement.Scheme`, `WorkFinal.hasSecurityBits_work`) and carried to
FIPS 205's scheme, whose answers are `30`-byte strings, by the bridge of
`HashSig.SLHDSA.SHAKE128s.Bridge.Scheme`: the two schemes issue the same oracle queries, and their
key generations have the same law.
-/

public section

namespace SLHDSA.SHAKE128s

/-- **SLH-DSA-SHAKE-128s has 127 bits of strong unforgeability**: FIPS 205's pure-mode scheme over
one SHAKE256 random oracle with deterministic signing, counting the adversary's signing requests,
its hash calls and the verification of its forgery. -/
theorem slhDsa_sufCma_127 : Game.HasSecurityBits FIPS205.scheme Game.adversaryWork 127 :=
  Bridge.hasSecurityBits_fips205
    ((Bridge.hasSecurityBits_model_iff _ _).mp WorkFinal.hasSecurityBits_work)

end SLHDSA.SHAKE128s
