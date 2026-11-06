/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Pathwise signing-query bounds

Every signing request counts toward the pathwise source-adversary budget, including repeated
requests and requests answered with failure.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Every execution path of the source adversary has at most `qs` signing calls.  Repeated
calls and calls answered with failure count; ambient uniform calls do not. -/
@[expose]
def SigningQueryBound (qs : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) : Prop :=
  ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs

end

end GXMSS.Unforgeability
