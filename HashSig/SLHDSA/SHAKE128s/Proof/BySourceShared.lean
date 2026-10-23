/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareFinal
public import HashSig.SLHDSA.SHAKE128s.Proof.BySourceBridge

/-!
# The shared half, with the signer's calls free

The shared half's cap is a cap on the adversary's own calls plus one per served request, so it
is read directly off the adversary's work and the requests; the signer's calls are never
charged. This file holds the one counting fact that step uses: the number of served requests
is at most the length of the signing log.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BySourceShared

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase
  SharePresent ShareRealCap BySourceBridge

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

theorem servedCount_le_length (log : SigningLog) :
    AdversaryQueries.servedCount log ≤ log.length :=
  List.length_filter_le _ _

end SlhDsaSecurity.BySourceShared
