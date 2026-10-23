/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedQueries

/-!
# The keys, given rather than generated

A handler has to exist before the run it answers. The signing handler is built from the secret
key, and the game produces that key *inside* the computation the handler would be answering —
so as long as key generation is a step of that computation, the signer cannot move out of it.

It need not be a step. Run from the walk's cache, key generation samples nothing and changes
nothing: `HonestProbes.run_keygenInternal_world_eq_pure` says its run is a `pure`, and the value
it returns is the key the cache already determines. Replacing the call by that value leaves the
rest of the game untouched, and `recordedAfterSeedsAt` is the game written that way — the same
do-block with its keys handed in.

**Nothing of the outcome moves.** Key generation's hash calls were never part of
`Outcome.counts`, which counts the adversary's own calls, the verifier's, and signing requests
and nothing else; what the substitution removes is calls the *outer* total counts, which is the
same thing the stripping surgery removes and is handled the same way — the law below is about
the uncounted run, with `Security.countAllHashes` left outside it. Being an equality of runs, it
carries every field of the outcome and the record as literally the same values.

**So apply it at the uncounted level, never inside the counter.** The substitution is sound
exactly because the law says nothing about the outer total, which it does change; used under
`Security.countAllHashes` it would be claiming something false.

The substitution also makes the key explicit: it is `⟨sds.1, sds.2.1, ⟨sds.2.2, root⟩⟩`, whose
only table coordinates are the secret seed and the honest root.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.KeygenValue

open Security CacheReplay RecordedQueries

/-- The keys the walk's cache determines. -/
noncomputable def honestKeys (sds : Digest × Digest × Digest)
    (outputs : CanonicalGraph.Programming.Outputs) : SecretKey × PublicKey :=
  @Scheme.keygenInternal Id _
    (replayQuery (HonestProbes.warmCache sds.2.2 sds.1 outputs)) sds.1 sds.2.1 sds.2.2

/-- The recorded game with its keys handed in rather than generated. The signer is the stripped
one. -/
noncomputable def recordedAfterSeedsAt (adversary : Adversary)
    (keys : SecretKey × PublicKey) (warm : QueryCache HashSpec) :
    OracleComp OracleWorld (Outcome × Multiset Bytes) := do
  let adversaryStep ←
    (simulateQ (recordedAdversaryImpl +
      recordedSigningOracle (StrippedGame.strippedSign warm keys.1))
      (adversary.main keys.2)).run.run []
  let verifierStep ← countRecorded verifierCost
    (Scheme.verify keys.2 adversaryStep.1.1.message adversaryStep.1.1.signature)
  pure ({
    forgery := adversaryStep.1.1
    signed := adversaryStep.2
    verified := verifierStep.1
    counts := (Multiplicative.toAdd adversaryStep.1.2).1 + verifierStep.2.1 },
    (Multiplicative.toAdd adversaryStep.1.2).2 + verifierStep.2.2)

/-- **Generating the keys and handing them in are the same run.** -/
theorem run_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (outputs : CanonicalGraph.Programming.Outputs) :
    (simulateQ KeygenUniform.rom
        (recordedAfterSeeds adversary sds
          (HonestProbes.warmCache sds.2.2 sds.1 outputs))).run
        (HonestProbes.warmCache sds.2.2 sds.1 outputs) =
      (simulateQ KeygenUniform.rom
        (recordedAfterSeedsAt adversary (honestKeys sds outputs)
          (HonestProbes.warmCache sds.2.2 sds.1 outputs))).run
        (HonestProbes.warmCache sds.2.2 sds.1 outputs) := by
  rw [recordedAfterSeeds, simulateQ_bind, StateT.run_bind,
    StrippedGame.run_strippedKeygen _ sds _ (StrippedGame.Extends.refl _),
    HonestProbes.run_keygenInternal_world_eq_pure, pure_bind]
  rfl

end SlhDsaSecurity.KeygenValue
