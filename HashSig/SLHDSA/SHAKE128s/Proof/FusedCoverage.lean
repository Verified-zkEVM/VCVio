/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.LateProbes
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomiserRecord

/-!
# The tail the ordering term reads, and the two equations it owes

`LateProbes` asks a fused presentation for two things and nothing else: that its tail **is** a
recorder run at the walk's own cache and key, and that forgetting its recordings leaves the
recorded paired run. This file supplies both, and the tail that does it is the one already in
hand — `RecordedTail.recordedAfterSeeds` run under `SplitPrefix.recorder` instead of under the
shared oracle.

Nothing is reshaped. The value is `RecordedTail.recordedTail`'s, so the adversary-and-verifier
record stays the `Multiset Bytes` beside the `Outcome` and `SharedJoin.recordOf` reads it
unchanged; the state is the recorder's own `SplitState`, disclosing recording first and target
second, in the position `StateT` already puts it. The two recordings stay **lists**: the
potential argument reads the cache in force when an entry was filed and counts the recording's
length, and a multiset of the same inputs is a different object no projection recovers them
from.

**Forgetting is an equality of computations, not merely of distributions.** `ForgetsTo` asks only
for the pointwise probabilities and a support containment, because the two runs were expected to
be different computations — but they are not. The recorder answers every query exactly as the
shared oracle does and appends to its recordings afterwards, so dropping the recordings returns
the shared oracle's run on the nose. `run_recorder_forget` is that, by one induction, and both
conjuncts fall out of it.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.FusedCoverage

open Security SplitPrefix

/-! ## Dropping the recordings -/

/-! ## The tail -/

/-- The two tests the answer side's join names, at a walk. -/
noncomputable abbrev leftKeepAt
    (walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    Bytes → QueryCache HashSpec → Prop :=
  SplitWitness.disclosingKeep walk.1.1.2.1
    (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)

/-- The target test at a walk. -/
noncomputable abbrev rightKeepAt
    (walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    Bytes → QueryCache HashSpec → Prop :=
  SplitWitness.targetKeep walk.1.1.2.1
    (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)

/-- **The tail the ordering term reads**: the recorded game, run under the recorder. -/
@[expose] noncomputable def fusedTail : LateProbes.FusedTail :=
  fun adversary walk =>
    (simulateQ (recorder (leftKeepAt walk) (rightKeepAt walk))
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run
        (walk.2, [], [])

end SlhDsaSecurity.FusedCoverage
