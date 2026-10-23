/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ClassGrowth
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitWitness
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomizerGate
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenUniform
public import HashSig.SLHDSA.SHAKE128s.Proof.SharedJoin

/-!
# The paired run carrying the recorder's recordings

The tail a fused presentation produces has as value the recorded tail's value and as state the
recorder's state (the cache and the two recordings). `pairedOf` is the paired run (walk, tail
result) at such a tail, and `forgetRecordings` is the map from it to the recorded pair
`SharedJoin.RecordedPair`: the recordings go, the cache stays.

The ordering event is not a predicate of the recorded pair alone: the record is a multiset, so
it remembers which queries were made and how often, not in which order, and the event is an
ordering. So it is read at a pair that carries the recordings besides, while everything defined
on the recorded pair keeps its probability under `forgetRecordings`, by `probEvent_forget`, once
the presentation satisfies `ForgetsTo`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.LateProbes

open Security SplitPrefix SplitWitness

/-! ## The pair the ordering term is read at

A fused presentation supplies two equations about its tail: that it *is* a recorder run at the
walk's cache, and that forgetting its recordings returns the recorded tail. -/

/-- The tail a fused presentation produces: the recorded tail's value, the recorder's state. -/
abbrev FusedTail : Type :=
  Adversary → (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ->
    ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitState)

/-- The pair the ordering term is read at. -/
abbrev SplitPair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    (((Outcome × Multiset Bytes) × Nat) × SplitState)

/-- The paired run at such a tail. -/
noncomputable def pairedOf (fused : FusedTail) (adversary : Adversary) : ProbComp SplitPair := do
  let walk <- WarmedGame.graphWalk
  let result <- fused adversary walk
  pure (walk, result)

/-- The recorded pair a split pair forgets to: the recordings go, the cache stays. -/
def forgetRecordings (pair : SplitPair) : SharedJoin.RecordedPair :=
  (pair.1, (pair.2.1, pair.2.2.1))

/-! ## What the forgetting map buys

One equation, that forgetting the recordings returns the recorded paired run, carries every
event and every count from the one object to the other. -/

/-- The equation a fused presentation owes: forgetting the recordings leaves the recorded paired
run.

It is an equality of **distributions**, not of computations. The two are different computations
and will stay different ones, while everything the join reads — a probability, a count, a
support — is a function of the distribution alone. Asking for the stronger equation would be
asking for something nobody can give and nothing here uses. -/
def ForgetsTo (fused : FusedTail) (adversary : Adversary) : Prop :=
  (∀ pair : SharedJoin.RecordedPair,
      Pr{let x ← forgetRecordings <$> pairedOf fused adversary}[x = pair] =
        Pr{let x ← RandomiserRecord.recordedPairedRun adversary}[x = pair]) ∧
    support (forgetRecordings <$> pairedOf fused adversary) ⊆
      support (RandomiserRecord.recordedPairedRun adversary)

open scoped Classical in
/-- **Every event the join already has keeps its probability.** -/
theorem probEvent_forget {fused : FusedTail} {adversary : Adversary}
    (hforget : ForgetsTo fused adversary) (event : SharedJoin.RecordedPair → Prop) :
    Pr{let pair ← pairedOf fused adversary}[event (forgetRecordings pair)] =
      Pr{let x ← RandomiserRecord.recordedPairedRun adversary}[event x] := by
  rw [← prEvent_map (pairedOf fused adversary) forgetRecordings event]
  exact (evalDistEq_of_forall_prEvent_eq_output hforget.1).prEvent_eq event

/-! ## Supports of the paired run -/

/-- A paired run's result is a walk in the graph walk's support beside a tail result at it. -/
theorem mem_support_pairedOf {fused : FusedTail} {adversary : Adversary} {pair : SplitPair}
    (hpair : pair ∈ support (pairedOf fused adversary)) :
    ∃ walk ∈ support WarmedGame.graphWalk, ∃ result ∈ support (fused adversary walk),
      (walk, result) = pair := by
  rw [pairedOf, mem_support_bind_iff] at hpair
  obtain ⟨walk, hwalk, hrest⟩ := hpair
  rw [mem_support_bind_iff] at hrest
  obtain ⟨result, hresult, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact ⟨walk, hwalk, result, hresult, hpure.symm⟩

end SlhDsaSecurity.LateProbes
