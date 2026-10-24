/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedQueries

/-!
# Which party made an entry the adversary's phase installed

`CacheProvenance` says an entry a run did not start with was made by a query. Inside the
adversary's phase there are two kinds of query — the adversary's own, forwarded by its handler,
and the signer's, made inside a signing sub-run — so the provenance of an entry the phase
installed is a two-way split, and this file proves it.

The vehicle for "the adversary asked at it" is **the record**, not a new predicate.
`RecordedQueries` already accumulates a `Multiset Bytes` of the adversary's own hash inputs in
the same writer as the counters, which is what makes `Multiset.card recorded = counts.work` hold
by construction; so a provenance stated at the record arrives already counted, and
`RecordedQueries.card_eq_work_adversary` is the bound. A fresh predicate would have to be
counted afterwards, and the obvious way to count it would be to prove it equivalent to the
record.

Recording is invisible (`RecordedQueries.run_simulateQ_map_writer`), so running the induction at
the recording handler costs nothing: the game's own phase is the image of the recorded one under
`forget`.

The signing branch carries the request's presence **in the log**, so a signing sub-run the log
names can be told from the adversary's own queries. Carrying it costs one more induction,
`log_append`, because the phase's log is only a *prefix* of the one the outcome reports.

The adversary's branch is the one place provenance cannot go through `CacheReplay`: the
adversary's handler forwards *world* queries, and a coin is not a hash call.
`CacheProvenance.queried_of_fresh_step` is that step, and it is where the coin half is discharged.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.PhaseProvenance

variable {α β : Type}

open Security CacheReplay RecordedQueries CacheProvenance

/-- The adversary's phase, run from a log and a cache, recording as it goes. -/
@[expose] noncomputable def recordedRun {α : Type} (x : RecordedRun α) (log : SigningLog)
    (cache : QueryCache HashSpec) :
    ProbComp (((α × Multiplicative Tally) × SigningLog) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom ((WriterT.run x).run log)).run cache

/-- The recorded run of a bind is that of its first half, followed by that of the continuation,
with the two tallies multiplied. -/
theorem recordedRun_bind {α β : Type} (x : RecordedRun α) (next : α → RecordedRun β)
    (log : SigningLog) (cache : QueryCache HashSpec) :
    recordedRun (x >>= next) log cache =
      recordedRun x log cache >>= fun outer =>
        (fun inner => (((inner.1.1.1, outer.1.1.2 * inner.1.1.2), inner.1.2), inner.2)) <$>
          recordedRun (next outer.1.1.1) outer.1.2 outer.2 := by
  simp only [recordedRun, WriterT.run_bind, StateT.run_bind, StateT.run_map, simulateQ_bind,
    simulateQ_map, StateT.run_map]

/-- A phase run only ever adds cache entries. -/
theorem persists_of_mem_recordedRun {α : Type} (x : RecordedRun α) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (result : ((α × Multiplicative Tally) × SigningLog) × QueryCache HashSpec)
    (hresult : result ∈ support (recordedRun x log cache)) :
    StrippedGame.Extends cache result.2 :=
  fun probe value hvalue => GrowthCharge.cache_value_persists ((WriterT.run x).run log) cache
    result.2 result.1 hresult probe value hvalue

/-! ## The log only grows

Each handler either leaves the log alone or appends one entry, so the log a sub-run is handed is
a prefix of the one it leaves. That is what lets a request named in the middle of the phase be
found in the log the phase finally reports. -/

/-- The adversary's own handler leaves the log alone. -/
theorem log_eq_recordedAdversaryImpl (queried : OracleWorld.Domain) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (outer : ((OracleWorld.Range queried × Multiplicative Tally) × SigningLog) ×
      QueryCache HashSpec)
    (houter : outer ∈ support (recordedRun (recordedAdversaryImpl queried) log cache)) :
    outer.1.2 = log := by
  rw [recordedRun, run_recordedAdversaryImpl, simulateQ_map, StateT.run_map,
    support_map] at houter
  obtain ⟨step, -, hstep⟩ := houter
  rw [← hstep]

/-- The signing oracle appends exactly one entry, for the request it served, to the log. -/
theorem log_eq_recordedSigningOracle
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (request : Message)
    (log : SigningLog) (cache : QueryCache HashSpec)
    (outer : ((Option Bytes × Multiplicative Tally) × SigningLog) × QueryCache HashSpec)
    (houter : outer ∈ support (recordedRun (recordedSigningOracle signer request) log cache)) :
    ∃ answer : Option Bytes, outer.1.2 = log ++ [⟨request, answer⟩] := by
  rw [recordedRun, run_recordedSigningOracle, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at houter
  obtain ⟨step, -, hrest⟩ := houter
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  exact ⟨step.1, by rw [hrest]⟩

/-- **The log a phase is handed is a prefix of the one it leaves.** -/
theorem log_append (signer : Message → OracleComp OracleWorld (Option Bytes)) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : ((α × Multiplicative Tally) × SigningLog) × QueryCache HashSpec),
      result ∈ support (recordedRun
        (simulateQ (recordedAdversaryImpl + recordedSigningOracle signer) computation)
        log cache) → ∃ rest : SigningLog, result.1.2 = log ++ rest := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hresult
    rw [simulateQ_pure, recordedRun, WriterT.run_pure, StateT.run_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    exact ⟨[], by rw [hresult]; simp⟩
  | query_bind t next ih =>
    intro log cache result hresult
    rw [simulateQ_bind, simulateQ_spec_query, recordedRun_bind, mem_support_bind_iff] at hresult
    obtain ⟨outer, houter, hrest⟩ := hresult
    rw [support_map] at hrest
    obtain ⟨inner, hinner, hvalue⟩ := hrest
    obtain ⟨rest, hrest⟩ := ih outer.1.1.1 outer.1.2 outer.2 inner hinner
    have hhead : ∃ first : SigningLog, outer.1.2 = log ++ first := by
      rcases t with world | request
      · exact ⟨[], by rw [log_eq_recordedAdversaryImpl world log cache outer houter]; simp⟩
      · obtain ⟨answer, hanswer⟩ :=
          log_eq_recordedSigningOracle signer request log cache outer houter
        exact ⟨[⟨request, answer⟩], hanswer⟩
    obtain ⟨first, hfirst⟩ := hhead
    refine ⟨first ++ rest, ?_⟩
    rw [show result.1.2 = inner.1.2 from by rw [← hvalue], hrest, hfirst, List.append_assoc]

/-! ## Where an entry the phase installed came from -/

/-- **An entry the adversary's own handler installed is in the record.** A coin installs
nothing, and a hash call installs only at the input it records. -/
theorem mem_record_of_fresh (queried : OracleWorld.Domain) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (outer : ((OracleWorld.Range queried × Multiplicative Tally) × SigningLog) ×
      QueryCache HashSpec)
    (houter : outer ∈ support (recordedRun (recordedAdversaryImpl queried) log cache))
    (probe : Bytes) (hfresh : cache probe = none) (hpresent : outer.2 probe ≠ none) :
    probe ∈ (Multiplicative.toAdd outer.1.1.2).2 := by
  rw [recordedRun, run_recordedAdversaryImpl, simulateQ_map, StateT.run_map,
    support_map] at houter
  obtain ⟨step, hstep, heq⟩ := houter
  have hcache : outer.2 = step.2 := by rw [← heq]
  have hqueried : queried = Sum.inr probe :=
    queried_of_fresh_step queried cache step hstep probe hfresh (by rw [← hcache]; exact hpresent)
  rw [show outer.1.1.2 = Multiplicative.ofAdd
      ((Counts.single .hash (hashCost queried) : Counts), recordOf queried) from by rw [← heq],
    toAdd_ofAdd, show recordOf queried = ({probe} : Multiset Bytes) from by rw [hqueried]; rfl]
  simp

/-- What a signing sub-run leaves behind about an entry it installed: the input is one the
signer consulted, and the request's own `PRF_msg` answer is in the cache.

The second half is not decoration. The randomiser the signer *derived* is `Hashing.truncate` of
the cached answer; with no entry there `CacheReplay.replay` answers `default` and the randomiser
becomes a fixed constant. So the entry's presence has to be carried from where the sub-run is in
hand, not recovered later from a `QueriesUnder` witness, which does not imply it. -/
@[expose] def SignerMade (sk : SecretKey) (cache : QueryCache HashSpec) (request : Message)
    (probe : Bytes) : Prop :=
  QueriesUnder cache (Scheme.sign (m := OracleComp HashSpec) sk request) probe ∧
    ∀ framed : Bytes, request.frame = some framed →
      cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) ≠ none

/-- **An entry a signing sub-run installed is one the signer consulted**, read at any cache
extending the one the sub-run left, and the request's own randomiser answer is there too. -/
theorem signerMade_of_fresh_step (sk : SecretKey) (request : Message) (log : SigningLog)
    (cache laterCache : QueryCache HashSpec)
    (outer : ((Option Bytes × Multiplicative Tally) × SigningLog) × QueryCache HashSpec)
    (houter : outer ∈ support
      (recordedRun (recordedSigningOracle (Scheme.sign sk) request) log cache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      outer.2 input = some output → laterCache input = some output)
    (probe : Bytes) (hfresh : cache probe = none) (hpresent : outer.2 probe ≠ none) :
    SignerMade sk laterCache request probe := by
  rw [recordedRun, run_recordedSigningOracle, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at houter
  obtain ⟨step, hstep, hrest⟩ := houter
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  have hcache : outer.2 = step.2 := by rw [hrest]
  have hstepLater : ∀ (input : Bytes) (output : HashOutput),
      step.2 input = some output → laterCache input = some output :=
    fun input output h => hlater input output (by rw [hcache]; exact h)
  exact ⟨queriesUnder_sign_of_fresh sk request cache step.2 laterCache step.1 hstep hstepLater
      probe hfresh (by rw [← hcache]; exact hpresent),
    fun framed hframe => sign_randomizer_cached sk request framed hframe cache step.2 laterCache
      step.1 hstep hstepLater⟩

/-- Where an entry the phase installed can have come from: the adversary's own record, or a
signing sub-run for a request the log names. -/
@[expose] def PhaseSource (sk : SecretKey) (record : Multiset Bytes) (log : SigningLog)
    (cache : QueryCache HashSpec) (probe : Bytes) : Prop :=
  probe ∈ record ∨ ∃ entry ∈ log, SignerMade sk cache entry.1 probe

/-- **An entry the adversary's phase installed is the adversary's own query, or the signer's on
a request the log names.**

The cache the consultation is read at is free, and has to be: the phase sits inside the game,
and the provenance that consumes this is about the game's *final* cache, which the phase's own
is only a prefix of. -/
theorem provenance_phase_subset (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : ((α × Multiplicative Tally) × SigningLog) × QueryCache HashSpec),
      result ∈ support (recordedRun
        (simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk)) computation)
        log cache) →
      ∀ laterCache : QueryCache HashSpec,
        (∀ (input : Bytes) (output : HashOutput),
          result.2 input = some output → laterCache input = some output) →
      ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
        PhaseSource sk (Multiplicative.toAdd result.1.1.2).2 result.1.2 laterCache probe := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hresult laterCache hlater probe hfresh hpresent
    rw [simulateQ_pure, recordedRun, WriterT.run_pure, StateT.run_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    exact absurd (show result.2 probe = none from by rw [hresult]; exact hfresh) hpresent
  | query_bind t next ih =>
    intro log cache result hresult laterCache hlater probe hfresh hpresent
    rw [simulateQ_bind, simulateQ_spec_query, recordedRun_bind, mem_support_bind_iff] at hresult
    obtain ⟨outer, houter, hrest⟩ := hresult
    rw [support_map] at hrest
    obtain ⟨inner, hinner, hvalue⟩ := hrest
    have hlog : result.1.2 = inner.1.2 := by rw [← hvalue]
    have hcache : result.2 = inner.2 := by rw [← hvalue]
    have hrecord : (Multiplicative.toAdd result.1.1.2).2 =
        (Multiplicative.toAdd outer.1.1.2).2 + (Multiplicative.toAdd inner.1.1.2).2 := by
      rw [show result.1.1.2 = outer.1.1.2 * inner.1.1.2 from by rw [← hvalue], toAdd_mul]
      rfl
    have hinnerLater : ∀ (input : Bytes) (output : HashOutput),
        inner.2 input = some output → laterCache input = some output := by
      intro input output hentry
      exact hlater input output (by rw [hcache]; exact hentry)
    by_cases houterfresh : outer.2 probe = none
    · -- The entry is not there yet after the head, so the continuation installed it.
      rcases ih outer.1.1.1 outer.1.2 outer.2 inner hinner laterCache hinnerLater probe
        houterfresh (by rw [← hcache]; exact hpresent) with hmem | ⟨entry, hentry, hquery⟩
      · exact Or.inl (by rw [hrecord]; exact Multiset.mem_add.mpr (Or.inr hmem))
      · exact Or.inr ⟨entry, by rw [hlog]; exact hentry, hquery⟩
    · -- The head installed it, and which handler ran decides which party made it.
      have hpresentOuter : outer.2 probe ≠ none := houterfresh
      have hgrow : ∀ (input : Bytes) (output : HashOutput),
          outer.2 input = some output → laterCache input = some output := by
        intro input output hentry
        exact hinnerLater input output (persists_of_mem_recordedRun _ outer.1.2 outer.2 inner
          hinner input output hentry)
      rcases t with world | request
      · refine Or.inl ?_
        rw [hrecord]
        exact Multiset.mem_add.mpr (Or.inl
          (mem_record_of_fresh world log cache outer houter probe hfresh hpresentOuter))
      · obtain ⟨answer, hanswer⟩ :=
          log_eq_recordedSigningOracle (Scheme.sign sk) request log cache outer houter
        obtain ⟨rest, hrest⟩ := log_append (Scheme.sign sk) (next outer.1.1.1) outer.1.2 outer.2
          inner hinner
        refine Or.inr ⟨⟨request, answer⟩, ?_, ?_⟩
        · rw [hlog, hrest, hanswer, List.append_assoc]
          exact List.mem_append_right log (List.mem_append_left rest (List.mem_singleton_self _))
        · exact signerMade_of_fresh_step sk request log cache laterCache outer houter hgrow
            probe hfresh hpresentOuter

end SlhDsaSecurity.PhaseProvenance
