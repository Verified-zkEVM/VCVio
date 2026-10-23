/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SignerRightRecord
public import HashSig.SLHDSA.SHAKE128s.Proof.PhaseProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedTail

/-!
# Where a target-recorded entry of the adversary's phase came from

`PhaseProvenance.provenance_phase_subset` attributes an entry the phase *installed* to the
adversary's record or to a signing sub-run, and it does so at the ROM. The ordering term needs
the same attribution for an entry the phase *filed as a target*, which is a question about the
recorder's second recording and therefore has to be asked of the recorder's own run.

This is that induction. It is the same shape as the one at the ROM, with two differences that
both make it smaller.

**The log drops out.** The provenance at the ROM names *which* logged request the signer was
serving, which costs it `log_eq_recordedSigningOracle` and `log_append`. Nothing here needs it:
the consumer only has to rule out the digest shape, so the conclusion quantifies over the frame
existentially and those two lemmas need no mirror.

**The signer's step is one lemma.** `SignerRightRecord.sign_right_record` already says what a
served request can file — its randomiser probe, or an entry that comes with a cache holding that
request's randomiser answer — so this file does the phase bookkeeping and nothing about the
signer.

The conclusion keeps both the answer and the containment rather than the bare fact that
something is cached, because the consumer has to match the entry's own randomiser against the
cached one; a lemma hands back the most it knows, not the least its first consumer asked for.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.PhaseRightRecord

open Security CacheReplay RecordedQueries SplitPrefix SignerRightRecord

/-! ## The phase, run under the recorder -/

/-- The adversary's phase, run from a log and a recorder state. -/
noncomputable def recorderRun (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (x : RecordedRun α) (log : SigningLog) (state : SplitState) :
    ProbComp (((α × Multiplicative Tally) × SigningLog) × SplitState) :=
  (simulateQ (recorder leftKeep rightKeep) ((WriterT.run x).run log)).run state

theorem recorderRun_bind (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α β : Type} (x : RecordedRun α) (next : α → RecordedRun β)
    (log : SigningLog) (state : SplitState) :
    recorderRun leftKeep rightKeep (x >>= next) log state =
      recorderRun leftKeep rightKeep x log state >>= fun outer =>
        (fun inner => (((inner.1.1.1, outer.1.1.2 * inner.1.1.2), inner.1.2), inner.2)) <$>
          recorderRun leftKeep rightKeep (next outer.1.1.1) outer.1.2 outer.2 := by
  simp only [recorderRun, WriterT.run_bind, StateT.run_bind, StateT.run_map, simulateQ_bind,
    simulateQ_map, StateT.run_map]

/-- **A phase run only ever adds cache entries.** -/
theorem persists_of_mem_recorderRun (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (x : RecordedRun α) (log : SigningLog) (state : SplitState)
    (result : ((α × Multiplicative Tally) × SigningLog) × SplitState)
    (hresult : result ∈ support (recorderRun leftKeep rightKeep x log state))
    (probe : Bytes) (value : HashOutput) (hentry : state.1 probe = some value) :
    result.2.1 probe = some value :=
  recorder_cache_value_persists leftKeep rightKeep ((WriterT.run x).run log) state result
    hresult probe value hentry

/-! ## The adversary's own step -/

/-- A world query, simulated, is the implementation at that query. -/
theorem simulateQ_worldQuery {σ : Type} (impl : QueryImpl OracleWorld (StateT σ ProbComp))
    (queried : OracleWorld.Domain) :
    simulateQ impl (liftM (OracleSpec.query (spec := OracleWorld) queried) :
      OracleComp OracleWorld (OracleWorld.Range queried)) = impl queried := by
  simp

set_option maxHeartbeats 800000 in
/-- **A hash step files at most its own input, and its own input is what it records.** -/
theorem right_record_adversaryImpl (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (queried : OracleWorld.Domain) (log : SigningLog) (state : SplitState)
    (outer : ((OracleWorld.Range queried × Multiplicative Tally) × SigningLog) × SplitState)
    (houter : outer ∈ support
      (recorderRun leftKeep rightKeep (recordedAdversaryImpl queried) log state)) :
    ∀ entry ∈ outer.2.2.2, entry ∈ state.2.2 ∨
      entry.1 ∈ (Multiplicative.toAdd outer.1.1.2).2 := by
  classical
  rw [recorderRun, run_recordedAdversaryImpl, simulateQ_map, StateT.run_map,
    simulateQ_worldQuery, support_map] at houter
  obtain ⟨step, hstep, heq⟩ := houter
  have hstate : outer.2 = step.2 := by rw [← heq]
  have hrecord : outer.1.1.2 = Multiplicative.ofAdd
      ((Counts.single .hash (hashCost queried) : Counts), recordOf queried) := by rw [← heq]
  intro entry hentry
  rw [hstate] at hentry
  rcases queried with coin | input
  · -- A private sample touches neither recording.
    rw [show step.2 = state from by
      rw [← RecorderView.recorderOf_cache leftKeep rightKeep] at hstep
      exact RecorderView.recorderOf_step_inl leftKeep rightKeep coin state step hstep] at hentry
    exact Or.inl hentry
  · rw [show step.2.2 = appended leftKeep rightKeep input state step.1 from by
      rw [← RecorderView.recorderOf_cache leftKeep rightKeep] at hstep
      have := RecorderView.recorderOf_step_record leftKeep rightKeep input state step hstep
      rwa [RecorderView.appendedOf_cache] at this] at hentry
    rcases appended_right_mem leftKeep rightKeep input state step.1 entry hentry with
      hprior | hself
    · exact Or.inl hprior
    · refine Or.inr ?_
      rw [hrecord, toAdd_ofAdd, hself]
      show input ∈ recordOf (Sum.inr input)
      simp [recordOf]

/-! ## The game's own sequencing, at the recorder

The first brick of the outer decomposition. `WarmedSplit.mem_support_counted_bind` says this at
the shared oracle, and its proof uses nothing about the oracle — `countAllHashes_bind` is an
equality of computations and the rest is the monad's own algebra — so it carries with the
recorder substituted. The count rides on the value and the recorder never reads it. -/

set_option maxHeartbeats 800000 in
/-- **The count comes off**, leaving the run that produced it. The count rides on the value and
never reaches the state, so this is `WarmedSplit.mem_support_of_countAllHashes` with the oracle
substituted and nothing else changed.

Kept as a separate step rather than folded into the split, because at a *bracketed* tail the
count cannot live in the computation at all — the phase there is at `OracleWorld + SigningSpec`
and `countAllHashes` wraps a single `OracleComp OracleWorld`. Anything stated with the count as
a parameter survives that move; anything stated with `countAllHashes` baked in does not. -/
theorem mem_support_of_countAllHashes (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitState)
    (result : (α × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (countAllHashes computation)).run state)) :
    (result.1.1, result.2) ∈
      support ((simulateQ (recorder leftKeep rightKeep) computation).run state) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure]
    rfl
  | query_bind queried next ih =>
    rw [GrowthBudget.countAllHashes_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨step, hstep, ?_⟩
    rw [show result.1.1 = inner.1.1 from by rw [← heq], show result.2 = inner.2 from by rw [← heq]]
    exact ih step.1 step.2 inner hinner

set_option maxHeartbeats 800000 in
/-- **A counted bind splits at the recorder**, with the recorder's state threaded through. -/
theorem mem_support_counted_bind (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α β : Type} (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (state : SplitState) (result : (β × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (countAllHashes (computation >>= next))).run state)) :
    ∃ (value : α) (mid : SplitState) (first second : Nat),
      ((value, first), mid) ∈ support ((simulateQ (recorder leftKeep rightKeep)
          (countAllHashes computation)).run state) ∧
        ((result.1.1, second), result.2) ∈ support ((simulateQ (recorder leftKeep rightKeep)
          (countAllHashes (next value))).run mid) := by
  rw [GrowthBudget.countAllHashes_bind, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨first, hfirst, hrest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨second, hsecond, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  refine ⟨first.1.1, first.2, first.1.2, second.1.2, hfirst, ?_⟩
  rw [show result.1.1 = second.1.1 from by rw [hpure],
    show result.2 = second.2 from by rw [hpure]]
  exact hsecond

/-! ## The attribution -/

/-- Where a target-recorded entry of the phase can have come from: the adversary's own record,
or a signing sub-run — and in the second case, either the request's randomiser probe or an
entry filed at a cache that already held that request's randomiser answer. -/
def RightSource (sk : SecretKey) (rightKeep : Bytes → QueryCache HashSpec → Prop)
    (record : Multiset Bytes) (final : QueryCache HashSpec) (entry : Bytes × HashOutput) :
    Prop :=
  entry.1 ∈ record ∨
    ∃ framed : Bytes,
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed framed ∨
        ∃ (mid : QueryCache HashSpec) (answer : HashOutput),
          mid (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some answer ∧
            (∀ (probe : Bytes) (value : HashOutput),
              mid probe = some value → final probe = some value) ∧
              mid entry.1 = none ∧ rightKeep entry.1 mid ∧
                QueriesUnder final (SignerRandomiser.signInternalAt
                  (m := OracleComp HashSpec) (Hashing.truncate answer) sk framed) entry.1

theorem RightSource.mono_record_right {sk : SecretKey}
    {rightKeep : Bytes → QueryCache HashSpec → Prop} {record extra : Multiset Bytes}
    {final : QueryCache HashSpec} {entry : Bytes × HashOutput}
    (hsource : RightSource sk rightKeep record final entry) :
    RightSource sk rightKeep (extra + record) final entry := by
  rcases hsource with hmem | hsigner
  · exact Or.inl (Multiset.mem_add.mpr (Or.inr hmem))
  · exact Or.inr hsigner

set_option maxHeartbeats 1000000 in
/-- **Every entry the phase files as a target is the adversary's own query, or a signing
sub-run's.** The record is the one the phase's own value carries. -/
theorem right_record_phase (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (state : SplitState)
      (result : ((α × Multiplicative Tally) × SigningLog) × SplitState),
      result ∈ support (recorderRun leftKeep rightKeep
        (simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk)) computation)
        log state) →
      ∀ final : QueryCache HashSpec,
        (∀ (probe : Bytes) (value : HashOutput),
          result.2.1 probe = some value → final probe = some value) →
        ∀ entry ∈ result.2.2.2, entry ∈ state.2.2 ∨
          RightSource sk rightKeep (Multiplicative.toAdd result.1.1.2).2 final entry := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log state result hresult final hfinal entry hentry
    rw [recorderRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [show result.2 = state from by rw [hresult]] at hentry
    exact Or.inl hentry
  | query_bind t next ih =>
    intro log state result hresult final hfinal entry hentry
    rw [simulateQ_bind, simulateQ_spec_query, recorderRun_bind, mem_support_bind_iff] at hresult
    obtain ⟨outer, houter, hrest⟩ := hresult
    rw [support_map] at hrest
    obtain ⟨inner, hinner, hvalue⟩ := hrest
    have hstate : result.2 = inner.2 := by rw [← hvalue]
    have hrecord : (Multiplicative.toAdd result.1.1.2).2 =
        (Multiplicative.toAdd outer.1.1.2).2 + (Multiplicative.toAdd inner.1.1.2).2 := by
      rw [show result.1.1.2 = outer.1.1.2 * inner.1.1.2 from by rw [← hvalue], toAdd_mul]
      rfl
    have hinnerFinal : ∀ (probe : Bytes) (value : HashOutput),
        inner.2.1 probe = some value → final probe = some value := by
      intro probe value hprobe
      exact hfinal probe value (by rw [hstate]; exact hprobe)
    have houterFinal : ∀ (probe : Bytes) (value : HashOutput),
        outer.2.1 probe = some value → final probe = some value := by
      intro probe value hprobe
      exact hinnerFinal probe value
        (persists_of_mem_recorderRun leftKeep rightKeep
          (simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
            (next outer.1.1.1)) outer.1.2 outer.2 inner hinner probe value hprobe)
    rw [hstate] at hentry
    rcases ih outer.1.1.1 outer.1.2 outer.2 inner hinner final hinnerFinal entry hentry with
      houterMem | hsource
    · -- The head step filed it, and which handler ran decides which party made it.
      rcases t with world | request
      · have houter' : outer ∈ support (recorderRun leftKeep rightKeep
            (recordedAdversaryImpl world) log state) := houter
        rcases right_record_adversaryImpl leftKeep rightKeep world log state outer houter' entry
          houterMem with hprior | hrec
        · exact Or.inl hprior
        · exact Or.inr (by rw [hrecord]; exact Or.inl (Multiset.mem_add.mpr (Or.inl hrec)))
      · -- A signing request: its own sub-run is the only thing that ran.
        have houter' : outer ∈ support
            ((simulateQ (recorder leftKeep rightKeep)
              (Scheme.sign (m := OracleComp OracleWorld) sk request >>= fun answer =>
                (pure ((answer, Multiplicative.ofAdd ((Counts.single .signing 1 : Counts),
                    (0 : Multiset Bytes))), log ++ [⟨request, answer⟩]) :
                  OracleComp OracleWorld
                    ((Option Bytes × Multiplicative Tally) × SigningLog)))).run state) := by
          rw [← run_recordedSigningOracle]
          exact houter
        rw [simulateQ_bind, StateT.run_bind] at houter'
        obtain ⟨signed, hsigned, hpure⟩ := support_bind_exists houter'
        have hsignedState : outer.2 = signed.2 := by
          simp only [simulateQ_pure, StateT.run_pure] at hpure
          exact congrArg Prod.snd hpure
        rw [hsignedState] at houterMem
        cases hframe : request.frame with
        | none =>
          rw [sign_right_record_none leftKeep rightKeep sk request hframe state signed hsigned]
            at houterMem
          exact Or.inl houterMem
        | some framed =>
          have hsignedFinal : ∀ (probe : Bytes) (value : HashOutput),
              signed.2.1 probe = some value → final probe = some value := by
            intro probe value hprobe
            exact houterFinal probe value (by rw [hsignedState]; exact hprobe)
          rcases sign_right_record leftKeep rightKeep sk request framed hframe state signed
            hsigned final hsignedFinal entry houterMem with hprior | hrandomiser |
              ⟨mid, answer, hmid, hmidLater, habsent, hkeep, hqueries⟩
          · exact Or.inl hprior
          · exact Or.inr (Or.inr ⟨framed, Or.inl hrandomiser⟩)
          · refine Or.inr (Or.inr ⟨framed, Or.inr ⟨mid, answer, hmid, ?_, habsent, hkeep,
              hqueries⟩⟩)
            intro probe value hprobe
            exact hsignedFinal probe value (hmidLater probe value hprobe)
    · exact Or.inr (by rw [hrecord]; exact hsource.mono_record_right)

/-! ## Key generation's own step

The first of the two outer phases, in the split form: one lemma, one sub-run, one question. Key
generation's question is about an input's **shape**, which the shared oracle can answer, so this
projects with `SplitPrefix.mem_support_rom` and asks it there rather than redoing anything at
the recorder. -/

set_option maxHeartbeats 800000 in
/-- **An entry key generation files as a target is one of its own probes.** -/
theorem keygen_right_record (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (secretSeed prfSeed publicSeed : Digest) (state : SplitState)
    (result : (SecretKey × PublicKey) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (Scheme.keygenInternal (m := OracleComp OracleWorld)
        secretSeed prfSeed publicSeed)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (probe : Bytes) (value : HashOutput),
      result.2.1 probe = some value → later probe = some value)
    (entry : Bytes × HashOutput) (hentry : entry ∈ result.2.2.2) :
    entry ∈ state.2.2 ∨ QueriesUnder later
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
      entry.1 := by
  classical
  obtain ⟨suffix, hsuffix, hentries⟩ :=
    right_record_suffix leftKeep rightKeep _ state result hmem
  rw [hsuffix] at hentry
  rcases List.mem_append.mp hentry with hprior | hnew
  · exact Or.inl hprior
  · obtain ⟨mid, hstart, -, habsent, -, hfinal⟩ := hentries entry hnew
    have hfresh : state.1 entry.1 = none := by
      rcases hstate : state.1 entry.1 with _ | value
      · rfl
      · rw [hstart entry.1 value hstate] at habsent
        exact absurd habsent (by simp)
    refine Or.inr (CacheProvenance.queriesUnder_keygenInternal_of_fresh secretSeed prfSeed
      publicSeed state.1 result.2.1 later result.1
      (mem_support_rom leftKeep rightKeep _ state result hmem) hlater entry.1 hfresh ?_)
    rw [hfinal]
    simp

/-! ## The whole game

The outer decomposition is three applications of `mem_support_counted_bind`, one
`mem_support_of_countAllHashes` on each part, and `right_record_suffix` to say which part filed
an entry — and then **each branch asks its question of the object that can answer it**. Key
generation's and the verifier's are questions about an input's *shape*, which the shared oracle
can answer, so a consumer projects those sub-runs with `SplitPrefix.mem_support_rom` and uses
the lemmas already proved there; the recorder is needed only for the adversary's phase, where
the *recording* is the question, and that is `right_record_phase`.

**Stated as one theorem it does not elaborate.** Carrying the three sub-runs and their value
types in a single existential block makes a term the `constructorNameAsVariable` linter cannot
whnf inside its own budget, which is the signal that the statement is doing three jobs. It wants
splitting one phase per lemma, each handing back its own sub-run, exactly as
`right_record_phase` does for the middle one. The pieces it needs — the counted-bind split, the
count's removal, and the phase's own attribution — are all above.
-/

end SlhDsaSecurity.PhaseRightRecord
