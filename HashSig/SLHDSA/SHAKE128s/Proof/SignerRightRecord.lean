/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SplitWitness
public import HashSig.SLHDSA.SHAKE128s.Proof.SignerRandomiser
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheProvenance

/-!
# What a signing sub-run can put in the target recording

`LateProvenance.hrecord`'s last branch needs that a target-recorded input is not the signer's own
digest query. Provenance inducts over the phase, where one signing request is a single step, so
the cache it can hand back is the one from *before* the request, while the recorder files at the
query *inside* it, after the randomiser. This file works at the sub-run, where both are in hand.
`Scheme.signInternal` is its randomiser query and then the rest, by
`SignerRandomiser.signInternal_eq`; after that first step the randomiser's answer is in the
cache, by `RecorderView.recorderOf_step_cache_self`; and `SplitPrefix.right_record_suffix`,
applied to **the rest**, says every entry the rest files comes with a cache that extends the one
the first step left. So every such cache holds the randomiser entry, with no ordering argument
and no step to name.

That leaves exactly one entry the first step itself could have filed — the `PRF_msg` input — and
`SplitWitness.narrowClass`'s last clause is what removes it, as its own docstring says.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.SignerRightRecord

open Security CacheAvailability SplitPrefix SignerRandomiser

/-- **One step files at most its own input.** The four cases of `appended`: a hit and a
left-kept query leave the target recording alone, a right-kept one appends this query's own
entry, and a query neither test keeps appends nothing. -/
theorem appended_right_mem (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput) (entry : Bytes × HashOutput)
    (hentry : entry ∈ (appended leftKeep rightKeep input state answer).2) :
    entry ∈ state.2.2 ∨ entry.1 = input := by
  classical
  cases hcached : state.1 input with
  | some cached =>
    rw [appended_of_cached leftKeep rightKeep input state answer cached hcached] at hentry
    exact Or.inl hentry
  | none =>
    by_cases hleft : leftKeep input state.1
    · rw [appended_of_left leftKeep rightKeep input state answer hcached hleft] at hentry
      exact Or.inl hentry
    · by_cases hright : rightKeep input state.1
      · rw [appended_of_right leftKeep rightKeep input state answer hcached hleft hright] at hentry
        rcases List.mem_append.mp hentry with hprior | hself
        · exact Or.inl hprior
        · exact Or.inr (by rw [List.mem_singleton.mp hself])
      · rw [appended_of_neither leftKeep rightKeep input state answer hleft hright] at hentry
        exact Or.inl hentry

/-! ## The rest of the signer, lifted

What the strengthened conclusion needs: the sub-run after the randomiser query read as a lift of
the hash-only computation, so that `CacheProvenance.queriesUnder_of_fresh_liftM` can say which
inputs it consulted. The naturality is `Correctness.Naturality.signInternal_simulate` without
its first line. -/

/-- Simulating the signer by a handler that forwards every hash query is the signer. -/
theorem signInternalAt_simulate {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]
    (impl : QueryImpl HashSpec m)
    (himpl : ∀ input, impl input = (query (spec := HashSpec) input : m HashOutput))
    (randomizer : Digest) (sk : SecretKey) (message : Bytes) :
    simulateQ impl (signInternalAt randomizer sk message) =
      (signInternalAt randomizer sk message : m Signature) := by
  simp only [signInternalAt, Hashing.messageDigest, simulateQ_bind, simulateQ_pure,
    VerifierNaturality.hash_simulate impl himpl,
    Correctness.Naturality.fors_sign_simulate impl himpl,
    VerifierNaturality.fors_simulate impl himpl,
    Correctness.Naturality.hypertree_sign_simulate impl himpl]

/-- **The rest of the signer, in the game's monad, is the hash-only one lifted.** -/
theorem signInternalAt_liftM (randomizer : Digest) (sk : SecretKey) (message : Bytes) :
    (signInternalAt (m := OracleComp OracleWorld) randomizer sk message) =
      liftM (signInternalAt (m := OracleComp HashSpec) randomizer sk message) := by
  rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_def]
  exact (signInternalAt_simulate
    (fun t => liftM (HashSpec.query t) : QueryImpl HashSpec (OracleComp OracleWorld))
    (fun _ => rfl) randomizer sk message).symm

/-- A hash query of the scheme's, simulated, is the implementation at that input. -/
theorem simulateQ_hash {σ : Type} (impl : QueryImpl OracleWorld (StateT σ ProbComp))
    (input : Bytes) :
    simulateQ impl (Hashing.hash (m := OracleComp OracleWorld) input) = impl (Sum.inr input) := by
  change simulateQ impl (liftM (OracleSpec.query (spec := OracleWorld) (Sum.inr input))) = _
  simp

/-- **The signer, cut at its randomiser query, under the recorder.** -/
theorem run_signInternal (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (message : Bytes) (state : SplitState) :
    (simulateQ (recorder leftKeep rightKeep)
        (Scheme.signInternal (m := OracleComp OracleWorld) sk message)).run state =
      ((recorder leftKeep rightKeep)
          (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed message))).run state >>=
        fun step =>
          (simulateQ (recorder leftKeep rightKeep)
            (signInternalAt (m := OracleComp OracleWorld) (Hashing.truncate step.1) sk
              message)).run step.2 := by
  rw [signInternal_eq sk message]
  simp only [Hashing.randomizer, Hashing.shortHash, bind_assoc, pure_bind,
    simulateQ_bind, StateT.run_bind, simulateQ_hash]
  rfl

/-- **Every entry a signing sub-run files as a target comes with the randomiser entry already
cached** — or is the `PRF_msg` input itself, which the narrowing removes.

The first query installs the randomiser answer;
`right_record_suffix` on the rest hands back, for each entry it files, a cache extending the one
that query left.

**The conclusion also names what the rest of the signer queried**, because a cache and an answer
are not usable together without knowing which entry the cache belongs to: the consumer has to
complete a disclosure witness at the *same* frame, and the entry's shape is what ties the two.
`probes_signInternalAt` reads that shape off the queries, at the cache the consumer names. -/
theorem signInternal_right_record (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (message : Bytes) (state : SplitState) (result : Signature × SplitState)
    (hresult : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (Scheme.signInternal (m := OracleComp OracleWorld) sk message)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (probe : Bytes) (value : HashOutput),
      result.2.1 probe = some value → later probe = some value) :
    ∀ entry ∈ result.2.2.2, entry ∈ state.2.2 ∨
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed message ∨
      ∃ (mid : QueryCache HashSpec) (answer : HashOutput),
        mid (Hashing.randomizerInput sk.prf sk.publicKey.seed message) = some answer ∧
          (∀ (probe : Bytes) (value : HashOutput),
            mid probe = some value → result.2.1 probe = some value) ∧
            mid entry.1 = none ∧ rightKeep entry.1 mid ∧
              CacheReplay.QueriesUnder later
                (signInternalAt (m := OracleComp HashSpec) (Hashing.truncate answer) sk message)
                entry.1 := by
  classical
  rw [run_signInternal, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, hrest⟩ := hresult
  -- The randomiser's answer is in the cache the first step leaves, whichever branch it took.
  have hcached : step.2.1 (Hashing.randomizerInput sk.prf sk.publicKey.seed message) =
      some step.1 := by
    rw [← RecorderView.recorderOf_cache leftKeep rightKeep] at hstep
    exact RecorderView.recorderOf_step_cache_self leftKeep rightKeep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step hstep
  -- What the rest of the signer filed, each with a cache extending that one.
  obtain ⟨suffix, hsuffix, hentries⟩ :=
    right_record_suffix leftKeep rightKeep
      (signInternalAt (m := OracleComp OracleWorld) (Hashing.truncate step.1) sk message)
      step.2 result hrest
  intro entry hentry
  rw [hsuffix] at hentry
  rcases List.mem_append.mp hentry with hold | hnew
  · -- Filed by the first step, if at all: its only input is the `PRF_msg` one.
    have hstepRecord := RecorderView.recorderOf_step_record leftKeep rightKeep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step
      (by rw [← RecorderView.recorderOf_cache leftKeep rightKeep] at *; exact hstep)
    rw [RecorderView.appendedOf_cache] at hstepRecord
    rw [show step.2.2 = appended leftKeep rightKeep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step.1 from
        hstepRecord] at hold
    rcases appended_right_mem leftKeep rightKeep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step.1 entry hold with
      hprior | hself
    · exact Or.inl hprior
    · exact Or.inr (Or.inl hself)
  · obtain ⟨mid, hstart, hmidLater, habsent, hkeep, hfinal⟩ := hentries entry hnew
    have hfreshStart : step.2.1 entry.1 = none := by
      rcases hstate : step.2.1 entry.1 with _ | value
      · rfl
      · rw [hstart entry.1 value hstate] at habsent
        exact absurd habsent (by simp)
    have hmemRom : (result.1, result.2.1) ∈ support ((simulateQ KeygenUniform.rom
        (liftM (signInternalAt (m := OracleComp HashSpec) (Hashing.truncate step.1) sk message) :
          OracleComp OracleWorld Signature)).run step.2.1) := by
      rw [← signInternalAt_liftM]
      exact mem_support_rom leftKeep rightKeep _ step.2 result hrest
    exact Or.inr (Or.inr ⟨mid, step.1, hstart _ _ hcached, hmidLater, habsent, hkeep,
      CacheProvenance.queriesUnder_of_fresh_liftM _ step.2.1 result.2.1 later result.1
        hmemRom hlater entry.1 hfreshStart
        (Option.ne_none_iff_exists'.mpr ⟨entry.2, hfinal⟩)⟩)

/-! ## At the request, which is where provenance names it

`Scheme.sign` is the framing test and then `signInternal`, so a served request files exactly what
its `signInternal` files and a rejected one files nothing. These are stated at the request, which
is the step provenance attributes. -/

/-- **A rejected request files nothing**, because it makes no query. -/
theorem sign_right_record_none (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (request : Message) (hframe : request.frame = none)
    (state : SplitState) (result : Option Bytes × SplitState)
    (hresult : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state)) :
    result.2 = state := by
  rw [Scheme.sign, hframe] at hresult
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
  rw [hresult]

/-- **A served request files what its `signInternal` files.** -/
theorem sign_right_record (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (state : SplitState) (result : Option Bytes × SplitState)
    (hresult : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (probe : Bytes) (value : HashOutput),
      result.2.1 probe = some value → later probe = some value) :
    ∀ entry ∈ result.2.2.2, entry ∈ state.2.2 ∨
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed framed ∨
      ∃ (mid : QueryCache HashSpec) (answer : HashOutput),
        mid (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some answer ∧
          (∀ (probe : Bytes) (value : HashOutput),
            mid probe = some value → result.2.1 probe = some value) ∧
            mid entry.1 = none ∧ rightKeep entry.1 mid ∧
              CacheReplay.QueriesUnder later
                (signInternalAt (m := OracleComp HashSpec) (Hashing.truncate answer) sk framed)
                entry.1 := by
  classical
  rw [Scheme.sign, hframe] at hresult
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨inner, hinner, hvalue⟩ := hresult
  rw [show result.2 = inner.2 from by rw [hvalue]]
  have hinnerState : result.2 = inner.2 := by rw [hvalue]
  refine signInternal_right_record leftKeep rightKeep sk framed state inner hinner later
    (fun probe value hprobe => hlater probe value ?_)
  rw [hinnerState]
  exact hprobe

end SlhDsaSecurity.SignerRightRecord
