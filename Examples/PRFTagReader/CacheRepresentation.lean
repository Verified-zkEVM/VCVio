/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.Network.Kernel
public import VCVio.OracleComp.QueryTracking.ListCache

/-!
# Association-list caches for PRF tag/reader reductions

Lookup keeps the first binding for a key and inserts only on misses. Decoding into
the library query cache commutes with each handler step and with adaptive clients.
The same projection preserves bad-event instrumentation and bounded FIFO verdicts,
including all three reader-cell and nonce-aliasing losses in the ideal-world bound.
-/

public section

open OracleComp OracleSpec PRFScheme

namespace PRFTagReader.ListCache

open QueryImpl.ListCache

variable {D R : Type} [DecidableEq D]

/-- Forward private randomness and memoize PRF answers in an association list. -/
@[expose]
def prfHandler [SampleableType R] :
    QueryImpl (PRFOracleSpec D R) (StateT (List (D × R)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (List (D × R)) ProbComp) + handler (D := D) (fun _ => $ᵗ R)

/-- Private randomness and ideal PRF calls preserve the decoded cache. -/
theorem prf_local_projection [SampleableType R]
    (q : (PRFOracleSpec D R).Domain) (cache : List (D × R)) :
    Prod.map id decode <$> prfHandler q cache =
      PRFScheme.prfIdealQueryImpl q (decode cache) := by
  cases q with
  | inl u =>
      change (Prod.map id decode <$> (do
        let x ← (query (spec := unifSpec) u : ProbComp (unifSpec.Range u))
        pure (x, cache))) = (do
        let x ← (query (spec := unifSpec) u : ProbComp (unifSpec.Range u))
        pure (x, decode cache))
      simp only [map_bind, map_pure, Prod.map_apply, id_eq]
  | inr d =>
      simp only [prfHandler, QueryImpl.add_apply_inr, PRFScheme.prfIdealQueryImpl_apply_inr]
      exact local_projection (fun _ => $ᵗ R) d cache

section Closing

variable {I S : Type} {spec : OracleSpec I} [SampleableType R]

/-- Close a stateful reduction with the association-list ideal PRF handler. -/
@[expose]
def close (reduction : QueryImpl spec (StateT S (OracleComp (PRFOracleSpec D R)))) :
    QueryImpl spec (StateT (S × List (D × R)) ProbComp) := fun q state => do
  let out ← (simulateQ prfHandler ((reduction q).run state.1)).run state.2
  pure (out.1.1, out.1.2, out.2)

/-- Close a stateful reduction with the function-valued ideal PRF cache. -/
@[expose]
def closeReference (reduction : QueryImpl spec (StateT S (OracleComp (PRFOracleSpec D R)))) :
    QueryImpl spec (StateT (S × (D →ₒ R).QueryCache) ProbComp) := fun q state => do
  let out ← (simulateQ PRFScheme.prfIdealQueryImpl ((reduction q).run state.1)).run state.2
  pure (out.1.1, out.1.2, out.2)

/-- Closing a reduction with the list handler preserves its result and decoded state. -/
theorem close_projection
    (reduction : QueryImpl spec (StateT S (OracleComp (PRFOracleSpec D R))))
    (q : spec.Domain) (state : S × List (D × R)) :
    Prod.map id (Prod.map id decode) <$> close reduction q state =
      closeReference reduction q (Prod.map id decode state) := by
  have h := map_run_simulateQ_eq_of_query_map_eq prfHandler PRFScheme.prfIdealQueryImpl
    decode prf_local_projection ((reduction q).run state.1) state.2
  have h' := congrArg (fun action => (fun out => (out.1.1, out.1.2, out.2)) <$> action) h
  simpa only [close, closeReference, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq] using h'

end Closing

section Instrumentation

variable {I S T U : Type} {spec : OracleSpec I}

/-- Reply-dependent auxiliary state commutes with the cache projection. -/
private theorem instrument_projection
    (left : QueryImpl spec (StateT S ProbComp)) (right : QueryImpl spec (StateT T ProbComp))
    (proj : S → T)
    (hlocal : ∀ q s, Prod.map id proj <$> left q s = right q (proj s))
    (advance : (q : spec.Domain) → spec.Range q → U → U) (q : spec.Domain) (state : S × U) :
    Prod.map id (Prod.map proj id) <$> (left.extendState (fun q _ r _ => advance q r)) q state =
      (right.extendState (fun q _ r _ => advance q r)) q (Prod.map proj id state) := by
  have h := congrArg (fun action =>
    (fun out => (out.1, out.2, advance q out.1 state.2)) <$> action) (hlocal q state.1)
  simpa only [QueryImpl.extendState, StateT.run, StateT.mk, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq] using h

end Instrumentation

end PRFTagReader.ListCache

namespace PRFTagReader.CachedPRF

open QueryImpl.ListCache PRFTagReader.ListCache PRFTagReader

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [DecidableEq Nonce] {sessionsPerTag : Nat}

/-- Decode the multiple-session cache while retaining the unlinkability state. -/
@[expose]
def projectMultiple (state : UnlinkState TagId × List ((TagId × Nonce) × Digest)) :=
  (state.1, decode state.2)

/-- Decode the single-session cache while retaining the unlinkability state. -/
@[expose]
def projectSingle
    (state : UnlinkState TagId × List (((TagId × Fin sessionsPerTag) × Nonce) × Digest)) :=
  (state.1, decode state.2)

@[simp] theorem projectMultiple_init :
    projectMultiple (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (UnlinkState.init, []) = (UnlinkState.init, ∅) := by
  simp [projectMultiple]

@[simp] theorem projectSingle_init :
    projectSingle (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) (UnlinkState.init, []) = (UnlinkState.init, ∅) := by
  simp [projectSingle]

/-- Decode the list cache and preserve the collision state. -/
@[expose]
def projectBad
    (state : (UnlinkState TagId × List ((TagId × Nonce) × Digest)) ×
      UnlinkBadState TagId Nonce Digest) :=
  (projectMultiple state.1, state.2)

@[simp] theorem projectBad_init :
    projectBad (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      ((UnlinkState.init, []), UnlinkBadState.init) =
        ((UnlinkState.init, ∅), UnlinkBadState.init) := by
  simp [projectBad]

section Network

variable {S T : Type} [DecidableEq Digest]

/-- An all-branch query bound lifts the local state projection to the FIFO verdict. -/
theorem verdict_projection
    (left : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (right : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT T ProbComp))
    (proj : S → T) (hlocal : ∀ q s, Prod.map id proj <$> left q s = right q (proj s))
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S) :
    Network.verdict left budget adversary state =
      Network.verdict right budget adversary (proj state) := by
  rw [Network.verdict_eq _ _ _ hbound, Network.verdict_eq _ _ _ hbound]
  exact run'_simulateQ_eq_of_query_map_eq left right proj hlocal adversary state

/-- The same bounded run preserves every Boolean observation of the projected state. -/
theorem stateEvent_projection
    (left : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S ProbComp))
    (right : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT T ProbComp))
    (proj : S → T) (hlocal : ∀ q s, Prod.map id proj <$> left q s = right q (proj s))
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) (state : S) (event : T → Bool) :
    Network.stateEvent left budget adversary state (event ∘ proj) =
      Network.stateEvent right budget adversary (proj state) event := by
  rw [Network.stateEvent_eq _ _ _ hbound, Network.stateEvent_eq _ _ _ hbound]
  have h := congrArg (fun action => (fun out => event out.2) <$> action)
    (map_run_simulateQ_eq_of_query_map_eq left right proj hlocal adversary state)
  simpa only [Functor.map_map, Prod.map, Function.comp_def] using h

end Network

variable [DecidableEq Digest] [Fintype TagId]
  [SampleableType Nonce] [SampleableType Digest]

/-- The multiple-session reduction closed with association-list caching. -/
noncomputable abbrev multiple := close (unlinkToMultiplePRFQueryImpl
  (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag))

/-- The single-session reduction closed with association-list caching. -/
noncomputable abbrev single := close (unlinkToSinglePRFQueryImpl
  (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag))

/-- One multiple-session service call preserves its response and decoded cache. -/
theorem multiple_local (q : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (state : UnlinkState TagId × List ((TagId × Nonce) × Digest)) :
    Prod.map id projectMultiple <$> multiple (sessionsPerTag := sessionsPerTag) q state =
      multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) q (projectMultiple state) :=
  close_projection _ q state

/-- One single-session service call preserves its response and decoded cache. -/
theorem single_local (q : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (state : UnlinkState TagId × List (((TagId × Fin sessionsPerTag) × Nonce) × Digest)) :
    Prod.map id projectSingle <$> single (sessionsPerTag := sessionsPerTag) q state =
      singleIdealQueryImpl (sessionsPerTag := sessionsPerTag) q (projectSingle state) :=
  close_projection _ q state

/-- Update the collision instrumentation after a tag request. -/
@[expose]
def advance : (q : (UnlinkOracleSpec TagId Nonce Digest).Domain) →
    (UnlinkOracleSpec TagId Nonce Digest).Range q →
    UnlinkBadState TagId Nonce Digest → UnlinkBadState TagId Nonce Digest
  | .inl tag, reply, state => multipleBadAdvance tag state reply
  | .inr _, _, state => state

/-- The list-cached multiple-session handler with collision instrumentation. -/
noncomputable abbrev bad :=
  (multiple (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag)).extendState (fun q _ r _ => advance q r)

/-- The collision instrumentation is the existing multiple-session bad handler. -/
theorem reference_instrument :
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)).extendState (fun q _ r _ => advance q r) =
      multipleBadQueryImpl _ _ _ sessionsPerTag := by
  funext q state
  cases q with
  | inl tag => rw [multipleBadQueryImpl_tag_run]; rfl
  | inr tr => rw [multipleBadQueryImpl_reader_run]; rfl

/-- Decoding preserves the response, cache, and collision instrumentation. -/
theorem bad_local (q : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (state : (UnlinkState TagId × List ((TagId × Nonce) × Digest)) ×
      UnlinkBadState TagId Nonce Digest) :
    Prod.map id projectBad <$> bad (sessionsPerTag := sessionsPerTag) q state =
      multipleBadQueryImpl _ _ _ sessionsPerTag q (projectBad state) := by
  have h := instrument_projection (multiple (sessionsPerTag := sessionsPerTag))
    (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag)) projectMultiple
    multiple_local advance q state
  rw [reference_instrument] at h
  exact h


variable [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag]

/-- The list-cached FIFO experiment satisfies the direct-coupling bound with all three losses. -/
theorem preserved_bound (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    𝒟[Network.verdict (multiple (sessionsPerTag := sessionsPerTag))
      (qReader + qTag) adversary (UnlinkState.init, [])] {true} ≤
    𝒟[Network.verdict (single (sessionsPerTag := sessionsPerTag))
      (qReader + qTag) adversary (UnlinkState.init, [])] {true} +
    𝒟[Network.stateEvent (bad (sessionsPerTag := sessionsPerTag))
      (qReader + qTag) adversary ((UnlinkState.init, []), UnlinkBadState.init)
      (fun state => state.2.bad)] {true} +
    ((qReader * Fintype.card TagId : Nat) : ENNReal) / (Fintype.card Digest : ENNReal) +
    ((qReader * qTag : Nat) : ENNReal) / (Fintype.card Nonce : ENNReal) +
    ((qReader * Fintype.card TagId * sessionsPerTag : Nat) : ENNReal) /
      (Fintype.card Digest : ENNReal) := by
  let : Countable (UnlinkState TagId) :=
    Function.Injective.countable (f := UnlinkState.sessionsUsed)
      (by rintro ⟨a⟩ ⟨b⟩ h; cases h; rfl)
  let : Countable (TagTranscript Nonce Digest) :=
    Function.Injective.countable
      (f := fun t : TagTranscript Nonce Digest => (t.nonce, t.auth))
      (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; cases Prod.mk.inj h; simp_all)
  let : Countable (UnlinkBadState TagId Nonce Digest) :=
    Function.Injective.countable
      (f := fun s : UnlinkBadState TagId Nonce Digest =>
        (s.sessionsUsed, s.responses, s.bad, s.cacheBad))
      (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; cases Prod.mk.inj h; simp_all)
  let : Countable ReaderReply :=
    Function.Injective.countable (f := ReaderReply.accepts)
      (by intro a b h; cases a <;> cases b <;> simp_all [ReaderReply.accepts])
  let (q : (UnlinkOracleSpec TagId Nonce Digest).Domain) :
      Countable ((UnlinkOracleSpec TagId Nonce Digest).Range q) := by
    cases q <;> dsimp [UnlinkOracleSpec] <;> infer_instance
  let (q : (UnlinkOracleSpec TagId Nonce Digest).Domain) :
      MeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range q) := ⊤
  let (q : (UnlinkOracleSpec TagId Nonce Digest).Domain) :
      DiscreteMeasurableSpace ((UnlinkOracleSpec TagId Nonce Digest).Range q) :=
    ⟨fun _ => trivial⟩
  let : MeasurableSpace (Network.MultipleServiceState TagId Nonce Digest) := ⊤
  let : DiscreteMeasurableSpace (Network.MultipleServiceState TagId Nonce Digest) :=
    ⟨fun _ => trivial⟩
  let : MeasurableSpace (Network.SingleServiceState TagId Nonce Digest sessionsPerTag) := ⊤
  let : DiscreteMeasurableSpace (Network.SingleServiceState TagId Nonce Digest sessionsPerTag) :=
    ⟨fun _ => trivial⟩
  let : MeasurableSpace (MultipleBadState TagId Nonce Digest sessionsPerTag) := ⊤
  let : DiscreteMeasurableSpace (MultipleBadState TagId Nonce Digest sessionsPerTag) :=
    ⟨fun _ => trivial⟩
  have hbound := Network.totalQueryBound adversary qReader qTag hReader hTag
  rw [verdict_projection _ _ projectMultiple multiple_local _ _ hbound,
      verdict_projection _ _ projectSingle single_local _ _ hbound]
  have hbad := stateEvent_projection (bad (sessionsPerTag := sessionsPerTag))
    (multipleBadQueryImpl _ _ _ sessionsPerTag) projectBad bad_local
    (qReader + qTag) adversary hbound ((UnlinkState.init, []), UnlinkBadState.init)
    (fun state => state.2.bad)
  simp only [Function.comp_def, projectBad] at hbad
  rw [hbad]
  simpa only [projectMultiple_init, projectSingle_init, projectBad_init] using
    Network.multiple_le_single_add_bad_of_joint_law
      (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
      (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
      (multipleBadQueryImpl _ _ _ sessionsPerTag)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      Measurable.of_discrete adversary qReader qTag hReader hTag

end PRFTagReader.CachedPRF
